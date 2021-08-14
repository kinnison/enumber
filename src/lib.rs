//! # Numerical enumerations
//!
//! The `enumber` crate provides a mechanism for deriving a lot of useful helpers
//! for your enumerations which are sets of numbers.  Its main purpose is to
//! provide convenience implementations of a number of useful traits for your
//! enumerations automatically.
//!
//! See the [`convert`][macro@convert] macro and [`into`][macro@into]
//! macro for details, however here is a basic example:
//!
//! ```rust
//! #[enumber::convert]
//! #[repr(usize)]
//! enum Simple {
//!     Foo = 1,
//!     Bar = 2,
//! }
//!
//! use std::convert::TryFrom;
//!
//! // You can use try_from() to go from a suitable number to an instance of
//! // your enumeration.
//! assert!(matches!(Simple::try_from(1), Ok(Simple::Foo)));
//!
//! // You can convert from instances of your enumeration to a number.
//! assert_eq!(2 as usize, Simple::Bar.into());
//!
//! // You can render instances of your enumeration to strings.
//! assert_eq!(&format!("{}", Simple::Foo), "Foo");
//!
//! // And you can convert from a string to your enumeration, using the names
//! // of the enumeration items (case insensitively) or by number.  If the
//! // name or number is invalid, you'll get an error.
//!
//! use std::str::FromStr;
//! assert!(matches!(Simple::from_str("Foo"), Ok(Simple::Foo)));
//! assert!(matches!(Simple::from_str("bAr"), Ok(Simple::Bar)));
//! assert!(matches!(Simple::from_str("1"), Ok(Simple::Foo)));
//! assert!(matches!(Simple::from_str("0x02"), Ok(Simple::Bar)));
//! assert!(matches!(Simple::from_str("3"), Err(ParseSimpleError::UnknownValue(_))));
//! assert!(matches!(Simple::from_str("wibble"), Err(ParseSimpleError::UnknownName(_))));
//! ```
//!
//! The [`into`][macro@into] macro only implements `From`.  But,
//! unlike the [`convert`][macro@convert] macro, it is able to convert
//! variants with data to a value.  (It can't convert values to
//! variants, because the data is missing.)  This is helpful, for
//! instance, for converting rich error types to simple error codes at
//! an FFI boundary.
//!
//! ```rust
//! #[enumber::into]
//! #[repr(usize)]
//! enum Errors {
//!     Success = 0,
//!     #[value(0x10)] NotDefined(String),
//!     InvalidArg(String, String) = 0x20,
//!     OpNotSupported = 0x30,
//! }
//!
//! // You can convert from instances of your enumeration to a number.
//! assert_eq!(0 as usize, Errors::Success.into());
//! assert_eq!(0x10 as usize, Errors::NotDefined("a".into()).into());
//! assert_eq!(0x10 as usize, Errors::NotDefined("123".into()).into());
//! assert_eq!(0x20 as usize, Errors::InvalidArg("a".into(), "123".into()).into());
//! assert_eq!(0x30 as usize, Errors::OpNotSupported.into());
//! ```

use proc_macro::TokenStream;

use quote::{quote, ToTokens};
use syn::{
    parse_macro_input, parse_quote, Attribute, Data, DeriveInput, Error, Expr, Field, Fields,
    Ident, Type, Visibility,
};
use syn::{punctuated::Punctuated, FieldsUnnamed};
use syn::{spanned::Spanned, ExprRange};
use syn::{token::Paren, RangeLimits};

// Whether we are in enumber::Convert or enumber::Into mode.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum Mode {
    Convert,
    Into,
}

fn find_repr(name: &Ident, input: &[Attribute]) -> Result<Type, Error> {
    for attr in input.iter() {
        if attr.path.is_ident("repr") {
            return attr.parse_args();
        }
    }
    Err(Error::new_spanned(name, "missing repr(SomeType) attribute"))
}

fn generate_conversions(input: DeriveInput, mode: Mode) -> Result<impl Into<TokenStream>, Error> {
    let name = &input.ident;
    let visibility = &input.vis;
    let variants = match &input.data {
        Data::Enum(data) => &data.variants,
        _ => return Err(Error::new_spanned(input, "input must be an enum")),
    };

    let mut exhaustive = input.attrs.iter().any(|a| a.path.is_ident("exhaustive"));

    let mut default_variant = None;
    let mut values: Vec<(_, _, usize)> = Vec::new();
    for (n, variant) in variants.iter().enumerate() {
        let mut value: Option<Expr> = None;
        for attr in variant.attrs.iter().filter(|a| a.path.is_ident("value")) {
            if value.is_some() {
                return Err(Error::new_spanned(attr, "only one value is permitted"));
            }
            value = Some(attr.parse_args()?);
        }

        // enum Foo {
        //     X,                 // Unit
        //     Y(String),         // Unnamed, len = 1,
        //     Z(String, String), // Unnamed, len = 2,
        // }
        match &variant.fields {
            Fields::Unit => {
                if let Some(value) = value {
                    values.push((value.clone(), value, 0));
                } else {
                    return Err(Error::new_spanned(
                        &variant.ident,
                        "variant does not have a specified value",
                    ));
                }
            }
            Fields::Unnamed(f) => {
                if let Some(value) = value {
                    values.push((value.clone(), value, f.unnamed.len()));
                } else {
                    if f.unnamed.len() != 1 {
                        return Err(Error::new_spanned(
                            &variant.ident,
                            "default variant must have single value",
                        ));
                    }
                    if variant.attrs.iter().any(|a| a.path.is_ident("default")) {
                        if default_variant.is_some() {
                            return Err(Error::new_spanned(
                                &variant.ident,
                                "an enum can only have one default variant",
                            ));
                        }
                        default_variant = Some(n);
                    } else if let Some(range) =
                        variant.attrs.iter().find(|a| a.path.is_ident("ranged"))
                    {
                        let range: ExprRange = range.parse_args()?;
                        if range.from.is_none() && range.to.is_none() {
                            return Err(Error::new_spanned(
                                range,
                                "empty ranges are not supported",
                            ));
                        }
                        let base = range
                            .from
                            .as_ref()
                            .unwrap_or_else(|| range.to.as_ref().unwrap());
                        let def: Expr = if range.from.is_none()
                            && matches!(range.limits, RangeLimits::HalfOpen(_))
                        {
                            parse_quote!(#base - 1)
                        } else {
                            parse_quote!(#base)
                        };
                        values.push((Expr::Range(range), def, f.unnamed.len()));
                    } else {
                        return Err(Error::new_spanned(
                            &variant.ident,
                            "tuple variant must have an explicit value (#[value(...)]) \
                             or be labelled default or ranged",
                        ));
                    }
                }
            }
            _ => {
                let span = variant.ident.span();
                return Err(Error::new(span, "variant with data is not supported"));
            }
        }
    }

    if let Some(n) = default_variant {
        if n != variants.len() - 1 {
            return Err(Error::new_spanned(
                &variants[n],
                "default variant must be the last one",
            ));
        }
    }

    let inttype = default_variant
        .map(|n| match &variants[n].fields {
            Fields::Unnamed(f) => Ok(f.unnamed[0].ty.clone()),
            _ => unreachable!(),
        })
        .unwrap_or_else(|| find_repr(name, &input.attrs))?;

    let inttype = match inttype {
        Type::Path(p) => p.path,
        other => {
            return Err(Error::new_spanned(
                other,
                "default type must be a simple path",
            ))
        }
    };

    let default_variant = default_variant.map(|n| {
        let name = &variants[n].ident;
        let lower_name = name.to_string().to_ascii_lowercase();
        (name, lower_name)
    });

    exhaustive |= default_variant.is_some();

    // At this point, we have a type for the enumeration and we have a default
    // variant if there is one.

    // A tuple consisting of:
    //
    //   0. The variant's name (Foo)
    //   1. The lowercased name (foo)
    //   2. The variant's value ('1').
    //   3. The variant's default value.  For ranges, this is the
    //   lower bound of the range.  For everything else it is the same
    //   as the value (#2).
    //   4. The number of fields in the variant.
    let mappings: Vec<_> = values
        .into_iter()
        .enumerate()
        .map(|(n, value)| {
            let name = &variants[n].ident;
            let lower_name = name.to_string().to_ascii_lowercase();
            (name, lower_name, value.0, value.1, value.2)
        })
        .collect();

    let mut tokens = quote! {};

    // We now have a set of mappings, so let's generate the conversion *to*
    // the type we want.  Something like:
    //
    //     impl ::std::convert::From<&OpenExample> for u16
    //     {
    //         fn from(item: &OpenExample) -> u16
    //         {
    //             match item
    //             {
    //                 &OpenExample::First => 1,
    //                 &OpenExample::Second => 2,
    //                 &OpenExample::Third => 23,
    //             }
    //         }
    //     }
    //     impl ::std::convert::From<OpenExample> for u16 {
    //         fn from(item: OpenExample) -> u16 {
    //             (& item).into()
    //         }
    //     }
    let matcharms: Vec<_> = mappings
        .iter()
        .map(|entry| {
            let ename = entry.0;
            let value = &entry.2;
            let fields = entry.4;
            if matches!(value, Expr::Range(_)) {
                quote!(
                    &#name :: #ename(value) => value,
                )
            } else if fields > 0 {
                let mut f = quote!();
                for _ in 0..fields {
                    quote!(_,).to_tokens(&mut f);
                }
                quote!(
                    &#name :: #ename(#f) => #value,
                )
            } else {
                quote!(
                    &#name :: #ename => #value,
                )
            }
        })
        .collect();
    let defaultarm = if let Some((ename, _)) = default_variant {
        quote!(
            &#name :: #ename (value) => value,
        )
    } else {
        quote!()
    };

    let t = quote! {
        impl ::std::convert::From<&#name> for #inttype {
            fn from(item: &#name) -> #inttype {
                match item {
                    #(#matcharms)*
                    #defaultarm
                }
            }
        }

        impl ::std::convert::From<#name> for #inttype {
            fn from(item: #name) -> #inttype {
                (&item).into()
            }
        }
    };
    t.to_tokens(&mut tokens);

    if mode == Mode::Convert {
        // The From or TryFrom implementation:
        //
        //   impl ::std::convert::TryFrom<u16> for OpenExample
        //   {
        //       type Error = u16;
        //       fn try_from(value : u16) -> ::std::result::Result<Self, u16>
        //       {
        //         #[deny(unreachable_patterns)]
        //         match value
        //         {
        //             1 => Ok(Self::First),
        //             2 => Ok(Self::Second),
        //             23 => Ok(Self::Third),
        //             other => Err(value),
        //         }
        //       }
        //   }
        if exhaustive {
            // It's exhaustive so we can implement From.
            let literal_arms: Vec<_> = mappings
                .iter()
                .map(|(ident, _, literal, _, _)| {
                    if matches!(literal, Expr::Range(_)) {
                        quote! {
                            value @ #literal => Self::#ident (value),
                        }
                    } else {
                        quote! {
                            #literal => Self::#ident,
                        }
                    }
                })
                .collect();
            let default_arm = if let Some((default_name, _)) = default_variant {
                quote!(other => Self :: #default_name (other),)
            } else {
                quote!()
            };

            let t = quote! {
                impl ::std::convert::From<#inttype> for #name {
                    fn from(value: #inttype) -> Self {
                        #[deny(unreachable_patterns)]
                        match value {
                            #(#literal_arms)*
                            #default_arm
                        }
                    }
                }
            };
            t.to_tokens(&mut tokens);
        } else {
            // It's not exhaustive so we implement TryFrom.
            let literal_arms: Vec<_> = mappings
                .iter()
                .map(|(ident, _, literal, _, _)| {
                    if matches!(literal, Expr::Range(_)) {
                        quote! {
                            value @ #literal => Ok(Self::#ident (value)),
                        }
                    } else {
                        quote! {
                            #literal => Ok(Self::#ident),
                        }
                    }
                })
                .collect();

            let t = quote! {
                impl ::std::convert::TryFrom<#inttype> for #name {
                    type Error = #inttype;

                    fn try_from(value: #inttype) -> ::std::result::Result<Self, #inttype> {
                        #[deny(unreachable_patterns)]
                        match value {
                            #(#literal_arms)*
                            other => Err(value),
                        }
                    }
                }
            };
            t.to_tokens(&mut tokens);
        }
    }

    // A Display implementation:
    //
    //   impl ::std::fmt::Display for OpenExample
    //   {
    //       fn fmt(&self, f: &mut::std::fmt::Formatter<'_>) -> std::fmt::Result
    //       {
    //           match self
    //           {
    //               Self::First => f.write_str("First"),
    //               Self::Second => f.write_str("Second"),
    //               Self::Third => f.write_str("Third"),
    //           }
    //       }
    //   }
    if mode == Mode::Convert {
        let matcharms: Vec<_> = mappings
            .iter()
            .map(|(i, _, lit, _, _)| {
                let istr = i.to_string();
                if matches!(lit, Expr::Range(_)) {
                    quote! {
                        Self :: #i (value) => write!(f, concat!(#istr, "({})"), value),
                    }
                } else {
                    quote! {
                        Self :: #i => f.write_str(#istr),
                    }
                }
            })
            .collect();
        let default_arm = if let Some(tokens) = default_variant.as_ref().map(|(i, _)| {
            let istr = i.to_string();
            quote!(
                Self :: #i (value) => write!(f, concat!(#istr, "({})"), value),
            )
        }) {
            tokens
        } else {
            quote!()
        };

        let t = quote! {
            impl ::std::fmt::Display for #name {
                fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> std::fmt::Result {
                    match self {
                        #(#matcharms)*
                        #default_arm
                    }
                }
            }
        };

        t.to_tokens(&mut tokens);
    }

    if mode == Mode::Convert {
        // A FromStr implementation:
        //
        //   #[derive(Debug)]
        //   enum ParseClosedExampleError
        //   {
        //       UnknownName(::std::string::String),
        //       UnknownValue(u8),
        //   }
        //   impl ::std::str::FromStr for ClosedExample
        //   {
        //       type Err = ParseClosedExampleError;
        //       fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err>
        //       {
        //           match s.to_ascii_lowercase().as_str()
        //           {
        //               "One" => Ok(Self::One),
        //               "two" => Ok(Self::Two),
        //               "five" => Ok(Self::Five),
        //               other => {
        //                   use ::std::convert::TryFrom;
        //                   let value : u8 = if let Some(rest) = other.strip_prefix("0x") {
        //                       u8::from_str_radix(rest, 16)
        //                   } else if let Some(rest) = other.strip_prefix("0o") {
        //                       u8::from_str_radix(rest, 8)
        //                   } else {
        //                       other.parse()
        //                   }.map_err(|_| ParseClosedExampleError::UnknownName(s.into()))?;
        //                   match ClosedExample::try_from(value) {
        //                       Err(v) => unreachable!(),
        //                       Ok(v) => Ok(v),
        //                   }
        //               }
        //           }
        //       }
        //   }
        let matcharms: Vec<_> = mappings
            .iter()
            .map(|(name, lower_name, lit, def, _)| {
                if matches!(lit, Expr::Range(_)) {
                    quote! {
                        #lower_name => Ok(Self::#name(#def)),
                    }
                } else {
                    quote! {
                        #lower_name => Ok(Self :: #name),
                    }
                }
            })
            .collect();
        let errorname = Ident::new(&format!("Parse{}Error", name), name.span());

        let err_convert_case = if default_variant.is_some() {
            quote!(
                Err(v) => unreachable!(),
            )
        } else {
            quote!(
                Err(_) => Err(#errorname :: UnknownValue(value)),
            )
        };

        let t = quote! {
            #[derive(Debug)]
            #visibility enum #errorname {
                UnknownName(::std::string::String),
                UnknownValue(#inttype),
            }

            impl ::std::str::FromStr for #name {
                type Err = #errorname;

                fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err> {
                    match s.to_ascii_lowercase().as_str() {
                        #(#matcharms)*
                        other => {
                            use ::std::convert::TryFrom;
                            let value: #inttype = if let Some(rest) = other.strip_prefix("0x") {
                                #inttype :: from_str_radix(rest, 16)
                            } else if let Some(rest) = other.strip_prefix("0o") {
                                #inttype :: from_str_radix(rest, 8)
                            } else {
                                other.parse()
                            }.map_err(|_| #errorname :: UnknownName(s.into()))?;
                            match #name :: try_from(value) {
                                #err_convert_case
                                Ok(v) => Ok(v),
                            }
                        }
                    }
                }
            }
        };
        t.to_tokens(&mut tokens);
    }

    Ok(tokens)
}

#[doc(hidden)]
#[proc_macro_derive(Convert, attributes(value, exhaustive, ranged, default))]
pub fn derive_convert(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    match generate_conversions(input, Mode::Convert) {
        Ok(res) => res.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn to_derive(mut input: DeriveInput, mode: Mode) -> Result<DeriveInput, Error> {
    let variants = match &mut input.data {
        Data::Enum(data) => &mut data.variants,
        _ => return Err(Error::new_spanned(input, "input must be an enum")),
    };

    input.attrs.insert(
        0,
        match mode {
            Mode::Convert => {
                parse_quote!(
                    #[derive(::enumber::Convert)]
                )
            }
            Mode::Into => {
                parse_quote!(
                    #[derive(::enumber::Into)]
                )
            }
        },
    );

    let mut repr = find_repr(&input.ident, &input.attrs).ok();

    for variant in variants.iter_mut() {
        let mut ranged = false;
        if let Some((_, e)) = variant.discriminant.take() {
            let e: Expr = e;
            if matches!(e, Expr::Range(_)) {
                variant.attrs.push(parse_quote!(
                    #[ranged(#e)]
                ));
                ranged = true;
            } else {
                variant.attrs.push(parse_quote!(
                    #[value(#e)]
                ));
            }
        }
        if mode != Mode::Into && matches!(variant.fields, Fields::Unnamed(_)) {
            variant.attrs.push(parse_quote!(#[default]));
            repr = Some(match &variant.fields {
                Fields::Unnamed(u) => u.unnamed[0].ty.clone(),
                _ => unreachable!(),
            });
        } else if ranged {
            if let Some(ty) = repr.as_ref() {
                let mut unnamed = Punctuated::new();
                unnamed.push(Field {
                    attrs: Vec::new(),
                    vis: Visibility::Inherited,
                    ident: None,
                    colon_token: None,
                    ty: ty.clone(),
                });
                variant.fields = Fields::Unnamed(FieldsUnnamed {
                    paren_token: Paren {
                        span: variant.span(),
                    },
                    unnamed,
                });
            }
        }
    }

    Ok(input)
}

/// Convert an `enumber` compliant enum into a proper enum with
/// appropriate associated traits.
///
/// As an example, you might have the following enum definition:
///
/// ```rust
/// #[enumber::convert]
/// enum Ordinals {
///     First = 1,
///     Second = 2,
///     Third = 3,
///     TheRest(u16),
/// }
/// ```
///
/// Normally that enum would be invalid because of the combination of
/// both explicit discriminants, and a tuple-style variant.  The conversion
/// will strip the discriminants off the enumeration and then implement
/// conversions to/from the number type of the tuple-style variant.
///
/// In addition, implementations of [`Display`][std::fmt::Display] and
/// [`FromStr`][std::str::FromStr] will be automatically provided.  The error
/// type for the `FromStr` implementation will be named `Parse${NAME}Error`
/// and will have the same visibility specifier as your enum had.
///
/// The error enumeration will look like this:
///
/// ```rust,no_compile
/// enum ParseOrdinalsError {
///     UnknownName(String),
///     UnknownValue(u16)
/// }
/// ```
///
/// Naturally the integer type in the `UnknownValue` variant will be that of the
/// enum's tuple-style variant.
///
/// If you do not wish to have an "other" variant, then you can omit it, in which
/// case you must specify the representation of the enumeration explicitly:
///
/// ```rust
/// #[enumber::convert]
/// #[repr(u8)]
/// enum AccessLevel {
///     Guest = 0,
///     Member = 1,
///     Developer = 2,
///     Owner = 3,
/// }
/// ```
///
/// In this case, `From<${TYPE}>` will not be implemented, and instead there
/// will be an implementation of `TryFrom<${TYPE}>` where the error type for
/// that conversion is simply the input number type.
///
/// You *may* specify variants as taking a range rather than a fixed value,
/// and if you do, then the variant will be converted into a tuple type
/// automatically, in order to hold the exact value given during conversion.
/// As with the above examples, if you do not also specify a default variant
/// then you will have to specify the relevant integer representation.
///
/// Finally, if you are certain that your given values (or ranges) cover all
/// possible input values to the conversion functions, and you wish to omit the
/// default variant, then you can specify `#[exhaustive]` on the enumeration and
/// `enumber` will create a `From<${TYPE}>` impl despite the lack of the default
/// variant.  Of course, if your values are not exhaustive then the compiler will
/// flag an error and not continue.
///
/// ```rust,compile_fail
/// #[enumber::convert]
/// #[exhaustive]
/// #[repr(u8)]
/// enum Age {
///     Child = 0..=12,
///     Teenager = 13..=19,
///     Adult = 20..=65,
///     Pensioner = 66..=254, // Not quite enough, so this will fail to compile
/// }
/// ```
#[proc_macro_attribute]
pub fn convert(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    match to_derive(input, Mode::Convert) {
        Ok(res) => quote!(#res).into(),
        Err(err) => err.to_compile_error().into(),
    }
}

#[doc(hidden)]
#[proc_macro_derive(Into, attributes(value))]
pub fn derive_into(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    match generate_conversions(input, Mode::Into) {
        Ok(res) => res.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Convert an `enumber` compliant enum whose variants have data into
/// a proper enum with appropriate associated traits.
///
/// As an example, you might have the following enum definition:
///
/// ```rust
/// #[enumber::into]
/// #[repr(usize)]
/// enum Errors {
///     Success = 0,
///     #[value(0x10)] NotDefined(String),
///     InvalidArg(String, String) = 0x20,
///     OpNotSupported = 0x30,
/// }
/// ```
///
/// Enumber turns this into a normal enum and also implements
/// [`From`][std::convert::From].  This makes it easy to convert the
/// enum into its corresponding numeric value, which is particularly
/// useful when converting from rich Rust-style errors to C-style
/// error codes:
///
/// ```rust
/// # #[enumber::into]
/// # #[repr(usize)]
/// # enum Errors {
/// #     Success = 0,
/// #     #[value(0x10)] NotDefined(String),
/// #     InvalidArg(String, String) = 0x20,
/// #     OpNotSupported = 0x30,
/// # }
/// type ErrorCode = usize;
///
/// fn some_ffi() -> ErrorCode {
///     Errors::OpNotSupported.into()
/// }
/// # assert_eq!(some_ffi(), 0x30);
/// ```
///
/// Unlike the [`convert`][macro@convert] macro, this macro does not
/// generate an implementation of `From` in the opposite direction
/// (i.e., from a numeric value to a variant), nor does it generate an
/// implementation of [`FromStr`][std::str::FromStr] for the simple
/// reason that it is not possible to convert an error code to a
/// variant that has data without having default values, which is not
/// always reasonable.
///
/// This macro also doesn't support ranges or a default, because we
/// are only converting from variants to values and only a single
/// value per variant makes sense.  As such, the following does not
/// work:
///
/// ```rust,compile_fail
/// #[enumber::into]
/// #[repr(u8)]
/// enum Age {
///     Child(String) = 0..=12,
///     Teenager(String) = 13..=19,
///     Adult(String) = 20..=65,
///     Pensioner(String) = 66..=255,
/// }
/// ```
///
/// And, `into` does not implement Display as there isn't a single
/// reasonable way to implement Display for variants with data.
#[proc_macro_attribute]
pub fn into(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    match to_derive(input, Mode::Into) {
        Ok(res) => quote!(#res).into(),
        Err(err) => err.to_compile_error().into(),
    }
}
