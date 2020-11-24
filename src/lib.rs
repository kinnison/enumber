use proc_macro::TokenStream;

use quote::quote;
use syn::{
    parse_macro_input, parse_quote, Attribute, Data, DeriveInput, Error, Fields, Ident, LitInt,
    Type,
};

fn find_repr(name: &Ident, input: &[Attribute]) -> Result<Type, Error> {
    for attr in input.iter() {
        if attr.path.is_ident("repr") {
            return attr.parse_args();
        }
    }
    Err(Error::new_spanned(name, "missing repr(SomeType) attribute"))
}

fn generate_conversions(input: DeriveInput) -> Result<impl Into<TokenStream>, Error> {
    let name = &input.ident;
    let visibility = &input.vis;
    let variants = match &input.data {
        Data::Enum(data) => &data.variants,
        _ => return Err(Error::new_spanned(input, "input must be an enum")),
    };

    let mut default_variant = None;
    let mut values = Vec::new();
    for (n, variant) in variants.iter().enumerate() {
        match &variant.fields {
            Fields::Unit => {
                let mut value: Option<LitInt> = None;
                for attr in variant.attrs.iter().filter(|a| a.path.is_ident("value")) {
                    if value.is_some() {
                        return Err(Error::new_spanned(attr, "only one value is permitted"));
                    }
                    value = Some(attr.parse_args()?);
                }
                if let Some(value) = value {
                    values.push(value);
                } else {
                    return Err(Error::new_spanned(
                        &variant.ident,
                        "variant does not have a specified value",
                    ));
                }
            }
            Fields::Unnamed(f) => {
                if f.unnamed.len() != 1 {
                    return Err(Error::new_spanned(
                        &variant.ident,
                        "default variant must have single value",
                    ));
                }
                if !variant.attrs.iter().any(|a| a.path.is_ident("default")) {
                    return Err(Error::new_spanned(
                        &variant.ident,
                        "default variant must be labelled as default",
                    ));
                }
                if default_variant.is_some() {
                    return Err(Error::new_spanned(
                        &variant.ident,
                        "default variant must be the only one in the enum",
                    ));
                }
                default_variant = Some(n);
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

    // At this point, we have a type for the enumeration and we have a default
    // variant if there is one.

    let mappings: Vec<_> = values
        .into_iter()
        .enumerate()
        .map(|(n, value)| {
            let name = &variants[n].ident;
            let lower_name = name.to_string().to_ascii_lowercase();
            (name, lower_name, value)
        })
        .collect();

    // We now have a set of mappings, so let's generate the conversion *to*
    // the type we want

    let into_literal = {
        let matcharms: Vec<_> = mappings
            .iter()
            .map(|entry| {
                let name = entry.0;
                let value = &entry.2;
                quote!(
                    Self :: #name => #value,
                )
            })
            .collect();
        let defaultarm = if let Some((name, _)) = default_variant {
            quote!(
                Self :: #name (value) => value,
            )
        } else {
            quote!()
        };
        quote! {
            impl ::std::convert::Into<#inttype> for #name {
                fn into(self) -> #inttype {
                    match self {
                        #(#matcharms)*
                        #defaultarm
                    }
                }
            }
        }
    };

    let from_literal = if let Some((default_name, _)) = default_variant {
        let literal_arms: Vec<_> = mappings
            .iter()
            .map(|(ident, _, literal)| {
                quote! {
                    #literal => Self::#ident,
                }
            })
            .collect();
        quote! {
            impl ::std::convert::From<#inttype> for #name {
                fn from(value: #inttype) -> Self {
                    match value {
                        #(#literal_arms)*
                        other => Self :: #default_name (value),
                    }
                }
            }
        }
    } else {
        let literal_arms: Vec<_> = mappings
            .iter()
            .map(|(ident, _, literal)| {
                quote! {
                    #literal => Ok(Self::#ident),
                }
            })
            .collect();

        quote! {
            impl ::std::convert::TryFrom<#inttype> for #name {
                type Error = #inttype;

                fn try_from(value: #inttype) -> ::std::result::Result<Self, Self::Error> {
                    match value {
                        #(#literal_arms)*
                        other => Err(value),
                    }
                }
            }
        }
    };

    let display_impl = {
        let matcharms: Vec<_> = mappings
            .iter()
            .map(|(i, _, _)| {
                let istr = i.to_string();
                quote! {
                    Self :: #i => f.write_str(#istr),
                }
            })
            .collect();
        let default_arm = default_variant
            .as_ref()
            .map(|(i, _)| {
                let istr = i.to_string();
                quote!(
                    Self :: #i (value) => write!(f, concat!(#istr, "({})"), value),
                )
            })
            .unwrap_or_else(|| quote!());

        quote! {
            impl ::std::fmt::Display for #name {
                fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> std::fmt::Result {
                    match self {
                        #(#matcharms)*
                        #default_arm
                    }
                }
            }
        }
    };

    let fromstr_impl = {
        let matcharms: Vec<_> = mappings
            .iter()
            .map(|(name, lower_name, _)| {
                quote! {
                    #lower_name => Ok(Self :: #name),
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

        quote! {

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
                            let value: #inttype = other.parse().map_err(|_| #errorname :: UnknownName(s.into()))?;
                            match #name :: try_from(value) {
                                #err_convert_case
                                Ok(v) => Ok(v),
                            }
                        }
                    }
                }
            }
        }
    };

    Ok(quote! {

        #into_literal

        #from_literal

        #display_impl

        #fromstr_impl
    })
}

#[proc_macro_derive(Convert, attributes(value, default))]
pub fn derive_convert(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    match generate_conversions(input) {
        Ok(res) => res.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn convert_to_derive(mut input: DeriveInput) -> Result<DeriveInput, Error> {
    let variants = match &mut input.data {
        Data::Enum(data) => &mut data.variants,
        _ => return Err(Error::new_spanned(input, "input must be an enum")),
    };

    input.attrs.push(parse_quote!(
        #[derive(::enumber::Convert)]
    ));

    for variant in variants.iter_mut() {
        if let Some((_, e)) = variant.discriminant.take() {
            variant.attrs.push(parse_quote!(
                #[value(#e)]
            ));
        }
        if matches!(variant.fields, Fields::Unnamed(_)) {
            variant.attrs.push(parse_quote!(#[default]));
        }
    }

    Ok(input)
}

#[proc_macro_attribute]
pub fn convert(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    match convert_to_derive(input) {
        Ok(res) => quote!(#res).into(),
        Err(err) => err.to_compile_error().into(),
    }
}
