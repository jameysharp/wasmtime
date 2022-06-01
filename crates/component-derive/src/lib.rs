use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse_macro_input, parse_quote, Data, DeriveInput, Error, Result};

#[proc_macro_derive(ComponentEnum)]
pub fn component_enum(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    expand_enum(input)
        .unwrap_or_else(Error::into_compile_error)
        .into()
}

fn expand_enum(input: DeriveInput) -> Result<TokenStream> {
    let private = quote!(wasmtime::component::private);

    let name = input.ident;

    let body = if let Data::Enum(body) = input.data {
        body
    } else {
        return Err(Error::new(name.span(), "not an enum"));
    };

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let variants = body.variants.len();
    let wasm_type = if variants <= u8::MAX as usize {
        quote!(u8)
    } else if variants <= u16::MAX as usize {
        quote!(u16)
    } else if variants <= u32::MAX as usize {
        quote!(u32)
    } else {
        return Err(Error::new(name.span(), "too many variants"));
    };

    let mut lower = TokenStream::new();
    let mut lift = TokenStream::new();
    for (idx, variant) in body.variants.iter().enumerate() {
        if let syn::Fields::Unit = variant.fields {
        } else {
            return Err(Error::new_spanned(&variant.fields, "no fields allowed"));
        }

        if let Some((_, value)) = &variant.discriminant {
            return Err(Error::new_spanned(
                value,
                "explicit discriminant not allowed",
            ));
        }

        let idx = idx as u32;
        let ident = &variant.ident;
        lower.extend(quote!(#name::#ident => #idx,));
        lift.extend(quote!(#idx => Ok(#name::#ident),));
    }

    let expanded = quote! {
        unsafe impl #impl_generics wasmtime::component::ComponentValue for #name #ty_generics #where_clause {
            type Lower = wasmtime::ValRaw;

            fn typecheck(
                ty: &#private::InterfaceType,
                types: &#private::ComponentTypes,
                _op: wasmtime::component::Op,
            ) -> #private::anyhow::Result<()> {
                match ty {
                    #private::InterfaceType::Enum(t) => {
                        let variants = types[*t].names.len();
                        if variants != #variants {
                            #private::anyhow::bail!("expected enum with {} names, found {} names", #variants, variants);
                        }
                        Ok(())
                    }
                    other => #private::anyhow::bail!("expected `enum` found `{}`", #private::desc(other)),
                }
            }

            fn lower<T>(
                &self,
                _store: &mut wasmtime::StoreContextMut<T>,
                _func: &wasmtime::component::Func,
                dst: &mut std::mem::MaybeUninit<Self::Lower>,
            ) -> #private::anyhow::Result<()> {
                dst.write(wasmtime::ValRaw::i32(match self { #lower } as i32));
                Ok(())
            }

            #[inline]
            fn size() -> usize {
                #wasm_type::size()
            }

            #[inline]
            fn align() -> u32 {
                #wasm_type::align()
            }

            fn store<T>(&self, memory: &mut #private::MemoryMut<'_, T>, offset: usize) -> #private::anyhow::Result<()> {
                (match self { #lower } as #wasm_type).store(memory, offset)
            }

            #[inline]
            fn lift(_store: &#private::StoreOpaque, _func: &wasmtime::component::Func, src: &Self::Lower) -> #private::anyhow::Result<Self> {
                match src.get_i32() as u32 {
                    #lift
                    _ => #private::anyhow::bail!("invalid {} value", stringify!(#name)),
                }
            }

            #[inline]
            fn load(mem: &#private::Memory, bytes: &[u8]) -> #private::anyhow::Result<Self> {
                match #wasm_type::load(mem, bytes)? as u32 {
                    #lift
                    _ => #private::anyhow::bail!("invalid {} value", stringify!(#name)),
                }
            }

        }
    };

    Ok(expanded)
}

fn add_trait_bounds(mut generics: syn::Generics) -> syn::Generics {
    for param in &mut generics.params {
        if let syn::GenericParam::Type(ref mut type_param) = *param {
            type_param
                .bounds
                .push(parse_quote!(wasmtime::component::ComponentValue));
        }
    }
    generics
}
