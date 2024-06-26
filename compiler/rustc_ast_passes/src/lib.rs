//! The `rustc_ast_passes` crate contains passes which validate the AST in `syntax`
//! parsed by `rustc_parse` and then lowered, after the passes in this crate,
//! by `rustc_ast_lowering`.
//!
//! The crate also contains other misc AST visitors, e.g. `node_count` and `show_span`.

#![allow(internal_features)]
#![doc(rust_logo)]
#![feature(rustdoc_internals)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(iter_is_partitioned)]
#![feature(let_chains)]
#![deny(rustc::untranslatable_diagnostic)]
#![deny(rustc::diagnostic_outside_of_impl)]

pub mod ast_validation;
mod errors;
pub mod feature_gate;
pub mod node_count;
pub mod show_span;

rustc_fluent_macro::fluent_messages! { "../messages.ftl" }
