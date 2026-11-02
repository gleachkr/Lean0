//! The export's top-level declarations in Lean syntax, which `lean0 check` lists at the end.
//!
//! A top-level declaration is a theorem, definition, opaque or axiom that no declaration of
//! the export mentions. For an export of some declarations and their dependencies
//! (`lean4export MOD -- NAMES`), these are the named ones. The text comes from nanoda's
//! pretty printer and is for a person to read; nothing is checked through it.

use nanoda_lib::env::Declar;
use nanoda_lib::expr::Expr;
use nanoda_lib::util::ExportFile;
use std::collections::HashSet;

/// The top-level declarations as `kind name : type` (no proofs or values), in export order.
pub fn top_level(export: &ExportFile<'_>) -> Vec<String> {
    export.with_ctx(|ctx| {
        // every constant a type or value mentions (memoized: expressions are DAGs)
        let mut used = HashSet::new();
        let mut seen = HashSet::new();
        let mut stack = Vec::new();
        for d in export.declars.values() {
            stack.push(d.info().ty);
            if let Declar::Theorem { val, .. } | Declar::Definition { val, .. } | Declar::Opaque { val, .. } = d {
                stack.push(*val);
            }
            while let Some(e) = stack.pop() {
                if !seen.insert(e) {
                    continue
                }
                match ctx.read_expr(e) {
                    Expr::Const { name, .. } => {
                        used.insert(name);
                    }
                    Expr::App { fun, arg, .. } => stack.extend([fun, arg]),
                    Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => stack.extend([binder_type, body]),
                    Expr::Let { binder_type, val, body, .. } => stack.extend([binder_type, val, body]),
                    Expr::Proj { structure, .. } => stack.push(structure),
                    Expr::Local { binder_type, .. } => stack.push(binder_type),
                    _ => {}
                }
            }
        }
        let mut out = Vec::new();
        for (name, d) in export.declars.iter() {
            let kind = match d {
                Declar::Theorem { .. } => "theorem",
                Declar::Definition { .. } => "def",
                Declar::Opaque { .. } => "opaque",
                Declar::Axiom { .. } => "axiom",
                _ => continue,
            };
            if !used.contains(name) {
                let lean = crate::statements::lean_name(ctx, *name);
                let ty = ctx.with_pp(|pp| pp.pp_expr(d.info().ty));
                out.push(format!("{kind} {lean} : {ty}"));
            }
        }
        out
    })
}
