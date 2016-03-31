// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use syntax::ast::{self, Name, Ident, NodeId};
use syntax::ext::scope_sets::{SetsOfScopes};
use syntax::visit;

use std::collections::HashMap;
use std::collections::hash_map::Entry;

/// TODO document

// TODO binding table per physical scope.

/// Represents a single binding table which maps names to scope sets and NodeIds
pub struct BindingTable {
    types: HashMap<Name, Bindings>,
    values: HashMap<Name, Bindings>,
}

impl BindingTable {
    fn new() -> BindingTable {
        BindingTable {
            types: HashMap::new(),
            values: HashMap::new(),
        }
    }

    pub fn insert_value(&mut self, ident: Ident, def: NodeId, local: bool) {
        match self.values.entry(ident.name) {
            Entry::Vacant(mut ve) => {
                // TODO factor out new fn
                ve.insert(Bindings(vec![Binding::new(ident.ctxt.0, def, local)]));
            }
            Entry::Occupied(ref mut oe) => {
                let bindings = &mut oe.get_mut().0;
                for b in bindings.iter() {
                    if b.scopes == ident.ctxt.0 {
                        if b.def != def {
                            panic!("TODO error, multiple defs in same scope");
                        }

                        assert!(b.local == local, "TODO can this fail?");
                        return;
                    }
                }
                bindings.push(Binding::new(ident.ctxt.0, def, local));
            }
        }
    }

    fn insert() {
        // TODO
    }
}

// A set of pairs of bindings for a name, each binding is an interned scope set
// and a node in the AST.
struct Bindings(Vec<Binding>);

struct Binding {
    scopes: u32,
    def: NodeId,
    local: bool,
}

impl Binding {
    fn new(scopes: u32, def: NodeId, local: bool) -> Binding {
        Binding {
            scopes: scopes,
            def: def,
            local: local,
        }
    }
}

/// Visits the AST building binding tables.
pub struct BindingBuilder<'a> {
    scopes: &'a SetsOfScopes,
    bindings: BindingTable,
}

impl<'a> BindingBuilder<'a> {
    pub fn from_scopes(scopes: &'a SetsOfScopes) -> BindingBuilder {
        BindingBuilder {
            scopes: scopes,
            bindings: BindingTable::new(),
        }
    }
}

impl<'a, 'v> visit::Visitor<'v> for BindingBuilder<'a> {
    fn visit_pat(&mut self, p: &'v ast::Pat) {
        if let Some(ident) = p.get_binding_name() {
            // TODO not always a local, perhaps this is not the best way to handle locals?
            self.bindings.insert_value(ident, p.id, true);
        }

        visit::walk_pat(self, p)
    }

    fn visit_item(&mut self, i: &'v ast::Item) {
        visit::walk_item(self, i)
    }

    fn visit_foreign_item(&mut self, i: &'v ast::ForeignItem) {
        visit::walk_foreign_item(self, i)
    }
    
    fn visit_generics(&mut self, g: &'v ast::Generics) {
        let idents = g.get_binding_names();
        // TODO need node ids

        visit::walk_generics(self, g)
    }

    // TODO
    // !!?? what about match arm patterns?
    // ?? name resolution stores refs to Defs, not node ids - should I do that? yes, later
    //    Need to move front into middle
    // ?? privacy - skip at first
    // dup checking (one name, same scope sets, different node ids)
    // names for items (every item kind, include use)
    //    ?? globs
    // names for local variables, args - both patterns?
}

trait BindingName {
    fn get_binding_name(&self) -> Option<Ident>;
}

impl BindingName for ast::Pat {
    fn get_binding_name(&self) -> Option<Ident> {
        if let ast::PatKind::Ident(_, ident, _) = self.node {
            Some(ident.node)
        } else {
            None
        }
    }
}

impl BindingName for ast::ForeignItem {
    fn get_binding_name(&self) -> Option<Ident> {
        Some(self.ident)
    }
}

impl BindingName for ast::Item {
    fn get_binding_name(&self) -> Option<Ident> {
        match self.node {
            ast::ItemKind::Static(..) |
            ast::ItemKind::Const(..) |
            ast::ItemKind::Fn(..) |
            ast::ItemKind::Mod(..) |
            ast::ItemKind::ForeignMod(..) |
            ast::ItemKind::Ty(..) |
            ast::ItemKind::Enum(..) |
            ast::ItemKind::Struct(..) |
            ast::ItemKind::Trait(..) => Some(self.ident),
            ast::ItemKind::Impl(..) |
            ast::ItemKind::DefaultImpl(..) => None,
            // TODO special case
            ast::ItemKind::Use(..) => None,
            ast::ItemKind::Mac(..) => panic!("macros should have been expanded by now"),
            // extern crate has weird lookup rules since it is available in
            // submodules, whereas submodules don't usually have this behaviour.
            ast::ItemKind::ExternCrate(..) => panic!("TODO"),
        }
    }
}

trait BindingNames {
    fn get_binding_names(&self) -> Vec<Ident>;
}

impl BindingNames for ast::Generics {
    fn get_binding_names(&self) -> Vec<Ident> {
        // TODO lifetimes are unhygienic for now
        // for l in self.lifetimes.iter() {
        //     l.lifetime.name
        // }

        self.ty_params.iter().map(|t| t.ident).collect()
    }
}

impl BindingNames for ast::ViewPath {
    fn get_binding_names(&self) -> Vec<Ident> {
        match self.node {
            ast::ViewPath_::ViewPathSimple(ident, _) => vec![ident],
            ast::ViewPath_::ViewPathGlob(_) => vec![],
            ast::ViewPath_::ViewPathList(_, ref items) => items.iter().filter_map(|i| match i.node {
                ast::PathListItemKind::Ident { name, rename: None, .. } => Some(name),
                ast::PathListItemKind::Ident { rename: Some(name), .. } => Some(name),
                ast::PathListItemKind::Mod { rename: None, .. } => None,
                ast::PathListItemKind::Mod { rename: Some(name), .. } => Some(name),
            }).collect(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use syntax::ext::scope_sets::{ScopeAssigner, SetsOfScopes};
    use syntax::ast::*;
    use syntax::fold::Folder;
    use syntax::parse;
    use syntax::ptr::P;
    use syntax::visit::Visitor;

    use std::collections::hash_map::Entry;

    fn mk_item_and_scopes(source: &str) -> (P<Item>, SetsOfScopes) {
        let ps = parse::ParseSess::new();
        let item = parse::parse_item_from_source_str("<source>".to_owned(),
                                                     source.to_owned(),
                                                     Vec::new(),
                                                     &ps).unwrap().unwrap();

        let mut sa = ScopeAssigner::new();
        let mut items = sa.fold_item(item);
        (items.pop().unwrap(), sa.sets_of_scopes())
    }

    fn count_values(bindings: &mut BindingTable, name: &str) -> usize {
        let name = ::syntax::parse::token::intern(name);
        match bindings.values.entry(name) {
            Entry::Vacant(_) => 0,
            Entry::Occupied(ref oe) => oe.get().0.len()
        }
    }

    #[test]
    fn test_binding_fn() {
        let (item, scopes) = mk_item_and_scopes("fn foo(x: u32) {}");
        let mut builder = BindingBuilder::from_scopes(&scopes);
        builder.visit_item(&item);

        // TODO test - we expect x in the bindings table (also foo, later)
        assert!(count_values(&mut builder.bindings, "x") == 1);
    }
}
