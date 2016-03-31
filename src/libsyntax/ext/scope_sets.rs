// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implement the sets of scopes algorithm for macro hygiene as described in [1].
//!
//! [1] Matthew Flatt. Binding as Sets of Scopes. POPL '16.
//! http://www.cs.utah.edu/plt/publications/popl16-f.pdf

// TODO document this - interning, other stuff?, repr of inside/outside edge scopes

//! ## Scopes
//!
//! A scope is a contigious section of the source program where a variable can
//! can be named. These are not the same as the scopes used by region inference.
//! Nor the same as syntactic blocks. A scope is used for both items and code in
//! function bodies.
//!
//! A scope itself is just a uniquely identified entity - there are no intrinsic
//! properties of scopes. We have scopes for different purposes, but that is
//! just a property of how the scope is used, not a property of the scope
//! itself.
//!
//! ## Assigning scopes
//!
//! First note that we assign sets of scopes (not individual scopes) to idents.
//!
//! A scope set a is nested in b if a is a subset of a. Such nesting means that
//! a variable declared in b can be named in a (but not vice versa). We use
//! nested scope sets for modelling the scopes due to blocks or `let`
//! statements. We use non-nested scope sets for nested modules or other items
//! (since names in outer modules must be explicitly imported).
//!
//! Function bodies may contain both statements and items. The statements can
//! refer to the items, but not the other way around. Items inside items cannot
//! be referred to by statements outside the outer item. Therefore, there is a
//! tree of nested scopes.
//!
//! To assign scope sets, we walk the AST top down. We track two stacks of scope
//! sets - one for items and one for statements. When we enter a scope, we
//! create a new scope set, push it onto the stack and walk the nodes in the
//! scope. When we're done, we pop the scope set.
//! 
//! The scopes sets we push may be either fresh or nested. In the nested case,
//! they may be nested inside the head of *either* stack, or the heads of both
//! stacks.
//! 
//! The ScopeAssigner sees only idents when assigning scope sets, not whole
//! expressions or items. Therefore it must keep track of whether it is inside
//! item or statement, this is the AssignmentContext. The ident is assigned the
//! an scope set at the head of the appropriate stack, as determined by the
//! current assignment context.

use ast::*;
use fold::{self, Folder};
use ptr::P;
use util::small_vector::SmallVector;

use std::cell::{Cell, RefCell};
use std::collections::HashSet;

// TODO use this for resolution etc., put into TLS like mtwt?

pub struct SetsOfScopes {
    sets: Vec<ScopeSet>,
}

impl SetsOfScopes {
    fn from_sets_table(sets: Vec<ScopeSet>) -> SetsOfScopes {
        SetsOfScopes {
            sets: sets,
        }
    }
}

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct Scope(u32);

impl Scope {
    pub fn is_inside_edge(self) -> bool {
        self.0 & 0x8000_0000 == 0
    }

    pub fn is_outside_edge(self) -> bool {
        self.0 & 0x8000_0000 == 1
    }

    fn inside_edge(self) -> Scope {
        Scope(self.0 | 0x8000_0000)
    }

    fn outside_edge(self) -> Scope {
        Scope(self.0 & !0x8000_0000)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScopeSet(HashSet<Scope>);

// TODO move into sub-mod, separate out folder
/// Assigns scopes to idents in an AST.
pub struct ScopeAssigner {
    // Interned scope sets.
    sets: RefCell<Vec<ScopeSet>>,
    // Stack of scope sets for statements and expressions.
    stmt_stack: RefCell<Vec<u32>>,
    // Stack of scope sets for items.
    item_stack: RefCell<Vec<u32>>,
    next_scope: Cell<u32>,
    context: AssignmentContext,
}

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
enum AssignmentContext {
    Item,
    Stmt,
}

impl ScopeAssigner {
    /// Create a new, empty ScopeAssigner.
    pub fn new() -> ScopeAssigner {
        let mut top = ScopeSet(HashSet::new());
        top.0.insert(Scope(1));
        top.0.insert(Scope(1).outside_edge());
        ScopeAssigner {
            // Set 0 is the empty set of scopes.
            sets: RefCell::new(vec![ScopeSet(HashSet::new()), top]),
            stmt_stack: RefCell::new(vec![1]),
            item_stack: RefCell::new(vec![1]),
            next_scope: Cell::new(2),
            context: AssignmentContext::Item,
        }
    }

    pub fn sets_of_scopes(self) -> SetsOfScopes {
        SetsOfScopes::from_sets_table(self.sets.into_inner())
    }

    /// Execute `f` in item context, then restore the context afterwards.
    fn with_item_context<F, T>(&mut self, f: F) -> T
        where F: FnOnce(&mut ScopeAssigner) -> T
    {
        let old_context = self.context;
        self.context = AssignmentContext::Item;
        let result = f(self);
        self.context = old_context;
        result
    }

    /// Execute `f` in statement context, then restore the context afterwards.
    fn with_stmt_context<F, T>(&mut self, f: F) -> T
        where F: FnOnce(&mut ScopeAssigner) -> T
    {
        let old_context = self.context;
        self.context = AssignmentContext::Stmt;
        let result = f(self);
        self.context = old_context;
        result
    }

    /// Get the current scope set.
    /// Note: clones the result.
    fn get_scope_set(&self, ctxt: u32) -> ScopeSet {
        let sets = self.sets.borrow();
        sets[ctxt as usize].clone()
    }

    /// Create a new scope for this ScopeAssigner.
    /// Just creates the scope, doesn't store it anywhere.
    fn new_scope(&self) -> Scope {
        let result = Scope(self.next_scope.get());
        self.next_scope.set(result.0 + 1);
        result
    }

    /// Create a new scope set nested inside the current item scope set.
    fn nested_item_scope_set(&self) -> ScopeSet {
        let mut set = {
            let sets = self.sets.borrow();
            sets[self.cur_item_set() as usize].clone()
        };
        let scope = self.new_scope();
        set.0.insert(scope);
        set.0.insert(scope.outside_edge());
        set
    }
    /// Create a new scope set nested inside the current statement scope set.
    fn nested_stmt_scope_set(&self) -> ScopeSet {
        let mut set = {
            let sets = self.sets.borrow();
            sets[self.cur_stmt_set() as usize].clone()
        };
        let scope = self.new_scope();
        set.0.insert(scope);
        set.0.insert(scope.outside_edge());
        set
    }
    /// Create a fresh (un-nested) scope set. This is useful for module nesting
    /// (for example), where the new scope cannot name items in outer scopes.
    fn fresh_scope_set(&self) -> ScopeSet {
        let mut set = ScopeSet(HashSet::new());
        let scope = self.new_scope();
        set.0.insert(scope);
        set.0.insert(scope.outside_edge());
        set
    }
    /// A new scope set found by creating a new scope which lives inside both the
    /// current statementt and item scope sets.
    fn nested_merged_scope_set(&self) -> ScopeSet {
        let set_stmt = {
            let sets = self.sets.borrow();
            sets[self.cur_stmt_set() as usize].clone()
        };
        let set_item = {
            let sets = self.sets.borrow();
            sets[self.cur_item_set() as usize].clone()
        };

        let mut set = ScopeSet(set_stmt.0.union(&set_item.0).cloned().collect());

        let scope = self.new_scope();
        set.0.insert(scope);
        set.0.insert(scope.outside_edge());
        set
    }

    /// Push `scope_set` onto the item stack, execute `f`, then pop the item stack.
    fn with_item_set<F, T>(&mut self, scope_set: ScopeSet, f: F) -> T
        where F: FnOnce(&mut ScopeAssigner) -> T
    {
        self.push_item_set(scope_set);
        let result = f(self);
        self.pop_item_set();
        result
    }
    /// Push `scope_set` onto the statement stack, execute `f`, then pop the
    /// statement stack.
    fn with_stmt_set<F, T>(&mut self, scope_set: ScopeSet, f: F) -> T
        where F: FnOnce(&mut ScopeAssigner) -> T
    {
        self.push_stmt_set(scope_set);
        let result = f(self);
        self.pop_stmt_set();
        result
    }

    /// Intern a scope set, producing an identifying u32.
    fn intern_scope_set(&self, set: ScopeSet) -> u32 {
        let mut sets = self.sets.borrow_mut();
        let result = sets.len();
        assert!(result < u32::max_value() as usize);
        let result = result as u32;
        sets.push(set);
        
        result
    }

    // Intern and push the given scope set onto the stack.
    fn push_stmt_set(&self, set: ScopeSet) {
        let interned = self.intern_scope_set(set);

        let mut stmt_stack = self.stmt_stack.borrow_mut();
        stmt_stack.push(interned);
    }
    fn push_item_set(&self, set: ScopeSet) {
        let interned = self.intern_scope_set(set);

        let mut item_stack = self.item_stack.borrow_mut();
        item_stack.push(interned);
    }

    fn pop_stmt_set(&self) {
        let mut stmt_stack = self.stmt_stack.borrow_mut();
        // TODO should be bug
        stmt_stack.pop().unwrap();
    }
    fn pop_item_set(&self) {
        let mut item_stack = self.item_stack.borrow_mut();
        // TODO should be bug
        item_stack.pop().unwrap();
    }

    fn cur_stmt_set(&self) -> u32 {
        let stmt_stack = self.stmt_stack.borrow();
        // TODO Should be bug
        *stmt_stack.last().unwrap()
    }
    fn cur_item_set(&self) -> u32 {
        let item_stack = self.item_stack.borrow();
        // TODO Should be bug
        *item_stack.last().unwrap()
    }

    fn cur_set(&self) -> u32 {
        match self.context {
            AssignmentContext::Item => self.cur_item_set(),
            AssignmentContext::Stmt => self.cur_stmt_set(),
        }
    }

    /// Takes a snapshot of the current state of self. Then runs `f`, then
    /// restores the state of self to the snapshot.
    ///
    /// If you just need to update a single stack with a scope set, then it is
    /// better to use with_item_set or with_stmt_set. Use this method if there
    /// is a more complex situation.
    fn snapshot<F, T>(&mut self, f: F) -> T
        where F: FnOnce(&mut ScopeAssigner) -> T
    {
        struct Snapshot {
            stmt_stack_len: usize,
            item_stack_len: usize,
        }

        let snap = {
            let stmt_stack = self.stmt_stack.borrow();
            let item_stack = self.item_stack.borrow();
            
            Snapshot {
                stmt_stack_len: stmt_stack.len(),
                item_stack_len: item_stack.len(),
            }
        };
        let result = f(self);

        let mut stmt_stack = self.stmt_stack.borrow_mut();
        let mut item_stack = self.item_stack.borrow_mut();

        assert!(snap.stmt_stack_len <= stmt_stack.len());
        assert!(snap.item_stack_len <= item_stack.len());

        stmt_stack.truncate(snap.stmt_stack_len);
        item_stack.truncate(snap.item_stack_len);

        result
    }
}

impl Folder for ScopeAssigner {
    fn fold_ident(&mut self, mut i: Ident) -> Ident {
        // Assign the appropriate scope set to the ident.
        i.ctxt = SyntaxContext(self.cur_set());
        i
    }
    fn fold_mac(&mut self, mut mac: Mac) -> Mac {
        // Assign the appropriate scope set to the macro.
        mac.node.ctxt = SyntaxContext(self.cur_set());
        mac
    }

    fn fold_crate(&mut self, c: Crate) -> Crate {
        let new_scope = self.fresh_scope_set();
        self.with_item_set(new_scope, |this| {
            fold::noop_fold_crate(c, this)
        })
    }
    fn fold_item_kind(&mut self, i: ItemKind) -> ItemKind {
        match i {
            ItemKind::Fn(decl, unsafety, constness, abi, generics, body) => {
                self.snapshot(|this| {
                    // A function creates two new scopes one for nested items
                    // and one for the statements. The statement scope is inside
                    // the item scope.

                    // Note that we fold the declaration and generics inside the
                    // statement scope. This puts them effectively at the top of
                    // that scope and prevents them being named from the items.
                    this.push_item_set(this.nested_item_scope_set());
                    this.push_stmt_set(this.nested_item_scope_set());
                    this.with_stmt_context(|this| {
                        ItemKind::Fn(
                            this.fold_fn_decl(decl),
                            unsafety,
                            constness,
                            abi,
                            this.fold_generics(generics),
                            // Don't call fold_block because that would
                            // introduce another new scope.
                            fold::noop_fold_block(body, this)
                        )
                    })
                })
            }
            ItemKind::Mod(..) | ItemKind::ForeignMod(..) => {
                let new_scope = self.fresh_scope_set();
                self.with_item_set(new_scope, |this| {
                    fold::noop_fold_item_kind(i, this)
                })
            }
            ItemKind::Enum(..) | ItemKind::Ty(..) | ItemKind::Struct(..) | ItemKind::Impl(..) |
            ItemKind::DefaultImpl(..) | ItemKind::Trait(..) => {
                let new_scope = self.nested_item_scope_set();
                self.with_item_set(new_scope, |this| {
                    fold::noop_fold_item_kind(i, this)
                })
            }
            _ => fold::noop_fold_item_kind(i, self),
        }
    }
    fn fold_block(&mut self, b: P<Block>) -> P<Block> {
        self.snapshot(|this| {
            // Entering a block. A block can contain both statements and items,
            // so we must update both stacks. Items can see items declared at
            // outer scopes, but not statements, so that stack is straightforward.
            // Statements can see both statements at outer scope and items in the
            // current scope, so we must merge scopes.
            this.push_item_set(this.nested_item_scope_set());
            this.push_stmt_set(this.nested_merged_scope_set());
            fold::noop_fold_block(b, this)
        })
    }
    fn fold_arm(&mut self, a: Arm) -> Arm {
        let new_scope = self.nested_stmt_scope_set();
        self.with_stmt_set(new_scope, |this| {
            fold::noop_fold_arm(a, this)
        })
    }
    fn fold_expr(&mut self, e: P<Expr>) -> P<Expr> {
        match e.node {
            ExprKind::IfLet(..) | ExprKind::WhileLet(..) | ExprKind::ForLoop(..) => {},
            _ => return e.map(|e| fold::noop_fold_expr(e, self)),
        }

        e.map(|e| Expr {
            id: e.id,
            node: match e.node {
                ExprKind::IfLet(pat, expr, body, els) => {
                    let expr = self.fold_expr(expr);
                    let new_scope = self.nested_stmt_scope_set();
                    self.with_stmt_set(new_scope, |this| {
                        ExprKind::IfLet(this.fold_pat(pat),
                                        expr,
                                        this.fold_block(body),
                                        els.map(|x| this.fold_expr(x)))
                    })
                }
                ExprKind::WhileLet(pat, expr, body, label) => {
                    let expr = self.fold_expr(expr);
                    let new_scope = self.nested_stmt_scope_set();
                    self.with_stmt_set(new_scope, |this| {
                        ExprKind::WhileLet(this.fold_pat(pat),
                                           expr,
                                           this.fold_block(body),
                                           label.map(|i| this.fold_ident(i)))
                    })
                }
                ExprKind::ForLoop(pat, iter, body, label) => {
                    let iter = self.fold_expr(iter);
                    let new_scope = self.nested_stmt_scope_set();
                    self.with_stmt_set(new_scope, |this| {
                        ExprKind::ForLoop(this.fold_pat(pat),
                                          iter,
                                          this.fold_block(body),
                                          label.map(|i| this.fold_ident(i)))
                    })
                }
                _ => unreachable!(),
            },
            span: e.span,
            attrs: e.attrs,
        })
    }

    fn fold_local(&mut self, l: P<Local>) -> P<Local> {
        self.push_stmt_set(self.nested_stmt_scope_set());
        fold::noop_fold_local(l, self)
        // Locals are popped at the end of the block (see fold_block).
    }

    fn fold_decl(&mut self, d: P<Decl>) -> SmallVector<P<Decl>> {
        if let DeclKind::Item(..) = d.node {
            self.with_item_context(|this| fold::noop_fold_decl(d, this))
        } else {
            fold::noop_fold_decl(d, self)
        }
    }

    fn fold_trait_item(&mut self, i: TraitItem) -> SmallVector<TraitItem> {
        if let TraitItemKind::Method(sig, body) = i.node {
            let TraitItem { id, ident, attrs, span, .. } = i;
            // See comments on functions in fold_item.
            let ident = self.fold_ident(ident);
            self.snapshot(move |this| {
                this.push_item_set(this.nested_item_scope_set());
                this.push_stmt_set(this.nested_item_scope_set());
                this.with_stmt_context(move |this| {
                    SmallVector::one(TraitItem {
                        id: id,
                        ident: ident,
                        attrs: attrs,
                        node: TraitItemKind::Method(MethodSig {
                                generics: this.fold_generics(sig.generics),
                                abi: sig.abi,
                                explicit_self: this.fold_explicit_self(sig.explicit_self),
                                unsafety: sig.unsafety,
                                constness: sig.constness,
                                decl: this.fold_fn_decl(sig.decl)
                            },
                            body.map(|b| fold::noop_fold_block(b, this))),
                        span: span,
                    })
                })
            })
        } else {
            fold::noop_fold_trait_item(i, self)
        }
    }

    fn fold_impl_item(&mut self, i: ImplItem) -> SmallVector<ImplItem> {
        if let ImplItemKind::Method(sig, body) = i.node {
            let ImplItem { id, ident, attrs, vis, defaultness, span, .. } = i;
            // See comments on functions in fold_item.
            let ident = self.fold_ident(ident);
            self.snapshot(move |this| {
                this.push_item_set(this.nested_item_scope_set());
                this.push_stmt_set(this.nested_item_scope_set());
                this.with_stmt_context(move |this| {
                    SmallVector::one(ImplItem {
                        id: id,
                        ident: ident,
                        attrs: attrs,
                        vis: vis,
                        defaultness: defaultness,
                        node: ImplItemKind::Method(MethodSig {
                                generics: this.fold_generics(sig.generics),
                                abi: sig.abi,
                                explicit_self: this.fold_explicit_self(sig.explicit_self),
                                unsafety: sig.unsafety,
                                constness: sig.constness,
                                decl: this.fold_fn_decl(sig.decl)
                            },
                            fold::noop_fold_block(body, this)),
                        span: span,
                    })
                })
            })
        } else {
            fold::noop_fold_impl_item(i, self)
        }
    }
}

#[cfg(test)]
mod test {
    use ast::*;
    use codemap::Span;
    use fold::Folder;
    use parse;
    use ptr::P;
    use visit::Visitor;
    
    use super::{ScopeAssigner, ScopeSet, Scope};

    use std::collections::HashSet;

    // Utility for finding idents by name.
    struct IdentFinder {
        to_find: &'static str,
        found: Vec<Ident>,
    }

    impl<'v> Visitor<'v> for IdentFinder {
        fn visit_ident(&mut self, _span: Span, ident: Ident) {
            let name = ident.name.as_str();
            if &*name == self.to_find {
                self.found.push(ident);
            }
        }
    }

    // Find all idents with unhygienic name needle.
    fn find_idents(needle: &'static str, item: &Item) -> Vec<Ident> {
        let mut finder = IdentFinder {
            to_find: needle,
            found: Vec::new(),
        };

        finder.visit_item(item);
        finder.found
    }

    // Find a single ident called needle, panics if there is not exactly one result.
    fn find_ident(needle: &'static str, item: &Item) -> Ident {
        let result = find_idents(needle, item);
        assert!(result.len() == 1, "{}: length: {}, expected 1", needle, result.len());
        result[0]
    }

    fn mk_scope_set(scopes: &[u32]) -> ScopeSet {
        let mut result = ScopeSet(HashSet::new());
        for &s in scopes.iter() {
            result.0.insert(Scope(s));
            result.0.insert(Scope(s).outside_edge());
        }
        result
    }

    fn mk_item_and_assign(sa: &mut ScopeAssigner, source: &str) -> P<Item> {
        let ps = parse::ParseSess::new();
        let item = parse::parse_item_from_source_str("<source>".to_owned(),
                                                     source.to_owned(),
                                                     Vec::new(),
                                                     &ps).unwrap().unwrap();

        let mut items = sa.fold_item(item);
        items.pop().unwrap()
    }

    fn assert_scopes(sa: &mut ScopeAssigner, item: &Item, name: &'static str, scopes: &[u32]) {
        let ident = find_ident(name, item);
        debug!("{}: {:?}", name, sa.get_scope_set(ident.ctxt.0));
        assert_eq!(sa.get_scope_set(ident.ctxt.0), mk_scope_set(scopes));        
    }

    // TODO can we model scopes for tests better?

    #[test]
    fn test_item() {
        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa, "mod foo { fn bar() {} }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "bar", &[2]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa, "mod foo { type Foo<T> = Bar<X>; }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "Foo", &[2]);
        assert_scopes(&mut sa, &item, "Bar", &[2, 3]);
        assert_scopes(&mut sa, &item, "T", &[2, 3]);
        assert_scopes(&mut sa, &item, "X", &[2, 3]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa, "mod foo { mod bar { fn baz() {} } fn qux() {} }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "bar", &[2]);
        assert_scopes(&mut sa, &item, "baz", &[3]);
        assert_scopes(&mut sa, &item, "qux", &[2]);
    }

    #[test]
    fn test_fn() {
        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa, "fn foo() { x }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa, "fn foo<U>(y: T) { fn bar() {} x }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "U", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "T", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "bar", &[1, 2]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                fn bar() {
                    fn baz() { z }
                    y
                }
                x;
                fn qux() { w }
            }");
        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "bar", &[1, 2]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "baz", &[1, 2, 4]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 4, 5]);
        assert_scopes(&mut sa, &item, "z", &[1, 2, 4, 6, 7]);
        assert_scopes(&mut sa, &item, "qux", &[1, 2]);
        assert_scopes(&mut sa, &item, "w", &[1, 2, 8, 9]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                fn bar() {}
                {
                    x;
                    fn baz() { y }
                }
            }");
        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "bar", &[1, 2]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 6, 7]);
        assert_scopes(&mut sa, &item, "baz", &[1, 2, 6]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 6, 8, 9]);
    }

    #[test]
    fn test_method() {
        // let mut sa = ScopeAssigner::new();
        // let item = mk_item_and_assign(&mut sa,
        //     "trait Tr<U> {
        //         fn foo<V>(y: T) {
        //             fn bar() {}

        //             x
        //         }
        //     }");

        // assert_scopes(&mut sa, &item, "Tr", &[1]);
        // assert_scopes(&mut sa, &item, "U", &[1, 2]);
        // assert_scopes(&mut sa, &item, "foo", &[1, 2]);
        // assert_scopes(&mut sa, &item, "V", &[1, 2, 3, 4]);
        // assert_scopes(&mut sa, &item, "y", &[1, 2, 3, 4]);
        // assert_scopes(&mut sa, &item, "T", &[1, 2, 3, 4]);
        // assert_scopes(&mut sa, &item, "bar", &[1, 2, 3]);
        // assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "impl<U> I for J {
                fn foo<V>(y: T) {
                    fn bar() {}

                    x
                }
            }");

        assert_scopes(&mut sa, &item, "I", &[1, 2]);
        assert_scopes(&mut sa, &item, "J", &[1, 2]);
        assert_scopes(&mut sa, &item, "U", &[1, 2]);
        assert_scopes(&mut sa, &item, "foo", &[1, 2]);
        assert_scopes(&mut sa, &item, "V", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "T", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "bar", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);
    }    

    #[test]
    fn test_let() {
        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                a;
                let x = 42;
                let y = 42;
                let z = 42;
                b
            }");
        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "a", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3, 4, 5]);
        assert_scopes(&mut sa, &item, "z", &[1, 2, 3, 4, 5, 6]);
        assert_scopes(&mut sa, &item, "b", &[1, 2, 3, 4, 5, 6]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                let x = 42;
                {
                    a;
                    let y = 42;
                    {
                        let z = 42;
                    }
                    b;
                }
                c;
                {
                    let w = 42;
                    d;
                }
                e;
            }");
        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "a", &[1, 2, 3, 4, 5, 6]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3, 4, 5, 6, 7]);
        assert_scopes(&mut sa, &item, "z", &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
        assert_scopes(&mut sa, &item, "b", &[1, 2, 3, 4, 5, 6, 7]);
        assert_scopes(&mut sa, &item, "c", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "w", &[1, 2, 3, 4, 11, 12, 13]);
        assert_scopes(&mut sa, &item, "d", &[1, 2, 3, 4, 11, 12, 13]);
        assert_scopes(&mut sa, &item, "e", &[1, 2, 3, 4]);

        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa, "mod foo { fn bar() { let x = 42; } }");
        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "bar", &[2]);
        assert_scopes(&mut sa, &item, "x", &[2, 3, 4, 5]);
    }

    #[test]
    fn test_if_let() {
        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                if let x = y {
                    z
                }
            }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "z", &[1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_while_let() {
        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                while let x = y {
                    z
                }
            }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "z", &[1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_for() {
        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                for x in y {
                    z
                }
            }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "z", &[1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_match() {
        let mut sa = ScopeAssigner::new();
        let item = mk_item_and_assign(&mut sa,
            "fn foo() {
                match z {
                    x => y,
                    w => { u }
                    a if b => {},
                }
            }");

        assert_scopes(&mut sa, &item, "foo", &[1]);
        assert_scopes(&mut sa, &item, "z", &[1, 2, 3]);
        assert_scopes(&mut sa, &item, "x", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "y", &[1, 2, 3, 4]);
        assert_scopes(&mut sa, &item, "w", &[1, 2, 3, 5]);
        assert_scopes(&mut sa, &item, "u", &[1, 2, 3, 5, 6, 7]);
        assert_scopes(&mut sa, &item, "a", &[1, 2, 3, 8]);
        assert_scopes(&mut sa, &item, "b", &[1, 2, 3, 8]);
    }
}
