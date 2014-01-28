// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// TODO explain a bit more maybe
// output data for analysis by the dxr rust plugin

use driver::driver::CrateAnalysis;
use driver::session::Session;
use middle::ty;
use middle::typeck;

use syntax::ast;
use syntax::ast::*;
use syntax::ast_map::*;
use syntax::attr;
use syntax::codemap::*;
use syntax::diagnostic;
use syntax::parse::lexer;
use syntax::parse::lexer::{reader, StringReader};
use syntax::parse::token::{get_ident_interner,ident_to_str,is_keyword,keywords,is_ident,Token,EOF,EQ,LPAREN,COLON,LT,GT,LBRACE,COMMA,to_str};
use syntax::visit;
use syntax::visit::Visitor;
use syntax::print::pprust::{path_to_str,ty_to_str};

use std::io;
use std::io::File;
use std::io::fs;
use std::os;
use std::path::Path;


struct DxrVisitor<'l> {
    sess: Session,
    analysis: &'l CrateAnalysis,

    collected_paths: ~[(NodeId, ast::Path, bool)],

    // output file
    out: ~Writer,
}

impl <'l> DxrVisitor<'l> {
    fn dump_crate_info(&mut self, name: &str, crate: &ast::Crate) {
        // the current crate
        write!(self.out, "{}", self.crate_str(&crate.span, name));

        // dump info about all the external crates referenced from this crate
        self.analysis.ty_cx.cstore.iter_crate_data(|n, cmd|
            {
                write!(self.out, "{}", self.external_crate_str(&crate.span, cmd.name, n))
            });
        write!(self.out, "end_external_crates\n");
    }

    // standard string for extents/location
    // sub_span starts at span.lo, so we need to adjust the positions etc.
    // if sub_span is None, we don't need to adjust.
    fn extent_str(&self, span:&Span, sub_span: Option<&Span>) -> ~str {
        let cm = self.sess.codemap;
        let base_loc = cm.lookup_char_pos(span.lo);
        let base_pos: CharPos = cm.bytepos_to_local_charpos(BytePos(*span.lo - *base_loc.file.start_pos));

        let mut lo_loc = base_loc;
        let mut hi_loc = base_loc;
        let mut lo_pos: uint;
        let mut hi_pos: uint;

        match sub_span {
            Some(ss) => {
                let sub_lo = cm.lookup_char_pos(ss.lo);
                let sub_hi = cm.lookup_char_pos(ss.hi);
                lo_loc.line = base_loc.line + sub_lo.line - 1;
                lo_loc.col = CharPos(*base_loc.col + *sub_lo.col);
                hi_loc.line = base_loc.line + sub_hi.line - 1;
                hi_loc.col = CharPos(*base_loc.col + *sub_hi.col);
                lo_pos = *base_pos + *cm.bytepos_to_local_charpos(BytePos(*ss.lo - *sub_lo.file.start_pos));
                hi_pos = *base_pos + *cm.bytepos_to_local_charpos(BytePos(*ss.hi - *sub_hi.file.start_pos));
            },
            None => {
                hi_loc = cm.lookup_char_pos(span.hi);
                lo_pos = *base_pos;
                let cph: CharPos = cm.bytepos_to_local_charpos(BytePos(*span.hi - *hi_loc.file.start_pos));
                hi_pos = *cph;
            }
        }

        return format!("file_name,{},file_line,{},file_col,{},extent_start,{},file_line_end,{},file_col_end,{},extent_end,{}",
                       lo_loc.file.name, lo_loc.line, *lo_loc.col, lo_pos,
                       hi_loc.line, *hi_loc.col, hi_pos);
    }

    fn retokenise_span(&self, span: &Span) -> @mut StringReader {
        // sadness - we don't have spans for sub-expressions nor access to the tokens
        // so in order to get extents for the function name itself (which dxr expects)
        // we need to re-tokenise the fn definition
        let cm = self.sess.codemap;
        let handler = diagnostic::mk_handler(None);
        let handler = diagnostic::mk_span_handler(handler, cm);

        let src_str = match cm.span_to_snippet(*span) {
            Some(s) => s,
            None => ~"",
        };
        let filemap = cm.new_filemap(@"<anon>",
                                     src_str.to_managed());
        lexer::new_string_reader(handler, filemap)
    }

    // Re-parses a path and returns the span for the last identifier in the path
    fn span_for_name(&self, span: &Span) -> Span {
        // If we can't find a name to select, select the entire expression. This might
        // screw things up later in DXR because we might overlap with a sub-expression.
        // But at least DXR will get all hissy then.
        let mut result = *span;

        let toks = self.retokenise_span(span);
        loop {
            let ts = toks.next_token();
            if ts.tok == EOF {
                return result
            }
            if is_ident(&ts.tok) || is_keyword(keywords::Self, &ts.tok) {
                result = ts.sp;
            }
        }
    }

    fn span_for_ident(&self, span: &Span) -> Span {
        //! Return the span for the first identifier in the path.
        let toks = self.retokenise_span(span);
        loop {
            let ts = toks.next_token();
            if ts.tok == EOF {
                return *span;
            }
            if is_ident(&ts.tok) || is_keyword(keywords::Self, &ts.tok) {
                return ts.sp;
            }
        }
    }

    fn sub_span_before_token(&self, span: &Span, tok: Token) -> Option<Span> {
        let toks = self.retokenise_span(span);
        let mut prev = toks.next_token();
        loop {
            if prev.tok == EOF {
                return None;
            }
            let next = toks.next_token();
            if next.tok == tok {
                return Some(prev.sp);
            }
            prev = next;
        }
    }

    // this is so bad...
    fn sub_span_after_token(&self, span: &Span, tok: Token) -> Span {
        let mut new_span = span.clone();
        while new_span.lo < new_span.hi {
            if self.sess.codemap.span_to_snippet(Span{
                    lo:new_span.lo, hi:new_span.lo+BytePos(1),
                    expn_info: new_span.expn_info}).unwrap() == to_str(get_ident_interner(), &tok) {
                return new_span;
            }
            new_span.lo = new_span.lo + BytePos(1);
        }
        return new_span;
    }

    fn sub_span_after_keyword(&self, span: &Span, keyword: keywords::Keyword) -> Option<Span> {
        let toks = self.retokenise_span(span);
        loop {
            let ts = toks.next_token();
            if ts.tok == EOF {
                return None;
            }
            if is_keyword(keyword, &ts.tok) {
                let ts = toks.next_token();
                return Some(ts.sp);
            }
        }
    }

    fn sub_span_for_keyword(&self, span: &Span, keyword: keywords::Keyword) -> Option<Span> {
        let toks = self.retokenise_span(span);
        loop {
            let ts = toks.next_token();
            if ts.tok == EOF {
                return None;
            }
            if is_keyword(keyword, &ts.tok) {
                return Some(ts.sp);
            }
        }
    }

    fn spans_for_path_segments(&self, path: &ast::Path) -> ~[Span] {
        let mut result: ~[Span] = ~[];

        let toks = self.retokenise_span(&path.span);
        // Only track spans for tokens outside of <...> so we don't get type vars
        let mut bracket_count = 0;
        loop {
            let ts = toks.next_token();
            if ts.tok == EOF {
                return result
            }
            if ts.tok == LT {
                bracket_count += 1;
            }
            if ts.tok == GT {
                bracket_count -= 1;
            }
            if is_ident(&ts.tok) &&
               bracket_count == 0 {
                result.push(ts.sp);
            }
        }
    }

    fn process_path_prefixes(&self, path: &ast::Path) -> ~[(Span, ~str)] {
        let spans = self.spans_for_path_segments(path);

        if spans.len() != path.segments.len() {
            println!("Miscalculated spans for path '{}'. Found {} spans, expected {}",
                     path_to_str(path, get_ident_interner()), spans.len(), path.segments.len());
            return ~[];
        }

        let mut result = ~[];
        for i in range(0, path.segments.len()) {
            let mut segs = path.segments.to_owned();
            segs.truncate(i+1);
            let sub_path = ast::Path{span: spans[i],
                                     global: path.global,
                                     segments: segs};

            let qualname = path_to_str(&sub_path, get_ident_interner());
            result.push((spans[i], qualname));
        }
        result
    }

    fn write_sub_paths(&mut self, path: &ast::Path) {
        let sub_paths = self.process_path_prefixes(path);
        for &(ref span, ref qualname) in sub_paths.iter() {
            let sub_mod_str = self.sub_mod_ref_str(&path.span, span, *qualname);
            write!(self.out, "{}", sub_mod_str);                                                                        
        }        
    }

    // As write_sub_paths, but does not process the last ident in the path (assuming it
    // will be processed elsewhere).
    fn write_sub_paths_truncated(&mut self, path: &ast::Path) {
        let sub_paths = self.process_path_prefixes(path);
        let len = sub_paths.len();
        let sub_paths = sub_paths.slice(0, len-1);
        for &(ref span, ref qualname) in sub_paths.iter() {
            let sub_mod_str = self.sub_mod_ref_str(&path.span, span, *qualname);
            write!(self.out, "{}", sub_mod_str);                                                                        
        }
    }

    // As write_sub_paths, but expects a path of the form module_path::trait::method
    // Where trait could actually be a struct too.
    fn write_sub_path_trait_truncated(&mut self, path: &ast::Path) {
        let sub_paths = self.process_path_prefixes(path);
        let len = sub_paths.len();
        let sub_paths = sub_paths.slice(0, len-1);
        if len == 1 {
            return;
        }
        let (ref span, ref qualname) = sub_paths[len-2];
        let sub_type_str = self.sub_type_ref_str(&path.span, span, *qualname);
        write!(self.out, "{}", sub_type_str);                                                                        
        let sub_paths = sub_paths.slice(0, len-2);
        for &(ref span, ref qualname) in sub_paths.iter() {
            let sub_mod_str = self.sub_mod_ref_str(&path.span, span, *qualname);
            write!(self.out, "{}", sub_mod_str);                                                                        
        }
    }

    // value is the initialising expression of the variable if it is not mut, otherwise "".
    fn variable_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, value: &str) -> ~str {
        // XXX getting a fully qualified name for a variable is hard because in
        // the local case they can be overridden in one block and there is no nice
        // way to refer to a scope in english, so we just hack it by appending the
        // variable def's node id
        format!("variable,{},id,{},name,{},qualname,{},value,\"{}\"\n",
                self.extent_str(span, Some(sub_span)), id, name,
                name + "$" + id.to_str(), value)
    }

    // formal parameters
    fn formal_str(&self, span: &Span, sub_span: &Span, id: NodeId, fn_name: &str, name: &str) -> ~str {
        format!("variable,{},id,{},name,{},qualname,{}\n",
                self.extent_str(span, Some(sub_span)), id, name,
                fn_name + "::" + name)
    }
    fn enum_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str) -> ~str {
        format!("enum,{},id,{},qualname,{}\n",
                self.extent_str(span, Some(sub_span)), id, name)
    }

    fn tuple_variant_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, qualname: &str, val: &str) -> ~str {
        format!("variant,{},id,{},name,{},qualname,{},value,\"{}\"\n",
            self.extent_str(span, Some(sub_span)), id, name, qualname, val)
    }

    // value is the initialising expression of the static if it is not mut, otherwise "".
    fn struct_variant_str(&self, span: &Span, sub_span: &Span, id: NodeId, ctor_id: NodeId, name: &str, val: &str) -> ~str {
        format!("variant_struct,{},id,{},ctor_id,{},qualname,{},value,\"{}\"\n",
                self.extent_str(span, Some(sub_span)), id, ctor_id, name, val)
    }

    fn static_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, qualname: &str, value: &str) -> ~str {
        format!("variable,{},id,{},name,{},qualname,{},value,\"{}\"\n",
                self.extent_str(span, Some(sub_span)), id, name, qualname, value)
    }

    fn field_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, qualname: &str) -> ~str {
        format!("variable,{},id,{},name,{},qualname,{}\n",
                self.extent_str(span, Some(sub_span)), id, name, qualname)
    }

    fn fn_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str) -> ~str {
        format!("function,{},qualname,{},id,{}\n",
                self.extent_str(span, Some(sub_span)), name, id)
    }

    fn method_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, decl_id: Option<DefId>, scope_id: NodeId) -> ~str {
        match decl_id {
            Some(decl_id) => format!("function,{},qualname,{},id,{},declid,{},declidcrate,{},scopeid,{}\n",
                self.extent_str(span, Some(sub_span)), name, id, decl_id.node, decl_id.crate, scope_id),
            None => format!("function,{},qualname,{},id,{},scopeid,{}\n",
                self.extent_str(span, Some(sub_span)), name, id, scope_id),
        }
    }

    fn method_decl_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, scope_id: NodeId) -> ~str {
        format!("method_decl,{},qualname,{},id,{},scopeid,{}\n",
                self.extent_str(span, Some(sub_span)), name, id, scope_id)
    }

    fn struct_str(&self, span: &Span, sub_span: &Span, id: NodeId, ctor_id: NodeId, name: &str, val: &str) -> ~str {
        format!("struct,{},id,{},ctor_id,{},qualname,{},value,\"{}\"\n",
                self.extent_str(span, Some(sub_span)), id, ctor_id, name, val)
    }

    fn trait_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str) -> ~str {
        format!("trait,{},id,{},qualname,{}\n",
                self.extent_str(span, Some(sub_span)), id, name)
    }

    fn impl_str(&self, span: &Span, sub_span: &Span, id: NodeId, ref_id: DefId) -> ~str {
        format!("impl,{},id,{},refid,{},refidcrate,{}\n",
                self.extent_str(span, Some(sub_span)), id, ref_id.node, ref_id.crate)        
    }

    fn mod_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, parent: NodeId, filename: &str) -> ~str {
        format!("module,{},id,{},qualname,{},scopeid,{},def_file,{}\n",
                self.extent_str(span, Some(sub_span)), id, name, parent, filename)
    }

    fn mod_alias_str(&self, span: &Span, sub_span: &Span, id: NodeId, mod_id: DefId, name: &str) -> ~str {
        format!("module_alias,{},id,{},refid,{},refidcrate,{},name,{}\n",
                self.extent_str(span, Some(sub_span)), id, mod_id.node, mod_id.crate, name)
    }

    fn extern_mod_str(&self, span: &Span, sub_span: &Span, id: NodeId, name: &str, loc: &str) -> ~str {
        let cstore = self.analysis.ty_cx.cstore;
        let cnum = match cstore.find_extern_mod_stmt_cnum(id) {
            Some(cnum) => cnum,
            None => 0,
        };
        format!("extern_mod,{},id,{},name,{},location,{},crate,{}\n",
                self.extent_str(span, Some(sub_span)), id, name, loc, cnum)        
    }

    fn ref_str(&self, kind: &str, span: &Span, sub_span: &Span, id: DefId) -> ~str {
        format!("{},{},refid,{},refidcrate,{}\n",
                kind, self.extent_str(span, Some(sub_span)), id.node, id.crate)
    }

    fn fn_call_str(&self, span: &Span, sub_span: &Span, id: DefId, scope_id:NodeId) -> ~str {
        format!("fn_call,{},refid,{},refidcrate,{},scopeid,{}\n",
                self.extent_str(span, Some(sub_span)), id.node, id.crate, scope_id)
    }

    fn meth_call_str(&self, span: &Span, sub_span: &Span, defid: DefId, declid: Option<DefId>, scope_id:NodeId) -> ~str {
        match declid {
            Some(declid) => format!("method_call,{},refid,{},refidcrate,{},declid,{},declidcrate,{},scopeid,{}\n",
                self.extent_str(span, Some(sub_span)), defid.node, defid.crate, declid.node, declid.crate, scope_id),
            None => format!("method_call,{},refid,{},refidcrate,{},scopeid,{}\n",
                self.extent_str(span, Some(sub_span)), defid.node, defid.crate, scope_id),
        }
        
    }

    fn mod_ref_str(&self, span: &Span, sub_span: Option<&Span>, id: DefId) -> ~str {
        format!("mod_ref,{},refid,{},refidcrate,{},qualname,\"\"\n",
                self.extent_str(span, sub_span), id.node, id.crate)
    }

    fn sub_mod_ref_str(&self, span: &Span, sub_span: &Span, qualname: &str) -> ~str {
        format!("mod_ref,{},refid,0,refidcrate,0,qualname,{}\n",
                self.extent_str(span, Some(sub_span)), qualname)
    }

    fn sub_type_ref_str(&self, span: &Span, sub_span: &Span, qualname: &str) -> ~str {
        format!("type_ref,{},refid,0,refidcrate,0,qualname,{}\n",
                self.extent_str(span, Some(sub_span)), qualname)
    }

    fn inherit_str(&self, base_id: DefId, deriv_id: NodeId) -> ~str {
        format!("inheritance,base,{},basecrate,{},derived,{},derivedcrate,0\n",
                base_id.node, base_id.crate, deriv_id)        
    }

    fn typedef_str(&self, span: &Span, sub_span: &Span, id: NodeId, qualname: &str, value: &str) -> ~str {
        format!("typedef,{},qualname,{},id,{},value,\"{}\"\n",
                self.extent_str(span, Some(sub_span)), qualname, id, value)
    }

    fn crate_str(&self, span: &Span, name: &str) -> ~str {        
        format!("crate,{},name,{}\n",
                self.extent_str(span, None), name)
    }

    fn external_crate_str(&self, span: &Span, name: &str, cnum: CrateNum) -> ~str {
        let lo_loc = self.sess.codemap.lookup_char_pos(span.lo);
        format!("external_crate,name,{},crate,{},file_name,{}\n",
                name, cnum, lo_loc.file.name)
    }

    // looksup anything, not just a type
    fn lookup_type_ref(&self, ref_id: NodeId, kind: &str) -> Option<DefId> {
        let def_map = self.analysis.ty_cx.def_map.borrow();
        let def = def_map.get().find(&ref_id);
        match def {
            Some(d) => match *d {
                ast::DefTy(def_id) |
                ast::DefMod(def_id) |
                ast::DefStruct(def_id) |
                ast::DefVariant(_,def_id,_) |
                ast::DefTrait(def_id) => Some(def_id),
                _ => {
                    println!("found unexpected def in {} lookup", kind);
                    None
                },
            },
            None => {
                println!("could not find {} def {}", kind, ref_id);
                None
            },
        }
    }

    fn process_method(&mut self, method: &method, e:DxrVisitorEnv) {
        let mut scope_id = 0;
        // The qualname for a method is the trait name or name of the struct in an impl in
        // which the method is declared in followed by the method's name.
        let qualname = match ty::impl_of_method(self.analysis.ty_cx, DefId{crate:0, node:method.id}) {
            Some(impl_id) => match *self.analysis.ty_cx.items.get(&impl_id.node) {
                node_item(item, _) => {
                    scope_id = item.id;
                    match item.node {
                        item_impl(_, _, ty, _) => ty_to_str(ty, get_ident_interner()) + "::",
                        _ => {
                            println!("Container {} for method {} not an impl?", impl_id.node, method.id);
                            ~"???::"                                
                        },                                    
                    }
                },
                _ => {
                    println!("Could not find container {} for method {}", impl_id.node, method.id);
                    ~"???::"                                
                },
            },
            None => match ty::trait_of_method(self.analysis.ty_cx, DefId{crate:0, node:method.id}) {
                Some(def_id) => {
                    scope_id = def_id.node;
                    match *self.analysis.ty_cx.items.get(&def_id.node) {
                        node_item(item, path) => path_ident_to_str(path, item.ident, get_ident_interner()) + "::",
                        _ => {
                            println!("Could not find container {} for method {}", def_id.node, method.id);
                            ~"???::"
                        }
                    }
                },
                None => {
                    println!("Could not find container for method {}", method.id);
                    ~"???::"                                
                },
            },
        };

        let qualname = qualname + ident_to_str(&method.ident);

        // record the decl for this def (if it has one)
        let decl_id = match ty::trait_method_of_method(self.analysis.ty_cx, DefId{crate:0, node:method.id}) {
            Some(def_id) => if method.id != def_id.node && def_id.node == 0 {
                Some(def_id)
            } else {
                None
            },
            None => None,
        };

        match self.sub_span_after_keyword(&method.span, keywords::Fn) {
            Some(sub_span) => write!(self.out, "{}",
                                     self.method_str(&method.span,
                                                     &sub_span,
                                                     method.id,
                                                     qualname,
                                                     decl_id,
                                                     scope_id)),
            None => println("Could not find sub-span for method name"),
        }

        // TODO factor this out (args)
        for arg in method.decl.inputs.iter() {
            self.collected_paths.clear();
            self.visit_pat(arg.pat, e);
            for &(id, ref p, _) in self.collected_paths.iter() {
                // get the span only for the name of the variable (I hope the path is only ever a
                // variable name, but who knows?)
                let sub_span = self.span_for_name(&p.span);
                write!(self.out, "{}",
                       self.formal_str(&p.span,
                                         &sub_span,
                                         id,
                                         qualname,
                                         path_to_str(p, get_ident_interner())));
            }
        }

        // explicit self
        let sub_span = self.sub_span_for_keyword(&method.span, keywords::Self);
        match sub_span {
            Some(sub_span) => write!(self.out, "{}",
                                     self.formal_str(&method.span,
                                                       &sub_span,
                                                       method.self_id,
                                                       qualname,
                                                        "self")),
            None => (),
        };

        visit::walk_explicit_self(self, &method.explicit_self, e);

        // walk arg and return types
        for arg in method.decl.inputs.iter() {
            self.visit_ty(arg.ty, e);
        }
        self.visit_ty(method.decl.output, e);
        // walk the fn body
        self.visit_block(method.body, DxrVisitorEnv::new_nested(method.id));

        // TODO type params
    }
    fn process_struct_field_def(&mut self, field: &ast::struct_field, qualname: &str) {
        match field.node.kind {
            named_field(ref ident, _) => {
                let name = ident_to_str(ident);
                let qualname = qualname + "::" + name;
                match self.sub_span_before_token(&field.span, COLON) {
                    Some(ref sub_span) => write!(self.out, "{}",
                    self.field_str(&field.span, sub_span, field.node.id,
                                   name, qualname)),
                    None => println!("Could not find sub-span for field {}", qualname),
                }
            },
            _ => (),
        }
    }
}

impl<'l> Visitor<DxrVisitorEnv> for DxrVisitor<'l> {
    fn visit_item(&mut self, item:@item, e: DxrVisitorEnv) {
        match item.node {
            item_fn(decl, _, _, _, body) => {
                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                match self.sub_span_after_keyword(&item.span, keywords::Fn) {
                    Some(sub_span) => write!(self.out, "{}",
                                             self.fn_str(&item.span,
                                                         &sub_span,
                                                         item.id,
                                                         qualname)),
                    None => println!("Could not find sub-span for fn name in {}, {}", qualname, self.extent_str(&item.span, None)),
                }

                for arg in decl.inputs.iter() {
                    self.collected_paths.clear();
                    self.visit_pat(arg.pat, e);
                    for &(id, ref p, _) in self.collected_paths.iter() {
                        // get the span only for the name of the variable (I hope the path is only ever a
                        // variable name, but who knows?)
                        let sub_span = self.span_for_name(&p.span);
                        write!(self.out, "{}",
                               self.formal_str(&p.span,
                                                 &sub_span,
                                                 id,
                                                 qualname,
                                                 path_to_str(p, get_ident_interner())));
                    }
                }

                // walk arg and return types
                for arg in decl.inputs.iter() {
                    self.visit_ty(arg.ty, e);
                }
                self.visit_ty(decl.output, e);

                // walk the body
                self.visit_block(body, DxrVisitorEnv::new_nested(item.id));

                // TODO walk type params
            },
            item_static(typ, mt, expr) => {
                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                let value = match mt {
                    MutMutable => ~"",
                    MutImmutable => {
                        match self.sess.codemap.span_to_snippet(expr.span) {
                            Some(s) => s,
                            None => ~"",
                        }
                    },
                };

                match self.sub_span_after_keyword(&item.span, keywords::Static) {
                    Some(sub_span) => write!(self.out, "{}",
                                             self.static_str(&item.span,
                                                             &sub_span,
                                                             item.id,
                                                             ident_to_str(&item.ident),
                                                             qualname,
                                                             value)),
                    None => println("Could not find sub-span for static item name"),
                }

                // walk type and init value
                self.visit_ty(typ, e);
                self.visit_expr(expr, e);
            },
            item_struct(def, ref _g) => {
                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                let ctor_id = match def.ctor_id {
                    Some(node_id) => node_id,
                    None => 0,
                };
                match self.sub_span_after_keyword(&item.span, keywords::Struct) {
                    Some(sub_span) => write!(self.out, "{}",
                                             self.struct_str(&item.span,
                                                             &sub_span,
                                                             item.id, ctor_id,
                                                             qualname, "")),
                    None => println!("Could not find sub-span for struct {}", qualname),
                }

                // fields
                for field in def.fields.iter() {
                    self.process_struct_field_def(field, qualname);
                }

                // TODO walk type params
            },
            item_enum(ref enum_definition, _) => {
                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };
                match self.sub_span_after_keyword(&item.span, keywords::Enum) {
                    Some(ref sub_span) => write!(self.out, "{}", self.enum_str(
                                                 &item.span, sub_span, item.id, qualname)),
                    None => println!("Could not find subspan for enum {}", qualname),
                }
                for &variant in enum_definition.variants.iter() {
                    let name = ident_to_str(&variant.node.name);
                    let qualname = qualname + "::" + name;
                    let val = match self.sess.codemap.span_to_snippet(variant.span) {
                        Some(snip) => snip,
                        None => ~"",
                    };
                    match variant.node.kind {
                        tuple_variant_kind(ref args) => {
                            // first ident in span is the variant's name
                            write!(self.out, "{}",
                                   self.tuple_variant_str(&variant.span,
                                                          &self.span_for_ident(&variant.span),
                                                          variant.node.id, name, qualname, val));
                            for arg in args.iter() {
                                self.visit_ty(arg.ty, e);
                            }
                        }
                        struct_variant_kind(ref struct_def) => {
                            let ctor_id = match struct_def.ctor_id {
                                Some(node_id) => node_id,
                                None => 0,
                            };
                            match self.sub_span_before_token(&variant.span, LBRACE) {
                                Some(sub_span) => write!(self.out, "{}",
                                                        self.struct_variant_str(&variant.span,
                                                        &sub_span, variant.node.id, ctor_id,
                                                        qualname, val)),
                                None => println!("Could not find sub-span for struct {}", qualname),
                            }
                            for field in struct_def.fields.iter() {
                                self.process_struct_field_def(field, qualname);
                                self.visit_ty(field.node.ty, e);
                            }
                        }
                    }
                }
            },
            item_impl(ref type_parameters,
                      ref trait_ref,
                      typ,
                      ref methods) => {
                match typ.node {
                    ty_path(ref path, _, id) => {
                        match self.lookup_type_ref(id, "impl") {
                            Some(id) => {
                                let sub_span = self.span_for_name(&path.span);
                                write!(self.out, "{}",
                                       self.impl_str(&path.span, &sub_span, item.id, id));
                            },
                            None => ()
                        }
                    },
                    _ => println("expected a path to a struct, but got some other type"),
                }

                match *trait_ref {
                    Some(ref trait_ref) => {
                        match self.lookup_type_ref(trait_ref.ref_id, "trait") {
                            Some(id) => {
                                let sub_span = self.span_for_name(&trait_ref.path.span);
                                write!(self.out, "{}",
                                       self.ref_str("type_ref", &trait_ref.path.span, &sub_span, id));
                                write!(self.out, "{}",
                                       self.impl_str(&trait_ref.path.span, &sub_span, item.id, id));
                            },
                            None => ()
                        }
                    },
                    None => (),
                }

                self.visit_generics(type_parameters, e);
                self.visit_ty(typ, e);
                for method in methods.iter() {
                    visit::walk_method_helper(self, *method, e)
                }
            },
            item_trait(ref generics, ref trait_refs, ref methods) => {
                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                match self.sub_span_after_keyword(&item.span, keywords::Trait) {
                    Some(sub_span) => write!(self.out, "{}",
                                             self.trait_str(&item.span,
                                                            &sub_span,
                                                            item.id,
                                                            qualname)),
                    None => println!("Could not find sub-span for trait {}", qualname),
                }

                // super-traits
                for trait_ref in trait_refs.iter() {
                    match self.lookup_type_ref(trait_ref.ref_id, "trait") {
                        Some(id) => {
                            let sub_span = self.span_for_name(&trait_ref.path.span);
                            write!(self.out, "{}",
                                   self.ref_str("type_ref", &trait_ref.path.span, &sub_span, id));
                            write!(self.out, "{}",
                                   self.inherit_str(id, item.id));
                        },
                        None => ()
                    }
                }

                // walk generics and methods
                self.visit_generics(generics, e);
                for method in methods.iter() {
                    self.visit_trait_method(method, e)
                }
            },
            item_mod(ref m) => {
                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                // For reasons I don't understand, if there are no items in a module
                // then items is not in fact empty, but contains an empty item in the current
                // file. That is non-optimal, but we can live with it because it should be
                // pretty rare that a module has no items.
                // I'm leaving the length check just in case it changes someday, returning
                // the current file for consistency.
                let cm = self.sess.codemap;
                let filename = if m.items.len() > 0 {
                    cm.span_to_filename(m.items[0].span)
                } else {
                    cm.span_to_filename(item.span)
                };

                match self.sub_span_after_keyword(&item.span, keywords::Mod) {
                    Some(sub_span) => write!(self.out, "{}",
                                             self.mod_str(&item.span,
                                                          &sub_span,
                                                          item.id,
                                                          qualname,
                                                          e.cur_scope,
                                                          filename)),
                    None => println!("Could not find sub-span for module {}", qualname),
                }

                visit::walk_mod(self, m, DxrVisitorEnv::new_nested(item.id))
            },
            item_ty(ty, ref _g) => {
                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };
                let value = ty_to_str(ty, get_ident_interner());
                match self.sub_span_after_keyword(&item.span, keywords::Type) {
                    Some(sub_span) => write!(self.out, "{}",
                                             self.typedef_str(&item.span,
                                                              &sub_span,
                                                              item.id,
                                                              qualname,
                                                              value)),
                    None => println!("Could not find sub-span for type defintion {}", qualname),
                }

                self.visit_ty(ty, e);
                //TODO type params
            },
            _ => visit::walk_item(self, item, e),
        }
    }

    // We don't actually index functions here, that is done in visit_item/ItemFn.
    // Here we just visit methods.
    fn visit_fn(&mut self, fk:&visit::fn_kind, fd:&fn_decl, b:P<Block>, s:Span, n:NodeId, e:DxrVisitorEnv) {
        match *fk {
            visit::fk_method(_, _, method) => self.process_method(method, e),
            _ => visit::walk_fn(self, fk, fd, b, s, n, e),
        }
    }

    fn visit_trait_method(&mut self, tm: &trait_method, e: DxrVisitorEnv) {
        match *tm {
            required(ref method_type) => {
                let mut scope_id = 0;
                let qualname = match ty::trait_of_method(self.analysis.ty_cx, DefId{crate:0, node:method_type.id}) {
                    Some(def_id) => {
                        scope_id = def_id.node;
                        match *self.analysis.ty_cx.items.get(&def_id.node) {
                            node_item(item, path) => path_ident_to_str(path, item.ident, get_ident_interner()) + "::",
                            _ => {
                                println!("Could not find trait {} for method {}", def_id.node, method_type.id);
                                ~"???::"
                            }
                        }
                    },
                    None => {
                        println!("Could not find trait for method {}", method_type.id);
                        ~"???::"                                
                    },
                };

                let qualname = qualname + ident_to_str(&method_type.ident);

                match self.sub_span_after_keyword(&method_type.span, keywords::Fn) {
                    Some(sub_span) => write!(self.out, "{}",
                                             self.method_decl_str(&method_type.span,
                                                                  &sub_span,
                                                                  method_type.id,
                                                                  qualname,
                                                                  scope_id)),
                    None => println("Could not find sub-span for method name"),
                }

                // walk arg and return types
                for arg in method_type.decl.inputs.iter() {
                    self.visit_ty(arg.ty, e);
                }
                self.visit_ty(method_type.decl.output, e);

                // TODO type params
            }
            provided(method) => self.process_method(method, e),
        }
    }

    fn visit_view_item(&mut self, i:&view_item, _e:DxrVisitorEnv) {
        match i.node {
            view_item_use(ref paths) => {
                for vp in paths.iter() {
                    match vp.node {
                        view_path_simple(ident, ref path, id) => {
                            let sub_span = self.span_for_name(&vp.span);
                            let mod_id = match self.lookup_type_ref(id, "module") {
                                Some(id) => {
                                    write!(self.out, "{}",
                                           self.mod_ref_str(&vp.span, Some(&sub_span), id));
                                    id
                                },
                                None => DefId{node:0, crate:0},
                            };

                            // 'use' always introduces a module alias, if there is not an explicit
                            // one, there is an implicit one.
                            let sub_span = match self.sub_span_before_token(&vp.span, EQ) {
                                Some(sub_span) => sub_span,
                                None => sub_span,
                            };

                            let name = ident_to_str(&ident);
                            write!(self.out, "{}",
                                   self.mod_alias_str(&vp.span,
                                                      &sub_span,
                                                      id, mod_id,
                                                      name));
                            self.write_sub_paths_truncated(path);
                        }
                        view_path_glob(ref path, _) => {
                            self.write_sub_paths(path);
                        }
                        view_path_list(ref path, ref list, _) => {
                            for plid in list.iter() {
                                match self.lookup_type_ref(plid.node.id, "module") {
                                    Some(id) => {
                                        write!(self.out, "{}",
                                               self.mod_ref_str(&plid.span, None, id));                                        
                                    },
                                    None => ()
                                }
                            }

                            self.write_sub_paths(path);
                        }
                    }
                }
            },
            view_item_extern_mod(ident, s, _, id) => {
                // TODO introduces an alias like use
                let name = ident_to_str(&ident);
                let s = match s {
                    Some((s, _)) => s.to_owned(),
                    None => name.to_owned(),
                };
                let sub_span = self.sub_span_after_keyword(&i.span, keywords::Mod);
                match sub_span {
                    Some(sub_span) => write!(self.out, "{}",
                        self.extern_mod_str(&i.span, &sub_span, id, name, s)),
                    None => println!("Could not find ident in extern mod item {}", id),
                }
            },
        }
    }

    fn visit_ty(&mut self, t:&Ty, e:DxrVisitorEnv) {
        match t.node {
            ty_path(ref path, ref bounds, id) => {
                match self.lookup_type_ref(id, "type") {
                    Some(id) => {
                        let sub_span = self.span_for_name(&t.span);
                        write!(self.out, "{}",
                               self.ref_str("type_ref", &t.span, &sub_span, id));
                    },
                    None => ()
                }

                self.write_sub_paths_truncated(path);

                visit::walk_path(self, path, e);
                for bounds in bounds.iter() {
                    visit::walk_ty_param_bounds(self, bounds, e)
                }
            },
            _ => visit::walk_ty(self, t, e),
        }
    }

    fn visit_expr(&mut self, ex: @Expr, e: DxrVisitorEnv) {
        match ex.node {
            ExprCall(_f, ref _args, _) => {
                // Don't need to do anything for function calls,
                // because just walking the callee path does what we want.
                visit::walk_expr(self, ex, e);
            },
            ExprPath(ref path) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&ex.id);
                let sub_span = self.span_for_name(&ex.span);
                match def {
                    Some(d) => {
                        match *d {
                            ast::DefLocal(id, _) |
                            ast::DefArg(id, _) |
                            ast::DefBinding(id, _) => write!(self.out, "{}",
                                self.ref_str("var_ref", &ex.span, &sub_span, DefId{node:id, crate:0})),
                            ast::DefStatic(def_id,_) => write!(self.out, "{}",
                                self.ref_str("var_ref", &ex.span, &sub_span, def_id)),
                            ast::DefStruct(def_id) => write!(self.out, "{}",
                                self.ref_str("struct_ref", &ex.span, &sub_span, def_id)),
                            ast::DefStaticMethod(declid, provenence, _) => {
                                let methods = self.analysis.ty_cx.methods.borrow();
                                let defid = match methods.get().find(&declid) {
                                    Some(m) => match provenence {
                                        FromTrait(def_id) =>
                                            match ty::trait_methods(self.analysis.ty_cx, def_id).iter()
                                            .find(|mr| mr.ident.name == m.ident.name) {
                                                Some(mr) => mr.def_id,
                                                None => DefId{crate:0,node:0},
                                            },
                                        FromImpl(def_id) => {
                                            let impls = self.analysis.ty_cx.impls.borrow();
                                            match impls.get().find(&def_id) {
                                                Some(i) => match i.methods.iter().find(|mr| mr.ident.name == m.ident.name) {
                                                    Some(mr) => mr.def_id,
                                                    None => DefId{crate:0,node:0},
                                                },
                                                None => DefId{crate:0,node:0},
                                            }
                                        }
                                    },
                                    None => DefId{crate:0,node:0},
                                };
                                write!(self.out, "{}",
                                       self.meth_call_str(&ex.span, &sub_span, defid, Some(declid), e.cur_scope));                                
                            }
                            ast::DefFn(def_id, _) => write!(self.out, "{}",
                                                            self.fn_call_str(&ex.span,
                                                                             &sub_span,
                                                                             def_id,
                                                                             e.cur_scope)),
                            ast::DefVariant(_, variant_id, _) => write!(self.out, "{}",
                                                                        self.ref_str("var_ref",
                                                                                     &ex.span,
                                                                                     &sub_span,
                                                                                     variant_id)),
                           _ => println!("Unexpected def kind while looking up path {}", ex.id),
                        }
                        // modules or types in the path prefix
                        match *d {
                            ast::DefStaticMethod(_, _, _) => self.write_sub_path_trait_truncated(path),
                            _ => self.write_sub_paths_truncated(path),
                        }
                    },
                    None => println!("Could not find path {}", ex.id),
                }

                visit::walk_path(self, path, e);
            },
            ExprSelf => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&ex.id);
                let sub_span = self.span_for_name(&ex.span);
                match def {
                    Some(d) => match *d {
                        ast::DefSelf(id, _) => {
                            write!(self.out, "{}",
                                   self.ref_str("var_ref", &ex.span, &sub_span, DefId{node:id, crate:0}));
                        },
                       _ => println!("Unexpected def kind while looking up self {}", ex.id),
                   },
                   None => println!("Could not find self {}", ex.id),
                }                
            }
            ExprStruct(ref path, ref fields, base) => {
                let mut struct_def: Option<DefId> = None;
                match self.lookup_type_ref(ex.id, "struct") {
                    Some(id) => {
                        struct_def = Some(id);
                        let sub_span = self.span_for_name(&path.span);
                        write!(self.out, "{}",
                               self.ref_str("struct_ref", &path.span, &sub_span, id));
                    },
                    None => ()
                }

                self.write_sub_paths_truncated(path);

                for field in fields.iter() {
                    match struct_def {
                        Some(struct_def) => {
                            let fields = ty::lookup_struct_fields(self.analysis.ty_cx, struct_def);
                            for f in fields.iter() {
                                if f.name == field.ident.node.name {
                                    // We don't really need a sub-span here, but no harm done
                                    let sub_span = self.span_for_name(&field.ident.span);
                                    write!(self.out, "{}",
                                           self.ref_str("var_ref", &field.ident.span, &sub_span, f.id));
                                }
                            }
                        },
                        _ => (),
                    }

                    self.visit_expr(field.expr, e)
                }
                visit::walk_expr_opt(self, base, e)
            },
            ExprMethodCall(_, callee, _, _, ref args, _) => {
                let method_map = self.analysis.maps.method_map.borrow();
                let method = method_map.get().find(&ex.id);
                match method {
                    Some(method) => match method.origin {
                        typeck::method_static(def_id) => {
                            // method invoked on a struct object (not a static method)
                            let sub_span = self.span_for_name(&ex.span);
                            let declid = match ty::trait_method_of_method(self.analysis.ty_cx, def_id) {
                                Some(def_id) => Some(def_id),
                                None => None
                            };
                            write!(self.out, "{}",
                                   self.meth_call_str(&ex.span, &sub_span, def_id, declid, e.cur_scope));
                        }
                        typeck::method_param(mp) => {
                            // method invoked on a type parameter
                            let method = ty::trait_method(self.analysis.ty_cx, mp.trait_id, mp.method_num);
                            let sub_span = self.span_for_name(&ex.span);
                            write!(self.out, "{}",
                                   self.meth_call_str(&ex.span, &sub_span, DefId{node:0,crate:0}, Some(method.def_id), e.cur_scope));
                        },
                        typeck::method_object(mo) => {
                            // method invoked on a trait instance
                            let method = ty::trait_method(self.analysis.ty_cx, mo.trait_id, mo.method_num);
                            let sub_span = self.span_for_name(&ex.span);
                            // We don't know where object methods are defined since they are staticaly
                            // dispatched, so pass 0 as the definition id.
                            write!(self.out, "{}",
                                   self.meth_call_str(&ex.span, &sub_span, DefId{node:0,crate:0}, Some(method.def_id), e.cur_scope));
                        },
                    },
                    None => println!("Could not find method in map {}", ex.id),
                }

                // walk receiver and args
                visit::walk_exprs(self, *args, e);
                self.visit_expr(callee, e);

                // TODO type params
            },
            ExprField(sub_ex, ident, _) => {
                self.visit_expr(sub_ex, e);

                let types = self.analysis.ty_cx.node_types.borrow();
                let t = types.get().find(&(sub_ex.id as uint));
                match t {
                    Some(t) => {
                        let t = ty::type_autoderef(self.analysis.ty_cx, *t);
                        let t_box = ty::get(t);
                        match t_box.sty {
                            ty::ty_struct(def_id, _) => {
                                let fields = ty::lookup_struct_fields(self.analysis.ty_cx, def_id);
                                for f in fields.iter() {
                                    if f.name == ident.name {
                                        let sub_span = self.span_for_name(&ex.span);
                                        write!(self.out, "{}",
                                               self.ref_str("var_ref", &ex.span, &sub_span, f.id));
                                    }
                                }
                            },
                            _ => println("Expected struct type, but not ty_struct"),
                        }
                    },
                    None => println("No type for sub-expression in field reference"),
                }
            },
            _ => visit::walk_expr(self, ex, e),
        }
    }

    fn visit_pat(&mut self, p:&Pat, e: DxrVisitorEnv) {
        match p.node {
            PatStruct(ref path, ref fields, _) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&p.id);
                let sub_span = match self.sub_span_before_token(&p.span, LBRACE) {
                    Some(ss) => ss,
                    None => self.span_for_name(&p.span),
                };
                match def {
                    Some(&def) => match def {
                        ast::DefVariant(_, v_id, _) => write!(self.out, "{}", self.ref_str("struct_ref",
                                                              &p.span, &sub_span, v_id)),
                        _ => println!("Struct pattern {} not a variant.", p.id)
                    },
                    _ => println!("Could not find definition for struct pattern {}.", p.id),
                }
                visit::walk_path(self, path, e);
                let struct_def = self.lookup_type_ref(p.id, "struct");
                // the AST doesn't give us a span for the struct field, so we have
                // to figure out where it is by assuming it comes before colons
                // first shorten field span to its opening brace
                let mut field_span = self.sub_span_after_token(&p.span, LBRACE);
                for field in fields.iter() {
                    match struct_def {
                        Some(struct_def) => {
                            let fields = ty::lookup_struct_fields(self.analysis.ty_cx, struct_def);
                            for f in fields.iter() {
                                if f.name == field.ident.name {
                                    // use text up to colon as subspan
                                    match self.sub_span_before_token(&field_span, COLON) {
                                        Some(fs) => {
                                            write!(self.out, "{}",
                                                self.ref_str("var_ref", &field_span, &fs, f.id));
                                        },
                                        None => (),
                                    }
                                    // shorten field_span to the next comma
                                    field_span = self.sub_span_after_token(&field_span, COMMA);
                                }
                            }
                        },
                        _ => (),
                    }
                    self.visit_pat(field.pat, e);
                }
            }
            PatEnum(ref path, ref children) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&p.id);
                let sub_span = match self.sub_span_before_token(&p.span, LPAREN) {
                    Some(ss) => ss,
                    None => self.span_for_name(&p.span),
                };
                match def {
                    Some(&def) => match def {
                        ast::DefVariant(_, v_id, _) => write!(self.out, "{}", self.ref_str(
                                                              "var_ref", &p.span, &sub_span, v_id)),
                        _ => println!("No variant definition found for {}", p.id),
                    },
                    _ => println!("No definition found for pattern {}", p.id),
                }
                visit::walk_path(self, path, e);
                for children in children.iter() {
                    for child in children.iter() {
                        self.visit_pat(*child, e);
                    }
                }
            }
            PatIdent(bm, ref path, ref optional_subpattern) => {
                let immut = match bm {
                    BindByRef(mt) |
                    BindByValue(mt) => {
                        match mt {
                            MutMutable => false,
                            MutImmutable => true,
                        }
                    }
                };
                // collect path for either visit_local or visit_arm
                self.collected_paths.push((p.id, path.clone(), immut));
                match *optional_subpattern {
                    None => {}
                    Some(subpattern) => self.visit_pat(subpattern, e),
                }
            }
            _ => visit::walk_pat(self, p, e)
        }
    }

    fn visit_arm(&mut self, arm: &ast::Arm, e: DxrVisitorEnv) {
        //! Visit a match arm and write arm bindings and variants to csv.
        self.collected_paths.clear();
        for pattern in arm.pats.iter() {
            // collect paths from the arm's patterns
            self.visit_pat(*pattern, e);
        }
        // process collected paths
        for &(id,ref p, ref immut) in self.collected_paths.iter() {
            let value = match self.sess.codemap.span_to_snippet(p.span) {
                Some(s) => if *immut { s.to_owned() } else { ~"" },
                None => ~"",
            };
            let sub_span = self.span_for_name(&p.span);
            let def_map = self.analysis.ty_cx.def_map.borrow();
            let def = def_map.get().find(&id);
            match def {
                Some(&def) => match def {
                    ast::DefBinding(id, _) => write!(self.out, "{}",
                                              self.variable_str(&p.span,
                                                                &sub_span, id,
                                                                path_to_str(p, get_ident_interner()),
                                                                value)),
                    ast::DefVariant(_,id,_) => write!(self.out, "{}",
                                               self.ref_str("var_ref",
                                                            &p.span, &sub_span, id)),
                    _ => (),
                },
                _ => (),
            }
        }
        visit::walk_expr_opt(self, arm.guard, e);
        self.visit_block(arm.body, e);
    }
    fn visit_local(&mut self, l:@Local, e: DxrVisitorEnv) {
        // the local could declare multiple new vars, we must walk the pattern and collect them all
        self.collected_paths.clear();
        self.visit_pat(l.pat, e);

        let value = match self.sess.codemap.span_to_snippet(l.span) {
            Some(s) => s,
            None => ~"",
        };

        for &(id,ref p, ref immut) in self.collected_paths.iter() {
            let value = if *immut { value.to_owned() } else { ~"" };
            // get the span only for the name of the variable (I hope the path is only ever a
            // variable name, but who knows?)
            let sub_span = self.span_for_name(&p.span);
            // Rust uses the id of the pattern for var lookups, so we'll use it too
            write!(self.out, "{}",
                   self.variable_str(&p.span,
                                     &sub_span,
                                     id,
                                     path_to_str(p, get_ident_interner()),
                                     value));
        }

        // Just walk the initialiser and type (don't want to walk the pattern again)
        self.visit_ty(l.ty, e);
        visit::walk_expr_opt(self, l.init, e);
    }
}

#[deriving(Clone)]
struct DxrVisitorEnv {
    cur_scope: NodeId,
}

impl DxrVisitorEnv {
    fn new() -> DxrVisitorEnv {
        DxrVisitorEnv{cur_scope: 0}
    }
    fn new_nested(new_mod: NodeId) -> DxrVisitorEnv {
        DxrVisitorEnv{cur_scope: new_mod}
    }
}

pub fn process_crate(sess: Session,
                     crate: &ast::Crate,
                     analysis: &CrateAnalysis,
                     odir: &Option<Path>) {
    let (cratename, crateid) = match attr::find_crateid(crate.attrs) {
        Some(crateid) => (crateid.name.clone(), crateid.to_str()),
        None => (~"unknown_crate",~"unknown_crate"),
    };

    println!("Dumping crate {} ({})", cratename, crateid);

    // find a path to dump our data to
    let mut root_path = match os::getenv("DXR_RUST_TEMP_FOLDER") {
        Some(val) => Path::new(val),
        None => match *odir {
            Some(ref val) => {
                let mut path = val.clone();
                path.push("dxr");
                path },
            None() => Path::new("dxr-temp"),
        },
    };
    
    fs::mkdir_recursive(&root_path, io::UserRWX);
    {
        let disp = root_path.display();
        println!("Writing output to {}", disp);
    }

    // create ouput file
    root_path.push(cratename + ".csv");
    let output_file = match File::create(&root_path) {
        Some(f) => ~f,
        None => {
            let disp = root_path.display();
            println!("Could not open {}", disp);
            return;
        }
    };
    root_path.pop();

    let mut visitor = DxrVisitor{sess: sess,
                                 analysis: analysis,
                                 collected_paths: ~[],
                                 out: output_file as ~Writer};

    visitor.dump_crate_info(cratename, crate);

    visit::walk_crate(&mut visitor, crate, DxrVisitorEnv::new());
}
