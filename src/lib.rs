use std::{
    fmt::Display,
    mem::take,
    sync::atomic::{AtomicBool, Ordering},
};

use char_classes as cc;
use char_classes::FirstElem;
use either::Either::{self, Left, Right};
use peg::RuleResult;

/// # Examples
/// ```
/// use cdecl_to_rsdecl::trim_csi;
/// assert_eq!("hi", trim_csi("\x1b[1;31mhi"));
/// assert_eq!("hi", trim_csi("\x1b[1;31m\x1b[8mhi"));
/// assert_eq!("hi", trim_csi("\x1b[1;31m\x1b[8mhi\x1b[0m"));
/// assert_eq!("hi", trim_csi("\x1b[1;31m\x1b[8mhi\x1b[0m\x1b[0m"));
/// ```
pub fn trim_csi(mut s: &str) -> &str {
    let alpha = cc::any!("a-zA-Z");
    while s.starts_with("\x1b[") {
        s = s.split_once(alpha).unwrap().1
    }
    while s.ends_with(alpha) {
        let part = &s[..s.len()-1];
        let Some(end_csi) = part
            .rsplit_once("\x1b[")
            .map(|it| it.1)
            .filter(|it| !it.contains(alpha))
        else {
            break;
        };
        s = &part[..part.len()-end_csi.len()-2];
    }
    s
}

macro_rules! any {
    ($($pat:tt)*) => {
        |str, i| str[i..].first_elem()
            .filter(cc::any!($($pat)*))
            .map_or(RuleResult::Failed, |ch| RuleResult::Matched(i+ch.len_utf8(), ch))
    };
}

fn is(cond: bool) -> impl Fn(&str, usize) -> RuleResult<()> {
    move |_, i| if cond {
        RuleResult::Matched(i, ())
    } else {
        RuleResult::Failed
    }
}

fn paren(paren: bool, s: &impl Display) -> String {
    if paren {
        format!("({s})")
    } else {
        s.to_string()
    }
}

pub static COLOR: AtomicBool = AtomicBool::new(false);

#[macro_export]
macro_rules! color {
    ($color:literal $(; $color1:literal)*, $e:expr) => {{
        if $crate::COLOR.load(Ordering::Acquire) {
            format!(
                "\x1b[{}m{}\x1b[m",
                concat!(stringify!($color)$(, ";", stringify!($color1))*),
                $e,
            )
        } else {
            format!("{}", $e)
        }
    }};
}

#[derive(Debug, Clone, PartialEq)]
pub struct CDecl {
    share: String,
    declarations: Vec<(DeclTree<Self>, String)>,
}

impl CDecl {
    pub fn into_rsdecl(self) -> Vec<RsDecl> {
        self.declarations.into_iter()
            .map(|(cdecl, init)| {
                let mut rsdecl = RsDecl {
                    name: Default::default(),
                    ty: DeclTree::Term(self.share.clone()),
                    init,
                };

                cdecl.cdecl_to_rsdecl(&mut rsdecl);
                rsdecl
            })
            .collect()
    }
}

impl Display for CDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let is_cast = self.declarations.len() == 1
            && self.declarations[0].0.term().is_empty()
            && f.alternate();
        if is_cast { write!(f, "(")? }
        write!(f, "{}", self.share)?;
        if let Some((first, init)) = self.declarations.first() {
            let first_output = first.output_c();
            if !self.share.is_empty()
            && !first_output.is_empty()
            && !trim_csi(&first_output).starts_with('[')
            && !trim_csi(&first_output).ends_with('*')
            {
                f.write_str(" ")?;
            }
            f.write_str(&first_output)?;

            if !init.trim().is_empty() { write!(f, " {init}")? }

            for (rest, init) in &self.declarations[1..] {
                write!(f, ", {}", rest.output_c())?;
                if !init.trim().is_empty() { write!(f, " {init}")? }
            }
        }
        if is_cast { write!(f, ")")? }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RsDecl {
    name: String,
    ty: DeclTree<Self>,
    init: String,
}

impl RsDecl {
    pub fn into_cdecl(self) -> CDecl {
        let mut c_decl = CDecl {
            share: Default::default(),
            declarations: vec![
                (DeclTree::Term(self.name), self.init),
            ],
        };
        self.ty.rsdecl_to_cdecl(&mut c_decl);
        c_decl
    }

    pub fn make_owned_param(&mut self) {
        self.ty.c_owned_param();
    }
}

impl Display for RsDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let semi = (!self.name.is_empty() || f.alternate())
            .then_some(": ")
            .unwrap_or_default();
        write!(f, "{}{semi}{}", self.name, self.ty.output_rs())?;

        if !self.init.trim().is_empty() {
            write!(f, " {}", self.init)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
enum DeclTree<Param> {
    Pointer { attr: String, sub: Box<Self> },
    Function { sub: Box<Self>, params: Vec<Param>, attr: String },
    Array { sub: Box<Self>, len: Option<String> },
    Term(String),
}

impl<Param> Default for DeclTree<Param> {
    fn default() -> Self {
        Self::Term(Default::default())
    }
}

impl<T> DeclTree<T> {
    /// Returns `true` if the decl tree is [`Pointer`].
    ///
    /// [`Pointer`]: DeclTree::Pointer
    #[must_use]
    fn is_pointer(&self) -> bool {
        matches!(self, Self::Pointer { .. })
    }

    /// Returns `true` if the decl tree is [`Function`].
    ///
    /// [`Function`]: DeclTree::Function
    #[must_use]
    fn is_function(&self) -> bool {
        matches!(self, Self::Function { .. })
    }

    fn term_mut(&mut self) -> &mut String {
        match self {
            DeclTree::Pointer { sub, .. }
            | DeclTree::Function { sub, .. }
            | DeclTree::Array { sub, .. } =>
            {
                sub.term_mut()
            }
            DeclTree::Term(target) => target,
        }
    }
}

impl DeclTree<RsDecl> {
    fn output_rs(&self) -> String {
        match self {
            DeclTree::Pointer { attr, sub } => {
                format!("{}{}", color!(1, format_args!("{attr}*")), sub.output_rs())
            },
            DeclTree::Function { sub, params, attr } => {
                let mut ret = sub.output_rs();
                if ret == "void" {
                    ret = String::new()
                } else if !ret.is_empty() {
                    ret = format!("{}{ret}", color!(1;32, " -> "))
                }
                let params = params.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(&color!(1;35, ", "));
                format!("{}({params}){ret}", color!(33, format_args!("{attr}fn")))
            },
            DeclTree::Array { sub, len } => {
                let l_bracket = color!(1;34, "[");
                let r_bracket = color!(1;34, "]");
                if let Some(len) = len {
                    format!(
                        "{l_bracket}{}{} {len}{r_bracket}",
                        sub.output_rs(),
                        color!(1;34, ";"),
                    )
                } else {
                    format!("{l_bracket}{}{r_bracket}", sub.output_rs())
                }
            },
            DeclTree::Term(s) => s.clone(),
        }
    }

    fn rsdecl_to_cdecl(self, decl: &mut CDecl) {
        let (ty, _) = decl.declarations.first_mut().unwrap();
        match self {
            DeclTree::Pointer { attr, sub } => {
                *ty = DeclTree::Pointer { attr, sub: take(ty).into() };
                sub.rsdecl_to_cdecl(decl);
            },
            DeclTree::Function { sub, params, attr } => {
                let params = params.into_iter()
                    .map(RsDecl::into_cdecl)
                    .collect();
                *ty = DeclTree::Function { sub: take(ty).into(), params, attr };
                sub.rsdecl_to_cdecl(decl);
            },
            DeclTree::Array { sub, len } => {
                *ty = DeclTree::Array { sub: take(ty).into(), len };
                sub.rsdecl_to_cdecl(decl);
            },
            DeclTree::Term(share) => decl.share = share,
        }
    }

    fn c_owned_param(&mut self) {
        match self {
            DeclTree::Term(_) => (),
            DeclTree::Pointer { sub, .. }
            | DeclTree::Function { sub, .. }
            | DeclTree::Array { sub, .. } =>
            {
                sub.c_owned_param();
            }
        }
        let DeclTree::Function { params, .. } = self else { return };
        for param in params {
            if !param.ty.is_function() { continue }
            param.ty = DeclTree::Pointer {
                attr: String::new(),
                sub: take(&mut param.ty).into(),
            }
        }
    }
}

impl DeclTree<CDecl> {
    fn output_c(&self) -> String {
        match self {
            DeclTree::Pointer { attr, sub } => {
                if attr.is_empty() {
                    format!("{}{}", color!(1, "*"), sub.output_c())
                } else {
                    let output = sub.output_c();
                    let attr = color!(1, format_args!("*{attr}"));
                    if output.is_empty() {
                        attr
                    } else {
                        format!("{attr} {output}")
                    }
                }
            },
            DeclTree::Function { sub, params, attr } => {
                let params = params.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(&color!(1;35, ", "));
                let sub = paren(sub.is_pointer(), &sub.output_c());
                let l_paren = color!(33, "(");
                let r_paren = color!(33, format_args!("){attr}"));
                format!("{sub}{l_paren}{params}{r_paren}")
            },
            DeclTree::Array { sub, len } => {
                let sub = paren(sub.is_pointer(), &sub.output_c());
                if let Some(len) = len {
                    let l_bracket = color!(1;34, "[");
                    let r_bracket = color!(1;34, "]");
                    format!("{sub}{l_bracket}{len}{r_bracket}")
                } else {
                    format!("{sub}{}", color!(1;34, "[]"))
                }
            },
            DeclTree::Term(s) => s.clone(),
        }
    }

    fn merge_suffix(self, suf: Either<(Vec<CDecl>, String), Option<String>>) -> Self {
        let sub = Box::new(self);
        match suf {
            Left((params, attr)) => DeclTree::Function { sub, params, attr },
            Right(len) => DeclTree::Array { sub, len },
        }
    }

    fn cdecl_to_rsdecl(self, decl: &mut RsDecl) {
        match self {
            DeclTree::Pointer { attr, sub } => {
                let ty = take(&mut decl.ty);
                decl.ty = DeclTree::Pointer { attr, sub: ty.into() };
                sub.cdecl_to_rsdecl(decl);
            },
            DeclTree::Function { sub, params, attr} => {
                let ty = take(&mut decl.ty);
                let params = params.into_iter()
                    .map(CDecl::into_rsdecl)
                    .inspect(|decls| assert_eq!(decls.len(), 1))
                    .map(|decls| decls.into_iter().next().unwrap())
                    .collect();
                decl.ty = DeclTree::Function { sub: ty.into(), params, attr };
                sub.cdecl_to_rsdecl(decl);
            },
            DeclTree::Array { sub, len } => {
                let ty = take(&mut decl.ty);
                decl.ty = DeclTree::Array { sub: ty.into(), len };
                sub.cdecl_to_rsdecl(decl);
            },
            DeclTree::Term(name) => decl.name = name,
        }
    }

    fn term(&self) -> &str {
        match self {
            DeclTree::Pointer { sub, .. } |
            DeclTree::Function { sub, .. } |
            DeclTree::Array { sub, .. } => {
                sub.term()
            },
            DeclTree::Term(term) => term,
        }
    }
}

const KWDS: &[&str] = &[
    "auto", "break", "case", "char", "const", "continue", "default", "do",
    "double", "else", "enum", "extern", "float", "for", "goto", "if",
    "inline", "int", "long", "register", "restrict", "return", "short", "signed",
    "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void",
    "volatile", "while",
];

peg::parser!(pub grammar parser() for str {
    rule alpha() = #{any!(^"\x00-\x20!\"#%&'()*+,./0-9:;<=\x3e?@[\\]^`{|}~\x7f-")}()
    rule digit() = #{any!("0-9")}()
    rule init() -> &'input str = _ s:$("=" _ (!";" !"," tt())*)? _ {s.unwrap_or_default()}
    rule string()
        = quiet!{"'"  ("\\" [_] / #{any!(^"'\\")}())* "'"}
        / quiet!{"\"" ("\\" [_] / #{any!(^"\"\\")}())* "\""}
        / expected!("string")
    rule ident() -> String
        = s:$(alpha() (alpha() / digit())*) ib()
        { s.into() }
        / expected!("ident")
    rule nident() -> String
        = i:ident() #{is(!KWDS.contains(&&*i))} attrq:$((_ attrq())*) { i+attrq }
        / expected!("ident")
    rule number()
        = quiet!{"0x" / "0X"} #{any!("0-9a-fA-F")}+ num_suf() ib()
        / quiet!{"0b" / "0B"} #{any!("01")}+ num_suf() ib()
        / #{any!("0-9")}+ num_suf() ib()
        / expected!("number")
    rule literal() -> String = s:$(tt()+) { s.into() }
    rule attrq() = &("[" _ "[") tt()
    rule attr() = ("const" / "volatile" / "restrict" / "_Atomic") ib() / attrq()
    rule attrs() -> String = s:(s:$(attr()++_) _ {s})? {s.unwrap_or_default().into()}
    rule num_suf() = #{any!("uUlL")}*
    rule _() = #{any!(" \t\r\n")}* (comment() _)?
    rule comment() = quiet!{ "//" #{any!(^"\r\n")}* / "/*" (!"*/" [_])* "*/" }
    rule ib() = !alpha()

    rule tt()
        = "{" _ (tt()_)* "}"
        / "(" _ (tt()_)* ")"
        / "[" _ (tt()_)* "]"
        / ident()
        / number()
        / #{any!(^"{}()[]'\"")}()
        / string()
        / expected!("any")

    rule adt()
        = ("struct" / "union" / "enum") ib() _ (&"{" tt() / ident() (_ &"{" tt())?)
        / "typeof" ib() _ &"(" tt()
    rule share() -> String
        = s:$(adt()) {s.into()}
        / ident()
        / s:$(attrq()) {s.into()}

    pub rule rs_decls() -> Vec<RsDecl>
        = d:rs_decl() ++ ";" ";"? {d}

    rule rs_decl() -> RsDecl
        = _ name:nident()? _ ":" _ ty:rs_type() _ init:init()
        { RsDecl { name: name.unwrap_or_default(), ty, init: init.into() } }

    rule rs_param() -> RsDecl
        = _ name:(n:nident() _ ":" _ {n})? ty:rs_type()
        { RsDecl { name: name.unwrap_or_default(), ty, init: String::new() } }
        / "..." { RsDecl { name: String::new(), ty: DeclTree::Term("...".to_owned()), init: String::new() } }

    rule rs_type() -> DeclTree<RsDecl>
        = attr:attrs() "*" _ sub:rs_type() { DeclTree::Pointer { attr, sub: sub.into() } }
        / attr:(s:$(attrq()++_) _ {s})?
          "fn" _ "(" _ params:(p:rs_param()++(_ "," _) _ ","? {p})? _ ")"
          ret:(_ "->" _ r:rs_type() {r})?
            { DeclTree::Function {
                sub: ret.unwrap_or_else(|| DeclTree::Term("void".into())).into(),
                params: params.unwrap_or_default(),
                attr: attr.unwrap_or_default().into(),
            } }
        / "[" _ sub:rs_type() _ len:(";" _ l:literal() _ {l})? "]"
            { DeclTree::Array { sub: sub.into(), len } }
        / "(" _ ty:rs_type() _ ")" {ty}
        / name:$(share()++_) { DeclTree::Term(name.into()) }

    pub rule c_decls() -> Vec<CDecl>
        = d:c_decl() ++ ";" ","? ";"? {d}

    rule c_decl() -> CDecl
        = _ d:c_declare_or_cast() _ {d}

    rule c_declare_or_cast() -> CDecl
        = "(" _ p:c_cast() _ ")" name:(_ i:ident() {i})?
        {
            let mut p = p;
            assert_eq!(p.declarations.len(), 1);
            if let Some(name) = name {
                *p.declarations[0].0.term_mut() = name;
            }
            p
        }
        / c_declare()

    rule c_declare() -> CDecl
        = share:share() _ !c_heur() sub:c_declare() {
            let mut sub = sub;
            if sub.share.is_empty() {
                sub.share = share
            } else {
                sub.share = format!("{share} {}", sub.share)
            }
            sub
        }
        / share:share() _ declarations:(b:c_body() i:init() {(b, i.into())}) ++ (_ "," _)
        { CDecl { share, declarations } }

    rule c_body() -> DeclTree<CDecl>
        = attr:c_ptr() sub:c_body() { DeclTree::Pointer { attr, sub: sub.into() }}
        / sub:c_atom()
          suf:c_suffix()*
        {
            suf.into_iter().fold(sub, DeclTree::merge_suffix)
        }

    rule c_atom() -> DeclTree<CDecl>
        = "(" _ sub:c_body() _ ")" {sub}
        / name:nident() {DeclTree::Term(name)}

    rule c_cast() -> CDecl
        = share:share()++_ _ sub:c_pbody()?
        {
            let sub = (sub.unwrap_or_default(), String::new());
            CDecl { share: share.join(" "), declarations: vec![sub] }
        }

    rule c_param() -> CDecl
        = share:share() _ !c_heur() sub:c_param() {
            let mut sub = sub;
            if sub.share.is_empty() {
                sub.share = share
            } else {
                sub.share = format!("{share} {}", sub.share)
            }
            sub
        }
        / share:share() sub:(_ b:c_pbody() {b})? {
            let sub = (sub.unwrap_or_default(), String::new());
            CDecl { share, declarations: vec![sub] }
        }
        / "..." { CDecl { share: "...".to_owned(), declarations: vec![(Default::default(), String::new())] } }

    rule c_pbody() -> DeclTree<CDecl>
        = attr:c_ptr() suf:c_suffix()+
        {
            let sub = DeclTree::Term(String::new());
            DeclTree::Pointer { attr, sub: suf.into_iter().fold(sub, DeclTree::merge_suffix).into() }
        }
        / attr:c_ptr() sub:c_pbody()?
        { DeclTree::Pointer { attr, sub: sub.unwrap_or_default().into() } }
        / c_patom()

    rule c_patom() -> DeclTree<CDecl>
        = "(" _ sub:c_pbody() _ ")" suf:c_suffix()*
        {
            if suf.is_empty() {
                sub
            } else {
                suf.into_iter().fold(sub, DeclTree::merge_suffix)
            }
        }
        / name:nident() suf:c_suffix()*
        {
            let sub = DeclTree::Term(name);
            suf.into_iter().fold(sub, DeclTree::merge_suffix)
        }
        / suf:c_suffix()+
        {
            let sub = DeclTree::Term(String::new());
            suf.into_iter().fold(sub, DeclTree::merge_suffix)
        }

    rule c_suffix() -> Either<(Vec<CDecl>, String), Option<String>>
        = _ s:(f:c_func() {Left(f)} / a:c_array() {Right(a)}) {s}

    rule c_func() -> (Vec<CDecl>, String)
        = "(" _ params:c_param() ** (_ "," _) _ ")"
          attr:(_ s:$(attrq()++_) {s})?
        {(params, attr.unwrap_or_default().into())}

    rule c_array() -> Option<String>
        = "[" _ lit:(l:literal() _ {l})? "]" {lit}

    rule c_ptr() -> String
        = "*" _ attrs:attrs() {attrs}

    rule c_heur() = nident() ("(" / "[")
});

#[cfg(test)]
mod tests {
    use super::*;
    use test_buffer::{TestBuffer, test_utils::{expect, ExpectSnapshot}};

    #[track_caller]
    fn check_rs_into_c(ra_fixture_src: &str, expect: impl ExpectSnapshot) {
        let mut buf = TestBuffer::with_name(ra_fixture_src);
        let decl = parser::rs_decls(ra_fixture_src).unwrap();
        assert_eq!(decl.len(), 1);
        let output = decl.into_iter().next().unwrap().into_cdecl();

        write!(buf, "{output:#}\n");
        let re_output = output.into_rsdecl();
        assert_eq!(re_output.len(), 1);
        let re_output = format!("{:#}", re_output[0]);

        if re_output != ra_fixture_src {
            write!(buf, "{re_output}\n");
        }

        buf.expect(expect);
    }

    #[track_caller]
    fn check_c_into_rs(ra_fixture_src: &str, expect: impl ExpectSnapshot) {
        let mut buf = TestBuffer::with_name(ra_fixture_src);
        let decl = parser::c_decls(ra_fixture_src).unwrap();
        assert_eq!(decl.len(), 1);
        let output = decl.into_iter().next().unwrap().into_rsdecl();
        assert_eq!(output.len(), 1);
        let output = output.into_iter().next().unwrap();

        write!(buf, "{output:#}");
        buf.expect(expect);
    }

    #[test]
    fn rs_as_c() {
        check_rs_into_c("x: int", expect![[r#"
            int x
        "#]]);
        check_rs_into_c("x: ty", expect![[r#"
            ty x
        "#]]);
        check_rs_into_c("x: fn()", expect![[r#"
            void x()
        "#]]);
        check_rs_into_c("x: fn() -> ret", expect![[r#"
            ret x()
        "#]]);
        check_rs_into_c("x: fn() -> int", expect![[r#"
            int x()
        "#]]);
        check_rs_into_c("x: *fn() -> int", expect![[r#"
            int (*x)()
        "#]]);
        check_rs_into_c("x: const*fn() -> int", expect![[r#"
            int (*const x)()
        "#]]);
        check_rs_into_c("x: restrict*fn() -> int", expect![[r#"
            int (*restrict x)()
        "#]]);
        check_rs_into_c("x: fn(int) -> int", expect![[r#"
            int x(int)
        "#]]);
        check_rs_into_c("x: fn(m: int) -> int", expect![[r#"
            int x(int m)
        "#]]);
        check_rs_into_c("x: fn(m: *int) -> int", expect![[r#"
            int x(int *m)
        "#]]);
        check_rs_into_c("x: fn(m: *[int]) -> int", expect![[r#"
            int x(int (*m)[])
        "#]]);
        check_rs_into_c("x: fn(m: [*int]) -> int", expect![[r#"
            int x(int *m[])
        "#]]);
        check_rs_into_c("x: fn(m: *[int; 2]) -> int", expect![[r#"
            int x(int (*m)[2])
        "#]]);
        check_rs_into_c("x: fn(m: [*int; 2]) -> int", expect![[r#"
            int x(int *m[2])
        "#]]);
        check_rs_into_c("x: fn(int) -> fn()", expect![[r#"
            void x(int)()
        "#]]);
        check_rs_into_c("x: fn(int) -> fn() -> float", expect![[r#"
            float x(int)()
        "#]]);
        check_rs_into_c("x: fn(int) -> *fn() -> float", expect![[r#"
            float (*x(int))()
        "#]]);
        check_rs_into_c("x: [fn(int)]", expect![[r#"
            void x[](int)
        "#]]);
        check_rs_into_c("x: [*fn(int)]", expect![[r#"
            void (*x[])(int)
        "#]]);
        check_rs_into_c("x: [*fn(int); 2]", expect![[r#"
            void (*x[2])(int)
        "#]]);
        check_rs_into_c("x: fn(int, ...)", expect![[r#"
            void x(int, ...)
        "#]]);
        check_rs_into_c("x: fn(...)", expect![[r#"
            void x(...)
        "#]]);
        check_rs_into_c("x : fn ( m : int SIGN , ... )", expect![[r#"
            void x(int SIGN m, ...)
            x: fn(m: int SIGN, ...)
        "#]]);
        check_rs_into_c(" : fn ( m : int SIGN , ... )", expect![[r#"
            (void (int SIGN m, ...))
            : fn(m: int SIGN, ...)
        "#]]);
    }

    #[test]
    fn c_as_rs() {
        check_c_into_rs("int x", expect!["x: int"]);
        check_c_into_rs("int *x", expect!["x: *int"]);
        check_c_into_rs("int **x", expect!["x: **int"]);
        check_c_into_rs("int x[]", expect!["x: [int]"]);
        check_c_into_rs("int *x[]", expect!["x: [*int]"]);
        check_c_into_rs("int *x[2]", expect!["x: [*int; 2]"]);
        check_c_into_rs("int (*x)[]", expect!["x: *[int]"]);
        check_c_into_rs("int (*x)[2]", expect!["x: *[int; 2]"]);
        check_c_into_rs("int (*x)()", expect!["x: *fn() -> int"]);
        check_c_into_rs("int *const x", expect!["x: const*int"]);
        check_c_into_rs("int const *x", expect!["x: *int const"]);
        check_c_into_rs("int const (*x)[]", expect!["x: *[int const]"]);
        check_c_into_rs("int const *x[]", expect!["x: [*int const]"]);
        check_c_into_rs("int (*const x)[]", expect!["x: const*[int]"]);
        check_c_into_rs("int x(int)", expect!["x: fn(int) -> int"]);
        check_c_into_rs("int x(int m)", expect!["x: fn(int m) -> int"]);
        check_c_into_rs("int x(int *m)", expect!["x: fn(m: *int) -> int"]);
        check_c_into_rs("int x(int m*)", expect!["x: fn(*int m) -> int"]);
        check_c_into_rs("int x(int m())", expect!["x: fn(m: fn() -> int) -> int"]);
        check_c_into_rs("int x(int m *())", expect!["x: fn(fn() -> *int m) -> int"]);
        check_c_into_rs("int x(int *)", expect!["x: fn(*int) -> int"]);
        check_c_into_rs("int x(int *())", expect!["x: fn(fn() -> *int) -> int"]);
        check_c_into_rs("int x(int *(int))", expect!["x: fn(fn(int) -> *int) -> int"]);
        check_c_into_rs("int x(int *(int,int))", expect!["x: fn(fn(int, int) -> *int) -> int"]);
        check_c_into_rs("int x(int *(int m,int n))", expect!["x: fn(fn(int m, int n) -> *int) -> int"]);
        check_c_into_rs("int x(int *(int)())", expect!["x: fn(fn(int) -> fn() -> *int) -> int"]);
        check_c_into_rs("int x(int())", expect!["x: fn(fn() -> int) -> int"]);
        check_c_into_rs("int long x(int())", expect!["x: fn(fn() -> int) -> int long"]);
        check_c_into_rs("int x(int long())", expect!["x: fn(fn() -> int long) -> int"]);
        check_c_into_rs("int x(int (*)())", expect!["x: fn(*fn() -> int) -> int"]);
        check_c_into_rs("int x(int (*)(int))", expect!["x: fn(*fn(int) -> int) -> int"]);
        check_c_into_rs("int x(int x)", expect!["x: fn(int x) -> int"]);
        check_c_into_rs("int x(int *x)", expect!["x: fn(x: *int) -> int"]);
        check_c_into_rs("int x(int *x())", expect!["x: fn(x: fn() -> *int) -> int"]);
        check_c_into_rs("int x(int (*x))", expect!["x: fn(x: *int) -> int"]);
        check_c_into_rs("int x(int (*x)())", expect!["x: fn(x: *fn() -> int) -> int"]);
        check_c_into_rs("int x(int *(*const x)())", expect!["x: fn(x: const*fn() -> *int) -> int"]);
        check_c_into_rs("int x(int *(*x)())", expect!["x: fn(x: *fn() -> *int) -> int"]);
        check_c_into_rs("int x(int *(*(int)))", expect!["x: fn(fn(int) -> **int) -> int"]);
        check_c_into_rs("int x(int *(int))", expect!["x: fn(fn(int) -> *int) -> int"]);
        check_c_into_rs("int x(int **(int))", expect!["x: fn(fn(int) -> **int) -> int"]);
        check_c_into_rs("int x(ty)", expect!["x: fn(ty) -> int"]);
        check_c_into_rs("int long x(ty)", expect!["x: fn(ty) -> int long"]);
        check_c_into_rs("int x(ty *)", expect!["x: fn(*ty) -> int"]);
        check_c_into_rs("int x(ty *())", expect!["x: fn(fn() -> *ty) -> int"]);
        check_c_into_rs("int x(ty *(ty))", expect!["x: fn(fn(ty) -> *ty) -> int"]);
        check_c_into_rs("int x(ty *(ty,ty))", expect!["x: fn(fn(ty, ty) -> *ty) -> int"]);
        check_c_into_rs("int x(ty *(ty m,ty n))", expect!["x: fn(fn(ty m, ty n) -> *ty) -> int"]);
        check_c_into_rs("int x(ty *(ty)())", expect!["x: fn(fn(ty) -> fn() -> *ty) -> int"]);
        check_c_into_rs("int x(ty())", expect!["x: fn(fn() -> ty) -> int"]);
        check_c_into_rs("int x(ty (*)())", expect!["x: fn(*fn() -> ty) -> int"]);
        check_c_into_rs("int x(ty (*)(ty))", expect!["x: fn(*fn(ty) -> ty) -> int"]);
        check_c_into_rs("int x(ty x)", expect!["x: fn(ty x) -> int"]);
        check_c_into_rs("int x(ty *x)", expect!["x: fn(x: *ty) -> int"]);
        check_c_into_rs("int x(ty *x())", expect!["x: fn(x: fn() -> *ty) -> int"]);
        check_c_into_rs("int x(ty (*x))", expect!["x: fn(x: *ty) -> int"]);
        check_c_into_rs("int x(ty (*x)())", expect!["x: fn(x: *fn() -> ty) -> int"]);
        check_c_into_rs("int x(ty *(*x)())", expect!["x: fn(x: *fn() -> *ty) -> int"]);
        check_c_into_rs("int x(ty *(*(ty)))", expect!["x: fn(fn(ty) -> **ty) -> int"]);
        check_c_into_rs("int x(ty *(ty))", expect!["x: fn(fn(ty) -> *ty) -> int"]);
        check_c_into_rs("int x(ty **(ty))", expect!["x: fn(fn(ty) -> **ty) -> int"]);

        check_c_into_rs("int f()", expect!["f: fn() -> int"]);
        check_c_into_rs("int (*f)()", expect!["f: *fn() -> int"]);
        check_c_into_rs("int (*f)(int)", expect!["f: *fn(int) -> int"]);
        check_c_into_rs("int (*f[2])(int)", expect!["f: [*fn(int) -> int; 2]"]);
        check_c_into_rs("int (*f(int))(int)", expect!["f: fn(int) -> *fn(int) -> int"]);
        check_c_into_rs("int (*f(int))[2]", expect!["f: fn(int) -> *[int; 2]"]);

        check_c_into_rs("int f(void)", expect!["f: fn(void) -> int"]);
        check_c_into_rs("int (*f)(void)", expect!["f: *fn(void) -> int"]);
        check_c_into_rs("int x(int, ...)", expect!["x: fn(int, ...) -> int"]);
        check_c_into_rs("int x(...)", expect!["x: fn(...) -> int"]);

        check_c_into_rs("const int *x", expect!["x: *const int"]);
        check_c_into_rs("int *const *x", expect!["x: *const*int"]);
        check_c_into_rs("int **const x", expect!["x: const**int"]);
        check_c_into_rs("int (*const f)(int)", expect!["f: const*fn(int) -> int"]);

        check_c_into_rs("int x[2][3]", expect!["x: [[int; 3]; 2]"]);
        check_c_into_rs("int (*x)[2][3]", expect!["x: *[[int; 3]; 2]"]);
        check_c_into_rs("int *x[2][3]", expect!["x: [[*int; 3]; 2]"]);

        check_c_into_rs("int x(int a[2])", expect!["x: fn(a: [int; 2]) -> int"]);
        check_c_into_rs("int x(int a[])", expect!["x: fn(a: [int]) -> int"]);

        check_c_into_rs("int x(int, int)", expect!["x: fn(int, int) -> int"]);
        check_c_into_rs("int x(int a, int)", expect!["x: fn(int a, int) -> int"]);

        check_c_into_rs("unsigned long long x", expect!["x: unsigned long long"]);
        check_c_into_rs("void *x", expect!["x: *void"]);
        check_c_into_rs("struct S *x", expect!["x: *struct S"]);

        check_c_into_rs("struct S * ( * x ( int m , ... ) )()", expect!["x: fn(int m, ...) -> *fn() -> *struct S"]);

        check_c_into_rs("int *x[10]", expect!["x: [*int; 10]"]);
        check_c_into_rs("int (*x)[10]", expect!["x: *[int; 10]"]);
        check_c_into_rs("int *f()", expect!["f: fn() -> *int"]);
        check_c_into_rs("int (*f)()", expect!["f: *fn() -> int"]);
        check_c_into_rs("int *(*x[5])[10]", expect!["x: [*[*int; 10]; 5]"]);
        check_c_into_rs("int (*f(int))(int)", expect!["f: fn(int) -> *fn(int) -> int"]);
        check_c_into_rs("int (*f[3])(int)", expect!["f: [*fn(int) -> int; 3]"]);
        check_c_into_rs("void (*signal(int, void (*)(int)))(int)", expect!["signal: fn(int, *fn(int)) -> *fn(int)"]);
        check_c_into_rs("int (*f(int))[10]", expect!["f: fn(int) -> *[int; 10]"]);
        check_c_into_rs("const int *const *x", expect!["x: *const*const int"]);
        check_c_into_rs("int *const *x", expect!["x: *const*int"]);
        check_c_into_rs("int *const x[4]", expect!["x: [const*int; 4]"]);
        check_c_into_rs("int x(int (*)(int)[10])", expect!["x: fn(*fn(int) -> [int; 10]) -> int"]);
        check_c_into_rs("int x(int (*(*)(int))(char))", expect!["x: fn(*fn(int) -> *fn(char) -> int) -> int"]);
        check_c_into_rs("int typedef a", expect!["a: int typedef"]);
        check_c_into_rs("int (*x)[3][4]", expect!["x: *[[int; 4]; 3]"]);
        check_c_into_rs("int *x[3][4]", expect!["x: [[*int; 4]; 3]"]);
        check_c_into_rs("int (*f())[3][4]", expect!["f: fn() -> *[[int; 4]; 3]"]);
        check_c_into_rs("int f()[10]", expect!["f: fn() -> [int; 10]"]);
        check_c_into_rs("int f()()", expect!["f: fn() -> fn() -> int"]);
        check_c_into_rs("int f[3]()", expect!["f: [fn() -> int; 3]"]);
    }

    #[test]
    fn c_cast_as_rs() {
        check_c_into_rs("(int)x", expect!["x: int"]);
        check_c_into_rs("(int*)x", expect!["x: *int"]);
        check_c_into_rs("(int())x", expect!["x: fn() -> int"]);
        check_c_into_rs("(int*())x", expect!["x: fn() -> *int"]);
        check_c_into_rs("(int(*)())x", expect!["x: *fn() -> int"]);
        check_c_into_rs("(int x())x", expect!["x: fn() -> int x"]);
        check_c_into_rs("(int x*())x", expect!["x: fn() -> *int x"]);
        check_c_into_rs("(int x*())", expect![": fn() -> *int x"]);
    }
}
