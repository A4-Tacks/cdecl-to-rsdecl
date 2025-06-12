use std::{
    env::args,
    fmt::Display,
    io::{stdin, Read},
    mem::take,
    process::exit,
    slice,
    str::FromStr,
    sync::atomic::{AtomicBool, Ordering},
};

use atty::Stream;
use char_classes::FirstElem;
use either::Either::{self, Left, Right};
use getopts_macro::getopts::Matches;
use linefeed as lf;
use peg::{str::LineCol, RuleResult};


macro_rules! any {
    ($($pat:tt)*) => {
        |str, i| str[i..].first_elem()
            .filter(char_classes::any!($($pat)*))
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

const PROG_NAME: &str = env!("CARGO_BIN_NAME");
static COLOR: AtomicBool = AtomicBool::new(false);

macro_rules! color {
    ($color:literal $(; $color1:literal)*, $e:expr) => {{
        if COLOR.load(Ordering::Acquire) {
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

enum ColorMode {
    Always,
    Auto,
    Never,
}

impl FromStr for ColorMode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "always" | "yes" | "force" => Self::Always,
            "never" | "no" | "none" => Self::Never,
            "auto" | "tty" | "if-tty" => Self::Auto,
            _ => Err(format!("invalid color mode: {s:?}"))?,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
struct CDecl {
    share: String,
    declarations: Vec<DeclTree<Self>>,
}

impl CDecl {
    fn into_rsdecl(self) -> Vec<RsDecl> {
        self.declarations.into_iter()
            .map(|cdecl| {
                let mut rsdecl = RsDecl {
                    name: Default::default(),
                    ty: DeclTree::Term(self.share.clone()),
                };

                cdecl.cdecl_to_rsdecl(&mut rsdecl);
                rsdecl
            })
            .collect()
    }
}

impl Display for CDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.share)?;
        if let Some(first) = self.declarations.first() {
            let first_output = first.output_c();
            if !self.share.is_empty()
            && !first_output.is_empty()
            && !first_output.starts_with('[')
            && !first_output.ends_with('*')
            {
                f.write_str(" ")?;
            }
            f.write_str(&first_output)?;

            for rest in &self.declarations[1..] {
                write!(f, ", {}", rest.output_c())?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
struct RsDecl {
    name: String,
    ty: DeclTree<Self>,
}

impl RsDecl {
    fn into_cdecl(self) -> CDecl {
        let mut c_decl = CDecl {
            share: Default::default(),
            declarations: vec![
                DeclTree::Term(self.name),
            ],
        };
        self.ty.rsdecl_to_cdecl(&mut c_decl);
        c_decl
    }
}

impl Display for RsDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.name.is_empty() {
            f.write_str(&self.ty.output_rs())
        } else {
            write!(f, "{}: {}", self.name, self.ty.output_rs())
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum DeclTree<Param> {
    Pointer { attr: String, sub: Box<Self> },
    Function { sub: Box<Self>, params: Vec<Param> },
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
            DeclTree::Function { sub, params } => {
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
                format!("{}({params}){ret}", color!(33, "fn"))
            },
            DeclTree::Array { sub, len } => {
                if let Some(len) = len {
                    format!("[{}; {}]", sub.output_rs(), color!(1;34, len))
                } else {
                    format!("[{}]", sub.output_rs())
                }
            },
            DeclTree::Term(s) => s.clone(),
        }
    }

    fn rsdecl_to_cdecl(self, decl: &mut CDecl) {
        let ty = decl.declarations.first_mut().unwrap();
        match self {
            DeclTree::Pointer { attr, sub } => {
                *ty = DeclTree::Pointer { attr, sub: take(ty).into() };
                sub.rsdecl_to_cdecl(decl);
            },
            DeclTree::Function { sub, params } => {
                let params = params.into_iter()
                    .map(RsDecl::into_cdecl)
                    .collect();
                *ty = DeclTree::Function { sub: take(ty).into(), params };
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
                    format!("{} {}", color!(1, format_args!("*{attr}")), sub.output_c())
                }
            },
            DeclTree::Function { sub, params } => {
                let params = params.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(&color!(1;35, ", "));
                format!("{}({})", paren(sub.is_pointer(), &sub.output_c()), params)
            },
            DeclTree::Array { sub, len } => {
                let sub = paren(sub.is_pointer(), &sub.output_c());
                if let Some(len) = len {
                    format!("{sub}[{}]", color!(1;34, len))
                } else {
                    format!("{sub}[]")
                }
            },
            DeclTree::Term(s) => s.clone(),
        }
    }

    fn merge_suffix(self, suf: Either<Vec<CDecl>, Option<String>>) -> Self {
        let sub = Box::new(self);
        match suf {
            Left(params) => DeclTree::Function { sub, params },
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
            DeclTree::Function { sub, params } => {
                let ty = take(&mut decl.ty);
                let params = params.into_iter()
                    .map(CDecl::into_rsdecl)
                    .inspect(|decls| assert_eq!(decls.len(), 1))
                    .map(|decls| decls.into_iter().next().unwrap())
                    .collect();
                decl.ty = DeclTree::Function { sub: ty.into(), params };
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
}

const KWDS: &[&str] = &[
    "auto", "break", "case", "char", "const", "continue", "default", "do",
    "double", "else", "enum", "extern", "float", "for", "goto", "if",
    "inline", "int", "long", "register", "restrict", "return", "short", "signed",
    "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void",
    "volatile", "while",
];

peg::parser!(grammar parser() for str {
    rule ident() -> String
        = s:$(#{any!("a-zA-Z_")} #{any!("a-zA-Z0-9_")}*)
        { s.into() }
        / expected!("ident")
    rule nident() -> String
        = i:ident() #{is(!KWDS.contains(&&*i))} {i}
        / expected!("ident")
    rule number()
        = quiet!{"0x" / "0X"} #{any!("0-9a-fA-F")}+ num_suf()
        / quiet!{"0b" / "0B"} #{any!("01")}+ num_suf()
        / #{any!("0-9")}+ num_suf()
        / expected!("number")
    rule literal() -> String
        = s:$(number()) { s.into() }
        / ident()
    rule attr() = "const" / "volatile" / "restrict"
    rule attrs() -> String = s:(s:$(attr()++_) _ {s})? {s.unwrap_or_default().into()}
    rule num_suf() = #{any!("uUlL")}*
    rule _() = #{any!(" \t\r\n")}*
    rule __() = #{any!(" \t\r\n")}+

    rule tt()
        = "{" tt()* "}"
        / "(" tt()* ")"
        / "[" tt()* "]"
        / #{any!(^"{}()[]")} _

    rule adt() = ("struct" / "union" / "enum") (__ ident())? (_ &"{" tt())?
    rule share() -> String
        = s:$(adt()) {s.into()}
        / ident()

    pub rule rs_decls() -> Vec<RsDecl>
        = d:rs_decl() ++ ";" ";"? {d}

    rule rs_decl() -> RsDecl
        = _ name:ident() _ ":" _ ty:rs_type() _
        { RsDecl { name, ty } }

    rule rs_param() -> RsDecl
        = _ name:(n:ident() _ ":" _ {n})? ty:rs_type() _
        { RsDecl { name: name.unwrap_or_default(), ty } }

    rule rs_type() -> DeclTree<RsDecl>
        = attr:attrs() "*" _ sub:rs_type() { DeclTree::Pointer { attr, sub: sub.into() } }
        / "[" _ sub:rs_type() _ len:(";" _ l:literal() _ {l})? "]"
            { DeclTree::Array { sub: sub.into(), len } }
        / "fn" _ "(" _ params:(p:rs_param()++"," ","? {p})? _ ")" ret:(_ "->" _ r:rs_type() {r})?
            { DeclTree::Function {
                sub: ret.unwrap_or_else(|| DeclTree::Term("void".into())).into(),
                params: params.unwrap_or_default(),
            } }
        / "(" _ ty:rs_type() _ ")" {ty}
        / name:$(share()**_) { DeclTree::Term(name.into()) }

    pub rule c_decls() -> Vec<CDecl>
        = d:c_decl() ++ ";" ";"? {d}

    rule c_decl() -> CDecl
        = _ d:c_declare_or_cast() _ {d}

    rule c_declare_or_cast() -> CDecl
        = "(" _ p:c_param() _ ")" name:(_ i:ident() {i})?
        {
            let mut p = p;
            assert_eq!(p.declarations.len(), 1);
            if let Some(name) = name {
                *p.declarations[0].term_mut() = name;
            }
            p
        }
        / c_declare()

    rule c_declare() -> CDecl
        = share:share() !"(" _ sub:c_declare() {
            let mut sub = sub;
            if sub.share.is_empty() {
                sub.share = share
            } else {
                sub.share = format!("{share} {}", sub.share)
            }
            sub
        }
        / declarations:c_body() ++ (_ "," _)
        { CDecl { share: String::new(), declarations } }

    rule c_body() -> DeclTree<CDecl>
        = "*" _ attr:attrs() sub:c_body() { DeclTree::Pointer { attr, sub: sub.into() }}
        / sub:c_atom()
          suf:c_suffix()*
        {
            suf.into_iter().fold(sub, DeclTree::merge_suffix)
        }

    rule c_atom() -> DeclTree<CDecl>
        = "(" _ sub:c_body() _ ")" {sub}
        / name:nident() {DeclTree::Term(name)}

    rule c_param() -> CDecl
        = share:share()++_ _ sub:c_pbody()?
        {
            let mut sub = sub.unwrap_or_default();
            CDecl { share: share.join(" "), declarations: vec![sub] }
        }

    rule c_pbody() -> DeclTree<CDecl>
        = attr:c_ptr() sub:c_pbody()?
        { DeclTree::Pointer { attr, sub: sub.unwrap_or_default().into() }}
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
        / suf:c_suffix()+
        {
            let sub = DeclTree::Term(String::new());
            suf.into_iter().fold(sub, DeclTree::merge_suffix)
        }

    rule c_suffix() -> Either<Vec<CDecl>, Option<String>>
        = _ s:(f:c_func() {Left(f)} / a:c_array() {Right(a)}) {s}

    rule c_func() -> Vec<CDecl>
        = "(" _ params:c_param() ++ (_ "," _) _ ")" {params}
        / "(" _ ")" { vec![] }

    rule c_array() -> Option<String>
        = "[" _ lit:(l:literal() _ {l})? "]" {lit}

    rule c_ptr() -> String
        = "*" _ attrs:attrs() {attrs}
});

fn main() {
    let options = getopts_macro::getopts_options! {
        -c                  "parse rust, into c";
        -o, --owned         "c owned rule, e.g `int f(int())` -> `int f(int (*)())`";
            --color*=MODE   "color mode";
        -h, --help*         "show help message";
        -v, --version       "show version";
    };
    let matches = match options.parse(args().skip(1)) {
        Ok(matches) => matches,
        Err(e) => {
            eprintln!("{e}");
            exit(2);
        },
    };

    if matches.opt_present("help") {
        let brief = format!(
            "Usage: {PROG_NAME} [Options] [decl]..\n{}",
            env!("CARGO_PKG_DESCRIPTION"),
        );
        let usage = options.usage(&brief);
        print!("{usage}");
        exit(0)
    }

    if matches.opt_present("version") {
        println!("v{}", env!("CARGO_PKG_VERSION"));
        exit(0)
    }

    match matches.opt_strs("color")
        .into_iter()
        .next_back()
        .as_deref()
        .unwrap_or("never")
        .parse()
    {
        Ok(ColorMode::Never) => COLOR.store(false, Ordering::Release),
        Ok(ColorMode::Always) => COLOR.store(true, Ordering::Release),
        Ok(ColorMode::Auto) => {
            COLOR.store(atty::is(Stream::Stdout), Ordering::Release)
        },
        Err(e) => {
            eprintln!("{e}");
            exit(2)
        },
    }


    if !matches.free.is_empty() {
        for s in &matches.free {
            process(&matches, s);
        }
        return;
    }

    if atty::is(Stream::Stdin) && atty::is(Stream::Stdout) {
        if atty::is(Stream::Stdout) {
            println!("Welcome to {PROG_NAME}, input `exit` to exit");
        }
        let lf = lf::Interface::new(PROG_NAME)
            .expect("Failed to open interactive");

        lf.set_prompt("> ").unwrap();
        lf.set_history_size(300);

        while let lf::ReadResult::Input(line) = lf.read_line().unwrap() {
            if ["exit", "quit"].contains(&line.trim()
                .trim_end_matches(['(', ')', ';'])
                .trim_matches('`'))
            {
                break;
            }

            if !line.is_empty() {
                lf.add_history_unique(line.clone());
            }

            process(&matches, &line);
        }
    } else {
        let buf = &mut String::new();
        stdin().read_to_string(buf).unwrap();
        process(&matches, buf);
    }
}

fn process(matches: &Matches, s: &str) {
    let s = s.trim_end();

    if matches.opt_present("c") {
        let mut rsdecls = parse_rs(s);
        owned_processor(matches, &mut rsdecls);
        rsdecls.into_iter()
            .map(RsDecl::into_cdecl)
            .for_each(|cdecl|
        {
            println!("{cdecl};");
        });
    } else {
        let cdecls = parse_c(s);
        cdecls.into_iter()
            .flat_map(CDecl::into_rsdecl)
            .for_each(|mut rsdecl|
        {
            owned_processor(matches, slice::from_mut(&mut rsdecl));
            println!("{rsdecl};");
        });
    }
}

fn owned_processor(matches: &Matches, rsdecls: &mut [RsDecl]) {
    if !matches.opt_present("owned") { return }
    for rsdecl in rsdecls {
        rsdecl.ty.c_owned_param();
    }
}

fn parse_c(s: &str) -> Vec<CDecl> {
    match parser::c_decls(s) {
        Ok(v) => v,
        Err(e) => error(s, e),
    }
}

fn parse_rs(s: &str) -> Vec<RsDecl> {
    match parser::rs_decls(s) {
        Ok(v) => v,
        Err(e) => error(s, e),
    }
}

fn error<T>(s: &str, e: peg::error::ParseError<LineCol>) -> Vec<T> {
    let near = s[e.location.offset..]
        .chars()
        .take_while(char_classes::any!(^" \t\r\n"))
        .take(5)
        .collect::<String>();
    if e.location.offset == s.len() {
        eprint!("at eof ");
    } else if !near.is_empty() {
        eprint!("near `{near}` ");
    }
    eprintln!("{}", color!(31;1, e));
    Vec::new()
}
