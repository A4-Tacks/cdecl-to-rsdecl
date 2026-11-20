use std::{
    env::args,
    io::{stdin, Read},
    process::exit,
    slice,
    str::FromStr,
    sync::atomic::Ordering,
};

use atty::Stream;
use cdecl_to_rsdecl::{color, parser, CDecl, RsDecl, COLOR};
use char_classes as cc;
use getopts_macro::getopts::Matches;
use rustyline as rl;
use peg::str::LineCol;

const PROG_NAME: &str = env!("CARGO_BIN_NAME");

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

fn main() {
    let options = getopts_macro::getopts_options! {
        -c                  "parse rust, into c";
        -a, --auto          "auto try reverse parse";
        -o, --owned         "c owned rule, e.g `int f(int())` -> `int f(int (*)())`";
            --color*?=MODE  "color mode";
        -h, --help*         "show help message";
        -v, --version       "show version";
    };
    let args = args().skip(1).collect::<Vec<_>>();
    let matches = match options.parse(&args) {
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

    match matches.opt_positions("color").last()
        .map(|&i| args[i].split_once('=')
            .map_or("always", |it| it.1))
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
        let mut rl = rl::DefaultEditor::new().unwrap();

        let is_exit = |line: &str| {
            ["exit", "quit"].contains(
                &line.trim().trim_end_matches(['(', ')', ';']).trim_matches('`'),
            )
        };

        loop {
            match rl.readline("> ") {
                Ok(line) if is_exit(&line) => break,
                Ok(line) => {
                    if let Err(e) = rl.add_history_entry(line.clone()) {
                        println!("Can't entry history: {e}")
                    }
                    process(&matches, &line)
                },
                Err(rustyline::error::ReadlineError::Interrupted) => {},
                Err(rustyline::error::ReadlineError::Eof) => break,
                Err(e) => panic!("unhandle error: {e}"),
            }
        }
    } else {
        let buf = &mut String::new();
        stdin().read_to_string(buf).unwrap();
        process(&matches, buf);
    }
}

fn process(matches: &Matches, s: &str) {
    let s = s.trim_end();
    let mut to_c = matches.opt_present("c");

    if matches.opt_present("auto") {
        let parsed_c = parser::c_decls(s).is_ok();
        let parsed_rs = parser::rs_decls(s).is_ok();

        if !parsed_rs && parsed_c {
            to_c = false
        } else if parsed_rs && !parsed_c {
            to_c = true
        }
    }

    if to_c {
        let mut rsdecls = parse_rs(s);
        owned_processor(matches, &mut rsdecls);
        rsdecls.into_iter()
            .map(RsDecl::into_cdecl)
            .for_each(|cdecl|
        {
            println!("{cdecl:#};");
        });
    } else {
        let cdecls = parse_c(s);
        cdecls.into_iter()
            .flat_map(CDecl::into_rsdecl)
            .for_each(|mut rsdecl|
        {
            owned_processor(matches, slice::from_mut(&mut rsdecl));
            println!("{rsdecl:#};");
        });
    }
}

fn owned_processor(matches: &Matches, rsdecls: &mut [RsDecl]) {
    if !matches.opt_present("owned") { return }
    for rsdecl in rsdecls {
        rsdecl.make_owned_param();
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
        .take_while(cc::any!(^" \t\r\n"))
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
