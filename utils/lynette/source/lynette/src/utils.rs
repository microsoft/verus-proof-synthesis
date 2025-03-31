use colored::Colorize;
use proc_macro2::TokenStream;
use quote::ToTokens;
use std::borrow::Cow;
use std::ffi::OsStr;
use std::fmt::{self, Display};
use std::fs;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;
use syn::spanned::Spanned;

pub enum Error {
    //IncorrectUsage,
    ReadFile(io::Error),
    ParseFile { error: syn_verus::Error, filepath: PathBuf, source_code: String },
    NotFound(String),
    Conflict(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            //IncorrectUsage => write!(f, "Usage: dump-syntax path/to/filename.rs"),
            ReadFile(error) => write!(f, "Unable to read file: {}", error),
            ParseFile { error, filepath, source_code } => {
                render_location(f, error, filepath, source_code)
            }
            NotFound(func) => write!(f, "{} not found", func),
            Conflict(func) => write!(f, "Conflict: {}", func),
        }
    }
}

// Render a rustc-style error message, including colors.
//
//     error: Syn unable to parse file
//       --> main.rs:40:17
//        |
//     40 |     fn fmt(&self formatter: &mut fmt::Formatter) -> fmt::Result {
//        |                  ^^^^^^^^^ expected `,`
//
fn render_location(
    formatter: &mut fmt::Formatter,
    err: &syn_verus::Error,
    filepath: &Path,
    code: &str,
) -> fmt::Result {
    let start = err.span().start();
    let mut end = err.span().end();

    if start.line == end.line && start.column == end.column {
        return render_fallback(formatter, err);
    }

    let code_line = match code.lines().nth(start.line - 1) {
        Some(line) => line,
        None => return render_fallback(formatter, err),
    };

    if end.line > start.line {
        end.line = start.line;
        end.column = code_line.len();
    }

    let filename =
        filepath.file_name().map(OsStr::to_string_lossy).unwrap_or(Cow::Borrowed("main.rs"));

    write!(
        formatter,
        "\n\
         {error}{header}\n\
         {indent}{arrow} {filename}:{linenum}:{colnum}\n\
         {indent} {pipe}\n\
         {label} {pipe} {code}\n\
         {indent} {pipe} {offset}{underline} {message}\n\
         ",
        error = "error".red().bold(),
        header = ": Syn unable to parse file".bold(),
        indent = " ".repeat(start.line.to_string().len()),
        arrow = "-->".blue().bold(),
        filename = filename,
        linenum = start.line,
        colnum = start.column,
        pipe = "|".blue().bold(),
        label = start.line.to_string().blue().bold(),
        code = code_line.trim_end(),
        offset = " ".repeat(start.column),
        underline = "^".repeat(end.column - start.column).red().bold(),
        message = err.to_string().red(),
    )
}

fn render_fallback(formatter: &mut fmt::Formatter, err: &syn_verus::Error) -> fmt::Result {
    write!(formatter, "Unable to parse file: {}", err)
}

pub fn fload_file(filepath: &PathBuf) -> Result<syn_verus::File, Error> {
    let code = fs::read_to_string(&filepath).map_err(Error::ReadFile)?;
    let ts = proc_macro2::TokenStream::from_str(&code).unwrap();

    syn_verus::parse2::<syn_verus::File>(ts).map_err(|e| Error::ParseFile {
        error: e,
        filepath: filepath.clone(),
        source_code: code.clone(),
    })
}

pub fn is_verus_macro(m: &syn_verus::Macro) -> bool {
    m.path.is_ident("verus")
}

// pub fn extract_verus_macro(file: &syn_verus::File) -> Result<Vec<syn_verus::File>, Error> {
//     file.items.iter()
//         .filter_map(|item| {
//             if let syn_verus::Item::Macro(m) = item {
//                 if is_verus_macro(&m.mac) {
//                     return syn_verus::parse2::<syn_verus::File>(m.mac.tokens.clone()).ok();
//                 }
//             }
//             None
//         })
//         .collect::<Vec<syn_verus::File>>()
// }

pub fn extract_verus_macro(file: &syn_verus::File) -> Result<Vec<syn_verus::File>, Error> {
    file.items
        .iter()
        .filter_map(|item| {
            if let syn_verus::Item::Macro(m) = item {
                if is_verus_macro(&m.mac) {
                    Some(m.mac.tokens.clone())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .map(|tokens| {
            syn_verus::parse2::<syn_verus::File>(tokens).map_err(|e| Error::ParseFile {
                error: e,
                filepath: PathBuf::from(""),
                source_code: String::from(""),
            })
        })
        .collect()
}

pub fn fextract_verus_macro(
    filepath: &PathBuf,
) -> Result<(Vec<syn_verus::File>, syn_verus::File), Error> {
    fload_file(&filepath).and_then(|orig_file| {
        extract_verus_macro(&orig_file).and_then(|verus_files| Ok((verus_files, orig_file)))
        //(extract_verus_macro(&orig_file), orig_file)
    })
}

pub enum Formatter {
    #[allow(dead_code)]
    VerusFmt,
    RustFmt,
    Mix,
}

// Use `verusfmt` to format the a TokenStream
pub fn format_token_stream(ts: &TokenStream, formatter: Formatter) -> String {
    let verus_s = ts.to_string();

    let mut tmp_file = tempfile::NamedTempFile::new().expect("Failed to create temp file");

    tmp_file.flush().expect("Failed to flush temp file");

    let tmp_path = tmp_file.path().to_owned();

    let mut cmd = match formatter {
        Formatter::VerusFmt => {
            write!(tmp_file, "verus!{{{}}}", verus_s).expect("Failed to write to temp file");
            Command::new("verusfmt")
        }
        Formatter::RustFmt => {
            write!(tmp_file, "{}", verus_s).expect("Failed to write to temp file");
            Command::new("rustfmt")
        }
        Formatter::Mix => {
            write!(tmp_file, "{}", format_token_stream(&ts, Formatter::RustFmt))
                .expect("Failed to write to temp file");
            Command::new("verusfmt")
        }
    };

    cmd.arg(tmp_path.clone());

    let output = cmd.output().expect("Failed to run the formatter");

    if !output.status.success() {
        let stdout = String::from_utf8(output.stdout).expect("Failed to read stdout");
        let stderr = String::from_utf8(output.stderr).expect("Failed to read stderr");

        eprintln!("status: {}", output.status);
        eprintln!("stdout: {}", stdout);
        eprintln!("stderr: {}", stderr);
    }

    let formatted_code = fs::read_to_string(tmp_path).expect("Failed to read temp file");

    tmp_file.close().expect("Failed to close temp file");

    formatted_code
}

pub fn fprint_file(file: &syn_verus::File, formatter: Formatter) -> String {
    let mut ts = TokenStream::new();

    file.to_tokens(&mut ts);

    format_token_stream(&ts, formatter)
}

#[allow(dead_code)]
fn print_file(file: &syn_verus::File) -> String {
    let mut ts = TokenStream::new();

    file.to_tokens(&mut ts);

    ts.to_string()
}

#[allow(dead_code)]
pub fn fprint_function(func: &syn_verus::ItemFn, formatter: Formatter) -> String {
    let mut ts = TokenStream::new();

    func.to_tokens(&mut ts);

    format_token_stream(&ts, formatter)
}

/// Update the verus macros in the original file with the new verus macros.
/// The new verus macros are passed as a vector of TokenStream, each for a verus macro in the original file.
pub fn update_verus_macros_tss(
    orig: &syn_verus::File,
    mut verus_tss: Vec<proc_macro2::TokenStream>,
) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &orig.items {
        if let syn_verus::Item::Macro(m) = item {
            if is_verus_macro(&m.mac) {
                new_items.push(syn_verus::Item::Macro(syn_verus::ItemMacro {
                    attrs: m.attrs.clone(),
                    ident: m.ident.clone(),
                    mac: syn_verus::Macro {
                        path: m.mac.path.clone(),
                        bang_token: m.mac.bang_token.clone(),
                        delimiter: m.mac.delimiter.clone(),
                        // TODO: Ideally this should not panic but we need to handle the error just in case
                        tokens: verus_tss.pop().unwrap(),
                    },
                    semi_token: m.semi_token.clone(),
                }));
            } else {
                new_items.push(item.clone());
            }
        } else {
            new_items.push(item.clone());
        }
    }

    syn_verus::File { shebang: orig.shebang.clone(), attrs: orig.attrs.clone(), items: new_items }
}

pub fn print_block(filepath: &PathBuf, block: Rect) -> io::Result<()> {
    let file = File::open(filepath)?;
    let reader = BufReader::new(file);

    let ((start_line, _), (end_line, _)) = block;

    for (index, line) in reader.lines().enumerate() {
        let current_line = index + 1; // Line numbers start at 1
        let line = line?;

        if current_line >= start_line && current_line <= end_line {
            print_line(&line, current_line, block);
        }
    }

    Ok(())
}

#[allow(dead_code)]
pub fn print_blocks(filepath: &PathBuf, block1: Rect, block2: Rect) -> io::Result<()> {
    let file = File::open(filepath)?;
    let reader = BufReader::new(file);

    let ((block1_start_line, _), (block1_end_line, _)) = block1;
    let ((block2_start_line, _), (block2_end_line, _)) = block2;

    for (index, line) in reader.lines().enumerate() {
        let current_line = index + 1; // Line numbers start at 1
        let line = line?;

        if current_line >= block1_start_line && current_line <= block1_end_line {
            print_line(&line, current_line, block1);
        }

        if current_line >= block2_start_line && current_line <= block2_end_line {
            print_line(&line, current_line, block2);
        }
    }

    Ok(())
}

fn print_line(line: &str, current_line: usize, block: Rect) {
    let ((start_line, start_col), (end_line, end_col)) = block;
    if current_line == start_line && current_line == end_line {
        println!("{}", &line[start_col..end_col]);
    } else if current_line == start_line {
        println!("{}", &line[start_col..]);
    } else if current_line == end_line {
        println!("{}", &line[..end_col]);
    } else {
        println!("{}", line);
    }
}

#[derive(Clone)]
pub enum FnMethod {
    Fn(syn_verus::ItemFn),
    // For Method and MethodDefault, we need to keep the Trait/Struct
    // information to get the qualified name of the method.
    Method(syn_verus::ItemImpl, syn_verus::ImplItemFn),
    MethodDefault(syn_verus::ItemTrait, syn_verus::TraitItemFn),
}

pub trait FnMethodExt {
    fn get_name(&self) -> String;
    fn get_args(
        &self,
    ) -> &syn_verus::punctuated::Punctuated<syn_verus::FnArg, syn_verus::token::Comma>;
    fn get_block(&self) -> &syn_verus::Block;
    fn get_sig(&self) -> &syn_verus::Signature;
    fn get_span_rect(&self) -> Rect;
}

impl FnMethodExt for FnMethod {
    fn get_name(&self) -> String {
        match self {
            FnMethod::Fn(f) => f.sig.ident.to_string(),
            // TODO: Do we return only the method name or the qualified name?
            FnMethod::Method(i, m) => {
                format!("{}::{}", type_path_to_string(&*i.self_ty), m.sig.ident.to_string())
            }
            FnMethod::MethodDefault(i, m) => {
                format!("{}::{}", i.ident.to_string(), &m.sig.ident.to_string())
            }
        }
    }

    fn get_args(
        &self,
    ) -> &syn_verus::punctuated::Punctuated<syn_verus::FnArg, syn_verus::token::Comma> {
        match self {
            FnMethod::Fn(f) => &f.sig.inputs,
            FnMethod::Method(_, m) => &m.sig.inputs,
            FnMethod::MethodDefault(_, m) => &m.sig.inputs,
        }
    }

    fn get_block(&self) -> &syn_verus::Block {
        match self {
            FnMethod::Fn(f) => &f.block,
            FnMethod::Method(_, m) => &m.block,
            FnMethod::MethodDefault(_, _m) => unimplemented!(),
        }
    }

    fn get_sig(&self) -> &syn_verus::Signature {
        match self {
            FnMethod::Fn(f) => &f.sig,
            // TODO: Do we return only the method name or the qualified name?
            FnMethod::Method(_, m) => &m.sig,
            FnMethod::MethodDefault(_, m) => &m.sig,
        }
    }

    fn get_span_rect(&self) -> Rect {
        match self {
            FnMethod::Fn(f) => (
                (f.span().start().line, f.span().start().column),
                (f.span().end().line, f.span().end().column),
            ),
            FnMethod::Method(_, m) => (
                (m.span().start().line, m.span().start().column),
                (m.span().end().line, m.span().end().column),
            ),
            FnMethod::MethodDefault(_, m) => (
                (m.span().start().line, m.span().start().column),
                (m.span().end().line, m.span().end().column),
            ),
        }
    }
}

pub fn arg_list_to_string(
    args: &syn_verus::punctuated::Punctuated<syn_verus::Expr, syn_verus::token::Comma>,
) -> Vec<String> {
    args.iter().map(|arg| arg.to_token_stream().to_string()).collect::<Vec<_>>()
}

pub type Rect = ((usize, usize), (usize, usize));

#[allow(dead_code)]
pub fn get_sig_rect(sig: &syn_verus::Signature) -> Rect {
    (
        (sig.span().start().line, sig.span().start().column),
        (sig.span().end().line, sig.span().end().column),
    )
}

pub fn get_block_rect(block: &syn_verus::Block) -> Rect {
    (
        (block.span().start().line, block.span().start().column),
        (block.span().end().line, block.span().end().column),
    )
}

pub fn update_verus_macros_files(
    orig: &syn_verus::File,
    verus_files: Vec<syn_verus::File>,
) -> syn_verus::File {
    let verus_tss: Vec<proc_macro2::TokenStream> = verus_files
        .iter()
        .map(|file| {
            let mut ts = TokenStream::new();
            file.to_tokens(&mut ts);
            ts
        })
        .collect();

    update_verus_macros_tss(orig, verus_tss)
}

static TARGET_IDENT: &str = "(llm4verus_target)";

pub fn attrs_have_target(attrs: &Vec<syn_verus::Attribute>) -> bool {
    // FIXME:
    //attrs.iter().any(|attr| attr.tokens.to_string() == TARGET_IDENT)
    false
}

pub fn func_is_target(f: &syn_verus::ItemFn) -> bool {
    attrs_have_target(&f.attrs)
}

pub fn method_is_target(m: &syn_verus::ImplItemFn) -> bool {
    attrs_have_target(&m.attrs)
}

pub fn sig_is_ghost(s: &syn_verus::Signature) -> bool {
    match s.mode {
        syn_verus::FnMode::Default => false,
        _ => true,
    }
}

pub fn func_is_ghost(f: &syn_verus::ItemFn) -> bool {
    sig_is_ghost(&f.sig)
}

pub fn method_is_ghost(m: &syn_verus::ImplItemFn) -> bool {
    sig_is_ghost(&m.sig)
}

pub fn attrs_have_ext_spec(attrs: &Vec<syn_verus::Attribute>) -> bool {
    // FIXME
    // attrs.iter().any(|attr| {
    //     attr.path.segments.len() == 2
    //         && attr.path.segments[0].ident.to_string() == "verifier"
    //         && attr.path.segments[1].ident.to_string() == "external_fn_specification"
    //         && attr.tokens.is_empty()
    // })
    false
}

pub fn func_is_ext_spec(f: &syn_verus::ItemFn) -> bool {
    attrs_have_ext_spec(&f.attrs)
}

pub fn method_is_ext_spec(m: &syn_verus::ImplItemFn) -> bool {
    attrs_have_ext_spec(&m.attrs)
}

pub fn type_path_to_string(t: &syn_verus::Type) -> String {
    if let syn_verus::Type::Path(p) = t {
        p.path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::")
    } else {
        String::new()
    }
}
