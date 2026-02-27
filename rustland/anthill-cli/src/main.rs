use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use anthill_core::codegen::generate_rust;
use anthill_core::parse;

// ── CLI types ───────────────────────────────────────────────────────

#[derive(Parser)]
#[command(name = "anthill", about = "Anthill language toolkit")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Generate host-language code from .anthill sources
    Codegen {
        #[command(subcommand)]
        target: CodegenTarget,
    },
}

#[derive(Subcommand)]
enum CodegenTarget {
    /// Generate Rust skeleton code (traits, structs, enums)
    Rust(RustCodegenArgs),
}

#[derive(Parser)]
struct RustCodegenArgs {
    /// .anthill files or directories to process
    #[arg(required = true)]
    paths: Vec<PathBuf>,

    /// Output directory for generated .rs files
    #[arg(short, long, default_value = "./generated")]
    output_dir: PathBuf,

    /// Print what would be generated without writing files
    #[arg(long)]
    dry_run: bool,
}

// ── File collection ─────────────────────────────────────────────────

fn collect_anthill_files(paths: &[PathBuf]) -> Result<Vec<PathBuf>, Vec<String>> {
    let mut files = Vec::new();
    let mut errors = Vec::new();

    for path in paths {
        if !path.exists() {
            errors.push(format!("path does not exist: {}", path.display()));
            continue;
        }
        if path.is_dir() {
            collect_from_dir(path, &mut files);
        } else if path.extension().and_then(|e| e.to_str()) == Some("anthill") {
            files.push(path.clone());
        } else {
            errors.push(format!("not an .anthill file: {}", path.display()));
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    files.sort();
    files.dedup();
    Ok(files)
}

fn collect_from_dir(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("warning: cannot read directory {}: {e}", dir.display());
            return;
        }
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_from_dir(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("anthill") {
            out.push(path);
        }
    }
}

// ── Output naming ───────────────────────────────────────────────────

fn output_filename(input: &Path) -> String {
    let stem = input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("out");
    format!("{stem}.rs")
}

// ── Codegen driver ──────────────────────────────────────────────────

fn run_codegen_rust(args: &RustCodegenArgs) -> Result<(), i32> {
    let files = match collect_anthill_files(&args.paths) {
        Ok(f) => f,
        Err(errs) => {
            for e in &errs {
                eprintln!("error: {e}");
            }
            return Err(1);
        }
    };

    if files.is_empty() {
        eprintln!("error: no .anthill files found");
        return Err(1);
    }

    if !args.dry_run {
        if let Err(e) = fs::create_dir_all(&args.output_dir) {
            eprintln!("error: cannot create output directory {}: {e}", args.output_dir.display());
            return Err(1);
        }
    }

    let mut errors: Vec<String> = Vec::new();
    let mut generated = 0u32;

    for file in &files {
        let source = match fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                errors.push(format!("{}: read error: {e}", file.display()));
                continue;
            }
        };

        let parsed = match parse::parse(&source) {
            Ok(p) => p,
            Err(parse_errors) => {
                for pe in &parse_errors {
                    errors.push(format!("{}: {pe}", file.display()));
                }
                continue;
            }
        };

        let rust_code = generate_rust(&parsed);
        let out_name = output_filename(file);
        let out_path = args.output_dir.join(&out_name);

        if args.dry_run {
            println!("[dry-run] {} -> {}", file.display(), out_path.display());
        } else {
            if let Err(e) = fs::write(&out_path, &rust_code) {
                errors.push(format!("{}: write error: {e}", out_path.display()));
                continue;
            }
            println!("{} -> {}", file.display(), out_path.display());
        }
        generated += 1;
    }

    if !errors.is_empty() {
        eprintln!();
        for e in &errors {
            eprintln!("error: {e}");
        }
        eprintln!();
    }

    let verb = if args.dry_run { "would generate" } else { "generated" };
    eprintln!("{verb} {generated} file(s), {} error(s)", errors.len());

    if errors.is_empty() {
        Ok(())
    } else {
        Err(1)
    }
}

// ── Entry point ─────────────────────────────────────────────────────

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = match cli.command {
        Command::Codegen { target } => match target {
            CodegenTarget::Rust(ref args) => run_codegen_rust(args),
        },
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
