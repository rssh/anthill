#!/usr/bin/env bash
# Generate PDF from design documents
# Usage: ./scripts/generate-pdf.sh [input.md] [output.pdf]
#   or:  ./scripts/generate-pdf.sh --all

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

generate_pdf() {
  local input="$1"
  local output="$2"
  local title="$3"

  echo "Generating: $output"
  pandoc "$input" -o "$output" \
    --pdf-engine=xelatex \
    -H "$SCRIPT_DIR/pdf-header.tex" \
    -V geometry:margin=1in \
    -V fontsize=11pt \
    -V mainfont="Arial Unicode MS" \
    -V monofont="Menlo" \
    -V colorlinks=true \
    -V linkcolor=blue \
    -V urlcolor=blue \
    --toc \
    -V title="$title"
  echo "  Done: $output"
}

if [[ "${1:-}" == "--all" ]]; then
  mkdir -p "$PROJECT_DIR/pdf"

  generate_pdf \
    "$PROJECT_DIR/docs/kernel-language.md" \
    "$PROJECT_DIR/pdf/kernel-language.pdf" \
    "The Anthill — Kernel Language Specification"

  generate_pdf \
    "$PROJECT_DIR/docs/rust-forward-mapping.md" \
    "$PROJECT_DIR/pdf/rust-forward-mapping.pdf" \
    "The Anthill — Rust Forward Mapping"

  generate_pdf \
    "$PROJECT_DIR/docs/cli-design.md" \
    "$PROJECT_DIR/pdf/cli-design.pdf" \
    "The Anthill — CLI Design"

  echo "All PDFs generated in $PROJECT_DIR/pdf/"
else
  INPUT="${1:-$PROJECT_DIR/docs/kernel-language.md}"
  OUTPUT="${2:-$PROJECT_DIR/pdf/kernel-language.pdf}"
  TITLE="${3:-The Anthill — Kernel Language Specification}"
  mkdir -p "$(dirname "$OUTPUT")"
  generate_pdf "$INPUT" "$OUTPUT" "$TITLE"
fi
