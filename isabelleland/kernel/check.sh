#!/bin/sh
set -e
ISABELLE="${ISABELLE:-/Applications/Isabelle2025-2.app/bin/isabelle}"
exec "$ISABELLE" build -d . Anthill_Kernel
