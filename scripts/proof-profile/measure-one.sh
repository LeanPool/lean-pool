#!/usr/bin/env bash
# Measure one file at one git revision with Lean's command
# heartbeat profiler plus wall time, into
# <outdir>/<slugified-path>.log. The source comes from `git show`
# and is compiled out-of-tree against whatever environment is
# currently built (imports resolve by module name, not path), so
# the working tree never has to sit at <ref>.
ref="$1"
file="$2"
outdir="$3"
# The checksum disambiguates paths that collide under `tr` (an
# underscore in a directory name vs a slash).
slug="$(printf '%s' "$file" | tr '/' '_')_$(printf '%s' "$file" | cksum | cut -d' ' -f1)"
src="$outdir/src-$slug.lean"
{
  echo "## $file"
  if git show "$ref:$file" > "$src"; then
    # The deprecated linter retries declarations after they already exist and
    # can report only the failed retry's cost. Trace the original elaboration.
    # Keep it synchronous so command totals include theorem bodies and kernel
    # checking. Enable only command traces; the high threshold suppresses the
    # nested profiler nodes, which would produce enormous logs and double count.
    /usr/bin/time -p "$HOME/.elan/bin/lake" env lean \
      -DElab.async=false \
      -Dtrace.Elab.command=true \
      -Dtrace.profiler=true \
      -Dtrace.profiler.useHeartbeats=true \
      -Dtrace.profiler.threshold=1000000000000000000 \
      "$src"
    status=$?
    if [ "$status" -ne 0 ]; then
      echo "error: count-heartbeats command exited with status $status"
    else
      echo "success: count-heartbeats command exited with status 0"
    fi
  else
    echo "error: could not read $file at revision $ref"
  fi
  echo
} > "$outdir/$slug.log" 2>&1
rm -f "$src"
