#!/bin/sh
# lean-check's tests inside its image, on a copy of the source (nothing written into the checkout):
# the screen's tests without Lean, then the Lean tests with one worker (Mathlib is imported once, then each check
# runs in a fresh environment). No network for the container.
#   sh tools/test.sh
set -e
cd "$(dirname "$0")/.."
docker run --rm --network none -v "$PWD":/src:ro lean-check sh -c '
  mkdir /w && cd /src && tar --exclude=./_build -cf - . | (cd /w && tar xf -) && cd /w &&
  rebar3 eunit && rebar3 dialyzer && rebar3 xref'
