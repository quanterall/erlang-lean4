# lean-check image: Erlang/OTP 27 (erlang:27-slim, Debian 12) + Lean 4 + Mathlib + the Lean REPL, all pinned. A worker runs
#   cd /env && lake env /repl/.lake/build/bin/repl
# and reads JSON commands on stdin (leanprover-community/repl).
#   docker build -t lean-check docker
FROM erlang@sha256:600f0c0d8a1167bdeb8b7d055c9100d9b0b072b8b5ef2ad229a72202e83b7fe4
RUN apt-get update && apt-get install -y --no-install-recommends curl git ca-certificates xz-utils zstd \
 && rm -rf /var/lib/apt/lists/*
ARG LEAN=leanprover/lean4:v4.36.0
ARG ELAN=v4.1.2
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/$ELAN/elan-init.sh -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain $LEAN && lean --version
# the REPL at its v4.36.0 tag, checked by commit
ARG REPL=1b9fdf8ab81e52ba8651207c07e405129de2ffbe
RUN git clone -q https://github.com/leanprover-community/repl /repl && cd /repl && git checkout -q $REPL \
 && test "$(git rev-parse HEAD)" = "$REPL" && lake build 2>&1 | tail -2 && test -x .lake/build/bin/repl
# the environment the checks run in: Mathlib at its v4.36.0 tag (commit pinned in lakefile.toml), its prebuilt cache;
# this layer depends only on the lakefile and the toolchain pin
COPY env/lakefile.toml env/lean-toolchain /env/
RUN cd /env && lake update 2>&1 | tail -2 && lake exe cache get 2>&1 | tail -3 \
 && test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
# lean-check's own Lean library (PqcfCert), built and proof-checked here; the build must produce its .olean files
COPY env/LeanCheckEnv.lean /env/
COPY env/LeanCheckEnv /env/LeanCheckEnv
RUN cd /env && lake build 2>&1 | tail -3 && test -f .lake/build/lib/lean/LeanCheckEnv/PolyCert.olean \
 && test -f .lake/build/lib/lean/LeanCheckEnv.olean
WORKDIR /env
CMD ["lake", "env", "/repl/.lake/build/bin/repl"]
