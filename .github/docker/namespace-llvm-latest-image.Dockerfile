# Custom base image for the Namespace runner profile that
# `lean_action_ci_llvm_latest.yml` runs on, rebuilt nightly by
# `rebuild-llvm-latest-image.yml`.
#
# It is the sibling of `namespace-base-image.Dockerfile`, which pins its LLVM
# so that pull-request CI is reproducible and the cross-checks in `Test/lit.cfg`
# match their pinned versions. This one builds LLVM's main branch instead, so
# that a change which breaks us is found while it is still upstream, months
# before it reaches a release and that pin is moved forward.
#
# It carries the whole toolchain, because the workflow that uses it does not
# activate the Nix development environment: that environment pins
# `llvmPackages_23`, and its `clang`, `llvm` and `mlir-opt` would come ahead of
# these on PATH.
#
# Unlike its sibling, this file is applied to the profile with
# `nsc github profile update --dockerfile`, so it is the source of truth rather
# than a copy to paste into the dashboard. A profile build still has no build
# context: nothing can be `COPY`ed from the repository. `COPY --from=<stage>`
# is a different thing and does work, which is what the staged build below
# relies on.

ARG NAMESPACE_BASE_IMAGE_REF=""

# Your image must build FROM NAMESPACE_BASE_IMAGE_REF
FROM ${NAMESPACE_BASE_IMAGE_REF} AS base

# Installing needs root; the image switches back to `runner` below, which the
# GitHub runner software requires.
USER root

# Everything the build needs that is not LLVM: what `flake.nix` listed besides
# the toolchain, and what compiling LLVM takes.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      ca-certificates curl git \
      cmake ninja-build python3 \
      # What the flake supplied besides LLVM, and what leanc links against.
      libgmp-dev pkg-config build-essential \
 && rm -rf /var/lib/apt/lists/*

# The LLVM build happens in a stage of its own. Only the install tree is
# copied forward, so the sources and the object files cannot reach the final
# image even for the length of one layer. The sibling image drops them with
# `rm -rf` at the end of the same `RUN`, which keeps them out of the image too
# but still needs the space while the layer is being built.
FROM base AS llvm-builder

# How many compile jobs the LLVM build may run at once. Ninja defaults to one
# per core plus two, and an LLVM or MLIR translation unit can take a couple of
# gigabytes, so on a wide builder that asks for more memory than any of them
# has and the build is killed rather than slowed. `LLVM_PARALLEL_LINK_JOBS`
# does not help with this: it is the compile phase that is wide.
#
# The budget is read from the cgroup the build runs in, falling back to the
# machine's memory when it is unlimited, so this follows the builder rather
# than guessing at it.
RUN mem=$(cat /sys/fs/cgroup/memory.max 2>/dev/null || true); \
    case "${mem}" in ''|max) mem=$(awk '/MemTotal/ {print $2 * 1024}' /proc/meminfo) ;; esac; \
    jobs=$((mem / 4000000000)); \
    if [ "${jobs}" -lt 1 ]; then jobs=1; fi; \
    if [ "${jobs}" -gt "$(nproc)" ]; then jobs=$(nproc); fi; \
    echo "${jobs}" > /tmp/llvm-jobs; \
    echo "memory ${mem}, $(nproc) cpus, ${jobs} compile jobs"

# The one LLVM this image carries, built from main and installed: `clang`,
# `llvm-config` and `mlir-opt` for the build and the MLIR compatibility tests,
# and `llubi` for the interpreter cross-checks. `llubi` is built from source
# because nothing packages it.
#
# Alive2's `alive-exec` is the other cross-check and is not here. It was
# dropped while this image tracked releases, which its default branch cannot
# build against because that branch follows LLVM's main branch. That is the
# branch built here now, so it could come back; until it does, `Test/lit.cfg`
# reports it missing and skips those cross-checks, which
# `namespace-base-image.Dockerfile` still runs at its pinned LLVM.
RUN git clone --depth 1 https://github.com/llvm/llvm-project /tmp/llvm \
 && git -C /tmp/llvm rev-parse HEAD > /tmp/llvm-revision \
 && echo "LLVM main at $(cat /tmp/llvm-revision)" \
 && cmake -S /tmp/llvm/llvm -B /tmp/llvm/build -GNinja \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_INSTALL_PREFIX=/usr/local \
      -DLLVM_TARGETS_TO_BUILD="host;RISCV" \
      -DLLVM_ENABLE_PROJECTS="clang;mlir" \
      -DLLVM_ENABLE_RTTI=ON \
      -DLLVM_ENABLE_EH=ON \
      # Limit parallelism of compile and link jobs
      -DLLVM_PARALLEL_COMPILE_JOBS="$(cat /tmp/llvm-jobs)" \
      -DLLVM_PARALLEL_LINK_JOBS=1 \
      # None of these is installed or run here, and MLIR's and clang's test
      # libraries are a large part of what the unrestricted build compiles.
      # `llubi` is an ordinary `add_llvm_tool` in `llvm/tools/llubi`, so it is
      # not one of the targets this drops.
      -DLLVM_INSTALL_UTILS=ON \
      -DLLVM_INCLUDE_TESTS=OFF \
      -DCLANG_INCLUDE_TESTS=OFF \
      -DMLIR_INCLUDE_TESTS=OFF \
      -DLLVM_INCLUDE_EXAMPLES=OFF \
      -DLLVM_INCLUDE_BENCHMARKS=OFF \
 && cmake --build /tmp/llvm/build \
 # Installing, rather than copying `llubi` out and discarding the rest, is
 # what lets `clang` keep its resource headers and gives `mlir-opt` and
 # `llvm-config` the same provenance as it.
 && DESTDIR=/stage cmake --install /tmp/llvm/build \
 && install -D -m 0755 /tmp/llvm/build/bin/llubi /stage/usr/local/bin/llubi \
 # Which commit this is was readable from `/tmp/llvm-revision` when the build
 # and the image were one stage. Carry it over, so the image can still say.
 && install -D -m 0644 /tmp/llvm-revision /stage/usr/local/share/veir/llvm-revision

# The image itself, which never sees a compiler input. `/stage` holds exactly
# what `cmake --install` and the two `install` calls above put there, so this
# is the same `/usr/local` the single-stage build produced.
FROM base AS final

COPY --from=llvm-builder /stage/usr/local /usr/local

# `uv` provides both the Python interpreter and the test dependencies, so no
# separate Python install is needed.
COPY --from=ghcr.io/astral-sh/uv:0.12.2 /uv /usr/local/bin/uv

USER runner

# Everything below installs into `runner`'s home at its default location. Doing
# it as root instead puts the interpreter and the tool virtualenvs under
# `/root`, and no amount of `chmod` on the target makes them usable: `/root` is
# mode 0700, so `runner` cannot traverse it to reach them.
#
# `HOME` is set explicitly because `USER` alone does not reliably set it during
# a build, and every default path below is derived from it.
ENV HOME=/home/runner
ENV PATH=/home/runner/.local/bin:/home/runner/.elan/bin:$PATH

# Pinned to the versions `uv.lock` resolves. Keep them in step by hand: the
# lockfile cannot be read here, and `filecheck` versions differ enough to change
# which tests pass. These do not float with LLVM: the point of this image is to
# vary one thing.
RUN uv python install 3.13 \
 && uv tool install --python 3.13 lit==18.1.8 \
 && uv tool install --python 3.13 filecheck==1.0.3

# `elan` manages the Lean toolchain; the toolchain itself is not baked in, since
# `lean-toolchain` pins it and it belongs on the cache volume. Installing as
# `runner` puts elan in `$HOME/.elan`, which is where `lean-action` looks.
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh \
      | sh -s -- -y --default-toolchain none

# Fail the image build rather than a CI run if a tool is missing or is not
# reachable as `runner`. Every tool is tried and the report names each one, so
# a failure here says which is absent rather than only that one of them is.
#
# GMP is checked by compiling against it rather than by looking for its header.
RUN status=0; \
    for tool in mlir-opt clang llvm-config llubi split-file uv lit filecheck elan; do \
      if out=$("${tool}" --version 2>&1); then \
        echo "ok   ${tool}: $(printf '%s' "${out}" | head -1)"; \
      else \
        echo "FAIL ${tool}: $(printf '%s' "${out}" | head -1)"; \
        status=1; \
      fi; \
    done; \
    printf '#include <gmp.h>\nint main(void) { return 0; }\n' > /tmp/gmp-check.c; \
    if cc -c /tmp/gmp-check.c -o /dev/null 2>&1; then \
      echo "ok   gmp.h"; \
    else \
      echo "FAIL gmp.h is not usable by the compiler"; \
      status=1; \
    fi; \
    rm -f /tmp/gmp-check.c; \
    exit "${status}"
