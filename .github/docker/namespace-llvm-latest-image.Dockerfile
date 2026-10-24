# Custom base image for the Namespace runner profile that
# `lean_action_ci_llvm_latest.yml` runs on, rebuilt nightly by
# `rebuild-llvm-latest-image.yml`.
#
# It is the sibling of `namespace-base-image.Dockerfile`, which pins its LLVM
# so that pull-request CI is reproducible and the cross-checks in `Test/lit.cfg`
# match their pinned versions. This one resolves the newest LLVM release at
# build time instead, so that a release which breaks us is found before that
# pin is next moved forward.
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
# the toolchain, and what compiling LLVM and Alive2 takes.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      ca-certificates curl git \
      cmake ninja-build python3 libz3-dev re2c \
      # What the flake supplied besides LLVM, and what leanc links against.
      libgmp-dev pkg-config build-essential \
 && rm -rf /var/lib/apt/lists/*

# The LLVM build happens in a stage of its own. Only the install tree is
# copied forward, so the sources and the object files cannot reach the final
# image even for the length of one layer. The sibling image drops them with
# `rm -rf` at the end of the same `RUN`, which keeps them out of the image too
# but still needs the space while the layer is being built.
FROM base AS llvm-builder

# The newest LLVM release, as the highest `llvmorg-<major>.<minor>.<patch>` tag
# the repository carries. Candidates are tagged `-rc<n>` and the pattern leaves
# them out, so this is the newest release and not the next one. Asking git
# rather than the GitHub API keeps the build off an anonymous rate limit that a
# shared builder address would exhaust.
#
# apt.llvm.org is deliberately not used. Every suite it publishes is a nightly
# snapshot of a branch rather than a release, so taking `mlir-opt` from there
# while building `llubi` from a tag would put two different LLVMs in one image.
RUN git ls-remote --tags --refs https://github.com/llvm/llvm-project 'llvmorg-*' \
      | sed 's|.*/||' \
      | grep -E '^llvmorg-[0-9]+\.[0-9]+\.[0-9]+$' \
      | sort -V | tail -1 > /tmp/llvm-release \
 && test -s /tmp/llvm-release \
 && echo "LLVM release $(cat /tmp/llvm-release)"

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
    jobs=$((mem / 2500000000)); \
    if [ "${jobs}" -lt 1 ]; then jobs=1; fi; \
    if [ "${jobs}" -gt "$(nproc)" ]; then jobs=$(nproc); fi; \
    echo "${jobs}" > /tmp/llvm-jobs; \
    echo "memory ${mem}, $(nproc) cpus, ${jobs} compile jobs"

# The one LLVM this image carries, built from the release resolved above and
# installed: `clang`, `llvm-config` and `mlir-opt` for the build and the MLIR
# compatibility tests, and `llubi` for the interpreter cross-checks. Alive2's
# `alive-exec` is the other cross-check and is built against the same LLVM, so
# the tests see one set of semantics rather than two. Both interpreters are
# built from source because nothing packages them, and Alive2 needs an LLVM
# with RTTI and exceptions, which a packaged one does not promise.
#
# Alive2 is taken at its default branch rather than at a commit: a commit old
# enough to be pinned will not compile against an LLVM newer than itself, and
# for an image whose job is to find breakage early, a build failure is the
# signal rather than something to engineer around.
RUN git clone --depth 1 --branch "$(cat /tmp/llvm-release)" \
      https://github.com/llvm/llvm-project /tmp/llvm \
 && cmake -S /tmp/llvm/llvm -B /tmp/llvm/build -GNinja \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_INSTALL_PREFIX=/usr/local \
      -DLLVM_TARGETS_TO_BUILD=host \
      -DLLVM_ENABLE_PROJECTS="clang;mlir" \
      -DLLVM_ENABLE_RTTI=ON \
      -DLLVM_ENABLE_EH=ON \
      # Ninja runs one job per core, and an LLVM link step takes gigabytes, so
      # on a builder with many cores the links are what exhausts the memory.
      # Serialising them is what keeps this build inside the builder's RAM.
      -DLLVM_PARALLEL_COMPILE_JOBS="$(cat /tmp/llvm-jobs)" \
      -DLLVM_PARALLEL_LINK_JOBS=1 \
      # None of these is installed or run here, and MLIR's and clang's test
      # libraries are a large part of what the unrestricted build compiles.
      # `llubi` is an ordinary `add_llvm_tool` in `llvm/tools/llubi`, so it is
      # not one of the targets this drops.
      -DLLVM_INCLUDE_TESTS=OFF \
      -DCLANG_INCLUDE_TESTS=OFF \
      -DMLIR_INCLUDE_TESTS=OFF \
      -DLLVM_INCLUDE_EXAMPLES=OFF \
      -DLLVM_INCLUDE_BENCHMARKS=OFF \
 && cmake --build /tmp/llvm/build \
 && git clone --depth 1 https://github.com/AliveToolkit/alive2 /tmp/alive2 \
 # Alive2 only looks for LLVM, and only offers `alive-exec`, once it is
 # asked for the tools that use LLVM. The translation validation plugin,
 # which `BUILD_TV` would add, is not needed here.
 && cmake -S /tmp/alive2 -B /tmp/alive2/build -GNinja \
      -DCMAKE_BUILD_TYPE=Release \
      -DBUILD_LLVM_UTILS=1 \
      -DLLVM_DIR=/tmp/llvm/build/lib/cmake/llvm \
 && cmake --build /tmp/alive2/build --target alive-exec \
 # Installing, rather than copying out the two interpreters and discarding the
 # rest, is what lets `clang` keep its resource headers and gives `mlir-opt`
 # and `llvm-config` the same provenance as `llubi`.
 && DESTDIR=/stage cmake --install /tmp/llvm/build \
 && install -D -m 0755 /tmp/llvm/build/bin/llubi /stage/usr/local/bin/llubi \
 && install -D -m 0755 /tmp/alive2/build/alive-exec /stage/usr/local/bin/alive-exec \
 # Which release this is was readable from `/tmp/llvm-release` when the build
 # and the image were one stage. Carry it over, so the image can still say.
 && install -D -m 0644 /tmp/llvm-release /stage/usr/local/share/veir/llvm-release

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
# reachable as `runner`. If a run reports `command not found` for one of these,
# the image did not build and the profile fell back to the stock base image.
RUN mlir-opt --version \
 && clang --version \
 && llvm-config --version \
 && test -f /usr/include/gmp.h \
 && llubi --version \
 && alive-exec --version \
 && uv --version \
 && lit --version \
 && filecheck --version \
 && elan --version
