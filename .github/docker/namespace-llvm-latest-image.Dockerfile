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
# context: nothing can be `COPY`ed from the repository.

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
      | grep -E '^llvmorg-[0-9]+\\.[0-9]+\\.[0-9]+$' \
      | sort -V | tail -1 > /tmp/llvm-release \
 && test -s /tmp/llvm-release \
 && echo "LLVM release $(cat /tmp/llvm-release)"

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
 && cmake --install /tmp/llvm/build \
 && install -m 0755 /tmp/llvm/build/bin/llubi /usr/local/bin/llubi \
 && install -m 0755 /tmp/alive2/build/alive-exec /usr/local/bin/alive-exec \
 && rm -rf /tmp/llvm /tmp/alive2

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
