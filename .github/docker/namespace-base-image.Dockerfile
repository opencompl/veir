# Custom base image for the Namespace runner profile used by
# `lean_action_ci_namespace.yml`.
#
# This file is not built by CI. Namespace builds it from the Dockerfile field of
# the runner profile in the dashboard, so the copy here is the source of truth
# to edit and paste back. A profile build has no build context: nothing can be
# `COPY`ed from the repository, which is why the Python tool versions below are
# spelled out rather than resolved from `uv.lock`.
#
# The Namespace runner image ships neither `mlir-opt` nor a Python tool cache,
# so the workflow installed both on every run. Baking them in removes the
# install, which caching alone cannot do: a cache saves the download, not the
# unpacking onto a fresh machine. `llubi` and `alive-exec` are built from
# source for a second reason: neither is packaged, so the interpreter tests
# that cross-check against them would always skip.

ARG NAMESPACE_BASE_IMAGE_REF=""

# Your image must build FROM NAMESPACE_BASE_IMAGE_REF
FROM ${NAMESPACE_BASE_IMAGE_REF} AS base

# Installing needs root; the image switches back to `runner` below, which the
# GitHub runner software requires.
USER root

# `noble` matches the Ubuntu 24.04 base image. On a different base image, change
# the LLVM apt suite to match.
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl \
 && curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key \
      -o /etc/apt/trusted.gpg.d/llvm-snapshot.asc \
 && echo "deb http://apt.llvm.org/noble/ llvm-toolchain-noble-23 main" \
      > /etc/apt/sources.list.d/llvm.list \
 && apt-get update \
 && apt-get install -y --no-install-recommends \
      mlir-23-tools \
      # leanc links through the system toolchain.
      build-essential \
 && ln -s /usr/bin/mlir-opt-23 /usr/bin/mlir-opt \
 && rm -rf /var/lib/apt/lists/*

# The interpreter tests cross-check themselves against two interpreters of
# LLVM IR that no one packages: `llubi`, which is a tool of the LLVM tree, and
# Alive2's `alive-exec`. Both are built here against one LLVM, which has to be
# the release the rest of the image uses, so that the tests see the semantics
# they were written against. Alive2 needs that LLVM to carry RTTI and
# exceptions, which the packaged one does not promise.
#
# Only the two binaries are kept; the sources and the LLVM build go again.
ARG LLVM_RELEASE=llvmorg-23.1.2
ARG ALIVE2_COMMIT=01a5ec45c8152995755f7331827407a9de19f262

RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      cmake ninja-build git python3 libz3-dev re2c \
 && git clone --depth 1 --branch "${LLVM_RELEASE}" \
      https://github.com/llvm/llvm-project /tmp/llvm \
 && cmake -S /tmp/llvm/llvm -B /tmp/llvm/build -GNinja \
      -DCMAKE_BUILD_TYPE=Release \
      -DLLVM_TARGETS_TO_BUILD=host \
      -DLLVM_ENABLE_RTTI=ON \
      -DLLVM_ENABLE_EH=ON \
 && cmake --build /tmp/llvm/build \
 && git clone https://github.com/AliveToolkit/alive2 /tmp/alive2 \
 && git -C /tmp/alive2 checkout -q "${ALIVE2_COMMIT}" \
 # Alive2 only looks for LLVM, and only offers `alive-exec`, once it is
 # asked for the tools that use LLVM. The translation validation plugin,
 # which `BUILD_TV` would add, is not needed here.
 && cmake -S /tmp/alive2 -B /tmp/alive2/build -GNinja \
      -DCMAKE_BUILD_TYPE=Release \
      -DBUILD_LLVM_UTILS=1 \
      -DLLVM_DIR=/tmp/llvm/build/lib/cmake/llvm \
 && cmake --build /tmp/alive2/build --target alive-exec \
 && install -m 0755 /tmp/llvm/build/bin/llubi /usr/bin/llubi \
 && install -m 0755 /tmp/alive2/build/alive-exec /usr/bin/alive-exec \
 && rm -rf /tmp/llvm /tmp/alive2 /var/lib/apt/lists/*

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
# which tests pass.
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
 && llubi --version \
 && alive-exec --version \
 && uv --version \
 && lit --version \
 && filecheck --version \
 && elan --version
