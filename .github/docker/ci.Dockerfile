# Image for the Namespace CI workflow.
#
# The Namespace runner image ships neither `mlir-opt` nor a Python tool cache,
# so the workflow installed both on every run. Baking them in removes the
# install, which caching alone cannot do: a cache saves the download, not the
# unpacking onto a fresh machine.
#
# `elan` is baked in, but the Lean toolchain it manages is not: the toolchain is
# pinned by `lean-toolchain` and changes with the repository, so it belongs on
# the cache volume rather than in an image that would go stale.

FROM ubuntu:24.04

# `noble` matches the LLVM apt suite below.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      git \
      # `nscloud-cache-action` shells out to `sudo` to bind-mount the volume.
      sudo \
      # leanc links through the system toolchain.
      build-essential \
      # ExArray's C code resolves GMP through pkg-config.
      libgmp-dev \
      pkg-config \
 && curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key \
      -o /etc/apt/trusted.gpg.d/llvm-snapshot.asc \
 && echo "deb http://apt.llvm.org/noble/ llvm-toolchain-noble-22 main" \
      > /etc/apt/sources.list.d/llvm.list \
 && apt-get update \
 && apt-get install -y --no-install-recommends mlir-22-tools \
 && ln -s /usr/bin/mlir-opt-22 /usr/bin/mlir-opt \
 && rm -rf /var/lib/apt/lists/*

# `uv` provides both the Python interpreter and the `lit`/`filecheck`
# dependencies, so no separate Python install is needed.
COPY --from=ghcr.io/astral-sh/uv:0.9.7 /uv /usr/local/bin/uv

# `elan` manages the Lean toolchain. `ELAN_HOME` is set away from `~/.elan` so
# the path is explicit rather than tied to whichever user the job runs as; the
# CI workflow caches this directory, which is also where elan puts the
# toolchain it downloads.
ENV ELAN_HOME=/usr/local/elan
ENV PATH=/usr/local/elan/bin:$PATH
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh \
      | sh -s -- -y --default-toolchain none

# Python and the `lit`/`filecheck` dependencies, resolved from the repository's
# own lockfile so the image cannot drift from it. `uv.lock` pins `filecheck`,
# whose versions differ enough to change test outcomes, so this must stay in
# step: the `CI image` workflow rebuilds when either file changes.
COPY pyproject.toml uv.lock /opt/veir-python/
ENV UV_PYTHON_INSTALL_DIR=/opt/uv-python
ENV PATH=/opt/veir-python/.venv/bin:$PATH
RUN cd /opt/veir-python \
 && uv sync --frozen --no-install-project

# Fail the build rather than the CI run if a tool is missing.
RUN mlir-opt --version && uv --version && git --version && elan --version \
 && lit --version && filecheck --version
