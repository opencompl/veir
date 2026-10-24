# Custom base image for the Namespace runner profile used by
# `nightly-llvm-latest.yml`.
#
# It is the sibling of `namespace-base-image.Dockerfile`, which pins its LLVM
# so that pull-request CI is reproducible and the cross-checks in `Test/lit.cfg`
# match their pinned versions. This one resolves the newest LLVM release at
# build time instead, and `nightly-llvm-latest.yml` rebuilds it every night, so
# the nightly run says whether the next LLVM release breaks us before it reaches
# the pinned image.
#
# Unlike its sibling, this file is applied to the profile by that workflow with
# `nsc github profile update --dockerfile`, so it is the source of truth rather
# than a copy to paste into the dashboard. A profile build still has no build
# context: nothing can be `COPY`ed from the repository.

ARG NAMESPACE_BASE_IMAGE_REF=""

# Your image must build FROM NAMESPACE_BASE_IMAGE_REF
FROM ${NAMESPACE_BASE_IMAGE_REF} AS base

# Installing needs root; the image switches back to `runner` below, which the
# GitHub runner software requires.
USER root

RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git \
 && rm -rf /var/lib/apt/lists/*

# The newest LLVM release, and the apt suite to match it.
#
# Every suite apt.llvm.org publishes is a nightly snapshot build, not a
# release: the versioned ones track a release branch and the unversioned one
# tracks main, so `llvm-toolchain-<codename>-23` can read `23.1.5~++<date>+<sha>`
# while the newest release is still `llvmorg-23.1.4`. The suites are therefore
# only good for naming the series; the release itself comes from the tags.
#
# A series is taken in descending order and the first one that has a release is
# used. During the qualification of a major, its suite exists while its first
# release is not yet tagged, and skipping it keeps the build off a series it
# could not name a release on. Candidates are tagged `-rc<n>` and the pattern
# leaves them out. Asking git rather than the GitHub API keeps the build off an
# anonymous rate limit that a shared builder address would exhaust.
RUN . /etc/os-release \
 && for major in $(curl -fsSL "https://apt.llvm.org/${VERSION_CODENAME}/dists/" \
      | sed -n "s|.*llvm-toolchain-${VERSION_CODENAME}-\\([0-9][0-9]*\\)/.*|\\1|p" \
      | sort -rn); do \
      release=$(git ls-remote --tags --refs https://github.com/llvm/llvm-project \
          "llvmorg-${major}.*" \
        | sed 's|.*/||' \
        | grep -E "^llvmorg-${major}\\.[0-9]+\\.[0-9]+$" \
        | sort -V | tail -1); \
      if [ -n "${release}" ]; then \
        echo "${major}" > /tmp/llvm-major; \
        echo "${release}" > /tmp/llvm-release; \
        break; \
      fi; \
      echo "no release on LLVM ${major} yet, trying the series below"; \
    done \
 && test -s /tmp/llvm-major && test -s /tmp/llvm-release \
 && echo "LLVM major $(cat /tmp/llvm-major), release $(cat /tmp/llvm-release)"

# The suite of the series resolved above, so it is known to be published. What
# it installs is a snapshot of that release branch rather than the release
# itself, which is close enough for `mlir-opt`: `Test/lit.cfg` selects the MLIR
# compatibility tests by major alone.
RUN . /etc/os-release \
 && major=$(cat /tmp/llvm-major) \
 && curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key \
      -o /etc/apt/trusted.gpg.d/llvm-snapshot.asc \
 && echo "deb http://apt.llvm.org/${VERSION_CODENAME}/ llvm-toolchain-${VERSION_CODENAME}-${major} main" \
      > /etc/apt/sources.list.d/llvm.list \
 && apt-get update \
 && apt-get install -y --no-install-recommends \
      "mlir-${major}-tools" \
      # leanc links through the system toolchain.
      build-essential \
 && ln -s "/usr/bin/mlir-opt-${major}" /usr/bin/mlir-opt \
 && rm -rf /var/lib/apt/lists/*

# The interpreter tests cross-check themselves against two interpreters of
# LLVM IR that no one packages: `llubi`, which is a tool of the LLVM tree, and
# Alive2's `alive-exec`. Both are built against the release resolved above, so
# that the tests see the semantics they were written against. Alive2 needs that
# LLVM to carry RTTI and exceptions, which the packaged one does not promise.
#
# Alive2 is taken at its default branch rather than at a commit: a commit old
# enough to be pinned will not compile against an LLVM newer than itself, and
# for a nightly whose job is to find breakage early, a build failure is the
# signal rather than something to engineer around.
#
# Only the two binaries are kept; the sources and the LLVM build go again.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      cmake ninja-build python3 libz3-dev re2c \
 && git clone --depth 1 --branch "$(cat /tmp/llvm-release)" \
      https://github.com/llvm/llvm-project /tmp/llvm \
 && cmake -S /tmp/llvm/llvm -B /tmp/llvm/build -GNinja \
      -DCMAKE_BUILD_TYPE=Release \
      -DLLVM_TARGETS_TO_BUILD=host \
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
 && llubi --version \
 && alive-exec --version \
 && uv --version \
 && lit --version \
 && filecheck --version \
 && elan --version
