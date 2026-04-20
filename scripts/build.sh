#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
CMAKE_BUILD_DIR="$PROJECT_DIR/.lake/cmake-build/cuda-tile"
CMAKE_SOURCE_DIR="$PROJECT_DIR/Extern/cuda-tile"

# Default CMake options
BUILD_TYPE="${BUILD_TYPE:-Release}"
ENABLE_TOOLS="${ENABLE_TOOLS:-ON}"
ENABLE_TESTING="${ENABLE_TESTING:-ON}"
ENABLE_CCACHE="${ENABLE_CCACHE:-OFF}"
ENABLE_CAPI="${ENABLE_CAPI:-ON}"
USE_LLVM_INSTALL_DIR="${CUDA_TILE_USE_LLVM_INSTALL_DIR:-}"
USE_LLVM_SOURCE_DIR="${CUDA_TILE_USE_LLVM_SOURCE_DIR:-}"

echo "============================================"
echo "  CUDA-TILE + VeIR Build Script"
echo "============================================"
echo "Build type:     $BUILD_TYPE"
echo "Enable tools:   $ENABLE_TOOLS"
echo "Enable testing: $ENABLE_TESTING"
echo "Build dir:      $CMAKE_BUILD_DIR"
if [ -n "$USE_LLVM_INSTALL_DIR" ]; then
  echo "LLVM install:   $USE_LLVM_INSTALL_DIR"
elif [ -n "$USE_LLVM_SOURCE_DIR" ]; then
  echo "LLVM source:    $USE_LLVM_SOURCE_DIR"
else
  echo "LLVM:           (not specified - will auto-download if configured)"
fi
echo "============================================"

# Step 1: Configure CMake
echo ""
echo "[1/2] Configuring CUDA-TILE with CMake..."
if [ ! -d "$CMAKE_BUILD_DIR" ]; then
  mkdir -p "$CMAKE_BUILD_DIR"
fi

cmake_configure_args=(
  "-S" "$CMAKE_SOURCE_DIR"
  "-B" "$CMAKE_BUILD_DIR"
  "-DCMAKE_BUILD_TYPE=$BUILD_TYPE"
  "-DCUDA_TILE_ENABLE_TOOLS=$ENABLE_TOOLS"
  "-DCUDA_TILE_ENABLE_TESTING=$ENABLE_TESTING"
  "-DCUDA_TILE_ENABLE_CCACHE=$ENABLE_CCACHE"
  "-DCUDA_TILE_ENABLE_CAPI=$ENABLE_CAPI"
)

if [ -n "$USE_LLVM_INSTALL_DIR" ]; then
  cmake_configure_args+=("-DCUDA_TILE_USE_LLVM_INSTALL_DIR=$USE_LLVM_INSTALL_DIR")
fi

if [ -n "$USE_LLVM_SOURCE_DIR" ]; then
  cmake_configure_args+=("-DCUDA_TILE_USE_LLVM_SOURCE_DIR=$USE_LLVM_SOURCE_DIR")
fi

cmake "${cmake_configure_args[@]}"

# Step 2: Build CMake project
echo ""
echo "[2/2] Building CUDA-TILE..."
cmake --build "$CMAKE_BUILD_DIR" --parallel

echo ""
echo "============================================"
echo "  CUDA-TILE build complete!"
echo "  Artifacts: $CMAKE_BUILD_DIR"
echo "============================================"
echo ""
echo "Now run: lake build"
echo ""
