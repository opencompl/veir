.DEFAULT_GOAL := help

LEAN_CC ?= $(CURDIR)/Tools/lean-clang
export LEAN_CC

.PHONY: help
help: ## show this help message
	@grep -E '^[a-zA-Z_-]+:.*?## ' $(MAKEFILE_LIST) | \
		awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-8s\033[0m %s\n", $$1, $$2}'

.PHONY: build
build: ## build the project
	lake build

.PHONY: tests
tests: build ## run all tests
	uv sync
	lake test
	lake build parser-tests allocator-tests ir-allocation-tests
	lake exe parser-tests
	lake exe allocator-tests
	lake exe ir-allocation-tests
	uv run python Tools/check-buffed-wrapper-codegen
	uv run python Tools/check-orphan-modules
	uv run python Tools/check-parser-cli
	cd ExArray && lake exe test
