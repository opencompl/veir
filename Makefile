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
	lake build parser-tests allocator-tests ir-reuse-tests
	lake exe parser-tests
	lake exe allocator-tests
	lake exe ir-reuse-tests
	uv run python Tools/check-buffed-wrapper-codegen
	uv run lit Test/ -v
	cd ExArray && lake exe test

.PHONY: sqlite
sqlite: build ## test sqlite3 parsing (expected to fail until fully supported)
	test -f /tmp/sqlite3.c || (curl -sfL https://sqlite.org/2026/sqlite-amalgamation-3530300.zip -o /tmp/sqlite.zip && unzip -oqj /tmp/sqlite.zip '*/sqlite3.c' -d /tmp && rm /tmp/sqlite.zip)
	Tools/vcc --emit-mlir /tmp/sqlite3.c -o /dev/null
