.DEFAULT_GOAL := help

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
	uv run lit Test/ -v
	[ "$(shell uname -m)" = arm64 ] || (cd ExArray && lake exe test)  # TODO: Fix LTO link bug on apple silicon
