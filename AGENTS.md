# Statlib

Lean 4 formalization library for mathematical statistics, built on mathlib4. See README.md for project vision and contribution workflow.

## Commands

- Build: `lake build Statlib`
- Lint: uses `batteries/runLinter` with mathlib standard set; CI runs lean-action with build, lint, and mk_all-check.
- API docs: `./build_api_docs.sh`; tutorial: `./build_tutorial.sh`.

## Structure

- `Statlib/` library modules; `Statlib.lean` is the root import.
- `docbuild/` and `tutorial-manual/` are separate Lake projects for docs.
- `scripts/nolints.json` lists allowed lint exceptions.

## Conventions

- Lean toolchain pinned in `lean-toolchain` (v4.35.0-rc4); `docbuild/` and `tutorial-manual/` must match it. Do not change without discussion.
- Design before code: open issue, discuss, implement, PR (see README).
- Add new modules to `Statlib.lean` imports.
- Prefer `rg` (ripgrep) over `grep` when searching file contents.
- Use `lean-explore` MCP tools to search Mathlib declarations.

## Boundaries

- Do not edit `.lake/` or `lake-manifest.json` unless updating dependencies.
- Do not remove entries from `scripts/nolints.json` without fixing the underlying lint.
