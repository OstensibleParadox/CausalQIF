# Roadmap

## Current status (June 2026)

The repository has a canonical Lean core in `lean/CausalQIF` with legacy material archived.
Active work should proceed only against the canonical imports and namespaces.

### Phase A — Canonicalization (done)

- Standardize package names: `causal_qif` / `CausalQIF`.
- Move active source into grouped modules under `lean/CausalQIF`.
- Migrate historical roots into:
  - `archive/legacy-dual-certificate`
  - `archive/legacy-popl27`
  - `archive/legacy-causalqif`
- Keep bridge material in `Experimental` until assumptions close.

### Phase B — Core hardening (in progress)

1. Keep `CausalQIF.lean` importing only stable modules.
2. Ensure `lake build` succeeds on active targets.
3. Remove residual root imports and stale references.
4. Add explicit root-level checks in CI/docs for:
   - forbidden imports (`FiniteQuerySandbox`, `CasualQIF`, legacy `DSeparation`)
   - stale absolute paths in docs
   - unresolved `sorry`/`admit` in active modules

### Phase C — Proof roadmap

- Validate bridge path:
  - bridge graph semantics to conditional-independence assumptions
  - preserve bridge assumptions explicitly in certificate statements
  - avoid introducing non-finite assumptions in active proofs
- Tighten theorem statements to avoid over-claiming.
- Publish stable naming for key theorem families used by downstream docs and papers.

### Phase D — Release preparation

- Finalize `MVP.md` acceptance criteria.
- Keep `docs/` aligned to active namespace and import roots only.
- Keep `provenance/MIGRATION_MANIFEST.md` updated as source locations change.
