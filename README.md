# Nondividing

Lean 4 formalization of the main theorem in `Manuscript.tex`
([Erdős problem 131](https://www.erdosproblems.com/131)):

> **`Nondividing.main_log_limit`** (`Nondividing/FinalAssembly.lean`):
> the maximum size `F(N)` of a *non-dividing* subset of `{1, …, N}` satisfies
> `log F(N) / log N → 1/5`, i.e. `F(N) = N^{1/5+o(1)}`.

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake update
lake build
```

Lean is pinned by `lean-toolchain`; mathlib is pinned to the commit in
`lakefile.toml`.

## Verifying the formalization (Comparator)

Following the [Lean FRO Comparator](https://github.com/leanprover/comparator)
workflow, the repository ships a mechanically checkable statement/proof pair,
so a referee does **not** have to trawl the 400+ lemmas:

- **`Challenge.lean`** — the trusted surface: the two definitions
  (`NonDividing`, `F`) and the main statement, with `sorry`. Read this file
  (≈50 lines) to check the theorem *says what it should*.
- **`Solution.lean`** — imports the full development; its environment contains
  the real `Nondividing.main_log_limit`.
- **`comparator-config.json`** — names the theorem and whitelists the
  permitted axioms: Lean's `propext`, `Classical.choice`, `Quot.sound` plus
  the eight E1–E5 interfaces below (and nothing else).

To run the Comparator locally (it kernel-replays the proof and certifies the
solution proves *exactly* the challenge statement under the whitelist):

```bash
lake build Challenge Solution
# clone + build https://github.com/leanprover/comparator, then:
lake env <path-to-comparator-binary> comparator-config.json
```

Two lighter checks that need no extra tooling:

```bash
# axiom audit: must print exactly core + the eight E1–E5 axioms
echo 'import Nondividing.FinalAssembly
#print axioms Nondividing.main_log_limit' > AxCheck.lean
lake env lean AxCheck.lean && rm AxCheck.lean

# statement identity: Challenge's statement is byte-identical (pp.all) to the
# proven theorem's — compare `#check @Nondividing.main_log_limit` under
# `set_option pp.all true` in the two environments (import Challenge vs
# import Nondividing.FinalAssembly) and diff the output.
```

The complete trust surface is: `Challenge.lean` + `comparator-config.json` +
the five short files in `Nondividing/External/` (245 lines, the statements of
the whitelisted axioms).

**Lean 4 Web.** A self-contained single-file version of the challenge
(definitions + statement against `import Mathlib`) is kept locally as
`comparator_web.lean` (gitignored; regenerate by inlining `Challenge.lean`'s
imports to `import Mathlib`). Paste it at
[live.lean-lang.org](https://live.lean-lang.org) to check the statement
compiles, or into the Challenge pane at
[comparator.live.lean-lang.org](https://comparator.live.lean-lang.org).

## Trusted external interfaces

The only non-foundational interfaces are the whitelisted results in
`Nondividing/External/`:

- `cfp_structure` — Conlon–Fox–Pham / Pham–Zakharov, Corollary 5;
- `discrete_john` — Pham–Zakharov, Lemma 7;
- `zonotope_rounding` — Conlon–Fox–Pham as used in Pham–Zakharov,
  Lemma 13 and equation (15);
- `convex_density_set` — Pham–Zakharov, Lemma 1;
- `blaschke_selection` and `convexBody_volume_tendsto` — Schneider,
  Theorems 1.8.6 and 1.8.20;
- `rogers_shephard` — Rogers–Shephard, Theorem 1;
- `full_rank_lattice_points_le_volume` — the stated corollary of
  Betke–Henk–Wills, Proposition 2.1, and Minkowski's second theorem.
