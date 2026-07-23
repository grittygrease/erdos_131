# Nondividing

Lean 4 formalization of the main theorem in `Manuscript.tex`.

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake update
lake build
```

Lean is pinned by `lean-toolchain`; mathlib is pinned to the commit in
`lakefile.toml`.

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
