# Agentic loop prompt — finish the `erdos_131` Lean formalization

> Paste everything below the line into Claude Code as the opening instruction of
> the loop. It is written to be handed to a fresh Claude with no prior context.
> Keep it in the repo; update the "Current state" section as work progresses.

---

## Mission

You are completing a Lean 4 + mathlib formalization of the main theorem of the
manuscript `Manuscript.tex` (Erdős problem 131 — the maximum size of a
*non-dividing* subset of `[N]` grows like `N^{1/5+o(1)}`). Work **autonomously in
a build-verified loop** until the whole development compiles with no `sorry`,
`admit`, `unsafe`, or unapproved axiom, and the audit in
`Nondividing/Audit.lean` passes.

The mathematical route is already written down. **Read these two files in full
before doing anything else, and treat them as the spec:**

- `LEAN_FORMALIZATION_ROUTE.md` — the authoritative roadmap: formal targets
  (§1), representation choices (§2), module layout (§3), the E1–E5 external
  whitelist and the *forbidden* interfaces (§4), the phase-by-phase
  implementation order (§5), the theorem dependency graph (§6), known
  formalization hazards (§7), and the audit checklist (§8).
- `Manuscript.tex` — the actual proofs. Every non-external lemma must be
  kernel-checked from earlier results, so when you formalize a step, find and
  follow the corresponding manuscript argument rather than inventing one.

## Environment (Windows / PowerShell)

Lean is managed by `elan`; `lake` lives under `%USERPROFILE%\.elan\bin`. At the
start of every shell session:

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake exe cache get   # download mathlib olean cache — do this ONCE per machine before building
lake build           # build the whole library
```

- The toolchain is pinned by `lean-toolchain` (`leanprover/lean4:v4.32.0`) and
  mathlib by the `rev` in `lakefile.toml` / `lake-manifest.json`. **Do not bump
  either** unless a fix genuinely requires it and you explain why.
- `lake exe cache get` is essential — without the prebuilt cache, building
  mathlib from source takes hours. Run it before your first build on this
  machine.
- To typecheck one file fast while iterating, build just its target, e.g.
  `lake build Nondividing.Shell`. Do a full `lake build` before declaring a
  phase done.

## Current state (update this as you go)

- **Done and green** (0 sorries): `Basic` (NonDividing / NonAveraging, `F N`,
  finiteness/attainment), `LowerBound` (translation lemma, parabola
  construction `b_i=(m^3+1)i+i^2`, `lower_construction`, `main_lower_eps`),
  `GAP` API, `Shell` (`ShellNonDividing`, `.mono`, `.map`), `Box`,
  `Geometry/RealBox`, `Geometry/ConvexLatticeJohn`, `Asymptotic`.
- **External interfaces E1–E5** are declared as whitelisted `axiom`s under
  `Nondividing/External/` (`cfp_structure`, `discrete_john`,
  `zonotope_rounding`, `convex_density_set`, `blaschke_selection`,
  `convexBody_volume_tendsto`, `rogers_shephard`,
  `full_rank_lattice_points_le_volume`).
- **`Nondividing/Main.lean` is still a stub** (empty namespace). The
  upper-bound / projective chain is **not started**.
- Track granular progress in `FORMALIZATION_STATUS.md` using its exact compact
  format (`- [x] … — green` / `- [ ] … — first blocker: <one line>`). Keep it
  terse; no logs or long reasoning in that file.

## What remains (dependency order — see route §5–§6)

Formalize in this order; each item should compile before you move on.

1. **Phase C — structural preprocessing**: `progression_comparison` (from E1,
   E2), then `unshifted_preprocessing` (accepted moves, stopping conditions,
   dimension bookkeeping, product estimate, the three output box estimates).
   Make every implicit constant a named positive constant and fold all "large
   enough" thresholds into one maximum.
2. **Phase D — geometric/arithmetic**: `slab_count`, `slab_exclusion`
   (keep the `r<d` and `r=d` cases), `one_sided_filling` (from E1/E3, tracking
   the rounding-error sign and subset-sum disjointness), `gap_contained`,
   `lattice_section_box`, `index_bound` (displayed dimension vs real rank),
   `projective_span`.
3. **Phase E — projective convexity**: indexed `μ`-convex position,
   `projective_duality`, `robust_zonotope`, `projective_convexity`.
4. **Phase F — weighted density & cap lifting**: indexed `weighted_density`
   (from E4/E5), `cap_lifting` (perspective-volume ratio; lower-rank and
   full-rank cases; exact functional transport).
5. **Phase G — numerology & density increment**: `σ₁=1/5, σ₂=1/4,
   σ_d=(d-2)/d`; `numerology` (finite case reduction + monotonicity —
   **not** `native_decide` over real inequalities); the `projective_theorem` in
   ε-form.
6. **Phase H — main theorem**: dyadic-shell pigeonhole → instantiate the
   projective theorem at `d=1`, `B=[-2X,2X]`, `λ(t)=t` → `main_upper_eps`;
   combine with `main_lower_eps` to get `main_log_limit`. Export all three
   theorem forms named in route §1 from `Nondividing/Main.lean`.
7. **Audit**: extend `Nondividing/Audit.lean` to `#print axioms` for
   `lower_construction`, `projective_convexity`, `projective_theorem`,
   `main_upper_eps`, `main_lower_eps`, and `main_log_limit`, and confirm the
   only axioms reached are the E1–E5 interfaces (plus Lean/mathlib's
   `propext`, `Classical.choice`, `Quot.sound`).

## Hard constraints (non-negotiable)

1. **No `sorry`, `admit`, `unsafe`, `decreasing_by sorry`, or `native_decide`
   over real inequalities** anywhere in `Nondividing/`.
2. **Axioms only under `Nondividing/External/`, and only from the E1–E5
   whitelist** (route §4). Each must be no stronger than its cited source and
   include every hypothesis. The interfaces listed as **forbidden** in route §4
   (translation, lower bound, functional transport, progression comparison,
   preprocessing, slab lemmas, filling, GAP containment, index, projective
   span/duality/convexity, robust zonotope, weighted density, cap lifting,
   numerology, projective theorem, main theorem) **must be proved**, never
   axiomatized.
3. **Search mathlib before adding anything to `External/`.** Only declare an
   external interface when the result is genuinely absent from mathlib.
4. **Keep imports acyclic** and each file reasonably small; follow the module
   layout in route §3 (splitting/merging is fine if imports stay acyclic).
5. Respect the **hazards in route §7** — divide-by-zero/positivity, indexed
   multiplicity vs deduplicated images, GAP displayed-dimension vs rank,
   properness radius, `φ_P` not being a global homomorphism, subset-sum
   disjointness, affine-hyperplane relative interior, the `d=1` zero-dimensional
   case, asymptotic quantifier order (fix dimensions/params, then threshold,
   then objects), and `Real.rpow`/`log` eventual-positivity.

## Loop discipline

Work in **small, compilable increments**. Each iteration:

1. Pick the next lemma from the ordered list above (respect the dependency
   graph — never depend on something unproved).
2. Locate the exact manuscript argument and the relevant mathlib API (use search
   tools; prefer existing repo abstractions from route §2).
3. Write the statement first; get it to typecheck (a scaffold with the goal
   stated is fine, but **do not leave `sorry`** — if you can't finish a lemma
   this iteration, leave it *unstated* rather than stubbed, and note it as the
   current blocker in `FORMALIZATION_STATUS.md`).
4. Prove it. Run `lake build <target>` (then a full `lake build` at phase
   boundaries). Fix all errors before moving on.
5. Update `FORMALIZATION_STATUS.md` (one line) and commit:
   `git commit -m "<phase>: <lemma> — green"`. Small, frequent, green commits.
6. If you get stuck on one lemma for a long time: try to isolate a smaller true
   sub-lemma, look for a mathlib result you missed, or reorganize — but never
   weaken a statement, never axiomatize a forbidden interface, and never paper
   over with `sorry`. If truly blocked, record the precise blocker in the status
   file and move to an independent lemma elsewhere in the graph.

## Definition of done

`lake build` is fully green from a clean checkout on the pinned toolchain;
`grep -rniE "sorry|admit|unsafe" Nondividing/` finds nothing; every `axiom` is
under `External/` and on the whitelist; and `Nondividing/Audit.lean` shows every
exported main theorem depending only on the E1–E5 interfaces plus Lean core
axioms. When all of that holds, update `FORMALIZATION_STATUS.md` so every box is
`[x] — green` and report completion.

## Reporting

At the end of each iteration, give a 2–4 line summary: what lemma is now green,
what the next target is, and any newly discovered blocker. Do not paste full
compiler logs — cite `file:line` and the one error that matters.
