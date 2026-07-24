# Erdős Problem 131 — a Lean 4 formalization

**The question** ([erdosproblems.com/131](https://www.erdosproblems.com/131)):
call a set of integers *non-dividing* if no member divides the sum of any
nonempty subset of the other members. How large can a non-dividing subset of
`{1, …, N}` be?

**The answer, formalized here:** if `F(N)` is that maximum size, then

```
log F(N) / log N  →  1/5        (i.e.  F(N) = N^(1/5 + o(1)))
```

This repository contains a complete, kernel-checked Lean 4 proof of that
statement — the main theorem of the accompanying paper (`Manuscript.tex`).
The theorem is `Nondividing.main_log_limit`, and it lives in
[`Nondividing/FinalAssembly.lean`](Nondividing/FinalAssembly.lean).

---

## I just want to know: should I trust this?

You don't need to read the proof (400+ lemmas). You need three short reads
and one command. In increasing order of effort:

**1. Check the statement says the right thing (2 minutes, no download).**
Read [`Challenge.lean`](Challenge.lean). It is ~50 lines: the definition of
*non-dividing*, the definition of `F`, and the theorem statement. Nothing
else. If that file matches your understanding of the problem, the statement
is right.

**2. Check what is assumed (5 minutes).**
The proof uses Lean's three standard axioms plus **eight explicitly declared
external results** — published theorems from the literature that were taken
as axioms rather than re-proved. They live in the five short files of
[`Nondividing/External/`](Nondividing/External/) (245 lines total), each with
a citation. The list is in the table below. *This is the entire trust
surface:* everything else is verified by the Lean kernel down to mathlib.

**3. Check the proof actually proves that statement (one command).**
Build the project (next section) — it compiles with **zero `sorry`**. Then
ask Lean which axioms the theorem really uses:

```bash
echo 'import Nondividing.FinalAssembly
#print axioms Nondividing.main_log_limit' > AxCheck.lean
lake env lean AxCheck.lean && rm AxCheck.lean
```

The output must list exactly: `propext`, `Classical.choice`, `Quot.sound`,
and the eight `Nondividing.External.*` axioms. Nothing more — in particular
no `sorryAx`.

**4. (Optional, strongest) Mechanical verification with the Comparator.**
See the [Comparator section](#full-verification-with-the-comparator) below.

---

## Building the project

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager). Lean's version is pinned by `lean-toolchain`, mathlib by
`lakefile.toml`, so the build is reproducible.

```powershell
# Windows (PowerShell)
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake exe cache get   # download prebuilt mathlib (much faster than compiling it)
lake build
```

```bash
# Linux / macOS
lake exe cache get
lake build
```

A successful `lake build` means every proof in the project was checked by
the Lean kernel.

---

## Full verification with the Comparator

The [Lean FRO Comparator](https://github.com/leanprover/comparator) is an
independent tool that certifies three things at once:

- the project proves **exactly** the statement in the trusted
  `Challenge.lean` (not a lookalike),
- using **only** the whitelisted axioms,
- and the proof is accepted by the Lean kernel on replay.

The three pieces it needs are already in the repository:

| File | Role |
|---|---|
| [`Challenge.lean`](Challenge.lean) | The trusted statement (with `sorry`) |
| [`Solution.lean`](Solution.lean) | The real proof (imports the development) |
| [`comparator-config.json`](comparator-config.json) | Theorem name + axiom whitelist |

To run it:

```bash
lake build Challenge Solution
# clone and build https://github.com/leanprover/comparator, then:
lake env <path-to-comparator-binary> comparator-config.json
```

**Checking the statement online instead (no install at all):** a
self-contained one-file version of the challenge (kept locally as the
gitignored `comparator_web.lean`; it is `Challenge.lean` with the imports
inlined to `import Mathlib`) can be pasted into
[live.lean-lang.org](https://live.lean-lang.org) — it compiles against plain
mathlib with a single `sorry` warning, showing the statement is well-formed
and self-contained — or into the Challenge pane of
[comparator.live.lean-lang.org](https://comparator.live.lean-lang.org).

---

## What exactly is assumed (the eight external results)

These are the only non-foundational axioms. Each is a published result,
stated in [`Nondividing/External/`](Nondividing/External/) with its citation:

| Axiom | Source |
|---|---|
| `cfp_structure` | Conlon–Fox–Pham structure theorem, as in Pham–Zakharov, Cor. 5 |
| `discrete_john` | Pham–Zakharov, Lemma 7 (discrete John's theorem) |
| `zonotope_rounding` | Conlon–Fox–Pham rounding, as in Pham–Zakharov, Lemma 13 / eq. (15) |
| `convex_density_set` | Pham–Zakharov, Lemma 1 (convex density lemma) |
| `blaschke_selection` | Schneider, *Convex Bodies*, Thm. 1.8.6 |
| `convexBody_volume_tendsto` | Schneider, *Convex Bodies*, Thm. 1.8.20 |
| `rogers_shephard` | Rogers–Shephard difference-body inequality, Thm. 1 |
| `full_rank_lattice_points_le_volume` | Corollary of Betke–Henk–Wills, Prop. 2.1 + Minkowski's second theorem |

Everything else in the paper — including all of its named lemmas
(preprocessing, progression comparison, slab counting, one-sided filling,
index bound, projective span/duality/convexity, robust zonotope, weighted
density, cap lifting, numerology, the density-increment iteration) — is
proved in Lean from mathlib.

---

## Repository layout

| Path | Contents |
|---|---|
| `Manuscript.tex` | The paper (the informal source of truth) |
| `Nondividing/Basic.lean` | The definitions: `NonDividing`, `F` |
| `Nondividing/FinalAssembly.lean` | **The main theorem** `main_log_limit` |
| `Nondividing/External/` | The eight axioms (the trust surface) |
| `Nondividing/Audit.lean`, `Audit2.lean` | `#print axioms` for every major result |
| `Nondividing/…` | The proof: ~430 lemmas across geometry, projective framework, preprocessing, and the descent iteration |
| `Challenge.lean`, `Solution.lean`, `comparator-config.json` | Comparator verification pair |
| `FORMALIZATION_STATUS.md` | Lemma-by-lemma progress ledger kept during development |
