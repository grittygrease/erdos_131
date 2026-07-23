import Nondividing.Projective.Normalization
import Mathlib.Analysis.Convex.Combination

open scoped BigOperators

namespace Nondividing

/-!
# Indexed convex position (Phase E)

The manuscript's projective duality, convexity, and weighted-density arguments
count incidences of an *indexed* family (with multiplicity), not of its
deduplicated image (route hazard §7.2).  This file fixes the indexed
`μ`-convex-position predicate and the negation used to pick a failing index.
-/

/-- An indexed family `p : ι → ℝ^r` is in `μ`-convex position if for every index
`j` there is a closed half-space containing `p j` and at most `μ·|ι|` indices
(counted with multiplicity).  A half-space is `{x : t ≤ ℓ x}`. -/
def IndexedMuConvexPosition {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ℝ) (p : ι → (Fin r → ℝ)) : Prop :=
  ∀ j : ι, ∃ (ℓ : Module.Dual ℝ (Fin r → ℝ)) (t : ℝ),
    t ≤ ℓ (p j) ∧
    ((Finset.univ.filter fun k => t ≤ ℓ (p k)).card : ℝ) ≤ μ * Fintype.card ι

/-- Negation: some index `a` lies in no half-space with few indices — every
closed half-space through `p a` contains more than `μ·|ι|` indices. -/
theorem not_indexedMuConvexPosition_iff {r : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {μ : ℝ} {p : ι → (Fin r → ℝ)} :
    ¬ IndexedMuConvexPosition μ p ↔
      ∃ a : ι, ∀ (ℓ : Module.Dual ℝ (Fin r → ℝ)) (t : ℝ), t ≤ ℓ (p a) →
        μ * Fintype.card ι <
          ((Finset.univ.filter fun k => t ≤ ℓ (p k)).card : ℝ) := by
  unfold IndexedMuConvexPosition
  push_neg
  rfl

end Nondividing
