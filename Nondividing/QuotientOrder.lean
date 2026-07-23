import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace Nondividing

/-!
# Finite quotient order (Phase E)

The projective-convexity argument uses the finite order of `a + L` in the finite
quotient `ℤ^d/L` (the step lattice): a positive multiple `r·a` lands in `L`, with
`r` dividing the index.  This is the abstract group-theoretic fact.
-/

/-- In a group with finite quotient `G/L`, some positive multiple of every element
lands in `L` (namely `r = addOrderOf (a + L)`, which divides the index). -/
theorem exists_positive_nsmul_mem {G : Type*} [AddCommGroup G] (L : AddSubgroup G)
    [Finite (G ⧸ L)] (a : G) : ∃ r : ℕ, 1 ≤ r ∧ r • a ∈ L := by
  refine ⟨addOrderOf (QuotientAddGroup.mk a : G ⧸ L), addOrderOf_pos _, ?_⟩
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul,
    addOrderOf_nsmul_eq_zero]

end Nondividing
