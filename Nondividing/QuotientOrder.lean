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

/-- Nearest multiple: for `1 ≤ r ≤ T` there is a positive multiple `m₀` of `r`
within distance `r` of `T`.  (In `projective_convexity`, `m₀·a ∈ L` lies in the
tube `T·a + ξn·B` since `r = o(ξn)`.) -/
theorem exists_nearby_multiple {r T : ℕ} (hr : 1 ≤ r) (hT : r ≤ T) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ r ∣ m₀ ∧ ((m₀ : ℤ) - T).natAbs ≤ r := by
  have hdm := Nat.div_add_mod T r
  have hcomm : (T / r) * r = r * (T / r) := Nat.mul_comm _ _
  have hmod : T % r < r := Nat.mod_lt T (by omega)
  have hdiv1 : 1 ≤ T / r := (Nat.one_le_div_iff (by omega)).mpr hT
  refine ⟨(T / r) * r, ?_, dvd_mul_left r (T / r), ?_⟩
  · calc 1 = 1 * 1 := (one_mul 1).symm
      _ ≤ (T / r) * r := Nat.mul_le_mul hdiv1 hr
  · omega

end Nondividing
