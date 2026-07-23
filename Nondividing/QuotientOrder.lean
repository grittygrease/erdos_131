import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Nondividing.Shell

open scoped BigOperators

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

/-- The order of any element of a finite quotient is at most the index
(`r ≪ γ⁻¹` in `thm:projective-convexity`, combined with `index_bound_part2`). -/
theorem addOrderOf_quotient_le_index {G : Type*} [AddCommGroup G]
    (L : AddSubgroup G) (hL : L.index ≠ 0) (a : G) :
    addOrderOf (QuotientAddGroup.mk a : G ⧸ L) ≤ L.index := by
  haveI : Finite (G ⧸ L) := AddSubgroup.index_ne_zero_iff_finite.mp hL
  have hdvd : addOrderOf (QuotientAddGroup.mk a : G ⧸ L) ∣ Nat.card (G ⧸ L) :=
    addOrderOf_dvd_natCard _
  rw [← AddSubgroup.index_eq_card] at hdvd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hdvd

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

/-- **Projective-convexity endgame** (`thm:projective-convexity`, final assembly).
Given the tube inclusion `L ∩ (T·a + ξn·B) ⊆ Σ(V∖{a})` supplied by the deep
lemmas (`one_sided_filling`, `robust_zonotope`, `index_bound`), and the finite
step-quotient with element order `r ≤ min(T, ξn)`, one derives a contradiction
with shell non-dividing: the nearest positive multiple `m₀·a` of `r` to `T` lies
in `L ∩ (T·a + ξn·B)`, hence is a subset sum, contradicting
`shellNonDividing_no_positive_multiple`. -/
theorem projective_convexity_of_tube {d : ℕ} (ℓ : (Fin d → ℤ) →+ ℤ) {X : ℕ}
    {V : Finset (Fin d → ℤ)} (hX : 1 ≤ X)
    (hV : ShellNonDividing (fun v => ℓ v) X V) {a : Fin d → ℤ} (haV : a ∈ V)
    (L : AddSubgroup (Fin d → ℤ)) [Finite ((Fin d → ℤ) ⧸ L)]
    {T ξn : ℕ} {M : Fin d → ℕ} (haM : a ∈ coordinateBox M)
    (hrT : addOrderOf (QuotientAddGroup.mk a : (Fin d → ℤ) ⧸ L) ≤ T)
    (hrξ : addOrderOf (QuotientAddGroup.mk a : (Fin d → ℤ) ⧸ L) ≤ ξn)
    (htube : ∀ y ∈ L, y - T • a ∈ coordinateBox (fun i => ξn * M i) →
      y ∈ subsetSums (V.erase a)) :
    False := by
  classical
  set r := addOrderOf (QuotientAddGroup.mk a : (Fin d → ℤ) ⧸ L) with hr
  have hr1 : 1 ≤ r := addOrderOf_pos _
  have hra : r • a ∈ L := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul,
      addOrderOf_nsmul_eq_zero]
  obtain ⟨m₀, hm₀1, ⟨k, hk⟩, hm₀T⟩ := exists_nearby_multiple hr1 hrT
  have hm₀a : m₀ • a ∈ L := by
    rw [hk, mul_comm r k, mul_smul]; exact L.nsmul_mem hra k
  -- `m₀·a` lies in the tube `T·a + ξn·B`
  have htubemem : (m₀ • a) - T • a ∈ coordinateBox (fun i => ξn * M i) := by
    rw [mem_coordinateBox]
    intro i
    have hai := (mem_coordinateBox.mp haM) i
    have h1 : (m₀ • a) i = (m₀ : ℤ) * a i := by rw [Pi.smul_apply, nsmul_eq_mul]
    have h2 : (T • a) i = (T : ℤ) * a i := by rw [Pi.smul_apply, nsmul_eq_mul]
    have hcoord : (m₀ • a - T • a) i = ((m₀ : ℤ) - T) * a i := by
      rw [Pi.sub_apply, h1, h2]; ring
    have habs1 : |((m₀ : ℤ) - T)| ≤ (r : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hm₀T
    have habs2 : |a i| ≤ (M i : ℤ) := abs_le.mpr hai
    have hrξZ : (r : ℤ) ≤ ξn := by exact_mod_cast hrξ
    have hbound : |((m₀ : ℤ) - T) * a i| ≤ (ξn : ℤ) * M i := by
      rw [abs_mul]
      calc |((m₀ : ℤ) - T)| * |a i| ≤ (r : ℤ) * (M i : ℤ) :=
            mul_le_mul habs1 habs2 (abs_nonneg _) (by positivity)
        _ ≤ (ξn : ℤ) * (M i : ℤ) :=
            mul_le_mul_of_nonneg_right hrξZ (by positivity)
    rw [hcoord]
    rw [abs_le] at hbound
    push_cast
    exact ⟨hbound.1, hbound.2⟩
  exact shellNonDividing_no_positive_multiple ℓ hX hV haV hm₀1
    (htube _ hm₀a htubemem)

end Nondividing
