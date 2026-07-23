import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Nondividing.Geometry.GAPVolume

open scoped BigOperators
open MeasureTheory

namespace Nondividing

/-!
# Slab volume via a determinant-1 shear (Phase F, `lem:slab-count` r = d)

The Fubini step `vol(B_ℝ ∩ {|u(x)| ≤ τw}) ≤ dτ·vol(B_ℝ)` is implemented by a
shear: the linear map fixing all coordinates except `x_j ↦ u(x)/a_j` has
determinant 1 and sends the slanted slab into a thin product box.
-/

/-- The shear matrix: identity except row `j`, which is `(a_i/a_j)_i`. -/
noncomputable def shearMatrix {d : ℕ} (a : Fin d → ℝ) (j : Fin d) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + Matrix.replicateCol (Fin 1) (Pi.single j (1 : ℝ))
      * Matrix.replicateRow (Fin 1) (fun i => if i = j then 0 else a i / a j)

/-- The shear has determinant 1 (Sherman–Morrison: the rank-one update is
orthogonal to the diagonal entry it modifies). -/
theorem det_shearMatrix {d : ℕ} (a : Fin d → ℝ) (j : Fin d) :
    (shearMatrix a j).det = 1 := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (Pi.single j (1 : ℝ)) (fun i => if i = j then 0 else a i / a j)
  have hv : (fun i => if i = j then 0 else a i / a j) ⬝ᵥ Pi.single j (1 : ℝ)
      = 0 := by simp [dotProduct, Pi.single_apply]
  rw [hv] at h
  rw [shearMatrix]
  exact h.trans (by norm_num)

/-- Coordinates of the shear: it fixes all coordinates except `j`, which becomes
`u(x)/a_j`. -/
theorem shear_apply {d : ℕ} (a : Fin d → ℝ) (j : Fin d) (ha : a j ≠ 0)
    (x : Fin d → ℝ) :
    ∀ k, Matrix.toLin' (shearMatrix a j) x k
      = if k = j then (∑ i, a i * x i) / a j else x k := by
  intro k
  rw [Matrix.toLin'_apply]
  simp only [shearMatrix, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [Pi.add_apply]
  have hcol : Matrix.mulVec (Matrix.replicateCol (Fin 1) (Pi.single j (1 : ℝ))
      * Matrix.replicateRow (Fin 1) (fun i => if i = j then 0 else a i / a j)) x
      = fun k => (Pi.single j (1 : ℝ) : Fin d → ℝ) k
          * ∑ i, (if i = j then 0 else a i / a j) * x i := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      one_smul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hcol]
  by_cases hk : k = j
  · rw [if_pos hk, hk, Pi.single_eq_same, one_mul]
    have hsplit : ∑ i, (if i = j then 0 else a i / a j) * x i
        = (∑ i, a i * x i) / a j - x j := by
      rw [eq_sub_iff_add_eq]
      rw [show (∑ i, a i * x i) / a j = ∑ i, (a i / a j) * x i from by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring]
      calc (∑ i, (if i = j then 0 else a i / a j) * x i) + x j
          = (∑ i ∈ Finset.univ.erase j, (if i = j then 0 else a i / a j) * x i)
              + (if j = j then (0 : ℝ) else a j / a j) * x j + x j := by
            rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
        _ = (∑ i ∈ Finset.univ.erase j, (a i / a j) * x i) + (a j / a j) * x j := by
            rw [if_pos rfl, zero_mul, add_zero, div_self ha, one_mul]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [if_neg (Finset.mem_erase.mp hi).1]
        _ = ∑ i, (a i / a j) * x i := Finset.sum_erase_add _ _ (Finset.mem_univ j)
    rw [hsplit]
    ring
  · rw [if_neg hk, Pi.single_eq_of_ne hk, zero_mul, add_zero]

end Nondividing
