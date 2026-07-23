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

/-- **Slab volume bound** (`lem:slab-count`, Fubini step, via the shear).
If `|a_j|·N_j ≥ w/d` (the pigeonhole coordinate) then the slab
`{x ∈ B_ℝ : |⟨a,x⟩| ≤ τw}` has volume at most `2dτ·N_j·∏_{i≠j}(2N_i)
= dτ·2^d·∏N_i = dτ·vol(B_ℝ)`. -/
theorem volume_slab_inter_box_le {d : ℕ} (N : Fin d → ℕ) (a : Fin d → ℝ)
    (j : Fin d) (ha : a j ≠ 0) {τ w : ℝ} (hτ : 0 ≤ τ) (hw : 0 ≤ w)
    (hjw : w ≤ d * (|a j| * (N j : ℝ))) :
    volume {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w}
      ≤ ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := by
  classical
  set T := Matrix.toLin' (shearMatrix a j) with hT
  set R : Fin d → ℝ := fun k => if k = j then d * τ * (N j : ℝ) else (N k : ℝ)
    with hR
  have hRj : R j = d * τ * (N j : ℝ) := by rw [hR]; simp
  have hRne : ∀ k, k ≠ j → R k = (N k : ℝ) := by
    intro k hk; rw [hR]; simp [hk]
  have hja : (0 : ℝ) < |a j| := abs_pos.mpr ha
  -- Key coordinate bound for the sheared point.
  have hkey : ∀ x : Fin d → ℝ, |∑ i, a i * x i| ≤ τ * w →
      |(∑ i, a i * x i) / a j| ≤ d * τ * (N j : ℝ) := by
    intro x hxslab
    have h1 : |(∑ i, a i * x i) / a j| ≤ τ * w / |a j| := by
      rw [abs_div]
      exact div_le_div_of_nonneg_right hxslab hja.le
    have h2 : τ * w / |a j| ≤ d * τ * (N j : ℝ) := by
      rw [div_le_iff₀ hja]
      calc τ * w ≤ τ * (d * (|a j| * (N j : ℝ))) :=
            mul_le_mul_of_nonneg_left hjw hτ
        _ = d * τ * (N j : ℝ) * |a j| := by ring
    exact h1.trans h2
  -- The shear sends the slab into the thin product box.
  have himg : T '' {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w}
      ⊆ Set.Icc (fun k => -(R k)) R := by
    rintro _ ⟨x, ⟨hxbox, hxslab⟩, rfl⟩
    have happly := shear_apply a j ha x
    have hbnd := abs_le.mp (hkey x hxslab)
    constructor <;> intro k <;> beta_reduce <;> rw [happly k] <;> by_cases hk : k = j
    · rw [if_pos hk, hk, hRj]; exact hbnd.1
    · rw [if_neg hk, hRne k hk]; exact hxbox.1 k
    · rw [if_pos hk, hk, hRj]; exact hbnd.2
    · rw [if_neg hk, hRne k hk]; exact hxbox.2 k
  -- The shear preserves volume (det = 1).
  have hdet : LinearMap.det T = 1 := by
    rw [hT, LinearMap.det_toLin', det_shearMatrix]
  have hvolT : volume (T '' {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w})
      = volume {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w} := by
    rw [MeasureTheory.Measure.addHaar_image_linearMap, hdet]
    norm_num
  -- Volume of the thin box.
  have hbox : volume (Set.Icc (fun k => -(R k)) R)
      = ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := by
    rw [Real.volume_Icc_pi]
    have hterm : ∀ k ∈ Finset.univ, ENNReal.ofReal (R k - -(R k))
        = ENNReal.ofReal (2 * R k) := by
      intro k _; congr 1; ring
    rw [Finset.prod_congr rfl hterm]
    have hRnneg : ∀ k, (0 : ℝ) ≤ R k := by
      intro k
      by_cases hk : k = j
      · rw [hk, hRj]; positivity
      · rw [hRne k hk]; positivity
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => by
      have := hRnneg k; linarith)]
    congr 1
    rw [show (∏ k, (2 * R k)) = 2 ^ d * ∏ k, R k from by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    have hprodR : (∏ k, R k)
        = (d * τ * (N j : ℝ)) * ∏ k ∈ Finset.univ.erase j, (N k : ℝ) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), hRj, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun k hk => hRne k (Finset.mem_erase.mp hk).1
    have hprodN : (∏ i, (N i : ℝ))
        = (N j : ℝ) * ∏ k ∈ Finset.univ.erase j, (N k : ℝ) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_comm]
    rw [hprodR, hprodN]
    ring
  calc volume {x : Fin d → ℝ | x ∈ realBox N ∧ |∑ i, a i * x i| ≤ τ * w}
      = volume (T '' _) := hvolT.symm
    _ ≤ volume (Set.Icc (fun k => -(R k)) R) := measure_mono himg
    _ = ENNReal.ofReal ((d * τ) * (2 ^ d * ∏ i, (N i : ℝ))) := hbox

end Nondividing
