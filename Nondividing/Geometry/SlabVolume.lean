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

end Nondividing
