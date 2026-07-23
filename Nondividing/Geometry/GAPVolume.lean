import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Hull
import Nondividing.Geometry.IndexDet

open scoped BigOperators
open MeasureTheory

namespace Nondividing

/-!
# GAP volume argument (Phase F, `lem:index-bound` part 2)

The parallelepiped `M(box)` of a full-rank GAP has Lebesgue volume
`|det M|·2^d·∏Nᵢ = [ℤ^d:L]·2^d·∏Nᵢ`, and it is contained in a fixed dilate of
`B_ℝ`.  Combined with `|P| ≍ 2^d∏Nᵢ` and `|P| ≥ γ|B|` this gives
`[ℤ^d:L] ≪ γ⁻¹`.
-/

/-- The real symmetric coordinate box `∏ᵢ[-Nᵢ, Nᵢ] ⊆ ℝ^d`. -/
def realBox {d : ℕ} (N : Fin d → ℕ) : Set (Fin d → ℝ) :=
  Set.Icc (fun i => -(N i : ℝ)) (fun i => (N i : ℝ))

/-- Volume of the real box: `vol(∏[-Nᵢ,Nᵢ]) = 2^d·∏Nᵢ`. -/
theorem volume_realBox {d : ℕ} (N : Fin d → ℕ) :
    volume (realBox N) = ENNReal.ofReal (2 ^ d * ∏ i, (N i : ℝ)) := by
  rw [realBox, Real.volume_Icc_pi]
  rw [show (∏ i : Fin d, ENNReal.ofReal ((N i : ℝ) - -(N i : ℝ)))
        = ∏ i : Fin d, ENNReal.ofReal (2 * (N i : ℝ)) from by
        refine Finset.prod_congr rfl fun i _ => ?_; ring_nf]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

open Module in
/-- `Pi.basisFun`'s change-of-basis matrix is the matrix whose `j`-th column is
`v j`. -/
theorem basisFun_toMatrix {d : ℕ} {R : Type*} [CommRing R] (v : Fin d → (Fin d → R)) :
    (Pi.basisFun R (Fin d)).toMatrix v = Matrix.of (fun i j => v j i) := by
  ext i j
  rw [Basis.toMatrix_apply, Pi.basisFun_repr]
  rfl

/-- The real step matrix (columns `= q₁,…,q_d`). -/
noncomputable def stepMatrixR {d : ℕ} (P : GAP d d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun i j => (P.step j i : ℝ))

/-- The real coefficient map `M : ℝ^d → ℝ^d`, `M(eₖ) = q_k`. -/
noncomputable def stepMapR {d : ℕ} (P : GAP d d) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.toLin' (stepMatrixR P)

open Module in
/-- The absolute real determinant of the coefficient map equals the lattice
index: `|det M| = [ℤ^d:L]`. -/
theorem abs_det_stepMapR {d : ℕ} (P : GAP d d) (hinj : Function.Injective P.evalHom) :
    |LinearMap.det (stepMapR P)|
      = ((LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ) := by
  have hM : stepMatrixR P
      = (Int.castRingHom ℝ).mapMatrix ((Pi.basisFun ℤ (Fin d)).toMatrix (fun i => P.step i)) := by
    ext i j
    simp only [stepMatrixR, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Basis.toMatrix_apply, Pi.basisFun_repr, Int.coe_castRingHom]
  have hdet : LinearMap.det (stepMapR P)
      = (((Pi.basisFun ℤ (Fin d)).det (fun i => P.step i) : ℤ) : ℝ) := by
    show LinearMap.det (Matrix.toLin' (stepMatrixR P))
      = (((Pi.basisFun ℤ (Fin d)).det (fun i => P.step i) : ℤ) : ℝ)
    rw [LinearMap.det_toLin', hM,
      ← RingHom.map_det (Int.castRingHom ℝ)
        ((Pi.basisFun ℤ (Fin d)).toMatrix (fun i => P.step i)),
      Basis.det_apply, Int.coe_castRingHom]
  have hidx : (LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index
      = ((Pi.basisFun ℤ (Fin d)).det (fun i => P.step i)).natAbs :=
    index_range_eq_natAbs_det P hinj
  rw [hdet, hidx]
  simp only [Nat.cast_natAbs]
  exact Int.cast_abs.symm

/-- **Parallelepiped volume**: the image of the coefficient box under the step
map has volume `[ℤ^d:L]·2^d·∏Nᵢ` (`eq:index-volume` of `lem:index-bound`). -/
theorem volume_stepMapR_realBox {d : ℕ} (P : GAP d d)
    (hinj : Function.Injective P.evalHom) :
    volume (stepMapR P '' realBox P.radius)
      = ENNReal.ofReal
          (((LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ)
            * (2 ^ d * ∏ i, (P.radius i : ℝ))) := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap, volume_realBox,
    abs_det_stepMapR P hinj]
  rw [← ENNReal.ofReal_mul (by positivity)]

end Nondividing
