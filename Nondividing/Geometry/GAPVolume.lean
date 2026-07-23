import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Hull
import Nondividing.Geometry.IndexDet
import Nondividing.Preprocessing

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

/-- Coordinates of the step map: `(Mx)ⱼ = ∑ᵢ xᵢ·(qᵢ)ⱼ`. -/
theorem stepMapR_apply {d : ℕ} (P : GAP d d) (x : Fin d → ℝ) (j : Fin d) :
    stepMapR P x j = ∑ i, x i * (P.step i j : ℝ) := by
  rw [stepMapR, Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, stepMatrixR, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Real parallelepiped containment**: under the `gap_contained` hypotheses,
every real point of `M(realBox)` obeys the same coordinate bound
`c·|(Mx)ⱼ| ≤ 4Mⱼ` as the integer carrier.  Key trick: the extreme coefficient
vector `nᵢ = sign((qᵢ)ⱼ)·Nᵢ` is an *integer* point of the coefficient box, its
image dominates `|(Mx)ⱼ|` coordinatewise, and `gap_contained` bounds it. -/
theorem stepMapR_realBox_bound {d : ℕ} (P : GAP d d) {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hcs2 : 2 ≤ c * s) {M : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)}
    (hC₀ : C₀ ⊆ coordinateBox M) (hk0 : (C₀.card : ℝ) ≤ s) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier (c * s), q + z ∈ subsetSums C₀) :
    ∀ x ∈ realBox P.radius, ∀ j, c * |stepMapR P x j| ≤ 4 * (M j : ℝ) := by
  intro x hx j
  -- The extreme integer coefficient vector for coordinate `j`.
  set n : Fin d → ℤ := fun i => if 0 ≤ P.step i j then (P.radius i : ℤ)
    else -(P.radius i : ℤ) with hn
  have hnbox : n ∈ P.coeffBox := by
    rw [GAP.coeffBox, mem_coordinateBox]
    intro i
    by_cases hsign : 0 ≤ P.step i j <;> simp [hn, hsign]
  have hncarrier : P.evalHom n ∈ P.carrier :=
    (GAP.mem_carrier P).mpr ⟨n, hnbox, rfl⟩
  -- Its `j`-th coordinate is `∑ᵢ Nᵢ|qᵢⱼ| ≥ 0`, dominating `|(Mx)ⱼ|`.
  have hnval : ((P.evalHom n j : ℤ) : ℝ) = ∑ i, (P.radius i : ℝ) * |(P.step i j : ℝ)| := by
    rw [GAP.evalHom_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hsign : 0 ≤ P.step i j
    · rw [hn]; simp only [hsign, if_true]
      rw [abs_of_nonneg (by exact_mod_cast hsign)]
      push_cast; ring
    · rw [hn]; simp only [hsign, if_false]
      push_neg at hsign
      rw [abs_of_neg (by exact_mod_cast hsign)]
      push_cast; ring
  have hxbound : ∀ i, |x i| ≤ (P.radius i : ℝ) := by
    intro i
    obtain ⟨h1, h2⟩ := hx
    exact abs_le.mpr ⟨h1 i, h2 i⟩
  have hdom : |stepMapR P x j| ≤ ((P.evalHom n j : ℤ) : ℝ) := by
    rw [stepMapR_apply, hnval]
    calc |∑ i, x i * (P.step i j : ℝ)|
        ≤ ∑ i, |x i * (P.step i j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |x i| * |(P.step i j : ℝ)| := by
          refine Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i, (P.radius i : ℝ) * |(P.step i j : ℝ)| :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hxbound i) (abs_nonneg _)
  -- `gap_contained` bounds the integer carrier point.
  have hgap := gap_contained P hc hs hcs2 hC₀ hk0 hincl (P.evalHom n) hncarrier j
  have hnonneg : (0 : ℝ) ≤ ((P.evalHom n j : ℤ) : ℝ) := by
    rw [hnval]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  calc c * |stepMapR P x j| ≤ c * ((P.evalHom n j : ℤ) : ℝ) :=
        mul_le_mul_of_nonneg_left hdom (le_of_lt hc)
    _ = c * |((P.evalHom n j : ℤ) : ℝ)| := by rw [abs_of_nonneg hnonneg]
    _ ≤ 4 * (M j : ℝ) := hgap

/-- **Volume comparison**: under the `gap_contained` hypotheses, the
parallelepiped volume identity plus containment in the `(4/c)`-dilated box gives
`[ℤ^d:L]·2^d·∏Nᵢ ≤ (8/c)^d·∏Mⱼ`. -/
theorem index_mul_le_volume_bound {d : ℕ} (P : GAP d d)
    (hinj : Function.Injective P.evalHom) {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hcs2 : 2 ≤ c * s) {M : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)}
    (hC₀ : C₀ ⊆ coordinateBox M) (hk0 : (C₀.card : ℝ) ≤ s) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier (c * s), q + z ∈ subsetSums C₀) :
    ((LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ)
        * (2 ^ d * ∏ i, (P.radius i : ℝ))
      ≤ (8 / c) ^ d * ∏ j, (M j : ℝ) := by
  -- The image is inside the real box with radii `(4/c)·Mⱼ`.
  have himg : stepMapR P '' realBox P.radius ⊆
      Set.Icc (fun j => -((4 / c) * (M j : ℝ))) (fun j => (4 / c) * (M j : ℝ)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hb := stepMapR_realBox_bound P hc hs hcs2 hC₀ hk0 hincl x hx
    constructor <;> intro j <;>
      [ have := (abs_le.mp ((le_div_iff₀' hc).mpr (hb j))).1;
        have := (abs_le.mp ((le_div_iff₀' hc).mpr (hb j))).2 ] <;>
      · rw [show (4 : ℝ) * (M j : ℝ) / c = (4 / c) * (M j : ℝ) by ring] at this
        simpa using this
  -- Compare volumes.
  have hvol := measure_mono (μ := (volume : MeasureTheory.Measure (Fin d → ℝ))) himg
  rw [volume_stepMapR_realBox P hinj] at hvol
  have hIccVol : volume (Set.Icc (fun j => -((4 / c) * (M j : ℝ)))
      (fun j => (4 / c) * (M j : ℝ)))
      = ENNReal.ofReal ((8 / c) ^ d * ∏ j, (M j : ℝ)) := by
    rw [Real.volume_Icc_pi]
    rw [show (∏ j : Fin d, ENNReal.ofReal ((4 / c) * (M j : ℝ) - -((4 / c) * (M j : ℝ))))
          = ∏ j : Fin d, ENNReal.ofReal ((8 / c) * (M j : ℝ)) from by
        refine Finset.prod_congr rfl fun j _ => ?_
        congr 1; ring]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity)]
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hIccVol] at hvol
  have hrhs : (0 : ℝ) ≤ (8 / c) ^ d * ∏ j, (M j : ℝ) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp hvol

end Nondividing
