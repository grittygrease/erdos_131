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

/-- A full-rank GAP's step lattice has nonzero (finite) index: the real step
map is injective (`realEval_injective`), hence surjective, hence has nonzero
determinant — and `|det| = index`. -/
theorem stepLattice_index_ne_zero {d : ℕ} (P : GAP d d) (hrank : P.realRank = d)
    (hinj : Function.Injective P.evalHom) :
    (LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index ≠ 0 := by
  intro h0
  have habs := abs_det_stepMapR P hinj
  rw [h0] at habs
  push_cast at habs
  have hdet0 : LinearMap.det (stepMapR P) = 0 := abs_eq_zero.mp habs
  -- But the step map is injective, hence surjective, hence range = ⊤.
  have hmapinj : Function.Injective (stepMapR P) := by
    have hfun : ∀ x : Fin d → ℝ, stepMapR P x
        = (Fintype.linearCombination ℝ
            (fun i : Fin d => (fun j : Fin d => (P.step i j : ℝ)))) x := by
      intro x
      funext j
      rw [stepMapR_apply]
      simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    intro x y hxy
    apply realEval_injective P hrank
    rw [← hfun x, ← hfun y, hxy]
  have hsurj : Function.Surjective (stepMapR P) :=
    LinearMap.surjective_of_injective hmapinj
  have hrange : LinearMap.range (stepMapR P) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have := LinearMap.range_lt_top_of_det_eq_zero hdet0
  rw [hrange] at this
  exact absurd this (lt_irrefl ⊤)

/-- The finite quotient instance for the step lattice of a full-rank GAP. -/
theorem stepLattice_finite_quotient {d : ℕ} (P : GAP d d) (hrank : P.realRank = d)
    (hinj : Function.Injective P.evalHom) :
    Finite ((Fin d → ℤ) ⧸
      (LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup) :=
  AddSubgroup.index_ne_zero_iff_finite.mp (stepLattice_index_ne_zero P hrank hinj)

/-- **Index bound, part 2** (`lem:index-bound`): under the `gap_contained`
hypotheses, a proper full-rank GAP with `|P| ≥ γ|B|` has step-lattice index
`[ℤ^d:L] ≤ (12/c)^d·γ⁻¹`.  Chain: `|P| ≤ 3^d∏Nᵢ`, so
`index·|P| ≤ (3/2)^d·(index·2^d∏Nᵢ) ≤ (3/2)^d(8/c)^d∏Mⱼ ≤ (12/c)^d|B|`,
then divide by `|P| ≥ γ|B| > 0`. -/
theorem index_bound_part2 {d : ℕ} (P : GAP d d) (hP : P.Proper)
    (hinj : Function.Injective P.evalHom) {c s : ℝ} (hc : 0 < c) (hc8 : c ≤ 8)
    (hs : 0 < s) (hcs2 : 2 ≤ c * s) {M : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)}
    (hC₀ : C₀ ⊆ coordinateBox M) (hk0 : (C₀.card : ℝ) ≤ s) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier (c * s), q + z ∈ subsetSums C₀)
    {γ : ℝ} (hγ : 0 < γ)
    (hlarge : γ * ((coordinateBox M).card : ℝ) ≤ P.carrier.card)
    (hBpos : 0 < ((coordinateBox M).card : ℝ)) :
    ((LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ)
      ≤ (12 / c) ^ d * γ⁻¹ := by
  set idx : ℝ :=
    ((LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index : ℝ) with hidx
  have hidx0 : 0 ≤ idx := Nat.cast_nonneg _
  -- Cardinality of the box `|B| = ∏(2Mⱼ+1) ≥ ∏Mⱼ`.
  have hMB : (∏ j, (M j : ℝ)) ≤ ((coordinateBox M).card : ℝ) := by
    rw [card_coordinateBox]
    push_cast
    exact Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _)
      (fun j _ => by push_cast; linarith [Nat.cast_nonneg (α := ℝ) (M j)])
  -- `|P| ≤ 3^d·∏Nᵢ`.
  have hPcard : (P.carrier.card : ℝ) ≤ 3 ^ d * ∏ i, (P.radius i : ℝ) := by
    have := P.card_le_three_pow_mul_prod_radius hP
    calc (P.carrier.card : ℝ) ≤ ((3 ^ d * ∏ i, P.radius i : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = 3 ^ d * ∏ i, (P.radius i : ℝ) := by push_cast; ring
  -- The volume comparison.
  have hvol := index_mul_le_volume_bound P hinj hc hs hcs2 hC₀ hk0 hincl
  -- Assemble: `idx·|P| ≤ (12/c)^d·|B|`.
  have hprod0 : (0 : ℝ) ≤ ∏ i, (P.radius i : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  have hmain : idx * (P.carrier.card : ℝ)
      ≤ (12 / c) ^ d * ((coordinateBox M).card : ℝ) := by
    calc idx * (P.carrier.card : ℝ)
        ≤ idx * (3 ^ d * ∏ i, (P.radius i : ℝ)) :=
          mul_le_mul_of_nonneg_left hPcard hidx0
      _ = (3 / 2 : ℝ) ^ d * (idx * (2 ^ d * ∏ i, (P.radius i : ℝ))) := by
          rw [show ((3 : ℝ) / 2) ^ d * (idx * (2 ^ d * ∏ i, (P.radius i : ℝ)))
              = idx * (((3 / 2 : ℝ) ^ d * 2 ^ d) * ∏ i, (P.radius i : ℝ)) by ring,
            ← mul_pow]
          norm_num
      _ ≤ (3 / 2 : ℝ) ^ d * ((8 / c) ^ d * ∏ j, (M j : ℝ)) :=
          mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = (12 / c) ^ d * ∏ j, (M j : ℝ) := by
          rw [show ((3 : ℝ) / 2) ^ d * ((8 / c) ^ d * ∏ j, (M j : ℝ))
              = ((3 / 2 : ℝ) * (8 / c)) ^ d * ∏ j, (M j : ℝ) by rw [mul_pow]; ring]
          congr 2
          ring
      _ ≤ (12 / c) ^ d * ((coordinateBox M).card : ℝ) :=
          mul_le_mul_of_nonneg_left hMB (by positivity)
  -- Divide by `|P| ≥ γ|B| > 0`.
  have hPpos : (0 : ℝ) < P.carrier.card := lt_of_lt_of_le (by positivity) hlarge
  have hstep : idx * (γ * ((coordinateBox M).card : ℝ))
      ≤ (12 / c) ^ d * ((coordinateBox M).card : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hlarge hidx0) hmain
  have h1 : idx * γ ≤ (12 / c) ^ d := by
    have hassoc : (idx * γ) * ((coordinateBox M).card : ℝ)
        ≤ (12 / c) ^ d * ((coordinateBox M).card : ℝ) := by
      rw [mul_assoc]; exact hstep
    exact le_of_mul_le_mul_right hassoc hBpos
  rw [show (12 / c : ℝ) ^ d * γ⁻¹ = ((12 / c) ^ d) / γ from
      (div_eq_mul_inv _ _).symm,
    le_div_iff₀ hγ]
  exact h1
