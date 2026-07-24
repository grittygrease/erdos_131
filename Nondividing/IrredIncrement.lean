import Nondividing.ProjectiveTheorem
import Nondividing.ProjectiveConvexity
import Nondividing.WeightedDensityLimit
import Nondividing.CapLifting
import Nondividing.CapConeVolume
import Nondividing.Projective.AffineSpan
import Nondividing.Projective.Convexity
import Nondividing.Geometry.SlabVolume

open scoped BigOperators Pointwise
open MeasureTheory

namespace Nondividing

open Nondividing.External

/-!
# The irreducible-stage density increment (`IrreducibleIncrement`)

This file discharges the geometric pipeline of the irreducible-stage step
(Manuscript.tex 1941–2024): at an unshiftedly `(δ,γ)`-irreducible stage, the
projective machinery (`weighted_density` in the hyperplane chart
`H_λ ≅ ℝ^{d-1}`, cap lifting through the cone volume count, and slab exclusion
to force full rank) produces a same-dimensional stage with box decay `≤ C·η·|B|`
and retention `≥ η^{κ_{d-1}+ε}·n`.

## Structure

1. **Chart volume machinery** (the `H_λ ≅ ℝ^{d-1}` identification): the
   flat-cone Fubini formula `vol(cone 1 (insertNth j 1 '' F)) = c_r · vol F`
   and its transfer to arbitrary hyperplanes `{λℝ = 1}` through a
   determinant-`ℓⱼ` linear map (diagonal · shear).
2. **The affine chart** `chartProj j` / `chartSec ℓ j` of `H_λ`, the stage
   body `Ω = {y ∈ H_λ : X·y ∈ B_ℝ}` and its chart image, and the transfer of
   `IndexedMuConvexPosition` through the chart.
3. **Span dichotomy**: at an irreducible stage a `δ`-large subset spans `ℝ^d`
   (else it lies in a width-`0` slab, contradicting `slab_exclusion`).
4. **Full-rank cap lifting** (`cap_lifting_full`): the `r = d` alternative of
   `lem:cap-lifting`, with box bound `|B'| ≤ C·η·|B|`, via `discrete_john`
   (E2) on the lattice points of the difference cone body and the
   Rogers–Shephard / lattice-count volume chain (E5c, E5d).
5. **The increment step** (`irreducible_cap_step`) and the assemblies
   `irreducibleIncrement_of_data` / `irreducibleIncrement_of_convexPosition`
   producing the `IrreducibleIncrement` predicate.
-/

/-! ## 1. Cone volumes in a hyperplane chart

The perspective-volume formula (eq:perspective-volume) in ratio-friendly form:
for `E` in the affine hyperplane `{λℝ = 1}`, the cone volume `vol(cone 1 E)`
is a fixed positive multiple (depending only on `λ` and the deleted
coordinate) of the `(d-1)`-dimensional volume of the graph-chart image of
`E`.  We never need the exact constant. -/

/-- Linear images of truncated cones are truncated cones of the image. -/
theorem image_cone {d d' : ℕ} (G : (Fin d → ℝ) →ₗ[ℝ] (Fin d' → ℝ)) (T : ℝ)
    (E : Set (Fin d → ℝ)) : G '' cone T E = cone T (G '' E) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, t, ht0, htT, rfl⟩, rfl⟩
    exact ⟨G y, ⟨y, hy, rfl⟩, t, ht0, htT, map_smul G t y⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, t, ht0, htT, rfl⟩
    exact ⟨t • y, ⟨y, hy, t, ht0, htT, rfl⟩, map_smul G t y⟩

/-- The universal cone constant `c_r = ∫₀¹ t^r dt` (kept abstract). -/
noncomputable def coneConst (r : ℕ) : ENNReal :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t ^ r)

theorem coneConst_le_one (r : ℕ) : coneConst r ≤ 1 := by
  have hmono : coneConst r ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, (1 : ENNReal) := by
    refine setLIntegral_mono measurable_const ?_
    intro t ht
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_one₀ ht.1 ht.2)
  calc coneConst r ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, (1 : ENNReal) := hmono
    _ = volume (Set.Icc (0 : ℝ) 1) := setLIntegral_one _
    _ = 1 := by rw [Real.volume_Icc]; norm_num

theorem coneConst_ne_top (r : ℕ) : coneConst r ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (coneConst_le_one r)

theorem coneConst_pos (r : ℕ) : 0 < coneConst r := by
  have hsub : Set.Icc (1 / 2 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.Icc_subset_Icc (by norm_num) le_rfl
  have hlow : ENNReal.ofReal ((1 / 2) ^ r) * volume (Set.Icc (1 / 2 : ℝ) 1) ≤
      coneConst r := by
    rw [← setLIntegral_const]
    calc ∫⁻ _ in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal ((1 / 2) ^ r)
        ≤ ∫⁻ t in Set.Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (t ^ r) := by
          refine setLIntegral_mono
            (by fun_prop) ?_
          intro t ht
          exact ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ (by norm_num) ht.1 r)
      _ ≤ coneConst r :=
          lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
  have hpos : (0 : ENNReal) <
      ENNReal.ofReal ((1 / 2) ^ r) * volume (Set.Icc (1 / 2 : ℝ) 1) := by
    rw [Real.volume_Icc]
    apply ENNReal.mul_pos
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      norm_num
  exact lt_of_lt_of_le hpos hlow

/-- **Flat-cone Fubini**: the volume of the truncated cone over a compact set
`F` placed at height `1` in coordinate `j` equals `c_r · vol F`. -/
theorem volume_cone_insertNth {r : ℕ} (j : Fin (r + 1)) {F : Set (Fin r → ℝ)}
    (hFc : IsCompact F) :
    volume (cone 1 (Fin.insertNth j (1 : ℝ) '' F)) = coneConst r * volume F := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) j with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => ℝ) j
  set C : Set (Fin (r + 1) → ℝ) := cone 1 (Fin.insertNth j (1 : ℝ) '' F)
    with hC
  set Chat : Set (ℝ × (Fin r → ℝ)) :=
    (fun p : ℝ × (Fin r → ℝ) => (p.1, p.1 • p.2)) '' (Set.Icc (0 : ℝ) 1 ×ˢ F)
    with hChat
  -- The key pointwise computation.
  have hesmul : ∀ (t : ℝ) (y : Fin r → ℝ),
      e (t • Fin.insertNth j (1 : ℝ) y) = (t, t • y) := by
    intro t y
    have h1 : (t • Fin.insertNth j (1 : ℝ) y) j = t := by
      rw [Pi.smul_apply, Fin.insertNth_apply_same, smul_eq_mul, mul_one]
    have h2 : j.removeNth (t • Fin.insertNth j (1 : ℝ) y) = t • y := by
      funext k
      rw [Fin.removeNth_apply, Pi.smul_apply, Fin.insertNth_apply_succAbove,
        Pi.smul_apply]
    show ((t • Fin.insertNth j (1 : ℝ) y) j,
      j.removeNth (t • Fin.insertNth j (1 : ℝ) y)) = (t, t • y)
    rw [h1, h2]
  -- `e` maps the cone onto the parameterized region.
  have himg : e '' C = Chat := by
    ext p
    constructor
    · rintro ⟨x, ⟨_, ⟨y, hy, rfl⟩, t, ht0, htT, rfl⟩, rfl⟩
      exact ⟨(t, y), ⟨Set.mem_Icc.mpr ⟨ht0, htT⟩, hy⟩, (hesmul t y).symm⟩
    · rintro ⟨⟨t, y⟩, ⟨htI, hy⟩, rfl⟩
      refine ⟨t • Fin.insertNth j (1 : ℝ) y, ?_, hesmul t y⟩
      exact ⟨Fin.insertNth j (1 : ℝ) y, ⟨y, hy, rfl⟩, t,
        (Set.mem_Icc.mp htI).1, (Set.mem_Icc.mp htI).2, rfl⟩
  -- `Chat` is compact, hence measurable.
  have hChatc : IsCompact Chat := by
    rw [hChat]
    exact (isCompact_Icc.prod hFc).image
      (continuous_fst.prodMk (continuous_fst.smul continuous_snd))
  have hChatm : MeasurableSet Chat := hChatc.isClosed.measurableSet
  -- Transfer the volume through `e`.
  have hCpre : C = e ⁻¹' Chat := by
    rw [← himg, Set.preimage_image_eq _ e.injective]
  have hvolC : volume C = volume Chat := by
    rw [hCpre]
    exact hmp.measure_preimage hChatm.nullMeasurableSet
  -- Fubini for the product region.
  have hsection : ∀ t : ℝ, Prod.mk t ⁻¹' Chat =
      if t ∈ Set.Icc (0 : ℝ) 1 then t • F else ∅ := by
    intro t
    ext z
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · rw [if_pos ht]
      constructor
      · rintro ⟨⟨a, y⟩, ⟨haI, hy⟩, heq⟩
        obtain ⟨h1, h2⟩ := Prod.mk_inj.mp heq
        subst h1
        exact h2 ▸ Set.smul_mem_smul_set hy
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(t, y), ⟨ht, hy⟩, rfl⟩
    · rw [if_neg ht]
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨a, y⟩, ⟨haI, hy⟩, heq⟩
      obtain ⟨h1, _⟩ := Prod.mk_inj.mp heq
      exact ht (h1 ▸ haI)
  have hprod : volume Chat = ∫⁻ t, volume (Prod.mk t ⁻¹' Chat) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hChatm]
  have hindic : (fun t => volume (Prod.mk t ⁻¹' Chat)) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun t => volume (t • F)) := by
    funext t
    rw [hsection t]
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · rw [if_pos ht, Set.indicator_of_mem ht]
    · rw [if_neg ht, Set.indicator_of_notMem ht, measure_empty]
  have hFvol : volume F ≠ ⊤ := hFc.measure_lt_top.ne
  calc volume C = volume Chat := hvolC
    _ = ∫⁻ t, volume (Prod.mk t ⁻¹' Chat) := hprod
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, volume (t • F) := by
        rw [hindic, lintegral_indicator measurableSet_Icc]
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t ^ r) * volume F := by
        refine setLIntegral_congr_fun measurableSet_Icc ?_
        intro t ht
        show volume (t • F) = ENNReal.ofReal (t ^ r) * volume F
        rw [Measure.addHaar_smul_of_nonneg volume ht.1 F,
          Module.finrank_fin_fun]
    _ = coneConst r * volume F :=
        lintegral_mul_const' (volume F) _ hFvol

/-! ### The hyperplane-to-flat linear map

`hypMatrix ℓ j` fixes all coordinates except `j`, which becomes the value of
the functional `λℝ`; its determinant is `ℓ j`.  It carries `{λℝ = 1}` onto the
flat hyperplane `{x j = 1}` while acting as the identity on the chart
coordinates. -/

/-- Diagonal (coordinate `j` scaled by `ℓ j`) times the determinant-1 shear:
the map `x ↦ x[j := λℝ(x)]`. -/
noncomputable def hypMatrix {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1)) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.diagonal (fun k => if k = j then (ℓ j : ℝ) else 1) *
    shearMatrix (fun i => (ℓ i : ℝ)) j

theorem det_hypMatrix {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1)) :
    (hypMatrix ℓ j).det = (ℓ j : ℝ) := by
  rw [hypMatrix, Matrix.det_mul, det_shearMatrix, mul_one,
    Matrix.det_diagonal]
  rw [Finset.prod_eq_single j (fun k _ hk => if_neg hk)
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [if_pos rfl]

theorem hypMatrix_apply {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (hj : (ℓ j : ℝ) ≠ 0) (x : Fin (r + 1) → ℝ) (k : Fin (r + 1)) :
    Matrix.toLin' (hypMatrix ℓ j) x k =
      if k = j then ∑ i, (ℓ i : ℝ) * x i else x k := by
  rw [hypMatrix, Matrix.toLin'_mul, LinearMap.comp_apply]
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [shear_apply (fun i => (ℓ i : ℝ)) j hj x k]
  by_cases hk : k = j
  · rw [if_pos hk, if_pos hk, if_pos hk, mul_comm, div_mul_cancel₀ _ hj]
  · rw [if_neg hk, if_neg hk, if_neg hk, one_mul]

/-- On the hyperplane `{λℝ = 1}` the map `hypMatrix` agrees with placing the
chart image at height 1 in coordinate `j`. -/
theorem hypMatrix_eq_insertNth {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (hj : (ℓ j : ℝ) ≠ 0) {x : Fin (r + 1) → ℝ}
    (hx : realFunctional ℓ x = 1) :
    Matrix.toLin' (hypMatrix ℓ j) x =
      Fin.insertNth j (1 : ℝ) (fun k => x (j.succAbove k)) := by
  set S := Matrix.toLin' (hypMatrix ℓ j) with hS
  have h1 : S x j = 1 := by
    rw [hS, hypMatrix_apply ℓ j hj, if_pos rfl]
    rw [realFunctional_apply] at hx
    exact hx
  have h2 : j.removeNth (S x) = fun k => x (j.succAbove k) := by
    funext k
    rw [Fin.removeNth_apply, hS, hypMatrix_apply ℓ j hj,
      if_neg (Fin.succAbove_ne j k)]
  calc S x = Fin.insertNth j (S x j) (j.removeNth (S x)) :=
        (Fin.insertNth_self_removeNth j (S x)).symm
    _ = Fin.insertNth j (1 : ℝ) (fun k => x (j.succAbove k)) := by
        rw [h1, h2]

/-- The chart projection deleting coordinate `j` (as a plain function). -/
def chartProj {r : ℕ} (j : Fin (r + 1)) (x : Fin (r + 1) → ℝ) : Fin r → ℝ :=
  fun k => x (j.succAbove k)

theorem continuous_chartProj {r : ℕ} (j : Fin (r + 1)) :
    Continuous (chartProj j) :=
  continuous_pi fun k => continuous_apply (j.succAbove k)

/-- The chart projection as a linear map. -/
def chartProjL {r : ℕ} (j : Fin (r + 1)) :
    (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun := chartProj j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem chartProjL_apply {r : ℕ} (j : Fin (r + 1))
    (x : Fin (r + 1) → ℝ) : chartProjL j x = chartProj j x := rfl

/-- **Cone volume through the hyperplane chart** (eq:perspective-volume,
ratio form): for compact `E ⊆ {λℝ = 1}`,
`|ℓⱼ| · vol(cone 1 E) = c_r · vol(chartProj j '' E)`. -/
theorem volume_cone_hyperplane {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (hj : ℓ j ≠ 0) {E : Set (Fin (r + 1) → ℝ)}
    (hEc : IsCompact E) (hE1 : ∀ x ∈ E, realFunctional ℓ x = 1) :
    ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E) =
      coneConst r * volume (chartProj j '' E) := by
  have hjR : (ℓ j : ℝ) ≠ 0 := by exact_mod_cast hj
  set S := Matrix.toLin' (hypMatrix ℓ j) with hS
  have himg : S '' E = Fin.insertNth j (1 : ℝ) '' (chartProj j '' E) := by
    rw [← Set.image_comp]
    apply Set.image_congr
    intro x hx
    exact hypMatrix_eq_insertNth ℓ j hjR (hE1 x hx)
  have hdet : LinearMap.det S = (ℓ j : ℝ) := by
    rw [hS, LinearMap.det_toLin', det_hypMatrix]
  have hchartc : IsCompact (chartProj j '' E) :=
    hEc.image (continuous_chartProj j)
  calc ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E)
      = volume (S '' cone 1 E) := by
        rw [Measure.addHaar_image_linearMap, hdet]
    _ = volume (cone 1 (S '' E)) := by rw [image_cone]
    _ = volume (cone 1 (Fin.insertNth j (1 : ℝ) '' (chartProj j '' E))) := by
        rw [himg]
    _ = coneConst r * volume (chartProj j '' E) :=
        volume_cone_insertNth j hchartc

/-- **Cone volume ratio transfer**: a volume ratio in the chart transfers to
the ambient cone volumes. -/
theorem cone_volume_ratio {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (hj : ℓ j ≠ 0) {E' E : Set (Fin (r + 1) → ℝ)} (hE'c : IsCompact E')
    (hEc : IsCompact E) (hE'1 : ∀ x ∈ E', realFunctional ℓ x = 1)
    (hE1 : ∀ x ∈ E, realFunctional ℓ x = 1) {η : ℝ}
    (hvol : volume (chartProj j '' E') ≤
      ENNReal.ofReal η * volume (chartProj j '' E)) :
    volume (cone 1 E') ≤ ENNReal.ofReal η * volume (cone 1 E) := by
  have hjR : (ℓ j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hne0 : ENNReal.ofReal |(ℓ j : ℝ)| ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr hjR
  have hnetop : ENNReal.ofReal |(ℓ j : ℝ)| ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← ENNReal.mul_le_mul_iff_right hne0 hnetop]
  calc ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E')
      = coneConst r * volume (chartProj j '' E') :=
        volume_cone_hyperplane ℓ j hj hE'c hE'1
    _ ≤ coneConst r * (ENNReal.ofReal η * volume (chartProj j '' E)) :=
        mul_le_mul' le_rfl hvol
    _ = ENNReal.ofReal η * (coneConst r * volume (chartProj j '' E)) := by
        ring
    _ = ENNReal.ofReal η * (ENNReal.ofReal |(ℓ j : ℝ)| * volume (cone 1 E)) := by
        rw [volume_cone_hyperplane ℓ j hj hEc hE1]
    _ = ENNReal.ofReal |(ℓ j : ℝ)| * (ENNReal.ofReal η * volume (cone 1 E)) := by
        ring

/-! ## 2. The affine chart of `H_λ = {λℝ = 1}`

`chartProj j` deletes coordinate `j`; `chartSec ℓ j` is its affine section
landing in the hyperplane.  Convexity, compactness, and the indexed
`μ`-convex-position predicate all transfer through the chart. -/

/-- A pointwise recognition principle for `insertNth`. -/
theorem insertNth_eq_of {r : ℕ} {j : Fin (r + 1)} {a : ℝ} {y : Fin r → ℝ}
    {x : Fin (r + 1) → ℝ} (h1 : x j = a)
    (h2 : ∀ k, x (j.succAbove k) = y k) :
    Fin.insertNth j a y = x := by
  have hy : y = j.removeNth x := funext fun k => (h2 k).symm
  rw [← h1, hy]
  exact Fin.insertNth_self_removeNth j x

/-- The affine section of the chart: the unique point of `{λℝ = 1}` above a
chart point. -/
noncomputable def chartSec {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) : Fin (r + 1) → ℝ :=
  Fin.insertNth j
    ((1 - ∑ k, (ℓ (j.succAbove k) : ℝ) * y k) / (ℓ j : ℝ)) y

@[simp] theorem chartProj_apply {r : ℕ} (j : Fin (r + 1))
    (x : Fin (r + 1) → ℝ) (k : Fin r) :
    chartProj j x k = x (j.succAbove k) := rfl

@[simp] theorem chartSec_apply_same {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (y : Fin r → ℝ) :
    chartSec ℓ j y j =
      (1 - ∑ k, (ℓ (j.succAbove k) : ℝ) * y k) / (ℓ j : ℝ) :=
  Fin.insertNth_apply_same j _ _

@[simp] theorem chartSec_apply_succAbove {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) (y : Fin r → ℝ) (k : Fin r) :
    chartSec ℓ j y (j.succAbove k) = y k :=
  Fin.insertNth_apply_succAbove j _ _ _

theorem chartProj_chartSec {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) : chartProj j (chartSec ℓ j y) = y := by
  funext k
  rw [chartProj_apply, chartSec_apply_succAbove]

theorem realFunctional_chartSec {r : ℕ} {ℓ : Fin (r + 1) → ℤ}
    {j : Fin (r + 1)} (hj : (ℓ j : ℝ) ≠ 0) (y : Fin r → ℝ) :
    realFunctional ℓ (chartSec ℓ j y) = 1 := by
  rw [realFunctional_apply,
    Fin.sum_univ_succAbove (fun i => (ℓ i : ℝ) * chartSec ℓ j y i) j,
    chartSec_apply_same]
  have hsum : ∑ k, (ℓ (j.succAbove k) : ℝ) * chartSec ℓ j y (j.succAbove k)
      = ∑ k, (ℓ (j.succAbove k) : ℝ) * y k :=
    Finset.sum_congr rfl fun k _ => by rw [chartSec_apply_succAbove]
  rw [hsum, mul_comm, div_mul_cancel₀ _ hj]
  ring

theorem chartSec_chartProj {r : ℕ} {ℓ : Fin (r + 1) → ℤ}
    {j : Fin (r + 1)} (hj : (ℓ j : ℝ) ≠ 0) {x : Fin (r + 1) → ℝ}
    (hx : realFunctional ℓ x = 1) : chartSec ℓ j (chartProj j x) = x := by
  rw [realFunctional_apply,
    Fin.sum_univ_succAbove (fun i => (ℓ i : ℝ) * x i) j] at hx
  refine insertNth_eq_of ?_ (fun k => rfl)
  have hsum : ∑ k, (ℓ (j.succAbove k) : ℝ) * chartProj j x k
      = ∑ k, (ℓ (j.succAbove k) : ℝ) * x (j.succAbove k) := rfl
  rw [hsum]
  rw [eq_comm, div_eq_iff hj]
  linear_combination -hx

/-- The linear part of the section. -/
noncomputable def chartSecL {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1)) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun y := Fin.insertNth j
    ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y
  map_add' y z := by
    refine insertNth_eq_of ?_ (fun k => ?_)
    · rw [Pi.add_apply, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
      rw [← add_div]
      congr 1
      rw [← neg_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Pi.add_apply]; ring
    · rw [Pi.add_apply, Fin.insertNth_apply_succAbove,
        Fin.insertNth_apply_succAbove]
      rfl
  map_smul' c y := by
    refine insertNth_eq_of ?_ (fun k => ?_)
    · show (c • Fin.insertNth j
        ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y) j = _
      rw [Pi.smul_apply, Fin.insertNth_apply_same, smul_eq_mul]
      have hsum : ∑ k, (ℓ (j.succAbove k) : ℝ) * (c • y) k
          = c * ∑ k, (ℓ (j.succAbove k) : ℝ) * y k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Pi.smul_apply, smul_eq_mul]; ring
      rw [hsum]
      ring
    · show (c • Fin.insertNth j
        ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y)
        (j.succAbove k) = (c • y) k
      rw [Pi.smul_apply, Fin.insertNth_apply_succAbove]
      rfl

theorem chartSecL_apply {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) :
    chartSecL ℓ j y = Fin.insertNth j
      ((-(∑ k, (ℓ (j.succAbove k) : ℝ) * y k)) / (ℓ j : ℝ)) y := rfl

/-- The affine decomposition `chartSec y = chartSec 0 + chartSecL y`. -/
theorem chartSec_eq_add {r : ℕ} (ℓ : Fin (r + 1) → ℤ) (j : Fin (r + 1))
    (y : Fin r → ℝ) :
    chartSec ℓ j y = chartSec ℓ j 0 + chartSecL ℓ j y := by
  refine insertNth_eq_of ?_ (fun k => ?_)
  · rw [Pi.add_apply, chartSec_apply_same, chartSecL_apply,
      Fin.insertNth_apply_same, ← add_div]
    congr 1
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    ring
  · rw [Pi.add_apply, chartSec_apply_succAbove, chartSecL_apply,
      Fin.insertNth_apply_succAbove, Pi.zero_apply, zero_add]

theorem continuous_chartSec {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) : Continuous (chartSec ℓ j) := by
  have : chartSec ℓ j = fun y => chartSec ℓ j 0 + chartSecL ℓ j y :=
    funext fun y => chartSec_eq_add ℓ j y
  rw [this]
  exact continuous_const.add (chartSecL ℓ j).continuous_of_finiteDimensional

theorem convex_chartSec_image {r : ℕ} (ℓ : Fin (r + 1) → ℤ)
    (j : Fin (r + 1)) {K : Set (Fin r → ℝ)} (hK : Convex ℝ K) :
    Convex ℝ (chartSec ℓ j '' K) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
  refine ⟨a • u + b • w, hK hu hw ha hb hab, ?_⟩
  rw [chartSec_eq_add ℓ j (a • u + b • w), chartSec_eq_add ℓ j u,
    chartSec_eq_add ℓ j w, map_add, map_smul, map_smul]
  have hc : a • chartSec ℓ j 0 + b • chartSec ℓ j 0 = chartSec ℓ j 0 := by
    rw [← add_smul, hab, one_smul]
  calc chartSec ℓ j 0 + (a • chartSecL ℓ j u + b • chartSecL ℓ j w)
      = (a • chartSec ℓ j 0 + b • chartSec ℓ j 0) +
        (a • chartSecL ℓ j u + b • chartSecL ℓ j w) := by rw [hc]
    _ = a • (chartSec ℓ j 0 + chartSecL ℓ j u) +
        b • (chartSec ℓ j 0 + chartSecL ℓ j w) := by
        rw [smul_add, smul_add]; abel

/-- Transfer of indexed `μ`-convex position through the chart: half-spaces of
the chart pull back to half-spaces of the ambient space along the affine
section. -/
theorem indexedMuConvexPosition_chartProj {r : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {μ : ℝ} {ℓ : Fin (r + 1) → ℤ} {j : Fin (r + 1)}
    (hj : (ℓ j : ℝ) ≠ 0) {p : ι → Fin (r + 1) → ℝ}
    (hp : ∀ i, realFunctional ℓ (p i) = 1)
    (h : IndexedMuConvexPosition μ p) :
    IndexedMuConvexPosition μ (fun i => chartProj j (p i)) := by
  intro i
  obtain ⟨u, t, hti, hcount⟩ := h i
  have hkey : ∀ k, u (chartSecL ℓ j (chartProj j (p k)))
      = u (p k) - u (chartSec ℓ j 0) := by
    intro k
    have h1 : chartSec ℓ j (chartProj j (p k)) = p k :=
      chartSec_chartProj hj (hp k)
    have h2 : chartSecL ℓ j (chartProj j (p k))
        = p k - chartSec ℓ j 0 := by
      have hd := chartSec_eq_add ℓ j (chartProj j (p k))
      rw [h1] at hd
      rw [eq_sub_iff_add_eq]
      exact (add_comm _ _).trans hd.symm
    rw [h2, map_sub]
  refine ⟨u ∘ₗ chartSecL ℓ j, t - u (chartSec ℓ j 0), ?_, ?_⟩
  · rw [LinearMap.comp_apply, hkey i]
    exact sub_le_sub_right hti _
  · have hfe : (Finset.univ.filter fun k =>
        t - u (chartSec ℓ j 0) ≤ (u ∘ₗ chartSecL ℓ j) (chartProj j (p k)))
        = Finset.univ.filter fun k => t ≤ u (p k) := by
      refine Finset.filter_congr fun k _ => ?_
      rw [LinearMap.comp_apply, hkey k]
      exact sub_le_sub_iff_right _
    rw [hfe]
    exact hcount

/-- Reindexing an indexed `μ`-convex-position family along an equivalence. -/
theorem IndexedMuConvexPosition.comp_equiv {r : ℕ} {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] {μ : ℝ}
    {p : ι → Fin r → ℝ} (h : IndexedMuConvexPosition μ p) (e : κ ≃ ι) :
    IndexedMuConvexPosition μ (fun k => p (e k)) := by
  intro k
  obtain ⟨u, t, ht, hc⟩ := h (e k)
  refine ⟨u, t, ht, ?_⟩
  have hcard : (Finset.univ.filter fun k' : κ => t ≤ u (p (e k'))).card
      = (Finset.univ.filter fun i : ι => t ≤ u (p i)).card := by
    refine Finset.card_bij (fun k' _ => e k') ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha
    · intro a _ b _ hab
      exact e.injective hab
    · intro b hb
      refine ⟨e.symm b, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simpa using hb
  rw [hcard, show (Fintype.card κ) = Fintype.card ι from Fintype.card_congr e]
  exact hc

/-! ### The stage body `Ω = {y ∈ H_λ : X·y ∈ B_ℝ}` -/

/-- The stage body: points of the hyperplane whose `X`-dilate lies in the
real coordinate box. -/
def stageOmega {d : ℕ} (ℓ : Fin d → ℤ) (X : ℕ) (M : Fin d → ℕ) :
    Set (Fin d → ℝ) :=
  {x | realFunctional ℓ x = 1 ∧ (X : ℝ) • x ∈ realCoordinateBox M}

theorem stageOmega_convex {d : ℕ} (ℓ : Fin d → ℤ) (X : ℕ) (M : Fin d → ℕ) :
    Convex ℝ (stageOmega ℓ X M) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [map_add, map_smul, map_smul, hx.1, hy.1, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one, hab]
  · have hrw : (X : ℝ) • (a • x + b • y)
        = a • ((X : ℝ) • x) + b • ((X : ℝ) • y) := by
      rw [smul_add, smul_comm (X : ℝ) a x, smul_comm (X : ℝ) b y]
    rw [hrw]
    exact (realCoordinateBox_convex M) hx.2 hy.2 ha hb hab

theorem stageOmega_subset_box {d : ℕ} {ℓ : Fin d → ℤ} {X : ℕ}
    {M : Fin d → ℕ} (hX : 1 ≤ X) :
    stageOmega ℓ X M ⊆ realCoordinateBox M := by
  intro x hx
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  rw [mem_realCoordinateBox]
  intro i
  have hb := (mem_realCoordinateBox.mp hx.2) i
  rw [Pi.smul_apply, smul_eq_mul] at hb
  have hM : (0 : ℝ) ≤ (M i : ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith [hb.1, hb.2]
  · nlinarith [hb.1, hb.2]

theorem stageOmega_isCompact {d : ℕ} (ℓ : Fin d → ℤ) {X : ℕ}
    (M : Fin d → ℕ) (hX : 1 ≤ X) : IsCompact (stageOmega ℓ X M) := by
  have hclosed : IsClosed (stageOmega ℓ X M) := by
    have h1 : IsClosed {x : Fin d → ℝ | realFunctional ℓ x = 1} :=
      isClosed_eq (realFunctional ℓ).continuous_of_finiteDimensional
        continuous_const
    have h2 : IsClosed {x : Fin d → ℝ | (X : ℝ) • x ∈ realCoordinateBox M} :=
      (realCoordinateBox_isCompact M).isClosed.preimage
        (continuous_const_smul ((X : ℝ)))
    exact h1.inter h2
  exact (realCoordinateBox_isCompact M).of_isClosed_subset hclosed
    (stageOmega_subset_box hX)

/-- The projective normalizations of the shell set live in the stage body. -/
theorem projNorm_mem_stageOmega {d : ℕ} {ℓ : Fin d → ℤ} {X : ℕ}
    {V : Finset (Fin d → ℤ)} {M : Fin d → ℕ} (hX : 1 ≤ X)
    (hshell : ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X V)
    (hVbox : V ⊆ coordinateBox M) {v : Fin d → ℤ} (hv : v ∈ V) :
    projNorm ℓ v ∈ stageOmega ℓ X M :=
  ⟨realFunctional_projNorm_of_shell hX hshell hv,
    smul_projNorm_mem_realBox hX (hshell.1 v hv).1 (hVbox hv)⟩

/-- The height-`X` cone over the stage body stays in the real box. -/
theorem cone_stageOmega_subset {d : ℕ} (ℓ : Fin d → ℤ) (X : ℕ)
    (M : Fin d → ℕ) :
    cone (X : ℝ) (stageOmega ℓ X M) ⊆ realCoordinateBox M := by
  rintro _ ⟨y, hy, t, ht0, htX, rfl⟩
  rw [mem_realCoordinateBox]
  intro i
  have hb := (mem_realCoordinateBox.mp hy.2) i
  rw [Pi.smul_apply, smul_eq_mul] at hb
  rw [Pi.smul_apply, smul_eq_mul]
  have hM : (0 : ℝ) ≤ (M i : ℝ) := Nat.cast_nonneg _
  rcases le_or_gt 0 (y i) with hyi | hyi
  · constructor
    · nlinarith
    · nlinarith
  · constructor
    · nlinarith
    · nlinarith

/-- **Interior of the chart image of the stage body is nonempty**, given that
the shell set spans `ℝ^d` (from `projective_span_package`): the chart image of
`π(V)` affinely spans the chart, and its convex hull sits inside the chart
image of `Ω`. -/
theorem interior_chart_stageOmega_nonempty {r : ℕ} {ℓ : Fin (r + 1) → ℤ}
    {j : Fin (r + 1)} (hj : (ℓ j : ℝ) ≠ 0) {V : Finset (Fin (r + 1) → ℤ)}
    {X : ℕ} {M : Fin (r + 1) → ℕ} (hX : 1 ≤ X)
    (hshell : ShellNonDividing (fun v => (intFunctional ℓ v : ℤ)) X V)
    (hVbox : V ⊆ coordinateBox M) (hVne : V.Nonempty)
    (hspanV : integerRealSpan V = ⊤) :
    (interior (chartProj j '' stageOmega ℓ X M)).Nonempty := by
  classical
  have hpos : ∀ v ∈ V, intFunctional ℓ v ≠ 0 := fun v hv =>
    ne_of_gt (intFunctional_pos_of_shell hX hshell hv)
  have hsp : Submodule.span ℝ (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ))) = ⊤ :=
    span_projNorm_eq_top ℓ hspanV hpos
  obtain ⟨v₀, hv₀⟩ := hVne
  -- The chart image of the projective family affinely spans the chart.
  have haff : affineSpan ℝ
      (chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))) = ⊤ := by
    have hmap := AffineSubspace.map_span ((chartProjL j).toAffineMap)
      (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))
    rw [show ((chartProjL j).toAffineMap) ''
        (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))
        = chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ))) from rfl]
      at hmap
    rw [← hmap]
    rw [eq_top_iff]
    intro y _
    rw [AffineSubspace.mem_map]
    refine ⟨chartSec ℓ j y, ?_, chartProj_chartSec ℓ j y⟩
    rw [mem_affineSpan_projNorm_iff (by omega : 1 ≤ r + 1) ℓ hv₀ hpos hsp]
    exact realFunctional_chartSec hj y
  -- The convex hull of the chart points has nonempty interior.
  have hconvΩc : Convex ℝ (chartProj j '' stageOmega ℓ X M) :=
    (stageOmega_convex ℓ X M).linear_image (chartProjL j)
  have hsubset : convexHull ℝ
      (chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ))))
      ⊆ chartProj j '' stageOmega ℓ X M := by
    refine convexHull_min ?_ hconvΩc
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨projNorm ℓ v, projNorm_mem_stageOmega hX hshell hVbox hv, rfl⟩
  have h1 : (interior (convexHull ℝ
      (chartProj j '' (projNorm ℓ '' (V : Set (Fin (r + 1) → ℤ)))))).Nonempty := by
    rw [Convex.interior_nonempty_iff_affineSpan_eq_top
      (convex_convexHull ℝ _)]
    rw [affineSpan_convexHull]
    exact haff
  exact h1.mono (interior_mono hsubset)

end Nondividing
