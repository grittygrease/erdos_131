import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Nondividing.Geometry.LatticeIndex
import Nondividing.External.DiscreteJohn

open scoped BigOperators
open Module Submodule

namespace Nondividing

open Nondividing.External

/-!
# Coordinate-projection existence (Phase D)

The one remaining ingredient of `lem:lattice-section-box`: an `r`-dimensional
subspace `H ≤ ℝ^d` projects injectively onto some `r`-element coordinate subset.
We realise this via the coordinate evaluation functionals on `H`, which separate
points and therefore span `Dual ℝ H`.
-/

variable {d : ℕ} (H : Submodule ℝ (Fin d → ℝ))

/-- The coordinate evaluation functionals on `H`. -/
noncomputable def coordDual (i : Fin d) : Module.Dual ℝ H :=
  H.dualRestrict (LinearMap.proj i)

@[simp] theorem coordDual_apply (i : Fin d) (x : H) :
    coordDual H i x = (x : Fin d → ℝ) i := by
  simp [coordDual, Submodule.dualRestrict_apply, LinearMap.proj_apply]

/-- The coordinate functionals separate points of `H`, hence span `Dual ℝ H`. -/
theorem span_range_coordDual_eq_top :
    Submodule.span ℝ (Set.range (coordDual H)) = ⊤ := by
  have hcoann : (Submodule.span ℝ (Set.range (coordDual H))).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    have hall : ∀ i, coordDual H i x = 0 := fun i =>
      hx (coordDual H i) (Submodule.subset_span ⟨i, rfl⟩)
    have hx0 : (x : Fin d → ℝ) = 0 := by
      funext i
      simpa using hall i
    rw [Submodule.mem_bot]
    exact Subtype.ext hx0
  have hfr := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span ℝ (Set.range (coordDual H)))
  rw [hcoann, finrank_bot, add_zero] at hfr
  -- `finrank (span) = finrank H = finrank (Dual ℝ H)`
  have hdual : Module.finrank ℝ (Module.Dual ℝ H) = Module.finrank ℝ H :=
    Subspace.dual_finrank_eq
  apply Submodule.eq_top_of_finrank_eq
  rw [hfr, hdual]

/-- **Coordinate-projection existence.**  An `r`-dimensional subspace of `ℝ^d`
projects injectively onto some `r`-element coordinate subset: there is a `Finset`
`I` of size `finrank H` such that the only vector of `H` vanishing on all
coordinates in `I` is `0`. -/
theorem exists_coordProjR_injOn :
    ∃ I : Finset (Fin d), I.card = Module.finrank ℝ H ∧
      ∀ x : Fin d → ℝ, x ∈ H → (∀ i ∈ I, x i = 0) → x = 0 := by
  classical
  have htop := span_range_coordDual_eq_top H
  obtain ⟨f, hf_mem, hf_span, hf_indep⟩ :=
    exists_fun_fin_finrank_span_eq ℝ (Set.range (coordDual H))
  have hf_top : Submodule.span ℝ (Set.range f) = ⊤ := hf_span.trans htop
  -- the index type has size `finrank H`
  have hr : Module.finrank ℝ (Submodule.span ℝ (Set.range (coordDual H)))
      = Module.finrank ℝ H := by
    rw [htop, finrank_top, Subspace.dual_finrank_eq]
  -- choose coordinate indices realising the extracted functionals
  choose idx hidx using hf_mem
  have hidx_inj : Function.Injective idx := by
    intro a b hab
    apply hf_indep.injective
    rw [← hidx a, ← hidx b, hab]
  refine ⟨Finset.univ.image idx, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hidx_inj, Finset.card_univ, Fintype.card_fin, hr]
  · intro x hx hxI
    -- every extracted functional vanishes at `⟨x, hx⟩`
    have hfk : ∀ k, f k ⟨x, hx⟩ = 0 := by
      intro k
      have hmem : idx k ∈ Finset.univ.image idx :=
        Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
      have := hxI (idx k) hmem
      rw [← hidx k]
      simpa using this
    -- the evaluation functional vanishes on the spanning set, hence everywhere
    set E := (Module.Dual.eval ℝ H) ⟨x, hx⟩ with hE
    have hEf : ∀ k, E (f k) = 0 := by
      intro k; rw [hE, Module.Dual.eval_apply]; exact hfk k
    have hker : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker E := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hEf k
    rw [hf_top] at hker
    have hE0 : E = 0 := by
      rw [← LinearMap.ker_eq_top]
      exact top_le_iff.mp hker
    have hall : ∀ φ : Module.Dual ℝ H, φ ⟨x, hx⟩ = 0 := by
      intro φ
      have := LinearMap.congr_fun hE0 φ
      rwa [hE, Module.Dual.eval_apply] at this
    have hx0 : (⟨x, hx⟩ : H) = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℝ _).mp hall
    exact congrArg (Subtype.val) hx0

/-- The real point of a subset sum of `V` lies in the real span of `V`. -/
theorem realPoint_subsetSums_mem {d : ℕ} {V : Finset (Fin d → ℤ)} {w : Fin d → ℤ}
    (hw : w ∈ subsetSums V) : realPoint w ∈ integerRealSpan V := by
  obtain ⟨S, hSV, rfl⟩ := mem_subsetSums.mp hw
  have hrw : realPoint (∑ a ∈ S, a) = ∑ a ∈ S, realPoint a := by
    funext j
    simp only [realPoint, Finset.sum_apply]
    push_cast
    rfl
  rw [hrw]
  exact Submodule.sum_mem _ fun a ha =>
    Submodule.subset_span ⟨a, hSV ha, rfl⟩

/-- Each real step vector of `P` lies in the real span of the shell set `V`,
using the E1 inclusion `q + step_i ∈ Σ(C₀) ⊆ ⟨V⟩` (valid once `c·s ≥ 1`, so the
unit coefficient vector is admissible). -/
theorem realStep_mem_integerRealSpan {d e : ℕ} (P : GAP d e) {c s : ℝ}
    (hcs : 1 ≤ c * s) {V C₀ : Finset (Fin d → ℤ)} (hC₀V : C₀ ⊆ V) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier (c * s), q + z ∈ subsetSums C₀) (i : Fin e) :
    (fun j => (P.step i j : ℝ)) ∈ integerRealSpan V := by
  classical
  have hri : 1 ≤ P.dilatedRadius (c * s) i := by
    show 1 ≤ ⌊(c * s) * (P.radius i : ℝ)⌋₊
    apply Nat.le_floor
    have : (1 : ℝ) ≤ (P.radius i : ℝ) := by exact_mod_cast P.radius_pos i
    push_cast
    nlinarith [hcs, this]
  have hei : (Pi.single i (1 : ℤ)) ∈ P.dilatedCoeffBox (c * s) := by
    rw [GAP.dilatedCoeffBox, mem_coordinateBox]
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [Pi.single_eq_same]
      have : (1 : ℤ) ≤ (P.dilatedRadius (c * s) j : ℤ) := by exact_mod_cast hri
      omega
    · rw [Pi.single_eq_of_ne hj]
      have : (0 : ℤ) ≤ (P.dilatedRadius (c * s) j : ℤ) := Int.natCast_nonneg _
      omega
  have heval : P.evalHom (Pi.single i (1 : ℤ)) = (fun j => P.step i j) := by
    funext j
    rw [GAP.evalHom_apply, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_mul]
    · intro k _ hk; rw [Pi.single_eq_of_ne hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hstep_mem : (fun j => P.step i j) ∈ P.dilatedCarrier (c * s) :=
    (P.mem_dilatedCarrier).mpr ⟨Pi.single i 1, hei, heval⟩
  have hsub : subsetSums C₀ ⊆ subsetSums V := by
    intro w hw
    obtain ⟨S, hSC₀, rfl⟩ := mem_subsetSums.mp hw
    exact mem_subsetSums.mpr ⟨S, hSC₀.trans hC₀V, rfl⟩
  have hq_mem : q ∈ subsetSums C₀ := by
    have := hincl 0 (P.zero_mem_dilatedCarrier _); rwa [add_zero] at this
  have hqs_mem : q + (fun j => P.step i j) ∈ subsetSums C₀ := hincl _ hstep_mem
  have h1 := realPoint_subsetSums_mem (hsub hq_mem)
  have h2 := realPoint_subsetSums_mem (hsub hqs_mem)
  have hdiff : (fun j => (P.step i j : ℝ)) =
      realPoint (q + (fun j => P.step i j)) - realPoint q := by
    funext j
    simp only [realPoint, Pi.sub_apply, Pi.add_apply]
    push_cast; ring
  rw [hdiff]
  exact Submodule.sub_mem _ h2 h1

/-- **Full-dimensional support** (`lem:projective-span`, first conclusion).  If
the step lattice of `P(V)` has full rank `d`, then the real span of the shell set
`V` is all of `ℝ^d`. -/
theorem integerRealSpan_eq_top {d e : ℕ} (P : GAP d e) {c s : ℝ}
    (hcs : 1 ≤ c * s) {V C₀ : Finset (Fin d → ℤ)} (hC₀V : C₀ ⊆ V) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier (c * s), q + z ∈ subsetSums C₀)
    (hrank : P.realRank = d) :
    integerRealSpan V = ⊤ := by
  have hsteps : Submodule.span ℝ
      (Set.range fun i : Fin e => (fun j : Fin d => (P.step i j : ℝ)))
        ≤ integerRealSpan V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact realStep_mem_integerRealSpan P hcs hC₀V hincl i
  have h1 : P.realRank ≤ Module.finrank ℝ (integerRealSpan V) :=
    Submodule.finrank_mono hsteps
  rw [hrank] at h1
  have h2 : Module.finrank ℝ (integerRealSpan V) ≤ d := by
    have h := Submodule.finrank_le (integerRealSpan V)
    rwa [Module.finrank_pi, Fintype.card_fin] at h
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_pi, Fintype.card_fin]
  omega

/-- The step rank never exceeds the displayed dimension. -/
theorem realRank_le {d e : ℕ} (P : GAP d e) : P.realRank ≤ e := by
  have h := finrank_range_le_card (R := ℝ)
    (fun i : Fin e => (fun j : Fin d => (P.step i j : ℝ)))
  rw [Fintype.card_fin] at h
  exact h

/-- The real rank of a dilated GAP carrier is at most the rank of its step
vectors: every carrier point is an integer combination of the steps. -/
theorem finrank_integerRealSpan_dilatedCarrier_le_realRank {d e : ℕ} (P : GAP d e)
    (t : ℝ) :
    Module.finrank ℝ (integerRealSpan (P.dilatedCarrier t)) ≤ P.realRank := by
  classical
  have hsub : integerRealSpan (P.dilatedCarrier t) ≤
      Submodule.span ℝ
        (Set.range fun i : Fin e => (fun j : Fin d => (P.step i j : ℝ))) := by
    rw [integerRealSpan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨n, _hn, rfl⟩ := (P.mem_dilatedCarrier).mp (Finset.mem_coe.mp hw)
    have heq : realPoint (P.evalHom n) =
        ∑ i, (n i : ℝ) • (fun j : Fin d => (P.step i j : ℝ)) := by
      funext j
      simp only [realPoint, GAP.evalHom_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      push_cast
      rfl
    rw [SetLike.mem_coe, heq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.finrank_mono hsub

/-- `realPoint` is injective. -/
theorem realPoint_injective {d : ℕ} : Function.Injective (realPoint (d := d)) := by
  intro z w h
  funext i
  have : (z i : ℝ) = (w i : ℝ) := congrFun h i
  exact_mod_cast this

/-- **Lattice sections of a coordinate box** (`lem:lattice-section-box`).  A set
`A` of integer points in the `t`-dilated symmetric coordinate box has
`|A| ≤ t^r · |B|`, where `r = dim ⟨A⟩_ℝ` is the real rank of `A`.  The injective
coordinate projection is supplied by `exists_coordProjR_injOn`. -/
theorem lattice_section_box {d : ℕ} {M : Fin d → ℕ} {t : ℝ} (ht : 1 ≤ t)
    {A : Finset (Fin d → ℤ)}
    (hA : A ⊆ coordinateBox (fun i => ⌊t * (M i : ℝ)⌋₊)) :
    (A.card : ℝ) ≤
      t ^ (Module.finrank ℝ (integerRealSpan A)) * ((coordinateBox M).card : ℝ) := by
  classical
  obtain ⟨I, hIcard, hInj⟩ := exists_coordProjR_injOn (integerRealSpan A)
  refine latticeSection_card_le ht hA I hIcard ?_
  -- Transfer the real injectivity to the integer coordinate projection on `A`.
  intro z hz w hw hzw
  have hmemI : ∀ i ∈ I, z i = w i := by
    intro i hi
    have := congrFun hzw i
    simpa [coordProj, hi] using this
  -- the difference of real points lies in `H` and vanishes on `I`
  have hzH : realPoint z ∈ integerRealSpan A :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  have hwH : realPoint w ∈ integerRealSpan A :=
    Submodule.subset_span ⟨w, hw, rfl⟩
  have hxH : realPoint z - realPoint w ∈ integerRealSpan A :=
    Submodule.sub_mem _ hzH hwH
  have hxI : ∀ i ∈ I, (realPoint z - realPoint w) i = 0 := by
    intro i hi
    have : z i = w i := hmemI i hi
    simp only [Pi.sub_apply, realPoint, this, sub_self]
  have hx0 : realPoint z - realPoint w = 0 := hInj _ hxH hxI
  have : realPoint z = realPoint w := by
    rw [sub_eq_zero] at hx0; exact hx0
  exact realPoint_injective this

/-- **Index cardinality bound** (`lem:index-bound`, section step).  The proper
dilate `csP` has `|csP| ≤ (2|C₀|)^r · |B|`, where `r = realRank P` is the rank of
the step lattice.  Combined with the proper lower bound `|csP| ≫ s^d |P|`, the
gap `d - r` forces full rank. -/
theorem card_dilatedCarrier_le_index {d e : ℕ} (P : GAP d e) {t : ℝ}
    {M : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)} (hC₀ : C₀ ⊆ coordinateBox M)
    (hcard : 1 ≤ C₀.card) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀) :
    ((P.dilatedCarrier t).card : ℝ) ≤
      (2 * C₀.card : ℝ) ^ P.realRank * ((coordinateBox M).card : ℝ) := by
  classical
  have ht1 : (1 : ℝ) ≤ 2 * C₀.card := by
    have : (1 : ℝ) ≤ (C₀.card : ℝ) := by exact_mod_cast hcard
    linarith
  have hcont : P.dilatedCarrier t ⊆
      coordinateBox (fun i => ⌊(2 * (C₀.card : ℝ)) * (M i : ℝ)⌋₊) := by
    have h1 := dilatedCarrier_subset_coordinateBox P hC₀ hincl
    intro z hz
    have hz2 := h1 hz
    rw [mem_coordinateBox] at hz2 ⊢
    intro i
    have hfloor : ⌊(2 * (C₀.card : ℝ)) * (M i : ℝ)⌋₊ = 2 * C₀.card * M i := by
      rw [show (2 * (C₀.card : ℝ)) * (M i : ℝ) = ((2 * C₀.card * M i : ℕ) : ℝ) by
        push_cast; ring, Nat.floor_natCast]
    rw [hfloor]; exact hz2 i
  have hlsb := lattice_section_box (M := M) (t := 2 * (C₀.card : ℝ)) ht1 hcont
  have hfr := finrank_integerRealSpan_dilatedCarrier_le_realRank P t
  calc ((P.dilatedCarrier t).card : ℝ)
      ≤ (2 * (C₀.card : ℝ)) ^
            (Module.finrank ℝ (integerRealSpan (P.dilatedCarrier t)))
          * ((coordinateBox M).card : ℝ) := hlsb
    _ ≤ (2 * (C₀.card : ℝ)) ^ P.realRank * ((coordinateBox M).card : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ ht1 hfr

/-- Assembled index inequality: the proper lower bound `t^e |P| ≤ 3^e |csP|`
composed with the section upper bound gives
`t^e |P| ≤ 3^e (2|C₀|)^r |B|`.  With `t = c·s`, `|C₀| ≤ s`, `e = d`, and
`|P| ≥ γ|B|`, the exponent gap `d - r` yields the full-rank conclusion of
`lem:index-bound`. -/
theorem index_cardinality_bound {d e : ℕ} (P : GAP d e) (hP : P.Proper) {t : ℝ}
    (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ)))
    {M : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)} (hC₀ : C₀ ⊆ coordinateBox M)
    (hcard : 1 ≤ C₀.card) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀) :
    t ^ e * (P.carrier.card : ℝ) ≤
      3 ^ e * (2 * C₀.card : ℝ) ^ P.realRank * ((coordinateBox M).card : ℝ) := by
  have h1 := P.scale_card_carrier_le_dilated hP ht hInj
  have h2 := card_dilatedCarrier_le_index P hC₀ hcard hincl
  calc t ^ e * (P.carrier.card : ℝ)
      ≤ 3 ^ e * ((P.dilatedCarrier t).card : ℝ) := h1
    _ ≤ 3 ^ e * ((2 * C₀.card : ℝ) ^ P.realRank * ((coordinateBox M).card : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 3 ^ e * (2 * C₀.card : ℝ) ^ P.realRank * ((coordinateBox M).card : ℝ) := by
        ring

/-- **Full rank from irreducibility** (`lem:index-bound`, first conclusion).  If
the progression's box occupancy is at least `γ|B|` and the scale product `sγ` is
large (`6^d < c^d·s·γ`), then the step lattice has full rank `d`.  The proof is
the exponent-gap contradiction `s^{d-r}γ ≪ 1`. -/
theorem realRank_eq_of_index {d e : ℕ} (hd : 1 ≤ e) (P : GAP d e)
    (hP : P.Proper)
    {c s γ : ℝ} (hc : 0 < c) (hs : 1 ≤ s) (hγ : 0 < γ) (hcs : 1 ≤ c * s)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox (c * s) : Set (Fin e → ℤ)))
    {M : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)} (hC₀ : C₀ ⊆ coordinateBox M)
    (hcard1 : 1 ≤ C₀.card) (hcards : (C₀.card : ℝ) ≤ s) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier (c * s), q + z ∈ subsetSums C₀)
    (hB : 0 < ((coordinateBox M).card : ℝ))
    (hPlow : γ * ((coordinateBox M).card : ℝ) ≤ (P.carrier.card : ℝ))
    (hthresh : (6 : ℝ) ^ e < c ^ e * (s * γ)) :
    P.realRank = e := by
  refine le_antisymm (realRank_le P) ?_
  by_contra hlt
  push_neg at hlt
  set r := P.realRank with hr
  have hspos : (0 : ℝ) < s := by linarith
  have hib := index_cardinality_bound P hP hcs hInj hC₀ hcard1 hincl
  have hbase : (2 * (C₀.card : ℝ)) ^ r ≤ (2 * s) ^ r :=
    pow_le_pow_left₀ (by positivity) (by linarith) r
  have hD : (c * s) ^ e * γ ≤ 3 ^ e * (2 * s) ^ r := by
    have hstep : (c * s) ^ e * (γ * ((coordinateBox M).card : ℝ)) ≤
        3 ^ e * (2 * s) ^ r * ((coordinateBox M).card : ℝ) := by
      calc (c * s) ^ e * (γ * ((coordinateBox M).card : ℝ))
          ≤ (c * s) ^ e * (P.carrier.card : ℝ) :=
            mul_le_mul_of_nonneg_left hPlow (by positivity)
        _ ≤ 3 ^ e * (2 * (C₀.card : ℝ)) ^ r * ((coordinateBox M).card : ℝ) := hib
        _ ≤ 3 ^ e * (2 * s) ^ r * ((coordinateBox M).card : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hbase (by positivity)
    have := le_of_mul_le_mul_right (by nlinarith [hstep] : ((c * s) ^ e * γ)
        * ((coordinateBox M).card : ℝ) ≤ (3 ^ e * (2 * s) ^ r)
        * ((coordinateBox M).card : ℝ)) hB
    linarith [this]
  have hsplit : s ^ e = s ^ r * s ^ (e - r) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
  have hsr : (0 : ℝ) < s ^ r := by positivity
  have hexp : c ^ e * (s ^ r * s ^ (e - r)) * γ ≤ 3 ^ e * (2 ^ r * s ^ r) := by
    have h1 : (c * s) ^ e = c ^ e * s ^ e := by rw [mul_pow]
    have h2 : (2 * s) ^ r = 2 ^ r * s ^ r := by rw [mul_pow]
    rw [h1, h2, hsplit] at hD
    linarith [hD]
  have hdiv : c ^ e * s ^ (e - r) * γ ≤ 3 ^ e * 2 ^ r :=
    le_of_mul_le_mul_right (by nlinarith [hexp]) hsr
  have hge : s ≤ s ^ (e - r) := by
    have : s ^ (1 : ℕ) ≤ s ^ (e - r) := pow_le_pow_right₀ hs (by omega)
    simpa using this
  have h2r : (2 : ℝ) ^ r ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) hlt.le
  have hfinal : c ^ e * (s * γ) ≤ 6 ^ e := by
    have hmono : c ^ e * (s * γ) ≤ c ^ e * s ^ (e - r) * γ := by
      have : c ^ e * s * γ ≤ c ^ e * s ^ (e - r) * γ := by
        apply mul_le_mul_of_nonneg_right _ hγ.le
        exact mul_le_mul_of_nonneg_left hge (by positivity)
      nlinarith [this]
    have h6 : (3 : ℝ) ^ e * 2 ^ e = 6 ^ e := by
      rw [← mul_pow]; norm_num
    calc c ^ e * (s * γ) ≤ c ^ e * s ^ (e - r) * γ := hmono
      _ ≤ 3 ^ e * 2 ^ r := hdiv
      _ ≤ 3 ^ e * 2 ^ e := by apply mul_le_mul_of_nonneg_left h2r (by positivity)
      _ = 6 ^ e := h6
  linarith [hthresh, hfinal]

end Nondividing
