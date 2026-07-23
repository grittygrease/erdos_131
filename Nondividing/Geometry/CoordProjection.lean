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

end Nondividing
