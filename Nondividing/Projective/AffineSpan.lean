import Nondividing.Projective.Normalization
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# Affine direction of the projective image (Phase E)

Toward `lem:projective-span` part 2 (`aff π(V) = H_λ`): the direction space of the
affine span of `π(V)` is contained in the hyperplane direction `ker λℝ`, since all
projective images lie on `{λℝ = 1}` and hence their differences are annihilated by
`λℝ`.  (The reverse inclusion follows from `span_projNorm_eq_top` by a dimension
count.)
-/

theorem vectorSpan_projNorm_le_ker {d : ℕ} (ℓ : Fin d → ℤ)
    {V : Finset (Fin d → ℤ)} (hpos : ∀ v ∈ V, intFunctional ℓ v ≠ 0) :
    vectorSpan ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ)))
      ≤ LinearMap.ker (realFunctional ℓ) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub]
  rw [realFunctional_projNorm ℓ v (hpos v hv),
    realFunctional_projNorm ℓ w (hpos w hw)]
  ring

/-- **Affine direction equality** (`lem:projective-span` part 2, direction).  When
the projective family spans `ℝ^d` linearly (`span_projNorm_eq_top`), the direction
of its affine span is exactly the hyperplane direction `ker λℝ`. -/
theorem vectorSpan_projNorm_eq_ker {d : ℕ} (hd : 1 ≤ d) (ℓ : Fin d → ℤ)
    {V : Finset (Fin d → ℤ)} (hVne : V.Nonempty)
    (hpos : ∀ v ∈ V, intFunctional ℓ v ≠ 0)
    (hspan : Submodule.span ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ))) = ⊤) :
    vectorSpan ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ)))
      = LinearMap.ker (realFunctional ℓ) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hVne
  set S := projNorm ℓ '' (V : Set (Fin d → ℤ)) with hSdef
  set p := projNorm ℓ v₀ with hpdef
  have hf1 : realFunctional ℓ p = 1 := realFunctional_projNorm ℓ v₀ (hpos v₀ hv₀)
  have hpne : p ≠ 0 := by
    intro h; rw [h] at hf1; simp at hf1
  have hle : vectorSpan ℝ S ≤ LinearMap.ker (realFunctional ℓ) :=
    vectorSpan_projNorm_le_ker ℓ hpos
  have hfr_top : Module.finrank ℝ (Fin d → ℝ) = d := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  -- `span S = ⊤ ≤ vectorSpan ⊔ span{p}`
  have hsub : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ vectorSpan ℝ S ⊔ Submodule.span ℝ {p} := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hdiff : projNorm ℓ v - p ∈ vectorSpan ℝ S := by
      rw [vectorSpan_def]
      apply Submodule.subset_span
      exact ⟨projNorm ℓ v, ⟨v, hv, rfl⟩, p, ⟨v₀, hv₀, rfl⟩, rfl⟩
    have heq : projNorm ℓ v = (projNorm ℓ v - p) + p := by abel
    rw [SetLike.mem_coe, heq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hdiff)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self p))
  -- dimension count: `d ≤ finrank(vectorSpan) + 1`
  have hd_le : d ≤ Module.finrank ℝ (vectorSpan ℝ S) + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ S)
      (Submodule.span ℝ {p})
    have h2 := Submodule.finrank_mono hsub
    rw [finrank_span_singleton hpne] at h1
    rw [finrank_top, hfr_top] at h2
    omega
  -- ker of a nonzero functional has dimension `d - 1`
  have hker : Module.finrank ℝ (LinearMap.ker (realFunctional ℓ)) + 1 = d := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (realFunctional ℓ)
    rw [hfr_top] at hrk
    have hsurj : Function.Surjective (realFunctional ℓ) := fun r =>
      ⟨r • p, by rw [map_smul, hf1, smul_eq_mul, mul_one]⟩
    have hrange : Module.finrank ℝ (LinearMap.range (realFunctional ℓ)) = 1 := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
    omega
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

/-- The affine span of `π(V)` is the affine hyperplane through `π(v₀)` with
direction `ker λℝ`. -/
theorem affineSpan_projNorm_eq_mk' {d : ℕ} (hd : 1 ≤ d) (ℓ : Fin d → ℤ)
    {V : Finset (Fin d → ℤ)} {v₀ : Fin d → ℤ} (hv₀ : v₀ ∈ V)
    (hpos : ∀ v ∈ V, intFunctional ℓ v ≠ 0)
    (hspan : Submodule.span ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ))) = ⊤) :
    affineSpan ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ))) =
      AffineSubspace.mk' (projNorm ℓ v₀) (LinearMap.ker (realFunctional ℓ)) := by
  apply AffineSubspace.ext_of_direction_eq
  · rw [direction_affineSpan, AffineSubspace.direction_mk',
      vectorSpan_projNorm_eq_ker hd ℓ ⟨v₀, hv₀⟩ hpos hspan]
  · exact ⟨projNorm ℓ v₀, subset_affineSpan ℝ _ ⟨v₀, hv₀, rfl⟩,
      AffineSubspace.self_mem_mk' _ _⟩

/-- **`lem:projective-span` part 2 (full):** `aff π(V) = H_λ = {q : λℝ(q) = 1}`. -/
theorem mem_affineSpan_projNorm_iff {d : ℕ} (hd : 1 ≤ d) (ℓ : Fin d → ℤ)
    {V : Finset (Fin d → ℤ)} {v₀ : Fin d → ℤ} (hv₀ : v₀ ∈ V)
    (hpos : ∀ v ∈ V, intFunctional ℓ v ≠ 0)
    (hspan : Submodule.span ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ))) = ⊤)
    {q : Fin d → ℝ} :
    q ∈ affineSpan ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ))) ↔
      realFunctional ℓ q = 1 := by
  rw [affineSpan_projNorm_eq_mk' hd ℓ hv₀ hpos hspan, AffineSubspace.mem_mk',
    LinearMap.mem_ker, vsub_eq_sub, map_sub,
    realFunctional_projNorm ℓ v₀ (hpos v₀ hv₀), sub_eq_zero]

end Nondividing
