import Nondividing.Projective.Normalization
import Mathlib.Analysis.Convex.Combination

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# Indexed convex position (Phase E)

The manuscript's projective duality, convexity, and weighted-density arguments
count incidences of an *indexed* family (with multiplicity), not of its
deduplicated image (route hazard §7.2).  This file fixes the indexed
`μ`-convex-position predicate and the negation used to pick a failing index.
-/

/-- An indexed family `p : ι → ℝ^r` is in `μ`-convex position if for every index
`j` there is a closed half-space containing `p j` and at most `μ·|ι|` indices
(counted with multiplicity).  A half-space is `{x : t ≤ ℓ x}`. -/
def IndexedMuConvexPosition {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ℝ) (p : ι → (Fin r → ℝ)) : Prop :=
  ∀ j : ι, ∃ (ℓ : Module.Dual ℝ (Fin r → ℝ)) (t : ℝ),
    t ≤ ℓ (p j) ∧
    ((Finset.univ.filter fun k => t ≤ ℓ (p k)).card : ℝ) ≤ μ * Fintype.card ι

/-- Negation: some index `a` lies in no half-space with few indices — every
closed half-space through `p a` contains more than `μ·|ι|` indices. -/
theorem not_indexedMuConvexPosition_iff {r : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {μ : ℝ} {p : ι → (Fin r → ℝ)} :
    ¬ IndexedMuConvexPosition μ p ↔
      ∃ a : ι, ∀ (ℓ : Module.Dual ℝ (Fin r → ℝ)) (t : ℝ), t ≤ ℓ (p a) →
        μ * Fintype.card ι <
          ((Finset.univ.filter fun k => t ≤ ℓ (p k)).card : ℝ) := by
  unfold IndexedMuConvexPosition
  push_neg
  rfl

/-- Multiplying a projective convex combination `π(a) = ∑ cᵥ·π(v)` by `λ(a)`
turns it into an integer-point relation `a = ∑ (cᵥ·λa/λv)·v`.  This connects the
separation output to `duality_representation`. -/
theorem projNorm_combination {d : ℕ} {ℓ : Fin d → ℤ} {a : Fin d → ℤ}
    {V : Finset (Fin d → ℤ)} {c : (Fin d → ℤ) → ℝ}
    (haℓ : intFunctional ℓ a ≠ 0) (hposV : ∀ v ∈ V, intFunctional ℓ v ≠ 0)
    (hrepr : projNorm ℓ a = ∑ v ∈ V, c v • projNorm ℓ v) :
    realPoint a = ∑ v ∈ V,
      (c v * ((intFunctional ℓ a : ℝ) / (intFunctional ℓ v : ℝ))) • realPoint v := by
  have ha' : ((intFunctional ℓ a : ℤ) : ℝ) ≠ 0 := by exact_mod_cast haℓ
  have h1 : realPoint a = (intFunctional ℓ a : ℝ) • projNorm ℓ a := by
    rw [projNorm, smul_inv_smul₀ ha']
  rw [h1, hrepr, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hv' : ((intFunctional ℓ v : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hposV v hv
  rw [projNorm, smul_smul, smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- **Duality representation** (`lem:projective-duality`, arithmetic core).  From
a bounded convex combination realising `a` as `∑_{v∈V} gᵥ·v` — where the
self-weight `g a ≤ 1/4`, all weights are in `[0,G]`, and the total weight lies in
`[1/2,2]` — one obtains a representation of `a` by the *other* points with weights
`βᵥ ∈ [0, (4/3)G]` whose total lies in `[1/3, 3]`.  (The convex combination itself
comes from the separation step, which is separate.) -/
theorem duality_representation {d : ℕ} {a : Fin d → ℤ}
    {V : Finset (Fin d → ℤ)} (haV : a ∈ V) {g : (Fin d → ℤ) → ℝ} {G : ℝ}
    (hg0 : ∀ v ∈ V, 0 ≤ g v) (hga : g a ≤ 1 / 4) (hgub : ∀ v ∈ V, g v ≤ G)
    (hgsum_lo : 1 / 2 ≤ ∑ v ∈ V, g v) (hgsum_hi : ∑ v ∈ V, g v ≤ 2)
    (hrepr : realPoint a = ∑ v ∈ V, g v • realPoint v) :
    ∃ β : (Fin d → ℤ) → ℝ,
      realPoint a = ∑ v ∈ V.erase a, β v • realPoint v ∧
      (∀ v ∈ V.erase a, 0 ≤ β v ∧ β v ≤ 4 / 3 * G) ∧
      1 / 3 ≤ ∑ v ∈ V.erase a, β v ∧ ∑ v ∈ V.erase a, β v ≤ 3 := by
  have hga0 : 0 ≤ g a := hg0 a haV
  have ha1 : (0 : ℝ) < 1 - g a := by linarith
  have hinv_pos : (0 : ℝ) < (1 - g a)⁻¹ := inv_pos.mpr ha1
  have hprod : (1 - g a)⁻¹ * (1 - g a) = 1 := inv_mul_cancel₀ (ne_of_gt ha1)
  have hinv_le : (1 - g a)⁻¹ ≤ 4 / 3 := by
    nlinarith [hprod, hinv_pos, hga]
  -- vector identity: (1 - g a) • a = ∑_{v≠a} g v • v
  have haux : g a • realPoint a + ∑ v ∈ V.erase a, g v • realPoint v
      = ∑ v ∈ V, g v • realPoint v :=
    Finset.add_sum_erase V (fun v => g v • realPoint v) haV
  have hkey : (1 - g a) • realPoint a = ∑ v ∈ V.erase a, g v • realPoint v := by
    have hsplit : realPoint a
        = g a • realPoint a + ∑ v ∈ V.erase a, g v • realPoint v :=
      hrepr.trans haux.symm
    rw [sub_smul, one_smul]
    nth_rewrite 1 [hsplit]
    abel
  refine ⟨fun v => (1 - g a)⁻¹ * g v, ?_, ?_, ?_, ?_⟩
  · have hexpand : ∑ v ∈ V.erase a, ((1 - g a)⁻¹ * g v) • realPoint v
        = (1 - g a)⁻¹ • ∑ v ∈ V.erase a, g v • realPoint v := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [smul_smul]
    rw [hexpand, ← hkey, inv_smul_smul₀ (ne_of_gt ha1)]
  · intro v hv
    have hv0 : 0 ≤ g v := hg0 v (Finset.mem_of_mem_erase hv)
    have hvub : g v ≤ G := hgub v (Finset.mem_of_mem_erase hv)
    have hGnn : 0 ≤ G := le_trans hv0 hvub
    exact ⟨mul_nonneg hinv_pos.le hv0,
      mul_le_mul hinv_le hvub hv0 (by norm_num)⟩
  · -- sum lower bound
    have hsumβ : ∑ v ∈ V.erase a, ((1 - g a)⁻¹ * g v)
        = (1 - g a)⁻¹ * ((∑ v ∈ V, g v) - g a) := by
      rw [← Finset.mul_sum]; congr 1
      have := Finset.add_sum_erase V g haV
      linarith
    rw [hsumβ]
    nlinarith [hprod, hinv_pos, hga, hga0, hgsum_lo]
  · have hsumβ : ∑ v ∈ V.erase a, ((1 - g a)⁻¹ * g v)
        = (1 - g a)⁻¹ * ((∑ v ∈ V, g v) - g a) := by
      rw [← Finset.mul_sum]; congr 1
      have := Finset.add_sum_erase V g haV
      linarith
    rw [hsumβ]
    nlinarith [hprod, hinv_pos, hga, hga0, hgsum_hi]

/-- **Projective duality modulo separation.**  Given a projective convex
combination `π(a) = ∑ cᵥ·π(v)` with `0 ≤ cᵥ ≤ (μn)⁻¹`, `∑ cᵥ = 1`, over a shell
set (so `λa/λv ∈ [1/2,2]`) with `μn ≥ 4`, the integer point `a` is a combination
of the other points with weights in `[0, 4/μn]` totalling in `[1/3, 3]`.  Only the
production of the convex combination (Hahn–Banach separation) remains for the
full `lem:projective-duality`. -/
theorem duality_representation_from_projective {d : ℕ} {ℓ : Fin d → ℤ}
    {a : Fin d → ℤ} {V : Finset (Fin d → ℤ)} (haV : a ∈ V) {c : (Fin d → ℤ) → ℝ}
    {X : ℕ} {μn : ℝ} (hμn : 4 ≤ μn) (hX : 1 ≤ X)
    (hshell : ∀ v ∈ V, (X : ℤ) ≤ intFunctional ℓ v ∧ intFunctional ℓ v ≤ 2 * X)
    (hc0 : ∀ v ∈ V, 0 ≤ c v) (hcub : ∀ v ∈ V, c v ≤ (μn)⁻¹)
    (hcsum : ∑ v ∈ V, c v = 1)
    (hrepr : projNorm ℓ a = ∑ v ∈ V, c v • projNorm ℓ v) :
    ∃ β : (Fin d → ℤ) → ℝ,
      realPoint a = ∑ v ∈ V.erase a, β v • realPoint v ∧
      (∀ v ∈ V.erase a, 0 ≤ β v ∧ β v ≤ 4 / μn) ∧
      1 / 3 ≤ ∑ v ∈ V.erase a, β v ∧ ∑ v ∈ V.erase a, β v ≤ 3 := by
  have hμnpos : 0 < μn := by linarith
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  -- positivity and ratio bounds from the shell
  have hlam_pos : ∀ v ∈ V, 0 < intFunctional ℓ v := by
    intro v hv
    have := (hshell v hv).1
    have : (1 : ℤ) ≤ (X : ℤ) := by exact_mod_cast hX
    linarith [(hshell v hv).1]
  have hlam_R : ∀ v ∈ V, 0 < ((intFunctional ℓ v : ℤ) : ℝ) := fun v hv => by
    exact_mod_cast hlam_pos v hv
  set g : (Fin d → ℤ) → ℝ :=
    fun v => c v * ((intFunctional ℓ a : ℝ) / (intFunctional ℓ v : ℝ)) with hg
  have hratio_lo : ∀ v ∈ V, (1 : ℝ) / 2 ≤
      (intFunctional ℓ a : ℝ) / (intFunctional ℓ v : ℝ) := by
    intro v hv
    rw [le_div_iff₀ (hlam_R v hv)]
    have h1 : ((X : ℤ) : ℝ) ≤ (intFunctional ℓ a : ℝ) := by exact_mod_cast (hshell a haV).1
    have h2 : ((intFunctional ℓ v : ℤ) : ℝ) ≤ (2 * X : ℤ) := by exact_mod_cast (hshell v hv).2
    push_cast at h1 h2 ⊢
    nlinarith [h1, h2, hXR]
  have hratio_hi : ∀ v ∈ V,
      (intFunctional ℓ a : ℝ) / (intFunctional ℓ v : ℝ) ≤ 2 := by
    intro v hv
    rw [div_le_iff₀ (hlam_R v hv)]
    have h1 : (intFunctional ℓ a : ℝ) ≤ (2 * X : ℤ) := by exact_mod_cast (hshell a haV).2
    have h2 : ((X : ℤ) : ℝ) ≤ (intFunctional ℓ v : ℝ) := by exact_mod_cast (hshell v hv).1
    push_cast at h1 h2 ⊢
    nlinarith [h1, h2, hXR]
  have hgint : realPoint a = ∑ v ∈ V, g v • realPoint v :=
    projNorm_combination (ne_of_gt (hlam_pos a haV))
      (fun v hv => ne_of_gt (hlam_pos v hv)) hrepr
  -- g-bounds
  have hg0 : ∀ v ∈ V, 0 ≤ g v := fun v hv =>
    mul_nonneg (hc0 v hv) (div_nonneg (hlam_R a haV).le (hlam_R v hv).le)
  have hga : g a ≤ 1 / 4 := by
    have hself : ((intFunctional ℓ a : ℝ) / (intFunctional ℓ a : ℝ)) = 1 :=
      div_self (ne_of_gt (hlam_R a haV))
    have : g a = c a := by rw [hg]; simp only [hself, mul_one]
    have hca : c a ≤ (μn)⁻¹ := hcub a haV
    have : (μn)⁻¹ ≤ 1 / 4 := by
      rw [inv_le_iff_one_le_mul₀ hμnpos]; linarith
    linarith [hcub a haV, ‹g a = c a›]
  have hgub : ∀ v ∈ V, g v ≤ 2 / μn := by
    intro v hv
    have hc := hcub v hv
    have hr := hratio_hi v hv
    have : g v = c v * ((intFunctional ℓ a : ℝ) / (intFunctional ℓ v : ℝ)) := rfl
    rw [this]
    have hrn : (0 : ℝ) ≤ (intFunctional ℓ a : ℝ) / (intFunctional ℓ v : ℝ) :=
      div_nonneg (hlam_R a haV).le (hlam_R v hv).le
    calc c v * _ ≤ (μn)⁻¹ * 2 :=
          mul_le_mul hc hr hrn (by positivity)
      _ = 2 / μn := by rw [inv_mul_eq_div]
  have hgsum_lo : 1 / 2 ≤ ∑ v ∈ V, g v := by
    calc (1 : ℝ) / 2 = ∑ v ∈ V, c v * (1 / 2) := by rw [← Finset.sum_mul, hcsum]; ring
      _ ≤ ∑ v ∈ V, g v :=
          Finset.sum_le_sum fun v hv =>
            mul_le_mul_of_nonneg_left (hratio_lo v hv) (hc0 v hv)
  have hgsum_hi : ∑ v ∈ V, g v ≤ 2 := by
    calc ∑ v ∈ V, g v ≤ ∑ v ∈ V, c v * 2 :=
          Finset.sum_le_sum fun v hv =>
            mul_le_mul_of_nonneg_left (hratio_hi v hv) (hc0 v hv)
      _ = 2 := by rw [← Finset.sum_mul, hcsum]; ring
  obtain ⟨β, hβrepr, hβbound, hβlo, hβhi⟩ :=
    duality_representation haV hg0 hga hgub hgsum_lo hgsum_hi hgint
  refine ⟨β, hβrepr, fun v hv => ⟨(hβbound v hv).1, ?_⟩, hβlo, hβhi⟩
  have hbv := (hβbound v hv).2
  have hμne : μn ≠ 0 := ne_of_gt hμnpos
  have h43 : (4 : ℝ) / 3 * (2 / μn) ≤ 4 / μn := by
    have hd : (0 : ℝ) < 4 / (3 * μn) := div_pos (by norm_num) (by linarith)
    have he : 4 / μn - 4 / 3 * (2 / μn) = 4 / (3 * μn) := by field_simp; ring
    linarith [hd, he]
  linarith [hbv, h43]

end Nondividing
