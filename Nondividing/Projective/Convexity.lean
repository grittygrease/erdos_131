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

end Nondividing
