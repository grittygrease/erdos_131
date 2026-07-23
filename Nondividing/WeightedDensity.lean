import Nondividing.External.ConvexDensity
import Nondividing.Projective.Convexity

open scoped BigOperators
open MeasureTheory

namespace Nondividing

/-!
# Weighted convex-density lemma, injective case (Phase G, `lem:weighted-density`)

For an *injective* indexed family the weighted lemma is exactly the published
set version (E4): the image finset has the same cardinality and the same
half-space counts, so μ-convex position and the cap count transfer verbatim.
(The manuscript's perturbation argument exists only to remove the injectivity
assumption; it is the remaining gap.)
-/

section
open Classical

/-- **Weighted convex-density, injective families** (`lem:weighted-density`
under injectivity).  Direct transfer to E4 through the image finset. -/
theorem weighted_density_injective (r : ℕ) (hr : 1 ≤ r) (eps : ℝ)
    (heps : 0 < eps) :
    ∃ tau μ₀ : ℝ, 0 < tau ∧ tau < 1 ∧ 0 < μ₀ ∧
      ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∃ n₀ : ℕ,
      ∀ (n : ℕ) (p : Fin n → (Fin r → ℝ)) (Omega : Set (Fin r → ℝ)),
        n₀ ≤ n → Function.Injective p →
        IsCompact Omega → Convex ℝ Omega → (interior Omega).Nonempty →
        (∀ i, p i ∈ Omega) → IndexedMuConvexPosition μ p →
        ∃ eta : ℝ, μ ≤ eta ∧ eta ≤ Real.rpow μ tau ∧
        ∃ Omega' : Set (Fin r → ℝ),
          MeasurableSet Omega' ∧ Convex ℝ Omega' ∧ Omega' ⊆ Omega ∧
          volume Omega' ≤ ENNReal.ofReal eta * volume Omega ∧
          (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * n ≤
            ((Finset.univ.filter (fun i => p i ∈ Omega')).card : ℝ) := by
  classical
  obtain ⟨tau, μ₀, htau0, htau1, hμ₀, hE4⟩ :=
    External.convex_density_set r hr eps heps
  refine ⟨tau, μ₀, htau0, htau1, hμ₀, ?_⟩
  intro μ hμ hμμ₀
  obtain ⟨n₀, hn₀⟩ := hE4 μ hμ hμμ₀
  refine ⟨n₀, ?_⟩
  intro n p Omega hn hinj hcomp hconv hint hpΩ hpos
  set A : Finset (Fin r → ℝ) := Finset.univ.image p with hA
  have hAcard : A.card = n := by
    rw [hA, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  -- ncard of set intersections equals the index-filter cardinality.
  have hncard : ∀ S : Set (Fin r → ℝ),
      ((A : Set (Fin r → ℝ)) ∩ S).ncard
        = (Finset.univ.filter (fun i => p i ∈ S)).card := by
    intro S
    have h1 : (A : Set (Fin r → ℝ)) ∩ S
        = ↑(A.filter (fun q => q ∈ S)) := by
      ext q
      simp [Set.mem_inter_iff]
    rw [h1, Set.ncard_coe_finset, hA]
    rw [show (Finset.univ.image p).filter (fun q => q ∈ S)
        = (Finset.univ.filter (fun i => p i ∈ S)).image p from by
      ext q
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨i, rfl⟩, hq⟩; exact ⟨i, hq, rfl⟩
      · rintro ⟨i, hq, rfl⟩; exact ⟨⟨i, rfl⟩, hq⟩]
    exact Finset.card_image_of_injective _ hinj
  -- Transfer μ-convex position.
  have hApos : External.SetMuConvexPosition μ A := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hA ▸ hq)
    obtain ⟨ℓ, t, hjt, hcount⟩ := hpos j
    refine ⟨ℓ, t, hjt, ?_⟩
    rw [hncard (External.closedUpperHalfspace ℓ t), hAcard]
    have hcount' : ((Finset.univ.filter (fun k => t ≤ ℓ (p k))).card : ℝ)
        ≤ μ * n := by
      calc ((Finset.univ.filter (fun k => t ≤ ℓ (p k))).card : ℝ)
          ≤ μ * Fintype.card (Fin n) := hcount
        _ = μ * n := by rw [Fintype.card_fin]
    have hpred : (Finset.univ.filter
          (fun i => p i ∈ External.closedUpperHalfspace ℓ t))
        = (Finset.univ.filter (fun k => t ≤ ℓ (p k))) := by
      apply Finset.filter_congr
      intro k _
      exact Iff.rfl
    rw [hpred]
    exact hcount'
  -- Apply E4.
  have hAΩ : (A : Set (Fin r → ℝ)) ⊆ Omega := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hA ▸ hq)
    exact hpΩ i
  have hAn₀ : n₀ ≤ A.card := by rw [hAcard]; exact hn
  obtain ⟨eta, hηlo, hηhi, Omega', hmeas, hconv', hsub', hvol, hcount⟩ :=
    hn₀ Omega A hAn₀ hcomp hconv hint hAΩ hApos
  refine ⟨eta, hηlo, hηhi, Omega', hmeas, hconv', hsub', hvol, ?_⟩
  rw [hncard Omega', hAcard] at hcount
  exact hcount

end

end Nondividing
