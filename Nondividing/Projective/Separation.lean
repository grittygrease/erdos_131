import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Dual.Defs

open scoped BigOperators
open Set

namespace Nondividing

/-!
# Capped-simplex separation (Phase E)

The separation heart of `lem:projective-duality`: if every closed half-space
through `p a` contains more than `M` of the indexed points `p k`, then `p a` is a
`M⁻¹`-capped convex combination of the `p k`.  Proved by separating `p a` from the
(compact convex) capped convex hull and using the incidence count to contradict
the separating functional.
-/

/-- The `M⁻¹`-capped standard simplex in `ι → ℝ`. -/
def cappedSimplex (ι : Type*) [Fintype ι] (M : ℝ) : Set (ι → ℝ) :=
  stdSimplex ℝ ι ∩ {c | ∀ k, c k ≤ M⁻¹}

theorem isCompact_cappedSimplex (ι : Type*) [Fintype ι] (M : ℝ) :
    IsCompact (cappedSimplex ι M) := by
  refine (isCompact_stdSimplex ℝ ι).inter_right ?_
  have : {c : ι → ℝ | ∀ k, c k ≤ M⁻¹} = ⋂ k, {c : ι → ℝ | c k ≤ M⁻¹} := by
    ext c; simp
  rw [this]
  exact isClosed_iInter fun k => isClosed_le (continuous_apply k) continuous_const

theorem convex_cappedSimplex (ι : Type*) [Fintype ι] (M : ℝ) :
    Convex ℝ (cappedSimplex ι M) := by
  refine (convex_stdSimplex ℝ ι).inter ?_
  intro x hx y hy s t hs ht hst k
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsm : s * M⁻¹ + t * M⁻¹ = M⁻¹ := by rw [← add_mul, hst, one_mul]
  have h1 : s * x k ≤ s * M⁻¹ := mul_le_mul_of_nonneg_left (hx k) hs
  have h2 : t * y k ≤ t * M⁻¹ := mul_le_mul_of_nonneg_left (hy k) ht
  linarith [h1, h2, hsm]

/-- **Capped separation.**  If every half-space `{x : u(p a) ≤ u x}` contains more
than `M ≥ 1` of the points `p k`, then `p a` is an `M⁻¹`-capped convex combination
of the `p k`. -/
theorem exists_capped_combination {r : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → (Fin r → ℝ)) (a : ι) {M : ℝ} (hM : 1 ≤ M)
    (hfail : ∀ u : Module.Dual ℝ (Fin r → ℝ),
      M < ((Finset.univ.filter fun k => u (p a) ≤ u (p k)).card : ℝ)) :
    ∃ c : ι → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k, c k ≤ M⁻¹) ∧ (∑ k, c k = 1) ∧
      p a = ∑ k, c k • p k := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the capped convex hull and its compactness/convexity
  set L : (ι → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    ∑ k, (LinearMap.proj k).smulRight (p k) with hLdef
  have hLapply : ∀ c : ι → ℝ, L c = ∑ k, c k • p k := by
    intro c
    simp [hLdef, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  set K : Set (Fin r → ℝ) := L '' cappedSimplex ι M with hK
  have hKcompact : IsCompact K :=
    (isCompact_cappedSimplex ι M).image (L.continuous_of_finiteDimensional)
  have hKconv : Convex ℝ K := (convex_cappedSimplex ι M).linear_image L
  have hpa : p a ∉ K := by
    rintro ⟨c, ⟨⟨hc0, hcsum⟩, hcub⟩, hLc⟩
    exact hcon c hc0 hcub hcsum (by rw [← hLapply c, hLc])
  obtain ⟨u, u', hu_lt, hu'⟩ :=
    geometric_hahn_banach_closed_point hKconv hKcompact.isClosed hpa
  -- incidence count
  set S₀ := Finset.univ.filter fun k => u (p a) ≤ u (p k) with hS₀def
  have hcard : M < (S₀.card : ℝ) := hfail u
  have hS₀card_pos : 0 < S₀.card := by
    have : (0 : ℝ) < S₀.card := lt_of_lt_of_le (by linarith) hcard.le
    exact_mod_cast this
  have hMle : M ≤ (S₀.card : ℝ) := hcard.le
  -- capped uniform combination on `S₀`
  set c₀ : ι → ℝ := fun k => if k ∈ S₀ then (S₀.card : ℝ)⁻¹ else 0 with hc₀def
  have hcardR : (0 : ℝ) < (S₀.card : ℝ) := by exact_mod_cast hS₀card_pos
  have hc₀0 : ∀ k, 0 ≤ c₀ k := by
    intro k; simp only [hc₀def]; split_ifs <;> positivity
  have hc₀ub : ∀ k, c₀ k ≤ M⁻¹ := by
    intro k; simp only [hc₀def]; split_ifs
    · rw [inv_le_inv₀ hcardR (by linarith)]; exact hMle
    · exact inv_nonneg.mpr (by linarith)
  have hc₀sum : ∑ k, c₀ k = 1 := by
    simp only [hc₀def]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    field_simp
  set y := ∑ k, c₀ k • p k with hy
  have hyK : y ∈ K := by
    refine ⟨c₀, ⟨⟨hc₀0, hc₀sum⟩, hc₀ub⟩, ?_⟩
    rw [hLapply]
  -- `u y < u (p a)` by separation, but `u y ≥ u (p a)` by the count
  have huy_lt : u y < u (p a) := lt_trans (hu_lt y hyK) hu'
  have huy_ge : u (p a) ≤ u y := by
    rw [hy, map_sum]
    have hcombo : ∑ k, u (c₀ k • p k) = ∑ k, c₀ k * u (p k) := by
      exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]
    rw [hcombo]
    calc u (p a) = ∑ k, c₀ k * u (p a) := by rw [← Finset.sum_mul, hc₀sum, one_mul]
      _ ≤ ∑ k, c₀ k * u (p k) := by
          refine Finset.sum_le_sum fun k _ => ?_
          simp only [hc₀def]
          split_ifs with hk
          · exact mul_le_mul_of_nonneg_left
              (Finset.mem_filter.mp hk).2 (by positivity)
          · simp
  linarith

end Nondividing
