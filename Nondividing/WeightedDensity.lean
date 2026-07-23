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

/-- **Stabilized subsequence** (Blaschke step of `lem:weighted-density`): a
sequence with finitely many possible values has a constant strictly monotone
subsequence — used to fix the index set `{i : qᵢ^{(m)} ∈ K_m}` along the
Blaschke-convergent subsequence. -/
theorem exists_constant_subseq {α : Type*} [Finite α] (f : ℕ → α) :
    ∃ (a : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, f (φ k) = a := by
  classical
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber f
  haveI : Infinite (f ⁻¹' {a} : Set ℕ) := ha
  refine ⟨a, Nat.orderEmbeddingOfSet (f ⁻¹' {a}), (Nat.orderEmbeddingOfSet _).strictMono, ?_⟩
  intro k
  have hrange := Nat.orderEmbeddingOfSet_range (f ⁻¹' {a})
  exact (Set.ext_iff.mp hrange _).mp (Set.mem_range_self k)

section Perturbation

open Metric

/-- **Half-space ∩ ball is infinite** (perturbation step of
`lem:weighted-density`): in `ℝ^r`, `r ≥ 1`, a closed half-space containing the
centre meets every ball in infinitely many points — walk from the centre in a
direction the functional does not decrease. -/
theorem halfspace_ball_infinite {r : ℕ} (hr : 1 ≤ r)
    (ℓ : Module.Dual ℝ (Fin r → ℝ)) (t : ℝ) {x : Fin r → ℝ} (hx : t ≤ ℓ x)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ({y : Fin r → ℝ | t ≤ ℓ y} ∩ Metric.ball x ρ).Infinite := by
  -- A direction `v ≠ 0` with `ℓ v ≥ 0`.
  set v₀ : Fin r → ℝ := Pi.single ⟨0, hr⟩ 1 with hv₀
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hr⟩
    rw [hv₀, Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  set v : Fin r → ℝ := if 0 ≤ ℓ v₀ then v₀ else -v₀ with hv
  have hvne : v ≠ 0 := by
    rw [hv]
    by_cases h : 0 ≤ ℓ v₀ <;> simp [h, hv₀ne]
  have hℓv : 0 ≤ ℓ v := by
    rw [hv]
    by_cases h : 0 ≤ ℓ v₀
    · rwa [if_pos h]
    · rw [if_neg h, map_neg]
      push_neg at h
      linarith
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  -- The injective segment `s ↦ x + s • v`, `s ∈ (0, ρ/‖v‖)`.
  set f : ℝ → (Fin r → ℝ) := fun s => x + s • v with hf
  have hfinj : Function.Injective f := by
    intro s₁ s₂ h
    have h2 : s₁ • v = s₂ • v := by
      have h3 : x + s₁ • v = x + s₂ • v := h
      have := congrArg (fun z => z - x) h3
      simpa [add_sub_cancel_left] using this
    have hsv : (s₁ - s₂) • v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp hsv with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hvne
  have himg : f '' (Set.Ioo 0 (ρ / ‖v‖)) ⊆
      {y : Fin r → ℝ | t ≤ ℓ y} ∩ Metric.ball x ρ := by
    rintro _ ⟨s, ⟨hs0, hsρ⟩, rfl⟩
    constructor
    · show t ≤ ℓ (x + s • v)
      rw [map_add, map_smul, smul_eq_mul]
      nlinarith
    · rw [Metric.mem_ball, dist_eq_norm]
      rw [show x + s • v - x = s • v from by abel]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      calc s * ‖v‖ < (ρ / ‖v‖) * ‖v‖ :=
            mul_lt_mul_of_pos_right hsρ hvnorm
        _ = ρ := by field_simp
  exact Set.Infinite.mono himg
    ((Set.Ioo_infinite (by positivity)).image (hfinj.injOn))

/-- **Ball avoiding finitely many closed sets**: a point outside finitely many
closed sets has a ball avoiding all of them. -/
theorem exists_ball_disjoint_closed {X : Type*} [MetricSpace X] {ι : Type*}
    (s : Finset ι) (F : ι → Set X) (hF : ∀ i ∈ s, IsClosed (F i))
    (x : X) (hx : ∀ i ∈ s, x ∉ F i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, Metric.ball x δ ∩ F i = ∅ := by
  classical
  have hopen : IsOpen (⋂ i ∈ s, (F i)ᶜ) :=
    isOpen_biInter_finset fun i hi => (hF i hi).isOpen_compl
  have hxU : x ∈ ⋂ i ∈ s, (F i)ᶜ := by
    rw [Set.mem_iInter₂]
    exact fun i hi => hx i hi
  obtain ⟨δ, hδ0, hδsub⟩ := Metric.isOpen_iff.mp hopen x hxU
  refine ⟨δ, hδ0, fun i hi => ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  intro y ⟨hyball, hyF⟩
  have := hδsub hyball
  rw [Set.mem_iInter₂] at this
  exact this i hi hyF

/-- **Distinct selection from infinite sets**: given infinitely many choices at
every index, an injective selection exists (recursive choice avoiding the
finitely many previous picks). -/
theorem exists_injective_selection {X : Type*} :
    ∀ (n : ℕ) (S : Fin n → Set X), (∀ i, (S i).Infinite) →
    ∃ q : Fin n → X, Function.Injective q ∧ ∀ i, q i ∈ S i := by
  intro n
  induction n with
  | zero => exact fun S _ => ⟨fun i => absurd i.2 (by omega), fun i => absurd i.2 (by omega),
      fun i => absurd i.2 (by omega)⟩
  | succ m ih =>
    intro S hS
    obtain ⟨q', hq'inj, hq'mem⟩ := ih (fun i => S i.castSucc)
      (fun i => hS i.castSucc)
    -- Pick the last point outside the finite range of `q'`.
    have hlast : (S (Fin.last m) \ (Set.range q')).Nonempty := by
      have hfin : (Set.range q').Finite := Set.finite_range q'
      exact Set.Infinite.nonempty (Set.Infinite.diff (hS (Fin.last m)) hfin)
    obtain ⟨x, hxS, hxq'⟩ := hlast
    refine ⟨Fin.snoc q' x, ?_, ?_⟩
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hij
        exact congrArg Fin.castSucc (hq'inj hij)
      · rw [Fin.snoc_castSucc, Fin.snoc_last] at hij
        exact absurd (Set.mem_range.mpr ⟨i', hij⟩) hxq'
      · rw [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd (Set.mem_range.mpr ⟨j', hij.symm⟩) hxq'
      · rfl
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact hq'mem i'
      · rw [Fin.snoc_last]
        exact hxS

/-- **The perturbed family exists** (`lem:weighted-density`, perturbation
step): the points can be moved distances `< ρ` to become pairwise distinct,
staying in their own witnessing half-spaces and entering no new ones. -/
theorem exists_perturbed_family {r n : ℕ} (hr : 1 ≤ r)
    (p : Fin n → (Fin r → ℝ))
    (ℓ : Fin n → Module.Dual ℝ (Fin r → ℝ)) (t : Fin n → ℝ)
    (hmem : ∀ j, t j ≤ ℓ j (p j)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ q : Fin n → (Fin r → ℝ), Function.Injective q ∧
      (∀ i, dist (q i) (p i) < ρ) ∧
      (∀ i, t i ≤ ℓ i (q i)) ∧
      (∀ i j, t j ≤ ℓ j (q i) → t j ≤ ℓ j (p i)) := by
  classical
  -- Half-spaces are closed.
  have hclosed : ∀ j : Fin n, IsClosed {y : Fin r → ℝ | t j ≤ ℓ j y} := by
    intro j
    have hcont : Continuous (ℓ j) := LinearMap.continuous_of_finiteDimensional _
    exact isClosed_le continuous_const hcont
  -- For each `i`, a radius avoiding all half-spaces not containing `p i`.
  have hδ : ∀ i : Fin n, ∃ δ : ℝ, 0 < δ ∧
      ∀ j ∈ Finset.univ.filter (fun j => ¬ t j ≤ ℓ j (p i)),
        Metric.ball (p i) δ ∩ {y : Fin r → ℝ | t j ≤ ℓ j y} = ∅ := by
    intro i
    apply exists_ball_disjoint_closed _ _ (fun j _ => hclosed j)
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  choose δ hδ0 hδavoid using hδ
  -- The infinite choice sets.
  set S : Fin n → Set (Fin r → ℝ) :=
    fun i => {y : Fin r → ℝ | t i ≤ ℓ i y} ∩ Metric.ball (p i) (min (δ i) ρ)
    with hS
  have hSinf : ∀ i, (S i).Infinite := by
    intro i
    exact halfspace_ball_infinite hr (ℓ i) (t i) (hmem i)
      (lt_min (hδ0 i) hρ)
  obtain ⟨q, hqinj, hqmem⟩ := exists_injective_selection n S hSinf
  refine ⟨q, hqinj, ?_, ?_, ?_⟩
  · intro i
    have := (hqmem i).2
    rw [Metric.mem_ball] at this
    exact lt_of_lt_of_le this (min_le_right _ _)
  · intro i
    exact (hqmem i).1
  · intro i j hqij
    by_contra hpij
    have hjbad : j ∈ Finset.univ.filter (fun j => ¬ t j ≤ ℓ j (p i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpij⟩
    have hempty := hδavoid i j hjbad
    have hqball : q i ∈ Metric.ball (p i) (δ i) := by
      have := (hqmem i).2
      rw [Metric.mem_ball] at this ⊢
      exact lt_of_lt_of_le this (min_le_left _ _)
    have : q i ∈ Metric.ball (p i) (δ i) ∩ {y : Fin r → ℝ | t j ≤ ℓ j y} :=
      ⟨hqball, hqij⟩
    rw [hempty] at this
    exact this

end Perturbation

end Nondividing
