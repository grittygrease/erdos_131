import Nondividing.WeightedDensity

/-!
# Weighted convex-density lemma: the ρ → 0 Blaschke limit (Phase G, final assembly)

`weighted_density_step` produces, at every scale `ρ > 0`, a density `η_ρ`, a convex
body `K_ρ` lying within `ρ` of `Ω`, and a perturbed family `q_ρ` capturing many points.
Here we send `ρ = 1/(m+1) → 0`: after extracting

* a convergent subsequence of the densities (compactness of `Icc μ (μ^τ)`),
* a Blaschke-convergent subsequence of the bodies (E5a), and
* a constant subsequence of the (finitely many) index sets,

the limit body `L` sits inside `Ω`, satisfies the volume bound with respect to `Ω`
itself (volume continuity E5b plus `vol(Ω + B̄_ρ) → vol Ω`), and captures the original
points `p i` for every index in the constant index set.
-/

open scoped BigOperators Pointwise
open MeasureTheory Metric Filter

namespace Nondividing

section
open Classical

/-- The volume of the `ε`-enlargement `Ω + B̄(0, ε)` of a convex body tends to the
volume of `Ω` as `ε → 0`, via Hausdorff convergence of convex bodies (E5b). -/
theorem tendsto_volume_add_closedBall {d : ℕ} {Omega : Set (Fin d → ℝ)}
    (hcomp : IsCompact Omega) (hconv : Convex ℝ Omega) (hΩne : Omega.Nonempty)
    {ε : ℕ → ℝ} (hε0 : ∀ k, 0 ≤ ε k) (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun k => volume (Omega + Metric.closedBall (0 : Fin d → ℝ) (ε k)))
      atTop (nhds (volume Omega)) := by
  obtain ⟨B, hcoeB⟩ : ∃ B : ℕ → ConvexBody (Fin d → ℝ),
      ∀ k, (B k : Set (Fin d → ℝ)) =
        Omega + Metric.closedBall (0 : Fin d → ℝ) (ε k) :=
    ⟨fun k =>
      ⟨Omega + Metric.closedBall (0 : Fin d → ℝ) (ε k),
        hconv.add (convex_closedBall _ _),
        hcomp.add (isCompact_closedBall _ _),
        hΩne.add ⟨0, Metric.mem_closedBall_self (hε0 k)⟩⟩,
      fun _ => rfl⟩
  obtain ⟨ΩB, hcoeΩ⟩ : ∃ ΩB : ConvexBody (Fin d → ℝ),
      (ΩB : Set (Fin d → ℝ)) = Omega :=
    ⟨⟨Omega, hconv, hcomp, hΩne⟩, rfl⟩
  have hdist : ∀ k, dist (B k) ΩB ≤ ε k := by
    intro k
    have hd : dist (B k) ΩB
        = hausdorffDist (B k : Set (Fin d → ℝ)) (ΩB : Set (Fin d → ℝ)) := rfl
    rw [hd, hcoeB, hcoeΩ]
    exact hausdorffDist_add_closedBall_le hΩne (hε0 k)
  have hBtend : Tendsto B atTop (nhds ΩB) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) hdist hε
  have hvol := External.convexBody_volume_tendsto hBtend
  simpa only [hcoeB, hcoeΩ] using hvol

/-- **Weighted convex-density lemma** (`lem:weighted-density`, full version):
the `ρ → 0` Blaschke limit of `weighted_density_step`. -/
theorem weighted_density (r : ℕ) (hr : 1 ≤ r) (eps : ℝ) (heps : 0 < eps) :
    ∃ tau μ₀ : ℝ, 0 < tau ∧ tau < 1 ∧ 0 < μ₀ ∧
      ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∃ n₀ : ℕ,
      ∀ (n : ℕ) (p : Fin n → (Fin r → ℝ)) (Omega : Set (Fin r → ℝ)),
        n₀ ≤ n → 1 ≤ n →
        IsCompact Omega → Convex ℝ Omega → (interior Omega).Nonempty →
        (∀ i, p i ∈ Omega) → IndexedMuConvexPosition μ p →
        ∃ eta : ℝ, μ ≤ eta ∧ eta ≤ Real.rpow μ tau ∧
        ∃ K : ConvexBody (Fin r → ℝ),
          (K : Set (Fin r → ℝ)) ⊆ Omega ∧
          volume (K : Set (Fin r → ℝ)) ≤ ENNReal.ofReal eta * volume Omega ∧
          (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * n ≤
            ((Finset.univ.filter
              (fun i => p i ∈ (K : Set (Fin r → ℝ)))).card : ℝ) := by
  classical
  -- Step 1: constants from the single-scale step.
  obtain ⟨tau, μ₀, htau0, htau1, hμ₀, hstep⟩ := weighted_density_step r hr eps heps
  refine ⟨tau, μ₀, htau0, htau1, hμ₀, ?_⟩
  intro μ hμ hμμ₀
  obtain ⟨n₀, hn₀⟩ := hstep μ hμ hμμ₀
  refine ⟨n₀, ?_⟩
  intro n p Omega hn hn1 hcomp hconv hint hpΩ hpos
  have hΩne : Omega.Nonempty := hint.mono interior_subset
  have hρpos : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
  -- Step 2: apply the step at every scale ρ m = 1/(m+1).
  have hall : ∀ m : ℕ, ∃ eta : ℝ, μ ≤ eta ∧ eta ≤ Real.rpow μ tau ∧
      ∃ K : ConvexBody (Fin r → ℝ),
        (∀ y ∈ K, infDist y Omega ≤ 1 / ((m : ℝ) + 1)) ∧
        volume (K : Set (Fin r → ℝ)) ≤ ENNReal.ofReal eta *
          volume (Omega + Metric.closedBall (0 : Fin r → ℝ) (1 / ((m : ℝ) + 1))) ∧
        ∃ q : Fin n → (Fin r → ℝ),
          (∀ i, dist (q i) (p i) < 1 / ((m : ℝ) + 1)) ∧
          (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * n ≤
            ((Finset.univ.filter
              (fun i => q i ∈ (K : Set (Fin r → ℝ)))).card : ℝ) :=
    fun m => hn₀ n p Omega hn hn1 hcomp hconv hint hpΩ hpos _ (hρpos m)
  choose η hη₁ hη₂ K hKinf hKvol q hqdist hqcount using hall
  -- Step 3: convergent subsequence of the densities.
  obtain ⟨ηs, hηsmem, φ₁, hφ₁, hηconv⟩ :=
    (isCompact_Icc (a := μ) (b := Real.rpow μ tau)).tendsto_subseq
      (fun m => Set.mem_Icc.mpr ⟨hη₁ m, hη₂ m⟩)
  -- Step 4: uniform bound for the bodies.
  obtain ⟨C₀, hcoeC⟩ : ∃ C₀ : ConvexBody (Fin r → ℝ),
      (C₀ : Set (Fin r → ℝ)) = Omega + Metric.closedBall (0 : Fin r → ℝ) 1 :=
    ⟨⟨Omega + Metric.closedBall (0 : Fin r → ℝ) 1,
      hconv.add (convex_closedBall _ _),
      hcomp.add (isCompact_closedBall _ _),
      hΩne.add ⟨0, Metric.mem_closedBall_self zero_le_one⟩⟩, rfl⟩
  have hKC : ∀ m, K m ≤ C₀ := by
    intro m y hy
    have hinf1 : infDist y Omega ≤ 1 := by
      refine (hKinf m y hy).trans ?_
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_left (Nat.cast_nonneg m)
    obtain ⟨a, ha, hda⟩ := hcomp.exists_infDist_eq_dist hΩne y
    rw [← SetLike.mem_coe, hcoeC, Set.mem_add]
    refine ⟨a, ha, y - a, ?_, by abel⟩
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact hda ▸ hinf1
  -- Step 5: Blaschke selection.
  obtain ⟨φ₂, hφ₂, L, hKL⟩ :=
    External.blaschke_selection (fun j => K (φ₁ j)) C₀ (fun j => hKC (φ₁ j))
  -- Step 6: constant subsequence of the index sets.
  obtain ⟨I₀, φ₃, hφ₃, hIconst⟩ := exists_constant_subseq
    (fun j => Finset.univ.filter
      (fun i => q (φ₁ (φ₂ j)) i ∈ (K (φ₁ (φ₂ j)) : Set (Fin r → ℝ))))
  have hIconst' : ∀ k : ℕ, Finset.univ.filter
      (fun i => q (φ₁ (φ₂ (φ₃ k))) i ∈
        (K (φ₁ (φ₂ (φ₃ k))) : Set (Fin r → ℝ))) = I₀ :=
    fun k => hIconst k
  have hψmono : StrictMono (fun k => φ₁ (φ₂ (φ₃ k))) := hφ₁.comp (hφ₂.comp hφ₃)
  have hψge : ∀ k, k ≤ φ₁ (φ₂ (φ₃ k)) := fun k => hψmono.le_apply
  have hρψle : ∀ k : ℕ,
      (1 : ℝ) / ((φ₁ (φ₂ (φ₃ k)) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ (hψge k)
  have hρψ0 : Tendsto (fun k => (1 : ℝ) / ((φ₁ (φ₂ (φ₃ k)) : ℝ) + 1))
      atTop (nhds 0) :=
    squeeze_zero (fun k => (hρpos _).le) hρψle
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hKψ : Tendsto (fun k => K (φ₁ (φ₂ (φ₃ k)))) atTop (nhds L) :=
    hKL.comp hφ₃.tendsto_atTop
  have hηψ : Tendsto (fun k => η (φ₁ (φ₂ (φ₃ k)))) atTop (nhds ηs) :=
    hηconv.comp (hφ₂.comp hφ₃).tendsto_atTop
  -- Step 7: every index in `I₀` is captured by the limit body.
  have hpL : ∀ i ∈ I₀, p i ∈ (L : Set (Fin r → ℝ)) := by
    intro i hi
    have hqmem : ∀ k : ℕ, q (φ₁ (φ₂ (φ₃ k))) i ∈ K (φ₁ (φ₂ (φ₃ k))) := by
      intro k
      have hik : i ∈ Finset.univ.filter
          (fun i => q (φ₁ (φ₂ (φ₃ k))) i ∈
            (K (φ₁ (φ₂ (φ₃ k))) : Set (Fin r → ℝ))) := by
        rw [hIconst' k]; exact hi
      exact (Finset.mem_filter.mp hik).2
    have hqtend : Tendsto (fun k => q (φ₁ (φ₂ (φ₃ k))) i) atTop (nhds (p i)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun k => dist_nonneg)
        (fun k => ((hqdist (φ₁ (φ₂ (φ₃ k))) i).le).trans (hρψle k))
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact mem_of_tendsto_convexBody hKψ hqtend hqmem
  have hsubL : I₀ ⊆ Finset.univ.filter (fun i => p i ∈ (L : Set (Fin r → ℝ))) :=
    fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpL i hi⟩
  -- Step 8: pass the counting bound to the limit.
  have hηs_pos : 0 < ηs := lt_of_lt_of_le hμ (Set.mem_Icc.mp hηsmem).1
  have hcount : ∀ k : ℕ,
      η (φ₁ (φ₂ (φ₃ k))) ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) * n
        ≤ (I₀.card : ℝ) := by
    intro k
    have h := hqcount (φ₁ (φ₂ (φ₃ k)))
    rwa [hIconst' k] at h
  have hpowtend : Tendsto (fun k =>
      η (φ₁ (φ₂ (φ₃ k))) ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) * (n : ℝ))
      atTop (nhds (ηs ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) * (n : ℝ))) :=
    ((Real.continuousAt_rpow_const ηs _ (Or.inl hηs_pos.ne')).tendsto.comp
      hηψ).mul_const _
  have hlimcount :
      ηs ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps) * (n : ℝ) ≤ (I₀.card : ℝ) :=
    le_of_tendsto hpowtend (Eventually.of_forall hcount)
  -- Step 9: the limit body sits inside Ω.
  have hLΩ : (L : Set (Fin r → ℝ)) ⊆ Omega :=
    tendsto_convexBody_subset hKψ hcomp.isClosed hΩne hρψ0
      (fun k => hKinf (φ₁ (φ₂ (φ₃ k))))
  -- Step 10: volume bound for the limit body.
  have hvolK : Tendsto (fun k => volume ((K (φ₁ (φ₂ (φ₃ k)))) : Set (Fin r → ℝ)))
      atTop (nhds (volume (L : Set (Fin r → ℝ)))) :=
    External.convexBody_volume_tendsto hKψ
  have hΩvol : Tendsto (fun k => volume (Omega + Metric.closedBall (0 : Fin r → ℝ)
      (1 / ((φ₁ (φ₂ (φ₃ k)) : ℝ) + 1)))) atTop (nhds (volume Omega)) :=
    tendsto_volume_add_closedBall hcomp hconv hΩne (fun k => (hρpos _).le) hρψ0
  have hRHS : Tendsto (fun k => ENNReal.ofReal (η (φ₁ (φ₂ (φ₃ k)))) *
      volume (Omega + Metric.closedBall (0 : Fin r → ℝ)
        (1 / ((φ₁ (φ₂ (φ₃ k)) : ℝ) + 1))))
      atTop (nhds (ENNReal.ofReal ηs * volume Omega)) :=
    ENNReal.Tendsto.mul (ENNReal.tendsto_ofReal hηψ)
      (Or.inr hcomp.measure_lt_top.ne) hΩvol (Or.inr ENNReal.ofReal_ne_top)
  have hvolL : volume (L : Set (Fin r → ℝ)) ≤ ENNReal.ofReal ηs * volume Omega :=
    le_of_tendsto_of_tendsto' hvolK hRHS (fun k => hKvol (φ₁ (φ₂ (φ₃ k))))
  -- Step 11: assemble.
  refine ⟨ηs, (Set.mem_Icc.mp hηsmem).1, (Set.mem_Icc.mp hηsmem).2,
    L, hLΩ, hvolL, ?_⟩
  exact hlimcount.trans (by exact_mod_cast Finset.card_le_card hsubL)

end

end Nondividing
