import Nondividing.IrredIncrement
import Nondividing.Asymptotic

namespace Nondividing

open Nondividing.External Filter

/-!
# Eventual numerics for the irreducible-stage supplier

The per-stage supplier of `irreducibleIncrement_of_numerics` contains nine
scale/gap thresholds and a scale clause on `δ`-large subsets, all of the
manuscript's "`n ≥ n₀(d, μ, δ, γ)`" type.  This file proves that they hold
for all sufficiently large stage cardinalities `n`, using the asymptotics of
`s(m) = m/(log m)²` from `Asymptotic.lean`:

* `tendsto_structureScale_atTop`, `tendsto_structureScale_pred_atTop`:
  `s(n), s(n-1) → ∞`;
* `eventually_pred_div_log_le`, `eventually_structureScale_pred_le`:
  `c⁻¹(n-1)/log(n-1) ≤ ε·n` and `s(n-1) ≤ ε·n` eventually (the `o(n)` decay
  of the deletion budget and the scale);
* `eventually_sqrt_le_scale_pred`: the filling threshold
  `3√(dn) ≤ c·s(n-1)/2`;
* `eventually_scale_range`: the uniform scale clause on all `m ∈ [δn, n]`;
* `eventually_stage_thresholds`: the full conjunction.
-/

/-- `s(n-1) → ∞` along `n` (via `tendsto_structureScale_atTop` from
`Preprocessing.lean`). -/
theorem tendsto_structureScale_pred_atTop :
    Tendsto (fun n : ℕ => structureScale (n - 1)) atTop atTop :=
  tendsto_structureScale_atTop.comp (tendsto_sub_atTop_nat 1)

/-- The deletion budget is `o(n)`: for any `ε > 0`, eventually
`c⁻¹·(n-1)/log(n-1) ≤ ε·n`. -/
theorem eventually_pred_div_log_le {c ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) ≤ ε * n := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n - 1 : ℕ) : ℝ))
      atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp
      (tendsto_sub_atTop_nat 1)
  filter_upwards [hlog.eventually_ge_atTop (|c⁻¹| / ε),
    hlog.eventually_ge_atTop 1] with n hL h1
  have hLpos : (0 : ℝ) < Real.log ((n - 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le one_pos h1
  have hm_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  have hm0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hLpos]
  have h2 : c⁻¹ ≤ ε * Real.log ((n - 1 : ℕ) : ℝ) := by
    have h3 : |c⁻¹| ≤ ε * Real.log ((n - 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hε] at hL
      calc |c⁻¹| ≤ Real.log ((n - 1 : ℕ) : ℝ) * ε := hL
        _ = ε * Real.log ((n - 1 : ℕ) : ℝ) := mul_comm _ _
    exact le_trans (le_abs_self _) h3
  calc c⁻¹ * ((n - 1 : ℕ) : ℝ)
      ≤ (ε * Real.log ((n - 1 : ℕ) : ℝ)) * (n : ℝ) := by
        refine mul_le_mul h2 hm_le hm0 ?_
        exact mul_nonneg hε.le hLpos.le
    _ = ε * (n : ℝ) * Real.log ((n - 1 : ℕ) : ℝ) := by ring

/-- The GAP scale is `o(n)`: for any `ε > 0`, eventually `s(n-1) ≤ ε·n`. -/
theorem eventually_structureScale_pred_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, structureScale (n - 1) ≤ ε * n := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n - 1 : ℕ) : ℝ))
      atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp
      (tendsto_sub_atTop_nat 1)
  filter_upwards [hlog.eventually_ge_atTop (1 / ε),
    hlog.eventually_ge_atTop 1] with n hL h1
  have hLpos : (0 : ℝ) < Real.log ((n - 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le one_pos h1
  have hL2 : (1 : ℝ) / ε ≤ (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 := by
    calc (1 : ℝ) / ε ≤ Real.log ((n - 1 : ℕ) : ℝ) := hL
      _ ≤ (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hm_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  have hm0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hss : structureScale (n - 1) =
      ((n - 1 : ℕ) : ℝ) / (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 := rfl
  rw [hss, div_le_iff₀ (by positivity)]
  have h1ε : (1 : ℝ) ≤ ε * (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 := by
    rw [div_le_iff₀ hε] at hL2
    linarith [hL2]
  calc ((n - 1 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) * 1 := (mul_one _).symm
    _ ≤ (n : ℝ) * (ε * (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2) := by
        refine mul_le_mul hm_le h1ε one_pos.le (Nat.cast_nonneg _)
    _ = ε * (n : ℝ) * (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 := by ring

/-- The filling threshold: eventually `3·√(d·n) ≤ c·s(n-1)/2`. -/
theorem eventually_sqrt_le_scale_pred {d : ℕ} {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (d * n) * 3 ≤ c * structureScale (n - 1) / 2 := by
  have hengine := eventually_mul_sqrt_le_mul_id_div_log_sq
    (C := 6 * Real.sqrt d) (κ := c / 2) (by positivity)
  have hcomp : ∀ᶠ n : ℕ in atTop,
      6 * Real.sqrt d * Real.sqrt ((n - 1 : ℕ) : ℝ) ≤
        c / 2 * (((n - 1 : ℕ) : ℝ) / (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2) :=
    (tendsto_sub_atTop_nat 1).eventually hengine
  filter_upwards [hcomp, eventually_ge_atTop 2] with n hn hn2
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : 1 ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  -- `√n ≤ 2√(n-1)` for `n ≥ 2`.
  have hsqrtn : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    have h4 : (n : ℝ) ≤ 4 * ((n : ℝ) - 1) := by linarith
    calc Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * ((n : ℝ) - 1)) :=
          Real.sqrt_le_sqrt h4
      _ = 2 * Real.sqrt ((n : ℝ) - 1) := by
          rw [show (4 : ℝ) * ((n : ℝ) - 1) = 2 ^ 2 * ((n : ℝ) - 1) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hsplit : Real.sqrt ((d : ℝ) * n) =
      Real.sqrt d * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul (Nat.cast_nonneg d) _
  have hss : structureScale (n - 1) =
      ((n - 1 : ℕ) : ℝ) / (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 := rfl
  have hsd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  calc Real.sqrt ((d : ℝ) * n) * 3
      = 3 * (Real.sqrt d * Real.sqrt (n : ℝ)) := by rw [hsplit]; ring
    _ ≤ 3 * (Real.sqrt d * (2 * Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hsqrtn hsd0
    _ = 6 * Real.sqrt d * Real.sqrt ((n - 1 : ℕ) : ℝ) := by ring
    _ ≤ c / 2 * (((n - 1 : ℕ) : ℝ) / (Real.log ((n - 1 : ℕ) : ℝ)) ^ 2) := hn
    _ = c * structureScale (n - 1) / 2 := by rw [hss]; ring

/-- The uniform scale clause: eventually, every `m ∈ [δn, n]` has
`s(m) ≥ 1`, `c·s(m) ≥ 1`, and `s(m)·γ > K`. -/
theorem eventually_scale_range {δ γ K c : ℝ} (hδ : 0 < δ) (hγ : 0 < γ)
    (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, δ * n ≤ (m : ℝ) → m ≤ n →
      1 ≤ structureScale m ∧ 1 ≤ c * structureScale m ∧
      K < structureScale m * γ := by
  set B : ℝ := max (max 1 c⁻¹) ((|K| + 1) / γ) with hB_def
  have hLtend : Tendsto (fun n : ℕ => δ * n / (Real.log n) ^ 2)
      atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => δ * ((n : ℝ) / (Real.log n) ^ 2))
        atTop atTop :=
      (tendsto_natCast_div_log_pow_atTop 2).const_mul_atTop hδ
    refine h1.congr fun n => ?_
    ring
  filter_upwards [hLtend.eventually_ge_atTop B,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / δ),
    eventually_ge_atTop 2] with n hL hδn hn2
  intro m hδnm hmn
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hδn2 : (2 : ℝ) ≤ δ * n := by
    rw [div_le_iff₀ hδ] at hδn
    linarith [hδn]
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ (m : ℝ) := le_trans hδn2 hδnm
    exact_mod_cast this
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hlogm : (0 : ℝ) < Real.log m :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlogn : (0 : ℝ) < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hloglog : Real.log m ≤ Real.log n := by
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    exact Real.log_le_log (by linarith) hmnR
  have hsq : (Real.log m) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith
  have hss : structureScale m = (m : ℝ) / (Real.log m) ^ 2 := rfl
  -- `s(m) ≥ δn/(log n)² = L n ≥ B`.
  have hlogm2 : (0 : ℝ) < (Real.log m) ^ 2 := pow_pos hlogm 2
  have hlogn2 : (0 : ℝ) < (Real.log n) ^ 2 := pow_pos hlogn 2
  have hchain : δ * n / (Real.log n) ^ 2 ≤ structureScale m := by
    rw [hss]
    calc δ * n / (Real.log n) ^ 2 ≤ (m : ℝ) / (Real.log n) ^ 2 := by
          rw [div_le_div_iff₀ hlogn2 hlogn2]
          exact mul_le_mul_of_nonneg_right hδnm hlogn2.le
      _ ≤ (m : ℝ) / (Real.log m) ^ 2 := by
          rw [div_le_div_iff₀ hlogn2 hlogm2]
          exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg m)
  have hsB : B ≤ structureScale m := le_trans hL hchain
  have hs1 : 1 ≤ structureScale m :=
    le_trans (le_trans (le_max_left 1 c⁻¹) (le_max_left _ _)) hsB
  refine ⟨hs1, ?_, ?_⟩
  · have hsc : c⁻¹ ≤ structureScale m :=
      le_trans (le_trans (le_max_right 1 c⁻¹) (le_max_left _ _)) hsB
    calc (1 : ℝ) = c * c⁻¹ := by
          rw [mul_inv_cancel₀ (ne_of_gt hc)]
      _ ≤ c * structureScale m :=
          mul_le_mul_of_nonneg_left hsc hc.le
  · have hsK : (|K| + 1) / γ ≤ structureScale m :=
      le_trans (le_max_right _ _) hsB
    have h1 : |K| + 1 ≤ structureScale m * γ := by
      rw [div_le_iff₀ hγ] at hsK
      exact hsK
    calc K ≤ |K| := le_abs_self K
      _ < |K| + 1 := by linarith
      _ ≤ structureScale m * γ := h1

/-- The `6^d` rank threshold from a scale lower bound. -/
theorem six_pow_lt_of_scale_ge {d : ℕ} {c γ S : ℝ} (hc : 0 < c)
    (hγ : 0 < γ) (hS : (6 : ℝ) ^ d / c ^ d / γ + 1 ≤ S) :
    (6 : ℝ) ^ d < c ^ d * (S * γ) := by
  have hcd : (0 : ℝ) < c ^ d := pow_pos hc d
  have h1 : (6 : ℝ) ^ d / c ^ d / γ < S := by linarith
  have h2 : (6 : ℝ) ^ d / c ^ d < S * γ := by
    rw [div_lt_iff₀ hγ] at h1
    exact h1
  calc (6 : ℝ) ^ d = c ^ d * ((6 : ℝ) ^ d / c ^ d) := by field_simp
    _ < c ^ d * (S * γ) := mul_lt_mul_of_pos_left h2 hcd

/-- **Eventual stage thresholds.**  For fixed dimension `d`, package constant
`c`, pipeline constants `cw, K`, and parameters `γ, μ, δ` in the hierarchy
`0 < δ ≤ μ/100`, `0 < μ ≤ 1`, `0 < γ`, every scale/gap threshold of the
per-stage supplier of `irreducibleIncrement_of_numerics` holds for all
sufficiently large stage cardinalities `n`.  This is the manuscript's
"`n ≥ n₀(d, μ, δ, γ)`". -/
theorem eventually_stage_thresholds (d : ℕ) {c cw K γ μ δ : ℝ}
    (hc : 0 < c) (hcw : 0 < cw) (hγ : 0 < γ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hδ0 : 0 < δ) (hδμ : δ ≤ μ / 100) :
    ∀ᶠ n : ℕ in atTop,
      8 ≤ μ * n ∧
      δ * n ≤ (n : ℝ) - 1 ∧
      (∀ m : ℕ, δ * n ≤ (m : ℝ) → m ≤ n →
        1 ≤ structureScale m ∧ 1 ≤ c * structureScale m ∧
        K < structureScale m * γ) ∧
      2 ≤ c * structureScale (n - 1) ∧
      (6 : ℝ) ^ d < c ^ d * (structureScale (n - 1) * γ) ∧
      (6 : ℝ) ^ d < c ^ d * (structureScale n * γ) ∧
      Real.sqrt (d * n) * 3 ≤ c * structureScale (n - 1) / 2 ∧
      (12 / min c 8) ^ d * γ⁻¹ + 1 ≤ μ * n / 8 ∧
      0 < μ * n / 24 - 1 -
        (c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) +
          structureScale (n - 1)) / 2 - 2 * (δ * n) ∧
      (12 / min c 8) ^ d * γ⁻¹ + 1 +
        ((c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) +
          structureScale (n - 1)) / 2 + structureScale (n - 1)) ≤
        cw * γ * (μ * n / 24 - 1 -
          (c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) +
            structureScale (n - 1)) / 2 - 2 * (δ * n)) := by
  set A : ℝ := (12 / min c 8) ^ d * γ⁻¹ + 1 with hA_def
  have hcwγ : (0 : ℝ) < cw * γ := mul_pos hcw hγ
  filter_upwards [
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 / μ),
    eventually_ge_atTop 2,
    eventually_scale_range (K := K) hδ0 hγ hc,
    tendsto_structureScale_pred_atTop.eventually_ge_atTop (2 / c),
    tendsto_structureScale_pred_atTop.eventually_ge_atTop
      ((6 : ℝ) ^ d / c ^ d / γ + 1),
    tendsto_structureScale_atTop.eventually_ge_atTop
      ((6 : ℝ) ^ d / c ^ d / γ + 1),
    eventually_sqrt_le_scale_pred (d := d) hc,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 * A / μ),
    eventually_pred_div_log_le (c := c)
      (show (0 : ℝ) < μ / 2000 by positivity),
    eventually_pred_div_log_le (c := c)
      (show (0 : ℝ) < cw * γ * μ / 2000 by positivity),
    eventually_structureScale_pred_le
      (show (0 : ℝ) < μ / 2000 by positivity),
    eventually_structureScale_pred_le
      (show (0 : ℝ) < cw * γ * μ / 2000 by positivity),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (200 / μ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop
      (1000 * A / (cw * γ * μ))] with n hF1 hF2 hF3 hF4 hF5 hF6 hF7 hF8
      hF9a hF9b hF10a hF10b hF11 hF12
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hF2
  -- (a) `8 ≤ μn`.
  have ha : 8 ≤ μ * n := by
    rw [div_le_iff₀ hμ] at hF1
    linarith
  -- `μn ≥ 200`.
  have hμn200 : 200 ≤ μ * n := by
    rw [div_le_iff₀ hμ] at hF11
    linarith
  -- `δn ≤ μn/100` and `μn ≤ n`.
  have hδn' : δ * n ≤ μ * n / 100 := by
    have h := mul_le_mul_of_nonneg_right hδμ hn0
    linarith
  have hμnn : μ * n ≤ n := by
    have h := mul_le_of_le_one_left hn0 hμ1
    linarith
  -- (b) `δn ≤ n - 1`.
  have hb : δ * n ≤ (n : ℝ) - 1 := by linarith
  -- (c) `2 ≤ c·s(n-1)`.
  have hc2 : 2 ≤ c * structureScale (n - 1) := by
    have h := mul_le_mul_of_nonneg_left hF4 hc.le
    have h2 : c * (2 / c) = 2 := by field_simp
    linarith
  -- gap and εκ preliminaries.
  set R : ℝ := c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ)
    with hR_def
  set S : ℝ := structureScale (n - 1) with hS_def
  -- (i) the gap `G ≥ μn/120 > 0`.
  have hgap120 : μ * n / 120 ≤
      μ * n / 24 - 1 - (R + S) / 2 - 2 * (δ * n) := by
    linarith [hF9a, hF10a]
  have hgap : 0 < μ * n / 24 - 1 - (R + S) / 2 - 2 * (δ * n) := by
    linarith
  -- (g) `A ≤ μn/8`.
  have hidx : A ≤ μ * n / 8 := by
    rw [div_le_iff₀ hμ] at hF8
    linarith
  -- (j) the `εκ` threshold.
  have hεκ : A + ((R + S) / 2 + S) ≤
      cw * γ * (μ * n / 24 - 1 - (R + S) / 2 - 2 * (δ * n)) := by
    have hRHS : cw * γ * (μ * n / 120) ≤
        cw * γ * (μ * n / 24 - 1 - (R + S) / 2 - 2 * (δ * n)) :=
      mul_le_mul_of_nonneg_left hgap120 hcwγ.le
    have hA2 : 1000 * A ≤ (n : ℝ) * (cw * γ * μ) := by
      rw [div_le_iff₀ (by positivity)] at hF12
      linarith
    nlinarith [hF9b, hF10b]
  exact ⟨ha, hb, hF3, hc2,
    six_pow_lt_of_scale_ge hc hγ hF5, six_pow_lt_of_scale_ge hc hγ hF6,
    hF7, hidx, hgap, hεκ⟩

/-- The scale/gap threshold package of the per-stage supplier at stage
cardinality `n` (dimension `d`, package constant `c = (pkgs d).c`, pipeline
constants `cw d`, `K d`). -/
abbrev StageThresholds {β : ℝ} (pkgs : ∀ r, Package r β) (cw K : ℕ → ℝ)
    (d : ℕ) (μ δ γ : ℝ) (n : ℕ) : Prop :=
  8 ≤ μ * n ∧
  δ * n ≤ (n : ℝ) - 1 ∧
  (∀ m : ℕ, δ * n ≤ (m : ℝ) → m ≤ n →
    1 ≤ structureScale m ∧ 1 ≤ (pkgs d).c * structureScale m ∧
    K d < structureScale m * γ) ∧
  2 ≤ (pkgs d).c * structureScale (n - 1) ∧
  (6 : ℝ) ^ d < (pkgs d).c ^ d * (structureScale (n - 1) * γ) ∧
  (6 : ℝ) ^ d < (pkgs d).c ^ d * (structureScale n * γ) ∧
  Real.sqrt (d * n) * 3 ≤ (pkgs d).c * structureScale (n - 1) / 2 ∧
  (12 / min (pkgs d).c 8) ^ d * γ⁻¹ + 1 ≤ μ * n / 8 ∧
  0 < μ * n / 24 - 1 -
    ((pkgs d).c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) +
      structureScale (n - 1)) / 2 - 2 * (δ * n) ∧
  (12 / min (pkgs d).c 8) ^ d * γ⁻¹ + 1 +
    (((pkgs d).c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) +
      structureScale (n - 1)) / 2 + structureScale (n - 1)) ≤
    cw d * γ * (μ * n / 24 - 1 -
      ((pkgs d).c⁻¹ * ((n - 1 : ℕ) : ℝ) / Real.log ((n - 1 : ℕ) : ℝ) +
        structureScale (n - 1)) / 2 - 2 * (δ * n))

/-- The threshold package holds eventually. -/
theorem eventually_stageThresholds {β : ℝ} (pkgs : ∀ r, Package r β)
    (cw K : ℕ → ℝ) (d : ℕ) (hcw : 0 < cw d) {γ μ δ : ℝ}
    (hγ : 0 < γ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hδ0 : 0 < δ)
    (hδμ : δ ≤ μ / 100) :
    ∀ᶠ n : ℕ in atTop, StageThresholds pkgs cw K d μ δ γ n := by
  have h := eventually_stage_thresholds d (c := (pkgs d).c) (cw := cw d)
    (K := K d) (pkgs d).c_pos hcw hγ hμ hμ1 hδ0 hδμ
  filter_upwards [h] with n hn
  exact hn

/-- **`IrreducibleIncrement` from the parameter regime.**  On top of
`irreducibleIncrement_of_numerics`, the nine scale/gap thresholds and the
scale clause on `δ`-large subsets are discharged for `n ≥ n₂(d, μ, δ, γ)`.
The remaining per-stage supplier consists of:

* the parameter regime `0 < δ ≤ min(μ^{1+ε}, μ/100)`, `0 < μ < min(1, μ₀ d)`,
  `0 < γ`;
* the largeness `n ≥ max(n₀(d,μ), n₂(d,μ,δ,γ))`;
* eligibility of `δ`-large subsets (the polynomial box bound `|B| ≤ |W|^β`
  and `m₀ ≤ |W|`, manuscript: the stage's box regime);
* `γ·|B| > 1` (the progression fraction is meaningful);
* the absorption numerics for `η ∈ [μ, μ^{τ_d}]`. -/
theorem irreducibleIncrement_of_regime {β : ℝ}
    (pkgs : ∀ r, Package r β) (eps : ℝ) (heps : 0 < eps) (Dcap : ℕ) :
    ∃ (tau C μ₀ : ℕ → ℝ) (n₀ : ℕ → ℝ → ℕ) (n₂ : ℕ → ℝ → ℝ → ℝ → ℕ),
      (∀ d, 0 < tau d ∧ tau d < 1 ∧ 0 < C d ∧ 0 < μ₀ d) ∧
      ∀ (ζ₀ ε δ γ ν : ℝ) (n₁ : ℕ), 2 ≤ n₁ →
      (∀ (X : ℕ) (s : PrepStage X), 1 ≤ X → n₁ ≤ s.V.card → s.dim ≤ Dcap →
        StageIrreducible pkgs δ γ s →
        ∃ μ : ℝ,
          0 < μ ∧ μ < 1 ∧ μ < μ₀ s.dim ∧
          0 < γ ∧ 0 < δ ∧ δ ≤ μ ^ ((1 : ℝ) + eps) ∧ δ ≤ μ / 100 ∧
          n₀ s.dim μ ≤ s.V.card ∧
          n₂ s.dim μ δ γ ≤ s.V.card ∧
          (∀ W : Finset (Fin s.dim → ℤ), W ⊆ s.V →
            δ * (s.V.card : ℝ) ≤ (W.card : ℝ) →
            Eligible β (pkgs s.dim).m₀ W s.M) ∧
          1 < γ * ((coordinateBox s.M).card : ℝ) ∧
          (∀ η : ℝ, μ ≤ η → η ≤ μ ^ tau s.dim →
            C s.dim * η < 1 ∧
            (C s.dim * η) ^ (sigma s.dim + ζ₀ - ν) ≤
              η ^ (((s.dim : ℝ) - 2) / (s.dim : ℝ) + eps) ∧
            (n₁ : ℝ) ≤ η ^ (((s.dim : ℝ) - 2) / (s.dim : ℝ) + eps) *
              (s.V.card : ℝ))) →
      IrreducibleIncrementCapped pkgs Dcap ζ₀ ε δ γ ν n₁ := by
  classical
  obtain ⟨tau, K, C, μ₀, cw, n₀, hpos, hmain⟩ :=
    irreducibleIncrement_of_numerics (β := β) pkgs eps heps Dcap
  -- Extract the eventual-threshold rank as a function of `(d, μ, δ, γ)`.
  have hev : ∀ (d : ℕ) (μ δ γ : ℝ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < γ → 0 < μ → μ ≤ 1 → 0 < δ → δ ≤ μ / 100 →
      StageThresholds pkgs cw K d μ δ γ n := by
    intro d μ δ γ
    by_cases h : 0 < γ ∧ 0 < μ ∧ μ ≤ 1 ∧ 0 < δ ∧ δ ≤ μ / 100
    · obtain ⟨hγ, hμ, hμ1, hδ0, hδμ⟩ := h
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (eventually_stageThresholds pkgs cw K d
          (hpos d).2.2.2.2.2 hγ hμ hμ1 hδ0 hδμ)
      exact ⟨N, fun n hn _ _ _ _ _ => hN n hn⟩
    · exact ⟨0, fun n _ hγ hμ hμ1 hδ0 hδμ =>
        absurd ⟨hγ, hμ, hμ1, hδ0, hδμ⟩ h⟩
  choose n₂ hn₂ using hev
  refine ⟨tau, C, μ₀, n₀, n₂,
    fun d => ⟨(hpos d).1, (hpos d).2.1, (hpos d).2.2.2.1,
      (hpos d).2.2.2.2.1⟩, ?_⟩
  intro ζ₀ ε δ γ ν n₁ hn₁ hsup
  refine hmain ζ₀ ε δ γ ν n₁ hn₁ ?_
  intro X s hX hn hcap hirr
  obtain ⟨μ, hμ0, hμ1, hμμ₀, hγ, hδ0, hδμe, hδμ100, hn₀le, hn₂le, hElig,
    hγB, habs⟩ := hsup X s hX hn hcap hirr
  have hthr := hn₂ s.dim μ δ γ s.V.card hn₂le hγ hμ0 hμ1.le hδ0 hδμ100
  obtain ⟨h8, hb, hrange, h2cs, h6dp, h6dn, hsqrt, hidx, hgap, hεκ⟩ := hthr
  exact ⟨μ, hμ0, hμ1, hμμ₀, hn₀le, hγ, hδ0.le, hδμe, h8, hb,
    (fun W hWV hWcard =>
      ⟨hElig W hWV hWcard,
        (hrange W.card hWcard (Finset.card_le_card hWV)).1,
        (hrange W.card hWcard (Finset.card_le_card hWV)).2.1,
        (hrange W.card hWcard (Finset.card_le_card hWV)).2.2⟩),
    hγB, h6dn, h2cs, h6dp, hsqrt, hidx, hgap, hεκ, habs⟩

/-- Eligibility of a `δ`-large subset from the stage-level box bound
`|B| ≤ (δn)^β` and the largeness `m₀ ≤ δn`. -/
theorem eligible_of_box_bound {d : ℕ} {β : ℝ} (m₀ : ℕ)
    {V W : Finset (Fin d → ℤ)} {M : Fin d → ℕ} {δ : ℝ}
    (hWV : W ⊆ V) (hVbox : V ⊆ coordinateBox M)
    (hm₀ : (m₀ : ℝ) ≤ δ * V.card)
    (hWcard : δ * V.card ≤ (W.card : ℝ)) (hβ : 0 ≤ β)
    (hbox : ((coordinateBox M).card : ℝ) ≤ (δ * V.card) ^ β) :
    Eligible β m₀ W M := by
  have hδn0 : (0 : ℝ) ≤ δ * V.card := le_trans (Nat.cast_nonneg m₀) hm₀
  refine ⟨?_, hWV.trans hVbox, ?_⟩
  · have h : (m₀ : ℝ) ≤ (W.card : ℝ) := le_trans hm₀ hWcard
    exact_mod_cast h
  · calc ((coordinateBox M).card : ℝ) ≤ (δ * V.card) ^ β := hbox
      _ ≤ (W.card : ℝ) ^ β := Real.rpow_le_rpow hδn0 hWcard hβ

/-- The absorption numerics for all `η ∈ [μ, μ^τ]` from four `μ`-level
inequalities: `C·μ^τ < 1`, the exponent ordering `b ≤ a`, the smallness
`C^a ≤ μ^{τ(b-a)}`, and the two retention bounds at the endpoints. -/
theorem absorption_of_mu_small {C tau a b μ : ℝ} {n₁ n : ℕ}
    (hC : 0 < C) (hτ0 : 0 < tau) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hba : b ≤ a) (hCμ : C * μ ^ tau < 1)
    (hCa : C ^ a ≤ μ ^ (tau * (b - a)))
    (hn₁b : (n₁ : ℝ) ≤ μ ^ b * n)
    (hn₁τb : (n₁ : ℝ) ≤ μ ^ (tau * b) * n) :
    ∀ η : ℝ, μ ≤ η → η ≤ μ ^ tau →
      C * η < 1 ∧ (C * η) ^ a ≤ η ^ b ∧ (n₁ : ℝ) ≤ η ^ b * n := by
  intro η hμη hητ
  have hη0 : 0 < η := lt_of_lt_of_le hμ0 hμη
  have hCη : C * η < 1 := by
    calc C * η ≤ C * μ ^ tau := mul_le_mul_of_nonneg_left hητ hC.le
      _ < 1 := hCμ
  refine ⟨hCη, ?_, ?_⟩
  · -- `(C·η)^a ≤ η^b`.
    have h1 : (C * η) ^ a = C ^ a * η ^ a := Real.mul_rpow hC.le hη0.le
    have h2 : η ^ (b - a) * η ^ a = η ^ b := by
      rw [← Real.rpow_add hη0]
      congr 1
      ring
    have h3 : C ^ a ≤ η ^ (b - a) := by
      have h4 : (μ ^ tau) ^ (b - a) ≤ η ^ (b - a) :=
        Real.rpow_le_rpow_of_nonpos hη0 hητ (by linarith)
      calc C ^ a ≤ μ ^ (tau * (b - a)) := hCa
        _ = (μ ^ tau) ^ (b - a) := Real.rpow_mul hμ0.le _ _
        _ ≤ η ^ (b - a) := h4
    calc (C * η) ^ a = C ^ a * η ^ a := h1
      _ ≤ η ^ (b - a) * η ^ a :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hη0.le a)
      _ = η ^ b := h2
  · -- `n₁ ≤ η^b·n`.
    rcases le_total 0 b with hb | hb
    · have h1 : μ ^ b ≤ η ^ b := Real.rpow_le_rpow hμ0.le hμη hb
      have h2 : μ ^ b * n ≤ η ^ b * n :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
      linarith
    · have h1' : μ ^ (tau * b) ≤ η ^ b := by
        rw [Real.rpow_mul hμ0.le]
        exact Real.rpow_le_rpow_of_nonpos hη0 hητ hb
      have h2 : μ ^ (tau * b) * n ≤ η ^ b * n :=
        mul_le_mul_of_nonneg_right h1' (Nat.cast_nonneg n)
      linarith

/-- **`IrreducibleIncrement` from stage parameters.**  The final reduction:
on top of `irreducibleIncrement_of_regime`, the subset-eligibility clause is
reduced to the stage-level box bound `|B| ≤ (δn)^β` (with `m₀ ≤ δn`), and the
`∀ η ∈ [μ, μ^τ]` absorption clause is reduced to `μ`-level inequalities.  The
remaining supplier is a per-stage choice of `μ` with:

* the regime `0 < δ ≤ min(μ^{1+ε}, μ/100)`, `0 < μ < min(1, μ₀ d)`, `0 < γ`;
* the largeness `n ≥ max(n₀(d,μ), n₂(d,μ,δ,γ))` and `m₀ ≤ δn`;
* the box regime `|B| ≤ (δn)^β` and `γ·|B| > 1`;
* the absorption smallness `C_d·μ^{τ_d} < 1`,
  `C_d^{σ_d+ζ₀-ν} ≤ μ^{τ_d((κ_d+ε)-(σ_d+ζ₀-ν))}`, the exponent ordering
  `κ_d + ε ≤ σ_d + ζ₀ - ν`, and the two retention endpoints
  `n₁ ≤ μ^{κ_d+ε}·n`, `n₁ ≤ μ^{τ_d(κ_d+ε)}·n`. -/
theorem irreducibleIncrement_of_parameters {β : ℝ}
    (pkgs : ∀ r, Package r β) (eps : ℝ) (heps : 0 < eps) (hβ : 0 ≤ β)
    (Dcap : ℕ) :
    ∃ (tau C μ₀ : ℕ → ℝ) (n₀ : ℕ → ℝ → ℕ) (n₂ : ℕ → ℝ → ℝ → ℝ → ℕ),
      (∀ d, 0 < tau d ∧ tau d < 1 ∧ 0 < C d ∧ 0 < μ₀ d) ∧
      ∀ (ζ₀ ε δ γ ν : ℝ) (n₁ : ℕ), 2 ≤ n₁ →
      (∀ (X : ℕ) (s : PrepStage X), 1 ≤ X → n₁ ≤ s.V.card → s.dim ≤ Dcap →
        StageIrreducible pkgs δ γ s →
        ∃ μ : ℝ,
          0 < μ ∧ μ < 1 ∧ μ < μ₀ s.dim ∧
          0 < γ ∧ 0 < δ ∧ δ ≤ μ ^ ((1 : ℝ) + eps) ∧ δ ≤ μ / 100 ∧
          n₀ s.dim μ ≤ s.V.card ∧
          n₂ s.dim μ δ γ ≤ s.V.card ∧
          ((pkgs s.dim).m₀ : ℝ) ≤ δ * s.V.card ∧
          ((coordinateBox s.M).card : ℝ) ≤ (δ * s.V.card) ^ β ∧
          1 < γ * ((coordinateBox s.M).card : ℝ) ∧
          C s.dim * μ ^ tau s.dim < 1 ∧
          C s.dim ^ (sigma s.dim + ζ₀ - ν) ≤
            μ ^ (tau s.dim * ((((s.dim : ℝ) - 2) / s.dim + eps) -
              (sigma s.dim + ζ₀ - ν))) ∧
          ((s.dim : ℝ) - 2) / s.dim + eps ≤ sigma s.dim + ζ₀ - ν ∧
          (n₁ : ℝ) ≤ μ ^ (((s.dim : ℝ) - 2) / s.dim + eps) *
            s.V.card ∧
          (n₁ : ℝ) ≤ μ ^ (tau s.dim * (((s.dim : ℝ) - 2) / s.dim + eps)) *
            s.V.card) →
      IrreducibleIncrementCapped pkgs Dcap ζ₀ ε δ γ ν n₁ := by
  classical
  obtain ⟨tau, C, μ₀, n₀, n₂, hpos, hmain⟩ :=
    irreducibleIncrement_of_regime (β := β) pkgs eps heps Dcap
  refine ⟨tau, C, μ₀, n₀, n₂, hpos, ?_⟩
  intro ζ₀ ε δ γ ν n₁ hn₁ hsup
  refine hmain ζ₀ ε δ γ ν n₁ hn₁ ?_
  intro X s hX hn hcap hirr
  obtain ⟨μ, hμ0, hμ1, hμμ₀, hγ, hδ0, hδμe, hδμ100, hn₀le, hn₂le, hm₀,
    hbox, hγB, hCμ, hCa, hba, hn₁b, hn₁τb⟩ := hsup X s hX hn hcap hirr
  exact ⟨μ, hμ0, hμ1, hμμ₀, hγ, hδ0, hδμe, hδμ100, hn₀le, hn₂le,
    (fun W hWV hWcard =>
      eligible_of_box_bound (pkgs s.dim).m₀ hWV s.subset hm₀ hWcard hβ hbox),
    hγB,
    absorption_of_mu_small (hpos s.dim).2.2.1 (hpos s.dim).1 hμ0 hμ1 hba
      hCμ hCa hn₁b hn₁τb⟩


end Nondividing
