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

end Nondividing
