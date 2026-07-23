import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Nondividing

/-- `x / (log x)^n → ∞`: a logarithmic power is negligible against the identity.
This is the analytic engine behind every `s(C) = m/(log m)^2 → ∞` threshold in
the manuscript. -/
theorem tendsto_id_div_log_pow_atTop (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => x / (Real.log x) ^ n) Filter.atTop Filter.atTop := by
  have hlit : (fun x : ℝ => (Real.log x) ^ n) =o[Filter.atTop] (id : ℝ → ℝ) :=
    Real.isLittleO_pow_log_id_atTop
  have h0 : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ n / x) Filter.atTop (nhds 0) := by
    simpa [id] using hlit.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ n / x ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    exact div_pos (pow_pos hlogpos n) (by linarith)
  have hnhds : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ n / x) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 hpos
  have hinv := hnhds.inv_tendsto_nhdsGT_zero
  refine hinv.congr ?_
  intro x
  simp only [Pi.inv_apply, inv_div]

/-- Log absorption: for any `δ > 0`, eventually `1 + log x ≤ x^δ`.  The Phase H
upper-bound assembly uses this to absorb the `1 + log₂ N` dyadic-shell loss into
the exponent. -/
theorem eventually_one_add_log_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop, 1 + Real.log x ≤ x ^ δ := by
  have hlit : Real.log =o[Filter.atTop] fun x => x ^ δ :=
    isLittleO_log_rpow_atTop hδ
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ (1 / 2) * ‖x ^ δ‖ :=
    hlit.def (by norm_num)
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ δ :=
    (tendsto_rpow_atTop hδ).eventually_ge_atTop 2
  filter_upwards [h1, h2, Filter.eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx3
  have hlogpos : 0 ≤ Real.log x := Real.log_nonneg hx3
  have hxδpos : 0 ≤ x ^ δ := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogpos,
    abs_of_nonneg hxδpos] at hx1
  linarith

/-- Dyadic-log absorption: for any `δ > 0`, eventually `Nat.log 2 N + 1 ≤ N^δ`.
The exact form the Phase H upper-bound assembly needs to absorb the
`(⌊log₂ N⌋ + 1)` dyadic-shell factor into the exponent. -/
theorem eventually_natLog_succ_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, ((Nat.log 2 N : ℝ) + 1) ≤ (N : ℝ) ^ δ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlit : Real.log =o[Filter.atTop] fun x : ℝ => x ^ δ :=
    isLittleO_log_rpow_atTop hδ
  have h1 : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x‖ ≤ (Real.log 2 / 2) * ‖x ^ δ‖ := hlit.def (by positivity)
  have h1' : ∀ᶠ N : ℕ in Filter.atTop,
      ‖Real.log (N : ℝ)‖ ≤ (Real.log 2 / 2) * ‖(N : ℝ) ^ δ‖ :=
    tendsto_natCast_atTop_atTop.eventually h1
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, (2 : ℝ) ≤ (N : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hNlog : ∀ᶠ N : ℕ in Filter.atTop,
      (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : N ≠ 0 := by omega
    have hple : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
    have hle : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log (N : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hple
    rw [Real.log_pow] at hle
    rw [le_div_iff₀ hlog2]
    linarith
  filter_upwards [h1', h2, hNlog, Filter.eventually_ge_atTop 1] with N hN1 hN2 hN3 hN4
  have hlogNnn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN4)
  have hNδnn : 0 ≤ (N : ℝ) ^ δ := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogNnn,
    abs_of_nonneg hNδnn] at hN1
  have hstep : Real.log (N : ℝ) / Real.log 2 ≤ (N : ℝ) ^ δ / 2 := by
    rw [div_le_iff₀ hlog2]
    nlinarith [hN1]
  linarith

/-- Natural-argument form: `m / (log m)^n → ∞`. -/
theorem tendsto_natCast_div_log_pow_atTop (n : ℕ) :
    Filter.Tendsto (fun m : ℕ => (m : ℝ) / (Real.log m) ^ n)
      Filter.atTop Filter.atTop :=
  (tendsto_id_div_log_pow_atTop n).comp tendsto_natCast_atTop_atTop

/-- `√m / (log m)^2 → ∞`: the growth needed so that the rounding error `C√|C|`
is eventually dominated by the GAP scale `s(C) = |C|/(log|C|)^2`.  Obtained as
`√(m / (log m)^4)`. -/
theorem tendsto_sqrt_natCast_div_log_sq :
    Filter.Tendsto (fun m : ℕ => Real.sqrt m / (Real.log m) ^ 2)
      Filter.atTop Filter.atTop := by
  have hsqrt : Filter.Tendsto
      (fun m : ℕ => Real.sqrt ((m : ℝ) / (Real.log m) ^ 4)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_div_log_pow_atTop 4)
  refine hsqrt.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m _
  rw [Real.sqrt_div (Nat.cast_nonneg m),
    show (Real.log m) ^ 4 = ((Real.log m) ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _)]

/-- Rounding-error absorption: for any `C` and any `κ > 0`, eventually
`C·√m ≤ κ·(m/(log m)^2)`.  In `lem:one-sided-filling` this gives
`C_d√|C| ≤ (c/2)·s(C)` for large `|C|`. -/
theorem eventually_mul_sqrt_le_mul_id_div_log_sq {C κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ m : ℕ in Filter.atTop,
      C * Real.sqrt m ≤ κ * ((m : ℝ) / (Real.log m) ^ 2) := by
  have hge : ∀ᶠ m : ℕ in Filter.atTop,
      C / κ ≤ Real.sqrt m / (Real.log m) ^ 2 :=
    tendsto_sqrt_natCast_div_log_sq.eventually_ge_atTop (C / κ)
  filter_upwards [hge, Filter.eventually_ge_atTop 2] with m hm hm2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsqrtpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hlogpos : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm2)
  have hLpos : 0 < (Real.log m) ^ 2 := by positivity
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (le_of_lt hmpos)
  rw [div_le_div_iff₀ hκ hLpos] at hm
  rw [show κ * ((m : ℝ) / (Real.log m) ^ 2) = κ * m / (Real.log m) ^ 2 from
      (mul_div_assoc κ _ _).symm, le_div_iff₀ hLpos]
  nlinarith [mul_le_mul_of_nonneg_right hm (le_of_lt hsqrtpos), hsq, hsqrtpos]

theorem eventually_const_mul_rpow_le_rpow_nat
    {a b c : ℝ} (hab : a < b) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      c * Real.rpow (n : ℝ) a ≤ Real.rpow (n : ℝ) b := by
  have ht :
      Filter.Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (b - a))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp
      tendsto_natCast_atTop_atTop
  have hC :
      ∀ᶠ n : ℕ in Filter.atTop, c ≤ Real.rpow (n : ℝ) (b - a) :=
    (Filter.tendsto_atTop.1 ht c)
  have hpos :
      ∀ᶠ n : ℕ in Filter.atTop, (0 : ℝ) < n := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  filter_upwards [hC, hpos] with n hn hn0
  calc
    c * Real.rpow (n : ℝ) a
        ≤ Real.rpow (n : ℝ) (b - a) * Real.rpow (n : ℝ) a :=
      mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hn0.le a)
    _ = Real.rpow (n : ℝ) ((b - a) + a) :=
      (Real.rpow_add hn0 (b - a) a).symm
    _ = Real.rpow (n : ℝ) b := by ring_nf

/-- Squeeze from two-sided `rpow` bounds to a logarithmic-ratio limit.  If a
positive function `f` is eventually sandwiched between `N^{σ-ε}` and `N^{σ+ε}`
for every `ε > 0`, then `log (f N) / log N → σ`.  This is the final step
combining the two epsilon bounds into `main_log_limit`. -/
theorem tendsto_log_div_log_of_rpow_bounds {f : ℕ → ℝ} {σ : ℝ}
    (hpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < f N)
    (hlb : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in Filter.atTop, Real.rpow (N : ℝ) (σ - ε) ≤ f N)
    (hub : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in Filter.atTop, f N ≤ Real.rpow (N : ℝ) (σ + ε)) :
    Filter.Tendsto (fun N : ℕ => Real.log (f N) / Real.log N)
      Filter.atTop (nhds σ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have H : ∀ᶠ N : ℕ in Filter.atTop,
      0 < f N ∧ 2 ≤ N ∧ Real.rpow (N : ℝ) (σ - ε / 2) ≤ f N ∧
        f N ≤ Real.rpow (N : ℝ) (σ + ε / 2) := by
    filter_upwards [hpos, Filter.eventually_ge_atTop 2, hlb (ε / 2) hε2,
      hub (ε / 2) hε2] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  rw [Filter.eventually_atTop] at H
  obtain ⟨N₀, hN₀⟩ := H
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hfpos, hN2, hlbf, hubf⟩ := hN₀ N hN
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  set L := Real.log (f N) with hL
  -- Lower and upper log bounds.
  have hlb2 : (σ - ε / 2) * Real.log (N : ℝ) ≤ L := by
    rw [← Real.log_rpow hN0 (σ - ε / 2)]
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hN0 _) hfpos).mpr hlbf
  have hub2 : L ≤ (σ + ε / 2) * Real.log (N : ℝ) := by
    rw [← Real.log_rpow hN0 (σ + ε / 2)]
    exact (Real.log_le_log_iff hfpos (Real.rpow_pos_of_pos hN0 _)).mpr hubf
  -- Divide by `log N > 0` and bound the distance.
  have hlow : σ - ε / 2 ≤ L / Real.log (N : ℝ) :=
    (le_div_iff₀ hlogN).mpr hlb2
  have hhigh : L / Real.log (N : ℝ) ≤ σ + ε / 2 :=
    (div_le_iff₀ hlogN).mpr hub2
  rw [Real.dist_eq]
  have : |L / Real.log (N : ℝ) - σ| ≤ ε / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith [this]

end Nondividing
