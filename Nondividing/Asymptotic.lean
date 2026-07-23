import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.Order.Field

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

/-- Natural-argument form: `m / (log m)^n → ∞`. -/
theorem tendsto_natCast_div_log_pow_atTop (n : ℕ) :
    Filter.Tendsto (fun m : ℕ => (m : ℝ) / (Real.log m) ^ n)
      Filter.atTop Filter.atTop :=
  (tendsto_id_div_log_pow_atTop n).comp tendsto_natCast_atTop_atTop

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

end Nondividing
