import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

namespace Nondividing

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
