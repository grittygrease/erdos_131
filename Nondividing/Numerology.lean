import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases

namespace Nondividing

/-!
# Numerology exponents (Phase G)

The projective theorem is stated with the dimension-indexed exponents
`σ₁ = 1/5`, `σ₂ = 1/4`, and `σ_d = (d-2)/d` for `d ≥ 3`.  Here we fix this data
and record its concrete values and elementary bounds.  The `numerology` lemma
itself — that these are the minima of the relevant optimisation over the finite
dimension range — is separate.
-/

/-- The numerology exponent `σ_d`. -/
noncomputable def sigma (d : ℕ) : ℝ :=
  if d ≤ 1 then 1 / 5 else if d = 2 then 1 / 4 else ((d : ℝ) - 2) / d

@[simp] theorem sigma_one : sigma 1 = 1 / 5 := by simp [sigma]

@[simp] theorem sigma_two : sigma 2 = 1 / 4 := by norm_num [sigma]

theorem sigma_ge_three {d : ℕ} (hd : 3 ≤ d) : sigma d = ((d : ℝ) - 2) / d := by
  have h1 : ¬ d ≤ 1 := by omega
  have h2 : d ≠ 2 := by omega
  simp [sigma, h1, h2]

theorem sigma_three : sigma 3 = 1 / 3 := by
  rw [sigma_ge_three (le_refl 3)]; norm_num

/-- Every numerology exponent is at least `1/5` (the extremal value `σ₁`). -/
theorem one_fifth_le_sigma (d : ℕ) : 1 / 5 ≤ sigma d := by
  unfold sigma
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · have hd3 : 3 ≤ d := by omega
    have hd : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
    rw [le_div_iff₀ (by linarith)]
    linarith

theorem sigma_pos (d : ℕ) : 0 < sigma d :=
  lt_of_lt_of_le (by norm_num) (one_fifth_le_sigma d)

/-- Consecutive step: `σ_d < σ_{d+1}` for `d ≥ 1`. -/
theorem sigma_lt_sigma_succ {d : ℕ} (hd : 1 ≤ d) : sigma d < sigma (d + 1) := by
  match d, hd with
  | 1, _ => rw [sigma_one, sigma_two]; norm_num
  | 2, _ => rw [sigma_two, sigma_three]; norm_num
  | (n + 3), _ =>
    rw [sigma_ge_three (by omega), sigma_ge_three (by omega)]
    have h1 : (0 : ℝ) < (↑(n + 3) : ℝ) := by positivity
    have h2 : (0 : ℝ) < (↑(n + 3 + 1) : ℝ) := by positivity
    rw [div_lt_div_iff₀ h1 h2]
    push_cast
    nlinarith

/-- `σ` is strictly increasing on `{d ≥ 1}` (so `σ_d < σ_e` for `1 ≤ d < e`),
the monotonicity feeding the `numerology` optimisation's `f' < 0` step. -/
theorem sigma_lt_sigma {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) : sigma d < sigma e := by
  induction e with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hde with h | h
    · exact (ih h).trans (sigma_lt_sigma_succ (by omega))
    · subst h; exact sigma_lt_sigma_succ hd

/-- **Numerology base inequality** (`lem:numerology` at `ζ = 0`, equivalent form).
`σ_e - σ_d ≤ σ_e·σ_d·(e-d)` for `1 ≤ d < e`.  Equivalent to `f_{d,e}(0) ≤ 1`, this
reduces to the clean quadratic facts `2 ≤ (d-2)(e-2)` (d,e ≥ 3) and
`(e-3)(e-4) ≥ 0` (small `d`). -/
theorem numerology_base {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) :
    sigma e - sigma d ≤ sigma e * sigma d * ((e : ℝ) - d) := by
  have hdeR : (d : ℝ) + 1 ≤ e := by exact_mod_cast hde
  rcases Nat.lt_or_ge d 3 with hd2 | hd3
  · -- d ∈ {1, 2}: handle small e explicitly, general e ≥ 5 by the quadratic
    rcases Nat.lt_or_ge e 5 with he5 | he5
    · interval_cases d <;> interval_cases e <;>
        simp only [sigma_one, sigma_two, sigma_three,
          sigma_ge_three (show 3 ≤ 4 by norm_num)] <;> push_cast <;> norm_num
    · have he0 : (0 : ℝ) < e := by positivity
      have heR : (5 : ℝ) ≤ e := by exact_mod_cast he5
      have hquad : (0 : ℝ) ≤ ((e : ℝ) - 3) * ((e : ℝ) - 4) :=
        mul_nonneg (by linarith) (by linarith)
      interval_cases d
      · rw [sigma_one, sigma_ge_three (by omega),
          div_sub_div _ _ (ne_of_gt he0) (by norm_num), div_mul_div_comm,
          div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        push_cast
        nlinarith [heR, hquad]
      · rw [sigma_two, sigma_ge_three (by omega),
          div_sub_div _ _ (ne_of_gt he0) (by norm_num), div_mul_div_comm,
          div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        push_cast
        nlinarith [heR, hquad]
  · -- d ≥ 3: reduces to `2 ≤ (d-2)(e-2)`
    have he3 : 3 ≤ e := by omega
    have hd0 : (0 : ℝ) < d := by positivity
    have he0 : (0 : ℝ) < e := by positivity
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    have hkey : (0 : ℝ) ≤ ((e : ℝ) - 2) * ((d : ℝ) - 2) - 2 := by
      nlinarith [hdeR, hdR,
        mul_nonneg (show (0:ℝ) ≤ (e:ℝ) - d - 1 by linarith)
          (show (0:ℝ) ≤ (d:ℝ) - 2 by linarith),
        mul_nonneg (show (0:ℝ) ≤ (d:ℝ) by linarith)
          (show (0:ℝ) ≤ (d:ℝ) - 3 by linarith)]
    rw [sigma_ge_three hd3, sigma_ge_three he3,
      div_sub_div _ _ (ne_of_gt he0) (ne_of_gt hd0), div_mul_div_comm,
      div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [hkey, mul_nonneg (show (0:ℝ) ≤ (e:ℝ) - d by linarith) hkey]

/-- Manuscript form of the base inequality: `f_{d,e}(0) = σ_e·(1/σ_d - (e-d)) ≤ 1`
for `1 ≤ d < e`. -/
theorem numerology_le_one {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) :
    sigma e * (1 / sigma d - ((e : ℝ) - d)) ≤ 1 := by
  have hsd := sigma_pos d
  have hb := numerology_base hd hde
  rw [← sub_nonneg]
  have hrw : (1 : ℝ) - sigma e * (1 / sigma d - ((e : ℝ) - d))
      = (sigma d - sigma e + sigma e * sigma d * ((e : ℝ) - d)) / sigma d := by
    field_simp
    ring
  rw [hrw]
  exact div_nonneg (by linarith [hb]) hsd.le

/-- Every numerology exponent is nonnegative. -/
theorem sigma_nonneg (d : ℕ) : 0 ≤ sigma d := by
  unfold sigma
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · have : 2 ≤ d := by omega
    have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
    apply div_nonneg <;> [linarith; positivity]

/-- Every numerology exponent is strictly below `1/2` (they are `< 1/2` for
`d ≤ 4`, and equal `(d-2)/d < 1/2` iff `d < 4`; for the manuscript's range the
extremal value is `σ₁ = 1/5`). -/
theorem sigma_one_le (d : ℕ) : sigma d < 1 := by
  unfold sigma
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · have hd : (2 : ℝ) ≤ (d : ℝ) := by
      have : 2 ≤ d := by omega
      exact_mod_cast this
    rw [div_lt_one (by linarith)]
    linarith

end Nondividing
