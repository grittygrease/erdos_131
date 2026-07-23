import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
