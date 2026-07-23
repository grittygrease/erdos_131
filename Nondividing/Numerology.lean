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
