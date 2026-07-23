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

/-- **Numerology inequality at all `ζ ≥ 0`:** `f_{d,e}(ζ) = (σ_e+ζ)(1/(σ_d+ζ) -
(e-d)) ≤ 1`.  Follows from the `ζ = 0` case since `(σ_e+ζ)(σ_d+ζ) ≥ σ_e σ_d`
(monotone in `ζ`), which is the manuscript's `f' < 0` content in packaged form. -/
theorem numerology_le_one_zeta {d e : ℕ} (hd : 1 ≤ d) (hde : d < e)
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    (sigma e + ζ) * (1 / (sigma d + ζ) - ((e : ℝ) - d)) ≤ 1 := by
  have hsd := sigma_pos d
  have hse := sigma_pos e
  have hA : 0 < sigma d + ζ := by linarith
  have hb := numerology_base hd hde
  have hde1 : (1 : ℝ) ≤ (e : ℝ) - d := by
    have : (d : ℝ) + 1 ≤ e := by exact_mod_cast hde
    linarith
  have hprod : sigma e * sigma d ≤ (sigma e + ζ) * (sigma d + ζ) := by
    nlinarith [hζ, hse.le, hsd.le]
  have hmain : sigma e - sigma d ≤ (sigma e + ζ) * (sigma d + ζ) * ((e : ℝ) - d) :=
    hb.trans (mul_le_mul_of_nonneg_right hprod (by linarith))
  rw [← sub_nonneg]
  have hrw : (1 : ℝ) - (sigma e + ζ) * (1 / (sigma d + ζ) - ((e : ℝ) - d))
      = ((sigma d + ζ) - (sigma e + ζ)
          + (sigma e + ζ) * (sigma d + ζ) * ((e : ℝ) - d)) / (sigma d + ζ) := by
    field_simp
    ring
  rw [hrw]
  exact div_nonneg (by linarith [hmain]) hA.le

/-- **Numerology strict gap** (`lem:numerology`, `ε = 0`).  For `ζ ∈ [ζ₀, 1-σ_d]`
with `ζ₀ > 0`, `f_{d,e}(ζ) ≤ 1 - (2/5)·ζ₀` with the *explicit uniform* constant
`c_* = (2/5)ζ₀` — no compactness argument needed, because `ζ ≤ 1-σ_d` forces
`σ_d+ζ ≤ 1`, so the gap `1 - f` (a positive quantity over `σ_d+ζ`) is at least the
numerator, which is `≥ (2/5)ζ₀`. -/
theorem numerology_strict {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) {ζ ζ₀ : ℝ}
    (hζ₀ : 0 < ζ₀) (hζlo : ζ₀ ≤ ζ) (hζhi : ζ ≤ 1 - sigma d) :
    (sigma e + ζ) * (1 / (sigma d + ζ) - ((e : ℝ) - d)) ≤ 1 - 2 / 5 * ζ₀ := by
  have hsd := sigma_pos d
  have hse := sigma_pos e
  have h1 : (1 : ℝ) / 5 ≤ sigma d := one_fifth_le_sigma d
  have h2 : (1 : ℝ) / 5 ≤ sigma e := one_fifth_le_sigma e
  have hζ : (0 : ℝ) ≤ ζ := le_trans hζ₀.le hζlo
  have hA : 0 < sigma d + ζ := by linarith
  have hAle1 : sigma d + ζ ≤ 1 := by linarith
  have hb := numerology_base hd hde
  have hde1 : (1 : ℝ) ≤ (e : ℝ) - d := by
    have : (d : ℝ) + 1 ≤ e := by exact_mod_cast hde
    linarith
  -- numerator `≥ (2/5) ζ₀`
  have hnum : 2 / 5 * ζ₀ ≤
      (sigma d + ζ) - (sigma e + ζ)
        + (sigma e + ζ) * (sigma d + ζ) * ((e : ℝ) - d) := by
    nlinarith [hb, hζlo, hζ₀, hde1, h1, h2, hsd, hse,
      mul_nonneg (mul_nonneg hζ (by linarith : (0:ℝ) ≤ sigma e + sigma d))
        (by linarith : (0:ℝ) ≤ (e:ℝ) - d),
      mul_nonneg (mul_nonneg hζ hζ) (by linarith : (0:ℝ) ≤ (e:ℝ) - d)]
  rw [← sub_nonneg]
  have hrw : (1 - 2 / 5 * ζ₀) - (sigma e + ζ) * (1 / (sigma d + ζ) - ((e : ℝ) - d))
      = (((sigma d + ζ) - (sigma e + ζ)
            + (sigma e + ζ) * (sigma d + ζ) * ((e : ℝ) - d))
          - 2 / 5 * ζ₀ * (sigma d + ζ)) / (sigma d + ζ) := by
    field_simp
    ring
  rw [hrw]
  refine div_nonneg ?_ hA.le
  have hle : 2 / 5 * ζ₀ * (sigma d + ζ) ≤ 2 / 5 * ζ₀ :=
    by nlinarith [hAle1, hζ₀]
  linarith [hnum, hle]

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

/-- **Numerology lemma** (`lem:numerology`, full form).  For `ζ ∈ [ζ₀, 1-σ_d]`
(`ζ₀ > 0`) and `ε ≥ 0` small (`ε·(e-d) ≤ ζ₀/10`), the perturbed functional obeys
`(σ_e+ζ)(1/(σ_d+ζ) - (1-ε)(e-d)) ≤ 1 - (1/5)ζ₀` with the explicit uniform gap
`c_* = (1/5)ζ₀`.  Derived from the `ε = 0` strict gap plus the bound
`(σ_e+ζ)·ε·(e-d) ≤ (1/5)ζ₀`. -/
theorem numerology_strict_eps {d e : ℕ} (hd : 1 ≤ d) (hde : d < e) {ζ ζ₀ ε : ℝ}
    (hζ₀ : 0 < ζ₀) (hζlo : ζ₀ ≤ ζ) (hζhi : ζ ≤ 1 - sigma d) (hε : 0 ≤ ε)
    (hεsmall : ε * ((e : ℝ) - d) ≤ ζ₀ / 10) :
    (sigma e + ζ) * (1 / (sigma d + ζ) - (1 - ε) * ((e : ℝ) - d)) ≤ 1 - 1 / 5 * ζ₀ := by
  have hbase := numerology_strict hd hde hζ₀ hζlo hζhi
  have hse1 := sigma_one_le e
  have h1 : (1 : ℝ) / 5 ≤ sigma d := one_fifth_le_sigma d
  have hde1 : (0 : ℝ) ≤ (e : ℝ) - d := by
    have : (d : ℝ) + 1 ≤ e := by exact_mod_cast hde
    linarith
  have hbnd : sigma e + ζ ≤ 2 := by linarith
  have hexp : (sigma e + ζ) * (1 / (sigma d + ζ) - (1 - ε) * ((e : ℝ) - d))
      = (sigma e + ζ) * (1 / (sigma d + ζ) - ((e : ℝ) - d))
        + (sigma e + ζ) * (ε * ((e : ℝ) - d)) := by ring
  rw [hexp]
  have hincr : (sigma e + ζ) * (ε * ((e : ℝ) - d)) ≤ 1 / 5 * ζ₀ := by
    calc (sigma e + ζ) * (ε * ((e : ℝ) - d))
        ≤ 2 * (ζ₀ / 10) :=
          mul_le_mul hbnd hεsmall (mul_nonneg hε hde1) (by norm_num)
      _ = 1 / 5 * ζ₀ := by ring
  linarith [hbase, hincr]

/-- **The numerology lemma** (`lem:numerology`), exact packaged form.  Fixing the
dimension bound `D ≥ 2` and `ζ₀ > 0`, there are explicit `ε₀, c_* > 0` such that
for all `1 ≤ d < e ≤ D`, `ζ ∈ [ζ₀, 1-σ_d]`, `0 < ε < ε₀`, the perturbed
numerology functional is `≤ 1 - c_*`.  The constants are `ε₀ = ζ₀/(10D)`,
`c_* = ζ₀/5` — no compactness/continuity argument required. -/
theorem numerology {D : ℕ} (hD : 2 ≤ D) {ζ₀ : ℝ} (hζ₀ : 0 < ζ₀) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
      ∀ (d e : ℕ), 1 ≤ d → d < e → e ≤ D →
        ∀ ζ : ℝ, ζ₀ ≤ ζ → ζ ≤ 1 - sigma d →
          ∀ ε : ℝ, 0 < ε → ε < ε₀ →
            (sigma e + ζ) * (1 / (sigma d + ζ) - (1 - ε) * ((e : ℝ) - d))
              ≤ 1 - c := by
  have hDR : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by omega
    exact_mod_cast this
  refine ⟨ζ₀ / (10 * D), 1 / 5 * ζ₀, by positivity, by positivity, ?_⟩
  intro d e hd hde heD ζ hζlo hζhi ε hεpos hεlt
  refine numerology_strict_eps hd hde hζ₀ hζlo hζhi hεpos.le ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heDR : (e : ℝ) ≤ D := by exact_mod_cast heD
  have hedD : (e : ℝ) - d ≤ D := by linarith
  have hed0 : (0 : ℝ) ≤ (e : ℝ) - d := by
    have : (d : ℝ) + 1 ≤ e := by exact_mod_cast hde
    linarith
  calc ε * ((e : ℝ) - d) ≤ (ζ₀ / (10 * D)) * D :=
        mul_le_mul hεlt.le hedD hed0 (by positivity)
    _ = ζ₀ / 10 := by field_simp

end Nondividing
