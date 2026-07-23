import Nondividing.LowerBound
import Nondividing.Shell
import Nondividing.Preprocessing
import Nondividing.Geometry.LatticeIndex
import Nondividing.Geometry.ConvexLatticeJohn
import Nondividing.Projective.Normalization
import Nondividing.Projective.Convexity
import Nondividing.Projective.Separation
import Nondividing.Projective.AffineSpan
import Nondividing.Geometry.CoordProjection
import Nondividing.Geometry.IndexDet
import Nondividing.Geometry.GAPVolume
import Nondividing.Geometry.SlabVolume
import Nondividing.Geometry.Zonotope
import Nondividing.Geometry.RobustZonotope
import Nondividing.ProjectiveConvexity
import Nondividing.Numerology
import Nondividing.QuotientOrder
import Nondividing.Filling
import Nondividing.Structure
import Nondividing.DyadicShell

namespace Nondividing

/-- Endgame reduction: the logarithmic limit `log (F N)/log N → 1/5` follows from
the upper epsilon bound alone, since the lower epsilon bound (`main_lower_eps`)
and eventual positivity (`one_le_F`) are already established.  Once
`main_upper_eps` is proved from the projective theorem, `main_log_limit` is
immediate by `main_log_limit_of_upper main_upper_eps`. -/
theorem main_log_limit_of_upper
    (hub : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (F N : ℝ) ≤ Real.rpow (N : ℝ) ((1 : ℝ) / 5 + ε)) :
    Filter.Tendsto (fun N : ℕ => Real.log (F N) / Real.log N)
      Filter.atTop (nhds ((1 : ℝ) / 5)) := by
  refine tendsto_log_div_log_of_rpow_bounds ?_ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have : (1 : ℕ) ≤ F N := one_le_F hN
    exact_mod_cast this
  · intro ε hε
    obtain ⟨N₀, h⟩ := main_lower_eps ε hε
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN using h N hN
  · intro ε hε
    obtain ⟨N₀, h⟩ := hub ε hε
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN using h N hN

/-- **Phase H capstone**: the upper epsilon bound `F N ≤ N^{1/5+ε}` follows from
the `d = 1` projective theorem alone.  Given the projective bound
`|W| ≤ X^{1/5+ε/2}` for dense shells `W ⊆ [X, 2X]` (density `X ≤ |W|^5`), the
dyadic-shell reduction `F N ≤ (⌊log₂N⌋+1)·|W|` yields the claim: sparse shells
give `|W| ≤ X^{1/5}` directly, and the `⌊log₂N⌋+1` factor is absorbed into the
exponent via `eventually_natLog_succ_le_rpow`.  This reduces the entire main
theorem (`main_log_limit`) to the projective theorem. -/
theorem main_upper_eps_of_projective
    (hproj : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ (X : ℕ) (W : Finset ℕ),
      X₀ ≤ X → (∀ a ∈ W, X ≤ a ∧ a ≤ 2 * X) →
      ShellNonDividing (fun a : ℕ => (a : ℤ)) X W →
      (X : ℝ) ≤ (W.card : ℝ) ^ 5 →
      (W.card : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (F N : ℝ) ≤ Real.rpow (N : ℝ) ((1 : ℝ) / 5 + ε) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨X₀, hX₀⟩ := hproj (ε / 2) hε2
  have hlog := eventually_natLog_succ_le_rpow (δ := ε / 2) hε2
  have hX₀N : ∀ᶠ N : ℕ in Filter.atTop, (X₀ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 5) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  suffices h : ∀ᶠ N : ℕ in Filter.atTop,
      (F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 5 + ε) by
    rw [Filter.eventually_atTop] at h
    obtain ⟨N₀, hN₀⟩ := h
    exact ⟨N₀, fun N hN => hN₀ N hN⟩
  filter_upwards [hlog, hX₀N, Filter.eventually_ge_atTop 1]
    with N hlogN hX₀le hN1
  obtain ⟨j, W, hWmem, hWle, hWshell, hFN⟩ := exists_shell_reduction N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hXpos : (1 : ℝ) ≤ (2 ^ j : ℕ) := by exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
  -- Key bound: `|W| ≤ N^{1/5+ε/2}`.
  have hkey : (W.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) := by
    rcases Nat.eq_zero_or_pos W.card with hc | hc
    · rw [hc, Nat.cast_zero]; positivity
    · obtain ⟨a, haW⟩ := Finset.card_pos.mp hc
      have hXa : 2 ^ j ≤ a := (Finset.mem_Ico.mp (hWmem a haW)).1
      have hXN : (2 ^ j : ℕ) ≤ N := le_trans hXa (hWle a haW)
      have hXR : ((2 ^ j : ℕ) : ℝ) ≤ N := by exact_mod_cast hXN
      have hshellW : ∀ b ∈ W, 2 ^ j ≤ b ∧ b ≤ 2 * 2 ^ j := by
        intro b hb
        have hbico := Finset.mem_Ico.mp (hWmem b hb)
        refine ⟨hbico.1, ?_⟩
        have hlt : b < 2 ^ (j + 1) := hbico.2
        rw [pow_succ] at hlt; omega
      have hcardX : W.card ≤ 2 ^ j := by
        calc W.card ≤ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card :=
              Finset.card_le_card hWmem
          _ = 2 ^ j := by rw [Nat.card_Ico, pow_succ]; omega
      by_cases hXX0 : X₀ ≤ 2 ^ j
      · by_cases hdens : ((2 ^ j : ℕ) : ℝ) ≤ (W.card : ℝ) ^ 5
        · calc (W.card : ℝ)
                ≤ ((2 ^ j : ℕ) : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
                  hX₀ (2 ^ j) W hXX0 hshellW hWshell hdens
            _ ≤ (N : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
                  Real.rpow_le_rpow (by positivity) hXR (by linarith)
        · push_neg at hdens
          have hcc : ((W.card : ℝ) ^ 5) ^ ((1 : ℝ) / 5) = (W.card : ℝ) := by
            rw [show ((1 : ℝ) / 5) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
            exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
          have hcle : (W.card : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ ((1 : ℝ) / 5) := by
            rw [← hcc]
            exact Real.rpow_le_rpow (by positivity) (le_of_lt hdens) (by norm_num)
          calc (W.card : ℝ)
                ≤ ((2 ^ j : ℕ) : ℝ) ^ ((1 : ℝ) / 5) := hcle
            _ ≤ ((2 ^ j : ℕ) : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
                  Real.rpow_le_rpow_of_exponent_le hXpos (by linarith)
            _ ≤ (N : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
                  Real.rpow_le_rpow (by positivity) hXR (by linarith)
      · push_neg at hXX0
        have hcX0 : (W.card : ℝ) < X₀ := by
          have : W.card < X₀ := lt_of_le_of_lt hcardX hXX0
          exact_mod_cast this
        calc (W.card : ℝ)
              ≤ (X₀ : ℝ) := le_of_lt hcX0
          _ ≤ (N : ℝ) ^ ((1 : ℝ) / 5) := hX₀le
          _ ≤ (N : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
  -- Combine with the dyadic-shell reduction and absorb the log factor.
  have hFNR : (F N : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) * (W.card : ℝ) := by
    exact_mod_cast hFN
  calc (F N : ℝ)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (W.card : ℝ) := hFNR
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
          mul_le_mul hlogN hkey (by positivity) (by positivity)
    _ = (N : ℝ) ^ ((1 : ℝ) / 5 + ε) := by
          rw [← Real.rpow_add hN0]; congr 1; ring

end Nondividing
