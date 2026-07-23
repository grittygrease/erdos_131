import Nondividing.LowerBound
import Nondividing.Shell
import Nondividing.Preprocessing
import Nondividing.Geometry.LatticeIndex
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

end Nondividing
