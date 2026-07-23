import Nondividing.Box
import Nondividing.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace Nondividing.External

def InZonotope {d : ℕ} (A : Finset (Fin d → ℤ)) (z : Fin d → ℝ) : Prop :=
  ∃ t : (Fin d → ℤ) → ℝ,
    (∀ a ∈ A, 0 ≤ t a ∧ t a ≤ 1) ∧
    z = fun i => ∑ a ∈ A, t a * (a i : ℝ)

/--
Trusted external interface E3.

Source: Conlon–Fox–Pham zonotope rounding lemma as used in
Pham–Zakharov, Lemma 13 and equation (15).  `z - sum S` is deliberately
oriented with the same sign as equation (15), and `S` is an actual
`Finset` subset of the distinct input set.
-/
axiom zonotope_rounding
    {d : ℕ} (A : Finset (Fin d → ℤ)) (M : Fin d → ℕ)
    (hA : A ⊆ coordinateBox M) {z : Fin d → ℝ}
    (hz : InZonotope A z) :
    ∃ S : Finset (Fin d → ℤ), S ⊆ A ∧
      ∀ i,
        |z i - ∑ a ∈ S, (a i : ℝ)| ≤
          Real.sqrt (d * (A ∪ {0}).card) * (2 * M i + 1)

end Nondividing.External
