import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Nondividing.External

def closedUpperHalfspace {r : ℕ}
    (ell : Module.Dual ℝ (Fin r → ℝ)) (t : ℝ) : Set (Fin r → ℝ) :=
  {x | t ≤ ell x}

def SetMuConvexPosition {r : ℕ} (μ : ℝ) (A : Finset (Fin r → ℝ)) : Prop :=
  ∀ p ∈ A, ∃ ell : Module.Dual ℝ (Fin r → ℝ), ∃ t : ℝ,
    p ∈ closedUpperHalfspace ell t ∧
    (((A : Set (Fin r → ℝ)) ∩ closedUpperHalfspace ell t).ncard : ℝ)
      ≤ μ * A.card

/--
Trusted external interface E4.

Source: Pham–Zakharov, Lemma 1.  This interface is only for a `Finset` of
distinct points, exactly as published; indexed multiplicity is absent.
The threshold is allowed to depend on `μ`, matching “sufficiently large in
δ”.  The exponent is `(r-1)/(r+1)+ε`.
-/
axiom convex_density_set
    (r : ℕ) (hr : 1 ≤ r) (eps : ℝ) (heps : 0 < eps) :
    ∃ tau μ₀ : ℝ, 0 < tau ∧ tau < 1 ∧ 0 < μ₀ ∧
      ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∃ n₀ : ℕ,
      ∀ (Omega : Set (Fin r → ℝ)) (A : Finset (Fin r → ℝ)),
        n₀ ≤ A.card →
        IsCompact Omega →
        Convex ℝ Omega →
        (interior Omega).Nonempty →
        (A : Set (Fin r → ℝ)) ⊆ Omega →
        SetMuConvexPosition μ A →
        ∃ eta : ℝ, μ ≤ eta ∧ eta ≤ Real.rpow μ tau ∧
        ∃ Omega' : Set (Fin r → ℝ),
          MeasurableSet Omega' ∧
          Convex ℝ Omega' ∧
          Omega' ⊆ Omega ∧
          MeasureTheory.volume Omega' ≤
            ENNReal.ofReal eta * MeasureTheory.volume Omega ∧
          (eta ^ (((r : ℝ) - 1) / ((r : ℝ) + 1) + eps)) * A.card ≤
            (((A : Set (Fin r → ℝ)) ∩ Omega').ncard : ℝ)

end Nondividing.External
