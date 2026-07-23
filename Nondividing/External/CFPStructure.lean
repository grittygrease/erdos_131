import Nondividing.GAP
import Nondividing.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Nondividing.External

/-- `s(C)=|C|/(log |C|)^2`, kept real so GAP dilation uses the manuscript's
floor convention. -/
noncomputable def structureScale (m : ℕ) : ℝ :=
  m / (Real.log m) ^ 2

/--
Trusted external interface E1.

Source: Conlon–Fox–Pham, homogeneous subset-sum structure theorem, in the
higher-dimensional form recorded by Pham–Zakharov, Corollary 5.  The fields
below correspond respectively to their large subset `Ĉ`, homogeneous
symmetric GAP `P(C)`, core `C₀`, translate `q`, core subset-sum inclusion,
and properness of `c s(C) P(C)`.  No preprocessing or later manuscript
consequence is included.
-/
axiom cfp_structure
    (ell : ℕ) (beta : ℝ) (hbeta : 1 < beta) :
    ∃ c : ℝ, 0 < c ∧ ∃ D m₀ : ℕ,
      ∀ (C : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ),
        m₀ ≤ C.card →
        C ⊆ coordinateBox M →
        ((coordinateBox M).card : ℝ) ≤
          Real.rpow (C.card : ℝ) beta →
        ∃ Chat : Finset (Fin ell → ℤ),
          Chat ⊆ C ∧
          ((C \ Chat).card : ℝ) ≤
            c⁻¹ * C.card / Real.log C.card ∧
        ∃ e : ℕ, e ≤ D ∧ ∃ P : GAP ell e,
          Chat ∪ {0} ⊆ P.carrier ∧
        ∃ C₀ : Finset (Fin ell → ℤ),
          C₀ ⊆ Chat ∧
          (C₀.card : ℝ) ≤ structureScale C.card ∧
        ∃ q : Fin ell → ℤ,
          q ∈ P.dilatedCarrier (structureScale C.card) ∧
          (∀ z ∈ P.dilatedCarrier (c * structureScale C.card),
            q + z ∈ subsetSums C₀) ∧
          Set.InjOn P.evalHom
            (P.dilatedCoeffBox (c * structureScale C.card) : Set (Fin e → ℤ))

end Nondividing.External
