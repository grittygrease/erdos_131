import Nondividing.Structure
import Nondividing.CapLifting

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# Unshifted preprocessing: failure dichotomy and the single moves (Phase C/G)

Building blocks for `lem:unshifted-preprocessing` (Manuscript.tex 449–745).
The manuscript iteration alternates two "moves" whenever unshifted
`(δ,γ)`-irreducibility *fails* for a stage `(V, B)`:

* a **shrink move** (`small_progression_move`): a witness `D ⊆ V` with
  `|D| ≥ δ|V|` whose fixed progression `P(D)` is small, `|P(D)| < γ|B|`;
  passing through the coefficient identification `φ_{P(D)}` lands the deleted
  set `D̂` in a coordinate box of cardinality `|P(D)| < γ|B|`;
* a **dimension move** (`dimension_move`, `dimension_move_up`): a witness
  whose displayed structural dimension `e = d(D)` differs from the ambient
  dimension; the same identification lands `D̂` in a box of size `≤ C·|B|`
  (all `e`), with the sharper decay `≤ C·s^{ℓ-e}|B|` available for up-moves.

Both moves preserve shell non-dividing exactly (`lem:functional-transform`,
already formalized as `GAP.shell_transport`) and delete at most
`c⁻¹|D|/log|D|` points (the E1 deletion estimate).

This file only *adds* lemmas; it does not modify any existing development.
-/

/-! ## Deliverable 1: the failure dichotomy -/

/-- **Failure dichotomy** for unshifted irreducibility.  Either `(V, M)` is
unshiftedly `(δ,γ)`-irreducible relative to the package, or there is an
eligible witness `D ⊆ V` with `|D| ≥ δ|V|` exhibiting a *dimension defect*
(`d(D) ≠ ℓ`) or a *small progression* (`|P(D)| < γ|box M|`). -/
theorem irreducible_or_witness {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    (δ γ : ℝ) (V : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ) :
    UnshiftedIrreducible pkg δ γ V M ∨
      ∃ D : Finset (Fin ell → ℤ), D ⊆ V ∧ δ * (V.card : ℝ) ≤ (D.card : ℝ) ∧
        ∃ hE : Eligible β pkg.m₀ D M,
          (pkg.out D M hE).e ≠ ell ∨
            ((pkg.out D M hE).P.carrier.card : ℝ) <
              γ * ((coordinateBox M).card : ℝ) := by
  classical
  by_cases h : UnshiftedIrreducible pkg δ γ V M
  · exact Or.inl h
  · right
    unfold UnshiftedIrreducible at h
    push Not at h
    obtain ⟨D, hDV, hcard, hE, hfail⟩ := h
    refine ⟨D, hDV, hcard, hE, ?_⟩
    by_cases he : (pkg.out D M hE).e = ell
    · exact Or.inr (hfail he)
    · exact Or.inl he

end Nondividing
