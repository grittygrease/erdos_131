import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Hull
import Nondividing.Geometry.IndexDet

open scoped BigOperators
open MeasureTheory

namespace Nondividing

/-!
# GAP volume argument (Phase F, `lem:index-bound` part 2)

The parallelepiped `M(box)` of a full-rank GAP has Lebesgue volume
`|det M|·2^d·∏Nᵢ = [ℤ^d:L]·2^d·∏Nᵢ`, and it is contained in a fixed dilate of
`B_ℝ`.  Combined with `|P| ≍ 2^d∏Nᵢ` and `|P| ≥ γ|B|` this gives
`[ℤ^d:L] ≪ γ⁻¹`.
-/

/-- The real symmetric coordinate box `∏ᵢ[-Nᵢ, Nᵢ] ⊆ ℝ^d`. -/
def realBox {d : ℕ} (N : Fin d → ℕ) : Set (Fin d → ℝ) :=
  Set.Icc (fun i => -(N i : ℝ)) (fun i => (N i : ℝ))

/-- Volume of the real box: `vol(∏[-Nᵢ,Nᵢ]) = 2^d·∏Nᵢ`. -/
theorem volume_realBox {d : ℕ} (N : Fin d → ℕ) :
    volume (realBox N) = ENNReal.ofReal (2 ^ d * ∏ i, (N i : ℝ)) := by
  rw [realBox, Real.volume_Icc_pi]
  rw [show (∏ i : Fin d, ENNReal.ofReal ((N i : ℝ) - -(N i : ℝ)))
        = ∏ i : Fin d, ENNReal.ofReal (2 * (N i : ℝ)) from by
        refine Finset.prod_congr rfl fun i _ => ?_; ring_nf]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Nondividing
