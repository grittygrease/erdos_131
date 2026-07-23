import Nondividing.GAP
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace Nondividing

/-!
# Structural preprocessing (Phase C)

This file collects the arithmetic building blocks used in the manuscript's
progression-comparison and unshifted-preprocessing arguments.  We begin with the
elementary cardinality estimate for a real dilation of a symmetric coordinate
box, which underlies the `e > r` counting chain in
`lem:progression-comparison`:
`|sQ| ≪_r s^r |Q|` for a coordinate GAP `Q` of rank `r` and dilation `s ≥ 1`.
-/

/-- Per-factor bound for a real dilation of a coordinate interval: when the
dilation `t` is at least one, the dilated interval radius grows by a factor at
most `t`. -/
theorem two_floor_mul_add_one_le {N : ℕ} {t : ℝ} (ht : 1 ≤ t) :
    (2 * (⌊t * (N : ℝ)⌋₊ : ℝ) + 1) ≤ t * (2 * (N : ℝ) + 1) := by
  have htpos : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hNnneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hfloor : (⌊t * (N : ℝ)⌋₊ : ℝ) ≤ t * (N : ℝ) :=
    Nat.floor_le (by positivity)
  nlinarith [hfloor, ht, hNnneg, htpos]

/-- Cardinality of a real dilation of a symmetric coordinate box grows at most
like `t^r` times the original.  Here the dilated box has radii `⌊t · N i⌋₊`, the
`natDilated`/`dilated` convention of `GAP`. -/
theorem card_dilatedCoordinateBox_le {r : ℕ} (N : Fin r → ℕ) {t : ℝ}
    (ht : 1 ≤ t) :
    ((coordinateBox (fun i => ⌊t * (N i : ℝ)⌋₊)).card : ℝ) ≤
      t ^ r * (coordinateBox N).card := by
  classical
  have htpos : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  rw [card_coordinateBox, card_coordinateBox]
  push_cast
  calc
    ∏ i : Fin r, (2 * (⌊t * (N i : ℝ)⌋₊ : ℝ) + 1)
        ≤ ∏ i : Fin r, (t * (2 * (N i : ℝ) + 1)) := by
          refine Finset.prod_le_prod (fun i _ => by positivity) ?_
          exact fun i _ => two_floor_mul_add_one_le ht
    _ = t ^ r * ∏ i : Fin r, (2 * (N i : ℝ) + 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]

end Nondividing
