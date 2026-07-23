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

/-- Per-factor lower bound for a real dilation of a coordinate interval: for a
positive radius `N ≥ 1` and dilation `t ≥ 1`, the dilated radius keeps at least a
`1/3` fraction of the naive growth `t · (2N+1)`. -/
theorem mul_add_one_le_three_floor {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 1 ≤ t) :
    t * (2 * (N : ℝ) + 1) ≤ 3 * (2 * (⌊t * (N : ℝ)⌋₊ : ℝ) + 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have htpos : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  -- `t·N ≤ ⌊t·N⌋ + 1 ≤ 2⌊t·N⌋ + 1`
  have hfloor : t * (N : ℝ) ≤ 2 * (⌊t * (N : ℝ)⌋₊ : ℝ) + 1 := by
    have h := (Nat.lt_floor_add_one (t * (N : ℝ))).le
    have hnn : (0 : ℝ) ≤ (⌊t * (N : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hprod : (0 : ℝ) ≤ t * ((N : ℝ) - 1) :=
    mul_nonneg htpos (by linarith)
  linarith [hfloor, hprod]

/-- Reverse cardinality estimate: a real dilation of a symmetric coordinate box
retains at least a `3^{-r}` fraction of `t^r` times the original cardinality
(here every radius is positive, matching the proper coordinate-GAP convention). -/
theorem card_le_dilatedCoordinateBox {r : ℕ} (N : Fin r → ℕ)
    (hN : ∀ i, 1 ≤ N i) {t : ℝ} (ht : 1 ≤ t) :
    t ^ r * (coordinateBox N).card ≤
      3 ^ r * ((coordinateBox (fun i => ⌊t * (N i : ℝ)⌋₊)).card : ℝ) := by
  classical
  have htpos : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  rw [card_coordinateBox, card_coordinateBox]
  push_cast
  calc
    t ^ r * ∏ i : Fin r, (2 * (N i : ℝ) + 1)
        = ∏ i : Fin r, (t * (2 * (N i : ℝ) + 1)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
    _ ≤ ∏ i : Fin r, (3 * (2 * (⌊t * (N i : ℝ)⌋₊ : ℝ) + 1)) := by
          refine Finset.prod_le_prod (fun i _ => by positivity) ?_
          exact fun i _ => mul_add_one_le_three_floor (hN i) ht
    _ = 3 ^ r * ∏ i : Fin r, (2 * (⌊t * (N i : ℝ)⌋₊ : ℝ) + 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]

/-- Subset sums of at most `k` points drawn from a symmetric coordinate box lie
in the `k`-fold dilated coordinate box.  This is the `Σ(C₀) ⊆ sQ` step of
`lem:progression-comparison` (with `k = |C₀| ≤ s`). -/
theorem subsetSums_subset_coordinateBox {r : ℕ} {M : Fin r → ℕ}
    {C : Finset (Fin r → ℤ)} (hC : C ⊆ coordinateBox M) {k : ℕ}
    (hk : C.card ≤ k) :
    subsetSums C ⊆ coordinateBox (fun i => k * M i) := by
  intro v hv
  obtain ⟨S, hSC, rfl⟩ := mem_subsetSums.mp hv
  rw [mem_coordinateBox]
  intro i
  have hbound (a : Fin r → ℤ) (ha : a ∈ S) :
      -(M i : ℤ) ≤ a i ∧ a i ≤ M i :=
    (mem_coordinateBox.mp (hC (hSC ha))) i
  have hcard : (S.card : ℤ) ≤ k := by
    exact_mod_cast le_trans (Finset.card_le_card hSC) hk
  have hMnn : (0 : ℤ) ≤ M i := Int.natCast_nonneg _
  constructor
  · calc
      -((k * M i : ℕ) : ℤ) ≤ -((S.card * M i : ℕ) : ℤ) := by
            have : (S.card * M i : ℤ) ≤ (k * M i : ℤ) :=
              mul_le_mul_of_nonneg_right hcard hMnn
            push_cast at this ⊢; linarith
      _ = ∑ a ∈ S, -(M i : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ a ∈ S, a i := Finset.sum_le_sum fun a ha => (hbound a ha).1
      _ = (∑ a ∈ S, a) i := by simp
  · calc
      (∑ a ∈ S, a) i = ∑ a ∈ S, a i := by simp
      _ ≤ ∑ a ∈ S, (M i : ℤ) := Finset.sum_le_sum fun a ha => (hbound a ha).2
      _ = ((S.card * M i : ℕ) : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
      _ ≤ ((k * M i : ℕ) : ℤ) := by
            have : (S.card * M i : ℤ) ≤ (k * M i : ℤ) :=
              mul_le_mul_of_nonneg_right hcard hMnn
            push_cast at this ⊢; linarith

namespace GAP

variable {d e : ℕ} (P : GAP d e)

/-- Real-dilation carrier lower bound: for a proper GAP `P` and a dilation
`t ≥ 1` whose dilated coefficient box is still evaluated injectively, the dilated
carrier retains at least a `3^{-e}` fraction of `t^e · |P|`.  This is the
`s^e |R| ≪ |csR|` step of `lem:progression-comparison`. -/
theorem scale_card_carrier_le_dilated (hP : P.Proper) {t : ℝ} (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ))) :
    t ^ e * (P.carrier.card : ℝ) ≤ 3 ^ e * ((P.dilatedCarrier t).card : ℝ) := by
  have hcarrier : (P.carrier.card : ℝ) = ((coordinateBox P.radius).card : ℝ) := by
    rw [P.card_carrier_of_proper hP]; rfl
  have hdil : ((P.dilatedCarrier t).card : ℝ)
      = ((coordinateBox (fun i => ⌊t * (P.radius i : ℝ)⌋₊)).card : ℝ) := by
    rw [P.card_dilatedCarrier_of_injOn t hInj]
    rfl
  rw [hcarrier, hdil]
  exact card_le_dilatedCoordinateBox P.radius (fun i => P.radius_pos i) ht

end GAP

end Nondividing
