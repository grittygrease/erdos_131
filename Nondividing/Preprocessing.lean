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

/-- Integer dilation of a symmetric coordinate box by a factor `k ≥ 1` increases
the cardinality by at most `k^r`.  (`|kQ| ≤ k^r |Q|`.) -/
theorem card_coordinateBox_smul_le {r : ℕ} (N : Fin r → ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (coordinateBox (fun i => k * N i)).card ≤ k ^ r * (coordinateBox N).card := by
  rw [card_coordinateBox, card_coordinateBox]
  calc
    ∏ i : Fin r, (2 * (k * N i) + 1)
        ≤ ∏ i : Fin r, (k * (2 * N i + 1)) :=
          Finset.prod_le_prod' fun i _ => by nlinarith [hk]
    _ = k ^ r * ∏ i : Fin r, (2 * N i + 1) := by
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

/-- For a dilation `t ≥ 1`, the base coefficient box embeds into the dilated
one (the dilated radii `⌊t·Nᵢ⌋₊` dominate `Nᵢ`). -/
theorem coeffBox_subset_dilatedCoeffBox {t : ℝ} (ht : 1 ≤ t) :
    P.coeffBox ⊆ P.dilatedCoeffBox t := by
  intro n hn
  rw [coeffBox, mem_coordinateBox] at hn
  rw [dilatedCoeffBox, mem_coordinateBox]
  intro i
  have hle : P.radius i ≤ P.dilatedRadius t i := by
    show P.radius i ≤ ⌊t * (P.radius i : ℝ)⌋₊
    have hstep : (P.radius i : ℝ) ≤ t * (P.radius i : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (P.radius i), ht]
    calc P.radius i = ⌊(P.radius i : ℝ)⌋₊ := (Nat.floor_natCast _).symm
      _ ≤ ⌊t * (P.radius i : ℝ)⌋₊ := Nat.floor_mono hstep
  refine ⟨?_, ?_⟩
  · have h1 : -((P.dilatedRadius t i : ℕ) : ℤ) ≤ -(P.radius i : ℤ) := by
      exact_mod_cast neg_le_neg (by exact_mod_cast hle)
    exact h1.trans (hn i).1
  · exact (hn i).2.trans (by exact_mod_cast hle)

/-- Hazard: properness of a proper dilate `t·P` (`t ≥ 1`) implies properness of
`P` itself, since the base coefficient box is a subset of the dilated one and
injectivity restricts to subsets.  (`lem:progression-comparison`, route §7.4.) -/
theorem proper_of_dilate {t : ℝ} (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ))) :
    P.Proper :=
  Set.InjOn.mono (Finset.coe_subset.mpr (P.coeffBox_subset_dilatedCoeffBox ht))
    hInj

/-- Counting core of `lem:progression-comparison`.  Given a proper rank-`e` GAP
`R = P` living in `ℤ^r`, a dilation `t = c·s ≥ 1` whose dilated coefficient box
is evaluated injectively, a core set `C₀` inside a coordinate box `Q` of radii
`N` with `|C₀| ≤ k`, and a translate `q` realizing `q + tR ⊆ Σ(C₀)`, the whole
counting chain `t^e |R| ≤ 3^e |Σ(C₀)| ≤ 3^e |kQ|` holds.  Both the `e > r` and
`e ≤ r` cases of the manuscript feed through this inequality with different
choices of `Q`. -/
theorem progression_counting_core (hP : P.Proper) {t : ℝ} (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ)))
    {N : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)} (hC₀ : C₀ ⊆ coordinateBox N)
    {k : ℕ} (hk : C₀.card ≤ k) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀) :
    t ^ e * (P.carrier.card : ℝ) ≤
      3 ^ e * ((coordinateBox (fun i => k * N i)).card : ℝ) := by
  classical
  -- Step 1: `t^e |R| ≤ 3^e |tR|`.
  have h1 := P.scale_card_carrier_le_dilated hP ht hInj
  -- Step 2: `|tR| ≤ |Σ(C₀)|` via the injection `z ↦ q + z`.
  have h2 : (P.dilatedCarrier t).card ≤ (subsetSums C₀).card := by
    apply Finset.card_le_card_of_injOn (fun z => q + z)
    · intro z hz
      exact hincl z hz
    · intro x _ y _ h
      exact add_left_cancel h
  -- Step 3: `Σ(C₀) ⊆ kQ`.
  have h3 : (subsetSums C₀).card ≤ (coordinateBox (fun i => k * N i)).card :=
    Finset.card_le_card (subsetSums_subset_coordinateBox hC₀ hk)
  have h23 : ((P.dilatedCarrier t).card : ℝ) ≤
      ((coordinateBox (fun i => k * N i)).card : ℝ) := by
    exact_mod_cast le_trans h2 h3
  calc
    t ^ e * (P.carrier.card : ℝ)
        ≤ 3 ^ e * ((P.dilatedCarrier t).card : ℝ) := h1
    _ ≤ 3 ^ e * ((coordinateBox (fun i => k * N i)).card : ℝ) := by
          have : (0 : ℝ) ≤ 3 ^ e := by positivity
          exact mul_le_mul_of_nonneg_left h23 this

/-- GAP-valued counting core for the `e ≤ r` case of
`lem:progression-comparison`.  Here the core set `C₀` lives inside another proper
GAP `R'` (the rank-`h` progression `Q_H` produced by the convex-lattice John
lemma), and the subset sums are counted in `R'`'s dilate:
`t^e |R| ≤ 3^e (2k+1)^h |R'|`. -/
theorem progression_counting_core_gap {h : ℕ} (hP : P.Proper) {t : ℝ}
    (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ)))
    (R' : GAP d h) (hR' : R'.Proper) {C₀ : Finset (Fin d → ℤ)}
    (hC₀ : C₀ ⊆ R'.carrier) {k : ℕ} (hk : C₀.card ≤ k) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀) :
    t ^ e * (P.carrier.card : ℝ) ≤
      (3 ^ e * (2 * k + 1) ^ h) * (R'.carrier.card : ℝ) := by
  classical
  have h1 := P.scale_card_carrier_le_dilated hP ht hInj
  have h2 : (P.dilatedCarrier t).card ≤ (subsetSums C₀).card := by
    apply Finset.card_le_card_of_injOn (fun z => q + z)
    · intro z hz
      exact hincl z hz
    · intro x _ y _ hxy
      exact add_left_cancel hxy
  have hsub : subsetSums C₀ ⊆ R'.natDilatedCarrier k := fun v hv =>
    R'.natDilatedCarrier_mono hk (R'.subsetSums_subset_natDilatedCarrier C₀ hC₀ hv)
  have h3 : (subsetSums C₀).card ≤ (2 * k + 1) ^ h * R'.carrier.card :=
    le_trans (Finset.card_le_card hsub) (R'.card_natDilatedCarrier_le_mul hR' k)
  have h23 : ((P.dilatedCarrier t).card : ℝ) ≤
      ((2 * k + 1) ^ h : ℝ) * (R'.carrier.card : ℝ) := by
    calc ((P.dilatedCarrier t).card : ℝ)
          ≤ (((2 * k + 1) ^ h * R'.carrier.card : ℕ) : ℝ) := by
            exact_mod_cast le_trans h2 h3
      _ = ((2 * k + 1) ^ h : ℝ) * (R'.carrier.card : ℝ) := by push_cast; ring
  calc
    t ^ e * (P.carrier.card : ℝ)
        ≤ 3 ^ e * ((P.dilatedCarrier t).card : ℝ) := h1
    _ ≤ 3 ^ e * (((2 * k + 1) ^ h : ℝ) * (R'.carrier.card : ℝ)) :=
          mul_le_mul_of_nonneg_left h23 (by positivity)
    _ = (3 ^ e * (2 * k + 1) ^ h) * (R'.carrier.card : ℝ) := by ring

/-- Assembled `e ≤ r` cardinality inequality of `lem:progression-comparison`.
Folding the convex-lattice John cardinality bound `|Q_H| ≤ Cⱼ |Q|` into the
GAP-valued counting core closes the chain to `t^e |R| ≤ (3^e (2k+1)^h Cⱼ) |Q|`.
-/
theorem progression_cardinality_bound_le {h : ℕ} (hP : P.Proper) {t : ℝ}
    (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ)))
    (R' : GAP d h) (hR' : R'.Proper) {C₀ : Finset (Fin d → ℤ)}
    (hC₀ : C₀ ⊆ R'.carrier) {k : ℕ} (hk : C₀.card ≤ k) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀)
    {Cj : ℕ} {Q : Finset (Fin d → ℤ)} (hJohn : R'.carrier.card ≤ Cj * Q.card) :
    t ^ e * (P.carrier.card : ℝ) ≤
      (3 ^ e * (2 * k + 1) ^ h * Cj) * (Q.card : ℝ) := by
  have core := P.progression_counting_core_gap hP ht hInj R' hR' hC₀ hk hincl
  have hJohnR : (R'.carrier.card : ℝ) ≤ (Cj : ℝ) * (Q.card : ℝ) := by
    calc (R'.carrier.card : ℝ) ≤ ((Cj * Q.card : ℕ) : ℝ) := by exact_mod_cast hJohn
      _ = (Cj : ℝ) * (Q.card : ℝ) := by push_cast; ring
  calc
    t ^ e * (P.carrier.card : ℝ)
        ≤ (3 ^ e * (2 * k + 1) ^ h) * (R'.carrier.card : ℝ) := core
    _ ≤ (3 ^ e * (2 * k + 1) ^ h) * ((Cj : ℝ) * (Q.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hJohnR (by positivity)
    _ = (3 ^ e * (2 * k + 1) ^ h * Cj) * (Q.card : ℝ) := by ring

/-- Assembled `e > r` cardinality inequality of `lem:progression-comparison`:
`t^e |R| ≤ (3^e k^r) |Q|`.  With the manuscript's choices `t = c·s(C)` and
`k = |C₀| ≤ s(C)` this is `s^e |R| ≪ s^r |Q|`, i.e. `|R| ≪ s^{-(e-r)} |Q|`. -/
theorem progression_cardinality_bound (hP : P.Proper) {t : ℝ} (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ)))
    {N : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)} (hC₀ : C₀ ⊆ coordinateBox N)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : C₀.card ≤ k) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀) :
    t ^ e * (P.carrier.card : ℝ) ≤
      (3 ^ e * k ^ d) * ((coordinateBox N).card : ℝ) := by
  have core := P.progression_counting_core hP ht hInj hC₀ hk hincl
  have hsmul : ((coordinateBox (fun i => k * N i)).card : ℝ) ≤
      (k ^ d : ℝ) * ((coordinateBox N).card : ℝ) := by
    have hnat := card_coordinateBox_smul_le N hk1
    calc ((coordinateBox (fun i => k * N i)).card : ℝ)
          ≤ ((k ^ d * (coordinateBox N).card : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (k ^ d : ℝ) * ((coordinateBox N).card : ℝ) := by push_cast; ring
  calc
    t ^ e * (P.carrier.card : ℝ)
        ≤ 3 ^ e * ((coordinateBox (fun i => k * N i)).card : ℝ) := core
    _ ≤ 3 ^ e * ((k ^ d : ℝ) * ((coordinateBox N).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsmul (by positivity)
    _ = (3 ^ e * k ^ d) * ((coordinateBox N).card : ℝ) := by ring

/-- Progression comparison, `e > r` case, stated directly from the E1
`cfp_structure` outputs: the base properness `hP` is derived internally from the
dilate properness via `proper_of_dilate`. -/
theorem progression_comparison_gt {t : ℝ} (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ)))
    {N : Fin d → ℕ} {C₀ : Finset (Fin d → ℤ)} (hC₀ : C₀ ⊆ coordinateBox N)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : C₀.card ≤ k) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀) :
    t ^ e * (P.carrier.card : ℝ) ≤
      (3 ^ e * k ^ d) * ((coordinateBox N).card : ℝ) :=
  P.progression_cardinality_bound (P.proper_of_dilate ht hInj) ht hInj hC₀ hk1 hk
    hincl

/-- Progression comparison, `e ≤ r` case, stated directly from the E1
`cfp_structure` outputs together with the convex-lattice John GAP `Q_H` and its
cardinality bound. -/
theorem progression_comparison_le {h : ℕ} {t : ℝ} (ht : 1 ≤ t)
    (hInj : Set.InjOn P.evalHom (P.dilatedCoeffBox t : Set (Fin e → ℤ)))
    (R' : GAP d h) (hR' : R'.Proper) {C₀ : Finset (Fin d → ℤ)}
    (hC₀ : C₀ ⊆ R'.carrier) {k : ℕ} (hk : C₀.card ≤ k) {q : Fin d → ℤ}
    (hincl : ∀ z ∈ P.dilatedCarrier t, q + z ∈ subsetSums C₀)
    {Cj : ℕ} {Q : Finset (Fin d → ℤ)} (hJohn : R'.carrier.card ≤ Cj * Q.card) :
    t ^ e * (P.carrier.card : ℝ) ≤
      (3 ^ e * (2 * k + 1) ^ h * Cj) * (Q.card : ℝ) :=
  P.progression_cardinality_bound_le (P.proper_of_dilate ht hInj) ht hInj R' hR'
    hC₀ hk hincl hJohn

end GAP

end Nondividing
