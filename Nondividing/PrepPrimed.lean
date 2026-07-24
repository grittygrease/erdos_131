import Nondividing.DescentInterface

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# The primed preprocessing supplier, unconditionally

This file proves `PrepSupplier'` (DescentInterface.lean) **without** the two
documented interface residues of `PrepSupplierProof.lean`:

* **no `hdown1`** — the primed down branch carries the constant-relaxed box
  bound `|B'| ≤ Cdown·|B|`, which is exactly what the proven geometric input
  (`dimension_move`, via `PrepMove.box_down`) delivers: a down move at
  ambient dimension `≤ Dcap` satisfies `|B'| ≤ Cd·|B|` with
  `Cd = max 1 (C·prepCinv^{Dcap})` (`prepMove_down_box_le`), and the chain
  master estimate turns this into `|B_end| ≤ Cd^{Dcap}·|B_start|` for a
  net-down good chain.  The supplier's constant is `Cdown := Cd^{Dcap}`.

* **no `hout`** — the primed interface has no uniform output threshold; the
  three output clauses are the chain retention bounds
  (`|V'| ≥ |V|^{1−ε}` resp. `ρ ≥ |V|^{−ε}`), which are exactly what the
  `(δ/2)^i`-retention with `i ≤ imax` gives in the proven regime
  `40·log(2/δ) ≤ ε·log(1/γ)` (`rpow_le_pow_prepImax`).

Route (mirroring `PrepSupplierProof.lean`):

1. `prep_step_uniform` — `prep_step` with the one-step constant `C`
   quantified **before** the shell parameter `X` (the construction is
   already `X`-uniform; `PrepSupplier'` fixes `Cdown` before the stage).
2. `prepMove_down_box_le` — the per-move relaxed down-box bound.
3. `prep_supplier_step'` — the single-stage master theorem: the invariant
   descent over good chains with down constant `Cd` (instead of the
   undischargeable sharp constant `1`), output in the `PrepSupplier'`
   branch shape.  The same-dimensional `ρ^{K₀}`-box accounting absorbs the
   down-move constants through the strengthened smallness clause
   `(Cup·Cd)² ≤ (δ/2)^{4K₀}·smin`.
4. `PrepNumerics'`/`prepNumerics'_of_large` — the numeric bundle for `n`
   large; the shrink cap is shifted by the constant
   `E = ⌈log(Cd^{Dcap})/log(1/γ)⌉` absorbing `Cd^{Dcap}` into the γ-power
   accounting, and the retention floor `n^{−ε} ≤ (δ/2)^{imax+E}` follows
   from `rpow_le_pow_prepImax` plus one further eventual clause.
5. `prepSupplier'_of_numerics`, `prepSupplier'_final`,
   `prepSupplier'_params` — assembly; `δ` is a **free** parameter
   (`0 < δ ≤ 1/2`), with `γ := (δ/2)^K`, `K := max 5 ⌈40/ε⌉`, so the regime
   `40·log(2/δ) ≤ ε·log(1/γ) = ε·K·log(2/δ)` holds for every such `δ`.

Everything here only *adds* declarations; no existing file is modified.
-/

/-! ## The `X`-uniform one-step lemma -/

/-- **Uniform one-step lemma**: `prep_step` with the constant `C` chosen
before the shell parameter `X`.  The construction of `prep_step` (sum of the
`dimension_move` constants over ambient dimensions `≤ dmax`) does not depend
on `X`; this restatement exposes that, so a single down-move constant can be
fixed before the `∀ X` of `PrepSupplier'`. -/
theorem prep_step_uniform {β : ℝ} (pkgs : ∀ r, Package r β) (dmax : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ) (δ γ : ℝ) (s : PrepStage X), s.dim ≤ dmax →
        ¬ StageIrreducible pkgs δ γ s →
        (∀ D : Finset (Fin s.dim → ℤ), D ⊆ s.V →
          δ * (s.V.card : ℝ) ≤ (D.card : ℝ) →
          ∀ _hE : Eligible β (pkgs s.dim).m₀ D s.M,
          1 ≤ structureScale D.card ∧
            1 ≤ (pkgs s.dim).c * structureScale D.card) →
        ∃ s' : PrepStage X, PrepMove pkgs δ γ C s s' := by
  classical
  choose Cdm hCdm using fun r : ℕ => dimension_move r (pkgs r)
  set C : ℝ := ∑ r ∈ Finset.range (dmax + 1), Cdm r with hCdef
  have hCpos : 0 < C :=
    Finset.sum_pos (fun r _ => (hCdm r).1)
      ⟨0, Finset.mem_range.mpr (by omega)⟩
  refine ⟨C, hCpos, ?_⟩
  intro X δ γ s hdim hnot hsupply
  rcases irreducible_or_witness (pkgs s.dim) δ γ s.V s.M with hirr |
    ⟨D, hDV, hDcard, hE, hdefect⟩
  · exact absurd hirr hnot
  obtain ⟨hs1, ht1⟩ := hsupply D hDV hDcard hE
  have hshellD : ShellNonDividing (fun v => s.lam v) X D := s.shell.mono hDV
  rcases Nat.lt_trichotomy ((pkgs s.dim).out D s.M hE).e s.dim with
    hlt | heq | hgt
  · -- down move
    obtain ⟨r, lam', D', N, hbox, hshell', hcardge, hr, hbound⟩ :=
      (hCdm s.dim).2 D s.M hE hs1 ht1 s.lam X hshellD
    refine ⟨⟨r, D', N, lam', hbox, hshell'⟩, D, hDV, hDcard, hcardge, ?_,
      Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · show r ≤ (pkgs s.dim).D
      rw [hr]; exact ((pkgs s.dim).out D s.M hE).e_le
    · show r < s.dim
      rw [hr]; exact hlt
    · show (pkgs s.dim).c ^ r * ((coordinateBox N).card : ℝ) ≤
        C * ((coordinateBox s.M).card : ℝ)
      have hCle : Cdm s.dim ≤ C := by
        rw [hCdef]
        exact Finset.single_le_sum (f := Cdm) (fun i _ => (hCdm i).1.le)
          (Finset.mem_range.mpr (by omega))
      rw [← hr] at hbound
      exact hbound.trans
        (mul_le_mul_of_nonneg_right hCle (Nat.cast_nonneg _))
  · -- same dimension: the defect must be a small progression
    rcases hdefect with hne | hsmall
    · exact absurd heq hne
    obtain ⟨r, lam', D', N, hbox, hshell', hcardge, hboxlt, hr⟩ :=
      small_progression_move (pkgs s.dim) hE ht1 hsmall s.lam X hshellD
    refine ⟨⟨r, D', N, lam', hbox, hshell'⟩, D, hDV, hDcard, hcardge, ?_,
      Or.inl ⟨?_, hboxlt⟩⟩
    · show r ≤ (pkgs s.dim).D
      rw [hr]; exact ((pkgs s.dim).out D s.M hE).e_le
    · show r = s.dim
      rw [hr]; exact heq
  · -- up move
    obtain ⟨r, lam', D', N, hbox, hshell', hcardge, hr, hbound⟩ :=
      dimension_move_up (pkgs s.dim) hE hs1 ht1 s.lam X hshellD
    refine ⟨⟨r, D', N, lam', hbox, hshell'⟩, D, hDV, hDcard, hcardge, ?_,
      Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · show r ≤ (pkgs s.dim).D
      rw [hr]; exact ((pkgs s.dim).out D s.M hE).e_le
    · show s.dim < r
      rw [hr]; exact hgt
    · show ((pkgs s.dim).c * structureScale D.card) ^ r *
          ((coordinateBox N).card : ℝ) ≤
        3 ^ r * structureScale D.card ^ s.dim *
          ((coordinateBox s.M).card : ℝ)
      rw [← hr] at hbound
      exact hbound

/-! ## The relaxed per-move down-box bound -/

/-- **Relaxed down-move box bound**: a dimension-decreasing `PrepMove` at
ambient dimension `≤ Dcap` satisfies `|B'| ≤ Cd·|B|` with the uniform
constant `Cd = max 1 (C·prepCinv^{Dcap})` — this is the constant that
`dimension_move` actually produces (`c^{d'}·|B'| ≤ C·|B|` with
`c⁻¹ ≤ prepCinv` and `d' < dim ≤ Dcap`). -/
theorem prepMove_down_box_le {β : ℝ} {pkgs : ∀ r, Package r β} {Dcap : ℕ}
    {δ γ C : ℝ} (hC0 : 0 < C) {X : ℕ} {x y : PrepStage X}
    (hdim : x.dim ≤ Dcap) (h : PrepMove pkgs δ γ C x y)
    (hlt : y.dim < x.dim) :
    ((coordinateBox y.M).card : ℝ) ≤
      max 1 (C * prepCinv pkgs Dcap ^ Dcap) *
        ((coordinateBox x.M).card : ℝ) := by
  have hbd := PrepMove.box_down h hlt
  have hc := (pkgs x.dim).c_pos
  have hinv : ((pkgs x.dim).c⁻¹) ^ y.dim * ((pkgs x.dim).c ^ y.dim *
      ((coordinateBox y.M).card : ℝ)) = ((coordinateBox y.M).card : ℝ) := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hc), one_pow,
      one_mul]
  have h1 : ((coordinateBox y.M).card : ℝ) ≤
      ((pkgs x.dim).c⁻¹) ^ y.dim * (C * ((coordinateBox x.M).card : ℝ)) := by
    rw [← hinv]
    exact mul_le_mul_of_nonneg_left hbd (by positivity)
  have hcinvle : ((pkgs x.dim).c⁻¹) ^ y.dim ≤ prepCinv pkgs Dcap ^ Dcap := by
    have ha : (pkgs x.dim).c⁻¹ ≤ prepCinv pkgs Dcap :=
      le_prepCinv pkgs Dcap hdim
    have hb : (1 : ℝ) ≤ prepCinv pkgs Dcap := one_le_prepCinv pkgs Dcap
    calc ((pkgs x.dim).c⁻¹) ^ y.dim
        ≤ prepCinv pkgs Dcap ^ y.dim := pow_le_pow_left₀ (by positivity) ha _
      _ ≤ prepCinv pkgs Dcap ^ Dcap := pow_le_pow_right₀ hb (by omega)
  calc ((coordinateBox y.M).card : ℝ)
      ≤ ((pkgs x.dim).c⁻¹) ^ y.dim *
          (C * ((coordinateBox x.M).card : ℝ)) := h1
    _ = (C * ((pkgs x.dim).c⁻¹) ^ y.dim) *
          ((coordinateBox x.M).card : ℝ) := by ring
    _ ≤ (C * prepCinv pkgs Dcap ^ Dcap) *
          ((coordinateBox x.M).card : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left hcinvle hC0.le
    _ ≤ max 1 (C * prepCinv pkgs Dcap ^ Dcap) *
          ((coordinateBox x.M).card : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)

/-! ## The primed per-stage master theorem

Adaptation of `prep_supplier_step` (PrepSupplierProof.lean) to the primed
interface: the `GoodStep` down constant is `Cd` (discharged from the move
structure via `hdownC`, no sharp `hdown1` needed), there is no uniform
output threshold (`hn₁out` dropped — the retention clauses *are* the
output), and the conclusion is the `PrepSupplier'` branch disjunction with
down-branch constant `Cd^{Dcap}`. -/

set_option maxHeartbeats 1000000 in
theorem prep_supplier_step' {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    (Dcap : ℕ) {ζ₀ ε δ γ K₀ : ℝ} {C Cd : ℝ} (s : PrepStage X)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hK₀ : 0 ≤ K₀) (hCd1 : 1 ≤ Cd) (hbad : ExcessiveStage ζ₀ s)
    {smin Cup T : ℝ} {Ucap Scap imax : ℕ}
    (hCup : 1 ≤ Cup) (hT : 1 < T) (hsminT : Cup * Cd * T ≤ smin)
    (hUcapT : Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) < T ^ (Ucap + 1))
    (hScapγ : Cup ^ Ucap * Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) <
      (1 / γ) ^ (Scap + 1))
    (himax : Scap + 2 * Ucap + s.dim ≤ imax)
    (hdimD : s.dim + Ucap ≤ Dcap)
    (hρε : (s.V.card : ℝ) ^ (-ε) ≤ (δ / 2) ^ imax)
    (hupbox : (s.V.card : ℝ) ^ (1 - ε) * (Cup ^ Ucap * Cd ^ Dcap) ≤ smin)
    (hγK₀ : γ ≤ (δ / 2) ^ K₀)
    (hsminK₀ : (Cup * Cd) * (Cup * Cd) ≤ (δ / 2) ^ (4 * K₀) * smin)
    (hscale : ∀ m : ℕ, δ * ((δ / 2) ^ imax * (s.V.card : ℝ)) ≤ (m : ℝ) →
      1 ≤ structureScale m ∧ smin ≤ structureScale m)
    (hcsmin : ∀ r, r ≤ Dcap → 1 ≤ (pkgs r).c * smin)
    (hCupB : ∀ r, r ≤ Dcap →
      ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D ≤ Cup)
    (hdel : ∀ r, r ≤ Dcap →
      (pkgs r).c⁻¹ ≤ δ / 2 *
        Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))))
    (hexp1 : Real.exp 1 ≤ δ * ((δ / 2) ^ imax * (s.V.card : ℝ)))
    (hdownC : ∀ x y : PrepStage X, x.dim ≤ Dcap →
      PrepMove pkgs δ γ C x y → y.dim < x.dim →
      ((coordinateBox y.M).card : ℝ) ≤ Cd * ((coordinateBox x.M).card : ℝ))
    (hCstep : ∀ t : PrepStage X, t.dim ≤ Dcap →
      ¬ StageIrreducible pkgs δ γ t →
      (∀ Dw : Finset (Fin t.dim → ℤ), Dw ⊆ t.V →
        δ * (t.V.card : ℝ) ≤ (Dw.card : ℝ) →
        ∀ _hE : Eligible β (pkgs t.dim).m₀ Dw t.M,
        1 ≤ structureScale Dw.card ∧
          1 ≤ (pkgs t.dim).c * structureScale Dw.card) →
      ∃ t', PrepMove pkgs δ γ C t t') :
    ∃ s' : PrepStage X,
      ((s.dim < s'.dim ∧ s'.dim ≤ Dcap ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            (s.V.card : ℝ) ^ (1 / (sigma s.dim + stageExcess s) -
              (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)))) ∨
        (s'.dim < s.dim ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            Cd ^ Dcap * ((coordinateBox s.M).card : ℝ)) ∨
        (s'.dim = s.dim ∧ StageIrreducible pkgs δ γ s' ∧
          ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
            (s.V.card : ℝ) ^ (-ε) ≤ ρ ∧
            ρ * (s.V.card : ℝ) ≤ (s'.V.card : ℝ) ∧
            ((coordinateBox s'.M).card : ℝ) ≤
              ρ ^ K₀ * ((coordinateBox s.M).card : ℝ))) := by
  classical
  -- Base stage facts.
  have hδ2pos : (0 : ℝ) < δ / 2 := by linarith
  have hδ2le : δ / 2 ≤ 1 := by linarith
  have hCup0 : (0 : ℝ) < Cup := lt_of_lt_of_le one_pos hCup
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le one_pos hCd1
  have hCupCd1 : (1 : ℝ) ≤ Cup * Cd := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ Cup * Cd := mul_le_mul hCup hCd1 zero_le_one (by linarith)
  have hsmin1 : (1 : ℝ) < smin := by
    have h := mul_le_mul_of_nonneg_right hCupCd1
      (le_of_lt (lt_trans one_pos hT))
    rw [one_mul] at h
    linarith
  have hsmin0 : (0 : ℝ) < smin := by linarith
  have hs1 : (1 : ℝ) ≤ smin := hsmin1.le
  have hnflδ : (0 : ℝ) < δ * ((δ / 2) ^ imax * (s.V.card : ℝ)) :=
    lt_of_lt_of_le (Real.exp_pos 1) hexp1
  have hn2 : 2 ≤ s.V.card := hbad.two_le_card hζ₀.le
  have hnR : (2 : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < (s.V.card : ℝ) := by linarith
  have hn1R : (1 : ℝ) ≤ (s.V.card : ℝ) := by linarith
  have hbox2 : 2 ≤ (coordinateBox s.M).card := hbad.two_le_box hζ₀.le
  have hB₀2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast hbox2
  have hB₀0 : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by linarith
  have hγinv : (1 : ℝ) < 1 / γ := by
    rw [lt_div_iff₀ hγ0]; linarith
  have hsdimD : s.dim ≤ Dcap := by omega
  -- The step predicate: retention + up-decay at floor `smin` + down with
  -- the relaxed constant `Cd` (from the move structure, via `hdownC`).
  set Q : PrepStage X → PrepStage X → Prop := GoodStep δ smin Cup Cd
    with hQdef
  -- U-cap along good chains.
  have hUcapCh : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → ch.upSum ≤ Ucap := by
    intro t ch hOK
    have h1 := PrepChain.pow_upSum_le_stepsOK (Cdown := Cd) hγ0 hγ1.le hCup
      hCd1 hT.le hsminT ch hOK
    have h2 : Cd ^ s.dim * ((coordinateBox s.M).card : ℝ) ≤
        Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hB₀0.le
      exact pow_le_pow_right₀ hCd1 hsdimD
    exact pow_exponent_cap hT (h1.trans h2) hUcapT
  -- Length cap along good chains (the γ-power accounting).
  have hlencap : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → ch.length ≤ imax := by
    intro t ch hOK
    have hU := hUcapCh t ch hOK
    have huc : ch.upCount ≤ ch.upSum := ch.upCount_le_upSum
    have hdc : ch.downCount ≤ s.dim + ch.upSum := ch.downCount_le
    have hS : ch.shrinkCount ≤ Scap := by
      have h1 := PrepChain.shrink_cap_stepsOK (Cdown := Cd) hγ0 hCup0
        hCd0 hs1 ch hOK
      have h2 : Cup ^ ch.upCount ≤ Cup ^ Ucap :=
        pow_le_pow_right₀ hCup (le_trans huc hU)
      have h2b : Cd ^ ch.downCount ≤ Cd ^ Dcap :=
        pow_le_pow_right₀ hCd1 (by omega)
      have h3 : (1 / γ) ^ ch.shrinkCount ≤
          Cup ^ Ucap * Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) := by
        refine le_trans h1 ?_
        apply mul_le_mul_of_nonneg_right _ hB₀0.le
        exact mul_le_mul h2 h2b (pow_nonneg hCd0.le _) (pow_nonneg hCup0.le _)
      exact pow_exponent_cap hγinv h3 hScapγ
    rw [ch.length_eq_counts]
    omega
  -- Cardinality floor at endpoints of good chains.
  have hcardfloor : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → (δ / 2) ^ imax * (s.V.card : ℝ) ≤ (t.V.card : ℝ) := by
    intro t ch hOK
    have h1 := PrepChain.card_retention_stepsOK (Cup := Cup) (Cdown := Cd)
      (smin := smin) hδ0.le ch hOK
    have h2 : (δ / 2) ^ imax ≤ (δ / 2) ^ ch.length :=
      pow_le_pow_of_le_one hδ2pos.le hδ2le (hlencap t ch hOK)
    calc (δ / 2) ^ imax * (s.V.card : ℝ)
        ≤ (δ / 2) ^ ch.length * (s.V.card : ℝ) :=
          mul_le_mul_of_nonneg_right h2 hn0.le
      _ ≤ (t.V.card : ℝ) := h1
  -- Dimension cap at endpoints of good chains.
  have hdimcap : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → t.dim ≤ Dcap := by
    intro t ch hOK
    have h1 := ch.dim_le
    have h2 := hUcapCh t ch hOK
    omega
  -- The descent step: extend any good chain at a non-irreducible endpoint.
  have hstepOK : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → ¬ StageIrreducible pkgs δ γ t →
      ∃ (u : PrepStage X) (_ : PrepMove pkgs δ γ C t u), Q t u := by
    intro t ch hOK hirr
    have hVt : (δ / 2) ^ imax * (s.V.card : ℝ) ≤ (t.V.card : ℝ) :=
      hcardfloor t ch hOK
    have htdim : t.dim ≤ Dcap := hdimcap t ch hOK
    have hVt0 : (0 : ℝ) < (t.V.card : ℝ) :=
      lt_of_lt_of_le (mul_pos (pow_pos hδ2pos _) hn0) hVt
    -- Scale facts for δ-large subsets of `V_t`.
    have hDwfacts : ∀ Dw : Finset (Fin t.dim → ℤ), Dw ⊆ t.V →
        δ * (t.V.card : ℝ) ≤ (Dw.card : ℝ) →
        1 ≤ structureScale Dw.card ∧ smin ≤ structureScale Dw.card := by
      intro Dw _ hlarge
      apply hscale
      calc δ * ((δ / 2) ^ imax * (s.V.card : ℝ))
          ≤ δ * (t.V.card : ℝ) := mul_le_mul_of_nonneg_left hVt hδ0.le
        _ ≤ (Dw.card : ℝ) := hlarge
    have hsupply : ∀ Dw : Finset (Fin t.dim → ℤ), Dw ⊆ t.V →
        δ * (t.V.card : ℝ) ≤ (Dw.card : ℝ) →
        ∀ _hE : Eligible β (pkgs t.dim).m₀ Dw t.M,
        1 ≤ structureScale Dw.card ∧
          1 ≤ (pkgs t.dim).c * structureScale Dw.card := by
      intro Dw h1 h2 _
      refine ⟨(hDwfacts Dw h1 h2).1, ?_⟩
      calc (1 : ℝ) ≤ (pkgs t.dim).c * smin := hcsmin t.dim htdim
        _ ≤ (pkgs t.dim).c * structureScale Dw.card :=
          mul_le_mul_of_nonneg_left (hDwfacts Dw h1 h2).2
            (pkgs t.dim).c_pos.le
    obtain ⟨u, hu⟩ := hCstep t htdim hirr hsupply
    refine ⟨u, hu, ?_, ?_, ?_⟩
    · -- Retention `|V_u| ≥ (δ/2)|V_t|` (E1 deletion is at most `(δ/2)|V_t|`).
      obtain ⟨Dw, hDV, hDcard, hdrop, _, _⟩ := hu
      have hc0 : (0 : ℝ) ≤ (pkgs t.dim).c⁻¹ :=
        inv_nonneg.mpr (pkgs t.dim).c_pos.le
      have hDwn : δ * ((δ / 2) ^ imax * (s.V.card : ℝ)) ≤ (Dw.card : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hVt hδ0.le) hDcard
      have hlogfloor : (1 : ℝ) ≤
          Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))) := by
        have := Real.log_le_log (Real.exp_pos 1) hexp1
        rwa [Real.log_exp] at this
      have hlogpos : (0 : ℝ) <
          Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))) := by linarith
      have hlogDw : Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))) ≤
          Real.log (Dw.card : ℝ) := Real.log_le_log hnflδ hDwn
      have hlogDwpos : (0 : ℝ) < Real.log (Dw.card : ℝ) := by linarith
      have hDwle : (Dw.card : ℝ) ≤ (t.V.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hDV
      have hdelstep : (Dw.card : ℝ) / Real.log (Dw.card : ℝ) ≤
          (t.V.card : ℝ) /
            Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))) := by
        rw [div_le_div_iff₀ hlogDwpos hlogpos]
        have e1 : (Dw.card : ℝ) *
            Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))) ≤
            (Dw.card : ℝ) * Real.log (Dw.card : ℝ) :=
          mul_le_mul_of_nonneg_left hlogDw (Nat.cast_nonneg _)
        have e2 : (Dw.card : ℝ) * Real.log (Dw.card : ℝ) ≤
            (t.V.card : ℝ) * Real.log (Dw.card : ℝ) :=
          mul_le_mul_of_nonneg_right hDwle hlogDwpos.le
        linarith
      have hdelbound : (pkgs t.dim).c⁻¹ * Dw.card / Real.log Dw.card ≤
          δ / 2 * (t.V.card : ℝ) := by
        have e3 : (pkgs t.dim).c⁻¹ * (Dw.card : ℝ) /
            Real.log (Dw.card : ℝ) =
            (pkgs t.dim).c⁻¹ *
              ((Dw.card : ℝ) / Real.log (Dw.card : ℝ)) := by ring
        rw [e3]
        calc (pkgs t.dim).c⁻¹ * ((Dw.card : ℝ) / Real.log (Dw.card : ℝ))
            ≤ (pkgs t.dim).c⁻¹ * ((t.V.card : ℝ) /
                Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ)))) :=
              mul_le_mul_of_nonneg_left hdelstep hc0
          _ ≤ (δ / 2 * Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ)))) *
                ((t.V.card : ℝ) /
                  Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ)))) :=
              mul_le_mul_of_nonneg_right (hdel t.dim htdim) (by positivity)
          _ = δ / 2 * (t.V.card : ℝ) *
                (Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))) /
                  Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ)))) := by
              ring
          _ = δ / 2 * (t.V.card : ℝ) := by
              rw [div_self (ne_of_gt hlogpos), mul_one]
      linarith
    · -- Up-move box decay at the scale floor.
      intro hlt
      have hboxup := PrepMove.box_up hu hlt hs1
        (fun Dw h1 h2 => (hDwfacts Dw h1 h2).2)
      obtain ⟨_, _, _, _, hdimle, _⟩ := hu
      set c_t : ℝ := (pkgs t.dim).c with hct
      have hc : (0 : ℝ) < c_t := (pkgs t.dim).c_pos
      have key : smin ^ (u.dim - t.dim) * ((coordinateBox u.M).card : ℝ) ≤
          (3 * c_t⁻¹) ^ u.dim * ((coordinateBox t.M).card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hboxup
          (le_of_lt (pow_pos (inv_pos.mpr hc) u.dim))
        calc smin ^ (u.dim - t.dim) * ((coordinateBox u.M).card : ℝ)
            = (c_t⁻¹) ^ u.dim * (c_t ^ u.dim *
                (smin ^ (u.dim - t.dim) *
                  ((coordinateBox u.M).card : ℝ))) := by
              rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hc),
                one_pow, one_mul]
          _ ≤ (c_t⁻¹) ^ u.dim *
                (3 ^ u.dim * ((coordinateBox t.M).card : ℝ)) := hmul
          _ = (3 * c_t⁻¹) ^ u.dim * ((coordinateBox t.M).card : ℝ) := by
              rw [mul_pow]; ring
      refine le_trans key
        (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
      have hmax1 : (1 : ℝ) ≤ max 1 c_t⁻¹ := le_max_left _ _
      calc (3 * c_t⁻¹) ^ u.dim
          ≤ (3 * max 1 c_t⁻¹) ^ u.dim := by
            apply pow_le_pow_left₀ (by positivity)
            have := le_max_right (1 : ℝ) c_t⁻¹
            linarith
        _ ≤ (3 * max 1 c_t⁻¹) ^ (pkgs t.dim).D :=
            pow_le_pow_right₀ (by linarith) hdimle
        _ ≤ Cup := hCupB t.dim htdim
    · -- Down-move: the relaxed constant bound from the move structure.
      intro hlt
      exact hdownC t u htdim hu hlt
  -- Run the descent.
  obtain ⟨t, ch, hOK, hirr⟩ :=
    exists_irreducible_chain_stepsOK s hlencap hstepOK
  -- End-of-chain facts.
  have hlen := hlencap t ch hOK
  have hret : (δ / 2) ^ ch.length * (s.V.card : ℝ) ≤ (t.V.card : ℝ) :=
    PrepChain.card_retention_stepsOK (Cup := Cup) (Cdown := Cd)
      (smin := smin) hδ0.le ch hOK
  have hVtfloor : (δ / 2) ^ imax * (s.V.card : ℝ) ≤ (t.V.card : ℝ) :=
    hcardfloor t ch hOK
  have hUt := hUcapCh t ch hOK
  have huct : ch.upCount ≤ ch.upSum := ch.upCount_le_upSum
  have hCupuc : Cup ^ ch.upCount ≤ Cup ^ Ucap :=
    pow_le_pow_right₀ hCup (le_trans huct hUt)
  have hdcD : ch.downCount ≤ Dcap := by
    have h1 := ch.downCount_le
    omega
  have hCddc : Cd ^ ch.downCount ≤ Cd ^ Dcap :=
    pow_le_pow_right₀ hCd1 hdcD
  have hγS1 : γ ^ ch.shrinkCount ≤ 1 := pow_le_one₀ hγ0.le hγ1.le
  have hretε : (s.V.card : ℝ) ^ (1 - ε) ≤ (t.V.card : ℝ) := by
    have h1 : (s.V.card : ℝ) ^ (1 - ε) =
        (s.V.card : ℝ) ^ (-ε) * (s.V.card : ℝ) := by
      rw [show (1 : ℝ) - ε = -ε + 1 by ring, Real.rpow_add hn0,
        Real.rpow_one]
    rw [h1]
    calc (s.V.card : ℝ) ^ (-ε) * (s.V.card : ℝ)
        ≤ (δ / 2) ^ imax * (s.V.card : ℝ) :=
          mul_le_mul_of_nonneg_right hρε hn0.le
      _ ≤ (t.V.card : ℝ) := hVtfloor
  -- Master box estimate along the chain (with down constant `Cd`).
  have hmaster : smin ^ ch.upSum * ((coordinateBox t.M).card : ℝ) ≤
      γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount *
        ((coordinateBox s.M).card : ℝ) :=
    PrepChain.box_master_stepsOK (Cdown := Cd) hγ0 hCup0 hCd0 hs1 ch hOK
  -- Case split on the net dimension change.
  rcases Nat.lt_trichotomy t.dim s.dim with hlt | heq | hgt
  · -- DOWN: `|B̃| ≤ Cd^{Dcap}·|B₀|` from the master estimate (`Cup ≤ smin`
    -- absorbs the up factors; `γ ≤ 1` kills the shrink factors).
    refine ⟨t, Or.inr (Or.inl ⟨hlt, hretε, ?_⟩)⟩
    have hCdT1 : (1 : ℝ) ≤ Cd * T :=
      le_trans hCd1 (le_mul_of_one_le_right hCd0.le hT.le)
    have hCupsmin : Cup ≤ smin := by
      have h1 : Cup * 1 ≤ Cup * (Cd * T) :=
        mul_le_mul_of_nonneg_left hCdT1 hCup0.le
      have h2 : Cup * (Cd * T) = Cup * Cd * T := by ring
      rw [mul_one, h2] at h1
      linarith
    have h1 : Cup ^ ch.upCount ≤ smin ^ ch.upSum :=
      le_trans (pow_le_pow_left₀ hCup0.le hCupsmin _)
        (pow_le_pow_right₀ hs1 huct)
    have hkey : γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount ≤
        smin ^ ch.upSum * Cd ^ Dcap := by
      calc γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount
          ≤ 1 * smin ^ ch.upSum * Cd ^ Dcap := by
            apply mul_le_mul _ hCddc (pow_nonneg hCd0.le _)
              (mul_nonneg zero_le_one (pow_nonneg hsmin0.le _))
            exact mul_le_mul hγS1 h1 (pow_nonneg hCup0.le _) one_pos.le
        _ = smin ^ ch.upSum * Cd ^ Dcap := by ring
    have h2 : γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount *
        ((coordinateBox s.M).card : ℝ) ≤
        smin ^ ch.upSum * (Cd ^ Dcap * ((coordinateBox s.M).card : ℝ)) := by
      calc γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount *
            ((coordinateBox s.M).card : ℝ)
          ≤ (smin ^ ch.upSum * Cd ^ Dcap) *
              ((coordinateBox s.M).card : ℝ) :=
            mul_le_mul_of_nonneg_right hkey hB₀0.le
        _ = smin ^ ch.upSum *
              (Cd ^ Dcap * ((coordinateBox s.M).card : ℝ)) := by ring
    have h3 := le_trans hmaster h2
    exact le_of_mul_le_mul_left h3 (pow_pos hsmin0 _)
  · -- SAME DIMENSION: irreducible output with `ρ = (δ/2)^i` bookkeeping.
    refine ⟨t, Or.inr (Or.inr ⟨heq, hirr, ?_⟩)⟩
    set ρ : ℝ := (δ / 2) ^ ch.length with hρdef
    have hρ0 : 0 < ρ := pow_pos hδ2pos _
    have hρ1 : ρ ≤ 1 := pow_le_one₀ hδ2pos.le hδ2le
    have hρlow : (s.V.card : ℝ) ^ (-ε) ≤ ρ :=
      le_trans hρε (pow_le_pow_of_le_one hδ2pos.le hδ2le hlen)
    refine ⟨ρ, hρ0, hρ1, hρlow, hret, ?_⟩
    set q : ℝ := (δ / 2) ^ K₀ with hqdef
    have hq0 : 0 < q := Real.rpow_pos_of_pos hδ2pos _
    have hq1 : q ≤ 1 := Real.rpow_le_one hδ2pos.le hδ2le hK₀
    have hρK : ρ ^ K₀ = q ^ ch.length := by
      rw [hρdef, hqdef, ← Real.rpow_natCast (δ / 2) ch.length,
        ← Real.rpow_mul hδ2pos.le, mul_comm ((ch.length : ℕ) : ℝ) K₀,
        Real.rpow_mul hδ2pos.le, Real.rpow_natCast]
    have hq4 : (q * q) * (q * q) = (δ / 2 : ℝ) ^ (4 * K₀) := by
      rw [hqdef, ← Real.rpow_add hδ2pos, ← Real.rpow_add hδ2pos,
        show K₀ + K₀ + (K₀ + K₀) = 4 * K₀ by ring]
    have hsums : ch.downSum = ch.upSum := by
      have := ch.dim_add_downSum_eq
      omega
    have hdct : ch.downCount ≤ ch.upSum := by
      have := ch.downCount_le_downSum
      omega
    set W : ℝ := Cup * Cd with hWdef
    have hW1 : (1 : ℝ) ≤ W := hCupCd1
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos hW1
    have hWsq : W * W ≤ (q * q) * (q * q) * smin := by
      rw [hq4]
      exact hsminK₀
    have hkey : γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount ≤
        smin ^ ch.upSum * q ^ ch.length := by
      have hγq : γ ^ ch.shrinkCount ≤ q ^ ch.shrinkCount :=
        pow_le_pow_left₀ hγ0.le hγK₀ _
      have hCupW : Cup ≤ W := by
        rw [hWdef]
        exact le_mul_of_one_le_right hCup0.le hCd1
      have hCdW : Cd ≤ W := by
        rw [hWdef]
        exact le_mul_of_one_le_left hCd0.le hCup
      have h1 : Cup ^ ch.upCount * Cd ^ ch.downCount ≤
          W ^ (ch.upCount + ch.downCount) := by
        rw [pow_add]
        exact mul_le_mul (pow_le_pow_left₀ hCup0.le hCupW _)
          (pow_le_pow_left₀ hCd0.le hCdW _) (pow_nonneg hCd0.le _)
          (pow_nonneg hW0.le _)
      have h2 : W ^ (ch.upCount + ch.downCount) ≤ W ^ (2 * ch.upSum) :=
        pow_le_pow_right₀ hW1 (by omega)
      have h3 : W ^ (2 * ch.upSum) = (W * W) ^ ch.upSum := by
        rw [pow_mul, pow_two]
      have h4 : (W * W) ^ ch.upSum ≤
          ((q * q) * (q * q) * smin) ^ ch.upSum :=
        pow_le_pow_left₀ (mul_nonneg hW0.le hW0.le) hWsq _
      have hq4' : (q * q) * (q * q) = q ^ (4 : ℕ) := by ring
      have h5 : ((q * q) * (q * q) * smin) ^ ch.upSum =
          q ^ (4 * ch.upSum) * smin ^ ch.upSum := by
        rw [hq4', mul_pow, ← pow_mul]
      have h6 : q ^ (4 * ch.upSum) ≤ q ^ (ch.upCount + ch.downCount) :=
        pow_le_pow_of_le_one hq0.le hq1 (by omega)
      calc γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount
          ≤ q ^ ch.shrinkCount * (Cup ^ ch.upCount * Cd ^ ch.downCount) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hγq
              (mul_nonneg (pow_nonneg hCup0.le _) (pow_nonneg hCd0.le _))
        _ ≤ q ^ ch.shrinkCount *
              (q ^ (ch.upCount + ch.downCount) * smin ^ ch.upSum) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0.le _)
            calc Cup ^ ch.upCount * Cd ^ ch.downCount
                ≤ W ^ (ch.upCount + ch.downCount) := h1
              _ ≤ W ^ (2 * ch.upSum) := h2
              _ = (W * W) ^ ch.upSum := h3
              _ ≤ ((q * q) * (q * q) * smin) ^ ch.upSum := h4
              _ = q ^ (4 * ch.upSum) * smin ^ ch.upSum := h5
              _ ≤ q ^ (ch.upCount + ch.downCount) * smin ^ ch.upSum :=
                  mul_le_mul_of_nonneg_right h6 (pow_nonneg hsmin0.le _)
        _ = smin ^ ch.upSum *
              q ^ (ch.shrinkCount + (ch.upCount + ch.downCount)) := by
            rw [pow_add]
            ring
        _ = smin ^ ch.upSum * q ^ ch.length := by
            rw [ch.length_eq_counts, add_assoc]
    have hfinal : smin ^ ch.upSum * ((coordinateBox t.M).card : ℝ) ≤
        smin ^ ch.upSum *
          (q ^ ch.length * ((coordinateBox s.M).card : ℝ)) := by
      calc smin ^ ch.upSum * ((coordinateBox t.M).card : ℝ)
          ≤ γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount *
              ((coordinateBox s.M).card : ℝ) := hmaster
        _ ≤ smin ^ ch.upSum * q ^ ch.length *
              ((coordinateBox s.M).card : ℝ) :=
            mul_le_mul_of_nonneg_right hkey hB₀0.le
        _ = smin ^ ch.upSum *
              (q ^ ch.length * ((coordinateBox s.M).card : ℝ)) := by ring
    have hboxfin : ((coordinateBox t.M).card : ℝ) ≤
        q ^ ch.length * ((coordinateBox s.M).card : ℝ) :=
      le_of_mul_le_mul_left hfinal (pow_pos hsmin0 _)
    rw [hρK]
    exact hboxfin
  · -- UP: net scale decay gives the manuscript's `|B̃| ≪ n^{-(1-ε)Δ}|B₀|`.
    refine ⟨t, Or.inl ⟨hgt, ?_, hretε, ?_⟩⟩
    · have h1 := ch.dim_le
      omega
    · -- Net-up master estimate.
      have hnet := PrepChain.box_master_net_up_stepsOK (Cdown := Cd) hγ0
        hCup0 hCd0 hs1 ch hOK
      have h1 : smin ^ (t.dim - s.dim) * ((coordinateBox t.M).card : ℝ) ≤
          Cup ^ Ucap * Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) := by
        refine le_trans hnet ?_
        apply mul_le_mul_of_nonneg_right _ hB₀0.le
        calc γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cd ^ ch.downCount
            ≤ 1 * Cup ^ Ucap * Cd ^ Dcap := by
              apply mul_le_mul _ hCddc (pow_nonneg hCd0.le _)
                (mul_nonneg zero_le_one (pow_nonneg hCup0.le _))
              exact mul_le_mul hγS1 hCupuc (pow_nonneg hCup0.le _) one_pos.le
          _ = Cup ^ Ucap * Cd ^ Dcap := by ring
      -- The exact excess identity `B₀ = n^{1/(σ+ζ)}`.
      have hζlo := hbad.zeta_lt_stageExcess hζ₀.le
      have hσd := sigma_pos s.dim
      have hσζ : 0 < sigma s.dim + stageExcess s := by linarith
      have hexact : ((coordinateBox s.M).card : ℝ) ^
          (sigma s.dim + stageExcess s) = (s.V.card : ℝ) :=
        rpow_sigma_add_stageExcess hbox2 (by omega)
      have hB₀eq : ((coordinateBox s.M).card : ℝ) =
          (s.V.card : ℝ) ^ (1 / (sigma s.dim + stageExcess s)) := by
        have h2 : (((coordinateBox s.M).card : ℝ) ^
            (sigma s.dim + stageExcess s)) ^
              (1 / (sigma s.dim + stageExcess s)) =
            ((coordinateBox s.M).card : ℝ) := by
          rw [← Real.rpow_mul hB₀0.le, mul_one_div,
            div_self (ne_of_gt hσζ), Real.rpow_one]
        rw [← h2, hexact]
      have hΔcast : ((t.dim - s.dim : ℕ) : ℝ) =
          (t.dim : ℝ) - (s.dim : ℝ) := by
        rw [Nat.cast_sub hgt.le]
      -- The exponent absorption `Cup^{Ucap}·Cd^{Dcap}·n^{(1-ε)Δ} ≤ smin^Δ`.
      set nP : ℝ := (s.V.card : ℝ) ^
        ((1 - ε) * ((t.dim : ℝ) - (s.dim : ℝ))) with hnPdef
      have hnP0 : 0 < nP := Real.rpow_pos_of_pos hn0 _
      have hkey : Cup ^ Ucap * Cd ^ Dcap * nP ≤
          smin ^ (t.dim - s.dim) := by
        have hΔ1 : 1 ≤ t.dim - s.dim := by omega
        have e1 : nP = ((s.V.card : ℝ) ^ (1 - ε)) ^ (t.dim - s.dim) := by
          rw [hnPdef, ← hΔcast, ← Real.rpow_natCast
            ((s.V.card : ℝ) ^ (1 - ε)) (t.dim - s.dim),
            ← Real.rpow_mul hn0.le]
        have hnε0 : (0 : ℝ) ≤ (s.V.card : ℝ) ^ (1 - ε) :=
          Real.rpow_nonneg hn0.le _
        have hCupU1 : (1 : ℝ) ≤ Cup ^ Ucap := one_le_pow₀ hCup
        have hCdD1 : (1 : ℝ) ≤ Cd ^ Dcap := one_le_pow₀ hCd1
        have hCC1 : (1 : ℝ) ≤ Cup ^ Ucap * Cd ^ Dcap := by
          calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
            _ ≤ Cup ^ Ucap * Cd ^ Dcap :=
                mul_le_mul hCupU1 hCdD1 zero_le_one (by linarith)
        rw [e1]
        calc Cup ^ Ucap * Cd ^ Dcap *
              ((s.V.card : ℝ) ^ (1 - ε)) ^ (t.dim - s.dim)
            ≤ (Cup ^ Ucap * Cd ^ Dcap) ^ (t.dim - s.dim) *
                ((s.V.card : ℝ) ^ (1 - ε)) ^ (t.dim - s.dim) := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg hnε0 _)
              calc Cup ^ Ucap * Cd ^ Dcap
                  = (Cup ^ Ucap * Cd ^ Dcap) ^ 1 := (pow_one _).symm
                _ ≤ (Cup ^ Ucap * Cd ^ Dcap) ^ (t.dim - s.dim) :=
                  pow_le_pow_right₀ hCC1 hΔ1
          _ = (Cup ^ Ucap * Cd ^ Dcap * (s.V.card : ℝ) ^ (1 - ε)) ^
                (t.dim - s.dim) := (mul_pow _ _ _).symm
          _ ≤ smin ^ (t.dim - s.dim) := by
              apply pow_le_pow_left₀
                (mul_nonneg (mul_nonneg (pow_nonneg hCup0.le _)
                  (pow_nonneg hCd0.le _)) hnε0)
              calc Cup ^ Ucap * Cd ^ Dcap * (s.V.card : ℝ) ^ (1 - ε)
                  = (s.V.card : ℝ) ^ (1 - ε) *
                      (Cup ^ Ucap * Cd ^ Dcap) := by ring
                _ ≤ smin := hupbox
      -- Conclude.
      have hchain : ((coordinateBox t.M).card : ℝ) *
          (Cup ^ Ucap * Cd ^ Dcap * nP) ≤
          Cup ^ Ucap * Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) := by
        calc ((coordinateBox t.M).card : ℝ) *
              (Cup ^ Ucap * Cd ^ Dcap * nP)
            ≤ ((coordinateBox t.M).card : ℝ) * smin ^ (t.dim - s.dim) :=
              mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
          _ = smin ^ (t.dim - s.dim) * ((coordinateBox t.M).card : ℝ) :=
              mul_comm _ _
          _ ≤ Cup ^ Ucap * Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) := h1
      have h2 : ((coordinateBox t.M).card : ℝ) * nP ≤
          ((coordinateBox s.M).card : ℝ) := by
        have h3 : Cup ^ Ucap * Cd ^ Dcap *
            (((coordinateBox t.M).card : ℝ) * nP) ≤
            Cup ^ Ucap * Cd ^ Dcap * ((coordinateBox s.M).card : ℝ) := by
          calc Cup ^ Ucap * Cd ^ Dcap *
                (((coordinateBox t.M).card : ℝ) * nP)
              = ((coordinateBox t.M).card : ℝ) *
                  (Cup ^ Ucap * Cd ^ Dcap * nP) := by ring
            _ ≤ Cup ^ Ucap * Cd ^ Dcap *
                  ((coordinateBox s.M).card : ℝ) := hchain
        exact le_of_mul_le_mul_left h3
          (mul_pos (pow_pos hCup0 _) (pow_pos hCd0 _))
      have htarget : (s.V.card : ℝ) ^
          (1 / (sigma s.dim + stageExcess s) -
            (1 - ε) * ((t.dim : ℝ) - (s.dim : ℝ))) =
          ((coordinateBox s.M).card : ℝ) * nP⁻¹ := by
        rw [Real.rpow_sub hn0, hB₀eq, hnPdef, div_eq_mul_inv]
      rw [htarget]
      calc ((coordinateBox t.M).card : ℝ)
          = ((coordinateBox t.M).card : ℝ) * nP * nP⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hnP0), mul_one]
        _ ≤ ((coordinateBox s.M).card : ℝ) * nP⁻¹ :=
            mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hnP0.le)

/-! ## The assembled primed supplier -/

/-- **Per-cardinality numeric threshold bundle** for `prep_supplier_step'`
(the primed variant of `PrepNumerics`): no uniform output-threshold clause,
and the up/shrink caps and smallness clauses carry the down-move constant
`Cd`. -/
def PrepNumerics' {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (ε δ γ K₀ Cd : ℝ) (n d₀ B₀ : ℕ) : Prop :=
  ∃ (smin Cup T : ℝ) (Ucap Scap imax : ℕ),
    1 ≤ Cup ∧ 1 < T ∧ Cup * Cd * T ≤ smin ∧
    Cd ^ Dcap * (B₀ : ℝ) < T ^ (Ucap + 1) ∧
    Cup ^ Ucap * Cd ^ Dcap * (B₀ : ℝ) < (1 / γ) ^ (Scap + 1) ∧
    Scap + 2 * Ucap + d₀ ≤ imax ∧
    d₀ + Ucap ≤ Dcap ∧
    (n : ℝ) ^ (-ε) ≤ (δ / 2) ^ imax ∧
    (n : ℝ) ^ (1 - ε) * (Cup ^ Ucap * Cd ^ Dcap) ≤ smin ∧
    γ ≤ (δ / 2) ^ K₀ ∧
    (Cup * Cd) * (Cup * Cd) ≤ (δ / 2) ^ (4 * K₀) * smin ∧
    (∀ m : ℕ, δ * ((δ / 2) ^ imax * (n : ℝ)) ≤ (m : ℝ) →
      1 ≤ structureScale m ∧ smin ≤ structureScale m) ∧
    (∀ r, r ≤ Dcap → 1 ≤ (pkgs r).c * smin) ∧
    (∀ r, r ≤ Dcap → ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D ≤ Cup) ∧
    (∀ r, r ≤ Dcap →
      (pkgs r).c⁻¹ ≤ δ / 2 * Real.log (δ * ((δ / 2) ^ imax * (n : ℝ)))) ∧
    Real.exp 1 ≤ δ * ((δ / 2) ^ imax * (n : ℝ))

/-- **The primed preprocessing supplier from the numeric bundle.**  Unlike
`prepSupplier_of_numerics`, no sharp down-box hypothesis and no uniform
output threshold are consumed: the (X-uniform) one-step data `hCstep` and
the relaxed per-move down bound `hdownC` suffice.  The supplier's
down-branch constant is `Cd^{Dcap}`. -/
theorem prepSupplier'_of_numerics {β : ℝ} (pkgs : ∀ r, Package r β)
    (Dcap : ℕ) (ζ₀ ε δ γ K₀ : ℝ) (C Cd : ℝ) (n₁ : ℕ)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hK₀ : 0 ≤ K₀) (hCd1 : 1 ≤ Cd)
    (hCstep : ∀ (X : ℕ) (s : PrepStage X), s.dim ≤ Dcap →
      ¬ StageIrreducible pkgs δ γ s →
      (∀ Dw : Finset (Fin s.dim → ℤ), Dw ⊆ s.V →
        δ * (s.V.card : ℝ) ≤ (Dw.card : ℝ) →
        ∀ _hE : Eligible β (pkgs s.dim).m₀ Dw s.M,
        1 ≤ structureScale Dw.card ∧
          1 ≤ (pkgs s.dim).c * structureScale Dw.card) →
      ∃ s' : PrepStage X, PrepMove pkgs δ γ C s s')
    (hdownC : ∀ (X : ℕ) (x y : PrepStage X), x.dim ≤ Dcap →
      PrepMove pkgs δ γ C x y → y.dim < x.dim →
      ((coordinateBox y.M).card : ℝ) ≤ Cd * ((coordinateBox x.M).card : ℝ))
    (hnum : ∀ n d₀ B₀ : ℕ, n₁ ≤ n →
      (B₀ : ℝ) ^ (sigma d₀ + ζ₀) < (n : ℝ) → n ≤ B₀ → 1 ≤ d₀ →
      (d₀ : ℝ) ≤ 2 / ζ₀ →
      PrepNumerics' pkgs Dcap ε δ γ K₀ Cd n d₀ B₀) :
    PrepSupplier' pkgs Dcap ζ₀ ε δ γ K₀ (Cd ^ Dcap) n₁ := by
  intro X s _hX hbad hn
  obtain ⟨smin, Cup, T, Ucap, Scap, imax,
    hCup, hT, hsminT, hUcapT, hScapγ, himax, hdimD, hρε, hupbox,
    hγK₀, hsminK₀, hscale, hcsmin, hCupB, hdel, hexp1⟩ :=
    hnum s.V.card s.dim (coordinateBox s.M).card hn hbad
      (stage_card_le_box s) (hbad.one_le_dim hζ₀.le)
      (hbad.dim_cast_le hζ₀)
  exact prep_supplier_step' Dcap s hζ₀ hδ0 hδ1 hγ0 hγ1 hK₀ hCd1 hbad
    hCup hT hsminT hUcapT hScapγ himax hdimD hρε hupbox hγK₀ hsminK₀
    hscale hcsmin hCupB hdel hexp1 (hdownC X) (hCstep X)

/-! ## Discharging the primed numeric bundle -/

set_option maxHeartbeats 2000000 in
/-- **All clauses of `PrepNumerics'` hold for `n` large.**  Explicit choices
`Ucap = 10`, `T = √n`, `smin = c₀·n^{1−ε/2}/(log n)²` with
`c₀ = δ·(δ/2)^E`, and `Scap/imax` shifted by the constant
`E = ⌈log(Cd^{Dcap})/log(1/γ)⌉` which absorbs the down-move constant into
the γ-power accounting.  Same regime as `prepNumerics_of_large`:
`0 < δ ≤ 1`, `0 < γ < 1`, `0 < ε < 1`, `γ ≤ (δ/2)^{K₀}`,
`40·log(2/δ) ≤ ε·log(1/γ)`, `2/ζ₀ + 10 ≤ Dcap` — and NO output-threshold
clause. -/
theorem prepNumerics'_of_large {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (ζ₀ ε δ γ K₀ Cd : ℝ)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hCd1 : 1 ≤ Cd)
    (hγK₀ : γ ≤ (δ / 2) ^ K₀)
    (hKε : 40 * Real.log (2 / δ) ≤ ε * Real.log (1 / γ))
    (hDζ : 2 / ζ₀ + 10 ≤ (Dcap : ℝ)) :
    ∃ n₂ : ℕ, ∀ n d₀ B₀ : ℕ, n₂ ≤ n →
      (B₀ : ℝ) ^ (sigma d₀ + ζ₀) < (n : ℝ) → n ≤ B₀ → 1 ≤ d₀ →
      (d₀ : ℝ) ≤ 2 / ζ₀ →
      PrepNumerics' pkgs Dcap ε δ γ K₀ Cd n d₀ B₀ := by
  have hCup1 : 1 ≤ prepCup pkgs Dcap := one_le_prepCup pkgs Dcap
  have hCup0 : (0 : ℝ) < prepCup pkgs Dcap := lt_of_lt_of_le one_pos hCup1
  have hCinv1 : 1 ≤ prepCinv pkgs Dcap := one_le_prepCinv pkgs Dcap
  have hδ2pos : (0 : ℝ) < δ / 2 := by linarith
  have hδ2le : δ / 2 ≤ 1 := by linarith
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le one_pos hCd1
  have hCdD1 : (1 : ℝ) ≤ Cd ^ Dcap := one_le_pow₀ hCd1
  have hCdD0 : (0 : ℝ) < Cd ^ Dcap := pow_pos hCd0 _
  have hγinv1 : (1 : ℝ) < 1 / γ := by rw [lt_div_iff₀ hγ0]; linarith
  have hLγ : 0 < Real.log (1 / γ) := Real.log_pos hγinv1
  -- The constant shift `E` absorbing `Cd^{Dcap}` into the shrink cap.
  obtain ⟨E, hγE⟩ : ∃ E : ℕ, Cd ^ Dcap ≤ (1 / γ) ^ E := by
    refine ⟨⌈Real.log (Cd ^ Dcap) / Real.log (1 / γ)⌉₊, ?_⟩
    have h1 : Real.log (Cd ^ Dcap) / Real.log (1 / γ) ≤
        ((⌈Real.log (Cd ^ Dcap) / Real.log (1 / γ)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : Real.log (Cd ^ Dcap) ≤
        ((⌈Real.log (Cd ^ Dcap) / Real.log (1 / γ)⌉₊ : ℕ) : ℝ) *
          Real.log (1 / γ) := by
      rw [div_le_iff₀ hLγ] at h1
      linarith
    calc Cd ^ Dcap = Real.exp (Real.log (Cd ^ Dcap)) :=
          (Real.exp_log hCdD0).symm
      _ ≤ Real.exp
            (((⌈Real.log (Cd ^ Dcap) / Real.log (1 / γ)⌉₊ : ℕ) : ℝ) *
              Real.log (1 / γ)) := Real.exp_le_exp.mpr h2
      _ = (1 / γ) ^ (⌈Real.log (Cd ^ Dcap) / Real.log (1 / γ)⌉₊ : ℕ) := by
          rw [← Real.log_pow, Real.exp_log
            (pow_pos (by linarith : (0 : ℝ) < 1 / γ) _)]
  set c₀ : ℝ := δ * (δ / 2) ^ E with hc₀def
  have hc₀0 : 0 < c₀ := by positivity
  have hc₀1 : c₀ ≤ 1 := by
    have h1 : (δ / 2 : ℝ) ^ E ≤ 1 := pow_le_one₀ hδ2pos.le hδ2le
    calc c₀ = δ * (δ / 2) ^ E := hc₀def
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ0.le
      _ = δ := mul_one δ
      _ ≤ 1 := hδ1
  -- Eventual clauses.
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCup pkgs Dcap * Cd * (Real.log n) ^ 2 ≤
        c₀ * (n : ℝ) ^ ((1 - ε) / 2) :=
    eventually_mul_log_sq_le hc₀0 (by linarith)
  have hev3 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCup pkgs Dcap ^ 10 * Cd ^ Dcap * (Real.log n) ^ 2 ≤
        c₀ * (n : ℝ) ^ (ε / 2) :=
    eventually_mul_log_sq_le hc₀0 (by linarith)
  have hev4 : ∀ᶠ n : ℕ in Filter.atTop,
      (prepCup pkgs Dcap * Cd) * (prepCup pkgs Dcap * Cd) *
          (Real.log n) ^ 2 ≤
        ((δ / 2) ^ (4 * K₀) * c₀) * (n : ℝ) ^ (1 - ε / 2) :=
    eventually_mul_log_sq_le
      (mul_pos (Real.rpow_pos_of_pos hδ2pos _) hc₀0) (by linarith)
  have hev5 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCinv pkgs Dcap * (Real.log n) ^ 2 ≤
        c₀ * (n : ℝ) ^ (1 - ε / 2) :=
    eventually_mul_log_sq_le hc₀0 (by linarith)
  have htm₁ : Filter.Tendsto (fun n : ℕ => c₀ * (n : ℝ) ^ (1 - ε / 2))
      Filter.atTop Filter.atTop :=
    (((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ε / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop hc₀0)
  have hev6 : ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp 2 ≤ c₀ * (n : ℝ) ^ (1 - ε / 2) :=
    htm₁.eventually_ge_atTop _
  have hev7 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCinv pkgs Dcap ≤
        δ / 2 * Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) := by
    have h := (Real.tendsto_log_atTop.comp htm₁).eventually_ge_atTop
      (2 / δ * prepCinv pkgs Dcap)
    filter_upwards [h] with n hn
    have h2 : δ / 2 * (2 / δ * prepCinv pkgs Dcap) ≤
        δ / 2 * Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) :=
      mul_le_mul_of_nonneg_left hn (by linarith)
    calc prepCinv pkgs Dcap = δ / 2 * (2 / δ * prepCinv pkgs Dcap) := by
          field_simp
      _ ≤ δ / 2 * Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) := h2
  have hev8 : ∀ᶠ n : ℕ in Filter.atTop,
      ε / 4 * Real.log (prepCup pkgs Dcap) +
        ((20 : ℝ) + Dcap) * Real.log (2 / δ) ≤
        3 * ε / 8 * Real.log n := by
    have h := (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop
      ((ε / 4 * Real.log (prepCup pkgs Dcap) +
        ((20 : ℝ) + Dcap) * Real.log (2 / δ)) / (3 * ε / 8))
    filter_upwards [h] with n hn
    simp only [Function.comp_apply] at hn
    rw [div_le_iff₀ (by linarith)] at hn
    linarith
  have hev9 : ∀ᶠ n : ℕ in Filter.atTop,
      ((2 / δ : ℝ)) ^ E ≤ (n : ℝ) ^ (ε / 2) := by
    have h := ((tendsto_rpow_atTop
      (by linarith : (0 : ℝ) < ε / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop ((2 / δ) ^ E)
    filter_upwards [h] with n hn
    simpa using hn
  have hev10 : ∀ᶠ n : ℕ in Filter.atTop,
      Cd ^ Dcap ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h := ((tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (Cd ^ Dcap)
    filter_upwards [h] with n hn
    simpa using hn
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop 2).and (hev2.and (hev3.and (hev4.and
      (hev5.and (hev6.and (hev7.and (hev8.and (hev9.and hev10)))))))))
  refine ⟨n₂, ?_⟩
  intro n d₀ B₀ hn hbadB hnB _hd₀ hdd
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hn₂ n hn
  have hn2 : 2 ≤ n := h1
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hsq : (0 : ℝ) < (Real.log n) ^ 2 := by positivity
  -- The retention floor with the `E`-shift.
  have hhalf : (n : ℝ) ^ (-(ε / 2)) ≤ (δ / 2) ^ prepImax pkgs Dcap γ n :=
    rpow_le_pow_prepImax pkgs Dcap hδ0 hδ1 hγ0 hγ1 hKε hn2 h8
  have hE2 : (n : ℝ) ^ (-(ε / 2)) ≤ (δ / 2) ^ E := by
    have hpos : (0 : ℝ) < (n : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hn0 _
    have key : (1 : ℝ) ≤ (δ / 2) ^ E * (n : ℝ) ^ (ε / 2) := by
      calc (1 : ℝ) = (δ / 2) ^ E * (2 / δ) ^ E := by
            rw [← mul_pow, show (δ / 2 : ℝ) * (2 / δ) = 1 by
              field_simp, one_pow]
        _ ≤ (δ / 2) ^ E * (n : ℝ) ^ (ε / 2) :=
            mul_le_mul_of_nonneg_left h9 (pow_nonneg hδ2pos.le _)
    have hmul : (n : ℝ) ^ (-(ε / 2)) * (n : ℝ) ^ (ε / 2) = 1 := by
      rw [← Real.rpow_add hn0, show -(ε / 2) + ε / 2 = 0 by ring,
        Real.rpow_zero]
    have hle : (n : ℝ) ^ (-(ε / 2)) * (n : ℝ) ^ (ε / 2) ≤
        (δ / 2) ^ E * (n : ℝ) ^ (ε / 2) := by
      rw [hmul]; exact key
    exact le_of_mul_le_mul_right hle hpos
  have hfloorE : (n : ℝ) ^ (-ε) ≤
      (δ / 2) ^ (prepImax pkgs Dcap γ n + E) := by
    have hnhalf : (n : ℝ) ^ (-(ε / 2)) * (n : ℝ) ^ (-(ε / 2)) =
        (n : ℝ) ^ (-ε) := by
      rw [← Real.rpow_add hn0, show -(ε / 2) + -(ε / 2) = -ε by ring]
    calc (n : ℝ) ^ (-ε)
        = (n : ℝ) ^ (-(ε / 2)) * (n : ℝ) ^ (-(ε / 2)) := hnhalf.symm
      _ ≤ (δ / 2) ^ prepImax pkgs Dcap γ n * (δ / 2) ^ E :=
          mul_le_mul hhalf hE2 (Real.rpow_nonneg hn0.le _)
            (pow_nonneg hδ2pos.le _)
      _ = (δ / 2) ^ (prepImax pkgs Dcap γ n + E) := (pow_add _ _ _).symm
  -- The floor value of the deletion/scale thresholds.
  have hm₁m₀ : c₀ * (n : ℝ) ^ (1 - ε / 2) ≤
      δ * ((δ / 2) ^ (prepImax pkgs Dcap γ n + E) * (n : ℝ)) := by
    have e1 : (n : ℝ) ^ (1 - ε / 2) = (n : ℝ) ^ (-(ε / 2)) * (n : ℝ) := by
      rw [show (1 - ε / 2 : ℝ) = -(ε / 2) + 1 by ring, Real.rpow_add hn0,
        Real.rpow_one]
    have hkey : (δ / 2 : ℝ) ^ E * (n : ℝ) ^ (1 - ε / 2) ≤
        (δ / 2) ^ (prepImax pkgs Dcap γ n + E) * (n : ℝ) := by
      calc (δ / 2 : ℝ) ^ E * (n : ℝ) ^ (1 - ε / 2)
          = (δ / 2) ^ E * ((n : ℝ) ^ (-(ε / 2)) * (n : ℝ)) := by rw [e1]
        _ ≤ (δ / 2) ^ E *
              ((δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ2pos.le _)
            exact mul_le_mul_of_nonneg_right hhalf hn0.le
        _ = (δ / 2) ^ (prepImax pkgs Dcap γ n + E) * (n : ℝ) := by
            rw [pow_add]
            ring
    calc c₀ * (n : ℝ) ^ (1 - ε / 2)
        = δ * ((δ / 2) ^ E * (n : ℝ) ^ (1 - ε / 2)) := by
          rw [hc₀def]; ring
      _ ≤ δ * ((δ / 2) ^ (prepImax pkgs Dcap γ n + E) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey hδ0.le
  have hm₁pos : (0 : ℝ) < c₀ * (n : ℝ) ^ (1 - ε / 2) := by positivity
  -- `B₀ < n^5`.
  have hB₀1 : (1 : ℝ) ≤ (B₀ : ℝ) := by
    have h : (n : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast hnB
    linarith
  have hB₀n5 : (B₀ : ℝ) < (n : ℝ) ^ (5 : ℕ) := by
    have h15 : (1 : ℝ) / 5 ≤ sigma d₀ + ζ₀ := by
      linarith [one_fifth_le_sigma d₀]
    have ha : (B₀ : ℝ) ^ ((1 : ℝ) / 5) ≤ (B₀ : ℝ) ^ (sigma d₀ + ζ₀) :=
      Real.rpow_le_rpow_of_exponent_le hB₀1 h15
    have hb : (B₀ : ℝ) ^ ((1 : ℝ) / 5) < (n : ℝ) := lt_of_le_of_lt ha hbadB
    have hc : ((B₀ : ℝ) ^ ((1 : ℝ) / 5)) ^ (5 : ℝ) < (n : ℝ) ^ (5 : ℝ) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg (by linarith) _) hb (by norm_num)
    have hd : ((B₀ : ℝ) ^ ((1 : ℝ) / 5)) ^ (5 : ℝ) = (B₀ : ℝ) := by
      rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ (B₀ : ℝ))]
      norm_num
    have he : (n : ℝ) ^ (5 : ℝ) = (n : ℝ) ^ (5 : ℕ) := by
      rw [← Real.rpow_natCast (n : ℝ) 5]
      norm_num
    rw [hd, he] at hc
    exact hc
  -- Assemble the bundle.
  refine ⟨c₀ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2, prepCup pkgs Dcap,
    (n : ℝ) ^ ((1 : ℝ) / 2), 10, prepScap pkgs Dcap γ n + E,
    prepImax pkgs Dcap γ n + E, hCup1, ?_, ?_, ?_, ?_, ?_, ?_, hfloorE, ?_,
    hγK₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `1 < T`
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 2) := (Real.one_rpow _).symm
      _ < (n : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_lt_rpow (by norm_num) (by linarith) (by norm_num)
  · -- `Cup·Cd·T ≤ smin`
    rw [le_div_iff₀ hsq]
    have hT0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg hn0.le _
    have hexp : (1 : ℝ) / 2 + (1 - ε) / 2 = 1 - ε / 2 := by ring
    calc prepCup pkgs Dcap * Cd * (n : ℝ) ^ ((1 : ℝ) / 2) *
          (Real.log n) ^ 2
        = (n : ℝ) ^ ((1 : ℝ) / 2) *
            (prepCup pkgs Dcap * Cd * (Real.log n) ^ 2) := by ring
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (c₀ * (n : ℝ) ^ ((1 - ε) / 2)) :=
          mul_le_mul_of_nonneg_left h2 hT0
      _ = c₀ * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 - ε) / 2)) := by
          ring
      _ = c₀ * (n : ℝ) ^ (1 - ε / 2) := by
          rw [← Real.rpow_add hn0, hexp]
  · -- `Cd^{Dcap}·B₀ < T^{11}`
    have hT10 : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 : ℕ) =
        (n : ℝ) ^ (5 : ℕ) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 2)) 10,
        ← Real.rpow_mul hn0.le, ← Real.rpow_natCast (n : ℝ) 5]
      norm_num
    calc Cd ^ Dcap * (B₀ : ℝ)
        < Cd ^ Dcap * (n : ℝ) ^ (5 : ℕ) :=
          mul_lt_mul_of_pos_left hB₀n5 hCdD0
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (5 : ℕ) :=
          mul_le_mul_of_nonneg_right h10 (by positivity)
      _ = (n : ℝ) ^ ((1 : ℝ) / 2) *
            ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 : ℕ) := by rw [hT10]
      _ = ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 + 1 : ℕ) :=
          (pow_succ' _ 10).symm
  · -- `Cup^{10}·Cd^{Dcap}·B₀ < (1/γ)^{Scap+E+1}`
    have hlt5 : prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ (5 : ℕ) <
        (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) :=
      lt_pow_prepScap_succ pkgs Dcap hγ0 hγ1 (by omega)
    have hpow : (1 / γ : ℝ) ^ (prepScap pkgs Dcap γ n + E + 1) =
        (1 / γ) ^ E * (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) := by
      rw [← pow_add,
        show E + (prepScap pkgs Dcap γ n + 1) =
          prepScap pkgs Dcap γ n + E + 1 by omega]
    calc prepCup pkgs Dcap ^ 10 * Cd ^ Dcap * (B₀ : ℝ)
        = Cd ^ Dcap * (prepCup pkgs Dcap ^ 10 * (B₀ : ℝ)) := by ring
      _ < Cd ^ Dcap * (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) := by
          apply mul_lt_mul_of_pos_left _ hCdD0
          calc prepCup pkgs Dcap ^ 10 * (B₀ : ℝ)
              < prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ (5 : ℕ) :=
                mul_lt_mul_of_pos_left hB₀n5 (pow_pos hCup0 _)
            _ < (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) := hlt5
      _ ≤ (1 / γ) ^ E * (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) :=
          mul_le_mul_of_nonneg_right hγE (pow_nonneg (by positivity) _)
      _ = (1 / γ) ^ (prepScap pkgs Dcap γ n + E + 1) := hpow.symm
  · -- `Scap + 2·Ucap + d₀ ≤ imax`
    have hd₀D : d₀ ≤ Dcap := by
      have h : (d₀ : ℝ) ≤ (Dcap : ℝ) := by linarith
      exact_mod_cast h
    have himx : prepImax pkgs Dcap γ n =
        prepScap pkgs Dcap γ n + 20 + Dcap := rfl
    omega
  · -- `d₀ + Ucap ≤ Dcap`
    have h : (d₀ : ℝ) + 10 ≤ (Dcap : ℝ) := by linarith
    exact_mod_cast h
  · -- `n^{1-ε}·Cup^{10}·Cd^{Dcap} ≤ smin`
    rw [le_div_iff₀ hsq]
    have hn1ε0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 - ε) := Real.rpow_nonneg hn0.le _
    have hexp : (1 - ε : ℝ) + ε / 2 = 1 - ε / 2 := by ring
    calc (n : ℝ) ^ (1 - ε) * (prepCup pkgs Dcap ^ 10 * Cd ^ Dcap) *
          (Real.log n) ^ 2
        = (n : ℝ) ^ (1 - ε) *
            (prepCup pkgs Dcap ^ 10 * Cd ^ Dcap * (Real.log n) ^ 2) := by
          ring
      _ ≤ (n : ℝ) ^ (1 - ε) * (c₀ * (n : ℝ) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left h3 hn1ε0
      _ = c₀ * ((n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (ε / 2)) := by ring
      _ = c₀ * (n : ℝ) ^ (1 - ε / 2) := by
          rw [← Real.rpow_add hn0, hexp]
  · -- `(Cup·Cd)² ≤ (δ/2)^{4K₀}·smin`
    rw [show (δ / 2) ^ (4 * K₀) *
        (c₀ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2) =
        ((δ / 2) ^ (4 * K₀) * c₀) * (n : ℝ) ^ (1 - ε / 2) /
          (Real.log n) ^ 2 by ring]
    rw [le_div_iff₀ hsq]
    exact h4
  · -- the scale supplier
    intro m hm
    have hm₁m : c₀ * (n : ℝ) ^ (1 - ε / 2) ≤ (m : ℝ) := le_trans hm₁m₀ hm
    have hf := le_structureScale h6 hm₁m
    have hsminf : c₀ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 ≤
        c₀ * (n : ℝ) ^ (1 - ε / 2) /
          (Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2))) ^ 2 := by
      have hm₁n : c₀ * (n : ℝ) ^ (1 - ε / 2) ≤ (n : ℝ) := by
        calc c₀ * (n : ℝ) ^ (1 - ε / 2)
            ≤ 1 * (n : ℝ) ^ (1 - ε / 2) :=
              mul_le_mul_of_nonneg_right hc₀1
                (Real.rpow_nonneg hn0.le _)
          _ = (n : ℝ) ^ (1 - ε / 2) := one_mul _
          _ ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
          _ = (n : ℝ) := Real.rpow_one _
      have hlm₁ : Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) ≤ Real.log n :=
        Real.log_le_log hm₁pos hm₁n
      have hlm₁2 : (2 : ℝ) ≤ Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) := by
        have h := Real.log_le_log (Real.exp_pos 2) h6
        rwa [Real.log_exp] at h
      have hlm₁0 : (0 : ℝ) ≤ Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) := by
        linarith
      have hsqm₁ : (0 : ℝ) <
          (Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2))) ^ 2 :=
        pow_pos (by linarith) 2
      have hsqle : (Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2))) ^ 2 ≤
          (Real.log n) ^ 2 := pow_le_pow_left₀ hlm₁0 hlm₁ 2
      rw [div_le_div_iff₀ hsq hsqm₁]
      exact mul_le_mul_of_nonneg_left hsqle hm₁pos.le
    have hsminsc : c₀ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 ≤
        structureScale m := le_trans hsminf hf
    refine ⟨?_, hsminsc⟩
    have hsmin1 : (1 : ℝ) ≤
        c₀ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 := by
      rw [le_div_iff₀ hsq, one_mul]
      calc (Real.log n) ^ 2
          = 1 * (Real.log n) ^ 2 := (one_mul _).symm
        _ ≤ prepCinv pkgs Dcap * (Real.log n) ^ 2 :=
            mul_le_mul_of_nonneg_right hCinv1 hsq.le
        _ ≤ c₀ * (n : ℝ) ^ (1 - ε / 2) := h5
    linarith
  · -- `1 ≤ c_r·smin`
    intro r hr
    have hCinvsmin : prepCinv pkgs Dcap ≤
        c₀ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 := by
      rw [le_div_iff₀ hsq]
      exact h5
    calc (1 : ℝ) = (pkgs r).c * (pkgs r).c⁻¹ :=
          (mul_inv_cancel₀ (ne_of_gt (pkgs r).c_pos)).symm
      _ ≤ (pkgs r).c * prepCinv pkgs Dcap :=
          mul_le_mul_of_nonneg_left (le_prepCinv pkgs Dcap hr)
            (pkgs r).c_pos.le
      _ ≤ (pkgs r).c *
            (c₀ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2) :=
          mul_le_mul_of_nonneg_left hCinvsmin (pkgs r).c_pos.le
  · -- `(3·max(1,c_r⁻¹))^{D_r} ≤ Cup`
    intro r hr
    exact le_prepCup pkgs Dcap hr
  · -- the deletion threshold
    intro r hr
    have hlogm : Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) ≤
        Real.log (δ * ((δ / 2) ^ (prepImax pkgs Dcap γ n + E) *
          (n : ℝ))) :=
      Real.log_le_log hm₁pos hm₁m₀
    calc (pkgs r).c⁻¹ ≤ prepCinv pkgs Dcap := le_prepCinv pkgs Dcap hr
      _ ≤ δ / 2 * Real.log (c₀ * (n : ℝ) ^ (1 - ε / 2)) := h7
      _ ≤ δ / 2 *
            Real.log (δ * ((δ / 2) ^ (prepImax pkgs Dcap γ n + E) *
              (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hlogm (by linarith)
  · -- `e ≤ δ·(δ/2)^{imax}·n`
    calc Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ c₀ * (n : ℝ) ^ (1 - ε / 2) := h6
      _ ≤ δ * ((δ / 2) ^ (prepImax pkgs Dcap γ n + E) * (n : ℝ)) := hm₁m₀

/-! ## Final assembly -/

/-- **`PrepSupplier'`, final form** — unconditional.  For any parameters in
the manuscript's regime (`0 < δ ≤ 1`, `0 < γ < 1`, `γ ≤ (δ/2)^{K₀}`,
`40·log(2/δ) ≤ ε·log(1/γ)`, `Dcap ≥ 2/ζ₀ + 10`) there are a constant
`Cdown ≥ 1` and a threshold `n₂` with
`PrepSupplier' pkgs Dcap ζ₀ ε δ γ K₀ Cdown n₁` for every `n₁ ≥ n₂` — no
`hdown1`, no `hout`. -/
theorem prepSupplier'_final {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (ζ₀ ε δ γ K₀ : ℝ)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hK₀ : 0 ≤ K₀)
    (hγK₀ : γ ≤ (δ / 2) ^ K₀)
    (hKε : 40 * Real.log (2 / δ) ≤ ε * Real.log (1 / γ))
    (hDζ : 2 / ζ₀ + 10 ≤ (Dcap : ℝ)) :
    ∃ Cdown : ℝ, 1 ≤ Cdown ∧
      ∃ n₂ : ℕ, ∀ n₁ : ℕ, n₂ ≤ n₁ →
        PrepSupplier' pkgs Dcap ζ₀ ε δ γ K₀ Cdown n₁ := by
  obtain ⟨C, hC0, hCstep⟩ := prep_step_uniform pkgs Dcap
  set Cd : ℝ := max 1 (C * prepCinv pkgs Dcap ^ Dcap) with hCddef
  have hCd1 : 1 ≤ Cd := le_max_left _ _
  obtain ⟨n₂, hnum⟩ := prepNumerics'_of_large pkgs Dcap ζ₀ ε δ γ K₀ Cd
    hζ₀ hδ0 hδ1 hγ0 hγ1 hε0 hε1 hCd1 hγK₀ hKε hDζ
  refine ⟨Cd ^ Dcap, one_le_pow₀ hCd1, n₂, fun n₁ hn₁ => ?_⟩
  refine prepSupplier'_of_numerics pkgs Dcap ζ₀ ε δ γ K₀ C Cd n₁
    hζ₀ hδ0 hδ1 hγ0 hγ1 hK₀ hCd1 ?_ ?_ ?_
  · intro X s hdim hnot hsupply
    exact hCstep X δ γ s hdim hnot hsupply
  · intro X x y hdim hmove hlt
    have h := prepMove_down_box_le (Dcap := Dcap) hC0 hdim hmove hlt
    rwa [← hCddef] at h
  · intro n d₀ B₀ hn hbadB hnB hd hdd
    exact hnum n d₀ B₀ (le_trans hn₁ hn) hbadB hnB hd hdd

/-- **Consumption-shaped corollary, primed and unconditional** —
`prepSupplier_params` minus its two hypothesis-clauses, with `δ` a *free*
parameter (`0 < δ ≤ 1/2`) and the down constant `Cdown` exposed.  `Dcap` is
an *input* (fixed upstream); besides `Dcap ≥ max(2, 2/ζ₀)` the proof needs
the up-move headroom `2/ζ₀ + 10 ≤ Dcap` (`hslack`): chains make at most
`Ucap = 10` up-moves from stages of dimension `≤ 2/ζ₀`, and the structural
package bounds are consumed at every intermediate dimension.

Parameter choices: `ε = min(ε₁/2, 1/4)`, `K₀ = 5`,
`γ = (δ/2)^K` with `K = max 5 ⌈40/ε⌉`, so the regime clauses
`γ ≤ (δ/2)^{K₀}` and `40·log(2/δ) ≤ ε·log(1/γ) = ε·K·log(2/δ)` hold for
every `0 < δ ≤ 1/2`. -/
theorem prepSupplier'_params {β : ℝ} (pkgs : ∀ r, Package r β)
    (Dcap : ℕ) (ζ₀ ε₁ δ : ℝ)
    (hDcap2 : 2 ≤ Dcap) (hDcapζ : 2 / ζ₀ ≤ (Dcap : ℝ))
    (hslack : 2 / ζ₀ + 10 ≤ (Dcap : ℝ))
    (hζ₀ : 0 < ζ₀) (hε₁ : 0 < ε₁) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ ε γ K₀ Cdown : ℝ,
      0 < ε ∧ 2 * ε ≤ ε₁ ∧ ε < 1 / 2 ∧ (5 : ℝ) ≤ K₀ ∧
      0 < γ ∧ γ < 1 ∧ 1 ≤ Cdown ∧
      ∃ n₂ : ℕ, ∀ n₁ : ℕ, n₂ ≤ n₁ →
        PrepSupplier' pkgs Dcap ζ₀ ε δ γ K₀ Cdown n₁ := by
  set ε : ℝ := min (ε₁ / 2) (1 / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε14 : ε ≤ 1 / 4 := min_le_right _ _
  have hεhalf : ε < 1 / 2 := by linarith
  have hε1' : ε < 1 := by linarith
  set K : ℕ := max 5 ⌈40 / ε⌉₊ with hKdef
  set γ : ℝ := (δ / 2) ^ K with hγdef
  have hδ2pos : (0 : ℝ) < δ / 2 := by linarith
  have hδ2lt1 : δ / 2 < 1 := by linarith
  have hγ0 : 0 < γ := by
    rw [hγdef]
    positivity
  have hK5 : (5 : ℕ) ≤ K := le_max_left _ _
  have hγ1 : γ < 1 := by
    rw [hγdef]
    exact pow_lt_one₀ hδ2pos.le hδ2lt1 (by omega)
  have h2δ : (1 : ℝ) < 2 / δ := by
    rw [lt_div_iff₀ hδ0]; linarith
  have hlog2δ : (0 : ℝ) < Real.log (2 / δ) := Real.log_pos h2δ
  have hinvγ : (1 : ℝ) / γ = (2 / δ) ^ K := by
    rw [hγdef, one_div, ← inv_pow, inv_div]
  have hlogγ : Real.log (1 / γ) = (K : ℝ) * Real.log (2 / δ) := by
    rw [hinvγ, Real.log_pow]
  have hK40 : 40 / ε ≤ (K : ℝ) := by
    calc (40 : ℝ) / ε ≤ (⌈40 / ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (K : ℝ) := by exact_mod_cast le_max_right 5 ⌈40 / ε⌉₊
  have hγK₀ : γ ≤ (δ / 2) ^ (5 : ℝ) := by
    rw [show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      hγdef]
    exact pow_le_pow_of_le_one hδ2pos.le (by linarith) hK5
  have hKε : 40 * Real.log (2 / δ) ≤ ε * Real.log (1 / γ) := by
    rw [hlogγ]
    have h2 : (40 : ℝ) ≤ ε * K := by
      have h3 : ε * (40 / ε) ≤ ε * K :=
        mul_le_mul_of_nonneg_left hK40 hε0.le
      rw [mul_div_cancel₀ _ (ne_of_gt hε0)] at h3
      linarith
    calc 40 * Real.log (2 / δ) ≤ (ε * K) * Real.log (2 / δ) :=
          mul_le_mul_of_nonneg_right h2 hlog2δ.le
      _ = ε * ((K : ℝ) * Real.log (2 / δ)) := by ring
  obtain ⟨Cdown, hCdown1, n₂, hsup⟩ :=
    prepSupplier'_final pkgs Dcap ζ₀ ε δ γ 5
      hζ₀ hδ0 (by linarith) hγ0 hγ1 hε0 hε1' (by norm_num) hγK₀ hKε hslack
  refine ⟨ε, γ, 5, Cdown, hε0, ?_, hεhalf, le_refl _, hγ0, hγ1, hCdown1,
    n₂, hsup⟩
  rw [hεdef]
  have h := min_le_left (ε₁ / 2) (1 / 4 : ℝ)
  linarith

end Nondividing
