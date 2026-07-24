import Nondividing.ProjectiveTheorem

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# Toward `PrepSupplier`: the preprocessing-chain numerics

This file discharges the preprocessing supplier `PrepSupplier`
(ProjectiveTheorem.lean) from the E1 package machinery
(`prep_step`, `PrepMove`, `PrepChain`) by closing the manuscript's
eligibility/cutoff/γ-power accounting (Manuscript.tex 560–660) over the
`PrepChain` toolkit.

The key structural difficulty is a *circularity* in the
reachability-relative hypotheses of `unshifted_preprocessing_toward`: the
numeric thresholds (scale floors, deletion bounds) at a stage need a
cardinality lower bound there, which needs the per-move retention at all
earlier stages, which needs the thresholds again.  The manuscript resolves
this by simultaneous induction along the iteration; here we do the same via
*chain-relative* estimates: a step predicate `GoodStep` recording the
per-move facts, the master product estimate and count caps for chains all
of whose steps are good (`box_master_stepsOK`, `pow_upSum_le_stepsOK`,
`shrink_cap_stepsOK`, `card_retention_stepsOK`), and a fuel-based descent
(`exists_irreducible_chain_stepsOK`) that *maintains* goodness: the numeric
facts needed to extend a good chain by one more move are derived from the
product estimate applied to the good chain built so far.

Everything here only *adds* declarations; no existing file is modified.
-/

namespace PrepChain

variable {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β} {δ γ C : ℝ}

/-! ## Chain length, `snoc`, and per-step predicates -/

/-- The number of moves in a chain (the manuscript's iteration count `i`). -/
def length : ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ _ _ _ rest => length rest + 1

@[simp] theorem length_nil (s : PrepStage X) :
    (PrepChain.nil (pkgs := pkgs) (δ := δ) (γ := γ) (C := C) s).length = 0 :=
  rfl

/-- Every move is exactly one of shrink/up/down:
`i = |𝒮| + |𝒰| + |𝒟|`. -/
theorem length_eq_counts : ∀ {a b : PrepStage X}
    (ch : PrepChain pkgs δ γ C a b),
    ch.length = ch.shrinkCount + ch.upCount + ch.downCount
  | _, _, .nil _ => rfl
  | _, _, .cons s t u h rest => by
      have ih := length_eq_counts rest
      simp only [length, shrinkCount, upCount, downCount]
      rcases Nat.lt_trichotomy t.dim s.dim with h1 | h1 | h1
      · rw [if_neg (by omega : ¬ t.dim = s.dim),
          if_neg (by omega : ¬ s.dim < t.dim), if_pos h1]
        omega
      · rw [if_pos h1, if_neg (by omega : ¬ s.dim < t.dim),
          if_neg (by omega : ¬ t.dim < s.dim)]
        omega
      · rw [if_neg (by omega : ¬ t.dim = s.dim), if_pos h1,
          if_neg (by omega : ¬ t.dim < s.dim)]
        omega

/-- Append a move at the *end* of a chain. -/
def snoc : ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b →
    ∀ {c : PrepStage X}, PrepMove pkgs δ γ C b c → PrepChain pkgs δ γ C a c
  | _, _, .nil s, c, h => .cons s c c h (.nil c)
  | _, _, .cons s t _ hm rest, c, h => .cons s t c hm (snoc rest h)

theorem length_snoc : ∀ {a b : PrepStage X}
    (ch : PrepChain pkgs δ γ C a b) {c : PrepStage X}
    (h : PrepMove pkgs δ γ C b c), (ch.snoc h).length = ch.length + 1
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons s t u hm rest, c, h => by
      simp only [snoc, length, length_snoc rest h]

/-- All steps of a chain satisfy the binary predicate `Q`. -/
def StepsOK (Q : PrepStage X → PrepStage X → Prop) :
    ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons s t _ _ rest => Q s t ∧ StepsOK Q rest

@[simp] theorem stepsOK_nil (Q : PrepStage X → PrepStage X → Prop)
    (s : PrepStage X) :
    (PrepChain.nil (pkgs := pkgs) (δ := δ) (γ := γ) (C := C) s).StepsOK Q :=
  trivial

theorem StepsOK.snoc {Q : PrepStage X → PrepStage X → Prop} :
    ∀ {a b : PrepStage X} {ch : PrepChain pkgs δ γ C a b}
      {c : PrepStage X} {h : PrepMove pkgs δ γ C b c},
      ch.StepsOK Q → Q b c → (ch.snoc h).StepsOK Q
  | _, _, .nil _, _, _, _, hQ => ⟨hQ, trivial⟩
  | _, _, .cons _ _ _ _ rest, _, h, hOK, hQ =>
      ⟨hOK.1, StepsOK.snoc (ch := rest) (h := h) hOK.2 hQ⟩

/-- The endpoint dimension is at most the start dimension plus the summed
up-move increase. -/
theorem dim_le {a b : PrepStage X} (ch : PrepChain pkgs δ γ C a b) :
    b.dim ≤ a.dim + ch.upSum := by
  have := ch.dim_add_downSum_eq
  omega

end PrepChain

/-! ## The step predicate and the chain-relative master estimates -/

/-- **Good step**: the per-move numeric facts the manuscript proves
inductively along the iteration — cardinality retention `|V'| ≥ (δ/2)|V|`,
the up-move box decay at scale floor `smin`, and the down-move box bound
with constant `Cdown`. -/
def GoodStep {X : ℕ} (δ smin Cup Cdown : ℝ) (x y : PrepStage X) : Prop :=
  δ / 2 * (x.V.card : ℝ) ≤ (y.V.card : ℝ) ∧
    (x.dim < y.dim →
      smin ^ (y.dim - x.dim) * ((coordinateBox y.M).card : ℝ) ≤
        Cup * ((coordinateBox x.M).card : ℝ)) ∧
    (y.dim < x.dim →
      ((coordinateBox y.M).card : ℝ) ≤
        Cdown * ((coordinateBox x.M).card : ℝ))

namespace PrepChain

variable {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β} {δ γ C : ℝ}
variable {smin Cup Cdown : ℝ}

/-- **Chain-relative master box estimate** (`eq:unshifted-product`): if every
step of the chain is good, the per-move bounds telescope to
`smin^U·|B_end| ≤ γ^{|𝒮|}·Cup^{|𝒰|}·Cdown^{|𝒟|}·|B_start|`.  Unlike
`box_master`, the hypotheses are required only *at the steps of the chain*
(this is what breaks the manuscript's threshold circularity). -/
theorem box_master_stepsOK (hγ0 : 0 < γ) (hCup : 0 < Cup)
    (hCdown : 0 < Cdown) (hs1 : 1 ≤ smin) :
    ∀ {a b : PrepStage X} (ch : PrepChain pkgs δ γ C a b),
      ch.StepsOK (GoodStep δ smin Cup Cdown) →
      smin ^ ch.upSum * ((coordinateBox b.M).card : ℝ) ≤
        γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cdown ^ ch.downCount *
          ((coordinateBox a.M).card : ℝ) := by
  intro a b ch
  induction ch with
  | nil s =>
      intro _
      simp [upSum, shrinkCount, upCount, downCount]
  | cons s t u h rest ih =>
      intro hOK
      obtain ⟨⟨_, hupQ, hdownQ⟩, hrest⟩ := hOK
      have IH := ih hrest
      have hsmin0 : (0 : ℝ) < smin := lt_of_lt_of_le one_pos hs1
      have hΓ : (0 : ℝ) ≤ γ ^ rest.shrinkCount * Cup ^ rest.upCount *
          Cdown ^ rest.downCount := by positivity
      rcases Nat.lt_trichotomy t.dim s.dim with hlt | heq | hgt
      · -- down move
        have hbnd := hdownQ hlt
        simp only [upSum, shrinkCount, upCount, downCount]
        rw [show t.dim - s.dim = 0 from by omega,
          if_neg (show ¬t.dim = s.dim from by omega),
          if_neg (show ¬s.dim < t.dim from by omega), if_pos hlt]
        simp only [Nat.zero_add, pow_add, pow_one]
        calc smin ^ rest.upSum * ((coordinateBox u.M).card : ℝ)
            ≤ γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                Cdown ^ rest.downCount * ((coordinateBox t.M).card : ℝ) := IH
          _ ≤ γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                Cdown ^ rest.downCount *
                (Cdown * ((coordinateBox s.M).card : ℝ)) :=
              mul_le_mul_of_nonneg_left hbnd hΓ
          _ = γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                (Cdown * Cdown ^ rest.downCount) *
                ((coordinateBox s.M).card : ℝ) := by ring
      · -- shrink move
        have hbnd := (PrepMove.box_shrink h heq).le
        simp only [upSum, shrinkCount, upCount, downCount]
        rw [show t.dim - s.dim = 0 from by omega, if_pos heq,
          if_neg (show ¬s.dim < t.dim from by omega),
          if_neg (show ¬t.dim < s.dim from by omega)]
        simp only [Nat.zero_add, pow_add, pow_one]
        calc smin ^ rest.upSum * ((coordinateBox u.M).card : ℝ)
            ≤ γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                Cdown ^ rest.downCount * ((coordinateBox t.M).card : ℝ) := IH
          _ ≤ γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                Cdown ^ rest.downCount *
                (γ * ((coordinateBox s.M).card : ℝ)) :=
              mul_le_mul_of_nonneg_left hbnd hΓ
          _ = γ * γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                Cdown ^ rest.downCount * ((coordinateBox s.M).card : ℝ) := by
              ring
      · -- up move
        have hbnd := hupQ hgt
        simp only [upSum, shrinkCount, upCount, downCount]
        rw [if_neg (show ¬t.dim = s.dim from by omega), if_pos hgt,
          if_neg (show ¬t.dim < s.dim from by omega)]
        simp only [Nat.zero_add, pow_add, pow_one]
        calc smin ^ (t.dim - s.dim) * smin ^ rest.upSum *
              ((coordinateBox u.M).card : ℝ)
            = smin ^ (t.dim - s.dim) *
                (smin ^ rest.upSum * ((coordinateBox u.M).card : ℝ)) := by
              ring
          _ ≤ smin ^ (t.dim - s.dim) *
                (γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                  Cdown ^ rest.downCount *
                  ((coordinateBox t.M).card : ℝ)) :=
              mul_le_mul_of_nonneg_left IH (by positivity)
          _ = γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                Cdown ^ rest.downCount *
                (smin ^ (t.dim - s.dim) *
                  ((coordinateBox t.M).card : ℝ)) := by ring
          _ ≤ γ ^ rest.shrinkCount * Cup ^ rest.upCount *
                Cdown ^ rest.downCount *
                (Cup * ((coordinateBox s.M).card : ℝ)) :=
              mul_le_mul_of_nonneg_left hbnd hΓ
          _ = γ ^ rest.shrinkCount * (Cup * Cup ^ rest.upCount) *
                Cdown ^ rest.downCount *
                ((coordinateBox s.M).card : ℝ) := by ring

/-- **Chain-relative cardinality retention**: good steps compose to
`|V_end| ≥ (δ/2)^i·|V_start|` (the manuscript's `|A_i| ≥ δ_*^i n`). -/
theorem card_retention_stepsOK (hδ0 : 0 ≤ δ) :
    ∀ {a b : PrepStage X} (ch : PrepChain pkgs δ γ C a b),
      ch.StepsOK (GoodStep δ smin Cup Cdown) →
      (δ / 2) ^ ch.length * (a.V.card : ℝ) ≤ (b.V.card : ℝ) := by
  intro a b ch
  induction ch with
  | nil s =>
      intro _
      simp [length]
  | cons s t u h rest ih =>
      intro hOK
      obtain ⟨⟨hcard, _, _⟩, hrest⟩ := hOK
      have IH := ih hrest
      have hδ2 : (0 : ℝ) ≤ δ / 2 := by linarith
      calc (δ / 2) ^ (rest.length + 1) * (s.V.card : ℝ)
          = (δ / 2) ^ rest.length * (δ / 2 * (s.V.card : ℝ)) := by ring
        _ ≤ (δ / 2) ^ rest.length * (t.V.card : ℝ) :=
            mul_le_mul_of_nonneg_left hcard (by positivity)
        _ ≤ (u.V.card : ℝ) := IH

/-- **Chain-relative net-up box estimate**: the box decays by the *net* scale
power `smin^{dim_end − dim_start}`. -/
theorem box_master_net_up_stepsOK (hγ0 : 0 < γ) (hCup : 0 < Cup)
    (hCdown : 0 < Cdown) (hs1 : 1 ≤ smin)
    {a b : PrepStage X} (ch : PrepChain pkgs δ γ C a b)
    (hOK : ch.StepsOK (GoodStep δ smin Cup Cdown)) :
    smin ^ (b.dim - a.dim) * ((coordinateBox b.M).card : ℝ) ≤
      γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cdown ^ ch.downCount *
        ((coordinateBox a.M).card : ℝ) := by
  have hmaster := box_master_stepsOK hγ0 hCup hCdown hs1 ch hOK
  have hpow : smin ^ (b.dim - a.dim) ≤ smin ^ ch.upSum :=
    pow_le_pow_right₀ hs1 ch.le_upSum
  calc smin ^ (b.dim - a.dim) * ((coordinateBox b.M).card : ℝ)
      ≤ smin ^ ch.upSum * ((coordinateBox b.M).card : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ ≤ γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cdown ^ ch.downCount *
        ((coordinateBox a.M).card : ℝ) := hmaster

end PrepChain

/-- Exponent cap from a power sandwich: `T^U ≤ R < T^{k+1}` with `T > 1`
forces `U ≤ k`. -/
theorem pow_exponent_cap {T R : ℝ} {U k : ℕ} (hT : 1 < T)
    (h : T ^ U ≤ R) (hR : R < T ^ (k + 1)) : U ≤ k := by
  by_contra hcon
  push Not at hcon
  have : T ^ (k + 1) ≤ T ^ U := pow_le_pow_right₀ hT.le hcon
  linarith

namespace PrepChain

variable {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β} {δ γ C : ℝ}
variable {smin Cup Cdown : ℝ}

/-- **Chain-relative total-up-move bound** (Manuscript.tex 587–607): with a
scale floor `smin ≥ Cup·Cdown·T`, the summed up-move increase obeys
`T^U ≤ Cdown^{d₀}·|B_start|`. -/
theorem pow_upSum_le_stepsOK {T : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hCup : 1 ≤ Cup) (hCdown : 1 ≤ Cdown)
    (hT : 1 ≤ T) (hsmin : Cup * Cdown * T ≤ smin)
    {a b : PrepStage X} (ch : PrepChain pkgs δ γ C a b)
    (hOK : ch.StepsOK (GoodStep δ smin Cup Cdown)) :
    T ^ ch.upSum ≤ Cdown ^ a.dim * ((coordinateBox a.M).card : ℝ) := by
  have hCup0 : (0 : ℝ) < Cup := lt_of_lt_of_le one_pos hCup
  have hCdown0 : (0 : ℝ) < Cdown := lt_of_lt_of_le one_pos hCdown
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have h11 : (1 : ℝ) ≤ Cup * Cdown := by nlinarith
  have h12 : (1 : ℝ) ≤ Cup * Cdown * T := by nlinarith
  have hs1 : (1 : ℝ) ≤ smin := by linarith
  have hmaster := box_master_stepsOK hγ0 hCup0 hCdown0 hs1 ch hOK
  have hBb : (1 : ℝ) ≤ ((coordinateBox b.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox b.M
  have hBa : (0 : ℝ) ≤ ((coordinateBox a.M).card : ℝ) := Nat.cast_nonneg _
  have h1 : smin ^ ch.upSum ≤
      Cup ^ ch.upCount * Cdown ^ ch.downCount *
        ((coordinateBox a.M).card : ℝ) := by
    have hγS : γ ^ ch.shrinkCount ≤ 1 := pow_le_one₀ hγ0.le hγ1
    have hstep : smin ^ ch.upSum * 1 ≤ smin ^ ch.upSum *
        ((coordinateBox b.M).card : ℝ) :=
      mul_le_mul_of_nonneg_left hBb (by positivity)
    rw [mul_one] at hstep
    have hdropγ : γ ^ ch.shrinkCount * Cup ^ ch.upCount *
        Cdown ^ ch.downCount * ((coordinateBox a.M).card : ℝ) ≤
        1 * Cup ^ ch.upCount * Cdown ^ ch.downCount *
          ((coordinateBox a.M).card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hBa
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hγS (by positivity)
    calc smin ^ ch.upSum
        ≤ smin ^ ch.upSum * ((coordinateBox b.M).card : ℝ) := hstep
      _ ≤ γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cdown ^ ch.downCount *
            ((coordinateBox a.M).card : ℝ) := hmaster
      _ ≤ 1 * Cup ^ ch.upCount * Cdown ^ ch.downCount *
            ((coordinateBox a.M).card : ℝ) := hdropγ
      _ = Cup ^ ch.upCount * Cdown ^ ch.downCount *
            ((coordinateBox a.M).card : ℝ) := by ring
  have h2 : Cup ^ ch.upCount ≤ Cup ^ ch.upSum :=
    pow_le_pow_right₀ hCup ch.upCount_le_upSum
  have h3 : Cdown ^ ch.downCount ≤ Cdown ^ (a.dim + ch.upSum) :=
    pow_le_pow_right₀ hCdown ch.downCount_le
  have h4 : smin ^ ch.upSum ≤
      Cup ^ ch.upSum * Cdown ^ (a.dim + ch.upSum) *
        ((coordinateBox a.M).card : ℝ) := by
    calc smin ^ ch.upSum
        ≤ Cup ^ ch.upCount * Cdown ^ ch.downCount *
            ((coordinateBox a.M).card : ℝ) := h1
      _ ≤ Cup ^ ch.upSum * Cdown ^ (a.dim + ch.upSum) *
            ((coordinateBox a.M).card : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hBa
          exact mul_le_mul h2 h3 (by positivity) (by positivity)
  have h5 : (Cup * Cdown * T) ^ ch.upSum ≤ smin ^ ch.upSum :=
    pow_le_pow_left₀ (by positivity) hsmin _
  have h6 : (Cup * Cdown * T) ^ ch.upSum =
      Cup ^ ch.upSum * Cdown ^ ch.upSum * T ^ ch.upSum := by
    rw [mul_pow, mul_pow]
  have h7 : Cdown ^ (a.dim + ch.upSum) =
      Cdown ^ a.dim * Cdown ^ ch.upSum := pow_add _ _ _
  have key : Cup ^ ch.upSum * Cdown ^ ch.upSum * T ^ ch.upSum ≤
      Cup ^ ch.upSum * Cdown ^ ch.upSum *
        (Cdown ^ a.dim * ((coordinateBox a.M).card : ℝ)) := by
    calc Cup ^ ch.upSum * Cdown ^ ch.upSum * T ^ ch.upSum
        = (Cup * Cdown * T) ^ ch.upSum := h6.symm
      _ ≤ smin ^ ch.upSum := h5
      _ ≤ Cup ^ ch.upSum * Cdown ^ (a.dim + ch.upSum) *
            ((coordinateBox a.M).card : ℝ) := h4
      _ = Cup ^ ch.upSum * Cdown ^ ch.upSum *
            (Cdown ^ a.dim * ((coordinateBox a.M).card : ℝ)) := by
          rw [h7]; ring
  exact le_of_mul_le_mul_left key (by positivity)

/-- **Chain-relative shrink cap** (the γ-power accounting): since the final
box is nonempty, `(1/γ)^{|𝒮|} ≤ Cup^{|𝒰|}·Cdown^{|𝒟|}·|B_start|` — this is
what bounds the *iteration count* in terms of `log|B₀|/log(1/γ)`. -/
theorem shrink_cap_stepsOK (hγ0 : 0 < γ)
    (hCup : 0 < Cup) (hCdown : 0 < Cdown) (hs1 : 1 ≤ smin)
    {a b : PrepStage X} (ch : PrepChain pkgs δ γ C a b)
    (hOK : ch.StepsOK (GoodStep δ smin Cup Cdown)) :
    (1 / γ) ^ ch.shrinkCount ≤
      Cup ^ ch.upCount * Cdown ^ ch.downCount *
        ((coordinateBox a.M).card : ℝ) := by
  have hmaster := box_master_stepsOK hγ0 hCup hCdown hs1 ch hOK
  have hBb : (1 : ℝ) ≤ ((coordinateBox b.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox b.M
  have hsminU : (1 : ℝ) ≤ smin ^ ch.upSum := one_le_pow₀ hs1
  have h1 : (1 : ℝ) ≤ γ ^ ch.shrinkCount *
      (Cup ^ ch.upCount * Cdown ^ ch.downCount *
        ((coordinateBox a.M).card : ℝ)) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ smin ^ ch.upSum * ((coordinateBox b.M).card : ℝ) :=
          mul_le_mul hsminU hBb one_pos.le (by positivity)
      _ ≤ γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cdown ^ ch.downCount *
            ((coordinateBox a.M).card : ℝ) := hmaster
      _ = γ ^ ch.shrinkCount *
            (Cup ^ ch.upCount * Cdown ^ ch.downCount *
              ((coordinateBox a.M).card : ℝ)) := by ring
  have hγS : (0 : ℝ) < γ ^ ch.shrinkCount := by positivity
  have hinv : (1 / γ) ^ ch.shrinkCount * γ ^ ch.shrinkCount = 1 := by
    rw [← mul_pow, one_div_mul_cancel (ne_of_gt hγ0), one_pow]
  calc (1 / γ) ^ ch.shrinkCount
      = (1 / γ) ^ ch.shrinkCount * 1 := (mul_one _).symm
    _ ≤ (1 / γ) ^ ch.shrinkCount *
          (γ ^ ch.shrinkCount *
            (Cup ^ ch.upCount * Cdown ^ ch.downCount *
              ((coordinateBox a.M).card : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((1 / γ) ^ ch.shrinkCount * γ ^ ch.shrinkCount) *
          (Cup ^ ch.upCount * Cdown ^ ch.downCount *
            ((coordinateBox a.M).card : ℝ)) := by ring
    _ = Cup ^ ch.upCount * Cdown ^ ch.downCount *
          ((coordinateBox a.M).card : ℝ) := by rw [hinv, one_mul]

end PrepChain

/-! ## The invariant-carrying descent -/

/-- **Fuel-based descent to an irreducible stage along a good chain.**  If
every good chain has length at most `imax` (the γ-power accounting), and
from every non-irreducible endpoint of a good chain a move preserving
goodness is available (the E1 one-step lemma plus the derived thresholds),
then some good chain ends at an unshiftedly irreducible stage.  No
termination measure is needed: the length cap itself terminates the
recursion. -/
theorem exists_irreducible_chain_stepsOK {X : ℕ} {β : ℝ}
    {pkgs : ∀ r, Package r β} {δ γ C : ℝ}
    {Q : PrepStage X → PrepStage X → Prop} {imax : ℕ} (s₀ : PrepStage X)
    (hcap : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s₀ t),
      ch.StepsOK Q → ch.length ≤ imax)
    (hstep : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s₀ t),
      ch.StepsOK Q → ¬ StageIrreducible pkgs δ γ t →
      ∃ (u : PrepStage X) (_ : PrepMove pkgs δ γ C t u), Q t u) :
    ∃ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s₀ t),
      ch.StepsOK Q ∧ StageIrreducible pkgs δ γ t := by
  suffices key : ∀ (f : ℕ) (t : PrepStage X)
      (ch : PrepChain pkgs δ γ C s₀ t), ch.StepsOK Q →
      imax ≤ ch.length + f →
      ∃ (t' : PrepStage X) (ch' : PrepChain pkgs δ γ C s₀ t'),
        ch'.StepsOK Q ∧ StageIrreducible pkgs δ γ t' by
    refine key imax s₀ (.nil s₀) (PrepChain.stepsOK_nil Q s₀) ?_
    simp
  intro f
  induction f with
  | zero =>
      intro t ch hOK hlen
      by_cases hirr : StageIrreducible pkgs δ γ t
      · exact ⟨t, ch, hOK, hirr⟩
      · obtain ⟨u, h, hQ⟩ := hstep t ch hOK hirr
        have hOK' : (ch.snoc h).StepsOK Q := hOK.snoc hQ
        have hc := hcap u (ch.snoc h) hOK'
        rw [PrepChain.length_snoc] at hc
        omega
  | succ f ih =>
      intro t ch hOK hlen
      by_cases hirr : StageIrreducible pkgs δ γ t
      · exact ⟨t, ch, hOK, hirr⟩
      · obtain ⟨u, h, hQ⟩ := hstep t ch hOK hirr
        refine ih u (ch.snoc h) (hOK.snoc hQ) ?_
        rw [PrepChain.length_snoc]
        omega

end Nondividing
