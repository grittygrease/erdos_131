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

/-! ## The per-stage master theorem -/

/-- **Single-stage preprocessing supplier step** (the body of `PrepSupplier`
at one excessive stage, from the chain numerics).  Given the numeric
threshold package for the stage's cardinality `n = |V|` — the constants
`smin, Cup, T` with the U-cap/shrink-cap drivers, the retention/ρ-power
inequalities, the scale/deletion suppliers, and the one-step move lemma
`hCstep` (from `prep_step`) — the invariant descent reaches an unshiftedly
`(δ,γ)`-irreducible stage along a good chain, and the chain accounting
delivers exactly the up/down/same-dimension disjunction of `PrepSupplier`.

Two hypotheses are `TODO(orchestrator)` inputs (see the file docstring of
the final assembly below):

* `hdown1` — the *sharp down-move box estimate* `|B'| ≤ |B|` (the manuscript
  only proves `|B'| ≪ C·|B|`, cf. `dimension_move`; `PrepSupplier`'s
  down-branch demands the clean inequality);
* `hn₁out` — the *uniform output threshold* `n₁ ≤ (δ/2)^{imax}·n` (false for
  `n` close to `n₁`; the manuscript instead tracks a shrinking threshold
  along the descent). -/
theorem prep_supplier_step {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    (Dcap : ℕ) {ζ₀ ε δ γ K₀ : ℝ} {n₁ : ℕ} {C : ℝ} (s : PrepStage X)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hK₀ : 0 ≤ K₀) (hbad : ExcessiveStage ζ₀ s)
    {smin Cup T : ℝ} {Ucap Scap imax : ℕ}
    (hCup : 1 ≤ Cup) (hT : 1 < T) (hsminT : Cup * T ≤ smin)
    (hUcapT : ((coordinateBox s.M).card : ℝ) < T ^ (Ucap + 1))
    (hScapγ : Cup ^ Ucap * ((coordinateBox s.M).card : ℝ) <
      (1 / γ) ^ (Scap + 1))
    (himax : Scap + 2 * Ucap + s.dim ≤ imax)
    (hdimD : s.dim + Ucap ≤ Dcap)
    (hρε : (s.V.card : ℝ) ^ (-ε) ≤ (δ / 2) ^ imax)
    (hn₁out : (n₁ : ℝ) ≤ (δ / 2) ^ imax * (s.V.card : ℝ))
    (hupbox : (s.V.card : ℝ) ^ (1 - ε) * Cup ^ Ucap ≤ smin)
    (hγK₀ : γ ≤ (δ / 2) ^ K₀)
    (hsminK₀ : Cup ≤ (δ / 2) ^ (2 * K₀) * smin)
    (hscale : ∀ m : ℕ, δ * ((δ / 2) ^ imax * (s.V.card : ℝ)) ≤ (m : ℝ) →
      1 ≤ structureScale m ∧ smin ≤ structureScale m)
    (hcsmin : ∀ r, r ≤ Dcap → 1 ≤ (pkgs r).c * smin)
    (hCupB : ∀ r, r ≤ Dcap →
      ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D ≤ Cup)
    (hdel : ∀ r, r ≤ Dcap →
      (pkgs r).c⁻¹ ≤ δ / 2 *
        Real.log (δ * ((δ / 2) ^ imax * (s.V.card : ℝ))))
    (hexp1 : Real.exp 1 ≤ δ * ((δ / 2) ^ imax * (s.V.card : ℝ)))
    (hdown1 : ∀ x y : PrepStage X, PrepMove pkgs δ γ C x y →
      y.dim < x.dim → (coordinateBox y.M).card ≤ (coordinateBox x.M).card)
    (hCstep : ∀ t : PrepStage X, t.dim ≤ Dcap →
      ¬ StageIrreducible pkgs δ γ t →
      (∀ Dw : Finset (Fin t.dim → ℤ), Dw ⊆ t.V →
        δ * (t.V.card : ℝ) ≤ (Dw.card : ℝ) →
        ∀ _hE : Eligible β (pkgs t.dim).m₀ Dw t.M,
        1 ≤ structureScale Dw.card ∧
          1 ≤ (pkgs t.dim).c * structureScale Dw.card) →
      ∃ t', PrepMove pkgs δ γ C t t') :
    ∃ s' : PrepStage X, n₁ ≤ s'.V.card ∧
      ((s.dim < s'.dim ∧ s'.dim ≤ Dcap ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            (s.V.card : ℝ) ^ (1 / (sigma s.dim + stageExcess s) -
              (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)))) ∨
        (s'.dim < s.dim ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          (coordinateBox s'.M).card ≤ (coordinateBox s.M).card) ∨
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
  have hsmin1 : (1 : ℝ) < smin := by nlinarith
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
  -- The step predicate: retention + up-decay at floor `smin` + down with
  -- constant `1` (the sharp bound, from `hdown1`).
  set Q : PrepStage X → PrepStage X → Prop := GoodStep δ smin Cup 1
    with hQdef
  -- U-cap along good chains.
  have hUcapCh : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → ch.upSum ≤ Ucap := by
    intro t ch hOK
    have h1 := PrepChain.pow_upSum_le_stepsOK (Cdown := 1) hγ0 hγ1.le hCup
      le_rfl hT.le (by rwa [mul_one]) ch hOK
    rw [one_pow, one_mul] at h1
    exact pow_exponent_cap hT h1 hUcapT
  -- Length cap along good chains (the γ-power accounting).
  have hlencap : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → ch.length ≤ imax := by
    intro t ch hOK
    have hU := hUcapCh t ch hOK
    have huc : ch.upCount ≤ ch.upSum := ch.upCount_le_upSum
    have hdc : ch.downCount ≤ s.dim + ch.upSum := ch.downCount_le
    have hS : ch.shrinkCount ≤ Scap := by
      have h1 := PrepChain.shrink_cap_stepsOK (Cdown := 1) hγ0 hCup0
        one_pos hs1 ch hOK
      rw [one_pow, mul_one] at h1
      have h2 : Cup ^ ch.upCount ≤ Cup ^ Ucap :=
        pow_le_pow_right₀ hCup (le_trans huc hU)
      have h3 : (1 / γ) ^ ch.shrinkCount ≤
          Cup ^ Ucap * ((coordinateBox s.M).card : ℝ) :=
        le_trans h1 (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _))
      exact pow_exponent_cap hγinv h3 hScapγ
    rw [ch.length_eq_counts]
    omega
  -- Cardinality floor at endpoints of good chains.
  have hcardfloor : ∀ (t : PrepStage X) (ch : PrepChain pkgs δ γ C s t),
      ch.StepsOK Q → (δ / 2) ^ imax * (s.V.card : ℝ) ≤ (t.V.card : ℝ) := by
    intro t ch hOK
    have h1 := PrepChain.card_retention_stepsOK (Cup := Cup) (Cdown := 1)
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
    have hVt0 : (0 : ℝ) < (t.V.card : ℝ) := by nlinarith
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
    · -- Down-move: the sharp box estimate (documented hypothesis).
      intro hlt
      have h1 := hdown1 t u hu hlt
      have h2 : ((coordinateBox u.M).card : ℝ) ≤
          ((coordinateBox t.M).card : ℝ) := by exact_mod_cast h1
      rw [one_mul]
      exact h2
  -- Run the descent.
  obtain ⟨t, ch, hOK, hirr⟩ :=
    exists_irreducible_chain_stepsOK s hlencap hstepOK
  -- End-of-chain facts.
  have hlen := hlencap t ch hOK
  have hret : (δ / 2) ^ ch.length * (s.V.card : ℝ) ≤ (t.V.card : ℝ) :=
    PrepChain.card_retention_stepsOK (Cup := Cup) (Cdown := 1)
      (smin := smin) hδ0.le ch hOK
  have hVtfloor : (δ / 2) ^ imax * (s.V.card : ℝ) ≤ (t.V.card : ℝ) :=
    hcardfloor t ch hOK
  have hn₁t : n₁ ≤ t.V.card := by
    have h1 : (n₁ : ℝ) ≤ (t.V.card : ℝ) := le_trans hn₁out hVtfloor
    exact_mod_cast h1
  have hUt := hUcapCh t ch hOK
  have huct : ch.upCount ≤ ch.upSum := ch.upCount_le_upSum
  have hCupuc : Cup ^ ch.upCount ≤ Cup ^ Ucap :=
    pow_le_pow_right₀ hCup (le_trans huct hUt)
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
  -- Master box estimate along the chain (with `Cdown = 1`).
  have hmaster : smin ^ ch.upSum * ((coordinateBox t.M).card : ℝ) ≤
      γ ^ ch.shrinkCount * Cup ^ ch.upCount *
        ((coordinateBox s.M).card : ℝ) := by
    have h1 := PrepChain.box_master_stepsOK (Cdown := 1) hγ0 hCup0 one_pos
      hs1 ch hOK
    rwa [one_pow, mul_one] at h1
  -- Case split on the net dimension change.
  rcases Nat.lt_trichotomy t.dim s.dim with hlt | heq | hgt
  · -- DOWN: `|B̃| ≤ |B₀|` from the master estimate (`Cup ≤ smin` absorbs
    -- the up factors; `γ ≤ 1` kills the shrink factors).
    refine ⟨t, hn₁t, Or.inr (Or.inl ⟨hlt, hretε, ?_⟩)⟩
    have hCupsmin : Cup ≤ smin := by nlinarith
    have h1 : Cup ^ ch.upCount ≤ smin ^ ch.upSum :=
      le_trans (pow_le_pow_left₀ hCup0.le hCupsmin _)
        (pow_le_pow_right₀ hs1 huct)
    have h2 : γ ^ ch.shrinkCount * Cup ^ ch.upCount *
        ((coordinateBox s.M).card : ℝ) ≤
        smin ^ ch.upSum * ((coordinateBox s.M).card : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hB₀0.le
      calc γ ^ ch.shrinkCount * Cup ^ ch.upCount
          ≤ 1 * smin ^ ch.upSum :=
            mul_le_mul hγS1 h1 (by positivity) one_pos.le
        _ = smin ^ ch.upSum := one_mul _
    have h3 : smin ^ ch.upSum * ((coordinateBox t.M).card : ℝ) ≤
        smin ^ ch.upSum * ((coordinateBox s.M).card : ℝ) :=
      le_trans hmaster h2
    have h4 : ((coordinateBox t.M).card : ℝ) ≤
        ((coordinateBox s.M).card : ℝ) :=
      le_of_mul_le_mul_left h3 (by positivity)
    exact_mod_cast h4
  · -- SAME DIMENSION: irreducible output with `ρ = (δ/2)^i` bookkeeping.
    refine ⟨t, hn₁t, Or.inr (Or.inr ⟨heq, hirr, ?_⟩)⟩
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
    have hq2 : (δ / 2 : ℝ) ^ (2 * K₀) = q * q := by
      rw [hqdef, ← Real.rpow_add hδ2pos]
      congr 1
      ring
    have hsums : ch.downSum = ch.upSum := by
      have := ch.dim_add_downSum_eq
      omega
    have hdct : ch.downCount ≤ ch.upSum := by
      have := ch.downCount_le_downSum
      omega
    have hCbq : Cup ≤ q * q * smin := by
      rw [hq2] at hsminK₀
      linarith
    have hbq1 : (1 : ℝ) ≤ q * q * smin := le_trans hCup hCbq
    have hkey : γ ^ ch.shrinkCount * Cup ^ ch.upCount ≤
        smin ^ ch.upSum * q ^ ch.length := by
      have hγq : γ ^ ch.shrinkCount ≤ q ^ ch.shrinkCount :=
        pow_le_pow_left₀ hγ0.le hγK₀ _
      have hCupq : Cup ^ ch.upCount ≤ (q * q * smin) ^ ch.upSum := by
        calc Cup ^ ch.upCount ≤ (q * q * smin) ^ ch.upCount :=
              pow_le_pow_left₀ hCup0.le hCbq _
          _ ≤ (q * q * smin) ^ ch.upSum := pow_le_pow_right₀ hbq1 huct
      have hquc : q ^ ch.upSum ≤ q ^ ch.upCount :=
        pow_le_pow_of_le_one hq0.le hq1 huct
      have hqdc : q ^ ch.upSum ≤ q ^ ch.downCount :=
        pow_le_pow_of_le_one hq0.le hq1 hdct
      calc γ ^ ch.shrinkCount * Cup ^ ch.upCount
          ≤ q ^ ch.shrinkCount * (q * q * smin) ^ ch.upSum :=
            mul_le_mul hγq hCupq (by positivity) (by positivity)
        _ = q ^ ch.shrinkCount *
              (q ^ ch.upSum * q ^ ch.upSum * smin ^ ch.upSum) := by
            rw [mul_pow, mul_pow]
        _ ≤ q ^ ch.shrinkCount *
              (q ^ ch.upCount * q ^ ch.downCount * smin ^ ch.upSum) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul hquc hqdc (by positivity) (by positivity)
        _ = smin ^ ch.upSum *
              (q ^ (ch.shrinkCount + ch.upCount + ch.downCount)) := by
            rw [pow_add, pow_add]
            ring
        _ = smin ^ ch.upSum * q ^ ch.length := by
            rw [ch.length_eq_counts]
    have hfinal : smin ^ ch.upSum * ((coordinateBox t.M).card : ℝ) ≤
        smin ^ ch.upSum *
          (q ^ ch.length * ((coordinateBox s.M).card : ℝ)) := by
      calc smin ^ ch.upSum * ((coordinateBox t.M).card : ℝ)
          ≤ γ ^ ch.shrinkCount * Cup ^ ch.upCount *
              ((coordinateBox s.M).card : ℝ) := hmaster
        _ ≤ smin ^ ch.upSum * q ^ ch.length *
              ((coordinateBox s.M).card : ℝ) :=
            mul_le_mul_of_nonneg_right hkey hB₀0.le
        _ = smin ^ ch.upSum *
              (q ^ ch.length * ((coordinateBox s.M).card : ℝ)) := by ring
    have hboxfin : ((coordinateBox t.M).card : ℝ) ≤
        q ^ ch.length * ((coordinateBox s.M).card : ℝ) :=
      le_of_mul_le_mul_left hfinal (by positivity)
    rw [hρK]
    exact hboxfin
  · -- UP: net scale decay gives the manuscript's `|B̃| ≪ n^{-(1-ε)Δ}|B₀|`.
    refine ⟨t, hn₁t, Or.inl ⟨hgt, ?_, hretε, ?_⟩⟩
    · have h1 := ch.dim_le
      omega
    · -- Net-up master estimate.
      have hnet := PrepChain.box_master_net_up_stepsOK (Cdown := 1) hγ0
        hCup0 one_pos hs1 ch hOK
      rw [one_pow, mul_one] at hnet
      have h1 : smin ^ (t.dim - s.dim) * ((coordinateBox t.M).card : ℝ) ≤
          Cup ^ Ucap * ((coordinateBox s.M).card : ℝ) := by
        refine le_trans hnet ?_
        apply mul_le_mul_of_nonneg_right _ hB₀0.le
        calc γ ^ ch.shrinkCount * Cup ^ ch.upCount
            ≤ 1 * Cup ^ Ucap :=
              mul_le_mul hγS1 hCupuc (by positivity) one_pos.le
          _ = Cup ^ Ucap := one_mul _
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
      -- The exponent absorption `Cup^{Ucap}·n^{(1-ε)Δ} ≤ smin^Δ`.
      set nP : ℝ := (s.V.card : ℝ) ^
        ((1 - ε) * ((t.dim : ℝ) - (s.dim : ℝ))) with hnPdef
      have hnP0 : 0 < nP := Real.rpow_pos_of_pos hn0 _
      have hkey : Cup ^ Ucap * nP ≤ smin ^ (t.dim - s.dim) := by
        have hΔ1 : 1 ≤ t.dim - s.dim := by omega
        have e1 : nP = ((s.V.card : ℝ) ^ (1 - ε)) ^ (t.dim - s.dim) := by
          rw [hnPdef, ← hΔcast, ← Real.rpow_natCast
            ((s.V.card : ℝ) ^ (1 - ε)) (t.dim - s.dim),
            ← Real.rpow_mul hn0.le]
        have hnε0 : (0 : ℝ) ≤ (s.V.card : ℝ) ^ (1 - ε) :=
          Real.rpow_nonneg hn0.le _
        have hCupUc1 : (1 : ℝ) ≤ Cup ^ Ucap := one_le_pow₀ hCup
        rw [e1]
        calc Cup ^ Ucap * ((s.V.card : ℝ) ^ (1 - ε)) ^ (t.dim - s.dim)
            ≤ (Cup ^ Ucap) ^ (t.dim - s.dim) *
                ((s.V.card : ℝ) ^ (1 - ε)) ^ (t.dim - s.dim) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc Cup ^ Ucap = (Cup ^ Ucap) ^ 1 := (pow_one _).symm
                _ ≤ (Cup ^ Ucap) ^ (t.dim - s.dim) :=
                  pow_le_pow_right₀ hCupUc1 hΔ1
          _ = (Cup ^ Ucap * (s.V.card : ℝ) ^ (1 - ε)) ^ (t.dim - s.dim) :=
              (mul_pow _ _ _).symm
          _ ≤ smin ^ (t.dim - s.dim) := by
              apply pow_le_pow_left₀ (by positivity)
              linarith
      -- Conclude.
      have hchain : ((coordinateBox t.M).card : ℝ) * (Cup ^ Ucap * nP) ≤
          Cup ^ Ucap * ((coordinateBox s.M).card : ℝ) := by
        calc ((coordinateBox t.M).card : ℝ) * (Cup ^ Ucap * nP)
            ≤ ((coordinateBox t.M).card : ℝ) * smin ^ (t.dim - s.dim) :=
              mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
          _ = smin ^ (t.dim - s.dim) * ((coordinateBox t.M).card : ℝ) :=
              mul_comm _ _
          _ ≤ Cup ^ Ucap * ((coordinateBox s.M).card : ℝ) := h1
      have h2 : ((coordinateBox t.M).card : ℝ) * nP ≤
          ((coordinateBox s.M).card : ℝ) := by
        have h3 : Cup ^ Ucap * (((coordinateBox t.M).card : ℝ) * nP) ≤
            Cup ^ Ucap * ((coordinateBox s.M).card : ℝ) := by
          calc Cup ^ Ucap * (((coordinateBox t.M).card : ℝ) * nP)
              = ((coordinateBox t.M).card : ℝ) * (Cup ^ Ucap * nP) := by
                ring
            _ ≤ Cup ^ Ucap * ((coordinateBox s.M).card : ℝ) := hchain
        exact le_of_mul_le_mul_left h3 (by positivity)
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

/-! ## The assembled supplier -/

/-- **Per-cardinality numeric threshold bundle** for `prep_supplier_step`,
recorded at a stage with `n = |V|`, ambient dimension `d₀` and box
cardinality `B₀`.  The witnesses are the scale floor `smin`, the up-move
constant `Cup`, the U-cap driver `T`, and the three caps
`Ucap/Scap/imax`; the seventeen clauses are exactly the hypotheses of
`prep_supplier_step`.  All clauses except the ninth (`hn₁out`, the uniform
output threshold — see `prep_supplier_step`) are the manuscript's
"`n` sufficiently large" numerics (Manuscript.tex 560–660). -/
def PrepNumerics {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (ε δ γ K₀ : ℝ) (n₁ n d₀ B₀ : ℕ) : Prop :=
  ∃ (smin Cup T : ℝ) (Ucap Scap imax : ℕ),
    1 ≤ Cup ∧ 1 < T ∧ Cup * T ≤ smin ∧
    (B₀ : ℝ) < T ^ (Ucap + 1) ∧
    Cup ^ Ucap * (B₀ : ℝ) < (1 / γ) ^ (Scap + 1) ∧
    Scap + 2 * Ucap + d₀ ≤ imax ∧
    d₀ + Ucap ≤ Dcap ∧
    (n : ℝ) ^ (-ε) ≤ (δ / 2) ^ imax ∧
    (n₁ : ℝ) ≤ (δ / 2) ^ imax * (n : ℝ) ∧
    (n : ℝ) ^ (1 - ε) * Cup ^ Ucap ≤ smin ∧
    γ ≤ (δ / 2) ^ K₀ ∧
    Cup ≤ (δ / 2) ^ (2 * K₀) * smin ∧
    (∀ m : ℕ, δ * ((δ / 2) ^ imax * (n : ℝ)) ≤ (m : ℝ) →
      1 ≤ structureScale m ∧ smin ≤ structureScale m) ∧
    (∀ r, r ≤ Dcap → 1 ≤ (pkgs r).c * smin) ∧
    (∀ r, r ≤ Dcap → ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D ≤ Cup) ∧
    (∀ r, r ≤ Dcap →
      (pkgs r).c⁻¹ ≤ δ / 2 *
        Real.log (δ * ((δ / 2) ^ imax * (n : ℝ)))) ∧
    Real.exp 1 ≤ δ * ((δ / 2) ^ imax * (n : ℝ))

/-- **The preprocessing supplier from the numeric bundle.**  Given

* the sharp down-move box estimate `hdown1`
  (`TODO(orchestrator)`: the manuscript only proves `|B'| ≪ C·|B|` for a
  down identification, cf. `dimension_move`; `PrepSupplier`'s down branch
  demands the clean `|B'| ≤ |B|`), and
* the numeric bundle `hnum` at every excessive-stage datum
  (all clauses are the manuscript's large-`n` numerics except the uniform
  output threshold `n₁ ≤ (δ/2)^{imax}·n`, cf. `prep_supplier_step`),

the full `PrepSupplier` predicate holds: the E1 one-step lemma
(`prep_step`) supplies the moves, and the invariant descent over good
chains closes the eligibility/cutoff/γ-power accounting. -/
theorem prepSupplier_of_numerics {β : ℝ} (pkgs : ∀ r, Package r β)
    (Dcap : ℕ) (ζ₀ ε δ γ K₀ : ℝ) (n₁ : ℕ)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hK₀ : 0 ≤ K₀)
    (hdown1 : ∀ (X : ℕ) (C : ℝ) (x y : PrepStage X),
      PrepMove pkgs δ γ C x y → y.dim < x.dim →
      (coordinateBox y.M).card ≤ (coordinateBox x.M).card)
    (hnum : ∀ n d₀ B₀ : ℕ, n₁ ≤ n →
      (B₀ : ℝ) ^ (sigma d₀ + ζ₀) < (n : ℝ) → n ≤ B₀ → 1 ≤ d₀ →
      (d₀ : ℝ) ≤ 2 / ζ₀ →
      PrepNumerics pkgs Dcap ε δ γ K₀ n₁ n d₀ B₀) :
    PrepSupplier pkgs Dcap ζ₀ ε δ γ K₀ n₁ := by
  intro X s _hX hbad hn
  obtain ⟨C, _hC0, hCstep⟩ := prep_step (X := X) pkgs Dcap
  obtain ⟨smin, Cup, T, Ucap, Scap, imax,
    hCup, hT, hsminT, hUcapT, hScapγ, himax, hdimD, hρε, hn₁out, hupbox,
    hγK₀, hsminK₀, hscale, hcsmin, hCupB, hdel, hexp1⟩ :=
    hnum s.V.card s.dim (coordinateBox s.M).card hn hbad
      (stage_card_le_box s) (hbad.one_le_dim hζ₀.le)
      (hbad.dim_cast_le hζ₀)
  exact prep_supplier_step Dcap s hζ₀ hδ0 hδ1 hγ0 hγ1 hK₀ hbad
    hCup hT hsminT hUcapT hScapγ himax hdimD hρε hn₁out hupbox
    hγK₀ hsminK₀ hscale hcsmin hCupB hdel hexp1 (hdown1 X C)
    (fun t h1 h2 h3 => hCstep δ γ t h1 h2 h3)

/-! ## Discharging the numeric bundle: analytic engines

The scale floor `smin ≤ structureScale m = m/(log m)²` for all
`m ≥ δ·(δ/2)^{imax}·n` reduces, via monotonicity of `x ↦ x/(log x)²` on
`[e², ∞)`, to a single evaluation at the left endpoint; the remaining
clauses are `(log n)² = o(n^a)` facts. -/

/-- `log t ≤ 2(√t − 1)` for `t ≥ 1` (from `log x ≤ x − 1` at `√t`). -/
theorem log_le_two_mul_sqrt_sub_one {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ 2 * (Real.sqrt t - 1) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos hs0
  have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [← Real.mul_self_sqrt ht0.le,
      Real.log_mul (ne_of_gt hs0) (ne_of_gt hs0)]
    rw [Real.mul_self_sqrt ht0.le]
    ring
  linarith

/-- **Monotonicity of `x/(log x)²` on `[e², ∞)`**: the analytic heart of the
scale-floor supplier.  For `e² ≤ a ≤ b`, writing `t = b/a` and `s = √t`,
`log b = log a + log t ≤ log a + 2(s−1) ≤ s·log a`, whence
`(log b)² ≤ t·(log a)²`. -/
theorem div_log_sq_mono {a b : ℝ} (ha : Real.exp 2 ≤ a) (hab : a ≤ b) :
    a / (Real.log a) ^ 2 ≤ b / (Real.log b) ^ 2 := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (Real.exp_pos 2) ha
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
  have hla : (2 : ℝ) ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 2) ha
    rwa [Real.log_exp] at this
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  set t : ℝ := b / a with htdef
  have ht1 : (1 : ℝ) ≤ t := (one_le_div ha0).mpr hab
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hbt : b = a * t := by
    rw [htdef, mul_div_cancel₀ _ (ne_of_gt ha0)]
  set s : ℝ := Real.sqrt t with hsdef
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hsdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ht1
  have hss : s * s = t := Real.mul_self_sqrt ht0.le
  have hlogt : Real.log t ≤ 2 * (s - 1) := log_le_two_mul_sqrt_sub_one ht1
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogb : Real.log b = Real.log a + Real.log t := by
    rw [hbt, Real.log_mul (ne_of_gt ha0) (ne_of_gt ht0)]
  have h3 : Real.log a + Real.log t ≤ Real.log a * s := by
    nlinarith
  have h4 : (0 : ℝ) ≤ Real.log a + Real.log t := by linarith
  have hkey : (Real.log b) ^ 2 ≤ (Real.log a) ^ 2 * t := by
    calc (Real.log b) ^ 2 = (Real.log a + Real.log t) ^ 2 := by rw [hlogb]
      _ ≤ (Real.log a * s) ^ 2 := pow_le_pow_left₀ h4 h3 2
      _ = (Real.log a) ^ 2 * (s * s) := by ring
      _ = (Real.log a) ^ 2 * t := by rw [hss]
  have hla2 : (0 : ℝ) < (Real.log a) ^ 2 := by positivity
  have hlb2 : (0 : ℝ) < (Real.log b) ^ 2 := by
    have : (2 : ℝ) ≤ Real.log b := le_trans hla hlab
    positivity
  rw [div_le_div_iff₀ hla2 hlb2]
  calc a * (Real.log b) ^ 2 ≤ a * ((Real.log a) ^ 2 * t) :=
        mul_le_mul_of_nonneg_left hkey ha0.le
    _ = (a * t) * (Real.log a) ^ 2 := by ring
    _ = b * (Real.log a) ^ 2 := by rw [← hbt]

/-- Scale-floor bridge: `x/(log x)² ≤ structureScale m` whenever
`e² ≤ x ≤ m`. -/
theorem le_structureScale {x : ℝ} {m : ℕ} (hx : Real.exp 2 ≤ x)
    (hxm : x ≤ (m : ℝ)) : x / (Real.log x) ^ 2 ≤ structureScale m :=
  div_log_sq_mono hx hxm

/-- `n^a/(log n)² → ∞` for every `a > 0` (via `x/(log x)² → ∞` composed
with `x ↦ x^a`). -/
theorem tendsto_rpow_div_log_sq {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ a / (Real.log n) ^ 2)
      Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ a)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) ^ a) / (Real.log ((n : ℝ) ^ a)) ^ 2)
      Filter.atTop Filter.atTop :=
    (tendsto_id_div_log_pow_atTop 2).comp h1
  have h3 : Filter.Tendsto
      (fun n : ℕ => (1 / a ^ 2) * ((n : ℝ) ^ a / (Real.log n) ^ 2))
      Filter.atTop Filter.atTop := by
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    rw [Real.log_rpow hn0]
    rw [mul_pow]
    have ha2 : (a : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  have h4 := h3.const_mul_atTop (show (0 : ℝ) < a ^ 2 by positivity)
  refine h4.congr ?_
  intro n
  have ha2 : (a : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp

/-- Eventual absorption of `(log n)²` into any positive power:
`c·(log n)² ≤ d·n^a` for `n` large. -/
theorem eventually_mul_log_sq_le {c d a : ℝ} (hd : 0 < d) (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop, c * (Real.log n) ^ 2 ≤ d * (n : ℝ) ^ a := by
  filter_upwards [(tendsto_rpow_div_log_sq ha).eventually_ge_atTop (c / d),
    Filter.eventually_ge_atTop 3] with n h1 h2
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hsq : 0 < (Real.log n) ^ 2 := by positivity
  rw [div_le_div_iff₀ hd hsq] at h1
  linarith

/-! ## Discharging the numeric bundle: explicit constants -/

/-- The uniform up-move constant `Cup` (dominating `(3/c_r)^{D_r}` for every
package in play). -/
noncomputable def prepCup {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) : ℝ :=
  1 + ∑ r ∈ Finset.range (Dcap + 1),
    ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D

/-- The uniform inverse-constant bound (dominating `c_r⁻¹`). -/
noncomputable def prepCinv {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) :
    ℝ :=
  1 + ∑ r ∈ Finset.range (Dcap + 1), (pkgs r).c⁻¹

/-- The shrink-count cap `⌊log(Cup^{10}·n^5)/log(1/γ)⌋` (the γ-power
accounting bound on `|𝒮|`). -/
noncomputable def prepScap {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (γ : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) / Real.log (1 / γ)⌋₊

/-- The chain-length cap `Scap + 2·Ucap + d₀ ≤ Scap + 20 + Dcap` (with the
uniform `Ucap = 10` from `B₀ < n^5 = (√n)^{10}`). -/
noncomputable def prepImax {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (γ : ℝ) (n : ℕ) : ℕ :=
  prepScap pkgs Dcap γ n + 20 + Dcap

theorem one_le_prepCup {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) :
    1 ≤ prepCup pkgs Dcap := by
  have h : 0 ≤ ∑ r ∈ Finset.range (Dcap + 1),
      ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D :=
    Finset.sum_nonneg fun r _ => by positivity
  rw [prepCup]
  linarith

theorem le_prepCup {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) {r : ℕ}
    (hr : r ≤ Dcap) :
    ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D ≤ prepCup pkgs Dcap := by
  have h : ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D ≤
      ∑ r ∈ Finset.range (Dcap + 1),
        ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D :=
    Finset.single_le_sum (f := fun r =>
        ((3 : ℝ) * max 1 (pkgs r).c⁻¹) ^ (pkgs r).D)
      (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
  rw [prepCup]
  linarith

theorem one_le_prepCinv {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) :
    1 ≤ prepCinv pkgs Dcap := by
  have h : 0 ≤ ∑ r ∈ Finset.range (Dcap + 1), (pkgs r).c⁻¹ :=
    Finset.sum_nonneg fun r _ => inv_nonneg.mpr (pkgs r).c_pos.le
  rw [prepCinv]
  linarith

theorem le_prepCinv {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) {r : ℕ}
    (hr : r ≤ Dcap) : (pkgs r).c⁻¹ ≤ prepCinv pkgs Dcap := by
  have h : (pkgs r).c⁻¹ ≤ ∑ r ∈ Finset.range (Dcap + 1), (pkgs r).c⁻¹ :=
    Finset.single_le_sum (f := fun r => (pkgs r).c⁻¹)
      (fun i _ => inv_nonneg.mpr (pkgs i).c_pos.le)
      (Finset.mem_range.mpr (by omega))
  rw [prepCinv]
  linarith

theorem log_prepR {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) =
      10 * Real.log (prepCup pkgs Dcap) + 5 * Real.log n := by
  have hCup0 : (0 : ℝ) < prepCup pkgs Dcap :=
    lt_of_lt_of_le one_pos (one_le_prepCup pkgs Dcap)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  push_cast
  ring

theorem one_le_prepR {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ) {n : ℕ}
    (hn : 1 ≤ n) : (1 : ℝ) ≤ prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5 := by
  have hCup1 := one_le_prepCup pkgs Dcap
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ prepCup pkgs Dcap ^ 10 := one_le_pow₀ hCup1
  have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hn1
  nlinarith

/-- Shrink-cap driver: `Cup^{10}·n^5 < (1/γ)^{Scap+1}`. -/
theorem lt_pow_prepScap_succ {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {n : ℕ} (hn : 1 ≤ n) :
    prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5 <
      (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) := by
  have hLγ : 0 < Real.log (1 / γ) :=
    Real.log_pos (by rw [lt_div_iff₀ hγ0]; linarith)
  have hR1 := one_le_prepR pkgs Dcap (n := n) hn
  have hR0 : (0 : ℝ) < prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5 := by linarith
  have hfl : Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) /
      Real.log (1 / γ) < (prepScap pkgs Dcap γ n : ℝ) + 1 := by
    rw [prepScap]
    exact Nat.lt_floor_add_one _
  have h6' : Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) <
      ((prepScap pkgs Dcap γ n : ℝ) + 1) * Real.log (1 / γ) := by
    rw [div_lt_iff₀ hLγ] at hfl
    linarith
  have hpow : (0 : ℝ) < (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) := by
    positivity
  calc prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5
      = Real.exp (Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5)) :=
        (Real.exp_log hR0).symm
    _ < Real.exp (((prepScap pkgs Dcap γ n : ℝ) + 1) * Real.log (1 / γ)) :=
        Real.exp_lt_exp.mpr h6'
    _ = (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) := by
        rw [← Real.exp_log hpow, Real.log_pow]
        push_cast
        ring_nf

/-- Length-cap logarithm bound: under the manuscript's `γ ≤ δ^K` regime
(`40·log(2/δ) ≤ ε·log(1/γ)`) and once `n` absorbs the constants,
`imax·log(2/δ) ≤ (ε/2)·log n`. -/
theorem prepImax_log_le {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    {ε δ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hKε : 40 * Real.log (2 / δ) ≤ ε * Real.log (1 / γ)) {n : ℕ}
    (hn : 2 ≤ n)
    (h8 : ε / 4 * Real.log (prepCup pkgs Dcap) +
      ((20 : ℝ) + Dcap) * Real.log (2 / δ) ≤ 3 * ε / 8 * Real.log n) :
    (prepImax pkgs Dcap γ n : ℝ) * Real.log (2 / δ) ≤
      ε / 2 * Real.log n := by
  have hLγ : 0 < Real.log (1 / γ) :=
    Real.log_pos (by rw [lt_div_iff₀ hγ0]; linarith)
  have hLδ : 0 < Real.log (2 / δ) :=
    Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hlogCup0 : 0 ≤ Real.log (prepCup pkgs Dcap) :=
    Real.log_nonneg (one_le_prepCup pkgs Dcap)
  have hlogn0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ n)
  have hlogR : Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) =
      10 * Real.log (prepCup pkgs Dcap) + 5 * Real.log n :=
    log_prepR pkgs Dcap (by omega)
  have hlogR0 : 0 ≤ Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) := by
    rw [hlogR]; linarith
  have hScaple : (prepScap pkgs Dcap γ n : ℝ) ≤
      Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) /
        Real.log (1 / γ) :=
    Nat.floor_le (by positivity)
  have hLδLγ : Real.log (2 / δ) / Real.log (1 / γ) ≤ ε / 40 := by
    rw [div_le_iff₀ hLγ]
    linarith
  have hScapLδ : (prepScap pkgs Dcap γ n : ℝ) * Real.log (2 / δ) ≤
      ε / 4 * Real.log (prepCup pkgs Dcap) + ε / 8 * Real.log n := by
    calc (prepScap pkgs Dcap γ n : ℝ) * Real.log (2 / δ)
        ≤ (Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) /
            Real.log (1 / γ)) * Real.log (2 / δ) :=
          mul_le_mul_of_nonneg_right hScaple hLδ.le
      _ = Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) *
            (Real.log (2 / δ) / Real.log (1 / γ)) := by ring
      _ ≤ Real.log (prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ 5) * (ε / 40) :=
          mul_le_mul_of_nonneg_left hLδLγ hlogR0
      _ = ε / 4 * Real.log (prepCup pkgs Dcap) + ε / 8 * Real.log n := by
          rw [hlogR]; ring
  have hcast : (prepImax pkgs Dcap γ n : ℝ) =
      (prepScap pkgs Dcap γ n : ℝ) + 20 + Dcap := by
    rw [prepImax]
    push_cast
    ring
  rw [hcast]
  have hexp : ((prepScap pkgs Dcap γ n : ℝ) + 20 + Dcap) *
      Real.log (2 / δ) =
      (prepScap pkgs Dcap γ n : ℝ) * Real.log (2 / δ) +
        ((20 : ℝ) + Dcap) * Real.log (2 / δ) := by ring
  rw [hexp]
  linarith

/-- The retention floor `n^{-ε/2} ≤ (δ/2)^{imax}` (whence
`(δ/2)^{imax}·n ≥ n^{1-ε/2}`). -/
theorem rpow_le_pow_prepImax {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    {ε δ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hKε : 40 * Real.log (2 / δ) ≤ ε * Real.log (1 / γ)) {n : ℕ}
    (hn : 2 ≤ n)
    (h8 : ε / 4 * Real.log (prepCup pkgs Dcap) +
      ((20 : ℝ) + Dcap) * Real.log (2 / δ) ≤ 3 * ε / 8 * Real.log n) :
    (n : ℝ) ^ (-(ε / 2)) ≤ (δ / 2) ^ prepImax pkgs Dcap γ n := by
  have hkey := prepImax_log_le pkgs Dcap hδ0 hδ1 hγ0 hγ1 hKε hn h8
  have hδ2pos : (0 : ℝ) < δ / 2 := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 : ((δ / 2 : ℝ)) ^ prepImax pkgs Dcap γ n =
      Real.exp (-((prepImax pkgs Dcap γ n : ℝ) * Real.log (2 / δ))) := by
    rw [← Real.exp_log (pow_pos hδ2pos (prepImax pkgs Dcap γ n)),
      Real.log_pow]
    congr 1
    have hlogδ2 : Real.log (δ / 2) = -Real.log (2 / δ) := by
      rw [show (δ / 2 : ℝ) = (2 / δ)⁻¹ by rw [inv_div], Real.log_inv]
    rw [hlogδ2]
    ring
  have h2 : (n : ℝ) ^ (-(ε / 2)) =
      Real.exp (Real.log (n : ℝ) * (-(ε / 2))) :=
    Real.rpow_def_of_pos hn0 _
  rw [h1, h2]
  apply Real.exp_le_exp.mpr
  nlinarith

/-! ## Discharging the numeric bundle: the eventual instantiation -/

/-- **All clauses of `PrepNumerics` hold for `n` large**, with the explicit
choices `Ucap = 10`, `T = √n`, `Scap/imax` from the γ-power accounting, and
`smin = δ·n^{1-ε/2}/(log n)²` — *given* the uniform output threshold
`hout` (the `TODO(orchestrator)` interface gap: `PrepSupplier` demands
output cardinality `≥ n₁` uniformly, which fails for `n` near `n₁`; the
manuscript instead tracks a shrinking threshold along the descent).

Parameter regime: `0 < δ ≤ 1`, `0 < γ < 1`, `0 < ε < 1`, `K₀ ≥ 0`, the
manuscript's `γ ≤ (δ/2)^{K₀}` and `γ ≤ δ^K`-type smallness
`40·log(2/δ) ≤ ε·log(1/γ)`, and the dimension headroom
`2/ζ₀ + 10 ≤ Dcap`. -/
theorem prepNumerics_of_large {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (ζ₀ ε δ γ K₀ : ℝ)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγK₀ : γ ≤ (δ / 2) ^ K₀)
    (hKε : 40 * Real.log (2 / δ) ≤ ε * Real.log (1 / γ))
    (hDζ : 2 / ζ₀ + 10 ≤ (Dcap : ℝ)) :
    ∃ n₂ : ℕ, ∀ n₁ n d₀ B₀ : ℕ, n₂ ≤ n →
      (n₁ : ℝ) ≤ (δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ) →
      (B₀ : ℝ) ^ (sigma d₀ + ζ₀) < (n : ℝ) → n ≤ B₀ → 1 ≤ d₀ →
      (d₀ : ℝ) ≤ 2 / ζ₀ →
      PrepNumerics pkgs Dcap ε δ γ K₀ n₁ n d₀ B₀ := by
  have hCup1 : 1 ≤ prepCup pkgs Dcap := one_le_prepCup pkgs Dcap
  have hCup0 : (0 : ℝ) < prepCup pkgs Dcap := lt_of_lt_of_le one_pos hCup1
  have hCinv1 : 1 ≤ prepCinv pkgs Dcap := one_le_prepCinv pkgs Dcap
  have hδ2pos : (0 : ℝ) < δ / 2 := by linarith
  have hδ2le : δ / 2 ≤ 1 := by linarith
  have hq2δ : (0 : ℝ) < (δ / 2) ^ (2 * K₀) := Real.rpow_pos_of_pos hδ2pos _
  -- The eventual clauses.
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCup pkgs Dcap * (Real.log n) ^ 2 ≤
        δ * (n : ℝ) ^ ((1 - ε) / 2) :=
    eventually_mul_log_sq_le hδ0 (by linarith)
  have hev3 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCup pkgs Dcap ^ 10 * (Real.log n) ^ 2 ≤
        δ * (n : ℝ) ^ (ε / 2) :=
    eventually_mul_log_sq_le hδ0 (by linarith)
  have hev4 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCup pkgs Dcap * (Real.log n) ^ 2 ≤
        ((δ / 2) ^ (2 * K₀) * δ) * (n : ℝ) ^ (1 - ε / 2) :=
    eventually_mul_log_sq_le (by positivity) (by linarith)
  have hev5 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCinv pkgs Dcap * (Real.log n) ^ 2 ≤
        δ * (n : ℝ) ^ (1 - ε / 2) :=
    eventually_mul_log_sq_le hδ0 (by linarith)
  have htm₁ : Filter.Tendsto (fun n : ℕ => δ * (n : ℝ) ^ (1 - ε / 2))
      Filter.atTop Filter.atTop :=
    (((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ε / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop hδ0)
  have hev6 : ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp 2 ≤ δ * (n : ℝ) ^ (1 - ε / 2) :=
    htm₁.eventually_ge_atTop _
  have hev7 : ∀ᶠ n : ℕ in Filter.atTop,
      prepCinv pkgs Dcap ≤
        δ / 2 * Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) := by
    have h := (Real.tendsto_log_atTop.comp htm₁).eventually_ge_atTop
      (2 / δ * prepCinv pkgs Dcap)
    filter_upwards [h] with n hn
    have h2 : δ / 2 * (2 / δ * prepCinv pkgs Dcap) ≤
        δ / 2 * Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) :=
      mul_le_mul_of_nonneg_left hn (by linarith)
    calc prepCinv pkgs Dcap = δ / 2 * (2 / δ * prepCinv pkgs Dcap) := by
          field_simp
      _ ≤ δ / 2 * Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) := h2
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
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop 2).and (hev2.and (hev3.and (hev4.and
      (hev5.and (hev6.and (hev7.and hev8)))))))
  refine ⟨n₂, ?_⟩
  intro n₁ n d₀ B₀ hn hout hbadB hnB _hd₀ hdd
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hn₂ n hn
  have hn2 : 2 ≤ n := h1
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hsq : (0 : ℝ) < (Real.log n) ^ 2 := by positivity
  -- The retention floor.
  have hhalf : (n : ℝ) ^ (-(ε / 2)) ≤ (δ / 2) ^ prepImax pkgs Dcap γ n :=
    rpow_le_pow_prepImax pkgs Dcap hδ0 hδ1 hγ0 hγ1 hKε hn2 h8
  have hm₁m₀ : δ * (n : ℝ) ^ (1 - ε / 2) ≤
      δ * ((δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hδ0.le
    calc (n : ℝ) ^ (1 - ε / 2)
        = (n : ℝ) ^ (-(ε / 2)) * (n : ℝ) := by
          rw [show (1 - ε / 2 : ℝ) = -(ε / 2) + 1 by ring,
            Real.rpow_add hn0, Real.rpow_one]
      _ ≤ (δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hhalf hn0.le
  have hm₁pos : (0 : ℝ) < δ * (n : ℝ) ^ (1 - ε / 2) := by positivity
  have h1exp2 : (1 : ℝ) ≤ Real.exp 2 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by norm_num)
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
  refine ⟨δ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2, prepCup pkgs Dcap,
    (n : ℝ) ^ ((1 : ℝ) / 2), 10, prepScap pkgs Dcap γ n,
    prepImax pkgs Dcap γ n, hCup1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout, ?_,
    hγK₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `1 < T`
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 2) := (Real.one_rpow _).symm
      _ < (n : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_lt_rpow (by norm_num) (by linarith) (by norm_num)
  · -- `Cup·T ≤ smin`
    rw [le_div_iff₀ hsq]
    have hT0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hn0.le _
    have hexp : (1 : ℝ) / 2 + (1 - ε) / 2 = 1 - ε / 2 := by ring
    calc prepCup pkgs Dcap * (n : ℝ) ^ ((1 : ℝ) / 2) * (Real.log n) ^ 2
        = (n : ℝ) ^ ((1 : ℝ) / 2) *
            (prepCup pkgs Dcap * (Real.log n) ^ 2) := by ring
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * (δ * (n : ℝ) ^ ((1 - ε) / 2)) :=
          mul_le_mul_of_nonneg_left h2 hT0
      _ = δ * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 - ε) / 2)) := by
          ring
      _ = δ * (n : ℝ) ^ (1 - ε / 2) := by
          rw [← Real.rpow_add hn0, hexp]
  · -- `B₀ < T^{11}`
    have hT1 : (1 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := by
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 2) := (Real.one_rpow _).symm
        _ < (n : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_lt_rpow (by norm_num) (by linarith) (by norm_num)
    have hT10 : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 : ℕ) = (n : ℝ) ^ (5 : ℕ) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 2)) 10,
        ← Real.rpow_mul hn0.le, ← Real.rpow_natCast (n : ℝ) 5]
      norm_num
    calc (B₀ : ℝ) < (n : ℝ) ^ (5 : ℕ) := hB₀n5
      _ = ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 : ℕ) := hT10.symm
      _ ≤ ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (10 + 1 : ℕ) :=
          pow_le_pow_right₀ hT1.le (by omega)
  · -- `Cup^{10}·B₀ < (1/γ)^{Scap+1}`
    calc prepCup pkgs Dcap ^ 10 * (B₀ : ℝ)
        < prepCup pkgs Dcap ^ 10 * (n : ℝ) ^ (5 : ℕ) :=
          mul_lt_mul_of_pos_left hB₀n5 (by positivity)
      _ < (1 / γ) ^ (prepScap pkgs Dcap γ n + 1) :=
          lt_pow_prepScap_succ pkgs Dcap hγ0 hγ1 (by omega)
  · -- `Scap + 2·Ucap + d₀ ≤ imax`
    have hd₀D : d₀ ≤ Dcap := by
      have h : (d₀ : ℝ) ≤ (Dcap : ℝ) := by linarith
      exact_mod_cast h
    have : prepImax pkgs Dcap γ n = prepScap pkgs Dcap γ n + 20 + Dcap :=
      rfl
    omega
  · -- `d₀ + Ucap ≤ Dcap`
    have h : (d₀ : ℝ) + 10 ≤ (Dcap : ℝ) := by linarith
    exact_mod_cast h
  · -- `n^{-ε} ≤ (δ/2)^{imax}`
    calc (n : ℝ) ^ (-ε) ≤ (n : ℝ) ^ (-(ε / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
      _ ≤ (δ / 2) ^ prepImax pkgs Dcap γ n := hhalf
  · -- `n^{1-ε}·Cup^{10} ≤ smin`
    rw [le_div_iff₀ hsq]
    have hn1ε0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 - ε) := Real.rpow_nonneg hn0.le _
    have hexp : (1 - ε : ℝ) + ε / 2 = 1 - ε / 2 := by ring
    calc (n : ℝ) ^ (1 - ε) * prepCup pkgs Dcap ^ 10 * (Real.log n) ^ 2
        = (n : ℝ) ^ (1 - ε) *
            (prepCup pkgs Dcap ^ 10 * (Real.log n) ^ 2) := by ring
      _ ≤ (n : ℝ) ^ (1 - ε) * (δ * (n : ℝ) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left h3 hn1ε0
      _ = δ * ((n : ℝ) ^ (1 - ε) * (n : ℝ) ^ (ε / 2)) := by ring
      _ = δ * (n : ℝ) ^ (1 - ε / 2) := by
          rw [← Real.rpow_add hn0, hexp]
  · -- `Cup ≤ (δ/2)^{2K₀}·smin`
    rw [show (δ / 2) ^ (2 * K₀) *
        (δ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2) =
        ((δ / 2) ^ (2 * K₀) * δ) * (n : ℝ) ^ (1 - ε / 2) /
          (Real.log n) ^ 2 by ring]
    rw [le_div_iff₀ hsq]
    exact h4
  · -- the scale supplier
    intro m hm
    have hm₁m : δ * (n : ℝ) ^ (1 - ε / 2) ≤ (m : ℝ) :=
      le_trans hm₁m₀ hm
    have hf := le_structureScale h6 hm₁m
    have hsminf : δ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 ≤
        δ * (n : ℝ) ^ (1 - ε / 2) /
          (Real.log (δ * (n : ℝ) ^ (1 - ε / 2))) ^ 2 := by
      have hm₁n : δ * (n : ℝ) ^ (1 - ε / 2) ≤ (n : ℝ) := by
        calc δ * (n : ℝ) ^ (1 - ε / 2)
            ≤ 1 * (n : ℝ) ^ (1 - ε / 2) :=
              mul_le_mul_of_nonneg_right hδ1 (Real.rpow_nonneg hn0.le _)
          _ = (n : ℝ) ^ (1 - ε / 2) := one_mul _
          _ ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
          _ = (n : ℝ) := Real.rpow_one _
      have hlm₁ : Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) ≤ Real.log n :=
        Real.log_le_log hm₁pos hm₁n
      have hlm₁2 : (2 : ℝ) ≤ Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) := by
        have h := Real.log_le_log (Real.exp_pos 2) h6
        rwa [Real.log_exp] at h
      have hlm₁0 : (0 : ℝ) ≤ Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) := by
        linarith
      have hsqm₁ : (0 : ℝ) <
          (Real.log (δ * (n : ℝ) ^ (1 - ε / 2))) ^ 2 := by positivity
      have hsqle : (Real.log (δ * (n : ℝ) ^ (1 - ε / 2))) ^ 2 ≤
          (Real.log n) ^ 2 := pow_le_pow_left₀ hlm₁0 hlm₁ 2
      rw [div_le_div_iff₀ hsq hsqm₁]
      exact mul_le_mul_of_nonneg_left hsqle hm₁pos.le
    have hsminsc : δ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 ≤
        structureScale m := le_trans hsminf hf
    refine ⟨?_, hsminsc⟩
    have hsmin1 : (1 : ℝ) ≤
        δ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 := by
      rw [le_div_iff₀ hsq]
      have h5' : prepCinv pkgs Dcap * (Real.log n) ^ 2 ≤
          δ * (n : ℝ) ^ (1 - ε / 2) := h5
      nlinarith [hsq.le]
    linarith
  · -- `1 ≤ c_r·smin`
    intro r hr
    have hCinvsmin : prepCinv pkgs Dcap ≤
        δ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2 := by
      rw [le_div_iff₀ hsq]
      exact h5
    calc (1 : ℝ) = (pkgs r).c * (pkgs r).c⁻¹ :=
          (mul_inv_cancel₀ (ne_of_gt (pkgs r).c_pos)).symm
      _ ≤ (pkgs r).c * prepCinv pkgs Dcap :=
          mul_le_mul_of_nonneg_left (le_prepCinv pkgs Dcap hr)
            (pkgs r).c_pos.le
      _ ≤ (pkgs r).c *
            (δ * (n : ℝ) ^ (1 - ε / 2) / (Real.log n) ^ 2) :=
          mul_le_mul_of_nonneg_left hCinvsmin (pkgs r).c_pos.le
  · -- `(3·max(1,c_r⁻¹))^{D_r} ≤ Cup`
    intro r hr
    exact le_prepCup pkgs Dcap hr
  · -- the deletion threshold
    intro r hr
    have hlogm : Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) ≤
        Real.log (δ * ((δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ))) :=
      Real.log_le_log hm₁pos hm₁m₀
    calc (pkgs r).c⁻¹ ≤ prepCinv pkgs Dcap := le_prepCinv pkgs Dcap hr
      _ ≤ δ / 2 * Real.log (δ * (n : ℝ) ^ (1 - ε / 2)) := h7
      _ ≤ δ / 2 *
            Real.log (δ * ((δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hlogm (by linarith)
  · -- `e ≤ δ·(δ/2)^{imax}·n`
    calc Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ δ * (n : ℝ) ^ (1 - ε / 2) := h6
      _ ≤ δ * ((δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ)) := hm₁m₀

/-! ## Final assembly

`PrepSupplier` is discharged up to exactly two `TODO(orchestrator)`
hypotheses:

* **`hdown1`** (sharp down-move box estimate): every dimension-decreasing
  `PrepMove` satisfies `|B'| ≤ |B|` on the nose.  The proven toolkit
  (`dimension_move`) gives only `c^{d'}·|B'| ≤ C·|B|`, i.e. `|B'| ≪ |B|`
  with a multiplicative constant — which matches the manuscript's `≪` but
  not `PrepSupplier`'s clean `≤` in the down branch.  Either the geometric
  estimate must be sharpened, or the `PrepSupplier`/`RawStep` interface
  relaxed to a constant (absorbable in the down-case σ-gap for `n` large).

* **`hout`** (uniform output threshold): `n₁ ≤ (δ/2)^{imax(n)}·n` for all
  `n ≥ n₁`.  This clause is *false near `n = n₁`* for any fixed parameters
  (one preprocessing move already loses a `δ/2` factor), so it cannot be
  discharged as stated: `PrepSupplier` demands output cardinality `≥ n₁`
  uniformly, while the manuscript tracks a *shrinking* threshold along the
  projective descent.  The interface needs a second (smaller) output
  threshold or a `|V'| ≥ |V|^{1-2ε}`-style clause. -/

/-- **`PrepSupplier`, final form.**  For any parameters in the manuscript's
regime (`0 < δ ≤ 1`, `γ ≤ (δ/2)^{K₀}`, `40·log(2/δ) ≤ ε·log(1/γ)`,
`Dcap ≥ 2/ζ₀ + 10`), there is a threshold `n₂` such that for every
`n₁ ≥ n₂` satisfying the uniform output-threshold clause `hout`,
`PrepSupplier pkgs Dcap ζ₀ ε δ γ K₀ n₁` holds — given the sharp down-move
box estimate `hdown1`.  (See the section docstring for the status of the
two hypotheses.) -/
theorem prepSupplier_final {β : ℝ} (pkgs : ∀ r, Package r β) (Dcap : ℕ)
    (ζ₀ ε δ γ K₀ : ℝ)
    (hζ₀ : 0 < ζ₀) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hK₀ : 0 ≤ K₀)
    (hγK₀ : γ ≤ (δ / 2) ^ K₀)
    (hKε : 40 * Real.log (2 / δ) ≤ ε * Real.log (1 / γ))
    (hDζ : 2 / ζ₀ + 10 ≤ (Dcap : ℝ))
    (hdown1 : ∀ (X : ℕ) (C : ℝ) (x y : PrepStage X),
      PrepMove pkgs δ γ C x y → y.dim < x.dim →
      (coordinateBox y.M).card ≤ (coordinateBox x.M).card) :
    ∃ n₂ : ℕ, ∀ n₁ : ℕ, n₂ ≤ n₁ →
      (∀ n : ℕ, n₁ ≤ n →
        (n₁ : ℝ) ≤ (δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ)) →
      PrepSupplier pkgs Dcap ζ₀ ε δ γ K₀ n₁ := by
  obtain ⟨n₂, hnum⟩ := prepNumerics_of_large pkgs Dcap ζ₀ ε δ γ K₀
    hζ₀ hδ0 hδ1 hγ0 hγ1 hε0 hε1 hγK₀ hKε hDζ
  refine ⟨n₂, fun n₁ hn₁ hout => ?_⟩
  exact prepSupplier_of_numerics pkgs Dcap ζ₀ ε δ γ K₀ n₁
    hζ₀ hδ0 hδ1 hγ0 hγ1 hK₀ hdown1
    (fun n d₀ B₀ hn hbad hle hd hdd =>
      hnum n₁ n d₀ B₀ (le_trans hn₁ hn) (hout n hn) hbad hle hd hdd)

/-- **Consumption-shaped corollary** (matching
`descentSupplier_of_pipeline`): for every excess parameter `ζ₀ > 0` and
every `ε₁ > 0` there are concrete parameters — `Dcap ≥ max(2, 2/ζ₀)`,
`0 < ε ≤ 1/2` with `2ε ≤ ε₁`, `δ = 1/2`, `K₀ = 5`, and
`γ = 4^{-max(5,⌈40/ε⌉)}` — for which the final supplier theorem applies. -/
theorem prepSupplier_params {β : ℝ} (pkgs : ∀ r, Package r β)
    (ζ₀ ε₁ : ℝ) (hζ₀ : 0 < ζ₀) (hε₁ : 0 < ε₁) :
    ∃ (Dcap : ℕ) (ε δ γ K₀ : ℝ),
      2 ≤ Dcap ∧ 2 / ζ₀ ≤ (Dcap : ℝ) ∧
      0 < ε ∧ 2 * ε ≤ ε₁ ∧ ε ≤ 1 / 2 ∧ (5 : ℝ) ≤ K₀ ∧
      0 < δ ∧ δ ≤ 1 ∧ 0 < γ ∧ γ < 1 ∧
      ((∀ (X : ℕ) (C : ℝ) (x y : PrepStage X),
          PrepMove pkgs δ γ C x y → y.dim < x.dim →
          (coordinateBox y.M).card ≤ (coordinateBox x.M).card) →
        ∃ n₂ : ℕ, ∀ n₁ : ℕ, n₂ ≤ n₁ →
          (∀ n : ℕ, n₁ ≤ n →
            (n₁ : ℝ) ≤ (δ / 2) ^ prepImax pkgs Dcap γ n * (n : ℝ)) →
          PrepSupplier pkgs Dcap ζ₀ ε δ γ K₀ n₁) := by
  set ε : ℝ := min (ε₁ / 2) (1 / 2) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hε1' : ε < 1 := lt_of_le_of_lt hεhalf (by norm_num)
  set K : ℕ := max 5 ⌈40 / ε⌉₊ with hKdef
  set γ : ℝ := (1 / 4 : ℝ) ^ K with hγdef
  set Dcap : ℕ := max 2 (⌈2 / ζ₀⌉₊ + 10) with hDdef
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  have hγ1 : γ < 1 := by
    rw [hγdef]
    apply pow_lt_one₀ (by norm_num) (by norm_num)
    omega
  have hceil : 2 / ζ₀ ≤ (⌈2 / ζ₀⌉₊ : ℝ) := Nat.le_ceil _
  have hDζR : 2 / ζ₀ + 10 ≤ (Dcap : ℝ) := by
    have h1 : (⌈2 / ζ₀⌉₊ + 10 : ℕ) ≤ Dcap := le_max_right _ _
    have h2 : ((⌈2 / ζ₀⌉₊ + 10 : ℕ) : ℝ) ≤ (Dcap : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hinvγ : (1 : ℝ) / γ = 4 ^ K := by
    rw [hγdef, one_div, ← inv_pow]
    norm_num
  have hlogγ : Real.log (1 / γ) = (K : ℝ) * Real.log 4 := by
    rw [hinvγ, Real.log_pow]
  have hK40 : 40 / ε ≤ (K : ℝ) := by
    calc (40 : ℝ) / ε ≤ (⌈40 / ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (K : ℝ) := by exact_mod_cast le_max_right 5 ⌈40 / ε⌉₊
  have hK5 : (5 : ℕ) ≤ K := le_max_left _ _
  refine ⟨Dcap, ε, 1 / 2, γ, 5, ?_, ?_, hε0, ?_, hεhalf, le_refl _,
    by norm_num, by norm_num, hγ0, hγ1, ?_⟩
  · exact le_max_left _ _
  · linarith
  · rw [hεdef]
    have := min_le_left (ε₁ / 2) (1 / 2 : ℝ)
    linarith [min_le_left (ε₁ / 2) (1 / 2 : ℝ)]
  · intro hdown1
    apply prepSupplier_final pkgs Dcap ζ₀ ε (1 / 2) γ 5
      hζ₀ (by norm_num) (by norm_num) hγ0 hγ1 hε0 hε1' (by norm_num)
      ?_ ?_ (by linarith) hdown1
    · -- `γ ≤ (1/4)^{(5:ℝ)}`
      have h1 : ((1 / 2 : ℝ) / 2) = 1 / 4 := by norm_num
      rw [h1, show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      rw [hγdef]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hK5
    · -- `40·log 4 ≤ ε·K·log 4`
      have h1 : (2 : ℝ) / (1 / 2) = 4 := by norm_num
      rw [h1, hlogγ]
      have h2 : (40 : ℝ) ≤ ε * K := by
        have h3 : ε * (40 / ε) ≤ ε * K :=
          mul_le_mul_of_nonneg_left hK40 hε0.le
        rw [mul_div_cancel₀ _ (ne_of_gt hε0)] at h3
        linarith
      calc 40 * Real.log 4 ≤ (ε * K) * Real.log 4 :=
            mul_le_mul_of_nonneg_right h2 hlog4.le
        _ = ε * ((K : ℝ) * Real.log 4) := by ring

/-- **Interface artifact (warning).**  `PrepSupplier` as stated is
*degenerately* satisfiable for any density parameter `δ > 1`: no subset
`D ⊆ V` can then satisfy `|D| ≥ δ|V|`, so every stage is vacuously
unshiftedly irreducible and the same-dimension branch fires with `s' = s`,
`ρ = 1`.  This costs nothing here but shifts all content onto
`IrreducibleIncrement`, which cannot be discharged from a vacuous
irreducibility hypothesis — so the *pipeline* still forces `δ ≤ 1/2`.
Recorded to document that `PrepSupplier` alone does not pin down the
manuscript's preprocessing content. -/
theorem prepSupplier_of_one_lt_delta {β : ℝ} (pkgs : ∀ r, Package r β)
    (D : ℕ) (ζ₀ ε δ γ K₀ : ℝ) (n₁ : ℕ) (hδ : 1 < δ) (hε : 0 ≤ ε)
    (hn₁ : 1 ≤ n₁) : PrepSupplier pkgs D ζ₀ ε δ γ K₀ n₁ := by
  intro X s _hX _hbad hn
  have hV1 : (1 : ℝ) ≤ (s.V.card : ℝ) := by
    exact_mod_cast le_trans hn₁ hn
  refine ⟨s, hn, Or.inr (Or.inr ⟨rfl, ?_, 1, one_pos, le_refl 1, ?_, ?_,
    ?_⟩)⟩
  · -- vacuous irreducibility: no `δ`-large subset exists for `δ > 1`
    intro Dw hsub hlarge hE
    exfalso
    have h1 : (Dw.card : ℝ) ≤ (s.V.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith
  · exact Real.rpow_le_one_of_one_le_of_nonpos hV1 (by linarith)
  · rw [one_mul]
  · rw [Real.one_rpow, one_mul]

end Nondividing
