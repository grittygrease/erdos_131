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

end Nondividing
