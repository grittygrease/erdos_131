import Nondividing.Preprocessing2
import Nondividing.Numerology
import Nondividing.DyadicShell
import Nondividing.Main

open scoped BigOperators

namespace Nondividing

/-!
# The projective theorem: density-increment iteration (`thm:projective-main`)

This file formalizes the iteration skeleton of the projective theorem
(Manuscript.tex 1712–2107): every `(λ,X)`-shell non-dividing `V ⊆ B ⊆ ℤ^d`
with `|B| ≤ |V|^β` satisfies `|V| ≤ |B|^{σ_d+ζ₀}` for `|V|` large.

Structure (all green, no sorry):

* **Bad stages** (`ExcessiveStage`): a stage of the iteration whose set beats
  the target exponent, `|B|^{σ_d+ζ₀} < |V|`.  Basic facts: excessive stages
  are automatically nontrivial (`two_le_card`, `two_le_box`), have
  `σ_d + ζ₀ < 1` (the manuscript's trivial branch `|V| ≤ |B|`), bounded
  dimension (`dim_cast_le`, via `sigma_dimension_cap`), and the *automatic*
  polynomial box bound `|B| < |V|^{β_*}`, `β_* = (1/5+ζ₀)⁻¹`
  (`box_lt_rpow`, via `box_exponent_of_excess`) — so the iteration never
  needs the initial `β` again.
* **Exact excess** (`stageExcess`): `log|V|/log|B| − σ_d`; excessive stages
  have excess in `(ζ₀, 1−σ_d]`.
* **Termination** (`descend_lex`, `no_excessive_stage`): the manuscript's
  potential argument.  Each one-step increment either raises the exact excess
  by a fixed `c > 0` (a dimension-changing move: `numerology` up-gap or the
  `Δ_D` down-gap) or keeps the excess while strictly shrinking the box (a
  same-dimensional step, `|B'| ≤ o(1)|B|`).  Since the excess is trapped in
  `(ζ₀, 1]`, the lexicographic measure `(⌊(1−excess)/c⌋₊, |B|)` strictly
  decreases, so no bad stage can exist.
* **The descent hypothesis** (`DescentStep`): the complete one-step analysis
  of the manuscript (preprocessing + projective convexity + weighted density
  + cap lifting + numerology).  `projective_theorem_of_descent` derives the
  projective theorem from it; discharging `DescentStep` is decomposed further
  below.
-/

/-! ## Bad stages -/

/-- A `ζ₀`-**excessive** (bad) stage: the stage set beats the target exponent,
`|box|^{σ_dim+ζ₀} < |V|`.  The projective theorem says: no excessive stage of
large cardinality exists. -/
def ExcessiveStage (ζ₀ : ℝ) {X : ℕ} (s : PrepStage X) : Prop :=
  ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀) < (s.V.card : ℝ)

/-- Stage sets are at most the box: `|V| ≤ |B|` (the manuscript's standing
`n ≤ |B|`). -/
theorem stage_card_le_box {X : ℕ} (s : PrepStage X) :
    s.V.card ≤ (coordinateBox s.M).card :=
  Finset.card_le_card s.subset

/-- **Trivial branch** of `thm:projective-main`: since `V ⊆ B`, any exponent
`≥ 1` bound holds outright; bad stages only exist below exponent `1`. -/
theorem card_le_rpow_box_of_one_le {d : ℕ} {V : Finset (Fin d → ℤ)}
    {M : Fin d → ℕ} (hsub : V ⊆ coordinateBox M) {e : ℝ} (he : 1 ≤ e) :
    (V.card : ℝ) ≤ ((coordinateBox M).card : ℝ) ^ e := by
  have hB1 : (1 : ℝ) ≤ ((coordinateBox M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox M
  calc (V.card : ℝ) ≤ ((coordinateBox M).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((coordinateBox M).card : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ ((coordinateBox M).card : ℝ) ^ e :=
        Real.rpow_le_rpow_of_exponent_le hB1 he

namespace ExcessiveStage

variable {ζ₀ : ℝ} {X : ℕ} {s : PrepStage X}

theorem card_lt (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) :
    (1 : ℝ) < (s.V.card : ℝ) := by
  have hB1 : (1 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s.M
  have hexp : (0 : ℝ) ≤ sigma s.dim + ζ₀ := by
    have := sigma_pos s.dim; linarith
  calc (1 : ℝ) = ((coordinateBox s.M).card : ℝ) ^ (0 : ℝ) :=
        (Real.rpow_zero _).symm
    _ ≤ ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀) :=
        Real.rpow_le_rpow_of_exponent_le hB1 hexp
    _ < (s.V.card : ℝ) := h

/-- Excessive stages have at least two points. -/
theorem two_le_card (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) :
    2 ≤ s.V.card := by
  have := h.card_lt hζ₀
  exact_mod_cast (by exact_mod_cast this : (1 : ℕ) < s.V.card)

/-- Excessive stages have a nontrivial box. -/
theorem two_le_box (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) :
    2 ≤ (coordinateBox s.M).card := by
  have h2 := h.two_le_card hζ₀
  have := stage_card_le_box s
  omega

/-- The manuscript's trivial-branch consequence: at an excessive stage,
`σ_dim + ζ₀ < 1` (else `|V| ≤ |B| = |B|^1 ≤ |B|^{σ+ζ₀}`). -/
theorem sigma_add_lt_one (h : ExcessiveStage ζ₀ s) : sigma s.dim + ζ₀ < 1 := by
  by_contra hcon
  push_neg at hcon
  exact absurd h (not_lt_of_ge (card_le_rpow_box_of_one_le s.subset hcon))

/-- **Dimension cap** at excessive stages: `dim ≤ 2/ζ₀` (the manuscript's
`D₀`).  Via `sigma_dimension_cap`. -/
theorem dim_cast_le (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 < ζ₀) :
    (s.dim : ℝ) ≤ 2 / ζ₀ := by
  rcases Nat.eq_zero_or_pos s.dim with h0 | h1
  · simp only [h0, Nat.cast_zero]; positivity
  · exact sigma_dimension_cap hζ₀ h1 h.sigma_add_lt_one.le

/-- The excess parameter is below `4/5` at any excessive stage. -/
theorem zeta_lt (h : ExcessiveStage ζ₀ s) : ζ₀ < 4 / 5 := by
  have h1 := h.sigma_add_lt_one
  have h2 := one_fifth_le_sigma s.dim
  linarith

/-- **Automatic polynomial box bound** at excessive stages: `|B| < |V|^{β_*}`,
`β_* = (1/5+ζ₀)⁻¹` (`thm:projective-main` preamble; via
`box_exponent_of_excess`).  The initial exponent `β` is never needed again
along the iteration. -/
theorem box_lt_rpow (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 < ζ₀) :
    ((coordinateBox s.M).card : ℝ) <
      (s.V.card : ℝ) ^ ((1 : ℝ) / (1 / 5 + ζ₀)) := by
  have hB1 : (1 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s.M
  have hAB : (s.V.card : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast stage_card_le_box s
  exact box_exponent_of_excess (d := s.dim) hζ₀ (h.zeta_lt).le hB1 h hAB

end ExcessiveStage

/-! ## The exact excess -/

/-- The **exact excess** of a stage: `log|V|/log|B| − σ_dim` (the manuscript's
`ζ`, from `p = log n/log|B| = σ_d + ζ`). -/
noncomputable def stageExcess {X : ℕ} (s : PrepStage X) : ℝ :=
  Real.log (s.V.card : ℝ) / Real.log ((coordinateBox s.M).card : ℝ) -
    sigma s.dim

namespace ExcessiveStage

variable {ζ₀ : ℝ} {X : ℕ} {s : PrepStage X}

theorem log_box_pos (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) :
    0 < Real.log ((coordinateBox s.M).card : ℝ) := by
  have h2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast h.two_le_box hζ₀
  exact Real.log_pos (by linarith)

/-- Excessive stages have exact excess `> ζ₀`. -/
theorem zeta_lt_stageExcess (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) :
    ζ₀ < stageExcess s := by
  have hlogB := h.log_box_pos hζ₀
  have hBpos : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by
    have := h.two_le_box hζ₀
    have : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by exact_mod_cast this
    linarith
  have hlt : (sigma s.dim + ζ₀) * Real.log ((coordinateBox s.M).card : ℝ) <
      Real.log (s.V.card : ℝ) := by
    have hlog := Real.log_lt_log
      (Real.rpow_pos_of_pos hBpos (sigma s.dim + ζ₀)) h
    rwa [Real.log_rpow hBpos] at hlog
  have hdiv : sigma s.dim + ζ₀ <
      Real.log (s.V.card : ℝ) / Real.log ((coordinateBox s.M).card : ℝ) := by
    rw [lt_div_iff₀ hlogB]
    exact hlt
  unfold stageExcess
  linarith

/-- Excessive stages have exact excess `≤ 1 − σ_dim` (since `|V| ≤ |B|`). -/
theorem stageExcess_le (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) :
    stageExcess s ≤ 1 - sigma s.dim := by
  have hlogB := h.log_box_pos hζ₀
  have hVpos : (0 : ℝ) < (s.V.card : ℝ) := lt_trans one_pos (h.card_lt hζ₀)
  have hVB : (s.V.card : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast stage_card_le_box s
  have hlog : Real.log (s.V.card : ℝ) ≤
      Real.log ((coordinateBox s.M).card : ℝ) :=
    Real.log_le_log hVpos hVB
  have hdiv : Real.log (s.V.card : ℝ) /
      Real.log ((coordinateBox s.M).card : ℝ) ≤ 1 :=
    (div_le_one hlogB).mpr hlog
  unfold stageExcess
  linarith

/-- Excessive stages have exact excess `≤ 4/5 < 1`. -/
theorem stageExcess_le_one (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) :
    stageExcess s ≤ 4 / 5 := by
  have h1 := h.stageExcess_le hζ₀
  have h2 := one_fifth_le_sigma s.dim
  linarith

end ExcessiveStage

/-! ## Termination: the lexicographic descent -/

/-- The up-move budget `⌊(1 − excess)/c⌋₊`: dimension-changing moves (excess
gain `≥ c`) strictly decrease it, same-dimensional moves never increase it. -/
noncomputable def excessBudget (c : ℝ) {X : ℕ} (s : PrepStage X) : ℕ :=
  ⌊(1 - stageExcess s) / c⌋₊

/-- A fixed excess gain `c` strictly decreases the budget (uses
`floor_lt_floor_of_le_sub_one`). -/
theorem excessBudget_lt_of_gain {c : ℝ} (hc : 0 < c) {X X' : ℕ}
    {s : PrepStage X} {s' : PrepStage X'} (h1 : stageExcess s' ≤ 1)
    (h : stageExcess s + c ≤ stageExcess s') :
    excessBudget c s' < excessBudget c s := by
  apply floor_lt_floor_of_le_sub_one
  · exact div_nonneg (by linarith) hc.le
  · calc (1 - stageExcess s') / c ≤ ((1 - stageExcess s) - c) / c :=
        (div_le_div_iff_of_pos_right hc).mpr (by linarith)
    _ = (1 - stageExcess s) / c - 1 := by
        rw [sub_div, div_self (ne_of_gt hc)]

/-- Monotone excess never increases the budget. -/
theorem excessBudget_le_of_mono {c : ℝ} (hc : 0 < c) {X X' : ℕ}
    {s : PrepStage X} {s' : PrepStage X'}
    (h : stageExcess s ≤ stageExcess s') :
    excessBudget c s' ≤ excessBudget c s :=
  Nat.floor_mono ((div_le_div_iff_of_pos_right hc).mpr (by linarith))

/-- **Lexicographic descent.**  If every bad state has a bad successor that
either strictly decreases a primary ℕ-measure or (keeping it) strictly
decreases a secondary ℕ-measure, then there is no bad state. -/
theorem descend_lex {α : Type*} (Bad : α → Prop) (b B : α → ℕ)
    (hstep : ∀ a, Bad a → ∃ a', Bad a' ∧
      (b a' < b a ∨ (b a' ≤ b a ∧ B a' < B a))) :
    ∀ a, ¬ Bad a := by
  have key : ∀ n m a, b a ≤ n → B a ≤ m → ¬ Bad a := by
    intro n
    induction n with
    | zero =>
      intro m
      induction m with
      | zero =>
        intro a hb hB hbad
        obtain ⟨a', _, h⟩ := hstep a hbad
        rcases h with h | ⟨h1, h2⟩ <;> omega
      | succ m ihm =>
        intro a hb hB hbad
        obtain ⟨a', hbad', h⟩ := hstep a hbad
        rcases h with h | ⟨h1, h2⟩
        · omega
        · exact ihm a' (by omega) (by omega) hbad'
    | succ n ihn =>
      intro m
      induction m with
      | zero =>
        intro a hb hB hbad
        obtain ⟨a', hbad', h⟩ := hstep a hbad
        rcases h with h | ⟨h1, h2⟩
        · exact ihn (B a') a' (by omega) le_rfl hbad'
        · omega
      | succ m ihm =>
        intro a hb hB hbad
        obtain ⟨a', hbad', h⟩ := hstep a hbad
        rcases h with h | ⟨h1, h2⟩
        · exact ihn (B a') a' (by omega) le_rfl hbad'
        · exact ihm a' (by omega) (by omega) hbad'
  intro a hbad
  exact key (b a) (B a) a le_rfl le_rfl hbad

/-! ## The descent hypothesis and the conditional projective theorem -/

/-- **The one-step density increment** of `thm:projective-main`
(Manuscript.tex 1858–2024), packaged as a single predicate.

`TODO(orchestrator)`: discharge this from the proven inventory.  It is the
manuscript's complete one-step analysis: from an excessive stage of
cardinality `≥ n₁`, unshifted preprocessing (`unshifted_preprocessing_toward`)
either changes dimension — the numerology (`numerology`) up-gap or the `Δ_D`
down-gap raises the exact excess by a uniform `c > 0` — or produces an
irreducible same-dimensional pair, to which projective convexity
(`projective_convexity_assembled`), weighted density (`weighted_density`) and
cap lifting (`cap_lifting_deficient` / `cap_cone_count`) apply, raising the
excess while shrinking the box by `o(1) < 1`.  In every case the new stage is
excessive again with cardinality `≥ n₁` (the manuscript's `|A_j| ≥ n₀^q`
bookkeeping). -/
def DescentStep (ζ₀ c : ℝ) (n₁ : ℕ) : Prop :=
  ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X →
    ExcessiveStage ζ₀ s → n₁ ≤ s.V.card →
    ∃ s' : PrepStage X,
      ExcessiveStage ζ₀ s' ∧ n₁ ≤ s'.V.card ∧
      (stageExcess s + c ≤ stageExcess s' ∨
        (stageExcess s ≤ stageExcess s' ∧
          (coordinateBox s'.M).card < (coordinateBox s.M).card))

/-- **No excessive stage** (the projective-theorem contradiction).  Under a
descent step with fixed excess gain `c > 0`, no excessive stage of cardinality
`≥ n₁` exists: the lexicographic measure `(⌊(1−excess)/c⌋₊, |box|)` would
strictly decrease forever. -/
theorem no_excessive_stage {ζ₀ c : ℝ} {n₁ : ℕ} (hζ₀ : 0 < ζ₀) (hc : 0 < c)
    (hstep : DescentStep ζ₀ c n₁) (X : ℕ) (s : PrepStage X) (hX : 1 ≤ X)
    (hbad : ExcessiveStage ζ₀ s) (hn : n₁ ≤ s.V.card) : False := by
  classical
  refine descend_lex
    (α := Σ Y : ℕ, PrepStage Y)
    (fun p => 1 ≤ p.1 ∧ ExcessiveStage ζ₀ p.2 ∧ n₁ ≤ p.2.V.card)
    (fun p => excessBudget c p.2)
    (fun p => (coordinateBox p.2.M).card)
    ?_ ⟨X, s⟩ ⟨hX, hbad, hn⟩
  intro p hp
  obtain ⟨hX', hbad', hn'⟩ := hp
  obtain ⟨s', hbads', hns', hcase⟩ := hstep p.1 p.2 hX' hbad' hn'
  refine ⟨⟨p.1, s'⟩, ⟨hX', hbads', hns'⟩, ?_⟩
  rcases hcase with hgain | ⟨hmono, hbox⟩
  · left
    exact excessBudget_lt_of_gain hc
      (le_trans (hbads'.stageExcess_le_one hζ₀.le) (by norm_num)) hgain
  · right
    exact ⟨excessBudget_le_of_mono hc hmono, hbox⟩

/-- **The projective theorem, given the descent step** (clean form).  Any
shell non-dividing `V ⊆ box M` with `|V| ≥ n₁` obeys
`|V| ≤ |box|^{σ_d+ζ₀}`. -/
theorem projective_theorem_of_descent {ζ₀ c : ℝ} {n₁ : ℕ}
    (hζ₀ : 0 < ζ₀) (hc : 0 < c) (hstep : DescentStep ζ₀ c n₁)
    (d : ℕ) (lam : (Fin d → ℤ) →+ ℤ) (X : ℕ) (V : Finset (Fin d → ℤ))
    (M : Fin d → ℕ) (hX : 1 ≤ X) (hn : n₁ ≤ V.card)
    (hsub : V ⊆ coordinateBox M)
    (hshell : ShellNonDividing (fun v => lam v) X V) :
    (V.card : ℝ) ≤ ((coordinateBox M).card : ℝ) ^ (sigma d + ζ₀) := by
  by_contra hcon
  push Not at hcon
  exact no_excessive_stage hζ₀ hc hstep X
    ⟨d, V, M, lam, hsub, hshell⟩ hX hcon hn

/-- **The projective theorem, target shape** (`thm:projective-main`), given a
descent-step supplier for the excess parameter `ζ₀`.  The `β` hypothesis is
carried but not needed: excessive stages regenerate the polynomial box bound
with the fixed exponent `β_* = (1/5+ζ₀)⁻¹` (`ExcessiveStage.box_lt_rpow`). -/
theorem projective_theorem_of_descent_supplier (d : ℕ) (_hd : 1 ≤ d)
    (β ζ₀ : ℝ) (_hβ : 1 < β) (hζ₀ : 0 < ζ₀)
    (hsupply : ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ DescentStep ζ₀ c n₀) :
    ∃ n₁ : ℕ, ∀ (lam : (Fin d → ℤ) →+ ℤ) (X : ℕ) (V : Finset (Fin d → ℤ))
      (M : Fin d → ℕ),
      1 ≤ X → n₁ ≤ V.card → V ⊆ coordinateBox M →
      ShellNonDividing (fun v => lam v) X V →
      ((coordinateBox M).card : ℝ) ≤ (V.card : ℝ) ^ β →
      (V.card : ℝ) ≤ ((coordinateBox M).card : ℝ) ^ (sigma d + ζ₀) := by
  obtain ⟨c, n₀, hc, hstep⟩ := hsupply
  exact ⟨n₀, fun lam X V M hX hn hsub hshell _ =>
    projective_theorem_of_descent hζ₀ hc hstep d lam X V M hX hn hsub hshell⟩

/-! ## The `d = 1` adapter and the main-theorem composition -/

/-- A **descent supplier**: for every excess parameter `ζ₀ > 0`, a uniform
one-step excess gain `c > 0` and a cardinality threshold `n₀` realizing the
one-step increment (`DescentStep`).  This is the single remaining
`TODO(orchestrator)` input to the whole main theorem. -/
def DescentSupplier : Prop :=
  ∀ ζ₀ : ℝ, 0 < ζ₀ → ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ DescentStep ζ₀ c n₀

/-- **`d = 1` adapter** (`thm:projective-main` feeding
`main_upper_eps_of_projective`).  Given a descent supplier, dense dyadic
shells `W ⊆ [X, 2X]` obey `|W| ≤ X^{1/5+ε}`: embed via `dOneEmbedding` into
the box of radius `2X` (cardinality `4X+1`), apply the projective theorem at
`d = 1`, `ζ₀ = ε/2`, and absorb the constant `(4X+1 ≤ 5X)^{1/5+ε/2}` into the
`ε/2` exponent gap for `X` large. -/
theorem projective_theorem_dOne (hsupply : DescentSupplier) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ (X : ℕ) (W : Finset ℕ),
      X₀ ≤ X → (∀ a ∈ W, X ≤ a ∧ a ≤ 2 * X) →
      ShellNonDividing (fun a : ℕ => (a : ℤ)) X W →
      (X : ℝ) ≤ (W.card : ℝ) ^ 5 →
      (W.card : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5 + ε) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨c, n₀, hc, hstep⟩ := hsupply (ε / 2) hε2
  -- Eventual facts absorbing the threshold and the constant `5`.
  have h1 : ∀ᶠ X : ℕ in Filter.atTop,
      (n₀ : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5 + ε) :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 5 + ε)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have h2 : ∀ᶠ X : ℕ in Filter.atTop,
      (5 : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) ≤ (X : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop hε2).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have h3 : ∀ᶠ X : ℕ in Filter.atTop, 1 ≤ X := Filter.eventually_ge_atTop 1
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨X₀, ?_⟩
  intro X W hXX₀ hWmem hWshell _hdens
  obtain ⟨hn₀X, h5X, hX1⟩ := hX₀ X hXX₀
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  by_cases hbig : n₀ ≤ W.card
  · -- The projective theorem at `d = 1`.
    set V : Finset (Fin 1 → ℤ) := W.map dOneEmbedding with hV
    have hcard : V.card = W.card := Finset.card_map _
    have hsub : V ⊆ coordinateBox (fun _ : Fin 1 => 2 * X) := by
      intro v hv
      obtain ⟨a, haW, rfl⟩ := Finset.mem_map.mp hv
      rw [mem_coordinateBox]
      intro i
      obtain ⟨_, ha2⟩ := hWmem a haW
      show -((2 * X : ℕ) : ℤ) ≤ (a : ℤ) ∧ (a : ℤ) ≤ ((2 * X : ℕ) : ℤ)
      constructor <;> [push_cast; push_cast] <;> omega
    have hbox : (coordinateBox (fun _ : Fin 1 => 2 * X)).card = 4 * X + 1 := by
      rw [card_coordinateBox, Fin.prod_univ_one]
      omega
    have hmain := projective_theorem_of_descent hε2 hc hstep 1 dOneFunctional X
      V (fun _ => 2 * X) hX1 (by rw [hcard]; exact hbig) hsub
      (shellNonDividing_dOne hWshell)
    rw [hcard, hbox, sigma_one] at hmain
    have h4X : ((4 * X + 1 : ℕ) : ℝ) ≤ 5 * (X : ℝ) := by
      have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
      push_cast
      linarith
    have hexp : (0 : ℝ) ≤ 1 / 5 + ε / 2 := by linarith
    calc (W.card : ℝ)
        ≤ ((4 * X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) := hmain
      _ ≤ (5 * (X : ℝ)) ^ ((1 : ℝ) / 5 + ε / 2) :=
          Real.rpow_le_rpow (by positivity) h4X hexp
      _ = (5 : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) * (X : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
          Real.mul_rpow (by norm_num) hXR.le
      _ ≤ (X : ℝ) ^ (ε / 2) * (X : ℝ) ^ ((1 : ℝ) / 5 + ε / 2) :=
          mul_le_mul_of_nonneg_right h5X (Real.rpow_nonneg hXR.le _)
      _ = (X : ℝ) ^ ((1 : ℝ) / 5 + ε) := by
          rw [← Real.rpow_add hXR]; congr 1; ring
  · push Not at hbig
    calc (W.card : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hbig.le
      _ ≤ (X : ℝ) ^ ((1 : ℝ) / 5 + ε) := hn₀X

/-- **Main upper epsilon bound, given a descent supplier**: `F N ≤ N^{1/5+ε}`
eventually.  Composition `main_upper_eps_of_projective ∘
projective_theorem_dOne`. -/
theorem main_upper_eps_of_descent (hsupply : DescentSupplier) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (F N : ℝ) ≤ Real.rpow (N : ℝ) ((1 : ℝ) / 5 + ε) :=
  main_upper_eps_of_projective (projective_theorem_dOne hsupply)

/-- **The main theorem, given a descent supplier**:
`log F(N)/log N → 1/5`.  The entire Erdős 131 upper bound is reduced to
`DescentSupplier`. -/
theorem main_log_limit_of_descent (hsupply : DescentSupplier) :
    Filter.Tendsto (fun N : ℕ => Real.log (F N) / Real.log N)
      Filter.atTop (nhds ((1 : ℝ) / 5)) :=
  main_log_limit_of_upper (main_upper_eps_of_descent hsupply)

/-! ## Toward discharging the descent step

The manuscript's one-step analysis (Manuscript.tex 1858–2024) produces, from
an excessive stage, a new stage with *counting* estimates (`n^{1−ε}` point
retention plus per-case box bounds).  Here we prove the entire *numerology
conversion*: those counting estimates imply the excess-gain/box-shrink
disjunction of `DescentStep`.  The remaining `TODO(orchestrator)` input is
`RawStep` — the geometric one-step output itself. -/

/-- Nontrivial boxes force positive ambient dimension (a `d = 0` box is the
single point `Fin 0 → ℤ`). -/
theorem one_le_dim_of_two_le_box {d : ℕ} {M : Fin d → ℕ}
    (h : 2 ≤ (coordinateBox M).card) : 1 ≤ d := by
  by_contra h0
  push Not at h0
  interval_cases d
  rw [card_coordinateBox] at h
  simp at h

/-- Excessive stages have positive ambient dimension. -/
theorem ExcessiveStage.one_le_dim {ζ₀ : ℝ} {X : ℕ} {s : PrepStage X}
    (h : ExcessiveStage ζ₀ s) (hζ₀ : 0 ≤ ζ₀) : 1 ≤ s.dim :=
  one_le_dim_of_two_le_box (h.two_le_box hζ₀)

/-- `σ` is monotone (with the `d ≤ 1` plateau `σ₀ = σ₁ = 1/5`). -/
theorem sigma_le_sigma {d e : ℕ} (hde : d ≤ e) : sigma d ≤ sigma e := by
  rcases Nat.lt_or_ge d 1 with hd | hd
  · have hd0 : d = 0 := by omega
    have h0 : sigma d = 1 / 5 := by rw [hd0]; norm_num [sigma]
    rw [h0]
    exact one_fifth_le_sigma e
  · rcases eq_or_lt_of_le hde with rfl | h
    · exact le_rfl
    · exact (sigma_lt_sigma hd h).le

/-- **Exactness of the excess**: `|B|^{σ_d+ζ} = |V|` for `ζ = stageExcess`
(the manuscript's defining identity `p = log n / log |B|`). -/
theorem rpow_sigma_add_stageExcess {X : ℕ} {s : PrepStage X}
    (hbox : 2 ≤ (coordinateBox s.M).card) (hV : 1 ≤ s.V.card) :
    ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + stageExcess s) =
      (s.V.card : ℝ) := by
  have hB2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by exact_mod_cast hbox
  have hBpos : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by linarith
  have hlogB : Real.log ((coordinateBox s.M).card : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  have hVpos : (0 : ℝ) < (s.V.card : ℝ) := by
    have : 0 < s.V.card := hV
    exact_mod_cast this
  have hexp : sigma s.dim + stageExcess s =
      Real.log (s.V.card : ℝ) / Real.log ((coordinateBox s.M).card : ℝ) := by
    unfold stageExcess; ring
  rw [hexp, Real.rpow_def_of_pos hBpos, mul_comm, div_mul_cancel₀ _ hlogB,
    Real.exp_log hVpos]

/-- Counting-to-excess conversion: a strict counting bound at exponent `q`
forces exact excess above `q − σ_dim`. -/
theorem lt_stageExcess_of_rpow_lt {X : ℕ} {s : PrepStage X} {q : ℝ}
    (hbox : 2 ≤ (coordinateBox s.M).card)
    (h : ((coordinateBox s.M).card : ℝ) ^ q < (s.V.card : ℝ)) :
    q - sigma s.dim < stageExcess s := by
  have hB2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by exact_mod_cast hbox
  have hBpos : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by linarith
  have hlogB : 0 < Real.log ((coordinateBox s.M).card : ℝ) :=
    Real.log_pos (by linarith)
  have hlt : q * Real.log ((coordinateBox s.M).card : ℝ) <
      Real.log (s.V.card : ℝ) := by
    have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hBpos q) h
    rwa [Real.log_rpow hBpos] at hlog
  have hdiv : q < Real.log (s.V.card : ℝ) /
      Real.log ((coordinateBox s.M).card : ℝ) := by
    rw [lt_div_iff₀ hlogB]
    exact hlt
  unfold stageExcess
  linarith

/-- **Counting form of the descent step**: from an excessive stage, a new
stage beating the *counting* exponent `σ_dim' + ζ + c` (excess-gain case) or
`σ_dim' + ζ` with a strictly smaller box (same-dimension case), where
`ζ = stageExcess s`.  This is what the geometric pipeline outputs. -/
def CountingStep (ζ₀ c : ℝ) (n₁ : ℕ) : Prop :=
  ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X →
    ExcessiveStage ζ₀ s → n₁ ≤ s.V.card →
    ∃ s' : PrepStage X, n₁ ≤ s'.V.card ∧
      (((coordinateBox s'.M).card : ℝ) ^
          (sigma s'.dim + stageExcess s + c) < (s'.V.card : ℝ) ∨
        (((coordinateBox s'.M).card : ℝ) ^
            (sigma s'.dim + stageExcess s) < (s'.V.card : ℝ) ∧
          (coordinateBox s'.M).card < (coordinateBox s.M).card))

/-- Counting bounds convert to the descent step (log bookkeeping only). -/
theorem descentStep_of_countingStep {ζ₀ c : ℝ} {n₁ : ℕ} (hζ₀ : 0 < ζ₀)
    (hc : 0 ≤ c) (hn₁ : 2 ≤ n₁) (h : CountingStep ζ₀ c n₁) :
    DescentStep ζ₀ c n₁ := by
  intro X s hX hbad hn
  obtain ⟨s', hn', hcase⟩ := h X s hX hbad hn
  have hbox' : 2 ≤ (coordinateBox s'.M).card :=
    le_trans (le_trans hn₁ hn') (stage_card_le_box s')
  have hB'1 : (1 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by
    have : (2 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by exact_mod_cast hbox'
    linarith
  have hζe : ζ₀ < stageExcess s := hbad.zeta_lt_stageExcess hζ₀.le
  rcases hcase with hcount | ⟨hcount, hboxlt⟩
  · -- excess-gain case
    have hbad' : ExcessiveStage ζ₀ s' := by
      unfold ExcessiveStage
      refine lt_of_le_of_lt ?_ hcount
      exact Real.rpow_le_rpow_of_exponent_le hB'1 (by linarith)
    have hgain := lt_stageExcess_of_rpow_lt hbox' hcount
    exact ⟨s', hbad', hn', Or.inl (by linarith)⟩
  · -- same-dimension case
    have hbad' : ExcessiveStage ζ₀ s' := by
      unfold ExcessiveStage
      refine lt_of_le_of_lt ?_ hcount
      exact Real.rpow_le_rpow_of_exponent_le hB'1 (by linarith)
    have hmono := lt_stageExcess_of_rpow_lt hbox' hcount
    exact ⟨s', hbad', hn', Or.inr ⟨by linarith, hboxlt⟩⟩

/-- **Raw one-step output** (`TODO(orchestrator)`: this is the geometric
content of the manuscript's one-step analysis, to be discharged from
`unshifted_preprocessing_toward` + `projective_convexity_assembled` +
`weighted_density` + `cap_lifting_deficient`/`cap_cone_count`).  From an
excessive stage `s` (`n = |V|`, `ζ = stageExcess s`), a new stage `s'` with
`|V'| ≥ n₁` and one of:

* **up-move** (`dim < dim' ≤ D`): `|V'| ≥ n^{1−ε}` and the box estimate
  `|B'| ≤ n^{1/(σ_d+ζ) − (1−ε)(dim'−dim)}` (manuscript: `|B̃| ≪ n^a`);
* **down-move** (`dim' < dim`): `|V'| ≥ n^{1−ε}` and `|B'| ≤ |B|`;
* **same-dimension** (`dim' = dim`): the density increment
  `|B'|^{σ_d+ζ} < |V'|` with `|B'| < |B|`. -/
def RawStep (D : ℕ) (ζ₀ ε : ℝ) (n₁ : ℕ) : Prop :=
  ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X →
    ExcessiveStage ζ₀ s → n₁ ≤ s.V.card →
    ∃ s' : PrepStage X, n₁ ≤ s'.V.card ∧
      ((s.dim < s'.dim ∧ s'.dim ≤ D ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            (s.V.card : ℝ) ^ (1 / (sigma s.dim + stageExcess s) -
              (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)))) ∨
        (s'.dim < s.dim ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          (coordinateBox s'.M).card ≤ (coordinateBox s.M).card) ∨
        (s'.dim = s.dim ∧
          ((coordinateBox s'.M).card : ℝ) ^
              (sigma s.dim + stageExcess s) < (s'.V.card : ℝ) ∧
          (coordinateBox s'.M).card < (coordinateBox s.M).card))

/-- **The numerology conversion** (`thm:projective-main`, one-step analysis).
The raw counting output `RawStep` yields the counting descent step with the
uniform excess gain `c = min(c₊/10, Δ_D/4)`: an up-move raises the excess via
`numerology` (`(σ_e+ζ)·a ≤ 1−c₊` plus `a ≤ 5` absorbs the gain), a down-move
via the sigma gap `Δ_D` (`exists_sigma_gap`), and a same-dimensional move
strictly shrinks the box.  The `a ≤ 0` branch of an up-move is impossible
(the box would collapse below the retained points). -/
theorem countingStep_of_rawStep (D : ℕ) (hD : 2 ≤ D) {ζ₀ : ℝ} (hζ₀ : 0 < ζ₀)
    (hDcap : 2 / ζ₀ ≤ (D : ℝ)) :
    ∃ c ε₁ : ℝ, 0 < c ∧ 0 < ε₁ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ n₁ : ℕ, 2 ≤ n₁ →
        RawStep D ζ₀ ε n₁ → CountingStep ζ₀ c n₁ := by
  obtain ⟨ε₀, cstar, hε₀, hcstar, hnum⟩ := numerology hD hζ₀
  obtain ⟨Δ, hΔ, hgap⟩ := exists_sigma_gap D hD
  refine ⟨min (cstar / 10) (Δ / 4),
    min (min (ε₀ / 2) (1 / 2)) (min (cstar / 4) (Δ / 4)),
    by positivity, by positivity, ?_⟩
  intro ε hε hεle n₁ hn₁ hraw X s hX hbad hn
  set c : ℝ := min (cstar / 10) (Δ / 4) with hcdef
  have hc0 : 0 < c := by positivity
  have hεε₀ : ε < ε₀ := by
    have h1 : ε ≤ ε₀ / 2 :=
      hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have hεhalf : ε ≤ 1 / 2 :=
    hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεc : ε ≤ cstar / 4 :=
    hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεΔ : ε ≤ Δ / 4 :=
    hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s', hn', hcase⟩ := hraw X s hX hbad hn
  -- Common stage facts.
  have hbox2 : 2 ≤ (coordinateBox s.M).card := hbad.two_le_box hζ₀.le
  have hbox2' : 2 ≤ (coordinateBox s'.M).card :=
    le_trans (le_trans hn₁ hn') (stage_card_le_box s')
  have hd1 : 1 ≤ s.dim := hbad.one_le_dim hζ₀.le
  have hd1' : 1 ≤ s'.dim := one_le_dim_of_two_le_box hbox2'
  set ζ : ℝ := stageExcess s with hζdef
  have hζlo : ζ₀ < ζ := hbad.zeta_lt_stageExcess hζ₀.le
  have hζhi : ζ ≤ 1 - sigma s.dim := hbad.stageExcess_le hζ₀.le
  have hσd := sigma_pos s.dim
  have hσd5 := one_fifth_le_sigma s.dim
  have hσd' := sigma_pos s'.dim
  have hp : 0 < sigma s.dim + ζ := by linarith
  have hn2 : 2 ≤ s.V.card := le_trans hn₁ hn
  have hnR : (2 : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn2
  have hn1R : (1 : ℝ) < (s.V.card : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (s.V.card : ℝ) := by linarith
  have hB2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast hbox2
  have hB'2 : (2 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by
    exact_mod_cast hbox2'
  have hB'1 : (1 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by linarith
  have hB'0 : (0 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by linarith
  have hnexact : ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ) =
      (s.V.card : ℝ) := rpow_sigma_add_stageExcess hbox2 (by omega)
  refine ⟨s', hn', ?_⟩
  rcases hcase with ⟨hlt, hDle, hcard, hboxle⟩ | ⟨hlt, hcard, hboxle⟩ |
    ⟨heq, hcount, hboxlt⟩
  · -- UP-MOVE: numerology gain.
    left
    set a : ℝ := 1 / (sigma s.dim + ζ) -
      (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)) with hadef
    -- `a > 0`, else the box collapses.
    have hapos : 0 < a := by
      by_contra hcon
      push Not at hcon
      have hb1 : ((coordinateBox s'.M).card : ℝ) ≤ 1 :=
        hboxle.trans
          (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hcon)
      linarith
    -- `a ≤ 5` from `σ_d + ζ ≥ 1/5`.
    have ha5 : a ≤ 5 := by
      have h1 : 1 / (sigma s.dim + ζ) ≤ 1 / (1 / 5 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have h2 : (0 : ℝ) ≤ (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)) := by
        have : (s.dim : ℝ) ≤ (s'.dim : ℝ) := by exact_mod_cast hlt.le
        nlinarith
      rw [hadef]
      norm_num at h1 ⊢
      linarith
    -- The numerology inequality `(σ_e+ζ)·a ≤ 1 − c₊`.
    have hnume : (sigma s'.dim + ζ) * a ≤ 1 - cstar := by
      have := hnum s.dim s'.dim hd1 hlt hDle ζ hζlo.le hζhi ε hε hεε₀
      rw [hadef]
      calc (sigma s'.dim + ζ) *
            (1 / (sigma s.dim + ζ) - (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)))
          = (sigma s'.dim + ζ) *
            (1 / (sigma s.dim + ζ) - (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ))) := rfl
        _ ≤ 1 - cstar := this
    -- Assemble the chain.
    have hc10 : c ≤ cstar / 10 := min_le_left _ _
    have hexp0 : (0 : ℝ) ≤ sigma s'.dim + ζ + cstar / 10 := by linarith
    have step1 : ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ + c) ≤
        ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ + cstar / 10) :=
      Real.rpow_le_rpow_of_exponent_le hB'1 (by linarith)
    have step2 : ((coordinateBox s'.M).card : ℝ) ^
        (sigma s'.dim + ζ + cstar / 10) ≤
        ((s.V.card : ℝ) ^ a) ^ (sigma s'.dim + ζ + cstar / 10) :=
      Real.rpow_le_rpow hB'0 hboxle hexp0
    have step3 : ((s.V.card : ℝ) ^ a) ^ (sigma s'.dim + ζ + cstar / 10) =
        (s.V.card : ℝ) ^ (a * (sigma s'.dim + ζ + cstar / 10)) :=
      (Real.rpow_mul hnpos.le _ _).symm
    have hexpbound : a * (sigma s'.dim + ζ + cstar / 10) ≤ 1 - cstar / 2 := by
      have h1 : a * (sigma s'.dim + ζ + cstar / 10) =
          (sigma s'.dim + ζ) * a + a * (cstar / 10) := by ring
      have h2 : a * (cstar / 10) ≤ 5 * (cstar / 10) :=
        mul_le_mul_of_nonneg_right ha5 (by positivity)
      rw [h1]
      linarith
    have step4 : (s.V.card : ℝ) ^ (a * (sigma s'.dim + ζ + cstar / 10)) ≤
        (s.V.card : ℝ) ^ (1 - cstar / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hexpbound
    have step5 : (s.V.card : ℝ) ^ (1 - cstar / 2) <
        (s.V.card : ℝ) ^ (1 - ε) :=
      Real.rpow_lt_rpow_of_exponent_lt hn1R (by linarith)
    calc ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ + c)
        ≤ ((coordinateBox s'.M).card : ℝ) ^
            (sigma s'.dim + ζ + cstar / 10) := step1
      _ ≤ ((s.V.card : ℝ) ^ a) ^ (sigma s'.dim + ζ + cstar / 10) := step2
      _ = (s.V.card : ℝ) ^ (a * (sigma s'.dim + ζ + cstar / 10)) := step3
      _ ≤ (s.V.card : ℝ) ^ (1 - cstar / 2) := step4
      _ < (s.V.card : ℝ) ^ (1 - ε) := step5
      _ ≤ (s'.V.card : ℝ) := hcard
  · -- DOWN-MOVE: sigma-gap gain.
    left
    have hd2 : 2 ≤ s.dim := by omega
    have hdD : s.dim ≤ D := by
      have h1 := hbad.dim_cast_le hζ₀
      have h2 : (s.dim : ℝ) ≤ (D : ℝ) := le_trans h1 hDcap
      exact_mod_cast h2
    have hσgap : sigma s'.dim + Δ ≤ sigma s.dim := by
      have h1 : sigma (s.dim - 1) + Δ ≤ sigma s.dim := hgap s.dim hd2 hdD
      have h2 : sigma s'.dim ≤ sigma (s.dim - 1) :=
        sigma_le_sigma (by omega)
      linarith
    have hcΔ : c ≤ Δ / 4 := min_le_right _ _
    have hexplt : sigma s'.dim + ζ + c < (1 - ε) * (sigma s.dim + ζ) := by
      have h1 : (1 - ε) * (sigma s.dim + ζ) =
          sigma s.dim + ζ - ε * (sigma s.dim + ζ) := by ring
      have h2 : ε * (sigma s.dim + ζ) ≤ ε := by nlinarith
      have h3 : sigma s'.dim + c + ε < sigma s.dim := by linarith
      linarith
    have hexp0 : (0 : ℝ) ≤ sigma s'.dim + ζ + c := by linarith
    have hBB : ((coordinateBox s'.M).card : ℝ) ≤
        ((coordinateBox s.M).card : ℝ) := by exact_mod_cast hboxle
    have step1 : ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ + c) ≤
        ((coordinateBox s.M).card : ℝ) ^ (sigma s'.dim + ζ + c) :=
      Real.rpow_le_rpow hB'0 hBB hexp0
    have step2 : ((coordinateBox s.M).card : ℝ) ^ (sigma s'.dim + ζ + c) <
        ((coordinateBox s.M).card : ℝ) ^ ((1 - ε) * (sigma s.dim + ζ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) hexplt
    have step3 : ((coordinateBox s.M).card : ℝ) ^
        ((1 - ε) * (sigma s.dim + ζ)) = (s.V.card : ℝ) ^ (1 - ε) := by
      rw [mul_comm, Real.rpow_mul (by linarith), hnexact]
    calc ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ + c)
        ≤ ((coordinateBox s.M).card : ℝ) ^ (sigma s'.dim + ζ + c) := step1
      _ < ((coordinateBox s.M).card : ℝ) ^ ((1 - ε) * (sigma s.dim + ζ)) :=
          step2
      _ = (s.V.card : ℝ) ^ (1 - ε) := step3
      _ ≤ (s'.V.card : ℝ) := hcard
  · -- SAME-DIMENSION: strict box shrink.
    right
    refine ⟨?_, hboxlt⟩
    have hσeq : sigma s'.dim = sigma s.dim := by rw [heq]
    rw [hσeq]
    exact hcount

/-- **Descent supplier from raw steps**: if for every excess parameter `ζ₀`
the geometric pipeline supplies raw one-step outputs at some dimension bound
`D ≥ max(2, 2/ζ₀)` and every sufficiently small `ε`, then the descent
supplier — and with it the whole main theorem — follows. -/
theorem descentSupplier_of_rawStep
    (h : ∀ ζ₀ : ℝ, 0 < ζ₀ → ∃ D : ℕ, 2 ≤ D ∧ 2 / ζ₀ ≤ (D : ℝ) ∧
      ∀ ε₁ : ℝ, 0 < ε₁ → ∃ (ε : ℝ) (n₁ : ℕ), 0 < ε ∧ ε ≤ ε₁ ∧ 2 ≤ n₁ ∧
        RawStep D ζ₀ ε n₁) :
    DescentSupplier := by
  intro ζ₀ hζ₀
  obtain ⟨D, hD, hDcap, hsup⟩ := h ζ₀ hζ₀
  obtain ⟨c, ε₁, hc, hε₁, hmain⟩ := countingStep_of_rawStep D hD hζ₀ hDcap
  obtain ⟨ε, n₁, hε, hεle, hn₁, hraw⟩ := hsup ε₁ hε₁
  exact ⟨c, n₁, hc,
    descentStep_of_countingStep hζ₀ hc.le hn₁ (hmain ε hε hεle n₁ hn₁ hraw)⟩

/-! ## Splitting `RawStep`: preprocessing supplier + irreducible increment

`RawStep` is the manuscript's one-step analysis.  It decomposes into the
*preprocessing* half (`unshifted_preprocessing_toward`: reach an unshiftedly
`(δ,γ)`-irreducible stage, with the three-case counting bookkeeping) and the
*pipeline* half (projective convexity + weighted density + cap lifting at the
irreducible stage).  Here we define the two supplier predicates and prove the
composition, including the manuscript's same-dimensional ratio computation
`|A'|/|B'|^p ≥ η^{a−p}·ρ^{1−K₀p} > 1` (Manuscript.tex 1993–2016). -/

/-- **Same-dimensional ratio numerology** (Manuscript.tex 1993–2016): from
`A' ≥ ρ·η^a·n`, `B' ≤ η·ρ^K·B`, `B^p = n` with `a < p`, `Kp ≥ 1`,
`0 < η < 1`, `0 < ρ ≤ 1`, the new pair strictly beats the old exponent:
`B'^p < A'`.  (The manuscript's `η^{a−p}ρ^{1−Kp} → ∞` in exact form; the
implicit constants are absorbed by the supplier.) -/
theorem sameDim_ratio_lt {n A' B B' η ρ a K p : ℝ}
    (hB1 : 1 ≤ B) (hn : B ^ p = n) (hp0 : 0 < p)
    (hη0 : 0 < η) (hη1 : η < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hap : a < p) (hKp : 1 ≤ K * p) (hB'0 : 0 ≤ B')
    (hA' : ρ * η ^ a * n ≤ A') (hB' : B' ≤ η * ρ ^ K * B) :
    B' ^ p < A' := by
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
  have hnpos : 0 < n := hn ▸ Real.rpow_pos_of_pos hB0 p
  have hηa : 0 < η ^ a := Real.rpow_pos_of_pos hη0 a
  have hρK : (0 : ℝ) < ρ ^ K := Real.rpow_pos_of_pos hρ0 K
  have h1 : B' ^ p ≤ (η * ρ ^ K * B) ^ p :=
    Real.rpow_le_rpow hB'0 hB' hp0.le
  have h2 : (η * ρ ^ K * B) ^ p = η ^ p * ρ ^ (K * p) * n := by
    rw [Real.mul_rpow (by positivity) hB0.le, Real.mul_rpow hη0.le hρK.le,
      ← Real.rpow_mul hρ0.le, hn]
  have h3 : η ^ p * ρ ^ (K * p) < ρ * η ^ a := by
    have e1 : η ^ a * η ^ (p - a) = η ^ p := by
      rw [← Real.rpow_add hη0]; congr 1; ring
    have e2 : ρ ^ (1 : ℝ) * ρ ^ (K * p - 1) = ρ ^ (K * p) := by
      rw [← Real.rpow_add hρ0]; congr 1; ring
    rw [Real.rpow_one] at e2
    have hη2 : η ^ (p - a) < 1 :=
      Real.rpow_lt_one hη0.le hη1 (by linarith)
    have hρ2 : ρ ^ (K * p - 1) ≤ 1 :=
      Real.rpow_le_one hρ0.le hρ1 (by linarith)
    have hsmall : η ^ (p - a) * ρ ^ (K * p - 1) < 1 := by
      have hstep : η ^ (p - a) * ρ ^ (K * p - 1) ≤ η ^ (p - a) * 1 :=
        mul_le_mul_of_nonneg_left hρ2 (Real.rpow_pos_of_pos hη0 _).le
      rw [mul_one] at hstep
      exact lt_of_le_of_lt hstep hη2
    calc η ^ p * ρ ^ (K * p)
        = (η ^ a * ρ) * (η ^ (p - a) * ρ ^ (K * p - 1)) := by
          rw [← e1, ← e2]; ring
      _ < (η ^ a * ρ) * 1 :=
          mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = ρ * η ^ a := by ring
  calc B' ^ p ≤ η ^ p * ρ ^ (K * p) * n := h1.trans_eq h2
    _ < ρ * η ^ a * n := mul_lt_mul_of_pos_right h3 hnpos
    _ ≤ A' := hA'

/-- **Preprocessing supplier** (`TODO(orchestrator)`: discharge from
`unshifted_preprocessing_toward` + the manuscript's chain numerics,
Manuscript.tex 560–660/1869–1903).  From an excessive stage, the preprocessing
iteration reaches a stage `s'` with `|V'| ≥ n₁` and one of:

* **up-move** (`dim < dim' ≤ D`): retention `|V'| ≥ n^{1−ε}` and the box
  estimate `|B'| ≤ n^{1/(σ_d+ζ) − (1−ε)(dim'−dim)}`;
* **down-move** (`dim' < dim`): retention `|V'| ≥ n^{1−ε}`, `|B'| ≤ |B|`;
* **same dimension**: `s'` unshiftedly `(δ,γ)`-irreducible with cardinality
  ratio `ρ ≥ n^{−ε}` and box decay `|B'| ≤ ρ^{K₀}|B|` (manuscript:
  `|B̃| ≪ ρ^{K₀}|B|`, constants absorbed). -/
def PrepSupplier {β : ℝ} (pkgs : ∀ r, Package r β) (D : ℕ)
    (ζ₀ ε δ γ K₀ : ℝ) (n₁ : ℕ) : Prop :=
  ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X →
    ExcessiveStage ζ₀ s → n₁ ≤ s.V.card →
    ∃ s' : PrepStage X, n₁ ≤ s'.V.card ∧
      ((s.dim < s'.dim ∧ s'.dim ≤ D ∧
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
              ρ ^ K₀ * ((coordinateBox s.M).card : ℝ)))

/-- **Irreducible-stage increment** (`TODO(orchestrator)`: discharge from
`projective_convexity_assembled` + `weighted_density` +
`cap_lifting_deficient`/`cap_cone_count`, Manuscript.tex 1941–2024).  At an
unshiftedly `(δ,γ)`-irreducible stage, the projective pipeline yields `s'`
with `|V'| ≥ n₁` and either

* a **dimension-lowering cap** (`dim' < dim`): `|V'| ≥ |V|^{1−ε}` and
  `|B'| ≤ |B|`; or
* a **same-dimensional cap**: a volume ratio `η ∈ (0,1)` with retention
  `|V'| ≥ η^{σ_d+ζ₀−ν}·|V|` (manuscript: `η^{κ_{d−1}+ε}`, and
  `κ_{d−1}+ε ≤ σ_d+ζ₀−ν` by the choice of `ε`, `ν`) and box decay
  `|B'| ≤ η·|B|`. -/
def IrreducibleIncrement {β : ℝ} (pkgs : ∀ r, Package r β)
    (ζ₀ ε δ γ ν : ℝ) (n₁ : ℕ) : Prop :=
  ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X → n₁ ≤ s.V.card →
    StageIrreducible pkgs δ γ s →
    ∃ s' : PrepStage X, n₁ ≤ s'.V.card ∧
      ((s'.dim < s.dim ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          (coordinateBox s'.M).card ≤ (coordinateBox s.M).card) ∨
        (s'.dim = s.dim ∧ ∃ η : ℝ, 0 < η ∧ η < 1 ∧
          η ^ (sigma s.dim + ζ₀ - ν) * (s.V.card : ℝ) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            η * ((coordinateBox s.M).card : ℝ)))

/-- **Composition: raw step from the two suppliers** (at `2ε`).  The up/down
preprocessing branches pass through (weakening `1−ε` to `1−2ε`); in the
same-dimensional branch the increment is applied at the irreducible stage and
converted by `sameDim_ratio_lt`; a dimension-lowering cap composes the two
retentions `((n^{1−ε})^{1−ε} ≥ n^{1−2ε})`. -/
theorem rawStep_of_suppliers {β : ℝ} (pkgs : ∀ r, Package r β) (D : ℕ)
    {ζ₀ ε δ γ ν K₀ : ℝ} {n₁ : ℕ} (hζ₀ : 0 < ζ₀) (hε : 0 < ε)
    (hεhalf : ε ≤ 1 / 2) (hν : 0 < ν) (hK₀ : 5 ≤ K₀) (hn₁ : 2 ≤ n₁)
    (hprep : PrepSupplier pkgs D ζ₀ ε δ γ K₀ n₁)
    (hinc : IrreducibleIncrement pkgs ζ₀ ε δ γ ν n₁) :
    RawStep D ζ₀ (2 * ε) n₁ := by
  intro X s hX hbad hn
  have hn2 : 2 ≤ s.V.card := le_trans hn₁ hn
  have hnR : (2 : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn2
  have hn1R : (1 : ℝ) ≤ (s.V.card : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (s.V.card : ℝ) := by linarith
  have hbox2 : 2 ≤ (coordinateBox s.M).card := hbad.two_le_box hζ₀.le
  have hB2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast hbox2
  have hBpos : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by linarith
  obtain ⟨s₁, hcard₁, hcase⟩ := hprep X s hX hbad hn
  rcases hcase with ⟨hlt, hDle, hcard, hboxle⟩ | ⟨hlt, hcard, hboxle⟩ |
    ⟨heq, hirr, ρ, hρ0, hρ1, hρlow, hρcard, hρbox⟩
  · -- UP-MOVE: pass through with `ε ↦ 2ε`.
    refine ⟨s₁, hcard₁, Or.inl ⟨hlt, hDle, ?_, ?_⟩⟩
    · calc (s.V.card : ℝ) ^ (1 - 2 * ε)
          ≤ (s.V.card : ℝ) ^ (1 - ε) :=
            Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
        _ ≤ (s₁.V.card : ℝ) := hcard
    · refine hboxle.trans (Real.rpow_le_rpow_of_exponent_le hn1R ?_)
      have hed : (0 : ℝ) ≤ (s₁.dim : ℝ) - (s.dim : ℝ) := by
        have : (s.dim : ℝ) ≤ (s₁.dim : ℝ) := by exact_mod_cast hlt.le
        linarith
      have hmul : (1 - 2 * ε) * ((s₁.dim : ℝ) - (s.dim : ℝ)) ≤
          (1 - ε) * ((s₁.dim : ℝ) - (s.dim : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hed
      linarith
  · -- DOWN-MOVE: pass through with `ε ↦ 2ε`.
    refine ⟨s₁, hcard₁, Or.inr (Or.inl ⟨hlt, ?_, hboxle⟩)⟩
    calc (s.V.card : ℝ) ^ (1 - 2 * ε)
        ≤ (s.V.card : ℝ) ^ (1 - ε) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
      _ ≤ (s₁.V.card : ℝ) := hcard
  · -- SAME DIMENSION: apply the increment at the irreducible stage `s₁`.
    obtain ⟨s₂, hcard₂', hcase₂⟩ := hinc X s₁ hX hcard₁ hirr
    have hρK1 : ρ ^ K₀ ≤ 1 :=
      Real.rpow_le_one hρ0.le hρ1 (by linarith)
    have hñ : (s.V.card : ℝ) ^ (1 - ε) ≤ (s₁.V.card : ℝ) := by
      have h1 : (s.V.card : ℝ) ^ (1 - ε) =
          (s.V.card : ℝ) ^ (-ε) * (s.V.card : ℝ) := by
        rw [show (1 - ε) = -ε + 1 by ring, Real.rpow_add hnpos,
          Real.rpow_one]
      rw [h1]
      calc (s.V.card : ℝ) ^ (-ε) * (s.V.card : ℝ)
          ≤ ρ * (s.V.card : ℝ) :=
            mul_le_mul_of_nonneg_right hρlow hnpos.le
        _ ≤ (s₁.V.card : ℝ) := hρcard
    rcases hcase₂ with ⟨hlt₂, hcard₂, hbox₂⟩ | ⟨heq₂, η, hη0, hη1, hηcard, hηbox⟩
    · -- Dimension-lowering cap: RawStep down branch at `2ε`.
      refine ⟨s₂, hcard₂', Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
      · omega
      · have hstep1 : ((s.V.card : ℝ) ^ (1 - ε)) ^ (1 - ε) ≤
            (s₁.V.card : ℝ) ^ (1 - ε) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hñ (by linarith)
        have hstep2 : ((s.V.card : ℝ) ^ (1 - ε)) ^ (1 - ε) =
            (s.V.card : ℝ) ^ ((1 - ε) * (1 - ε)) :=
          (Real.rpow_mul hnpos.le _ _).symm
        have hstep3 : (s.V.card : ℝ) ^ (1 - 2 * ε) ≤
            (s.V.card : ℝ) ^ ((1 - ε) * (1 - ε)) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by nlinarith [sq_nonneg ε])
        calc (s.V.card : ℝ) ^ (1 - 2 * ε)
            ≤ (s.V.card : ℝ) ^ ((1 - ε) * (1 - ε)) := hstep3
          _ = ((s.V.card : ℝ) ^ (1 - ε)) ^ (1 - ε) := hstep2.symm
          _ ≤ (s₁.V.card : ℝ) ^ (1 - ε) := hstep1
          _ ≤ (s₂.V.card : ℝ) := hcard₂
      · have hreal : ((coordinateBox s₂.M).card : ℝ) ≤
            ((coordinateBox s.M).card : ℝ) := by
          have h1 : ((coordinateBox s₂.M).card : ℝ) ≤
              ((coordinateBox s₁.M).card : ℝ) := by exact_mod_cast hbox₂
          have h3 : ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) ≤
              1 * ((coordinateBox s.M).card : ℝ) :=
            mul_le_mul_of_nonneg_right hρK1 hBpos.le
          calc ((coordinateBox s₂.M).card : ℝ)
              ≤ ((coordinateBox s₁.M).card : ℝ) := h1
            _ ≤ ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) := hρbox
            _ ≤ 1 * ((coordinateBox s.M).card : ℝ) := h3
            _ = ((coordinateBox s.M).card : ℝ) := one_mul _
        exact_mod_cast hreal
    · -- Same-dimensional cap: the ratio numerology.
      have hσeq : sigma s₁.dim = sigma s.dim := by rw [heq]
      rw [hσeq] at hηcard
      have hζlo := hbad.zeta_lt_stageExcess hζ₀.le
      have hσ5 := one_fifth_le_sigma s.dim
      have hp0 : (0 : ℝ) < sigma s.dim + stageExcess s := by linarith
      have hexact : ((coordinateBox s.M).card : ℝ) ^
          (sigma s.dim + stageExcess s) = (s.V.card : ℝ) :=
        rpow_sigma_add_stageExcess hbox2 (by omega)
      have hB'chain : ((coordinateBox s₂.M).card : ℝ) ≤
          η * ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) := by
        calc ((coordinateBox s₂.M).card : ℝ)
            ≤ η * ((coordinateBox s₁.M).card : ℝ) := hηbox
          _ ≤ η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ)) :=
              mul_le_mul_of_nonneg_left hρbox hη0.le
          _ = η * ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) := by ring
      refine ⟨s₂, hcard₂', Or.inr (Or.inr ⟨heq₂.trans heq, ?_, ?_⟩)⟩
      · -- Counting increment at the old exponent.
        refine sameDim_ratio_lt (B := ((coordinateBox s.M).card : ℝ))
          (η := η) (ρ := ρ) (a := sigma s.dim + ζ₀ - ν) (K := K₀)
          (by linarith) hexact hp0 hη0 hη1 hρ0 hρ1 ?_ ?_
          (Nat.cast_nonneg _) ?_ hB'chain
        · linarith
        · have h5p : 5 * (sigma s.dim + stageExcess s) ≤
              K₀ * (sigma s.dim + stageExcess s) :=
            mul_le_mul_of_nonneg_right hK₀ hp0.le
          nlinarith
        · calc ρ * η ^ (sigma s.dim + ζ₀ - ν) * (s.V.card : ℝ)
              = η ^ (sigma s.dim + ζ₀ - ν) * (ρ * (s.V.card : ℝ)) := by ring
            _ ≤ η ^ (sigma s.dim + ζ₀ - ν) * (s₁.V.card : ℝ) :=
                mul_le_mul_of_nonneg_left hρcard
                  (Real.rpow_nonneg hη0.le _)
            _ ≤ (s₂.V.card : ℝ) := hηcard
      · -- Strict box shrink.
        have hreal : ((coordinateBox s₂.M).card : ℝ) <
            ((coordinateBox s.M).card : ℝ) := by
          have h2 : η * ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) <
              1 * ((coordinateBox s.M).card : ℝ) := by
            apply mul_lt_mul_of_pos_right _ hBpos
            calc η * ρ ^ K₀ ≤ η * 1 :=
                  mul_le_mul_of_nonneg_left hρK1 hη0.le
              _ = η := mul_one η
              _ < 1 := hη1
          calc ((coordinateBox s₂.M).card : ℝ)
              ≤ η * ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) := hB'chain
            _ < 1 * ((coordinateBox s.M).card : ℝ) := h2
            _ = ((coordinateBox s.M).card : ℝ) := one_mul _
        exact_mod_cast hreal

/-- **Descent supplier from the pipeline suppliers**: the main theorem is
reduced to `PrepSupplier` + `IrreducibleIncrement` (for each `ζ₀`, at a
suitable dimension bound and all sufficiently small `ε`). -/
theorem descentSupplier_of_pipeline
    (h : ∀ ζ₀ : ℝ, 0 < ζ₀ → ∃ (β : ℝ) (pkgs : ∀ r, Package r β) (D : ℕ),
      2 ≤ D ∧ 2 / ζ₀ ≤ (D : ℝ) ∧
      ∀ ε₁ : ℝ, 0 < ε₁ → ∃ (ε δ γ ν K₀ : ℝ) (n₁ : ℕ),
        0 < ε ∧ 2 * ε ≤ ε₁ ∧ ε ≤ 1 / 2 ∧ 0 < ν ∧ 5 ≤ K₀ ∧ 2 ≤ n₁ ∧
        PrepSupplier pkgs D ζ₀ ε δ γ K₀ n₁ ∧
        IrreducibleIncrement pkgs ζ₀ ε δ γ ν n₁) :
    DescentSupplier := by
  apply descentSupplier_of_rawStep
  intro ζ₀ hζ₀
  obtain ⟨β, pkgs, D, hD, hDcap, hsup⟩ := h ζ₀ hζ₀
  refine ⟨D, hD, hDcap, ?_⟩
  intro ε₁ hε₁
  obtain ⟨ε, δ, γ, ν, K₀, n₁, hε, hεle, hεhalf, hν, hK₀, hn₁, hprep, hinc⟩ :=
    hsup ε₁ hε₁
  exact ⟨2 * ε, n₁, by linarith, hεle, hn₁,
    rawStep_of_suppliers pkgs D hζ₀ hε hεhalf hν hK₀ hn₁ hprep hinc⟩

/-! ## Chain bookkeeping for preprocessing moves

Toward discharging `PrepSupplier`: the manuscript's product estimate over the
move chain (`eq:unshifted-product`, Manuscript.tex 566–572), with the exact
dimension bookkeeping (`eq:dimension-bookkeeping`).  `PrepChain` is the
explicit path data (list of `PrepMove`s); the counts of shrink/up/down moves
and the summed dimension changes are defined by recursion, and the master
box estimate telescopes the three per-move bounds. -/

/-- Explicit chain of preprocessing moves (path data for bookkeeping). -/
inductive PrepChain {X : ℕ} {β : ℝ} (pkgs : ∀ r, Package r β) (δ γ C : ℝ) :
    PrepStage X → PrepStage X → Type where
  | nil (s : PrepStage X) : PrepChain pkgs δ γ C s s
  | cons (s t u : PrepStage X) (h : PrepMove pkgs δ γ C s t)
      (rest : PrepChain pkgs δ γ C t u) : PrepChain pkgs δ γ C s u

/-- **Shrink-move box bound**: a same-dimension move shrinks the box by `γ`
(first disjunct of `PrepMove`). -/
theorem PrepMove.box_shrink {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    {δ γ C : ℝ} {s t : PrepStage X} (h : PrepMove pkgs δ γ C s t)
    (hdim : t.dim = s.dim) :
    ((coordinateBox t.M).card : ℝ) < γ * ((coordinateBox s.M).card : ℝ) := by
  obtain ⟨D, _, _, _, _, hcase⟩ := h
  rcases hcase with ⟨_, hb⟩ | ⟨hlt', _⟩ | ⟨hlt', _⟩
  · exact hb
  · omega
  · omega

/-- **Down-move box bound**: a dimension-decreasing move satisfies
`c^{d'}·|B'| ≤ C·|B|` (third disjunct of `PrepMove`). -/
theorem PrepMove.box_down {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    {δ γ C : ℝ} {s t : PrepStage X} (h : PrepMove pkgs δ γ C s t)
    (hdim : t.dim < s.dim) :
    (pkgs s.dim).c ^ t.dim * ((coordinateBox t.M).card : ℝ) ≤
      C * ((coordinateBox s.M).card : ℝ) := by
  obtain ⟨D, _, _, _, _, hcase⟩ := h
  rcases hcase with ⟨heq, _⟩ | ⟨hlt', _⟩ | ⟨hlt', hb⟩
  · omega
  · omega
  · exact hb

/-- **Up-move box decay** in scale-multiplied form: a dimension-increasing
move satisfies `c^{d'}·smin^{d'−d}·|B'| ≤ 3^{d'}·|B|`, given a lower bound
`smin` on the witness scale (the manuscript's
`|P_{j+1}| ≤ C·s(A_{j+1})^{-(d_{j+1}-d_j)}|P_j|`). -/
theorem PrepMove.box_up {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    {δ γ C : ℝ} {s t : PrepStage X} (h : PrepMove pkgs δ γ C s t)
    (hdim : s.dim < t.dim) {smin : ℝ} (hs1 : 1 ≤ smin)
    (hscale : ∀ Dw : Finset (Fin s.dim → ℤ), Dw ⊆ s.V →
      δ * (s.V.card : ℝ) ≤ (Dw.card : ℝ) →
      smin ≤ External.structureScale Dw.card) :
    (pkgs s.dim).c ^ t.dim * (smin ^ (t.dim - s.dim) *
        ((coordinateBox t.M).card : ℝ)) ≤
      3 ^ t.dim * ((coordinateBox s.M).card : ℝ) := by
  obtain ⟨D, hDV, hDcard, _, _, hcase⟩ := h
  rcases hcase with ⟨heq, _⟩ | ⟨hlt', hb⟩ | ⟨hlt', _⟩
  · omega
  · have hsDge : smin ≤ External.structureScale D.card := hscale D hDV hDcard
    have hsD1 : (1 : ℝ) ≤ External.structureScale D.card := le_trans hs1 hsDge
    have hsDpos : (0 : ℝ) < External.structureScale D.card :=
      lt_of_lt_of_le one_pos hsD1
    have hc := (pkgs s.dim).c_pos
    have hsplit : External.structureScale D.card ^ t.dim =
        External.structureScale D.card ^ (t.dim - s.dim) *
          External.structureScale D.card ^ s.dim := by
      rw [← pow_add]
      congr 1
      omega
    have hpowle : smin ^ (t.dim - s.dim) ≤
        External.structureScale D.card ^ (t.dim - s.dim) :=
      pow_le_pow_left₀ (by linarith) hsDge _
    have hBt : (0 : ℝ) ≤ ((coordinateBox t.M).card : ℝ) := Nat.cast_nonneg _
    have key : (pkgs s.dim).c ^ t.dim * (smin ^ (t.dim - s.dim) *
        ((coordinateBox t.M).card : ℝ)) *
          External.structureScale D.card ^ s.dim ≤
        3 ^ t.dim * ((coordinateBox s.M).card : ℝ) *
          External.structureScale D.card ^ s.dim := by
      calc (pkgs s.dim).c ^ t.dim * (smin ^ (t.dim - s.dim) *
            ((coordinateBox t.M).card : ℝ)) *
              External.structureScale D.card ^ s.dim
          ≤ (pkgs s.dim).c ^ t.dim *
              (External.structureScale D.card ^ (t.dim - s.dim) *
                ((coordinateBox t.M).card : ℝ)) *
              External.structureScale D.card ^ s.dim := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hpowle hBt
        _ = ((pkgs s.dim).c * External.structureScale D.card) ^ t.dim *
              ((coordinateBox t.M).card : ℝ) := by
            rw [mul_pow, hsplit]; ring
        _ ≤ 3 ^ t.dim * External.structureScale D.card ^ s.dim *
              ((coordinateBox s.M).card : ℝ) := hb
        _ = 3 ^ t.dim * ((coordinateBox s.M).card : ℝ) *
              External.structureScale D.card ^ s.dim := by ring
    exact le_of_mul_le_mul_right key (by positivity)
  · omega

namespace PrepChain

variable {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β} {δ γ C : ℝ}

/-- Number of same-dimension (shrink) moves: the manuscript's `|𝒮|`. -/
def shrinkCount : ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons s t _ _ rest =>
      (if t.dim = s.dim then 1 else 0) + shrinkCount rest

/-- Number of up-moves: the manuscript's `|𝒰|`. -/
def upCount : ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons s t _ _ rest =>
      (if s.dim < t.dim then 1 else 0) + upCount rest

/-- Number of down-moves: the manuscript's `|𝒟|`. -/
def downCount : ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons s t _ _ rest =>
      (if t.dim < s.dim then 1 else 0) + downCount rest

/-- Summed dimension increase over up-moves: the manuscript's
`U = Σ_{j∈𝒰}(d_{j+1}−d_j)` (truncated subtraction vanishes elsewhere). -/
def upSum : ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons s t _ _ rest => (t.dim - s.dim) + upSum rest

/-- Summed dimension decrease over down-moves. -/
def downSum : ∀ {a b : PrepStage X}, PrepChain pkgs δ γ C a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons s t _ _ rest => (s.dim - t.dim) + downSum rest

/-- **Exact dimension bookkeeping** (`eq:dimension-bookkeeping`):
`dim_end + downSum = dim_start + upSum`. -/
theorem dim_add_downSum_eq : ∀ {a b : PrepStage X}
    (ch : PrepChain pkgs δ γ C a b),
    b.dim + ch.downSum = a.dim + ch.upSum
  | _, _, .nil _ => by simp [downSum, upSum]
  | _, _, .cons s t u h rest => by
      have ih := dim_add_downSum_eq rest
      simp only [downSum, upSum]
      omega

/-- Each up-move raises the dimension by at least one: `|𝒰| ≤ U`. -/
theorem upCount_le_upSum : ∀ {a b : PrepStage X}
    (ch : PrepChain pkgs δ γ C a b), ch.upCount ≤ ch.upSum
  | _, _, .nil _ => le_rfl
  | _, _, .cons s t u h rest => by
      have ih := upCount_le_upSum rest
      simp only [upCount, upSum]
      split_ifs with hlt
      · omega
      · omega

/-- Each down-move lowers the dimension by at least one: `|𝒟| ≤ downSum`. -/
theorem downCount_le_downSum : ∀ {a b : PrepStage X}
    (ch : PrepChain pkgs δ γ C a b), ch.downCount ≤ ch.downSum
  | _, _, .nil _ => le_rfl
  | _, _, .cons s t u h rest => by
      have ih := downCount_le_downSum rest
      simp only [downCount, downSum]
      split_ifs with hlt
      · omega
      · omega

/-- The manuscript's `|𝒟| ≤ d₀ + U` (via the exact bookkeeping). -/
theorem downCount_le : ∀ {a b : PrepStage X}
    (ch : PrepChain pkgs δ γ C a b), ch.downCount ≤ a.dim + ch.upSum
  | a, b, ch => by
      have h1 := ch.downCount_le_downSum
      have h2 := ch.dim_add_downSum_eq
      omega

/-- A chain yields reachability. -/
theorem toReflTransGen : ∀ {a b : PrepStage X},
    PrepChain pkgs δ γ C a b →
    Relation.ReflTransGen (PrepMove pkgs δ γ C) a b
  | _, _, .nil _ => Relation.ReflTransGen.refl
  | _, _, .cons s t u h rest =>
      Relation.ReflTransGen.head h (toReflTransGen rest)

/-- Reachability yields a chain (path extraction). -/
theorem nonempty_of_reflTransGen {a b : PrepStage X}
    (h : Relation.ReflTransGen (PrepMove pkgs δ γ C) a b) :
    Nonempty (PrepChain pkgs δ γ C a b) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _⟩
  | head hxy _ ih =>
      obtain ⟨ch⟩ := ih
      exact ⟨.cons _ _ _ hxy ch⟩

/-- **Master box product estimate** (`eq:unshifted-product`): telescoping the
per-move bounds along a chain,
`smin^U·|B_end| ≤ γ^{|𝒮|}·Cup^{|𝒰|}·Cdown^{|𝒟|}·|B_start|`,
where the per-move up/down bounds are supplied at stages reachable from
`s₀` (the manuscript's thresholds `s(A_j) ≥ n^{1−ε}` etc.). -/
theorem box_master {s₀ : PrepStage X} {smin Cup Cdown : ℝ}
    (hγ0 : 0 < γ) (hCup : 0 < Cup) (hCdown : 0 < Cdown) (hs1 : 1 ≤ smin)
    (hup : ∀ x y : PrepStage X,
      Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ x →
      PrepMove pkgs δ γ C x y → x.dim < y.dim →
      smin ^ (y.dim - x.dim) * ((coordinateBox y.M).card : ℝ) ≤
        Cup * ((coordinateBox x.M).card : ℝ))
    (hdown : ∀ x y : PrepStage X,
      Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ x →
      PrepMove pkgs δ γ C x y → y.dim < x.dim →
      ((coordinateBox y.M).card : ℝ) ≤
        Cdown * ((coordinateBox x.M).card : ℝ)) :
    ∀ {a b : PrepStage X} (ch : PrepChain pkgs δ γ C a b),
      Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ a →
      smin ^ ch.upSum * ((coordinateBox b.M).card : ℝ) ≤
        γ ^ ch.shrinkCount * Cup ^ ch.upCount * Cdown ^ ch.downCount *
          ((coordinateBox a.M).card : ℝ) := by
  intro a b ch
  induction ch with
  | nil s =>
      intro _
      simp [upSum, shrinkCount, upCount, downCount]
  | cons s t u h rest ih =>
      intro hreach
      have hreacht : Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ t :=
        hreach.tail h
      have IH := ih hreacht
      have hsmin0 : (0 : ℝ) < smin := lt_of_lt_of_le one_pos hs1
      have hΓ : (0 : ℝ) ≤ γ ^ rest.shrinkCount * Cup ^ rest.upCount *
          Cdown ^ rest.downCount := by positivity
      rcases Nat.lt_trichotomy t.dim s.dim with hlt | heq | hgt
      · -- down move
        have hbnd := hdown s t hreach h hlt
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
        have hbnd := hup s t hreach h hgt
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

end PrepChain

end Nondividing
