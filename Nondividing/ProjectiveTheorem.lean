import Nondividing.Preprocessing2
import Nondividing.Numerology

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

end Nondividing
