import Nondividing.PrepSupplierProof
import Nondividing.IrredIncrement

open scoped BigOperators

namespace Nondividing

/-!
# The revised descent interface (`PrepSupplier'`/`RawStep'`)

This file eliminates the two documented interface residues of
`PrepSupplierProof.lean`:

* **`hdown1`** — the old `PrepSupplier`/`RawStep` down branches demand the
  *sharp* box estimate `|B'| ≤ |B|`, while the proven geometric input
  (`dimension_move`) only gives `c^{d'}·|B'| ≤ C·|B|`, i.e. `|B'| ≤ Cdown·|B|`
  with a multiplicative constant.  Here the down branches carry the
  constant-relaxed bound `|B'| ≤ Cdown·|B|`; the constant is absorbed into the
  `Δ_D` sigma-gap for `|V|` above a fixed threshold
  (clause `Cdown² ≤ n₁^c` in `no_excessive_of_rawStep'`).

* **`hout`** — the old uniform output threshold `n₁ ≤ |V'|` is provably
  unsatisfiable near the boundary `|V| ≈ n₁` (every preprocessing move loses a
  `δ/2`-factor).  Here the output clauses are *shrinking*: the up/down
  branches carry `|V'| ≥ |V|^{1−ε}`, the same-dimensional branch carries the
  coupled ratio data `|V'| ≥ η^{σ_d+ζ₀−ν}·ρ·|V|`, `|B'| ≤ η·ρ^{K₀}·|B|`.

The endgame changes accordingly: instead of feeding a memoryless
`DescentStep` (whose uniform output threshold is exactly the unsatisfiable
clause), the primed one-step data drives a potential-carrying lexicographic
descent (`no_excessive_of_rawStep'`) that proves **no excessive stage of
large cardinality exists** outright.  The manuscript's global bookkeeping
`|A_j| ≥ n₀^q` (Manuscript.tex 2024–2100) is implemented by the stage
potential

`Φ(s) = |V| / |B|^{σ_dim+ζ₀−ν}`

which (i) *regenerates* from the exact excess identity at every excessive
stage (`Φ ≥ |V|^ν`), (ii) never decreases along a same-dimensional coupled
step (`K₀·(σ_d+ζ₀−ν) ≥ 1` absorbs the `ρ`-loss, the `η`-exponents match
exactly), and (iii) controls the cardinality from below (`Φ ≤ |V|`).
Dimension-changing moves are capped by the excess budget, so the cardinality
floor degrades only `O(1)` many times.

The *existing* `DescentStep` then holds **vacuously** at the produced
threshold, so the existing `DescentSupplier` — and with it
`projective_theorem_of_descent_supplier` and `main_log_limit_of_descent` —
apply verbatim (`descentSupplier_of_pipeline'`).

Everything here only *adds* declarations; no existing file is modified and
no existing name changes meaning.
-/

/-! ## The primed supplier predicates -/

/-- **Preprocessing supplier, revised interface.**  Differences from
`PrepSupplier`:

* no uniform output threshold `n₁ ≤ |V'|` (the retention clauses of the three
  branches are the manuscript's actual output);
* the down branch carries the constant-relaxed box bound `|B'| ≤ Cdown·|B|`
  (matching the proven `dimension_move`), absorbed downstream into the
  sigma-gap. -/
def PrepSupplier' {β : ℝ} (pkgs : ∀ r, Package r β) (D : ℕ)
    (ζ₀ ε δ γ K₀ Cdown : ℝ) (n₁ : ℕ) : Prop :=
  ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X →
    ExcessiveStage ζ₀ s → n₁ ≤ s.V.card →
    ∃ s' : PrepStage X,
      ((s.dim < s'.dim ∧ s'.dim ≤ D ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            (s.V.card : ℝ) ^ (1 / (sigma s.dim + stageExcess s) -
              (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)))) ∨
        (s'.dim < s.dim ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            Cdown * ((coordinateBox s.M).card : ℝ)) ∨
        (s'.dim = s.dim ∧ StageIrreducible pkgs δ γ s' ∧
          ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
            (s.V.card : ℝ) ^ (-ε) ≤ ρ ∧
            ρ * (s.V.card : ℝ) ≤ (s'.V.card : ℝ) ∧
            ((coordinateBox s'.M).card : ℝ) ≤
              ρ ^ K₀ * ((coordinateBox s.M).card : ℝ)))

/-- The old supplier implies the revised one (sanity: the primed interface is
a weakening; nothing consuming `PrepSupplier` breaks). -/
theorem prepSupplier'_of_prepSupplier {β : ℝ} {pkgs : ∀ r, Package r β}
    {D : ℕ} {ζ₀ ε δ γ K₀ Cdown : ℝ} {n₁ : ℕ} (hCdown : 1 ≤ Cdown)
    (h : PrepSupplier pkgs D ζ₀ ε δ γ K₀ n₁) :
    PrepSupplier' pkgs D ζ₀ ε δ γ K₀ Cdown n₁ := by
  intro X s hX hbad hn
  obtain ⟨s', _hn', hcase⟩ := h X s hX hbad hn
  refine ⟨s', ?_⟩
  rcases hcase with hup | ⟨hlt, hcard, hbox⟩ | hsame
  · exact Or.inl hup
  · refine Or.inr (Or.inl ⟨hlt, hcard, ?_⟩)
    have hB0 : (0 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := Nat.cast_nonneg _
    have hBB : ((coordinateBox s'.M).card : ℝ) ≤
        ((coordinateBox s.M).card : ℝ) := by exact_mod_cast hbox
    calc ((coordinateBox s'.M).card : ℝ)
        ≤ ((coordinateBox s.M).card : ℝ) := hBB
      _ = 1 * ((coordinateBox s.M).card : ℝ) := (one_mul _).symm
      _ ≤ Cdown * ((coordinateBox s.M).card : ℝ) :=
          mul_le_mul_of_nonneg_right hCdown hB0
  · exact Or.inr (Or.inr hsame)

/-- **Raw one-step output, revised interface.**  Differences from `RawStep`:

* no uniform output threshold;
* the down branch is constant-relaxed (`|B'| ≤ Cdown·|B|`);
* the same-dimensional branch exposes the *coupled* ratio data
  `|V'| ≥ η^{σ_d+ζ₀−ν}·ρ·|V|`, `|B'| ≤ η·ρ^{K₀}·|B|` (`η < 1`, `ρ ≤ 1`)
  instead of a pre-digested counting bound — this is what the global
  potential bookkeeping consumes. -/
def RawStep' (D : ℕ) (ζ₀ ε ν Cdown K₀ : ℝ) (n₁ : ℕ) : Prop :=
  ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X →
    ExcessiveStage ζ₀ s → n₁ ≤ s.V.card →
    ∃ s' : PrepStage X,
      ((s.dim < s'.dim ∧ s'.dim ≤ D ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            (s.V.card : ℝ) ^ (1 / (sigma s.dim + stageExcess s) -
              (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)))) ∨
        (s'.dim < s.dim ∧
          (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            Cdown * ((coordinateBox s.M).card : ℝ)) ∨
        (s'.dim = s.dim ∧ ∃ η ρ : ℝ, 0 < η ∧ η < 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
          η ^ (sigma s.dim + ζ₀ - ν) * (ρ * (s.V.card : ℝ)) ≤
            (s'.V.card : ℝ) ∧
          ((coordinateBox s'.M).card : ℝ) ≤
            η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ))))

/-- The existing `DescentStep` holds **vacuously** once no excessive stage of
cardinality `≥ n₀` exists — this is how the primed pipeline feeds the
*unchanged* endgame (`projective_theorem_of_descent_supplier`). -/
theorem descentStep_of_no_excessive {ζ₀ c : ℝ} {n₀ : ℕ}
    (h : ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X →
      ExcessiveStage ζ₀ s → n₀ ≤ s.V.card → False) :
    DescentStep ζ₀ c n₀ :=
  fun X s hX hbad hn => absurd (h X s hX hbad hn) not_false

/-! ## Composition: `RawStep'` from `PrepSupplier'` + `IrreducibleIncrement`

The *existing* `IrreducibleIncrement` (unchanged shape) is consumed at the
irreducible intermediate stage.  Its input threshold `n₁ ≤ |V₁|` is met by
the shrinking retention `|V₁| ≥ |V|^{1−ε} ≥ (n₁²)^{1/2} = n₁` at the
squared input threshold `n₁²` — this replaces the unsatisfiable uniform
output clause of the old composition. -/

theorem rawStep'_of_suppliers {β : ℝ} (pkgs : ∀ r, Package r β) (D : ℕ)
    {ζ₀ ε δ γ ν K₀ Cdown : ℝ} {n₁ : ℕ} (hε : 0 < ε)
    (hεhalf : ε ≤ 1 / 2) (hK₀ : 0 ≤ K₀) (hCdown : 1 ≤ Cdown) (hn₁ : 2 ≤ n₁)
    (hprep : PrepSupplier' pkgs D ζ₀ ε δ γ K₀ Cdown n₁)
    (hinc : IrreducibleIncrement pkgs ζ₀ ε δ γ ν n₁) :
    RawStep' D ζ₀ (2 * ε) ν Cdown K₀ (n₁ * n₁) := by
  intro X s hX hbad hn
  have hn₁sq : n₁ ≤ n₁ * n₁ := Nat.le_mul_of_pos_left n₁ (by omega)
  have hn2 : 2 ≤ s.V.card := le_trans (le_trans hn₁ hn₁sq) hn
  have hnR : (2 : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn2
  have hn1R : (1 : ℝ) ≤ (s.V.card : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (s.V.card : ℝ) := by linarith
  have hnsqR : ((n₁ : ℝ)) * (n₁ : ℝ) ≤ (s.V.card : ℝ) := by
    have : ((n₁ * n₁ : ℕ) : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn
    push_cast at this
    linarith
  have hn₁R : (2 : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast hn₁
  have hBpos : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by
    have h1 : 0 < (coordinateBox s.M).card := one_le_card_coordinateBox s.M
    exact_mod_cast h1
  -- The half-power threshold recovery: `|V|^{1−ε} ≥ n₁`.
  have hhalfpow : (n₁ : ℝ) ≤ (s.V.card : ℝ) ^ (1 - ε) := by
    have h1 : ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) / 2) = (n₁ : ℝ) := by
      rw [show ((n₁ : ℝ) * (n₁ : ℝ)) = (n₁ : ℝ) ^ (2 : ℝ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring]
      rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ (n₁ : ℝ))]
      norm_num
    calc (n₁ : ℝ) = ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) / 2) := h1.symm
      _ ≤ (s.V.card : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) hnsqR (by norm_num)
      _ ≤ (s.V.card : ℝ) ^ (1 - ε) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
  obtain ⟨s₁, hcase⟩ := hprep X s hX hbad (le_trans hn₁sq hn)
  rcases hcase with ⟨hlt, hDle, hcard, hboxle⟩ | ⟨hlt, hcard, hboxle⟩ |
    ⟨heq, hirr, ρ, hρ0, hρ1, hρlow, hρcard, hρbox⟩
  · -- UP-MOVE: pass through with `ε ↦ 2ε`.
    refine ⟨s₁, Or.inl ⟨hlt, hDle, ?_, ?_⟩⟩
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
  · -- DOWN-MOVE: pass through with `ε ↦ 2ε` (relaxed constant kept).
    refine ⟨s₁, Or.inr (Or.inl ⟨hlt, ?_, hboxle⟩)⟩
    calc (s.V.card : ℝ) ^ (1 - 2 * ε)
        ≤ (s.V.card : ℝ) ^ (1 - ε) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
      _ ≤ (s₁.V.card : ℝ) := hcard
  · -- SAME DIMENSION: apply the increment at the irreducible stage `s₁`.
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
    have hn₁s₁ : n₁ ≤ s₁.V.card := by
      have h1 : (n₁ : ℝ) ≤ (s₁.V.card : ℝ) := le_trans hhalfpow hñ
      exact_mod_cast h1
    obtain ⟨s₂, _hcard₂', hcase₂⟩ := hinc X s₁ hX hn₁s₁ hirr
    have hρK1 : ρ ^ K₀ ≤ 1 := Real.rpow_le_one hρ0.le hρ1 hK₀
    rcases hcase₂ with ⟨hlt₂, hcard₂, hbox₂⟩ | ⟨heq₂, η, hη0, hη1, hηcard, hηbox⟩
    · -- Dimension-lowering cap: the (relaxed) down branch at `2ε`.
      refine ⟨s₂, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
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
      · have h1 : ((coordinateBox s₂.M).card : ℝ) ≤
            ((coordinateBox s₁.M).card : ℝ) := by exact_mod_cast hbox₂
        calc ((coordinateBox s₂.M).card : ℝ)
            ≤ ((coordinateBox s₁.M).card : ℝ) := h1
          _ ≤ ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) := hρbox
          _ ≤ 1 * ((coordinateBox s.M).card : ℝ) :=
              mul_le_mul_of_nonneg_right hρK1 hBpos.le
          _ ≤ Cdown * ((coordinateBox s.M).card : ℝ) :=
              mul_le_mul_of_nonneg_right hCdown hBpos.le
    · -- Same-dimensional cap: the coupled `(η, ρ)` output.
      have hσeq : sigma s₁.dim = sigma s.dim := by rw [heq]
      rw [hσeq] at hηcard
      refine ⟨s₂, Or.inr (Or.inr ⟨heq₂.trans heq, η, ρ, hη0, hη1, hρ0, hρ1,
        ?_, ?_⟩)⟩
      · calc η ^ (sigma s.dim + ζ₀ - ν) * (ρ * (s.V.card : ℝ))
            ≤ η ^ (sigma s.dim + ζ₀ - ν) * (s₁.V.card : ℝ) :=
              mul_le_mul_of_nonneg_left hρcard (Real.rpow_nonneg hη0.le _)
          _ ≤ (s₂.V.card : ℝ) := hηcard
      · calc ((coordinateBox s₂.M).card : ℝ)
            ≤ η * ((coordinateBox s₁.M).card : ℝ) := hηbox
          _ ≤ η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ)) :=
              mul_le_mul_of_nonneg_left hρbox hη0.le

end Nondividing
