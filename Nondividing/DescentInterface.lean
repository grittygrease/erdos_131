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

/-- **Composition with the capped increment**: identical to
`rawStep'_of_suppliers`, but consuming `IrreducibleIncrementCapped` — the
irreducible intermediate stage has the same dimension as the excessive input
stage, hence dimension `≤ 2/ζ₀ ≤ Dcap` (`ExcessiveStage.dim_cast_le`). -/
theorem rawStep''_of_suppliers {β : ℝ} (pkgs : ∀ r, Package r β) (D Dcap : ℕ)
    {ζ₀ ε δ γ ν K₀ Cdown : ℝ} {n₁ n₂ : ℕ} (hζ₀ : 0 < ζ₀)
    (hDcap : 2 / ζ₀ ≤ (Dcap : ℝ)) (hε : 0 < ε)
    (hεhalf : ε ≤ 1 / 2) (hK₀ : 5 ≤ K₀) (hCdown : 1 ≤ Cdown) (hn₁ : 2 ≤ n₁)
    (hn₂pow : (n₂ : ℝ) ≤ ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - ε))
    (hprep : PrepSupplier' pkgs D ζ₀ ε δ γ K₀ Cdown n₁)
    (hinc : IrreducibleIncrementCapped pkgs Dcap ζ₀ ε δ γ ν n₁ n₂) :
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
  · refine ⟨s₁, Or.inl ⟨hlt, hDle, ?_, ?_⟩⟩
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
  · refine ⟨s₁, Or.inr (Or.inl ⟨hlt, ?_, hboxle⟩)⟩
    calc (s.V.card : ℝ) ^ (1 - 2 * ε)
        ≤ (s.V.card : ℝ) ^ (1 - ε) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
      _ ≤ (s₁.V.card : ℝ) := hcard
  · -- SAME DIMENSION: the intermediate stage is capped, apply the increment.
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
    -- The dimension cap at the intermediate stage.
    have hcap₁ : s₁.dim ≤ Dcap := by
      rw [heq]
      have h2 : (s.dim : ℝ) ≤ (Dcap : ℝ) :=
        le_trans (hbad.dim_cast_le hζ₀) hDcap
      exact_mod_cast h2
    -- The second threshold at the intermediate stage.
    have hn₂s₁ : n₂ ≤ s₁.V.card := by
      have h1 : (n₂ : ℝ) ≤ (s₁.V.card : ℝ) := by
        calc (n₂ : ℝ) ≤ ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - ε) := hn₂pow
          _ ≤ (s.V.card : ℝ) ^ ((1 : ℝ) - ε) :=
              Real.rpow_le_rpow (by positivity) hnsqR (by linarith)
          _ ≤ (s₁.V.card : ℝ) := hñ
      exact_mod_cast h1
    -- The intermediate stage is excessive: `K₀(σ+ζ₀) ≥ 1` beats the ρ-loss.
    have hσ5 := one_fifth_le_sigma s.dim
    have hKσ : (1 : ℝ) ≤ K₀ * (sigma s.dim + ζ₀) := by nlinarith
    have hexc₁ : ExcessiveStage ζ₀ s₁ := by
      unfold ExcessiveStage
      have hσeq : sigma s₁.dim = sigma s.dim := by rw [heq]
      rw [hσeq]
      have hB₁0 : (0 : ℝ) ≤ ((coordinateBox s₁.M).card : ℝ) :=
        Nat.cast_nonneg _
      have hσζ0 : (0 : ℝ) ≤ sigma s.dim + ζ₀ := by linarith
      have hρK₀0 : (0 : ℝ) < ρ ^ K₀ := Real.rpow_pos_of_pos hρ0 _
      calc ((coordinateBox s₁.M).card : ℝ) ^ (sigma s.dim + ζ₀)
          ≤ (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ)) ^ (sigma s.dim + ζ₀) :=
            Real.rpow_le_rpow hB₁0 hρbox hσζ0
        _ = (ρ ^ K₀) ^ (sigma s.dim + ζ₀) *
              ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀) :=
            Real.mul_rpow hρK₀0.le hBpos.le
        _ = ρ ^ (K₀ * (sigma s.dim + ζ₀)) *
              ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀) := by
            rw [← Real.rpow_mul hρ0.le]
        _ < ρ ^ (K₀ * (sigma s.dim + ζ₀)) * (s.V.card : ℝ) := by
            apply mul_lt_mul_of_pos_left hbad
            exact Real.rpow_pos_of_pos hρ0 _
        _ ≤ ρ ^ (1 : ℝ) * (s.V.card : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hnpos.le
            exact Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 hKσ
        _ = ρ * (s.V.card : ℝ) := by rw [Real.rpow_one]
        _ ≤ (s₁.V.card : ℝ) := hρcard
    obtain ⟨s₂, _hcard₂', hcase₂⟩ := hinc X s₁ hX hn₂s₁ hcap₁ hexc₁ hirr
    have hρK1 : ρ ^ K₀ ≤ 1 :=
      Real.rpow_le_one hρ0.le hρ1 (by linarith)
    rcases hcase₂ with ⟨hlt₂, hcard₂, hbox₂⟩ | ⟨heq₂, η, hη0, hη1, hηcard, hηbox⟩
    · refine ⟨s₂, Or.inr (Or.inl ⟨?_, ?_, ?_⟩)⟩
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
    · have hσeq : sigma s₁.dim = sigma s.dim := by rw [heq]
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

/-! ## The stage potential

The manuscript's global cardinality bookkeeping `|A_j| ≥ n₀^q`
(Manuscript.tex 2024–2100) is carried by the potential
`Φ(s) = |V| / |B|^{σ_dim+ζ₀−ν}`:

* `rpow_le_descentPotential` — at every excessive stage, the exact excess
  identity `|B|^{σ+ζ} = |V|` *regenerates* the floor `Φ ≥ |V|^ν`;
* `descentPotential_le_card` — conversely `Φ ≤ |V|`, so a potential floor is a
  cardinality floor;
* `descentPotential_mono_sameDim` — along a coupled same-dimensional step the
  potential never decreases: the `η`-exponents match exactly and
  `K₀·(σ_d+ζ₀−ν) ≥ 1` absorbs the `ρ`-loss into the `ρ^{K₀}` box decay. -/

/-- The stage potential `Φ(s) = |V| / |B|^{σ_dim+ζ₀−ν}`. -/
noncomputable def descentPotential (ζ₀ ν : ℝ) {X : ℕ} (s : PrepStage X) : ℝ :=
  (s.V.card : ℝ) /
    ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν)

theorem descentPotential_nonneg (ζ₀ ν : ℝ) {X : ℕ} (s : PrepStage X) :
    0 ≤ descentPotential ζ₀ ν s :=
  div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The potential is a cardinality lower bound: `Φ(s) ≤ |V|`. -/
theorem descentPotential_le_card (ζ₀ ν : ℝ) {X : ℕ} (s : PrepStage X)
    (hθ : 0 ≤ sigma s.dim + ζ₀ - ν) :
    descentPotential ζ₀ ν s ≤ (s.V.card : ℝ) := by
  have hB1 : (1 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s.M
  have h1 : (1 : ℝ) ≤
      ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν) := by
    calc (1 : ℝ) = ((coordinateBox s.M).card : ℝ) ^ (0 : ℝ) :=
          (Real.rpow_zero _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB1 hθ
  exact div_le_self (Nat.cast_nonneg _) h1

/-- **Potential regeneration** at excessive stages: by the exact excess
identity, `Φ(s) = |B|^{ζ−ζ₀+ν} ≥ |V|^ν`. -/
theorem rpow_le_descentPotential {ζ₀ ν : ℝ} (hζ₀ : 0 < ζ₀) (hν0 : 0 ≤ ν)
    {X : ℕ} {s : PrepStage X} (hbad : ExcessiveStage ζ₀ s) :
    (s.V.card : ℝ) ^ ν ≤ descentPotential ζ₀ ν s := by
  have hbox2 : 2 ≤ (coordinateBox s.M).card := hbad.two_le_box hζ₀.le
  have hn2 : 2 ≤ s.V.card := hbad.two_le_card hζ₀.le
  have hB2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast hbox2
  have hB0 : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by linarith
  have hnR : (2 : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn2
  have hn1 : (1 : ℝ) ≤ (s.V.card : ℝ) := by linarith
  have hζlt : ζ₀ < stageExcess s := hbad.zeta_lt_stageExcess hζ₀.le
  have hexact : ((coordinateBox s.M).card : ℝ) ^
      (sigma s.dim + stageExcess s) = (s.V.card : ℝ) :=
    rpow_sigma_add_stageExcess hbox2 (by omega)
  have hVB : (s.V.card : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast stage_card_le_box s
  have hkey : descentPotential ζ₀ ν s =
      ((coordinateBox s.M).card : ℝ) ^ (stageExcess s - ζ₀ + ν) := by
    unfold descentPotential
    rw [← hexact, ← Real.rpow_sub hB0]
    congr 1
    ring
  rw [hkey]
  calc (s.V.card : ℝ) ^ ν
      ≤ (s.V.card : ℝ) ^ (stageExcess s - ζ₀ + ν) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ ≤ ((coordinateBox s.M).card : ℝ) ^ (stageExcess s - ζ₀ + ν) :=
        Real.rpow_le_rpow (by linarith) hVB (by linarith)

/-- **Potential monotonicity along a coupled same-dimensional step**:
from `|V'| ≥ η^θ·ρ·|V|` and `|B'| ≤ η·ρ^{K₀}·|B|` with `θ = σ_d+ζ₀−ν`,
`K₀·θ ≥ 1`, the potential never decreases (`ρ^{K₀θ} ≤ ρ`). -/
theorem descentPotential_mono_sameDim {ζ₀ ν K₀ η ρ : ℝ} {X : ℕ}
    {s s' : PrepStage X} (hdim : s'.dim = s.dim)
    (hθ0 : 0 ≤ sigma s.dim + ζ₀ - ν)
    (hK₀θ : 1 ≤ K₀ * (sigma s.dim + ζ₀ - ν))
    (hη0 : 0 < η) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcard : η ^ (sigma s.dim + ζ₀ - ν) * (ρ * (s.V.card : ℝ)) ≤
      (s'.V.card : ℝ))
    (hbox : ((coordinateBox s'.M).card : ℝ) ≤
      η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ))) :
    descentPotential ζ₀ ν s ≤ descentPotential ζ₀ ν s' := by
  have hB'1 : (1 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s'.M
  have hB1 : (1 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s.M
  have hB'θ : (0 : ℝ) <
      ((coordinateBox s'.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hBθ : (0 : ℝ) <
      ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hσeq : sigma s'.dim = sigma s.dim := by rw [hdim]
  show (s.V.card : ℝ) /
      ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν) ≤
    (s'.V.card : ℝ) /
      ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ₀ - ν)
  rw [hσeq, div_le_div_iff₀ hBθ hB'θ]
  -- Denominator expansion: `B'^θ ≤ η^θ·ρ^{K₀θ}·B^θ`.
  have hBB' : ((coordinateBox s'.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν) ≤
      (η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ))) ^
        (sigma s.dim + ζ₀ - ν) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hbox hθ0
  have hexpand : (η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ))) ^
      (sigma s.dim + ζ₀ - ν) =
      η ^ (sigma s.dim + ζ₀ - ν) *
        (ρ ^ (K₀ * (sigma s.dim + ζ₀ - ν)) *
          ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν)) := by
    rw [Real.mul_rpow hη0.le (by positivity),
      Real.mul_rpow (Real.rpow_nonneg hρ0.le _) (Nat.cast_nonneg _),
      ← Real.rpow_mul hρ0.le]
  -- `ρ^{K₀θ} ≤ ρ` absorbs the loss.
  have hρpow : ρ ^ (K₀ * (sigma s.dim + ζ₀ - ν)) ≤ ρ := by
    have h1 : ρ ^ (K₀ * (sigma s.dim + ζ₀ - ν)) ≤ ρ ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 hK₀θ
    rwa [Real.rpow_one] at h1
  calc (s.V.card : ℝ) *
        ((coordinateBox s'.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν)
      ≤ (s.V.card : ℝ) *
          (η ^ (sigma s.dim + ζ₀ - ν) *
            (ρ ^ (K₀ * (sigma s.dim + ζ₀ - ν)) *
              ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν))) :=
        mul_le_mul_of_nonneg_left (hBB'.trans_eq hexpand) (Nat.cast_nonneg _)
    _ ≤ (s.V.card : ℝ) *
          (η ^ (sigma s.dim + ζ₀ - ν) *
            (ρ * ((coordinateBox s.M).card : ℝ) ^
              (sigma s.dim + ζ₀ - ν))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hη0.le _)
        exact mul_le_mul_of_nonneg_right hρpow hBθ.le
    _ = (η ^ (sigma s.dim + ζ₀ - ν) * (ρ * (s.V.card : ℝ))) *
          ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν) := by
        ring
    _ ≤ (s'.V.card : ℝ) *
          ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ₀ - ν) :=
        mul_le_mul_of_nonneg_right hcard hBθ.le

/-! ## Per-branch step facts

The three branches of `RawStep'` are converted into the data the descent
consumes: the same-dimensional branch yields excess monotonicity, a strict
box shrink and potential monotonicity (`sameDim_step_facts`); the up branch
yields the numerology counting gain (`up_step_facts`); the down branch
yields the sigma-gap counting gain with the `Cdown` constant absorbed into
`Δ_D` above the threshold `Cdown² ≤ n₁^c` (`down_step_facts`). -/

/-- **Same-dimensional step conversion**: the coupled `(η,ρ)` output beats
the old exponent (`sameDim_ratio_lt`), so the new stage is excessive with
monotone excess, a strictly smaller box, and monotone potential. -/
theorem sameDim_step_facts {ζ₀ ν K₀ η ρ : ℝ} {X : ℕ} {s s' : PrepStage X}
    (hζ₀ : 0 < ζ₀) (hν0 : 0 < ν) (hνζ : ν ≤ ζ₀) (hK₀ : 5 ≤ K₀)
    (hbad : ExcessiveStage ζ₀ s) (hdim : s'.dim = s.dim)
    (hη0 : 0 < η) (hη1 : η < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcard : η ^ (sigma s.dim + ζ₀ - ν) * (ρ * (s.V.card : ℝ)) ≤
      (s'.V.card : ℝ))
    (hbox : ((coordinateBox s'.M).card : ℝ) ≤
      η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ))) :
    ExcessiveStage ζ₀ s' ∧ stageExcess s ≤ stageExcess s' ∧
      (coordinateBox s'.M).card < (coordinateBox s.M).card ∧
      descentPotential ζ₀ ν s ≤ descentPotential ζ₀ ν s' := by
  have hbox2 : 2 ≤ (coordinateBox s.M).card := hbad.two_le_box hζ₀.le
  have hn2 : 2 ≤ s.V.card := hbad.two_le_card hζ₀.le
  have hB2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast hbox2
  have hB0 : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by linarith
  have hζlt : ζ₀ < stageExcess s := hbad.zeta_lt_stageExcess hζ₀.le
  have hσ := sigma_pos s.dim
  have hσ5 := one_fifth_le_sigma s.dim
  have hp0 : 0 < sigma s.dim + stageExcess s := by linarith
  have hexact : ((coordinateBox s.M).card : ℝ) ^
      (sigma s.dim + stageExcess s) = (s.V.card : ℝ) :=
    rpow_sigma_add_stageExcess hbox2 (by omega)
  have hB'1 : (1 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s'.M
  -- The ratio numerology at the old exponent.
  have hcount : ((coordinateBox s'.M).card : ℝ) ^
      (sigma s.dim + stageExcess s) < (s'.V.card : ℝ) := by
    refine sameDim_ratio_lt (B := ((coordinateBox s.M).card : ℝ))
      (η := η) (ρ := ρ) (a := sigma s.dim + ζ₀ - ν) (K := K₀)
      hB1 hexact hp0 hη0 hη1 hρ0 hρ1 (by linarith) (by nlinarith)
      (Nat.cast_nonneg _) ?_ ?_
    · calc ρ * η ^ (sigma s.dim + ζ₀ - ν) * (s.V.card : ℝ)
          = η ^ (sigma s.dim + ζ₀ - ν) * (ρ * (s.V.card : ℝ)) := by ring
        _ ≤ (s'.V.card : ℝ) := hcard
    · calc ((coordinateBox s'.M).card : ℝ)
          ≤ η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ)) := hbox
        _ = η * ρ ^ K₀ * ((coordinateBox s.M).card : ℝ) := by ring
  -- `|V'| ≥ 2`, `|B'| ≥ 2`.
  have hB'p1 : (1 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) ^
      (sigma s.dim + stageExcess s) := by
    calc (1 : ℝ) = ((coordinateBox s'.M).card : ℝ) ^ (0 : ℝ) :=
          (Real.rpow_zero _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB'1 hp0.le
  have hV'2 : 2 ≤ s'.V.card := by
    have h1 : (1 : ℝ) < (s'.V.card : ℝ) := lt_of_le_of_lt hB'p1 hcount
    exact_mod_cast (by exact_mod_cast h1 : (1 : ℕ) < s'.V.card)
  have hbox2' : 2 ≤ (coordinateBox s'.M).card :=
    le_trans hV'2 (stage_card_le_box s')
  -- Excessiveness and excess monotonicity.
  have hσeq : sigma s'.dim = sigma s.dim := by rw [hdim]
  have hbad' : ExcessiveStage ζ₀ s' := by
    unfold ExcessiveStage
    rw [hσeq]
    refine lt_of_le_of_lt ?_ hcount
    exact Real.rpow_le_rpow_of_exponent_le hB'1 (by linarith)
  have hmono : stageExcess s ≤ stageExcess s' := by
    have h1 := lt_stageExcess_of_rpow_lt hbox2' hcount
    -- `h1 : (σ_d + ζ) − σ_{d'} < ζ'` with `σ_{d'} = σ_d`.
    rw [hσeq] at h1
    linarith
  -- Strict box shrink.
  have hboxlt : (coordinateBox s'.M).card < (coordinateBox s.M).card := by
    have hρK : ρ ^ K₀ ≤ 1 :=
      Real.rpow_le_one hρ0.le hρ1 (by linarith)
    have h1 : ((coordinateBox s'.M).card : ℝ) <
        ((coordinateBox s.M).card : ℝ) := by
      calc ((coordinateBox s'.M).card : ℝ)
          ≤ η * (ρ ^ K₀ * ((coordinateBox s.M).card : ℝ)) := hbox
        _ ≤ η * (1 * ((coordinateBox s.M).card : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hη0.le
            exact mul_le_mul_of_nonneg_right hρK hB0.le
        _ = η * ((coordinateBox s.M).card : ℝ) := by ring
        _ < 1 * ((coordinateBox s.M).card : ℝ) :=
            mul_lt_mul_of_pos_right hη1 hB0
        _ = ((coordinateBox s.M).card : ℝ) := one_mul _
    exact_mod_cast h1
  -- Potential monotonicity.
  have hΦ : descentPotential ζ₀ ν s ≤ descentPotential ζ₀ ν s' :=
    descentPotential_mono_sameDim hdim (by linarith) (by nlinarith)
      hη0 hρ0 hρ1 hcard hbox
  exact ⟨hbad', hmono, hboxlt, hΦ⟩

/-- **Up-move step conversion** (numerology gain): the raw up-move output
beats the counting exponent `σ_{dim'} + ζ + c₊/10`. -/
theorem up_step_facts {D : ℕ} {ζ₀ ε₀ cstar ε : ℝ} {X : ℕ}
    {s s' : PrepStage X} (hζ₀ : 0 < ζ₀) (hcstar : 0 < cstar)
    (hnum : ∀ (d e : ℕ), 1 ≤ d → d < e → e ≤ D →
      ∀ ζ : ℝ, ζ₀ ≤ ζ → ζ ≤ 1 - sigma d →
        ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
          (sigma e + ζ) * (1 / (sigma d + ζ) - (1 - ε') * ((e : ℝ) - d)) ≤
            1 - cstar)
    (hbad : ExcessiveStage ζ₀ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεε₀ : ε < ε₀) (hεc : ε ≤ cstar / 4)
    (hV'2 : 2 ≤ s'.V.card)
    (hlt : s.dim < s'.dim) (hDle : s'.dim ≤ D)
    (hcard : (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ))
    (hboxle : ((coordinateBox s'.M).card : ℝ) ≤
      (s.V.card : ℝ) ^ (1 / (sigma s.dim + stageExcess s) -
        (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)))) :
    ((coordinateBox s'.M).card : ℝ) ^
        (sigma s'.dim + stageExcess s + cstar / 10) < (s'.V.card : ℝ) := by
  have hd1 : 1 ≤ s.dim := hbad.one_le_dim hζ₀.le
  set ζ : ℝ := stageExcess s with hζdef
  have hζlo : ζ₀ < ζ := hbad.zeta_lt_stageExcess hζ₀.le
  have hζhi : ζ ≤ 1 - sigma s.dim := hbad.stageExcess_le hζ₀.le
  have hσd := sigma_pos s.dim
  have hσd5 := one_fifth_le_sigma s.dim
  have hσd' := sigma_pos s'.dim
  have hn2 : 2 ≤ s.V.card := hbad.two_le_card hζ₀.le
  have hnR : (2 : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn2
  have hn1R : (1 : ℝ) < (s.V.card : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (s.V.card : ℝ) := by linarith
  have hbox2' : 2 ≤ (coordinateBox s'.M).card :=
    le_trans hV'2 (stage_card_le_box s')
  have hB'2 : (2 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by
    exact_mod_cast hbox2'
  have hB'1 : (1 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by linarith
  have hB'0 : (0 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by linarith
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
    have h1 : 1 / (sigma s.dim + ζ) ≤ 5 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < sigma s.dim + ζ)]
      linarith
    have h2 : (0 : ℝ) ≤ (1 - ε) * ((s'.dim : ℝ) - (s.dim : ℝ)) := by
      have hdd : (s.dim : ℝ) ≤ (s'.dim : ℝ) := by exact_mod_cast hlt.le
      have hε1' : (0 : ℝ) ≤ 1 - ε := by linarith
      nlinarith
    rw [hadef]
    linarith
  -- The numerology inequality `(σ_e+ζ)·a ≤ 1 − c₊`.
  have hnume : (sigma s'.dim + ζ) * a ≤ 1 - cstar := by
    have := hnum s.dim s'.dim hd1 hlt hDle ζ hζlo.le hζhi ε hε hεε₀
    rw [hadef]
    exact this
  -- Assemble the chain.
  have hexp0 : (0 : ℝ) ≤ sigma s'.dim + ζ + cstar / 10 := by linarith
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
  calc ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ + cstar / 10)
      ≤ ((s.V.card : ℝ) ^ a) ^ (sigma s'.dim + ζ + cstar / 10) := step2
    _ = (s.V.card : ℝ) ^ (a * (sigma s'.dim + ζ + cstar / 10)) := step3
    _ ≤ (s.V.card : ℝ) ^ (1 - cstar / 2) := step4
    _ < (s.V.card : ℝ) ^ (1 - ε) := step5
    _ ≤ (s'.V.card : ℝ) := hcard

/-- **Down-move step conversion** (sigma-gap gain, `Cdown` absorbed): the
constant-relaxed down-move output beats the counting exponent
`σ_{dim'} + ζ + c` once `Cdown² ≤ n₁^c` and `c, ε ≤ Δ_D/8` — the gap
`σ_{dim} − σ_{dim'} ≥ Δ_D` strictly dominates the constant for
`|B| ≥ |V| ≥ n₁`. -/
theorem down_step_facts {D : ℕ} {ζ₀ Δ c ε Cdown : ℝ} {n₁ : ℕ}
    {X : ℕ} {s s' : PrepStage X}
    (hζ₀ : 0 < ζ₀) (hD : 2 ≤ D) (hDcap : 2 / ζ₀ ≤ (D : ℝ)) (hΔ : 0 < Δ)
    (hgap : ∀ r, 2 ≤ r → r ≤ D → sigma (r - 1) + Δ ≤ sigma r)
    (hbad : ExcessiveStage ζ₀ s)
    (hc : 0 < c) (hcΔ : c ≤ Δ / 8) (hε : 0 < ε) (hεΔ : ε ≤ Δ / 8)
    (hCdown : 1 ≤ Cdown) (habs : Cdown ^ 2 ≤ (n₁ : ℝ) ^ c)
    (hn : n₁ ≤ s.V.card) (hV'2 : 2 ≤ s'.V.card)
    (hlt : s'.dim < s.dim)
    (hcard : (s.V.card : ℝ) ^ (1 - ε) ≤ (s'.V.card : ℝ))
    (hboxle : ((coordinateBox s'.M).card : ℝ) ≤
      Cdown * ((coordinateBox s.M).card : ℝ)) :
    ((coordinateBox s'.M).card : ℝ) ^
        (sigma s'.dim + stageExcess s + c) < (s'.V.card : ℝ) := by
  have hbox2 : 2 ≤ (coordinateBox s.M).card := hbad.two_le_box hζ₀.le
  have hn2 : 2 ≤ s.V.card := hbad.two_le_card hζ₀.le
  have hB2 : (2 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast hbox2
  have hB0 : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (s.V.card : ℝ) := by
    have : (2 : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn2
    linarith
  set ζ : ℝ := stageExcess s with hζdef
  have hζlo : ζ₀ < ζ := hbad.zeta_lt_stageExcess hζ₀.le
  have hζhi : ζ ≤ 1 - sigma s.dim := hbad.stageExcess_le hζ₀.le
  have hζ45 : ζ ≤ 4 / 5 := hbad.stageExcess_le_one hζ₀.le
  have hσd := sigma_pos s.dim
  have hσd' := sigma_pos s'.dim
  have hσd'1 : sigma s'.dim < 1 := sigma_one_le s'.dim
  have hbox2' : 2 ≤ (coordinateBox s'.M).card :=
    le_trans hV'2 (stage_card_le_box s')
  have hB'0 : (0 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := Nat.cast_nonneg _
  have hd1' : 1 ≤ s'.dim := one_le_dim_of_two_le_box hbox2'
  have hd2 : 2 ≤ s.dim := by omega
  have hdD : s.dim ≤ D := by
    have h1 := hbad.dim_cast_le hζ₀
    have h2 : (s.dim : ℝ) ≤ (D : ℝ) := le_trans h1 hDcap
    exact_mod_cast h2
  have hσgap : sigma s'.dim + Δ ≤ sigma s.dim := by
    have h1 : sigma (s.dim - 1) + Δ ≤ sigma s.dim := hgap s.dim hd2 hdD
    have h2 : sigma s'.dim ≤ sigma (s.dim - 1) := sigma_le_sigma (by omega)
    linarith
  have hΔ20 : Δ ≤ 1 / 20 := by
    have h1 := hgap 2 (le_refl 2) hD
    have h2 : sigma (2 - 1) = sigma 1 := rfl
    rw [h2, sigma_one, sigma_two] at h1
    linarith
  have hexact : ((coordinateBox s.M).card : ℝ) ^ (sigma s.dim + ζ) =
      (s.V.card : ℝ) := rpow_sigma_add_stageExcess hbox2 (by omega)
  have hn₁B : (n₁ : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    have h1 : n₁ ≤ (coordinateBox s.M).card :=
      le_trans hn (stage_card_le_box s)
    exact_mod_cast h1
  have hn₁0 : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
  -- The exponent bounds.
  have hE0 : (0 : ℝ) ≤ sigma s'.dim + ζ + c := by linarith
  have hE2 : sigma s'.dim + ζ + c ≤ 2 := by linarith
  have hCd0 : (0 : ℝ) < Cdown := by linarith
  -- `Cdown^E ≤ B^{Δ/2}`.
  have hCdE : Cdown ^ (sigma s'.dim + ζ + c) ≤
      ((coordinateBox s.M).card : ℝ) ^ (Δ / 2) := by
    calc Cdown ^ (sigma s'.dim + ζ + c)
        ≤ Cdown ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hCdown (by push_cast; linarith)
      _ = Cdown ^ (2 : ℕ) := Real.rpow_natCast _ _
      _ ≤ (n₁ : ℝ) ^ c := habs
      _ ≤ ((coordinateBox s.M).card : ℝ) ^ c :=
          Real.rpow_le_rpow hn₁0 hn₁B hc.le
      _ ≤ ((coordinateBox s.M).card : ℝ) ^ (Δ / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  -- The strict exponent gap.
  have hexplt : Δ / 2 + (sigma s'.dim + ζ + c) < (1 - ε) * (sigma s.dim + ζ) := by
    have h1 : ε * (sigma s.dim + ζ) ≤ ε := by nlinarith
    nlinarith
  -- Assemble.
  calc ((coordinateBox s'.M).card : ℝ) ^ (sigma s'.dim + ζ + c)
      ≤ (Cdown * ((coordinateBox s.M).card : ℝ)) ^ (sigma s'.dim + ζ + c) :=
        Real.rpow_le_rpow hB'0 hboxle hE0
    _ = Cdown ^ (sigma s'.dim + ζ + c) *
          ((coordinateBox s.M).card : ℝ) ^ (sigma s'.dim + ζ + c) :=
        Real.mul_rpow hCd0.le hB0.le
    _ ≤ ((coordinateBox s.M).card : ℝ) ^ (Δ / 2) *
          ((coordinateBox s.M).card : ℝ) ^ (sigma s'.dim + ζ + c) :=
        mul_le_mul_of_nonneg_right hCdE (Real.rpow_nonneg hB0.le _)
    _ = ((coordinateBox s.M).card : ℝ) ^ (Δ / 2 + (sigma s'.dim + ζ + c)) :=
        (Real.rpow_add hB0 _ _).symm
    _ < ((coordinateBox s.M).card : ℝ) ^ ((1 - ε) * (sigma s.dim + ζ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) hexplt
    _ = (s.V.card : ℝ) ^ (1 - ε) := by
        rw [mul_comm, Real.rpow_mul (by linarith), hexact]
    _ ≤ (s'.V.card : ℝ) := hcard

/-! ## The potential-carrying descent driver

`no_excessive_of_rawStep'`: from the primed one-step data, **no excessive
stage of large cardinality exists**.  The lexicographic measure is
`(excessBudget, |box|)`; the cardinality floor is carried by the invariant
`Φ(s) ≥ n₀^{e(budget)}` with `e(b) = ν·θ^{B₀−b}`, `θ = ν(1−ε)`: dimension
moves lose exactly a `θ`-power (retention `|V'| ≥ |V|^{1−ε}` then potential
regeneration `Φ' ≥ |V'|^ν`), matched by the budget's strict drop
(`e(b)·θ = e(b−1)`); same-dimensional moves keep the potential
(`descentPotential_mono_sameDim`). -/

theorem no_excessive_of_rawStep' {D : ℕ} {ζ₀ ε ν Cdown K₀ cstar ε₀ Δ : ℝ}
    {m : ℕ}
    (hζ₀ : 0 < ζ₀) (hζ₀45 : ζ₀ < 4 / 5)
    (hν0 : 0 < ν) (hνζ : ν ≤ ζ₀) (hK₀ : 5 ≤ K₀)
    (hε : 0 < ε) (hε1 : ε < 1) (hεε₀ : ε < ε₀) (hεc : ε ≤ cstar / 4)
    (hεΔ : ε ≤ Δ / 8)
    (hcstar : 0 < cstar) (hΔ : 0 < Δ) (hD : 2 ≤ D)
    (hDcap : 2 / ζ₀ ≤ (D : ℝ))
    (hgap : ∀ r, 2 ≤ r → r ≤ D → sigma (r - 1) + Δ ≤ sigma r)
    (hnum : ∀ (d e : ℕ), 1 ≤ d → d < e → e ≤ D →
      ∀ ζ : ℝ, ζ₀ ≤ ζ → ζ ≤ 1 - sigma d →
        ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
          (sigma e + ζ) * (1 / (sigma d + ζ) - (1 - ε') * ((e : ℝ) - d)) ≤
            1 - cstar)
    (hCdown : 1 ≤ Cdown)
    (habs : Cdown ^ 2 ≤ (m : ℝ) ^ min (cstar / 10) (Δ / 8))
    (hraw : RawStep' D ζ₀ ε ν Cdown K₀ m)
    (n₀ : ℕ) (hn₀1 : 1 ≤ n₀)
    (hfloor : ((max m 2 : ℕ) : ℝ) ≤ (n₀ : ℝ) ^
      (ν * (ν * (1 - ε)) ^ (⌊1 / min (cstar / 10) (Δ / 8)⌋₊) * (1 - ε))) :
    ∀ (X : ℕ) (s : PrepStage X), 1 ≤ X → ExcessiveStage ζ₀ s →
      n₀ ≤ s.V.card → False := by
  classical
  set cg : ℝ := min (cstar / 10) (Δ / 8) with hcgdef
  have hcg : 0 < cg := lt_min (by positivity) (by positivity)
  have hcgΔ : cg ≤ Δ / 8 := min_le_right _ _
  have hcgstar : cg ≤ cstar / 10 := min_le_left _ _
  set θ : ℝ := ν * (1 - ε) with hθdef
  have hθ0 : 0 < θ := by
    rw [hθdef]; exact mul_pos hν0 (by linarith)
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    have hν1 : ν ≤ 1 := by linarith
    nlinarith
  set B₀ : ℕ := ⌊1 / cg⌋₊ with hB₀def
  set e : ℕ → ℝ := fun b => ν * θ ^ (B₀ - b) with hedef
  have he_pos : ∀ b, 0 < e b := fun b => mul_pos hν0 (pow_pos hθ0 _)
  have he_le_ν : ∀ b, e b ≤ ν := by
    intro b
    rw [hedef]
    calc ν * θ ^ (B₀ - b) ≤ ν * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hθ0.le hθ1) hν0.le
      _ = ν := mul_one ν
  have he_mono : ∀ {b b' : ℕ}, b' ≤ b → e b' ≤ e b := by
    intro b b' hbb
    rw [hedef]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hθ0.le hθ1 (by omega)) hν0.le
  set N : ℝ := (n₀ : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hn₀1
  have hN0 : (0 : ℝ) < N := by linarith
  set E : ℝ := ν * θ ^ B₀ * (1 - ε) with hEdef
  have hEe0 : E = e 0 * (1 - ε) := by rw [hEdef, hedef]; norm_num
  have hE_le : ∀ b, E ≤ e b := by
    intro b
    have h1 : e 0 * (1 - ε) ≤ e 0 * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (he_pos 0).le
    rw [hEe0]
    calc e 0 * (1 - ε) ≤ e 0 := by linarith
      _ ≤ e b := he_mono (Nat.zero_le b)
  have hfloorE : ((max m 2 : ℕ) : ℝ) ≤ N ^ E := by rw [hNdef]; exact hfloor
  -- Budget is uniformly bounded at excessive stages.
  have hbudget_le : ∀ {Y : ℕ} (t : PrepStage Y), ExcessiveStage ζ₀ t →
      excessBudget cg t ≤ B₀ := by
    intro Y t hbad
    have hζpos : 0 < stageExcess t := by
      have := hbad.zeta_lt_stageExcess hζ₀.le
      linarith
    apply Nat.floor_mono
    rw [div_le_div_iff_of_pos_right hcg]
    linarith
  -- The main descent.
  intro X s hX hbad hn
  refine descend_lex
    (α := Σ Y : ℕ, PrepStage Y)
    (fun p => 1 ≤ p.1 ∧ ExcessiveStage ζ₀ p.2 ∧
      N ^ e (excessBudget cg p.2) ≤ descentPotential ζ₀ ν p.2)
    (fun p => excessBudget cg p.2)
    (fun p => (coordinateBox p.2.M).card)
    ?_ ⟨X, s⟩ ⟨hX, hbad, ?_⟩
  · -- The descent step.
    rintro ⟨Y, t⟩ ⟨hY, hbadt, hinv⟩
    -- Cardinality floor at the current stage.
    have hθt : 0 ≤ sigma t.dim + ζ₀ - ν := by
      have := sigma_pos t.dim
      linarith
    have hcardfloor : N ^ E ≤ (t.V.card : ℝ) := by
      calc N ^ E ≤ N ^ e (excessBudget cg t) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (hE_le _)
        _ ≤ descentPotential ζ₀ ν t := hinv
        _ ≤ (t.V.card : ℝ) := descentPotential_le_card ζ₀ ν t hθt
    have hm_le : m ≤ t.V.card := by
      have h1 : ((max m 2 : ℕ) : ℝ) ≤ (t.V.card : ℝ) :=
        le_trans hfloorE hcardfloor
      have h2 : (max m 2 : ℕ) ≤ t.V.card := by exact_mod_cast h1
      omega
    have h2_le : 2 ≤ t.V.card := by
      have h1 : ((max m 2 : ℕ) : ℝ) ≤ (t.V.card : ℝ) :=
        le_trans hfloorE hcardfloor
      have h2 : (max m 2 : ℕ) ≤ t.V.card := by exact_mod_cast h1
      omega
    have htpos : (0 : ℝ) < (t.V.card : ℝ) := by
      have : (0 : ℕ) < t.V.card := by omega
      exact_mod_cast this
    have ht1R : (1 : ℝ) ≤ (t.V.card : ℝ) := by
      have : (1 : ℕ) ≤ t.V.card := by omega
      exact_mod_cast this
    -- Apply the raw step.
    obtain ⟨t', hcase⟩ := hraw Y t hY hbadt hm_le
    -- Common dimension-move processing.
    have hdimmove : ∀ (hcard : (t.V.card : ℝ) ^ (1 - ε) ≤ (t'.V.card : ℝ)),
        (2 : ℕ) ≤ t'.V.card ∧
        (ExcessiveStage ζ₀ t' →
          N ^ (e (excessBudget cg t) * θ) ≤ descentPotential ζ₀ ν t') := by
      intro hcard
      have hb := hbudget_le t hbadt
      have hV'floor : N ^ (e (excessBudget cg t) * (1 - ε)) ≤
          (t'.V.card : ℝ) := by
        have h1 : N ^ e (excessBudget cg t) ≤ (t.V.card : ℝ) :=
          le_trans hinv (descentPotential_le_card ζ₀ ν t hθt)
        calc N ^ (e (excessBudget cg t) * (1 - ε))
            = (N ^ e (excessBudget cg t)) ^ (1 - ε) :=
              Real.rpow_mul hN0.le _ _
          _ ≤ (t.V.card : ℝ) ^ (1 - ε) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) h1 (by linarith)
          _ ≤ (t'.V.card : ℝ) := hcard
      constructor
      · -- `|V'| ≥ 2`.
        have h2 : (2 : ℝ) ≤ N ^ (e (excessBudget cg t) * (1 - ε)) := by
          have hEb : E ≤ e (excessBudget cg t) * (1 - ε) := by
            rw [hEe0]
            exact mul_le_mul_of_nonneg_right (he_mono (Nat.zero_le _))
              (by linarith)
          calc (2 : ℝ) ≤ ((max m 2 : ℕ) : ℝ) := by
                have : (2 : ℕ) ≤ max m 2 := le_max_right _ _
                exact_mod_cast this
            _ ≤ N ^ E := hfloorE
            _ ≤ N ^ (e (excessBudget cg t) * (1 - ε)) :=
                Real.rpow_le_rpow_of_exponent_le hN1 hEb
        have h3 : (2 : ℝ) ≤ (t'.V.card : ℝ) := le_trans h2 hV'floor
        exact_mod_cast h3
      · -- Potential regeneration.
        intro hbad'
        have hregen := rpow_le_descentPotential hζ₀ hν0.le hbad'
        calc N ^ (e (excessBudget cg t) * θ)
            = N ^ (e (excessBudget cg t) * (1 - ε) * ν) := by
              rw [hθdef]; ring_nf
          _ = (N ^ (e (excessBudget cg t) * (1 - ε))) ^ ν :=
              Real.rpow_mul hN0.le _ _
          _ ≤ (t'.V.card : ℝ) ^ ν :=
              Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hV'floor hν0.le
          _ ≤ descentPotential ζ₀ ν t' := hregen
    -- The budget-drop exponent identity.
    have hexp_drop : ∀ b : ℕ, 1 ≤ b → b ≤ B₀ →
        e b * θ = e (b - 1) := by
      intro b hb1 hbB
      rw [hedef]
      have harith : B₀ - (b - 1) = (B₀ - b) + 1 := by omega
      simp only []
      rw [harith, pow_succ]
      ring
    rcases hcase with ⟨hlt, hDle, hcard, hboxle⟩ | ⟨hlt, hcard, hboxle⟩ |
      ⟨heq, η, ρ, hη0, hη1, hρ0, hρ1, hcard, hbox⟩
    · -- UP-MOVE.
      obtain ⟨hV'2, hregen⟩ := hdimmove hcard
      have hcount := up_step_facts hζ₀ hcstar hnum hbadt hε (by linarith)
        hεε₀ hεc hV'2 hlt hDle hcard hboxle
      have hbox2' : 2 ≤ (coordinateBox t'.M).card :=
        le_trans hV'2 (stage_card_le_box t')
      have hB'1 : (1 : ℝ) ≤ ((coordinateBox t'.M).card : ℝ) := by
        have : (1 : ℕ) ≤ (coordinateBox t'.M).card := by omega
        exact_mod_cast this
      have hζlt : ζ₀ < stageExcess t := hbadt.zeta_lt_stageExcess hζ₀.le
      have hbad' : ExcessiveStage ζ₀ t' := by
        unfold ExcessiveStage
        calc ((coordinateBox t'.M).card : ℝ) ^ (sigma t'.dim + ζ₀)
            ≤ ((coordinateBox t'.M).card : ℝ) ^
                (sigma t'.dim + stageExcess t + cstar / 10) :=
              Real.rpow_le_rpow_of_exponent_le hB'1 (by linarith)
          _ < (t'.V.card : ℝ) := hcount
      have hgain : stageExcess t + cg ≤ stageExcess t' := by
        have h1 := lt_stageExcess_of_rpow_lt hbox2' hcount
        have h2 : stageExcess t + cstar / 10 < stageExcess t' := by
          linarith
        linarith
      have hbdrop : excessBudget cg t' < excessBudget cg t :=
        excessBudget_lt_of_gain hcg
          (le_trans (hbad'.stageExcess_le_one hζ₀.le) (by norm_num)) hgain
      have hb1 : 1 ≤ excessBudget cg t := by omega
      have hbB₀ := hbudget_le t hbadt
      refine ⟨⟨Y, t'⟩, ⟨hY, hbad', ?_⟩, Or.inl hbdrop⟩
      calc N ^ e (excessBudget cg t')
          ≤ N ^ e (excessBudget cg t - 1) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (he_mono (by omega))
        _ = N ^ (e (excessBudget cg t) * θ) := by
            rw [hexp_drop _ hb1 hbB₀]
        _ ≤ descentPotential ζ₀ ν t' := hregen hbad'
    · -- DOWN-MOVE.
      obtain ⟨hV'2, hregen⟩ := hdimmove hcard
      have hcount := down_step_facts hζ₀ hD hDcap hΔ hgap hbadt hcg hcgΔ
        hε hεΔ hCdown (by rw [hcgdef] at habs ⊢; exact habs) hm_le hV'2
        hlt hcard hboxle
      have hbox2' : 2 ≤ (coordinateBox t'.M).card :=
        le_trans hV'2 (stage_card_le_box t')
      have hB'1 : (1 : ℝ) ≤ ((coordinateBox t'.M).card : ℝ) := by
        have : (1 : ℕ) ≤ (coordinateBox t'.M).card := by omega
        exact_mod_cast this
      have hζlt : ζ₀ < stageExcess t := hbadt.zeta_lt_stageExcess hζ₀.le
      have hbad' : ExcessiveStage ζ₀ t' := by
        unfold ExcessiveStage
        calc ((coordinateBox t'.M).card : ℝ) ^ (sigma t'.dim + ζ₀)
            ≤ ((coordinateBox t'.M).card : ℝ) ^
                (sigma t'.dim + stageExcess t + cg) :=
              Real.rpow_le_rpow_of_exponent_le hB'1 (by linarith)
          _ < (t'.V.card : ℝ) := hcount
      have hgain : stageExcess t + cg ≤ stageExcess t' := by
        have h1 := lt_stageExcess_of_rpow_lt hbox2' hcount
        linarith
      have hbdrop : excessBudget cg t' < excessBudget cg t :=
        excessBudget_lt_of_gain hcg
          (le_trans (hbad'.stageExcess_le_one hζ₀.le) (by norm_num)) hgain
      have hb1 : 1 ≤ excessBudget cg t := by omega
      have hbB₀ := hbudget_le t hbadt
      refine ⟨⟨Y, t'⟩, ⟨hY, hbad', ?_⟩, Or.inl hbdrop⟩
      calc N ^ e (excessBudget cg t')
          ≤ N ^ e (excessBudget cg t - 1) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (he_mono (by omega))
        _ = N ^ (e (excessBudget cg t) * θ) := by
            rw [hexp_drop _ hb1 hbB₀]
        _ ≤ descentPotential ζ₀ ν t' := hregen hbad'
    · -- SAME-DIMENSIONAL MOVE.
      obtain ⟨hbad', hmono, hboxlt, hΦmono⟩ := sameDim_step_facts hζ₀ hν0
        hνζ hK₀ hbadt heq hη0 hη1 hρ0 hρ1 hcard hbox
      have hble : excessBudget cg t' ≤ excessBudget cg t :=
        excessBudget_le_of_mono hcg hmono
      refine ⟨⟨Y, t'⟩, ⟨hY, hbad', ?_⟩, Or.inr ⟨hble, hboxlt⟩⟩
      calc N ^ e (excessBudget cg t')
          ≤ N ^ e (excessBudget cg t) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (he_mono hble)
        _ ≤ descentPotential ζ₀ ν t := hinv
        _ ≤ descentPotential ζ₀ ν t' := hΦmono
  · -- The initial invariant.
    have hregen := rpow_le_descentPotential hζ₀ hν0.le hbad
    have hcardN : N ≤ (s.V.card : ℝ) := by rw [hNdef]; exact_mod_cast hn
    calc N ^ e (excessBudget cg s)
        ≤ N ^ ν := Real.rpow_le_rpow_of_exponent_le hN1 (he_le_ν _)
      _ ≤ (s.V.card : ℝ) ^ ν :=
          Real.rpow_le_rpow hN0.le hcardN hν0.le
      _ ≤ descentPotential ζ₀ ν s := hregen

end Nondividing
