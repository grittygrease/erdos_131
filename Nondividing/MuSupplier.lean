import Nondividing.IrredNumerics

namespace Nondividing

open Nondividing.External

/-!
# The per-stage `μ`-supplier: unconditional discharge of the capped increment

This file discharges `IrreducibleIncrementCapped` (the two-threshold,
excessive-input capped irreducible-stage increment of
`ProjectiveTheorem.lean`) unconditionally, by providing the per-stage
`μ`-supplier demanded by `irreducibleIncrement_of_parameters`
(`IrredNumerics.lean`).

## Design

At a stage `s` with `d := s.dim ≤ Dcap`, `n := s.V.card ≥ C₂·n₁`,
excessive and irreducible, we choose `μ := μf d` where `μf d` is a small
per-dimension constant fixed up front (there are only finitely many
`d ≤ Dcap`, so all thresholds max out over `Finset.range (Dcap+1)`).

* **Absorption smallness** (`exists_mu_small`): with `ν := ζ₀/2` and
  `eps ≤ ζ₀/4` the absorption exponent
  `τ_d·((κ_d+eps) − (σ_d+ζ₀−ν))`, `κ_d := (d−2)/d`, is *negative* —
  `κ_d ≤ σ_d` for every `d` (`kappa_le_sigma`; equality for `d ≥ 3`),
  so `(κ_d+eps) − (σ_d+ζ₀/2) ≤ eps − ζ₀/2 ≤ −ζ₀/4 < 0` — hence
  `μ^{exponent} → ∞` as `μ → 0⁺` and an explicit small `μ` works.
* **Regime**: `δ` is constrained by
  `δ₀ := min_{d ≤ Dcap} min((μf d)^{1+eps}, μf d/100)` (a `Finset.inf'`).
* **Largeness / box / retention**: all remaining clauses are folded into
  the single linear threshold `n ≥ C₂·n₁`, with
  `C₂ := Nthr + ⌈m₀max/δ⌉ + ⌈δ⁻¹^β⌉ + ⌈2/γ⌉ + ⌈R⌉ + 1` where `Nthr`
  bounds `n₀(d,μf d), n₂(d,μf d,δ,γ)` over `d ≤ Dcap`, `m₀max` bounds
  the package thresholds, `δ⁻¹^β` gives `|B| ≤ n^5 ≤ (δn)^β` (using
  `ExcessiveStage.box_lt_rpow` and `β ≥ 6`), `2/γ` gives `1 < γ|B|`,
  and `R` bounds the retention constants `μf d^{−(κ_d+eps)}`,
  `μf d^{−τ_d(κ_d+eps)}` — this is exactly what the *second* threshold
  slot of `IrreducibleIncrementCapped` exists for.

## Quantifier order of `muSupplier_discharge` (DOCUMENTED)

```
∃ δ₀ > 0, ∀ δ γ, 0 < δ → δ ≤ δ₀ → 0 < γ → γ < 1 →
  ∃ C₂ > 0, ∀ n₁, 2 ≤ n₁ → C₂*C₂ ≤ n₁ →
    (C₂*n₁ : ℝ) ≤ (n₁*n₁)^(1−eps) ∧
    ∀ ε, IrreducibleIncrementCapped pkgs Dcap ζ₀ ε δ γ (ζ₀/2) n₁ (C₂*n₁)
```

* `δ₀` depends only on `(pkgs, Dcap, ζ₀, eps)`; `C₂` additionally on
  `(δ, γ)`; the second threshold is the *explicit linear* `n₂ := C₂·n₁`.
* The side condition `(C₂*n₁ : ℝ) ≤ ((n₁:ℝ)*(n₁:ℝ))^(1−eps)` is exactly
  the `hn₂pow` hypothesis of `descentStep_of_primed`
  (`DescentInterface.lean`); it holds as soon as `n₁ ≥ C₂²` because
  `eps < 1/5` (from `eps ≤ ζ₀/4`, `ζ₀ < 4/5`).
* The increment is provided for **every** `ε` (the retention-exponent
  slot of the capped predicate is free in the supplier clauses);
  `muSupplier_discharge_at_eps` specializes `ε := eps`, which is the
  instance `descentStep_of_primed` consumes (it needs `0 < ε < 1/2`,
  satisfied by `eps`).
* `ν := ζ₀/2` satisfies the consumption site's `0 < ν ≤ ζ₀`.
-/

/-- `κ_d ≤ σ_d` for every `d`: the manuscript's key exponent comparison.
Equality holds for `d ≥ 3`; for `d ≤ 2` the left side is `≤ 0 < σ_d`
(with Lean's `x/0 = 0` convention at `d = 0`). -/
theorem kappa_le_sigma (d : ℕ) : ((d : ℝ) - 2) / d ≤ sigma d := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · rw [show sigma 0 = 1 / 5 from by simp [sigma]]
      norm_num
    · rw [sigma_one]; norm_num
    · rw [sigma_two]; norm_num
  · rw [sigma_ge_three hd]

/-- Choice of a per-dimension `μ`: positive, `< 1`, below a given cap
`μcap`, with the two absorption smallness inequalities `C·μ^τ < 1` and
`C^a ≤ μ^t` — the latter for **any** fixed negative exponent `t < 0`,
since then `μ^t → ∞` as `μ → 0⁺`.  Fully explicit:
`μ := min(1/2, μcap/2, (1/(2·max C 1))^{τ⁻¹}, (max (C^a) 1)^{t⁻¹})`. -/
theorem exists_mu_small (C τ μcap a t : ℝ) (hC : 0 < C) (hτ : 0 < τ)
    (hμcap : 0 < μcap) (ht : t < 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ μ < μcap ∧ C * μ ^ τ < 1 ∧ C ^ a ≤ μ ^ t := by
  set M : ℝ := max C 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hxbase : (0 : ℝ) < 1 / (2 * M) :=
    div_pos one_pos (by linarith)
  set x : ℝ := (1 / (2 * M)) ^ τ⁻¹ with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hxbase _
  set A : ℝ := max (C ^ a) 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
  set y : ℝ := A ^ t⁻¹ with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos hA0 _
  refine ⟨min (min (1 / 2) (μcap / 2)) (min x y), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min (by norm_num) (by linarith)) (lt_min hx0 hy0)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by norm_num)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _))
      (by linarith)
  · -- `C·μ^τ < 1` from `μ ≤ x` and `x^τ = 1/(2M)`.
    have hμ0 : 0 < min (min (1 / 2) (μcap / 2)) (min x y) :=
      lt_min (lt_min (by norm_num) (by linarith)) (lt_min hx0 hy0)
    have hμx : min (min (1 / 2) (μcap / 2)) (min x y) ≤ x :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hxτ : x ^ τ = 1 / (2 * M) := by
      rw [hxdef, ← Real.rpow_mul hxbase.le,
        inv_mul_cancel₀ (ne_of_gt hτ), Real.rpow_one]
    have h1 : (min (min (1 / 2) (μcap / 2)) (min x y)) ^ τ ≤ x ^ τ :=
      Real.rpow_le_rpow hμ0.le hμx hτ.le
    have h2 : C * (min (min (1 / 2) (μcap / 2)) (min x y)) ^ τ ≤
        C * (1 / (2 * M)) := by
      rw [← hxτ]
      exact mul_le_mul_of_nonneg_left h1 hC.le
    have h3 : C * (1 / (2 * M)) ≤ M * (1 / (2 * M)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hxbase.le
    have h4 : M * (1 / (2 * M)) = 1 / 2 := by
      rw [mul_one_div, mul_comm 2 M, div_mul_eq_div_div,
        div_self (ne_of_gt hM0)]
    linarith
  · -- `C^a ≤ μ^t` from `μ ≤ y`, `t < 0`, and `y^t = A ≥ C^a`.
    have hμ0 : 0 < min (min (1 / 2) (μcap / 2)) (min x y) :=
      lt_min (lt_min (by norm_num) (by linarith)) (lt_min hx0 hy0)
    have hμy : min (min (1 / 2) (μcap / 2)) (min x y) ≤ y :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hyt : y ^ t = A := by
      rw [hydef, ← Real.rpow_mul hA0.le,
        inv_mul_cancel₀ (ne_of_lt ht), Real.rpow_one]
    calc C ^ a ≤ A := le_max_left _ _
      _ = y ^ t := hyt.symm
      _ ≤ (min (min (1 / 2) (μcap / 2)) (min x y)) ^ t :=
          Real.rpow_le_rpow_of_nonpos hμ0 hμy ht.le

/-- Retention from a linear threshold: `x·μ^{−b} ≤ n` gives `x ≤ μ^b·n`. -/
theorem le_rpow_mul_of_mul_neg_le {μ b x n : ℝ} (hμ : 0 < μ)
    (h : x * μ ^ (-b) ≤ n) : x ≤ μ ^ b * n := by
  have hb : (0 : ℝ) < μ ^ b := Real.rpow_pos_of_pos hμ b
  rw [← div_le_iff₀' hb, div_eq_mul_inv, ← Real.rpow_neg hμ.le]
  exact h

/-- **Unconditional discharge of the capped irreducible increment.**
See the module docstring for the quantifier-order documentation.  The
increment is provided at `ν := ζ₀/2` and threshold pair
`(n₁, n₂ := C₂·n₁)`, together with the `hn₂pow` side condition of
`descentStep_of_primed`, for every retention exponent `ε`. -/
theorem muSupplier_discharge {β : ℝ} (pkgs : ∀ r, Package r β)
    (hβ6 : 6 ≤ β) (Dcap : ℕ) (ζ₀ eps : ℝ) (hζ₀ : 0 < ζ₀)
    (hζ₀45 : ζ₀ < 4 / 5) (heps : 0 < eps) (hepsζ : eps ≤ ζ₀ / 4) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ γ : ℝ, 0 < δ → δ ≤ δ₀ → 0 < γ → γ < 1 →
        ∃ C₂ : ℕ, 0 < C₂ ∧
          ∀ n₁ : ℕ, 2 ≤ n₁ → C₂ * C₂ ≤ n₁ →
            ((C₂ * n₁ : ℕ) : ℝ) ≤
              ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - eps) ∧
            ∀ ε : ℝ, IrreducibleIncrementCapped pkgs Dcap ζ₀ ε δ γ
              (ζ₀ / 2) n₁ (C₂ * n₁) := by
  classical
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have heps5 : eps < 1 / 5 := by linarith
  obtain ⟨tau, C, μ₀, n₀, n₂f, hpos, hmain⟩ :=
    irreducibleIncrement_of_parameters (β := β) pkgs eps heps hβ0 Dcap
  -- The per-dimension `μ`: small enough for the absorption numerics.
  have hmu : ∀ d : ℕ, ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ μ < μ₀ d ∧
      C d * μ ^ tau d < 1 ∧
      C d ^ (sigma d + ζ₀ - ζ₀ / 2) ≤
        μ ^ (tau d * ((((d : ℝ) - 2) / d + eps) -
          (sigma d + ζ₀ - ζ₀ / 2))) := by
    intro d
    have hκσ := kappa_le_sigma d
    have hlt : (((d : ℝ) - 2) / d + eps) - (sigma d + ζ₀ - ζ₀ / 2) < 0 := by
      linarith
    have ht : tau d * ((((d : ℝ) - 2) / d + eps) -
        (sigma d + ζ₀ - ζ₀ / 2)) < 0 :=
      mul_neg_of_pos_of_neg (hpos d).1 hlt
    exact exists_mu_small (C d) (tau d) (μ₀ d) (sigma d + ζ₀ - ζ₀ / 2) _
      (hpos d).2.2.1 (hpos d).1 (hpos d).2.2.2 ht
  choose μf hμf0 hμf1 hμfcap hμfC hμfCa using hmu
  -- The finite dimension range and the `δ`-regime bound.
  set S : Finset ℕ := Finset.range (Dcap + 1) with hSdef
  have hSne : S.Nonempty := ⟨0, by simp [hSdef]⟩
  set δ₀ : ℝ :=
    S.inf' hSne fun d => min (μf d ^ ((1 : ℝ) + eps)) (μf d / 100)
    with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def, Finset.lt_inf'_iff]
    intro d _
    have := hμf0 d
    exact lt_min (Real.rpow_pos_of_pos (hμf0 d) _) (by linarith)
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro δ γ hδ0 hδδ₀ hγ0 hγ1
  -- The per-dimension thresholds, maxed out over `d ≤ Dcap`.
  set Nthr : ℕ :=
    S.sup fun d => max (n₀ d (μf d)) (n₂f d (μf d) δ γ) with hNthrdef
  set m₀max : ℕ := S.sup fun d => (pkgs d).m₀ with hm₀maxdef
  set R : ℝ := S.sup' hSne fun d =>
    max (μf d ^ (-(((d : ℝ) - 2) / d + eps)))
      (μf d ^ (-(tau d * (((d : ℝ) - 2) / d + eps)))) with hRdef
  set C₂ : ℕ := Nthr + ⌈(m₀max : ℝ) / δ⌉₊ + ⌈δ⁻¹ ^ β⌉₊ + ⌈2 / γ⌉₊ +
    ⌈R⌉₊ + 1 with hC₂def
  have hC₂pos : 0 < C₂ := by omega
  refine ⟨C₂, hC₂pos, ?_⟩
  intro n₁ hn₁2 hn₁sq
  have hn₁pos : 0 < n₁ := by omega
  have hn₁R0 : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁pos
  have hC₂R1 : (1 : ℝ) ≤ (C₂ : ℝ) := by exact_mod_cast hC₂pos
  constructor
  · -- The `hn₂pow` side condition: `C₂·n₁ ≤ (n₁·n₁)^{1−eps}` for `n₁ ≥ C₂²`.
    have hsqcast : ((C₂ : ℝ)) * (C₂ : ℝ) ≤ (n₁ : ℝ) := by
      exact_mod_cast hn₁sq
    have hkey : (C₂ : ℝ) ≤ (n₁ : ℝ) ^ ((1 : ℝ) - 2 * eps) := by
      have h2 : (C₂ : ℝ) ≤ ((C₂ : ℝ) * (C₂ : ℝ)) ^ ((1 : ℝ) - 2 * eps) := by
        have hsq : (C₂ : ℝ) * (C₂ : ℝ) = (C₂ : ℝ) ^ (2 : ℝ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          ring
        rw [hsq, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ (C₂ : ℝ))]
        calc (C₂ : ℝ) = (C₂ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (C₂ : ℝ) ^ ((2 : ℝ) * (1 - 2 * eps)) :=
              Real.rpow_le_rpow_of_exponent_le hC₂R1 (by linarith)
      calc (C₂ : ℝ) ≤ ((C₂ : ℝ) * (C₂ : ℝ)) ^ ((1 : ℝ) - 2 * eps) := h2
        _ ≤ (n₁ : ℝ) ^ ((1 : ℝ) - 2 * eps) :=
            Real.rpow_le_rpow (by positivity) hsqcast (by linarith)
    calc ((C₂ * n₁ : ℕ) : ℝ) = (C₂ : ℝ) * (n₁ : ℝ) := by push_cast; ring
      _ ≤ (n₁ : ℝ) ^ ((1 : ℝ) - 2 * eps) * (n₁ : ℝ) :=
          mul_le_mul_of_nonneg_right hkey hn₁R0.le
      _ = (n₁ : ℝ) ^ ((1 : ℝ) - 2 * eps) * (n₁ : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = (n₁ : ℝ) ^ ((1 : ℝ) - 2 * eps + 1) :=
          (Real.rpow_add hn₁R0 _ _).symm
      _ = ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - eps) := by
          rw [show (n₁ : ℝ) * (n₁ : ℝ) = (n₁ : ℝ) ^ (2 : ℝ) from by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
                Real.rpow_natCast]
              ring,
            ← Real.rpow_mul (Nat.cast_nonneg n₁)]
          congr 1
          ring
  · -- The capped increment itself, for every retention exponent `ε`.
    intro ε
    refine hmain ζ₀ ε δ γ (ζ₀ / 2) n₁ (C₂ * n₁) hn₁2
      (Nat.le_mul_of_pos_left n₁ hC₂pos) ?_
    intro X s hX hn hdim hexc _hirr
    have hdS : s.dim ∈ S := by
      rw [hSdef]
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hdim)
    -- Cardinality bookkeeping.
    have hC₂le : C₂ ≤ s.V.card :=
      le_trans (Nat.le_mul_of_pos_right C₂ hn₁pos) hn
    have hC₂leR : (C₂ : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hC₂le
    have hn1R : (1 : ℝ) ≤ (s.V.card : ℝ) := le_trans hC₂R1 hC₂leR
    have hnpos : (0 : ℝ) < (s.V.card : ℝ) := lt_of_lt_of_le one_pos hn1R
    have hnR : ((C₂ * n₁ : ℕ) : ℝ) ≤ (s.V.card : ℝ) := by exact_mod_cast hn
    -- The `δ`-regime at dimension `s.dim`.
    have hδd : δ ≤ min (μf s.dim ^ ((1 : ℝ) + eps)) (μf s.dim / 100) := by
      refine le_trans hδδ₀ ?_
      rw [hδ₀def]
      exact Finset.inf'_le _ hdS
    -- The threshold bounds at dimension `s.dim`.
    have hthr : max (n₀ s.dim (μf s.dim)) (n₂f s.dim (μf s.dim) δ γ) ≤
        Nthr := by
      rw [hNthrdef]
      exact Finset.le_sup
        (f := fun d => max (n₀ d (μf d)) (n₂f d (μf d) δ γ)) hdS
    -- The retention constants at dimension `s.dim`.
    have hRd : max (μf s.dim ^ (-(((s.dim : ℝ) - 2) / s.dim + eps)))
        (μf s.dim ^ (-(tau s.dim * (((s.dim : ℝ) - 2) / s.dim + eps)))) ≤
        R := by
      rw [hRdef]
      exact Finset.le_sup'
        (fun d => max (μf d ^ (-(((d : ℝ) - 2) / d + eps)))
          (μf d ^ (-(tau d * (((d : ℝ) - 2) / d + eps))))) hdS
    have hRC₂ : R ≤ (C₂ : ℝ) := by
      refine le_trans (Nat.le_ceil R) ?_
      exact_mod_cast (by omega : ⌈R⌉₊ ≤ C₂)
    -- Generic retention: `x ≤ R` gives `n₁·x ≤ n`.
    have hret : ∀ x : ℝ, x ≤ R → (n₁ : ℝ) * x ≤ (s.V.card : ℝ) := by
      intro x hx
      calc (n₁ : ℝ) * x ≤ (n₁ : ℝ) * (C₂ : ℝ) :=
            mul_le_mul_of_nonneg_left (le_trans hx hRC₂)
              (Nat.cast_nonneg n₁)
        _ = ((C₂ * n₁ : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (s.V.card : ℝ) := hnR
    refine ⟨μf s.dim, hμf0 s.dim, hμf1 s.dim, hμfcap s.dim, hγ0, hδ0,
      le_trans hδd (min_le_left _ _), le_trans hδd (min_le_right _ _),
      ?_, ?_, ?_, ?_, ?_, hμfC s.dim, hμfCa s.dim, ?_, ?_, ?_⟩
    · -- `n₀(d, μf d) ≤ n`.
      exact le_trans (le_trans (le_max_left _ _) hthr)
        (le_trans (by omega) hC₂le)
    · -- `n₂(d, μf d, δ, γ) ≤ n`.
      exact le_trans (le_trans (le_max_right _ _) hthr)
        (le_trans (by omega) hC₂le)
    · -- `m₀ ≤ δ·n`.
      have h1 : (pkgs s.dim).m₀ ≤ m₀max := by
        rw [hm₀maxdef]
        exact Finset.le_sup (f := fun d => (pkgs d).m₀) hdS
      have h2 : (m₀max : ℝ) / δ ≤ (C₂ : ℝ) := by
        refine le_trans (Nat.le_ceil _) ?_
        exact_mod_cast (by omega : ⌈(m₀max : ℝ) / δ⌉₊ ≤ C₂)
      have h3 : (m₀max : ℝ) ≤ δ * (C₂ : ℝ) := by
        rw [div_le_iff₀ hδ0] at h2
        linarith [h2]
      calc ((pkgs s.dim).m₀ : ℝ) ≤ (m₀max : ℝ) := by exact_mod_cast h1
        _ ≤ δ * (C₂ : ℝ) := h3
        _ ≤ δ * (s.V.card : ℝ) :=
            mul_le_mul_of_nonneg_left hC₂leR hδ0.le
    · -- `|B| ≤ (δ·n)^β`, via `|B| ≤ n^5 ≤ δ^β·n^β`.
      have hB5 : ((coordinateBox s.M).card : ℝ) ≤
          (s.V.card : ℝ) ^ (5 : ℝ) := by
        have h1 := hexc.box_lt_rpow hζ₀
        have hexp : (1 : ℝ) / (1 / 5 + ζ₀) ≤ 5 := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 / 5 + ζ₀)]
          linarith
        calc ((coordinateBox s.M).card : ℝ) ≤
            (s.V.card : ℝ) ^ ((1 : ℝ) / (1 / 5 + ζ₀)) := h1.le
          _ ≤ (s.V.card : ℝ) ^ (5 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hn1R hexp
      have hδinv : δ⁻¹ ^ β ≤ (s.V.card : ℝ) := by
        refine le_trans (Nat.le_ceil _) (le_trans ?_ hC₂leR)
        exact_mod_cast (by omega : ⌈δ⁻¹ ^ β⌉₊ ≤ C₂)
      have hδβpos : (0 : ℝ) < δ ^ β := Real.rpow_pos_of_pos hδ0 β
      have hone : (1 : ℝ) ≤ δ ^ β * (s.V.card : ℝ) ^ (β - 5) := by
        have hnb5 : (s.V.card : ℝ) ≤ (s.V.card : ℝ) ^ (β - 5) := by
          calc (s.V.card : ℝ) = (s.V.card : ℝ) ^ (1 : ℝ) :=
                (Real.rpow_one _).symm
            _ ≤ (s.V.card : ℝ) ^ (β - 5) :=
                Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
        have h2 : (δ ^ β)⁻¹ ≤ (s.V.card : ℝ) ^ (β - 5) := by
          rw [← Real.inv_rpow hδ0.le]
          exact le_trans hδinv hnb5
        calc (1 : ℝ) = δ ^ β * (δ ^ β)⁻¹ :=
              (mul_inv_cancel₀ hδβpos.ne').symm
          _ ≤ δ ^ β * (s.V.card : ℝ) ^ (β - 5) :=
              mul_le_mul_of_nonneg_left h2 hδβpos.le
      calc ((coordinateBox s.M).card : ℝ) ≤ (s.V.card : ℝ) ^ (5 : ℝ) := hB5
        _ = 1 * (s.V.card : ℝ) ^ (5 : ℝ) := (one_mul _).symm
        _ ≤ δ ^ β * (s.V.card : ℝ) ^ (β - 5) * (s.V.card : ℝ) ^ (5 : ℝ) :=
            mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hnpos.le _)
        _ = δ ^ β * (s.V.card : ℝ) ^ β := by
            rw [mul_assoc, ← Real.rpow_add hnpos,
              show β - 5 + 5 = β from by ring]
        _ = (δ * (s.V.card : ℝ)) ^ β :=
            (Real.mul_rpow hδ0.le hnpos.le).symm
    · -- `1 < γ·|B|`.
      have hBn : (s.V.card : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
        exact_mod_cast stage_card_le_box s
      have h2γ : 2 / γ ≤ (C₂ : ℝ) := by
        refine le_trans (Nat.le_ceil _) ?_
        exact_mod_cast (by omega : ⌈2 / γ⌉₊ ≤ C₂)
      have hchain : 2 / γ ≤ ((coordinateBox s.M).card : ℝ) :=
        le_trans h2γ (le_trans hC₂leR hBn)
      have h2 : γ * (2 / γ) ≤ γ * ((coordinateBox s.M).card : ℝ) :=
        mul_le_mul_of_nonneg_left hchain hγ0.le
      have h3 : γ * (2 / γ) = 2 := by
        rw [mul_comm]
        exact div_mul_cancel₀ 2 (ne_of_gt hγ0)
      linarith
    · -- Exponent ordering `κ_d + eps ≤ σ_d + ζ₀ − ζ₀/2`.
      have := kappa_le_sigma s.dim
      linarith
    · -- Retention endpoint `n₁ ≤ μ^{κ_d+eps}·n`.
      refine le_rpow_mul_of_mul_neg_le (hμf0 s.dim) ?_
      exact hret _ (le_trans (le_max_left _ _) hRd)
    · -- Retention endpoint `n₁ ≤ μ^{τ_d(κ_d+eps)}·n`.
      refine le_rpow_mul_of_mul_neg_le (hμf0 s.dim) ?_
      exact hret _ (le_trans (le_max_right _ _) hRd)

/-- Specialization of `muSupplier_discharge` at the retention exponent
`ε := eps` — the exact instance consumed by `descentStep_of_primed`
(whose hypotheses `hn₂pow` and `hinc` share the same `ε`; note
`0 < eps < 1/5 < 1/2` there). -/
theorem muSupplier_discharge_at_eps {β : ℝ} (pkgs : ∀ r, Package r β)
    (hβ6 : 6 ≤ β) (Dcap : ℕ) (ζ₀ eps : ℝ) (hζ₀ : 0 < ζ₀)
    (hζ₀45 : ζ₀ < 4 / 5) (heps : 0 < eps) (hepsζ : eps ≤ ζ₀ / 4) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ γ : ℝ, 0 < δ → δ ≤ δ₀ → 0 < γ → γ < 1 →
        ∃ C₂ : ℕ, 0 < C₂ ∧
          ∀ n₁ : ℕ, 2 ≤ n₁ → C₂ * C₂ ≤ n₁ →
            ((C₂ * n₁ : ℕ) : ℝ) ≤
              ((n₁ : ℝ) * (n₁ : ℝ)) ^ ((1 : ℝ) - eps) ∧
            IrreducibleIncrementCapped pkgs Dcap ζ₀ eps δ γ (ζ₀ / 2) n₁
              (C₂ * n₁) := by
  obtain ⟨δ₀, hδ₀, h⟩ :=
    muSupplier_discharge pkgs hβ6 Dcap ζ₀ eps hζ₀ hζ₀45 heps hepsζ
  refine ⟨δ₀, hδ₀, fun δ γ h1 h2 h3 h4 => ?_⟩
  obtain ⟨C₂, hC₂, hall⟩ := h δ γ h1 h2 h3 h4
  exact ⟨C₂, hC₂, fun n₁ ha hb =>
    ⟨(hall n₁ ha hb).1, (hall n₁ ha hb).2 eps⟩⟩

end Nondividing
