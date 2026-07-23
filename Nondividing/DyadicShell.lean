import Nondividing.Basic
import Nondividing.Shell
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace Nondividing

/-!
# Dyadic shell pigeonhole (Phase H)

The upper-bound proof partitions `[1,N]` into the `1 + ⌊log₂ N⌋` dyadic shells
`[2^j, 2^{j+1})` and pigeonholes one shell that retains a `1/(1+log₂ N)`
fraction of a non-dividing set.  Here we prove the elementary pigeonhole in the
form `|A| ≤ (1 + log₂ N) · |A ∩ [2^j, 2^{j+1})|`, and identify the dyadic fiber
with the interval intersection.
-/

/-- For `1 ≤ a`, having dyadic level `j` is exactly lying in `[2^j, 2^{j+1})`. -/
theorem log_eq_iff_mem_Ico {a j : ℕ} (ha : 1 ≤ a) :
    Nat.log 2 a = j ↔ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
  rw [Finset.mem_Ico]
  constructor
  · rintro rfl
    exact ⟨Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp ha),
      Nat.lt_pow_succ_log_self (by decide) a⟩
  · rintro ⟨h1, h2⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2

/-- Dyadic-shell pigeonhole.  A finite subset `A ⊆ [1,N]` has a dyadic shell
`[2^j, 2^{j+1})` containing at least a `1/(1+⌊log₂ N⌋)` fraction of `A`. -/
theorem exists_dyadic_shell {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    ∃ j : ℕ, A.card ≤
      (Nat.log 2 N + 1) *
        (A.filter (fun a => a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)))).card := by
  classical
  set K := Nat.log 2 N with hK
  -- The dyadic level maps `A` into `range (K+1)`.
  have hmaps : ∀ a ∈ A, Nat.log 2 a ∈ Finset.range (K + 1) := by
    intro a ha
    have haN : a ≤ N := (Finset.mem_Icc.mp (hA ha)).2
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right haN)
  -- Fiberwise decomposition of `|A|`.
  have hsum : A.card =
      ∑ j ∈ Finset.range (K + 1), (A.filter (fun a => Nat.log 2 a = j)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  -- Fibers coincide with dyadic shells (every `a ∈ A` satisfies `1 ≤ a`).
  have hfiber : ∀ j, A.filter (fun a => Nat.log 2 a = j) =
      A.filter (fun a => a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1))) := by
    intro j
    apply Finset.filter_congr
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hA ha)).1
    simp only [log_eq_iff_mem_Ico ha1]
  -- Pigeonhole: pick the largest shell.
  rcases Finset.range (K + 1) |>.exists_max_image
      (fun j => (A.filter (fun a => Nat.log 2 a = j)).card)
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩ with ⟨j₀, _hj₀, hmax⟩
  refine ⟨j₀, ?_⟩
  rw [← hfiber]
  calc A.card = ∑ j ∈ Finset.range (K + 1),
          (A.filter (fun a => Nat.log 2 a = j)).card := hsum
    _ ≤ (Finset.range (K + 1)).card •
          (A.filter (fun a => Nat.log 2 a = j₀)).card :=
          Finset.sum_le_card_nsmul _ _ _ hmax
    _ = (K + 1) * (A.filter (fun a => Nat.log 2 a = j₀)).card := by
          rw [Finset.card_range, smul_eq_mul]

/-- Bridge to the shell setting: a non-dividing set all of whose elements lie in
`[X, 2X]` is `ShellNonDividing` for the identity functional `a ↦ (a : ℤ)` with
shell parameter `X`.  This is the `d = 1`, `λ(t) = t` input to the projective
theorem. -/
theorem shellNonDividing_of_nonDividing {A : Finset ℕ} (hA : NonDividing A)
    (X : ℕ) (hshell : ∀ a ∈ A, X ≤ a ∧ a ≤ 2 * X) :
    ShellNonDividing (fun a : ℕ => (a : ℤ)) X A := by
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨h1, h2⟩ := hshell a ha
    refine ⟨?_, ?_⟩
    · show (X : ℤ) ≤ (a : ℤ); exact_mod_cast h1
    · show (a : ℤ) ≤ 2 * (X : ℤ); push_cast; exact_mod_cast h2
  · intro a ha S hS hSA hdvd
    -- transport the divisibility back to `ℕ`
    have hcast : ∑ v ∈ S, ((v : ℕ) : ℤ) = ((∑ v ∈ S, v : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
    rw [hcast, Int.natCast_dvd_natCast] at hdvd
    exact hA a ha S hS hSA hdvd

/-- Shell reduction for the upper bound.  For every `N` there is a dyadic shell
`[2^j, 2^{j+1})` and a `ShellNonDividing` set `W` inside it (for the identity
functional, shell parameter `2^j`) retaining a `1/(1+⌊log₂ N⌋)` fraction of
`F N`:  `F N ≤ (1 + ⌊log₂ N⌋) · |W|`.  This is the pigeonhole step feeding the
projective theorem at `d = 1`. -/
theorem exists_shell_reduction (N : ℕ) :
    ∃ (j : ℕ) (W : Finset ℕ),
      (∀ a ∈ W, a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      ShellNonDividing (fun a : ℕ => (a : ℤ)) (2 ^ j) W ∧
      F N ≤ (Nat.log 2 N + 1) * W.card := by
  classical
  obtain ⟨A, hAIcc, hnd, hcard⟩ := exists_extremal N
  obtain ⟨j, hj⟩ := exists_dyadic_shell A hAIcc
  refine ⟨j, A.filter (fun a => a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1))), ?_, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · refine shellNonDividing_of_nonDividing (hnd.mono (Finset.filter_subset _ _)) (2 ^ j) ?_
    intro a ha
    have hmem := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).2)
    refine ⟨hmem.1, ?_⟩
    have : a < 2 ^ (j + 1) := hmem.2
    rw [pow_succ] at this
    omega
  · rw [← hcard]; exact hj

/-- The `d = 1` embedding `ℕ ↪ (Fin 1 → ℤ)`, `a ↦ (fun _ => a)`. -/
def dOneEmbedding : ℕ ↪ (Fin 1 → ℤ) where
  toFun a := fun _ => (a : ℤ)
  inj' := by
    intro a b h
    have h0 : (a : ℤ) = (b : ℤ) := congrFun h 0
    exact_mod_cast h0

/-- The `d = 1` shell functional `λ(v) = v 0`. -/
def dOneFunctional : (Fin 1 → ℤ) →+ ℤ where
  toFun v := v 0
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Transport a shell-non-dividing set of naturals to the `d = 1` projective
setting `(Fin 1 → ℤ, λ(v) = v 0)`, the exact input shape of the projective
theorem for the upper bound. -/
theorem shellNonDividing_dOne {W : Finset ℕ} {X : ℕ}
    (hW : ShellNonDividing (fun a : ℕ => (a : ℤ)) X W) :
    ShellNonDividing (fun v : Fin 1 → ℤ => dOneFunctional v) X
      (W.map dOneEmbedding) :=
  hW.map dOneEmbedding (fun _ => rfl)

end Nondividing
