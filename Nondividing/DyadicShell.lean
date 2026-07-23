import Nondividing.Basic
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

end Nondividing
