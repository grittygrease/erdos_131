import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int

open scoped BigOperators

namespace Nondividing

def coordinateBox {d : ℕ} (M : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (-(M i : ℤ)) (M i : ℤ)

@[simp] theorem mem_coordinateBox {d : ℕ} {M : Fin d → ℕ} {x : Fin d → ℤ} :
    x ∈ coordinateBox M ↔ ∀ i, -(M i : ℤ) ≤ x i ∧ x i ≤ M i := by
  simp [coordinateBox, Fintype.mem_piFinset]

theorem zero_mem_coordinateBox {d : ℕ} (M : Fin d → ℕ) :
    (0 : Fin d → ℤ) ∈ coordinateBox M := by
  simp

theorem neg_mem_coordinateBox {d : ℕ} {M : Fin d → ℕ} {x : Fin d → ℤ}
    (hx : x ∈ coordinateBox M) : -x ∈ coordinateBox M := by
  rw [mem_coordinateBox] at hx ⊢
  intro i
  change -(M i : ℤ) ≤ -x i ∧ -x i ≤ M i
  exact ⟨(neg_le_neg_iff.mpr (hx i).2),
    (neg_le_neg_iff.mp (by simpa using (hx i).1))⟩

@[simp] theorem card_coordinateBox {d : ℕ} (M : Fin d → ℕ) :
    (coordinateBox M).card = ∏ i : Fin d, (2 * M i + 1) := by
  classical
  rw [coordinateBox, Fintype.piFinset, Finset.card_map]
  change (Multiset.pi Finset.univ.val
    (fun i : Fin d => (Finset.Icc (-(M i : ℤ)) (M i : ℤ)).val)).card =
      ∏ i : Fin d, (2 * M i + 1)
  rw [Multiset.card_pi]
  change (Multiset.map (fun i : Fin d =>
      (Finset.Icc (-(M i : ℤ)) (M i : ℤ)).card) Finset.univ.val).prod =
    ∏ i : Fin d, (2 * M i + 1)
  have hinterval (i : Fin d) :
      (Finset.Icc (-(M i : ℤ)) (M i : ℤ)).card = 2 * M i + 1 := by
    rw [Int.card_Icc]
    omega
  simp_rw [hinterval]
  rfl

end Nondividing
