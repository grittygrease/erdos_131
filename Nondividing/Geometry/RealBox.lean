import Nondividing.Box
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Nondividing

def realCoordinateBox {d : ℕ} (M : Fin d → ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Icc (-(M i : ℝ)) (M i : ℝ)

@[simp] theorem mem_realCoordinateBox {d : ℕ} {M : Fin d → ℕ}
    {x : Fin d → ℝ} :
    x ∈ realCoordinateBox M ↔
      ∀ i, -(M i : ℝ) ≤ x i ∧ x i ≤ M i := by
  simp only [realCoordinateBox, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc]

theorem realCoordinateBox_isCompact {d : ℕ} (M : Fin d → ℕ) :
    IsCompact (realCoordinateBox M) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem realCoordinateBox_convex {d : ℕ} (M : Fin d → ℕ) :
    Convex ℝ (realCoordinateBox M) :=
  convex_pi fun _ _ => convex_Icc _ _

theorem realCoordinateBox_symmetric {d : ℕ} (M : Fin d → ℕ)
    (x : Fin d → ℝ) :
    x ∈ realCoordinateBox M ↔ -x ∈ realCoordinateBox M := by
  simp only [mem_realCoordinateBox, Pi.neg_apply]
  have hneg : ∀ y : Fin d → ℝ,
      (∀ i, -(M i : ℝ) ≤ y i ∧ y i ≤ M i) →
      ∀ i, -(M i : ℝ) ≤ -y i ∧ -y i ≤ M i := by
    intro y hy i
    exact ⟨neg_le_neg (hy i).2, by simpa using neg_le_neg (hy i).1⟩
  exact ⟨hneg x, fun hx => by simpa using hneg (-x) hx⟩

theorem realPoint_mem_realCoordinateBox_iff {d : ℕ} (M : Fin d → ℕ)
    (z : Fin d → ℤ) :
    (fun i => (z i : ℝ)) ∈ realCoordinateBox M ↔
      z ∈ coordinateBox M := by
  rw [mem_realCoordinateBox, mem_coordinateBox]
  norm_cast

end Nondividing
