import Nondividing.Box
import Nondividing.Preprocessing

open scoped BigOperators

namespace Nondividing

/-!
# Lattice sections and index bounds (Phase D)

This file develops the combinatorial core of `lem:lattice-section-box`: a finite
set of integer points inside a symmetric coordinate box whose projection to a
coordinate subset `I` is injective has cardinality at most the size of the box
`I`-face `∏_{i∈I}(2Mᵢ+1)`.  The manuscript uses this with `I` an `r`-subset on
which a fixed `r`-dimensional subspace projects injectively.
-/

/-- Coordinate projection of an integer point onto the coordinate subset `I`
(zeroing the complementary coordinates). -/
def coordProj {d : ℕ} (I : Finset (Fin d)) (z : Fin d → ℤ) : Fin d → ℤ :=
  fun i => if i ∈ I then z i else 0

theorem coordProj_mem_coordinateBox {d : ℕ} {M : Fin d → ℕ} {I : Finset (Fin d)}
    {z : Fin d → ℤ} (hz : z ∈ coordinateBox M) :
    coordProj I z ∈ coordinateBox (fun i => if i ∈ I then M i else 0) := by
  rw [mem_coordinateBox] at hz ⊢
  intro i
  by_cases hi : i ∈ I
  · simp only [coordProj, hi, if_true]
    exact hz i
  · simp only [coordProj, hi, if_false]
    simp

/-- Cardinality of the projected box `∏_{i∈I}(2Mᵢ+1)`, the size of the `I`-face
of a symmetric coordinate box. -/
theorem card_coordinateBox_proj {d : ℕ} (M : Fin d → ℕ) (I : Finset (Fin d)) :
    (coordinateBox (fun i => if i ∈ I then M i else 0)).card =
      ∏ i ∈ I, (2 * M i + 1) := by
  rw [card_coordinateBox]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ I)]
  have h1 : ∏ i ∈ Finset.univ.filter (· ∈ I),
      (2 * (if i ∈ I then M i else 0) + 1) = ∏ i ∈ I, (2 * M i + 1) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.prod_congr rfl fun i hi => by simp [hi]
  have h2 : ∏ i ∈ Finset.univ.filter (¬ · ∈ I),
      (2 * (if i ∈ I then M i else 0) + 1) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_filter] at hi
    simp [hi.2]
  rw [h1, h2, mul_one]

/-- Combinatorial core of `lem:lattice-section-box`.  If the coordinate
projection to `I` is injective on a set `A` inside a symmetric coordinate box,
then `|A| ≤ ∏_{i∈I}(2Mᵢ+1)`. -/
theorem card_le_prod_of_injOn_coordProj {d : ℕ} {M : Fin d → ℕ}
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ coordinateBox M) (I : Finset (Fin d))
    (hinj : Set.InjOn (coordProj I) (A : Set (Fin d → ℤ))) :
    A.card ≤ ∏ i ∈ I, (2 * M i + 1) := by
  classical
  calc A.card = (A.image (coordProj I)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (coordinateBox (fun i => if i ∈ I then M i else 0)).card := by
          apply Finset.card_le_card
          intro w hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          exact coordProj_mem_coordinateBox (hA hz)
    _ = ∏ i ∈ I, (2 * M i + 1) := card_coordinateBox_proj M I

/-- The `I`-face size is at most the whole box size, since the omitted factors
are at least one. -/
theorem prod_proj_le_card_coordinateBox {d : ℕ} (M : Fin d → ℕ)
    (I : Finset (Fin d)) :
    ∏ i ∈ I, (2 * M i + 1) ≤ (coordinateBox M).card := by
  rw [card_coordinateBox]
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ I)
  intro i _ _
  exact Nat.le_add_left 1 (2 * M i)

end Nondividing
