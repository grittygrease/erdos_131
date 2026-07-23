import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

namespace Nondividing

open scoped BigOperators

noncomputable def subsetSums {α : Type*} [DecidableEq α] [AddCommMonoid α]
    (A : Finset α) : Finset α := by
  classical
  exact A.powerset.image fun S => ∑ a ∈ S, a

@[simp] theorem mem_subsetSums {α : Type*} [DecidableEq α] [AddCommMonoid α]
    {A : Finset α} {x : α} :
    x ∈ subsetSums A ↔ ∃ S : Finset α, S ⊆ A ∧ ∑ a ∈ S, a = x := by
  classical
  simp [subsetSums]

/-- Subset sums over disjoint index sets add: the final assembly step of
`lem:one-sided-filling`, `y = z̃ + ((z−z̃)+t)` with the producing subsets in
`C̄` and `C₀` respectively. -/
theorem add_mem_subsetSums_union {α : Type*} [DecidableEq α] [AddCommMonoid α]
    {A B : Finset α} {x y : α} (hd : Disjoint A B)
    (hx : x ∈ subsetSums A) (hy : y ∈ subsetSums B) :
    x + y ∈ subsetSums (A ∪ B) := by
  obtain ⟨S, hSA, hSx⟩ := mem_subsetSums.mp hx
  obtain ⟨T, hTB, hTy⟩ := mem_subsetSums.mp hy
  refine mem_subsetSums.mpr ⟨S ∪ T, Finset.union_subset_union hSA hTB, ?_⟩
  rw [Finset.sum_union (hd.mono hSA hTB), hSx, hTy]

theorem subsetSums_mono {α : Type*} [DecidableEq α] [AddCommMonoid α]
    {A B : Finset α} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B := by
  intro x hx
  obtain ⟨S, hSA, hSx⟩ := mem_subsetSums.mp hx
  exact mem_subsetSums.mpr ⟨S, hSA.trans h, hSx⟩

/-- No member of `A` divides a nonempty sum of other, distinct members of `A`. -/
def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S.Nonempty → S ⊆ A.erase a → ¬a ∣ ∑ s ∈ S, s

/-- No member of `A` is the average of a nonempty set of other members. -/
def NonAveraging (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℤ, S.Nonempty → S ⊆ A.erase a →
    ∑ s ∈ S, s ≠ S.card * a

/-- Non-dividing subsets of `[1,N]`. -/
noncomputable def candidates (N : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 N).powerset.filter NonDividing

/-- The largest cardinality of a non-dividing subset of `[1,N]`. -/
noncomputable def F (N : ℕ) : ℕ :=
  (candidates N).sup Finset.card

theorem nonDividing_empty : NonDividing ∅ := by
  simp [NonDividing]

theorem nonDividing_singleton (a : ℕ) : NonDividing {a} := by
  intro b hb S hS hsub
  simp only [Finset.mem_singleton] at hb
  subst b
  have hS0 : S = ∅ := Finset.subset_empty.mp (by simpa using hsub)
  exact (hS.ne_empty hS0).elim

theorem NonDividing.mono {A B : Finset ℕ} (hA : NonDividing A) (hBA : B ⊆ A) :
    NonDividing B := by
  intro a ha S hS hSB
  apply hA a (hBA ha) S hS
  intro x hx
  have hx' := Finset.mem_erase.mp (hSB hx)
  exact Finset.mem_erase.mpr ⟨hx'.1, hBA hx'.2⟩

theorem NonAveraging.mono {A B : Finset ℤ} (hA : NonAveraging A) (hBA : B ⊆ A) :
    NonAveraging B := by
  intro a ha S hS hSB
  apply hA a (hBA ha) S hS
  intro x hx
  have hx' := Finset.mem_erase.mp (hSB hx)
  exact Finset.mem_erase.mpr ⟨hx'.1, hBA hx'.2⟩

@[simp] theorem mem_candidates {A : Finset ℕ} {N : ℕ} :
    A ∈ candidates N ↔ A ⊆ Finset.Icc 1 N ∧ NonDividing A := by
  classical
  simp [candidates]

theorem candidates_nonempty (N : ℕ) : (candidates N).Nonempty :=
  ⟨∅, by simp [mem_candidates, nonDividing_empty]⟩

private theorem exists_card_eq_sup {α : Type*} [DecidableEq α]
    (s : Finset (Finset α)) (hs : s.Nonempty) :
    ∃ A ∈ s, A.card = s.sup Finset.card := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hsn : s.Nonempty
      · obtain ⟨b, hb, hcard⟩ := ih hsn
        by_cases h : s.sup Finset.card ≤ a.card
        · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
          simp [Finset.sup_insert, max_eq_left h]
        · have hle : a.card ≤ s.sup Finset.card :=
            Nat.le_of_lt (lt_of_not_ge h)
          refine ⟨b, Finset.mem_insert_of_mem hb, ?_⟩
          simpa [Finset.sup_insert, max_eq_right hle] using hcard
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        refine ⟨a, Finset.mem_singleton_self a, ?_⟩
        simp

theorem card_le_F {A : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hnd : NonDividing A) :
    A.card ≤ F N :=
  Finset.le_sup (s := candidates N) (f := Finset.card)
    (mem_candidates.mpr ⟨hA, hnd⟩)

theorem exists_extremal (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ NonDividing A ∧ A.card = F N := by
  obtain ⟨A, hA, hcard⟩ := exists_card_eq_sup (candidates N) (candidates_nonempty N)
  exact ⟨A, (mem_candidates.mp hA).1, (mem_candidates.mp hA).2, hcard⟩

theorem F_mono : Monotone F := by
  intro N M hNM
  obtain ⟨A, hAI, hnd, hcard⟩ := exists_extremal N
  rw [← hcard]
  apply card_le_F (N := M) _ hnd
  exact hAI.trans (Finset.Icc_subset_Icc le_rfl hNM)

theorem one_le_F {N : ℕ} (hN : 1 ≤ N) : 1 ≤ F N := by
  simpa using card_le_F (A := {1}) (N := N) (by simp [hN])
    (nonDividing_singleton 1)

end Nondividing
