import Nondividing.External.CFPStructure
import Nondividing.Preprocessing

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# The fixed structural package (Phase C)

The manuscript fixes, once and for all, a *structural package* assigning to every
eligible finite set `C` its CFP data `P(C), d(C), s(C), C₀, q`.  This turns the
existential external interface E1 (`cfp_structure`) into fixed choice data, so
that downstream lemmas (`progression_comparison`, `index_bound`,
`slab_exclusion`, `projective_span`, …) may all refer to *the* progression
`P(C)`.  We realize the package via `Classical.choice`.
-/

/-- Eligibility of `(C, M)` for a structural package: enough points, containment
in the symmetric coordinate box `M`, and a polynomial box bound. -/
structure Eligible {ell : ℕ} (β : ℝ) (m₀ : ℕ)
    (C : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ) : Prop where
  card_ge : m₀ ≤ C.card
  subset : C ⊆ coordinateBox M
  box_le : ((coordinateBox M).card : ℝ) ≤ Real.rpow (C.card : ℝ) β

/-- The per-set structural output of E1: the large subset `Chat`, the homogeneous
GAP `P` of displayed dimension `e ≤ D`, the core `C₀`, and the translate `q`,
together with all of E1's guaranteed properties. -/
structure StructOut {ell : ℕ} (c : ℝ) (D : ℕ) (C : Finset (Fin ell → ℤ)) where
  Chat : Finset (Fin ell → ℤ)
  e : ℕ
  P : GAP ell e
  C₀ : Finset (Fin ell → ℤ)
  q : Fin ell → ℤ
  Chat_subset : Chat ⊆ C
  Chat_card : ((C \ Chat).card : ℝ) ≤ c⁻¹ * C.card / Real.log C.card
  e_le : e ≤ D
  cover : Chat ∪ {0} ⊆ P.carrier
  C₀_subset : C₀ ⊆ Chat
  C₀_card : (C₀.card : ℝ) ≤ structureScale C.card
  q_mem : q ∈ P.dilatedCarrier (structureScale C.card)
  incl : ∀ z ∈ P.dilatedCarrier (c * structureScale C.card),
    q + z ∈ subsetSums C₀
  inj : Set.InjOn P.evalHom
    (P.dilatedCoeffBox (c * structureScale C.card) : Set (Fin e → ℤ))

/-- A structural package for ambient dimension `ell` and polynomial-box exponent
`β`: fixed constants `c, D, m₀` and a fixed choice `out` of E1 data for every
eligible input. -/
structure Package (ell : ℕ) (β : ℝ) where
  c : ℝ
  c_pos : 0 < c
  D : ℕ
  m₀ : ℕ
  out : ∀ (C : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ),
    Eligible β m₀ C M → StructOut c D C

/-- A structural package exists: repackage the E1 existential as choice data. -/
theorem nonempty_package (ell : ℕ) (β : ℝ) (hβ : 1 < β) :
    Nonempty (Package ell β) := by
  classical
  obtain ⟨c, hc, D, m₀, hspec⟩ := cfp_structure ell β hβ
  have helper : ∀ (C : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ),
      Eligible β m₀ C M → Nonempty (StructOut c D C) := by
    intro C M hE
    obtain ⟨Chat, hChatsub, hChatcard, e, hele, P, hcover, C₀, hC₀sub,
      hC₀card, q, hqmem, hincl, hinj⟩ :=
      hspec C M hE.card_ge hE.subset hE.box_le
    exact ⟨⟨Chat, e, P, C₀, q, hChatsub, hChatcard, hele, hcover, hC₀sub,
      hC₀card, hqmem, hincl, hinj⟩⟩
  exact ⟨⟨c, hc, D, m₀, fun C M hE => (helper C M hE).some⟩⟩

/-- The fixed structural package for `(ell, β)`. -/
noncomputable def package (ell : ℕ) (β : ℝ) (hβ : 1 < β) : Package ell β :=
  (nonempty_package ell β hβ).some

/-- Progression comparison referencing the *fixed* progression `P(C)` of a
structural package: once `c·s(C) ≥ 1`, the counting chain of
`lem:progression-comparison` bounds `P(C)` in terms of the coordinate box.  Base
properness of `P(C)` is derived internally (route §7.4). -/
theorem progression_comparison_package {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    {C : Finset (Fin ell → ℤ)} {M : Fin ell → ℕ} (hE : Eligible β pkg.m₀ C M)
    (ht : 1 ≤ pkg.c * External.structureScale C.card) :
    (pkg.c * External.structureScale C.card) ^ (pkg.out C M hE).e *
        ((pkg.out C M hE).P.carrier.card : ℝ) ≤
      (3 ^ (pkg.out C M hE).e * (max 1 (pkg.out C M hE).C₀.card) ^ ell) *
        ((coordinateBox M).card : ℝ) := by
  set o := pkg.out C M hE with ho
  have hC₀box : o.C₀ ⊆ coordinateBox M :=
    (o.C₀_subset.trans o.Chat_subset).trans hE.subset
  exact o.P.progression_comparison_gt ht o.inj hC₀box (le_max_left _ _)
    (le_max_right _ _) o.incl

end Nondividing
