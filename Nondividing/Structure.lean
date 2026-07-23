import Nondividing.External.CFPStructure
import Nondividing.Preprocessing
import Nondividing.Geometry.ConvexLatticeJohn
import Nondividing.Geometry.CoordProjection

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

/-- Unshifted `(δ,γ)`-irreducibility (manuscript Definition, Phase C).  Relative
to a structural package, `(V, B)` is irreducible if every eligible subset
`D ⊆ V` with `|D| ≥ δ|V|` has full subset-sum dimension `d(D) = ell` and its
progression `P(D)` occupies at least a `γ` fraction of the box. -/
def UnshiftedIrreducible {ell : ℕ} {β : ℝ} (pkg : Package ell β) (δ γ : ℝ)
    (V : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ) : Prop :=
  ∀ (D : Finset (Fin ell → ℤ)), D ⊆ V → δ * (V.card : ℝ) ≤ (D.card : ℝ) →
    ∀ hE : Eligible β pkg.m₀ D M,
      (pkg.out D M hE).e = ell ∧
      γ * ((coordinateBox M).card : ℝ) ≤ ((pkg.out D M hE).P.carrier.card : ℝ)

/-- Irreducibility gives, for the whole eligible set `V` itself (taking `D = V`
when `δ ≤ 1`), full dimension and the box-fraction lower bound. -/
theorem UnshiftedIrreducible.self {ell : ℕ} {β : ℝ} {pkg : Package ell β}
    {δ γ : ℝ} {V : Finset (Fin ell → ℤ)} {M : Fin ell → ℕ}
    (h : UnshiftedIrreducible pkg δ γ V M) (hδ : δ ≤ 1) (hV : 0 ≤ (V.card : ℝ))
    (hE : Eligible β pkg.m₀ V M) :
    (pkg.out V M hE).e = ell ∧
      γ * ((coordinateBox M).card : ℝ) ≤ ((pkg.out V M hE).P.carrier.card : ℝ) :=
  h V (le_refl _) (by nlinarith) hE

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

/-- Progression comparison, `e ≤ r` case, over the fixed package.  The John GAP
`Q_H` housing the core `C₀` is produced by `section_in_gap` (rank `r ≤ ell`), so
this closes the manuscript's second alternative
`|P(C)| ≪ s^{r-e} |Q_H| ≪ |B|` at the level of the raw counting inequality
`t^e |P(C)| ≤ (3^e (2|C₀|+1)^r Cⱼ) |B|`. -/
theorem progression_comparison_le_package {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    {C : Finset (Fin ell → ℤ)} {M : Fin ell → ℕ} (hE : Eligible β pkg.m₀ C M)
    (ht : 1 ≤ pkg.c * External.structureScale C.card) :
    ∃ (r Cj : ℕ),
      (pkg.c * External.structureScale C.card) ^ (pkg.out C M hE).e *
          ((pkg.out C M hE).P.carrier.card : ℝ) ≤
        (3 ^ (pkg.out C M hE).e *
            (2 * (pkg.out C M hE).C₀.card + 1) ^ r * Cj) *
          ((coordinateBox M).card : ℝ) := by
  set o := pkg.out C M hE with ho
  have hC₀box : o.C₀ ⊆ coordinateBox M :=
    (o.C₀_subset.trans o.Chat_subset).trans hE.subset
  obtain ⟨Cj, _hCj, hsec⟩ := section_in_gap ell
  obtain ⟨r, Q, hQprop, hC₀Q, hQcard⟩ := hsec o.C₀ M hC₀box
  exact ⟨r, Cj,
    o.P.progression_comparison_le ht o.inj Q hQprop hC₀Q (le_refl _) o.incl hQcard⟩

/-- **Projective span over the package** (`lem:projective-span`, first
conclusion).  For an irreducible eligible shell set `V` whose fixed progression
`P(V)` occupies at least a `γ` fraction of the box, once the scale product `s·γ`
is large the real span of `V` is all of `ℝ^d`. -/
theorem projective_span_package {d : ℕ} {β : ℝ} (hd : 1 ≤ d) (pkg : Package d β)
    {V : Finset (Fin d → ℤ)} {M : Fin d → ℕ} (hE : Eligible β pkg.m₀ V M)
    {γ : ℝ} (hγ : 0 < γ) (he : (pkg.out V M hE).e = d)
    (hs : 1 ≤ External.structureScale V.card)
    (hcs : 1 ≤ pkg.c * External.structureScale V.card)
    (hcard1 : 1 ≤ (pkg.out V M hE).C₀.card)
    (hPlow : γ * ((coordinateBox M).card : ℝ) ≤
      ((pkg.out V M hE).P.carrier.card : ℝ))
    (hthresh : (6 : ℝ) ^ d < pkg.c ^ d *
      (External.structureScale V.card * γ)) :
    integerRealSpan V = ⊤ := by
  set o := pkg.out V M hE with ho
  have hproper := o.P.proper_of_dilate hcs o.inj
  have hC₀box : o.C₀ ⊆ coordinateBox M :=
    (o.C₀_subset.trans o.Chat_subset).trans hE.subset
  have hC₀V : o.C₀ ⊆ V := o.C₀_subset.trans o.Chat_subset
  have hBpos : 0 < ((coordinateBox M).card : ℝ) := by
    have : 0 < (coordinateBox M).card :=
      Finset.card_pos.mpr ⟨0, zero_mem_coordinateBox M⟩
    exact_mod_cast this
  have hde : 1 ≤ o.e := by rw [he]; exact hd
  have hthresh' : (6 : ℝ) ^ o.e < pkg.c ^ o.e *
      (External.structureScale V.card * γ) := by rw [he]; exact hthresh
  have hrank : o.P.realRank = d :=
    (realRank_eq_of_index hde o.P hproper pkg.c_pos hs hγ hcs o.inj hC₀box hcard1
      o.C₀_card o.incl hBpos hPlow hthresh').trans he
  exact integerRealSpan_eq_top o.P hcs hC₀V o.incl hrank

end Nondividing
