import Nondividing.Structure
import Nondividing.CapLifting

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# Unshifted preprocessing: failure dichotomy and the single moves (Phase C/G)

Building blocks for `lem:unshifted-preprocessing` (Manuscript.tex 449–745).
The manuscript iteration alternates two "moves" whenever unshifted
`(δ,γ)`-irreducibility *fails* for a stage `(V, B)`:

* a **shrink move** (`small_progression_move`): a witness `D ⊆ V` with
  `|D| ≥ δ|V|` whose fixed progression `P(D)` is small, `|P(D)| < γ|B|`;
  passing through the coefficient identification `φ_{P(D)}` lands the deleted
  set `D̂` in a coordinate box of cardinality `|P(D)| < γ|B|`;
* a **dimension move** (`dimension_move`, `dimension_move_up`): a witness
  whose displayed structural dimension `e = d(D)` differs from the ambient
  dimension; the same identification lands `D̂` in a box of size `≤ C·|B|`
  (all `e`), with the sharper decay `≤ C·s^{ℓ-e}|B|` available for up-moves.

Both moves preserve shell non-dividing exactly (`lem:functional-transform`,
already formalized as `GAP.shell_transport`) and delete at most
`c⁻¹|D|/log|D|` points (the E1 deletion estimate).

This file only *adds* lemmas; it does not modify any existing development.
-/

/-! ## Deliverable 1: the failure dichotomy -/

/-- **Failure dichotomy** for unshifted irreducibility.  Either `(V, M)` is
unshiftedly `(δ,γ)`-irreducible relative to the package, or there is an
eligible witness `D ⊆ V` with `|D| ≥ δ|V|` exhibiting a *dimension defect*
(`d(D) ≠ ℓ`) or a *small progression* (`|P(D)| < γ|box M|`). -/
theorem irreducible_or_witness {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    (δ γ : ℝ) (V : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ) :
    UnshiftedIrreducible pkg δ γ V M ∨
      ∃ D : Finset (Fin ell → ℤ), D ⊆ V ∧ δ * (V.card : ℝ) ≤ (D.card : ℝ) ∧
        ∃ hE : Eligible β pkg.m₀ D M,
          (pkg.out D M hE).e ≠ ell ∨
            ((pkg.out D M hE).P.carrier.card : ℝ) <
              γ * ((coordinateBox M).card : ℝ) := by
  classical
  by_cases h : UnshiftedIrreducible pkg δ γ V M
  · exact Or.inl h
  · right
    unfold UnshiftedIrreducible at h
    push Not at h
    obtain ⟨D, hDV, hcard, hE, hfail⟩ := h
    refine ⟨D, hDV, hcard, hE, ?_⟩
    by_cases he : (pkg.out D M hE).e = ell
    · exact Or.inr (hfail he)
    · exact Or.inl he

/-! ## The deletion estimate in subtraction form -/

/-- E1 deletion bookkeeping: the retained set `Ĉ = Chat` keeps at least
`|D| - c⁻¹|D|/log|D|` points. -/
theorem chat_card_ge {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    {D : Finset (Fin ell → ℤ)} {M : Fin ell → ℕ} (hE : Eligible β pkg.m₀ D M) :
    (D.card : ℝ) - pkg.c⁻¹ * D.card / Real.log D.card ≤
      ((pkg.out D M hE).Chat.card : ℝ) := by
  set o := pkg.out D M hE with ho
  have hsub : o.Chat ⊆ D := o.Chat_subset
  have hle : o.Chat.card ≤ D.card := Finset.card_le_card hsub
  have hcard : (D \ o.Chat).card = D.card - o.Chat.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  have h1 : ((D \ o.Chat).card : ℝ) = (D.card : ℝ) - (o.Chat.card : ℝ) := by
    rw [hcard, Nat.cast_sub hle]
  have h2 := o.Chat_card
  rw [h1] at h2
  linarith

/-! ## The generic coefficient-identification move -/

/-- **Generic identification move.**  For an eligible `D` (with the scale
threshold `1 ≤ c·s(D)` making `P(D)` proper), the deleted set `D̂ = Chat` maps
by the shell-preserving coefficient identification `φ_{P(D)}` bijectively onto
a set `D' ⊆ ℤ^{e}` (`e = d(D)` the displayed dimension) contained in the
symmetric coordinate box of `P(D)`'s radii, whose total box cardinality is
exactly `|P(D)|`.  This is the common core of the shrink and dimension moves
of `lem:unshifted-preprocessing`. -/
theorem identification_move {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    {D : Finset (Fin ell → ℤ)} {M : Fin ell → ℕ} (hE : Eligible β pkg.m₀ D M)
    (ht : 1 ≤ pkg.c * structureScale D.card)
    (lam : (Fin ell → ℤ) →+ ℤ) (X : ℕ)
    (hshell : ShellNonDividing (fun v => lam v) X D) :
    ∃ (lam' : (Fin (pkg.out D M hE).e → ℤ) →+ ℤ)
      (D' : Finset (Fin (pkg.out D M hE).e → ℤ)),
      D' ⊆ coordinateBox (pkg.out D M hE).P.radius ∧
      D'.card = (pkg.out D M hE).Chat.card ∧
      ShellNonDividing (fun n => lam' n) X D' ∧
      (coordinateBox (pkg.out D M hE).P.radius).card =
        (pkg.out D M hE).P.carrier.card := by
  classical
  set o := pkg.out D M hE with ho
  have hproper : o.P.Proper := o.P.proper_of_dilate ht o.inj
  have hChatP : o.Chat ⊆ o.P.carrier := fun v hv =>
    o.cover (Finset.mem_union_left _ hv)
  -- Lift `Chat` to the carrier subtype.
  set lift : {x // x ∈ o.Chat} ↪ {v // v ∈ o.P.carrier} :=
    ⟨fun x => ⟨x.1, hChatP x.2⟩, by
      intro x y hxy
      apply Subtype.ext
      exact Subtype.mk_eq_mk.mp hxy⟩ with hlift
  set Csub : Finset {v // v ∈ o.P.carrier} := o.Chat.attach.map lift with hCsub
  -- `Csub` maps back onto `Chat` under the subtype embedding.
  have hval : Csub.map ⟨Subtype.val, Subtype.val_injective⟩ = o.Chat := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (hCsub ▸ hv)
      exact x.2
    · intro hz
      refine Finset.mem_map.mpr ⟨lift ⟨z, hz⟩, ?_, rfl⟩
      rw [hCsub]
      exact Finset.mem_map_of_mem lift (Finset.mem_attach o.Chat ⟨z, hz⟩)
  -- The subtype shell property.
  have hshellsub : ShellNonDividing
      (fun v : {v // v ∈ o.P.carrier} => lam v.1) X Csub := by
    have := ShellNonDividing.of_map
      (ell := fun v => lam v) (S := Csub)
      ⟨Subtype.val, Subtype.val_injective⟩
      (by rw [hval]; exact hshell.mono o.Chat_subset)
    exact this
  -- Transport through the coefficient identification.
  have htrans := o.P.shell_transport hproper lam X Csub hshellsub
  refine ⟨o.P.transportedFunctional lam,
    Csub.map (o.P.coeffCarrierEmbedding hproper), ?_, ?_, htrans, ?_⟩
  · -- coefficients live in the coefficient box
    intro n hn
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hn
    exact o.P.coeffOf_mem v
  · rw [Finset.card_map, hCsub, Finset.card_map, Finset.card_attach]
  · calc (coordinateBox o.P.radius).card
        = o.P.coeffBox.card := by rw [GAP.coeffBox]
      _ = o.P.carrier.card := (o.P.card_carrier_of_proper hproper).symm

/-! ## Deliverable 2: the shrink move -/

/-- **Shrink move** (`lem:unshifted-preprocessing`, small-progression defect).
If the witness `D` has a small progression, `|P(D)| < γ|box M|`, then the
identification move lands a shell non-dividing set `D'` of cardinality
`≥ |D| - c⁻¹|D|/log|D|` inside a coordinate box in `ℤ^{d(D)}` of cardinality
`< γ·|box M|` — the box shrinks by the factor `γ`. -/
theorem small_progression_move {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    {D : Finset (Fin ell → ℤ)} {M : Fin ell → ℕ} (hE : Eligible β pkg.m₀ D M)
    (ht : 1 ≤ pkg.c * structureScale D.card) {γ : ℝ}
    (hsmall : ((pkg.out D M hE).P.carrier.card : ℝ) <
      γ * ((coordinateBox M).card : ℝ))
    (lam : (Fin ell → ℤ) →+ ℤ) (X : ℕ)
    (hshell : ShellNonDividing (fun v => lam v) X D) :
    ∃ (r : ℕ) (lam' : (Fin r → ℤ) →+ ℤ) (D' : Finset (Fin r → ℤ))
      (N : Fin r → ℕ),
      D' ⊆ coordinateBox N ∧
      ShellNonDividing (fun n => lam' n) X D' ∧
      (D.card : ℝ) - pkg.c⁻¹ * D.card / Real.log D.card ≤ (D'.card : ℝ) ∧
      ((coordinateBox N).card : ℝ) < γ * ((coordinateBox M).card : ℝ) ∧
      r = (pkg.out D M hE).e := by
  obtain ⟨lam', D', hbox, hcard, hshell', hboxcard⟩ :=
    identification_move pkg hE ht lam X hshell
  refine ⟨(pkg.out D M hE).e, lam', D', (pkg.out D M hE).P.radius,
    hbox, hshell', ?_, ?_, rfl⟩
  · rw [hcard]
    exact chat_card_ge pkg hE
  · rw [hboxcard]
    exact hsmall

end Nondividing
