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

/-! ## Deliverable 3: the dimension move -/

/-- The real span of any subset of a rank-`e` GAP carrier has dimension at
most `e` (every carrier point is an integer combination of the `e` steps). -/
theorem finrank_integerRealSpan_le_of_subset_carrier {d e : ℕ} (P : GAP d e)
    {S : Finset (Fin d → ℤ)} (hS : S ⊆ P.carrier) :
    Module.finrank ℝ (integerRealSpan S) ≤ e := by
  classical
  have hsub : integerRealSpan S ≤
      Submodule.span ℝ
        (Set.range fun i : Fin e => (fun j : Fin d => (P.step i j : ℝ))) := by
    rw [integerRealSpan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨n, _hn, rfl⟩ := P.mem_carrier.mp (hS (Finset.mem_coe.mp hw))
    have heq : realPoint (P.evalHom n) =
        ∑ i, (n i : ℝ) • (fun j : Fin d => (P.step i j : ℝ)) := by
      funext j
      simp only [realPoint, GAP.evalHom_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      push_cast
      rfl
    rw [SetLike.mem_coe, heq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact le_trans (Submodule.finrank_mono hsub) (realRank_le P)

/-- Rank-exposed variant of `section_in_gap`: the John GAP produced for
`S ⊆ box M` has rank exactly `dim span_ℝ(S)` (and cardinality `≤ C·|box M|`).
The exposed rank feeds the manuscript's `e ≤ r` progression-comparison case,
where the John GAP of the core `C₀ ⊆ P(D)` has rank `≤ d(D)`. -/
theorem section_in_gap_rank (d : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (S : Finset (Fin d → ℤ)) (M : Fin d → ℕ),
      S ⊆ coordinateBox M →
      ∃ (r : ℕ) (Q : GAP d r),
        r = Module.finrank ℝ (integerRealSpan S) ∧
        Q.Proper ∧ S ⊆ Q.carrier ∧
        Q.carrier.card ≤ C * (coordinateBox M).card := by
  obtain ⟨C, hC, hjohn⟩ := coordinate_section_john d
  refine ⟨C, hC, ?_⟩
  intro S M hSbox
  set H := integerRealSpan S with hH
  obtain ⟨Q, _hstep, hproper, hcover, hcard⟩ :=
    hjohn (Module.finrank ℝ H) H M S rfl hSbox rfl
  refine ⟨Module.finrank ℝ H, Q, rfl, hproper, ?_, hcard⟩
  intro z hz
  apply hcover
  rw [mem_latticeSection]
  exact ⟨hSbox hz, Submodule.subset_span ⟨z, hz, rfl⟩⟩

/-- **Dimension move, uniform box bound** (`lem:unshifted-preprocessing`,
down-move estimate `|P_{j+1}| ≤ C|P_j|`).  There is a constant `C` (uniform in
the package) such that any eligible witness `D` with the scale thresholds
moves, through the coefficient identification of `P(D)`, to a shell
non-dividing `D' ⊆ ℤ^{d(D)}` in a coordinate box `N` with
`c^{d(D)}·|box N| ≤ C·|box M|`.  Valid for *every* displayed dimension
(the manuscript uses it when `d(D) < ℓ`); the sharper up-move decay is
`dimension_move_up`.  The chain is `progression_comparison_le` through the
John GAP of the core, whose rank is `≤ d(D)` by
`finrank_integerRealSpan_le_of_subset_carrier`. -/
theorem dimension_move (ell : ℕ) {β : ℝ} (pkg : Package ell β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : Finset (Fin ell → ℤ)) (M : Fin ell → ℕ)
        (hE : Eligible β pkg.m₀ D M),
        1 ≤ structureScale D.card →
        1 ≤ pkg.c * structureScale D.card →
        ∀ (lam : (Fin ell → ℤ) →+ ℤ) (X : ℕ),
          ShellNonDividing (fun v => lam v) X D →
          ∃ (r : ℕ) (lam' : (Fin r → ℤ) →+ ℤ) (D' : Finset (Fin r → ℤ))
            (N : Fin r → ℕ),
            D' ⊆ coordinateBox N ∧
            ShellNonDividing (fun n => lam' n) X D' ∧
            (D.card : ℝ) - pkg.c⁻¹ * D.card / Real.log D.card ≤ (D'.card : ℝ) ∧
            r = (pkg.out D M hE).e ∧
            pkg.c ^ (pkg.out D M hE).e * ((coordinateBox N).card : ℝ) ≤
              C * ((coordinateBox M).card : ℝ) := by
  classical
  obtain ⟨Cj, hCj, hsec⟩ := section_in_gap_rank ell
  have hCjR : (0 : ℝ) < (Cj : ℝ) := by exact_mod_cast hCj
  refine ⟨9 ^ pkg.D * Cj, by positivity, ?_⟩
  intro D M hE hs ht lam X hshell
  set o := pkg.out D M hE with ho
  obtain ⟨lam', D', hbox, hcard, hshell', hboxcard⟩ :=
    identification_move pkg hE ht lam X hshell
  refine ⟨o.e, lam', D', o.P.radius, hbox, hshell', ?_, rfl, ?_⟩
  · rw [hcard]
    exact chat_card_ge pkg hE
  · -- Counting chain through the John GAP of the core.
    set s := structureScale D.card with hsdef
    have hC₀box : o.C₀ ⊆ coordinateBox M :=
      (o.C₀_subset.trans o.Chat_subset).trans hE.subset
    obtain ⟨r₀, Q, hr₀, hQprop, hC₀Q, hQcard⟩ := hsec o.C₀ M hC₀box
    have hC₀P : o.C₀ ⊆ o.P.carrier := fun v hv =>
      o.cover (Finset.mem_union_left _ (o.C₀_subset hv))
    have hr₀e : r₀ ≤ o.e := by
      rw [hr₀]
      exact finrank_integerRealSpan_le_of_subset_carrier o.P hC₀P
    have hcount := o.P.progression_comparison_le (t := pkg.c * s) ht o.inj Q
      hQprop hC₀Q (le_refl o.C₀.card) o.incl (Cj := Cj)
      (Q := coordinateBox M) hQcard
    have hBnn : (0 : ℝ) ≤ ((coordinateBox M).card : ℝ) := Nat.cast_nonneg _
    have hspos : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
    have h3s1 : (1 : ℝ) ≤ 3 * s := by linarith
    have hk3s : 2 * (o.C₀.card : ℝ) + 1 ≤ 3 * s := by
      have h := o.C₀_card
      rw [← hsdef] at h
      linarith
    have hkpow : (2 * (o.C₀.card : ℝ) + 1) ^ r₀ ≤ (3 * s) ^ o.e :=
      le_trans (pow_le_pow_left₀ (by positivity) hk3s r₀)
        (pow_le_pow_right₀ h3s1 hr₀e)
    have h1 : (pkg.c * s) ^ o.e * (o.P.carrier.card : ℝ) ≤
        (3 ^ o.e * (3 * s) ^ o.e * Cj) * ((coordinateBox M).card : ℝ) := by
      refine hcount.trans ?_
      apply mul_le_mul_of_nonneg_right _ hBnn
      apply mul_le_mul_of_nonneg_right _ hCjR.le
      exact mul_le_mul_of_nonneg_left hkpow (by positivity)
    have h2 : pkg.c ^ o.e * (o.P.carrier.card : ℝ) ≤
        (9 : ℝ) ^ o.e * Cj * ((coordinateBox M).card : ℝ) := by
      have h1' : pkg.c ^ o.e * (o.P.carrier.card : ℝ) * s ^ o.e ≤
          (9 : ℝ) ^ o.e * Cj * ((coordinateBox M).card : ℝ) * s ^ o.e := by
        calc pkg.c ^ o.e * (o.P.carrier.card : ℝ) * s ^ o.e
            = (pkg.c * s) ^ o.e * (o.P.carrier.card : ℝ) := by
              rw [mul_pow]; ring
          _ ≤ (3 ^ o.e * (3 * s) ^ o.e * Cj) * ((coordinateBox M).card : ℝ) := h1
          _ = (9 : ℝ) ^ o.e * Cj * ((coordinateBox M).card : ℝ) * s ^ o.e := by
              rw [mul_pow, show (9 : ℝ) ^ o.e = 3 ^ o.e * 3 ^ o.e from by
                rw [← mul_pow]; norm_num]
              ring
      exact le_of_mul_le_mul_right h1' (by positivity)
    have h9 : (9 : ℝ) ^ o.e ≤ 9 ^ pkg.D :=
      pow_le_pow_right₀ (by norm_num) o.e_le
    calc pkg.c ^ o.e * ((coordinateBox o.P.radius).card : ℝ)
        = pkg.c ^ o.e * (o.P.carrier.card : ℝ) := by rw [hboxcard]
      _ ≤ (9 : ℝ) ^ o.e * Cj * ((coordinateBox M).card : ℝ) := h2
      _ ≤ 9 ^ pkg.D * Cj * ((coordinateBox M).card : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hBnn
          exact mul_le_mul_of_nonneg_right h9 hCjR.le

/-- **Dimension move, up-move decay** (`lem:unshifted-preprocessing`,
up-move estimate `|P_{j+1}| ≤ C·s^{-(d_{j+1}-d_j)}|P_j|` in multiplied form).
The witness moves into a coordinate box `N ⊆ ℤ^{d(D)}` with
`(c·s)^{d(D)}·|box N| ≤ 3^{d(D)}·s^ℓ·|box M|`; dividing out, for `d(D) > ℓ`
the box shrinks by `≈ s^{ℓ-d(D)}`. -/
theorem dimension_move_up {ell : ℕ} {β : ℝ} (pkg : Package ell β)
    {D : Finset (Fin ell → ℤ)} {M : Fin ell → ℕ} (hE : Eligible β pkg.m₀ D M)
    (hs : 1 ≤ structureScale D.card)
    (ht : 1 ≤ pkg.c * structureScale D.card)
    (lam : (Fin ell → ℤ) →+ ℤ) (X : ℕ)
    (hshell : ShellNonDividing (fun v => lam v) X D) :
    ∃ (r : ℕ) (lam' : (Fin r → ℤ) →+ ℤ) (D' : Finset (Fin r → ℤ))
      (N : Fin r → ℕ),
      D' ⊆ coordinateBox N ∧
      ShellNonDividing (fun n => lam' n) X D' ∧
      (D.card : ℝ) - pkg.c⁻¹ * D.card / Real.log D.card ≤ (D'.card : ℝ) ∧
      r = (pkg.out D M hE).e ∧
      (pkg.c * structureScale D.card) ^ (pkg.out D M hE).e *
          ((coordinateBox N).card : ℝ) ≤
        3 ^ (pkg.out D M hE).e * structureScale D.card ^ ell *
          ((coordinateBox M).card : ℝ) := by
  classical
  set o := pkg.out D M hE with ho
  obtain ⟨lam', D', hbox, hcard, hshell', hboxcard⟩ :=
    identification_move pkg hE ht lam X hshell
  refine ⟨o.e, lam', D', o.P.radius, hbox, hshell', ?_, rfl, ?_⟩
  · rw [hcard]
    exact chat_card_ge pkg hE
  · set s := structureScale D.card with hsdef
    have hcount := progression_comparison_package pkg hE ht
    push_cast at hcount
    have hmaxle : max (1 : ℝ) (o.C₀.card : ℝ) ≤ s := by
      refine max_le hs ?_
      have h := o.C₀_card
      rw [← hsdef] at h
      exact h
    have hpow : (max (1 : ℝ) (o.C₀.card : ℝ)) ^ ell ≤ s ^ ell :=
      pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmaxle ell
    calc (pkg.c * s) ^ o.e * ((coordinateBox o.P.radius).card : ℝ)
        = (pkg.c * s) ^ o.e * (o.P.carrier.card : ℝ) := by rw [hboxcard]
      _ ≤ (3 ^ o.e * (max 1 (o.C₀.card : ℝ)) ^ ell) *
            ((coordinateBox M).card : ℝ) := hcount
      _ ≤ 3 ^ o.e * s ^ ell * ((coordinateBox M).card : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)

end Nondividing
