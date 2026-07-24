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

/-! ## Deliverable 4: termination skeleton

The iteration state, the move relation with the manuscript's three cases
(shrink / up / down) and their box bookkeeping, the one-step lemma
(`prep_step`, real content: dichotomy + the three moves), and the
well-founded iteration (`preprocessing_iteration`).  The strict decrease of a
termination measure is the manuscript's product-estimate numerology
(`γ ≤ δ^K`, `γ ≥ n^{-1/3}`, `n` large); it enters as an explicit hypothesis —
`TODO(orchestrator)`: discharge it, e.g. with the potential
`Φ(s) = log|box| + λ·dim`, `log C < λ < (1-ε)·log n`. -/

/-- **Well-founded descent.**  If from every non-`Good` state a `Rel`-step
strictly decreases a ℕ-measure, every state reaches a `Good` state. -/
theorem descend_to_good {α : Type*} (μ : α → ℕ) (Good : α → Prop)
    (Rel : α → α → Prop)
    (hstep : ∀ a, Good a ∨ ∃ b, Rel a b ∧ μ b < μ a) :
    ∀ a, ∃ b, Relation.ReflTransGen Rel a b ∧ Good b := by
  have key : ∀ n a, μ a ≤ n → ∃ b, Relation.ReflTransGen Rel a b ∧ Good b := by
    intro n
    induction n with
    | zero =>
      intro a ha
      rcases hstep a with hg | ⟨b, _, hlt⟩
      · exact ⟨a, Relation.ReflTransGen.refl, hg⟩
      · omega
    | succ n ih =>
      intro a ha
      rcases hstep a with hg | ⟨b, hab, hlt⟩
      · exact ⟨a, Relation.ReflTransGen.refl, hg⟩
      · obtain ⟨c, hbc, hc⟩ := ih b (by omega)
        exact ⟨c, Relation.ReflTransGen.head hab hbc, hc⟩
  intro a
  exact key (μ a) a le_rfl

/-- A preprocessing stage: an ambient dimension, a shell non-dividing set `V`
inside the symmetric coordinate box of radii `M`, with its integer-linear
shell functional (parameter `X`).  The manuscript's `A_j^♯ ⊆ Q_j ⊆ ℤ^{d_j}`. -/
structure PrepStage (X : ℕ) where
  /-- The ambient dimension of the stage. -/
  dim : ℕ
  /-- The stage set (image of the accepted set under the identifications). -/
  V : Finset (Fin dim → ℤ)
  /-- The radii of the ambient symmetric coordinate box. -/
  M : Fin dim → ℕ
  /-- The transported shell functional. -/
  lam : (Fin dim → ℤ) →+ ℤ
  /-- The stage set lives in the box. -/
  subset : V ⊆ coordinateBox M
  /-- Shell non-dividing is preserved along the iteration. -/
  shell : ShellNonDividing (fun v => lam v) X V

/-- Unshifted irreducibility of a stage, relative to a family of structural
packages (one for each ambient dimension, fixed before the iteration). -/
def StageIrreducible {X : ℕ} {β : ℝ} (pkgs : ∀ r, Package r β) (δ γ : ℝ)
    (s : PrepStage X) : Prop :=
  UnshiftedIrreducible (pkgs s.dim) δ γ s.V s.M

/-- The move relation of `lem:unshifted-preprocessing`: `s'` arises from `s`
by choosing a witness `D ⊆ V` of size `≥ δ|V|`, deleting at most
`c⁻¹|D|/log|D|` points, and applying the coefficient identification of
`P(D)`, with the manuscript's three box estimates:

* **shrink move** (same dimension): `|box'| < γ·|box|`;
* **up move** (dimension increases): `(c·s(D))^{d'}·|box'| ≤ 3^{d'}·s(D)^{d}·|box|`
  (the `s^{-(d'-d)}` decay in multiplied form);
* **down move** (dimension decreases): `c^{d'}·|box'| ≤ C·|box|`. -/
def PrepMove {X : ℕ} {β : ℝ} (pkgs : ∀ r, Package r β) (δ γ C : ℝ)
    (s s' : PrepStage X) : Prop :=
  ∃ D : Finset (Fin s.dim → ℤ), D ⊆ s.V ∧
    δ * (s.V.card : ℝ) ≤ (D.card : ℝ) ∧
    (D.card : ℝ) - (pkgs s.dim).c⁻¹ * D.card / Real.log D.card ≤
      (s'.V.card : ℝ) ∧
    s'.dim ≤ (pkgs s.dim).D ∧
    ((s'.dim = s.dim ∧
        ((coordinateBox s'.M).card : ℝ) <
          γ * ((coordinateBox s.M).card : ℝ)) ∨
      (s.dim < s'.dim ∧
        ((pkgs s.dim).c * structureScale D.card) ^ s'.dim *
            ((coordinateBox s'.M).card : ℝ) ≤
          3 ^ s'.dim * structureScale D.card ^ s.dim *
            ((coordinateBox s.M).card : ℝ)) ∨
      (s'.dim < s.dim ∧
        (pkgs s.dim).c ^ s'.dim * ((coordinateBox s'.M).card : ℝ) ≤
          C * ((coordinateBox s.M).card : ℝ)))

/-- **One-step lemma.**  There is a single constant `C` (uniform over ambient
dimensions `≤ dmax`) such that from every non-irreducible stage of dimension
`≤ dmax` whose `δ`-large subsets meet the scale thresholds, some `PrepMove`
is available.  This composes `irreducible_or_witness` with
`small_progression_move`, `dimension_move_up` and `dimension_move`. -/
theorem prep_step {X : ℕ} {β : ℝ} (pkgs : ∀ r, Package r β) (dmax : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (δ γ : ℝ) (s : PrepStage X), s.dim ≤ dmax →
        ¬ StageIrreducible pkgs δ γ s →
        (∀ D : Finset (Fin s.dim → ℤ), D ⊆ s.V →
          δ * (s.V.card : ℝ) ≤ (D.card : ℝ) →
          ∀ _hE : Eligible β (pkgs s.dim).m₀ D s.M,
          1 ≤ structureScale D.card ∧
            1 ≤ (pkgs s.dim).c * structureScale D.card) →
        ∃ s' : PrepStage X, PrepMove pkgs δ γ C s s' := by
  classical
  choose Cd hCd using fun r : ℕ => dimension_move r (pkgs r)
  set C : ℝ := ∑ r ∈ Finset.range (dmax + 1), Cd r with hCdef
  have hCpos : 0 < C :=
    Finset.sum_pos (fun r _ => (hCd r).1) ⟨0, Finset.mem_range.mpr (by omega)⟩
  refine ⟨C, hCpos, ?_⟩
  intro δ γ s hdim hnot hsupply
  rcases irreducible_or_witness (pkgs s.dim) δ γ s.V s.M with hirr |
    ⟨D, hDV, hDcard, hE, hdefect⟩
  · exact absurd hirr hnot
  obtain ⟨hs1, ht1⟩ := hsupply D hDV hDcard hE
  have hshellD : ShellNonDividing (fun v => s.lam v) X D := s.shell.mono hDV
  rcases Nat.lt_trichotomy ((pkgs s.dim).out D s.M hE).e s.dim with
    hlt | heq | hgt
  · -- down move
    obtain ⟨r, lam', D', N, hbox, hshell', hcardge, hr, hbound⟩ :=
      (hCd s.dim).2 D s.M hE hs1 ht1 s.lam X hshellD
    refine ⟨⟨r, D', N, lam', hbox, hshell'⟩, D, hDV, hDcard, hcardge, ?_,
      Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · show r ≤ (pkgs s.dim).D
      rw [hr]; exact ((pkgs s.dim).out D s.M hE).e_le
    · show r < s.dim
      rw [hr]; exact hlt
    · show (pkgs s.dim).c ^ r * ((coordinateBox N).card : ℝ) ≤
        C * ((coordinateBox s.M).card : ℝ)
      have hCle : Cd s.dim ≤ C := by
        rw [hCdef]
        exact Finset.single_le_sum (f := Cd) (fun i _ => (hCd i).1.le)
          (Finset.mem_range.mpr (by omega))
      rw [← hr] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right hCle (Nat.cast_nonneg _))
  · -- same dimension: the defect must be a small progression
    rcases hdefect with hne | hsmall
    · exact absurd heq hne
    obtain ⟨r, lam', D', N, hbox, hshell', hcardge, hboxlt, hr⟩ :=
      small_progression_move (pkgs s.dim) hE ht1 hsmall s.lam X hshellD
    refine ⟨⟨r, D', N, lam', hbox, hshell'⟩, D, hDV, hDcard, hcardge, ?_,
      Or.inl ⟨?_, hboxlt⟩⟩
    · show r ≤ (pkgs s.dim).D
      rw [hr]; exact ((pkgs s.dim).out D s.M hE).e_le
    · show r = s.dim
      rw [hr]; exact heq
  · -- up move
    obtain ⟨r, lam', D', N, hbox, hshell', hcardge, hr, hbound⟩ :=
      dimension_move_up (pkgs s.dim) hE hs1 ht1 s.lam X hshellD
    refine ⟨⟨r, D', N, lam', hbox, hshell'⟩, D, hDV, hDcard, hcardge, ?_,
      Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · show r ≤ (pkgs s.dim).D
      rw [hr]; exact ((pkgs s.dim).out D s.M hE).e_le
    · show s.dim < r
      rw [hr]; exact hgt
    · show ((pkgs s.dim).c * structureScale D.card) ^ r *
          ((coordinateBox N).card : ℝ) ≤
        3 ^ r * structureScale D.card ^ s.dim *
          ((coordinateBox s.M).card : ℝ)
      rw [← hr] at hbound
      exact hbound

/-- **Preprocessing iteration** (skeleton of `lem:unshifted-preprocessing`).
If every move strictly decreases a ℕ-measure (`TODO(orchestrator)`: this is
the manuscript's product-estimate termination, valid under `γ ≤ δ^K`,
`γ ≥ n^{-1/3}`, `n` large) and a move is available at every non-irreducible
stage, then from any start stage a finite chain of moves reaches an
unshiftedly `(δ,γ)`-irreducible stage. -/
theorem preprocessing_iteration {X : ℕ} {β : ℝ} (pkgs : ∀ r, Package r β)
    (δ γ C : ℝ) (μ : PrepStage X → ℕ)
    (hdec : ∀ s s' : PrepStage X, PrepMove pkgs δ γ C s s' → μ s' < μ s)
    (hmove : ∀ s : PrepStage X, ¬ StageIrreducible pkgs δ γ s →
      ∃ s', PrepMove pkgs δ γ C s s')
    (s₀ : PrepStage X) :
    ∃ s : PrepStage X,
      Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ s ∧
        StageIrreducible pkgs δ γ s := by
  refine descend_to_good μ (StageIrreducible pkgs δ γ)
    (PrepMove pkgs δ γ C) ?_ s₀
  intro a
  by_cases hg : StageIrreducible pkgs δ γ a
  · exact Or.inl hg
  · obtain ⟨b, hb⟩ := hmove a hg
    exact Or.inr ⟨b, hb, hdec _ _ hb⟩

/-- **Assembled iteration.**  `prep_step` supplies the moves; the remaining
hypotheses are exactly the manuscript's numerics, taken as input
(`TODO(orchestrator)`): a strictly decreasing measure for `PrepMove`, and at
every non-irreducible stage the dimension cutoff `dim ≤ dmax` plus the scale
thresholds for `δ`-large subsets. -/
theorem preprocessing_iteration_full {X : ℕ} {β : ℝ}
    (pkgs : ∀ r, Package r β) (dmax : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (δ γ : ℝ) (μ : PrepStage X → ℕ),
        (∀ s s' : PrepStage X, PrepMove pkgs δ γ C s s' → μ s' < μ s) →
        (∀ s : PrepStage X, ¬ StageIrreducible pkgs δ γ s →
          s.dim ≤ dmax ∧
          ∀ D : Finset (Fin s.dim → ℤ), D ⊆ s.V →
            δ * (s.V.card : ℝ) ≤ (D.card : ℝ) →
            ∀ _hE : Eligible β (pkgs s.dim).m₀ D s.M,
            1 ≤ structureScale D.card ∧
              1 ≤ (pkgs s.dim).c * structureScale D.card) →
        ∀ s₀ : PrepStage X,
          ∃ s : PrepStage X,
            Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ s ∧
              StageIrreducible pkgs δ γ s := by
  obtain ⟨C, hC, hstep⟩ := prep_step pkgs dmax
  refine ⟨C, hC, ?_⟩
  intro δ γ μ hdec hcond s₀
  refine preprocessing_iteration pkgs δ γ C μ hdec ?_ s₀
  intro s hns
  obtain ⟨hdim, hsup⟩ := hcond s hns
  exact hstep δ γ s hdim hns hsup

/-! ## Deliverable 4b: a concrete termination measure, discharged

The potential `Φ(s) = log|box_s| + λ·dim_s` drops by at least `1` under every
`PrepMove` once the manuscript's numeric thresholds hold: `log γ ≤ -1`
(shrink), `λ ≥ log C + D̄·log⁺(1/c) + 1` (down), and the witness scale
`log s(D) ≥ λ + D̄·(log 3 + log⁺(1/c)) + 1` (up; manuscript: `s(D) ≥ n^{1-ε}`).
Hence `⌊Φ⌋₊` is a strictly decreasing ℕ-measure, and the iteration
terminates: `preprocessing_iteration_measured`. -/

/-- Symmetric coordinate boxes are nonempty. -/
theorem one_le_card_coordinateBox {d : ℕ} (M : Fin d → ℕ) :
    1 ≤ (coordinateBox M).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_coordinateBox M⟩

/-- The termination potential `Φ(s) = log|box_s| + λ·dim_s`. -/
noncomputable def stagePotential {X : ℕ} (lam : ℝ) (s : PrepStage X) : ℝ :=
  Real.log ((coordinateBox s.M).card : ℝ) + lam * s.dim

/-- The ℕ-valued termination measure `⌊Φ⌋₊`. -/
noncomputable def stageMeasure {X : ℕ} (lam : ℝ) (s : PrepStage X) : ℕ :=
  ⌊stagePotential lam s⌋₊

theorem stagePotential_nonneg {X : ℕ} {lam : ℝ} (hlam : 0 ≤ lam)
    (s : PrepStage X) : 0 ≤ stagePotential lam s :=
  add_nonneg (Real.log_natCast_nonneg _)
    (mul_nonneg hlam (Nat.cast_nonneg _))

/-- Floor comparison: a unit drop of a nonnegative real strictly drops the
floor. -/
theorem floor_lt_floor_of_le_sub_one {x y : ℝ} (hy : 0 ≤ y) (h : y ≤ x - 1) :
    ⌊y⌋₊ < ⌊x⌋₊ := by
  have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
  have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ x := by push_cast; linarith
  have h3 : ⌊y⌋₊ + 1 ≤ ⌊x⌋₊ := Nat.le_floor h2
  omega

/-- **The potential drops by `≥ 1` along every move.**  Numeric thresholds:
`log γ ≤ -1` handles shrink moves; `λ` dominating `log C + D̄·log⁺(1/c) + 1`
handles down moves; the witness scale dominating
`λ + D̄·(log 3 + log⁺(1/c)) + 1` handles up moves.  These are exactly the
manuscript's `γ` small / `s(D) ≥ n^{1-ε}` large regime. -/
theorem prepMove_potential_decrease {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    {δ γ C lam : ℝ} {s s' : PrepStage X}
    (hC : 0 < C) (hγ0 : 0 < γ) (hγ : Real.log γ ≤ -1) (hlam0 : 0 ≤ lam)
    (hlam : Real.log C +
        ((pkgs s.dim).D : ℝ) * max 0 (Real.log ((pkgs s.dim).c)⁻¹) + 1 ≤ lam)
    (hscale : ∀ Dw : Finset (Fin s.dim → ℤ), Dw ⊆ s.V →
      δ * (s.V.card : ℝ) ≤ (Dw.card : ℝ) →
      1 ≤ structureScale Dw.card ∧
        lam + ((pkgs s.dim).D : ℝ) *
            (Real.log 3 + max 0 (Real.log ((pkgs s.dim).c)⁻¹)) + 1 ≤
          Real.log (structureScale Dw.card))
    (h : PrepMove pkgs δ γ C s s') :
    stagePotential lam s' ≤ stagePotential lam s - 1 := by
  classical
  obtain ⟨D, hDV, hDcard, _hdel, hdimD, hcases⟩ := h
  set c : ℝ := (pkgs s.dim).c with hcdef
  have hc : 0 < c := (pkgs s.dim).c_pos
  set Dd : ℝ := ((pkgs s.dim).D : ℝ) with hDddef
  set m : ℝ := max 0 (Real.log c⁻¹) with hmdef
  have hm0 : 0 ≤ m := le_max_left _ _
  have hmc : -Real.log c ≤ m := by
    rw [hmdef, Real.log_inv]
    exact le_max_right _ _
  have hDd0 : (0 : ℝ) ≤ Dd := Nat.cast_nonneg _
  have hd2Dd : (s'.dim : ℝ) ≤ Dd := by
    rw [hDddef]
    exact_mod_cast hdimD
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hB1 : (1 : ℝ) ≤ ((coordinateBox s.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s.M
  have hB'1 : (1 : ℝ) ≤ ((coordinateBox s'.M).card : ℝ) := by
    exact_mod_cast one_le_card_coordinateBox s'.M
  have hB0 : (0 : ℝ) < ((coordinateBox s.M).card : ℝ) :=
    lt_of_lt_of_le one_pos hB1
  have hB'0 : (0 : ℝ) < ((coordinateBox s'.M).card : ℝ) :=
    lt_of_lt_of_le one_pos hB'1
  simp only [stagePotential]
  rcases hcases with ⟨hdim, hlt⟩ | ⟨hlt, hbound⟩ | ⟨hlt, hbound⟩
  · -- shrink move: `log|box'| ≤ log γ + log|box| ≤ log|box| - 1`
    have hlog : Real.log ((coordinateBox s'.M).card : ℝ) ≤
        Real.log γ + Real.log ((coordinateBox s.M).card : ℝ) := by
      have hstep := Real.log_le_log hB'0 hlt.le
      rwa [Real.log_mul (ne_of_gt hγ0) (ne_of_gt hB0)] at hstep
    have hdimR : ((s'.dim : ℕ) : ℝ) = ((s.dim : ℕ) : ℝ) := by rw [hdim]
    have hmul : lam * ((s'.dim : ℕ) : ℝ) = lam * ((s.dim : ℕ) : ℝ) := by
      rw [hdimR]
    linarith
  · -- up move: pay `λ·Δdim`, gain `Δdim·log s(D)`
    obtain ⟨hs1, hslog⟩ := hscale D hDV hDcard
    set sD : ℝ := structureScale D.card with hsDdef
    have hsD0 : (0 : ℝ) < sD := lt_of_lt_of_le one_pos hs1
    have e1 : Real.log ((c * sD) ^ s'.dim * ((coordinateBox s'.M).card : ℝ))
        = (s'.dim : ℝ) * (Real.log c + Real.log sD) +
          Real.log ((coordinateBox s'.M).card : ℝ) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hB'0), Real.log_pow,
        Real.log_mul (ne_of_gt hc) (ne_of_gt hsD0)]
    have e2 : Real.log (3 ^ s'.dim * sD ^ s.dim *
          ((coordinateBox s.M).card : ℝ))
        = (s'.dim : ℝ) * Real.log 3 + (s.dim : ℝ) * Real.log sD +
          Real.log ((coordinateBox s.M).card : ℝ) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hB0),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    have hL : (s'.dim : ℝ) * (Real.log c + Real.log sD) +
        Real.log ((coordinateBox s'.M).card : ℝ) ≤
        (s'.dim : ℝ) * Real.log 3 + (s.dim : ℝ) * Real.log sD +
          Real.log ((coordinateBox s.M).card : ℝ) := by
      rw [← e1, ← e2]
      exact Real.log_le_log (by positivity) hbound
    have hprod : 0 ≤ Dd * (Real.log 3 + m) :=
      mul_nonneg hDd0 (by linarith)
    have hd21 : ((s.dim : ℕ) : ℝ) + 1 ≤ ((s'.dim : ℕ) : ℝ) := by
      exact_mod_cast hlt
    have hd20 : (0 : ℝ) ≤ ((s'.dim : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep1 : (s'.dim : ℝ) * (Real.log 3 + -Real.log c) ≤
        Dd * (Real.log 3 + m) :=
      le_trans
        (mul_le_mul_of_nonneg_left (by linarith) hd20)
        (mul_le_mul_of_nonneg_right hd2Dd (by linarith))
    have hstep2 : Real.log sD - lam ≤
        (((s'.dim : ℕ) : ℝ) - ((s.dim : ℕ) : ℝ)) * (Real.log sD - lam) :=
      le_mul_of_one_le_left (by linarith) (by linarith)
    linarith [hL, hstep1, hstep2, hslog]
  · -- down move: pay `log C`, gain `λ·Δdim`
    obtain ⟨hs1, _⟩ := hscale D hDV hDcard
    have e1 : Real.log (c ^ s'.dim * ((coordinateBox s'.M).card : ℝ))
        = (s'.dim : ℝ) * Real.log c +
          Real.log ((coordinateBox s'.M).card : ℝ) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hB'0), Real.log_pow]
    have e2 : Real.log (C * ((coordinateBox s.M).card : ℝ))
        = Real.log C + Real.log ((coordinateBox s.M).card : ℝ) := by
      rw [Real.log_mul (ne_of_gt hC) (ne_of_gt hB0)]
    have hL : (s'.dim : ℝ) * Real.log c +
        Real.log ((coordinateBox s'.M).card : ℝ) ≤
        Real.log C + Real.log ((coordinateBox s.M).card : ℝ) := by
      rw [← e1, ← e2]
      exact Real.log_le_log (by positivity) hbound
    have hd12 : ((s'.dim : ℕ) : ℝ) + 1 ≤ ((s.dim : ℕ) : ℝ) := by
      exact_mod_cast hlt
    have hd20 : (0 : ℝ) ≤ ((s'.dim : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep1 : (s'.dim : ℝ) * (-Real.log c) ≤ Dd * m :=
      le_trans (mul_le_mul_of_nonneg_left hmc hd20)
        (mul_le_mul_of_nonneg_right hd2Dd hm0)
    have hstep2 : lam ≤ lam * (((s.dim : ℕ) : ℝ) - ((s'.dim : ℕ) : ℝ)) :=
      le_mul_of_one_le_right hlam0 (by linarith)
    linarith [hL, hstep1, hstep2, hlam]

/-- The ℕ-measure `⌊Φ⌋₊` strictly decreases along every move (thresholds as
in `prepMove_potential_decrease`). -/
theorem prepMove_measure_decrease {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    {δ γ C lam : ℝ} {s s' : PrepStage X}
    (hC : 0 < C) (hγ0 : 0 < γ) (hγ : Real.log γ ≤ -1) (hlam0 : 0 ≤ lam)
    (hlam : Real.log C +
        ((pkgs s.dim).D : ℝ) * max 0 (Real.log ((pkgs s.dim).c)⁻¹) + 1 ≤ lam)
    (hscale : ∀ Dw : Finset (Fin s.dim → ℤ), Dw ⊆ s.V →
      δ * (s.V.card : ℝ) ≤ (Dw.card : ℝ) →
      1 ≤ structureScale Dw.card ∧
        lam + ((pkgs s.dim).D : ℝ) *
            (Real.log 3 + max 0 (Real.log ((pkgs s.dim).c)⁻¹)) + 1 ≤
          Real.log (structureScale Dw.card))
    (h : PrepMove pkgs δ γ C s s') :
    stageMeasure lam s' < stageMeasure lam s :=
  floor_lt_floor_of_le_sub_one (stagePotential_nonneg hlam0 s')
    (prepMove_potential_decrease hC hγ0 hγ hlam0 hlam hscale h)

/-- **Measured preprocessing iteration** — the termination measure is now
*discharged*: only the manuscript's numeric thresholds remain as hypotheses
(`TODO(orchestrator)`: derive them from `γ ≤ δ^K`, `γ ≥ n^{-1/3}`,
`|A_j| > n^{1-ε/2}`, `n` large).  From any start stage, a finite chain of
`PrepMove`s reaches an unshiftedly `(δ,γ)`-irreducible stage. -/
theorem preprocessing_iteration_measured {X : ℕ} {β : ℝ}
    (pkgs : ∀ r, Package r β) (dmax : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (δ γ lam : ℝ), 0 < γ → Real.log γ ≤ -1 → 0 ≤ lam →
        (∀ s : PrepStage X, ¬ StageIrreducible pkgs δ γ s →
          s.dim ≤ dmax ∧
          (Real.log C + ((pkgs s.dim).D : ℝ) *
              max 0 (Real.log ((pkgs s.dim).c)⁻¹) + 1 ≤ lam) ∧
          ∀ D : Finset (Fin s.dim → ℤ), D ⊆ s.V →
            δ * (s.V.card : ℝ) ≤ (D.card : ℝ) →
            1 ≤ structureScale D.card ∧
            1 ≤ (pkgs s.dim).c * structureScale D.card ∧
            lam + ((pkgs s.dim).D : ℝ) *
                (Real.log 3 + max 0 (Real.log ((pkgs s.dim).c)⁻¹)) + 1 ≤
              Real.log (structureScale D.card)) →
        ∀ s₀ : PrepStage X,
          ∃ s : PrepStage X,
            Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ s ∧
              StageIrreducible pkgs δ γ s := by
  obtain ⟨C, hC, hstep⟩ := prep_step pkgs dmax
  refine ⟨C, hC, ?_⟩
  intro δ γ lam hγ0 hγ hlam0 hcond s₀
  refine descend_to_good (stageMeasure lam) (StageIrreducible pkgs δ γ)
    (PrepMove pkgs δ γ C) ?_ s₀
  intro a
  by_cases hg : StageIrreducible pkgs δ γ a
  · exact Or.inl hg
  · obtain ⟨hdim, hlamS, hsup⟩ := hcond a hg
    obtain ⟨b, hb⟩ := hstep δ γ a hdim hg
      (fun D h1 h2 _hE => ⟨(hsup D h1 h2).1, (hsup D h1 h2).2.1⟩)
    refine Or.inr ⟨b, hb, ?_⟩
    exact prepMove_measure_decrease hC hγ0 hγ hlam0 hlamS
      (fun Dw hw1 hw2 => ⟨(hsup Dw hw1 hw2).1, (hsup Dw hw1 hw2).2.2⟩) hb

/-! ## Deliverable 5 (toward assembly): reachability-relative iteration and
the cardinality estimate along the chain

The numeric thresholds are only available (and only true) at stages
*reachable* from the start — the manuscript proves them inductively along the
iteration (`|A_i| ≥ δ_*^i n`, dimensions stay `< d̄`).  We therefore provide
the descent and the chain bookkeeping in reachability-relative form, and the
manuscript's cardinality estimate `|A_i| ≥ δ_*^i·n` with the iteration count
`i` bounded by the initial measure. -/

/-- Reachability-relative well-founded descent: the step hypothesis is only
required at stages reachable from the start. -/
theorem descend_to_good_from {α : Type*} (μ : α → ℕ) (Good : α → Prop)
    (Rel : α → α → Prop) (a₀ : α)
    (hstep : ∀ a, Relation.ReflTransGen Rel a₀ a →
      Good a ∨ ∃ b, Rel a b ∧ μ b < μ a) :
    ∃ b, Relation.ReflTransGen Rel a₀ b ∧ Good b := by
  have key : ∀ n a, Relation.ReflTransGen Rel a₀ a → μ a ≤ n →
      ∃ b, Relation.ReflTransGen Rel a₀ b ∧ Good b := by
    intro n
    induction n with
    | zero =>
      intro a hreach ha
      rcases hstep a hreach with hg | ⟨b, _, hlt⟩
      · exact ⟨a, hreach, hg⟩
      · omega
    | succ n ih =>
      intro a hreach ha
      rcases hstep a hreach with hg | ⟨b, hab, hlt⟩
      · exact ⟨a, hreach, hg⟩
      · exact ih b (hreach.tail hab) (by omega)
  exact key (μ a₀) a₀ Relation.ReflTransGen.refl le_rfl

/-- **Chain power estimate.**  If along a `Rel`-chain each step multiplies a
nonnegative weight `f` by at least `ρ ∈ [0,1]` and strictly decreases a
ℕ-measure `μ`, then the endpoint weight is at least `ρ^{μ(start)}·f(start)`
(the chain has at most `μ(start)` steps).  This is the manuscript's
`|A_i| ≥ δ_*^i·n` bookkeeping. -/
theorem chain_pow_lower {α : Type*} (μ : α → ℕ) (Rel : α → α → Prop)
    (f : α → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hf : ∀ x, 0 ≤ f x) {a b : α}
    (hchain : Relation.ReflTransGen Rel a b)
    (hdec : ∀ x y, Relation.ReflTransGen Rel a x → Rel x y → μ y < μ x)
    (hlow : ∀ x y, Relation.ReflTransGen Rel a x → Rel x y →
      ρ * f x ≤ f y) :
    ρ ^ μ a * f a ≤ f b := by
  suffices h : ∃ n, n + μ b ≤ μ a ∧ ρ ^ n * f a ≤ f b by
    obtain ⟨n, hn, hρn⟩ := h
    calc ρ ^ μ a * f a ≤ ρ ^ n * f a := by
          apply mul_le_mul_of_nonneg_right _ (hf a)
          exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
      _ ≤ f b := hρn
  induction hchain with
  | refl => exact ⟨0, by omega, by simp⟩
  | @tail x y hax hxy ih =>
      obtain ⟨n, hn, hρn⟩ := ih
      have hd := hdec x y hax hxy
      refine ⟨n + 1, by omega, ?_⟩
      calc ρ ^ (n + 1) * f a = ρ * (ρ ^ n * f a) := by ring
        _ ≤ ρ * f x := mul_le_mul_of_nonneg_left hρn hρ0
        _ ≤ f y := hlow x y hax hxy

/-- Monotone weight along a chain (reachability-relative step hypothesis). -/
theorem chain_le {α : Type*} (g : α → ℝ) (Rel : α → α → Prop) {a b : α}
    (hchain : Relation.ReflTransGen Rel a b)
    (hstep : ∀ x y, Relation.ReflTransGen Rel a x → Rel x y → g y ≤ g x) :
    g b ≤ g a := by
  induction hchain with
  | refl => exact le_refl _
  | @tail x y hax hxy ih => exact le_trans (hstep x y hax hxy) ih

/-- Single-move cardinality retention: when the E1 deletion at the witness is
at most `(δ/2)|V|` (manuscript: `c⁻¹|D|/log|D| = o(|D|)`), each move keeps
`|V'| ≥ (δ/2)|V|` — the manuscript's `|A_{j+1}| ≥ δ_*|A_j|`. -/
theorem prepMove_card_lower {X : ℕ} {β : ℝ} {pkgs : ∀ r, Package r β}
    {δ γ C : ℝ} {s s' : PrepStage X}
    (h : PrepMove pkgs δ γ C s s')
    (hdel : ∀ D : Finset (Fin s.dim → ℤ), D ⊆ s.V →
      δ * (s.V.card : ℝ) ≤ (D.card : ℝ) →
      (pkgs s.dim).c⁻¹ * D.card / Real.log D.card ≤
        δ / 2 * (s.V.card : ℝ)) :
    δ / 2 * (s.V.card : ℝ) ≤ (s'.V.card : ℝ) := by
  obtain ⟨D, hDV, hDcard, hdrop, _, _⟩ := h
  have hd := hdel D hDV hDcard
  linarith

/-- **Toward `lem:unshifted-preprocessing`** (assembled skeleton).  Under the
manuscript's numeric thresholds — required only at stages *reachable* from
the start (`TODO(orchestrator)`: derive them from `γ ≤ δ^K`, `γ ≥ n^{-1/3}`,
`n` large, exactly as in Manuscript.tex 560–660) — the iteration reaches an
unshiftedly `(δ,γ)`-irreducible stage `s` with the cardinality estimate
`(δ/2)^{⌊Φ(s₀)⌋}·|V₀| ≤ |V_s|` (whence `|Ṽ| > n^{1-ε}` after the
orchestrator's count bound).  Shell non-dividing holds at `s` by
construction (`s.shell`), and `s.V ⊆ box s.M` (`s.subset`). -/
theorem unshifted_preprocessing_toward {X : ℕ} {β : ℝ}
    (pkgs : ∀ r, Package r β) (dmax : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (δ γ lam : ℝ), 0 < γ → Real.log γ ≤ -1 → 0 ≤ lam →
        0 ≤ δ → δ ≤ 2 →
        ∀ s₀ : PrepStage X,
          (∀ s : PrepStage X,
            Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ s →
            s.dim ≤ dmax ∧
            (Real.log C + ((pkgs s.dim).D : ℝ) *
                max 0 (Real.log ((pkgs s.dim).c)⁻¹) + 1 ≤ lam) ∧
            ∀ D : Finset (Fin s.dim → ℤ), D ⊆ s.V →
              δ * (s.V.card : ℝ) ≤ (D.card : ℝ) →
              1 ≤ structureScale D.card ∧
              1 ≤ (pkgs s.dim).c * structureScale D.card ∧
              (lam + ((pkgs s.dim).D : ℝ) *
                  (Real.log 3 + max 0 (Real.log ((pkgs s.dim).c)⁻¹)) + 1 ≤
                Real.log (structureScale D.card)) ∧
              (pkgs s.dim).c⁻¹ * D.card / Real.log D.card ≤
                δ / 2 * (s.V.card : ℝ)) →
          ∃ s : PrepStage X,
            Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ s ∧
            StageIrreducible pkgs δ γ s ∧
            (δ / 2) ^ stageMeasure lam s₀ * (s₀.V.card : ℝ) ≤
              (s.V.card : ℝ) ∧
            Real.log ((coordinateBox s.M).card : ℝ) ≤
              stagePotential lam s₀ := by
  obtain ⟨C, hC, hstep⟩ := prep_step pkgs dmax
  refine ⟨C, hC, ?_⟩
  intro δ γ lam hγ0 hγ hlam0 hδ0 hδ2 s₀ hcond
  -- The per-move measure decrease at reachable stages.
  have hdec : ∀ x y : PrepStage X,
      Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ x →
      PrepMove pkgs δ γ C x y →
      stageMeasure lam y < stageMeasure lam x := by
    intro x y hx hxy
    obtain ⟨_, hlamS, hsup⟩ := hcond x hx
    exact prepMove_measure_decrease hC hγ0 hγ hlam0 hlamS
      (fun Dw hw1 hw2 => ⟨(hsup Dw hw1 hw2).1, (hsup Dw hw1 hw2).2.2.1⟩) hxy
  -- The per-move cardinality retention at reachable stages.
  have hlow : ∀ x y : PrepStage X,
      Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ x →
      PrepMove pkgs δ γ C x y →
      δ / 2 * (x.V.card : ℝ) ≤ (y.V.card : ℝ) := by
    intro x y hx hxy
    obtain ⟨_, _, hsup⟩ := hcond x hx
    exact prepMove_card_lower hxy
      (fun Dw hw1 hw2 => (hsup Dw hw1 hw2).2.2.2)
  -- The descent step at reachable stages.
  have hstepgood : ∀ a : PrepStage X,
      Relation.ReflTransGen (PrepMove pkgs δ γ C) s₀ a →
      StageIrreducible pkgs δ γ a ∨
        ∃ b, PrepMove pkgs δ γ C a b ∧
          stageMeasure lam b < stageMeasure lam a := by
    intro a hreach
    by_cases hg : StageIrreducible pkgs δ γ a
    · exact Or.inl hg
    · obtain ⟨hdim, hlamS, hsup⟩ := hcond a hreach
      obtain ⟨b, hb⟩ := hstep δ γ a hdim hg
        (fun D h1 h2 _hE => ⟨(hsup D h1 h2).1, (hsup D h1 h2).2.1⟩)
      exact Or.inr ⟨b, hb, hdec a b hreach hb⟩
  -- Reach an irreducible stage by well-founded descent.
  obtain ⟨s, hreach, hirr⟩ :=
    descend_to_good_from (stageMeasure lam)
      (StageIrreducible pkgs δ γ) (PrepMove pkgs δ γ C) s₀ hstepgood
  refine ⟨s, hreach, hirr, ?_, ?_⟩
  · exact chain_pow_lower (stageMeasure lam) (PrepMove pkgs δ γ C)
      (fun t => (t.V.card : ℝ)) (δ / 2) (by linarith) (by linarith)
      (fun t => Nat.cast_nonneg _) hreach hdec hlow
  · -- coarse box bound from potential monotonicity
    have hpot : stagePotential lam s ≤ stagePotential lam s₀ := by
      refine chain_le (stagePotential lam) (PrepMove pkgs δ γ C) hreach ?_
      intro x y hx hxy
      obtain ⟨_, hlamS, hsup⟩ := hcond x hx
      have hd := prepMove_potential_decrease hC hγ0 hγ hlam0 hlamS
        (fun Dw hw1 hw2 => ⟨(hsup Dw hw1 hw2).1, (hsup Dw hw1 hw2).2.2.1⟩) hxy
      linarith
    have hdim0 : 0 ≤ lam * (s.dim : ℝ) :=
      mul_nonneg hlam0 (Nat.cast_nonneg _)
    have := stagePotential_nonneg hlam0 s
    simp only [stagePotential] at hpot ⊢
    linarith

end Nondividing
