import Nondividing.Geometry.ConvexLatticeJohn
import Nondividing.Shell

open scoped BigOperators

namespace Nondividing

/-!
# Projective cap lifting, deficient-rank alternative (Phase G, `lem:cap-lifting`)

Alternative (i) of `lem:cap-lifting`: any shell set `W ⊆ B` transfers, through
the coefficient identification of the John GAP `Q ⊇ W` (rank `r`, `|Q| ≤ C|B|`),
to a shell set in a symmetric coordinate box `B' ⊆ ℤ^r` with `|B'| ≤ C|B|` —
shell non-divisibility and the shell parameter preserved exactly.  (The `r = d`
refinement `|B'| ≪ η|B|` needs the perspective-cone volume; deferred.)
-/

/-- **Cap lifting, alternative (i)** (`lem:cap-lifting`).  Every shell
non-dividing `W ⊆ B` maps injectively into a symmetric coordinate box
`B' ⊆ ℤ^r` of size `≤ C·|B|` by a shell-preserving coefficient
identification. -/
theorem cap_lifting_deficient (d : ℕ) :
    ∃ C : ℕ, 0 < C ∧
    ∀ (W : Finset (Fin d → ℤ)) (M : Fin d → ℕ), W ⊆ coordinateBox M →
    ∀ (lam : (Fin d → ℤ) →+ ℤ) (X : ℕ),
    ShellNonDividing (fun v => lam v) X W →
    ∃ (r : ℕ) (lam' : (Fin r → ℤ) →+ ℤ) (W' : Finset (Fin r → ℤ))
      (N : Fin r → ℕ),
      W' ⊆ coordinateBox N ∧
      W'.card = W.card ∧
      ShellNonDividing (fun n => lam' n) X W' ∧
      (coordinateBox N).card ≤ C * (coordinateBox M).card := by
  classical
  obtain ⟨C, hC, hsec⟩ := section_in_gap d
  refine ⟨C, hC, ?_⟩
  intro W M hWbox lam X hshell
  obtain ⟨r, Q, hQprop, hWQ, hQcard⟩ := hsec W M hWbox
  -- Lift `W` to the carrier subtype.
  set lift : {x // x ∈ W} ↪ {v // v ∈ Q.carrier} :=
    ⟨fun x => ⟨x.1, hWQ x.2⟩, by
      intro x y hxy
      apply Subtype.ext
      exact Subtype.mk_eq_mk.mp hxy⟩ with hlift
  set Wsub : Finset {v // v ∈ Q.carrier} := W.attach.map lift with hWsub
  -- `Wsub` maps back onto `W` under the subtype embedding.
  have hval : Wsub.map ⟨Subtype.val, Subtype.val_injective⟩ = W := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (hWsub ▸ hv)
      exact x.2
    · intro hz
      refine Finset.mem_map.mpr ⟨lift ⟨z, hz⟩, ?_, rfl⟩
      rw [hWsub]
      exact Finset.mem_map_of_mem lift (Finset.mem_attach W ⟨z, hz⟩)
  -- The subtype shell property.
  have hshellsub : ShellNonDividing
      (fun v : {v // v ∈ Q.carrier} => lam v.1) X Wsub := by
    have := ShellNonDividing.of_map
      (ell := fun v => lam v) (S := Wsub)
      ⟨Subtype.val, Subtype.val_injective⟩ (by rwa [hval])
    exact this
  -- Transport through the coefficient identification.
  have htrans := Q.shell_transport hQprop lam X Wsub hshellsub
  refine ⟨r, Q.transportedFunctional lam,
    Wsub.map (Q.coeffCarrierEmbedding hQprop), Q.radius, ?_, ?_, htrans, ?_⟩
  · -- coefficients live in the coefficient box
    intro n hn
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hn
    exact Q.coeffOf_mem v
  · rw [Finset.card_map, hWsub, Finset.card_map, Finset.card_attach]
  · calc (coordinateBox Q.radius).card
        = Q.coeffBox.card := by rw [GAP.coeffBox]
      _ = Q.carrier.card := (Q.card_carrier_of_proper hQprop).symm
      _ ≤ C * (coordinateBox M).card := hQcard

end Nondividing
