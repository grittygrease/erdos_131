import Nondividing.GAP
import Mathlib.Data.Finset.Preimage

open scoped BigOperators

namespace Nondividing

def ShellNonDividing {α : Type*} [DecidableEq α]
    (ell : α → ℤ) (X : ℕ) (V : Finset α) : Prop :=
  (∀ v ∈ V, (X : ℤ) ≤ ell v ∧ ell v ≤ 2 * X) ∧
  (∀ a ∈ V, ∀ S : Finset α, S.Nonempty → S ⊆ V.erase a →
    ¬ell a ∣ ∑ v ∈ S, ell v)

theorem ShellNonDividing.mono {α : Type*} [DecidableEq α]
    {ell : α → ℤ} {X : ℕ} {V W : Finset α}
    (hV : ShellNonDividing ell X V) (hWV : W ⊆ V) :
    ShellNonDividing ell X W := by
  constructor
  · intro w hw
    exact hV.1 w (hWV hw)
  · intro a ha S hS hSW
    apply hV.2 a (hWV ha) S hS
    intro s hs
    have hs' := Finset.mem_erase.mp (hSW hs)
    exact Finset.mem_erase.mpr ⟨hs'.1, hWV hs'.2⟩

theorem ShellNonDividing.map
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ell : α → ℤ} {μ : β → ℤ} {X : ℕ} {V : Finset α}
    (e : α ↪ β) (hval : ∀ a, μ (e a) = ell a)
    (hV : ShellNonDividing ell X V) :
    ShellNonDividing μ X (V.map e) := by
  constructor
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    simpa [hval] using hV.1 a ha
  · intro b hb S hS hsub
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    let T := S.preimage e e.injective.injOn
    have hmap : T.map e = S := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hz
        exact Finset.mem_preimage.mp ht
      · intro hz
        have hzV : z ∈ V.map e :=
          (Finset.erase_subset (e a) (V.map e)) (hsub hz)
        obtain ⟨t, ht, htz⟩ := Finset.mem_map.mp hzV
        subst z
        exact Finset.mem_map.mpr ⟨t, Finset.mem_preimage.mpr hz, rfl⟩
    have hT : T.Nonempty := by
      rw [← hmap] at hS
      simpa using hS
    have hTV : T ⊆ V.erase a := by
      intro t ht
      have het : e t ∈ S := Finset.mem_preimage.mp ht
      simpa using hsub het
    intro hdvd
    apply hV.2 a ha T hT hTV
    rw [← hmap] at hdvd
    simpa [Finset.sum_map, hval] using hdvd

/-- Reverse transport: shell non-dividing on an embedded image pulls back
along the embedding. -/
theorem ShellNonDividing.of_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ell : β → ℤ} {X : ℕ} {S : Finset α} (e : α ↪ β)
    (h : ShellNonDividing ell X (S.map e)) :
    ShellNonDividing (fun a => ell (e a)) X S := by
  constructor
  · intro a ha
    exact h.1 (e a) (Finset.mem_map_of_mem e ha)
  · intro a ha T hT hTsub hdvd
    apply h.2 (e a) (Finset.mem_map_of_mem e ha) (T.map e) hT.map
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hz
      have ht' := Finset.mem_erase.mp (hTsub ht)
      exact Finset.mem_erase.mpr
        ⟨fun hcon => ht'.1 (e.injective hcon), Finset.mem_map_of_mem e ht'.2⟩
    · rwa [Finset.sum_map]

/-- **Projective-convexity final contradiction** (`thm:projective-convexity`).
If a shell set `V` (for an integer-linear functional `ℓ`) contains `a`, and a
*positive* integer multiple `m₀·a` is a subset sum of `V \ {a}`, then shell
non-dividing is violated: applying `ℓ` gives `m₀·ℓ(a) = ∑ ℓ(v)`, so `ℓ(a)`
divides a nonempty sum of the other shell values. -/
theorem shellNonDividing_no_positive_multiple {d : ℕ} (ℓ : (Fin d → ℤ) →+ ℤ)
    {X : ℕ} {V : Finset (Fin d → ℤ)} (hX : 1 ≤ X)
    (hV : ShellNonDividing (fun v => ℓ v) X V) {a : Fin d → ℤ} (haV : a ∈ V)
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hmem : (m₀ • a) ∈ subsetSums (V.erase a)) : False := by
  classical
  obtain ⟨S, hSV, hSsum⟩ := mem_subsetSums.mp hmem
  -- `ℓ(a) > 0` from the shell condition
  have hla : 0 < ℓ a := by
    have h1 : (X : ℤ) ≤ ℓ a := (hV.1 a haV).1
    have h2 : (1 : ℤ) ≤ (X : ℤ) := by exact_mod_cast hX
    linarith
  -- `m₀·ℓ(a) = ∑_{v∈S} ℓ(v)`
  have hlm : (m₀ : ℤ) * ℓ a = ∑ v ∈ S, ℓ v := by
    have : ℓ (m₀ • a) = ∑ v ∈ S, ℓ v := by rw [← hSsum, map_sum]
    rwa [map_nsmul, nsmul_eq_mul] at this
  -- `S` is nonempty (else `m₀·a = 0`, forcing `a = 0`, contradicting `ℓ(a) > 0`)
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      rw [Finset.sum_empty] at hSsum
      have ha0 : a = 0 := by
        rcases smul_eq_zero.mp hSsum.symm with h | h
        · exact absurd h (by omega)
        · exact h
      rw [ha0, map_zero] at hla
      exact absurd hla (lt_irrefl 0)
    · exact hS
  -- `ℓ(a) ∣ ∑ ℓ(v)`, contradicting shell non-dividing
  exact hV.2 a haV S hSne hSV ⟨(m₀ : ℤ), by rw [← hlm]; ring⟩

namespace GAP

variable {d e : ℕ} (P : GAP d e)

def transportedFunctional (ell : (Fin d → ℤ) →+ ℤ) :
    (Fin e → ℤ) →+ ℤ :=
  ell.comp P.evalHom

@[simp] theorem transportedFunctional_apply
    (ell : (Fin d → ℤ) →+ ℤ) (n : Fin e → ℤ) :
    P.transportedFunctional ell n = ell (P.evalHom n) := rfl

noncomputable def coeffCarrierEmbedding (hP : P.Proper) :
    {v // v ∈ P.carrier} ↪ (Fin e → ℤ) where
  toFun := P.coeffOf
  inj' := by
    intro v w hvw
    apply Subtype.ext
    rw [← P.eval_coeffOf v, ← P.eval_coeffOf w, hvw]

theorem functional_transform
    (hP : P.Proper) (ell : (Fin d → ℤ) →+ ℤ)
    (v : {v // v ∈ P.carrier}) :
    P.transportedFunctional ell (P.coeffCarrierEmbedding hP v) = ell v := by
  simp [coeffCarrierEmbedding, P.eval_coeffOf v]

theorem shell_transport
    (hP : P.Proper) (ell : (Fin d → ℤ) →+ ℤ) (X : ℕ)
    (V : Finset {v // v ∈ P.carrier})
    (hV : ShellNonDividing
      (fun v : {v // v ∈ P.carrier} => ell v.1) X V) :
    ShellNonDividing (P.transportedFunctional ell) X
      (V.map (P.coeffCarrierEmbedding hP)) :=
  hV.map (P.coeffCarrierEmbedding hP)
    (fun v => P.functional_transform hP ell v)

end GAP

end Nondividing
