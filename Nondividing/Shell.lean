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
