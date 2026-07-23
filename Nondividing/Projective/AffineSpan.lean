import Nondividing.Projective.Normalization
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

open scoped BigOperators

namespace Nondividing

open Nondividing.External

/-!
# Affine direction of the projective image (Phase E)

Toward `lem:projective-span` part 2 (`aff π(V) = H_λ`): the direction space of the
affine span of `π(V)` is contained in the hyperplane direction `ker λℝ`, since all
projective images lie on `{λℝ = 1}` and hence their differences are annihilated by
`λℝ`.  (The reverse inclusion follows from `span_projNorm_eq_top` by a dimension
count.)
-/

theorem vectorSpan_projNorm_le_ker {d : ℕ} (ℓ : Fin d → ℤ)
    {V : Finset (Fin d → ℤ)} (hpos : ∀ v ∈ V, intFunctional ℓ v ≠ 0) :
    vectorSpan ℝ (projNorm ℓ '' (V : Set (Fin d → ℤ)))
      ≤ LinearMap.ker (realFunctional ℓ) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub]
  rw [realFunctional_projNorm ℓ v (hpos v hv),
    realFunctional_projNorm ℓ w (hpos w hw)]
  ring

end Nondividing
