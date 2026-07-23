import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Nondividing.Geometry.CoordProjection

open scoped BigOperators
open Module

namespace Nondividing

/-!
# Index equals determinant (Phase F, `lem:index-bound`)

The step lattice `L = ⟨q₁,…,q_d⟩ = range(evalHom)` of a full-rank GAP has index
`[ℤ^d : L] = |det(q₁,…,q_d)|`.  When `evalHom` is injective the standard basis
transports to a basis of `L` given by the steps, and mathlib's
`AddSubgroup.index_eq_natAbs_det` finishes.
-/

/-- `[ℤ^d : L] = |det(steps)|` for the step lattice `L = range(evalHom)` of a
full-rank GAP. -/
theorem index_range_eq_natAbs_det {d : ℕ} (P : GAP d d)
    (hinj : Function.Injective P.evalHom) :
    (LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index
      = ((Pi.basisFun ℤ (Fin d)).det (fun i => P.step i)).natAbs := by
  classical
  set f : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ) := P.evalHom.toIntLinearMap with hf
  have hfinj : Function.Injective f := hinj
  let bN : Basis (Fin d) ℤ (LinearMap.range f).toAddSubgroup :=
    (Pi.basisFun ℤ (Fin d)).map (LinearEquiv.ofInjective f hfinj)
  have hbN : (fun i => ((bN i : Fin d → ℤ))) = (fun i => P.step i) := by
    funext i
    show ((LinearEquiv.ofInjective f hfinj) (Pi.basisFun ℤ (Fin d) i) : Fin d → ℤ)
      = P.step i
    rw [LinearEquiv.ofInjective_apply, Pi.basisFun_apply]
    show P.evalHom (Pi.single i 1) = P.step i
    exact P.evalHom_single i
  rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d))
    (LinearMap.range f).toAddSubgroup bN]
  congr 1
  rw [hbN]

end Nondividing
