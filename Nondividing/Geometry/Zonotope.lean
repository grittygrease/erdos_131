import Mathlib.Analysis.Convex.Body
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Nondividing.External.DiscreteJohn

open scoped BigOperators

namespace Nondividing

/-!
# The symmetric weighted zonotope (Phase F, `lem:robust-zonotope`)

`Z⁰ = ∑_{v∈C} [-θ_v, θ_v]·v` — the symmetric zonotope of the weighted set.
The robust-zonotope lemma separates a point outside `Z⁰` and contradicts
`slab_exclusion`; here we record the set, its convexity, compactness, and the
support-function bound.
-/

/-- The symmetric weighted zonotope `∑_{v∈C} [-θ_v, θ_v]·v ⊆ ℝ^d`. -/
def symZonotope {d : ℕ} (C : Finset (Fin d → ℤ)) (θ : (Fin d → ℤ) → ℝ) :
    Set (Fin d → ℝ) :=
  {x | ∃ t : (Fin d → ℤ) → ℝ, (∀ v ∈ C, |t v| ≤ θ v) ∧
    x = fun j => ∑ v ∈ C, t v * (v j : ℝ)}

theorem symZonotope_convex {d : ℕ} (C : Finset (Fin d → ℤ))
    (θ : (Fin d → ℤ) → ℝ) : Convex ℝ (symZonotope C θ) := by
  rintro x ⟨tx, htx, rfl⟩ y ⟨ty, hty, rfl⟩ s r hs hr hsr
  refine ⟨fun v => s * tx v + r * ty v, fun v hv => ?_, ?_⟩
  · calc |s * tx v + r * ty v| ≤ |s * tx v| + |r * ty v| := abs_add_le _ _
      _ = s * |tx v| + r * |ty v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hr]
      _ ≤ s * θ v + r * θ v := add_le_add
          (mul_le_mul_of_nonneg_left (htx v hv) hs)
          (mul_le_mul_of_nonneg_left (hty v hv) hr)
      _ = θ v := by rw [← add_mul, hsr, one_mul]
  · funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring

/-- The zonotope is the continuous image of the compact coefficient box, hence
compact. -/
theorem symZonotope_isCompact {d : ℕ} (C : Finset (Fin d → ℤ))
    (θ : (Fin d → ℤ) → ℝ) (hθ : ∀ v ∈ C, 0 ≤ θ v) :
    IsCompact (symZonotope C θ) := by
  classical
  -- Coefficient box over the subtype `↥C`.
  have hbox : IsCompact (Set.Icc (fun v : {v // v ∈ C} => -(θ v.1))
      (fun v : {v // v ∈ C} => θ v.1)) := isCompact_Icc
  -- The evaluation map.
  set F : ({v // v ∈ C} → ℝ) → (Fin d → ℝ) :=
    fun t => fun j => ∑ v ∈ C.attach, t v * (v.1 j : ℝ) with hF
  have hFcont : Continuous F := by
    apply continuous_pi
    intro j
    exact continuous_finsetSum _ fun v _ =>
      (continuous_apply v).mul continuous_const
  have himg : symZonotope C θ = F '' (Set.Icc
      (fun v : {v // v ∈ C} => -(θ v.1)) (fun v : {v // v ∈ C} => θ v.1)) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨fun v => t v.1, ⟨fun v => ?_, fun v => ?_⟩, ?_⟩
      · exact (abs_le.mp (ht v.1 v.2)).1
      · exact (abs_le.mp (ht v.1 v.2)).2
      · rw [hF]
        funext j
        beta_reduce
        exact (Finset.sum_attach C (fun v => t v * (v j : ℝ)))
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      refine ⟨fun v => if hv : v ∈ C then t ⟨v, hv⟩ else 0, fun v hv => ?_, ?_⟩
      · simp only [dif_pos hv]
        exact abs_le.mpr ⟨h1 ⟨v, hv⟩, h2 ⟨v, hv⟩⟩
      · rw [hF]
        funext j
        beta_reduce
        rw [← Finset.sum_attach C
          (fun v => (if hv : v ∈ C then t ⟨v, hv⟩ else 0) * (v j : ℝ))]
        exact Finset.sum_congr rfl fun v _ => by simp only [dif_pos v.2]
  rw [himg]
  exact hbox.image hFcont

/-- Support-function bound: every point of the zonotope has `f`-value at most
`∑_v θ_v·|f(v)|`, for any linear functional `f`. -/
theorem symZonotope_support_le {d : ℕ} {C : Finset (Fin d → ℤ)}
    {θ : (Fin d → ℤ) → ℝ} (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    {x : Fin d → ℝ} (hx : x ∈ symZonotope C θ) :
    f x ≤ ∑ v ∈ C, θ v * |f (External.realPoint v)| := by
  obtain ⟨t, ht, rfl⟩ := hx
  have hexp : f (fun j => ∑ v ∈ C, t v * (v j : ℝ))
      = ∑ v ∈ C, t v * f (External.realPoint v) := by
    rw [show (fun j => ∑ v ∈ C, t v * (v j : ℝ))
        = ∑ v ∈ C, t v • External.realPoint v from by
      funext j
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun v _ => by
        simp [External.realPoint, smul_eq_mul]]
    rw [map_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [map_smul, smul_eq_mul]
  rw [hexp]
  refine Finset.sum_le_sum fun v hv => ?_
  calc t v * f (External.realPoint v) ≤ |t v * f (External.realPoint v)| :=
        le_abs_self _
    _ = |t v| * |f (External.realPoint v)| := abs_mul _ _
    _ ≤ θ v * |f (External.realPoint v)| :=
        mul_le_mul_of_nonneg_right (ht v hv) (abs_nonneg _)

end Nondividing
