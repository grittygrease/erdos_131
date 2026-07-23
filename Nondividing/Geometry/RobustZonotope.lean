import Nondividing.Structure
import Nondividing.Geometry.Zonotope

open scoped BigOperators

namespace Nondividing

/-!
# The robust zonotope theorem (Phase F, `lem:robust-zonotope`)

Full assembly: `slab_exclusion` (via `robust_slab_bound`) feeds the slab-card
hypothesis of the mass-counting core `symZonotope_contains_box_of_slab_bound`,
and the shift step moves the symmetric containment to the one-sided zonotope
`Z(C)`.  Conclusion: `z_C + ε·B_ℝ ⊆ Z(C)` with `ε ≤ c_w·γ·(m − 2δ|V|)`
(manuscript: `ξ ≍ μγ`, since `m ≍ μn` dominates `2δn`).
-/

/-- **Robust zonotope** (`lem:robust-zonotope`).  For weights `θ` on `C ⊆ V`
with mass `≥ m` and `θ_v ≤ 1/2`, under `(δ,γ)`-irreducibility with eligibility
and scale thresholds for all large subsets, the shifted box
`z_C + ε·B_ℝ` lies inside the one-sided zonotope `Z(C)` whenever
`ε ≤ c_w·γ·(m − 2δ|V|)`. -/
theorem robust_zonotope {d : ℕ} {β : ℝ} (pkg : Package d β) (hd : 1 ≤ d) :
    ∃ cw K : ℝ, 0 < cw ∧ 0 < K ∧
    ∀ (V C : Finset (Fin d → ℤ)) (M : Fin d → ℕ) (δ γ : ℝ)
      (θ : (Fin d → ℤ) → ℝ) (m ε : ℝ),
      UnshiftedIrreducible pkg δ γ V M → C ⊆ V → 0 < γ → 0 ≤ δ →
      (∀ D : Finset (Fin d → ℤ), D ⊆ V → δ * (V.card : ℝ) ≤ (D.card : ℝ) →
        ∃ hE : Eligible β pkg.m₀ D M,
          1 ≤ External.structureScale D.card ∧
          1 ≤ pkg.c * External.structureScale D.card ∧
          K < External.structureScale D.card * γ) →
      (∀ v ∈ C, 0 ≤ θ v) → (∀ v ∈ C, θ v ≤ 1 / 2) →
      m ≤ ∑ v ∈ C, θ v →
      0 < m - 2 * (δ * (V.card : ℝ)) →
      ε ≤ (cw * γ) * (m - 2 * (δ * (V.card : ℝ))) →
      ∀ y : Fin d → ℝ,
        (∀ i, |y i - ∑ v ∈ C, θ v * (v i : ℝ)| ≤ ε * (M i : ℝ)) →
        y ∈ realZonotope C := by
  classical
  obtain ⟨cw, K, hcw, hK, hslab⟩ := robust_slab_bound pkg hd
  refine ⟨cw, K, hcw, hK, ?_⟩
  intro V C M δ γ θ m ε hirr hCV hγ hδ hsupply hθ0 hθhalf hmass hgap hεκ y hy
  -- The centred difference lies in the symmetric zonotope.
  have hx : (fun j => y j - ∑ v ∈ C, θ v * (v j : ℝ)) ∈ symZonotope C θ := by
    refine symZonotope_contains_box_of_slab_bound hθ0 hθhalf hmass hgap
      (by positivity) hεκ ?_ hy
    intro f ρ hρ0 hρw
    exact hslab V C M δ γ hirr hCV hγ hsupply f ρ hρ0 hρw
  -- Shift back into the one-sided zonotope.
  have := centre_add_symZonotope_subset_realZonotope hθ0 hθhalf hx
  have hy' : (fun j => (∑ v ∈ C, θ v * (v j : ℝ))
      + (y j - ∑ v ∈ C, θ v * (v j : ℝ))) = y := by
    funext j; ring
  rwa [hy'] at this

end Nondividing
