import Nondividing.Structure
import Nondividing.Geometry.Zonotope
import Nondividing.Filling

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

/-- **The tube inclusion** (`thm:projective-convexity` (†)).  Composing
`robust_zonotope` with `one_sided_filling`: under the irreducibility, weight,
and structural-core hypotheses, every step-lattice point `y` whose shift
`y − q` is `ε`-close (coordinatewise, relative to the box) to the zonotope
centre `z̄ = ∑ θ_v·v` is a subset sum of `C`.  This is the exact hypothesis
shape consumed by `projective_convexity_of_tube`. -/
theorem tube_inclusion {d : ℕ} {β : ℝ} (pkg : Package d β) (hd : 1 ≤ d) :
    ∃ cw K : ℝ, 0 < cw ∧ 0 < K ∧
    ∀ (V Cbar C C0 : Finset (Fin d → ℤ)) (M : Fin d → ℕ)
      (δ γ m ε cs : ℝ) (θ : (Fin d → ℤ) → ℝ) (P : GAP d d) (q : Fin d → ℤ),
      -- robust-zonotope block
      UnshiftedIrreducible pkg δ γ V M → Cbar ⊆ V → 0 < γ → 0 ≤ δ →
      (∀ D : Finset (Fin d → ℤ), D ⊆ V → δ * (V.card : ℝ) ≤ (D.card : ℝ) →
        ∃ hE : Eligible β pkg.m₀ D M,
          1 ≤ External.structureScale D.card ∧
          1 ≤ pkg.c * External.structureScale D.card ∧
          K < External.structureScale D.card * γ) →
      (∀ v ∈ Cbar, 0 ≤ θ v) → (∀ v ∈ Cbar, θ v ≤ 1 / 2) →
      m ≤ ∑ v ∈ Cbar, θ v →
      0 < m - 2 * (δ * (V.card : ℝ)) →
      ε ≤ (cw * γ) * (m - 2 * (δ * (V.card : ℝ))) →
      -- filling block
      P.realRank = d → Cbar ⊆ P.carrier → 0 ≤ cs →
      Real.sqrt (d * (Cbar.card + 1)) * 3 ≤ cs / 2 →
      (∀ w ∈ P.dilatedCarrier cs, q + w ∈ subsetSums C0) →
      Disjoint Cbar C0 → Cbar ∪ C0 ⊆ C →
      -- the point
      ∀ (y ny nq : Fin d → ℤ), P.evalHom ny = y → P.evalHom nq = q →
      (∀ i, |(((y - q) i : ℤ) : ℝ) - ∑ v ∈ Cbar, θ v * (v i : ℝ)|
        ≤ ε * (M i : ℝ)) →
      y ∈ subsetSums C := by
  obtain ⟨cw, K, hcw, hK, hrz⟩ := robust_zonotope pkg hd
  refine ⟨cw, K, hcw, hK, ?_⟩
  intro V Cbar C C0 M δ γ m ε cs θ P q hirr hCV hγ hδ hsupply hθ0 hθhalf
    hmass hgap hεκ hrank hCbarP hcs hthr hcore hdisj hsub y ny nq hy hq hclose
  -- The shifted point lies in the zonotope.
  have hzon : (fun j => (((y - q) j : ℤ) : ℝ)) ∈ realZonotope Cbar :=
    hrz V Cbar M δ γ θ m ε hirr hCV hγ hδ hsupply hθ0 hθhalf hmass hgap hεκ
      _ hclose
  -- Feed it to the filling.
  exact tube_inclusion_of_zonotope P hrank hCbarP hcs hthr hcore hdisj hsub
    hy hq ((realZonotope_iff_inZonotope Cbar _).mp hzon)

/-- **Tube shape bridge**: if `y − Ta` lies in the integer box `k·M` and the
centre satisfies `|((Ta−q)ᵢ) − z̄ᵢ| ≤ ε₂Mᵢ`, then `y − q` is `(k+ε₂)`-close to
`z̄` — converting `projective_convexity_of_tube`'s coordinateBox tube into
`tube_inclusion`'s ε-closeness. -/
theorem tube_closeness_of_box {d : ℕ} {y Ta q : Fin d → ℤ}
    {zbar : Fin d → ℝ} {M : Fin d → ℕ} {k : ℕ} {ε₂ : ℝ}
    (hbox : y - Ta ∈ coordinateBox (fun i => k * M i))
    (h2 : ∀ i, |(((Ta - q) i : ℤ) : ℝ) - zbar i| ≤ ε₂ * (M i : ℝ)) :
    ∀ i, |(((y - q) i : ℤ) : ℝ) - zbar i| ≤ ((k : ℝ) + ε₂) * (M i : ℝ) := by
  intro i
  have h1 := (mem_coordinateBox.mp hbox) i
  have h1R : |(((y - Ta) i : ℤ) : ℝ)| ≤ (k : ℝ) * (M i : ℝ) := by
    have : |(y - Ta) i| ≤ ((k * M i : ℕ) : ℤ) := abs_le.mpr h1
    calc |(((y - Ta) i : ℤ) : ℝ)| = ((|(y - Ta) i| : ℤ) : ℝ) := by
          rw [Int.cast_abs]
      _ ≤ (((k * M i : ℕ) : ℤ) : ℝ) := by exact_mod_cast this
      _ = (k : ℝ) * (M i : ℝ) := by push_cast; ring
  have hsplit : (((y - q) i : ℤ) : ℝ) - zbar i
      = (((y - Ta) i : ℤ) : ℝ) + ((((Ta - q) i : ℤ) : ℝ) - zbar i) := by
    push_cast [Pi.sub_apply]
    ring
  rw [hsplit]
  calc |(((y - Ta) i : ℤ) : ℝ) + ((((Ta - q) i : ℤ) : ℝ) - zbar i)|
      ≤ |(((y - Ta) i : ℤ) : ℝ)| + |(((Ta - q) i : ℤ) : ℝ) - zbar i| :=
        abs_add_le _ _
    _ ≤ (k : ℝ) * (M i : ℝ) + ε₂ * (M i : ℝ) := add_le_add h1R (h2 i)
    _ = ((k : ℝ) + ε₂) * (M i : ℝ) := by ring

end Nondividing
