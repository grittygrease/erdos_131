import Nondividing.Geometry.RobustZonotope
import Nondividing.QuotientOrder

open scoped BigOperators

namespace Nondividing

/-!
# Projective convexity, assembled (Phase E, `thm:projective-convexity`)

The full contradiction: the tube inclusion (`robust_zonotope` ∘
`one_sided_filling`), the finite step-quotient (`index_bound`), and the shell
divisibility endgame (`projective_convexity_of_tube`) compose into the complete
theorem, parameterized over the structural package and the scale/threshold
choices that `projective_theorem` will make.
-/

/-- **Projective convexity, assembled** (`thm:projective-convexity`).
Under: a shell non-dividing `V` containing `a`; `(δ,γ)`-irreducibility with
eligibility/scale suppliers; weights `θ` of mass `≥ m` on `Cbar ⊆ V`; a
full-rank structural progression `P` with core inclusion `q + cs·P ⊆ Σ(C₀)`,
`Cbar ∪ C₀ ⊆ V∖{a}` disjointly; step-lattice index bounds `≤ T, ξn`; and the
centre closeness `|T·a − q − z̄| ≤ ε₂·M` — a contradiction follows.  (The
manuscript's parameter regime supplies every threshold.) -/
theorem projective_convexity_assembled {d : ℕ} {β : ℝ} (pkg : Package d β)
    (hd : 1 ≤ d) :
    ∃ cw K : ℝ, 0 < cw ∧ 0 < K ∧
    ∀ (ℓ : (Fin d → ℤ) →+ ℤ) (X : ℕ) (V Cbar C0 : Finset (Fin d → ℤ))
      (M : Fin d → ℕ) (δ γ m cs ε₂ : ℝ) (θ : (Fin d → ℤ) → ℝ)
      (P : GAP d d) (q nq a : Fin d → ℤ) (T ξn : ℕ),
      -- shell block
      1 ≤ X → ShellNonDividing (fun v => ℓ v) X V → a ∈ V →
      a ∈ coordinateBox M →
      -- robust-zonotope block
      UnshiftedIrreducible pkg δ γ V M → Cbar ⊆ V → 0 < γ → 0 ≤ δ →
      (∀ D : Finset (Fin d → ℤ), D ⊆ V → δ * (V.card : ℝ) ≤ (D.card : ℝ) →
        ∃ hE : Eligible β pkg.m₀ D M,
          1 ≤ External.structureScale D.card ∧
          1 ≤ pkg.c * External.structureScale D.card ∧
          K < External.structureScale D.card * γ) →
      (∀ v ∈ Cbar, 0 ≤ θ v) → (∀ v ∈ Cbar, θ v ≤ 1 / 2) →
      m ≤ ∑ v ∈ Cbar, θ v →
      0 < m - 2 * (δ * (V.card : ℝ)) → 0 ≤ ε₂ →
      ((ξn : ℝ) + ε₂) ≤ (cw * γ) * (m - 2 * (δ * (V.card : ℝ))) →
      -- filling block
      P.realRank = d → Cbar ⊆ P.carrier → 0 ≤ cs →
      Real.sqrt (d * (Cbar.card + 1)) * 3 ≤ cs / 2 →
      (∀ w ∈ P.dilatedCarrier cs, q + w ∈ subsetSums C0) →
      Disjoint Cbar C0 → Cbar ∪ C0 ⊆ V.erase a →
      P.evalHom nq = q →
      -- index/order block
      (LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index ≤ T →
      (LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup.index ≤ ξn →
      -- centre closeness
      (∀ i, |(((T • a - q) i : ℤ) : ℝ) - ∑ v ∈ Cbar, θ v * (v i : ℝ)|
        ≤ ε₂ * (M i : ℝ)) →
      False := by
  obtain ⟨cw, K, hcw, hK, htubeincl⟩ := tube_inclusion pkg hd
  refine ⟨cw, K, hcw, hK, ?_⟩
  intro ℓ X V Cbar C0 M δ γ m cs ε₂ θ P q nq a T ξn
    hX hV haV haM hirr hCbarV hγ hδ hsupply hθ0 hθhalf hmass hgap hε₂ hεκ
    hrank hCbarP hcs hthr hcore hdisj hsub hq hidxT hidxξ hcentre
  set L : AddSubgroup (Fin d → ℤ) :=
    (LinearMap.range P.evalHom.toIntLinearMap).toAddSubgroup with hL
  have hinj : Function.Injective P.evalHom := evalHom_injective P hrank
  have hne : L.index ≠ 0 := stepLattice_index_ne_zero P hrank hinj
  haveI hfin : Finite ((Fin d → ℤ) ⧸ L) :=
    stepLattice_finite_quotient P hrank hinj
  -- The element order is bounded by the index, hence by `T` and `ξn`.
  have hrT : addOrderOf (QuotientAddGroup.mk a : (Fin d → ℤ) ⧸ L) ≤ T :=
    (addOrderOf_quotient_le_index L hne a).trans hidxT
  have hrξ : addOrderOf (QuotientAddGroup.mk a : (Fin d → ℤ) ⧸ L) ≤ ξn :=
    (addOrderOf_quotient_le_index L hne a).trans hidxξ
  -- The tube: lattice points near `T·a` are subset sums of `V∖{a}`.
  have htube : ∀ y ∈ L, y - T • a ∈ coordinateBox (fun i => ξn * M i) →
      y ∈ subsetSums (V.erase a) := by
    intro y hyL hybox
    obtain ⟨ny, hny⟩ := hyL
    have hclose := tube_closeness_of_box (Ta := T • a) hybox hcentre
    exact htubeincl V Cbar (V.erase a) C0 M δ γ m ((ξn : ℝ) + ε₂) cs θ P q
      hirr hCbarV hγ hδ hsupply hθ0 hθhalf hmass hgap hεκ
      hrank hCbarP hcs hthr hcore hdisj hsub y ny nq hny hq hclose
  exact projective_convexity_of_tube ℓ hX hV haV L haM hrT hrξ htube

end Nondividing
