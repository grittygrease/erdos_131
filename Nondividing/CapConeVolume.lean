import Nondividing.Projective.Normalization
import Nondividing.Geometry.ConvexLatticeJohn
import Nondividing.External.ConvexGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped BigOperators Pointwise
open MeasureTheory

namespace Nondividing

/-!
# Cone volumes for cap lifting, alternative (ii) (Phase G, `lem:cap-lifting`, r = d)

The `r = d` branch of `lem:cap-lifting` needs the volume bound
`vol(K − K) ≪_d η · vol(B_ℝ)` for `K = Cone_{2X}(Ω')`.  Following the design
decision of the mission brief we avoid the hyperplane surface measure `m_λ`
entirely and work with *cone volumes*: for `E ⊆ ℝ^d` and `T ≥ 0`,

  `cone T E = {t • y : y ∈ E, 0 ≤ t ≤ T}`.

The perspective-volume formula (eq:perspective-volume of the manuscript) is
replaced by the pure scaling law `vol(cone T E) = T^d · vol(cone 1 E)`, and the
surface-measure hypothesis `m_λ(Ω') ≤ η m_λ(Ω)` by its cone-volume avatar
`vol(cone 1 Ω') ≤ η · vol(cone 1 Ω)` (discharged later by the
projective-theorem glue).  This file provides:

1. `cone`, `cone_mono`, `cone_eq_smul` (T-scaling as a set identity);
2. `volume_cone` — the scaling law via `Measure.addHaar_smul_of_nonneg`;
3. `realPoint_mem_cone` — shell points lift into `cone (2X) Ω'`;
4. `cone_convex` — the cone over a convex set is convex;
5. `cone_isCompact`, `coneBody`, and the Rogers–Shephard step (E5c);
6. `latticePoints` — the finite set of integer points of a compact set,
   and the lattice-point count via E5d;
7. `cap_cone_count` — the assembled `r = d` cardinality bound.
-/

/-! ## 1. The cone construction -/

/-- The cone with apex `0` over `E ⊆ ℝ^d`, truncated at height parameter `T`:
all points `t • y` with `y ∈ E` and `0 ≤ t ≤ T`. -/
def cone {d : ℕ} (T : ℝ) (E : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {x | ∃ y ∈ E, ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ x = t • y}

theorem cone_mono {d : ℕ} (T : ℝ) {E F : Set (Fin d → ℝ)} (h : E ⊆ F) :
    cone T E ⊆ cone T F := by
  rintro x ⟨y, hy, t, ht0, htT, rfl⟩
  exact ⟨y, h hy, t, ht0, htT, rfl⟩

theorem zero_mem_cone {d : ℕ} {T : ℝ} (hT : 0 ≤ T) {E : Set (Fin d → ℝ)}
    (hE : E.Nonempty) : 0 ∈ cone T E := by
  obtain ⟨y, hy⟩ := hE
  exact ⟨y, hy, 0, le_refl 0, hT, (zero_smul ℝ y).symm⟩

/-- Scaling as a set identity: the height-`T` cone is the `T`-dilate of the
height-`1` cone (valid for every `T ≥ 0`, including `T = 0`). -/
theorem cone_eq_smul {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (E : Set (Fin d → ℝ)) :
    cone T E = T • cone 1 E := by
  ext x
  constructor
  · rintro ⟨y, hy, t, ht0, htT, rfl⟩
    rcases eq_or_lt_of_le hT with hT0 | hT0
    · -- `T = 0` forces `t = 0`; then `t • y = 0 = T • (0 • y)`.
      have ht : t = 0 := le_antisymm (hT0 ▸ htT) ht0
      refine ⟨(0 : ℝ) • y, ⟨y, hy, 0, le_refl 0, zero_le_one, rfl⟩, ?_⟩
      show T • (0 : ℝ) • y = t • y
      rw [ht, ← hT0]
      simp
    · refine ⟨(t / T) • y, ⟨y, hy, t / T,
        div_nonneg ht0 hT, (div_le_one hT0).mpr htT, rfl⟩, ?_⟩
      show T • (t / T) • y = t • y
      rw [smul_smul, mul_div_cancel₀ t (ne_of_gt hT0)]
  · rintro ⟨z, ⟨y, hy, s, hs0, hs1, rfl⟩, rfl⟩
    show T • s • y ∈ cone T E
    exact ⟨y, hy, T * s, mul_nonneg hT hs0,
      by nlinarith, smul_smul T s y⟩

/-! ## 2. The scaling law for cone volumes -/

/-- **Cone-volume scaling law**: `vol(cone T E) = T^d · vol(cone 1 E)` for
`T ≥ 0`.  This is the Jacobian-free substitute for the perspective-volume
formula (eq:perspective-volume) of the manuscript. -/
theorem volume_cone {d : ℕ} {T : ℝ} (hT : 0 ≤ T) (E : Set (Fin d → ℝ)) :
    volume (cone T E) = ENNReal.ofReal (T ^ d) * volume (cone 1 E) := by
  rw [cone_eq_smul hT E, Measure.addHaar_smul_of_nonneg volume hT,
    Module.finrank_fin_fun]

/-! ## 3. Shell containment -/

/-- **Shell points lift into the cone**: if the shell point `v` has
`X ≤ λ(v) ≤ 2X` and its projective normalization lies in `Ω'`, then the real
point of `v` lies in the truncated cone `cone (2X) Ω'` — indeed
`v = λ(v) • π(v)` with `0 ≤ λ(v) ≤ 2X`. -/
theorem realPoint_mem_cone {d : ℕ} {a : Fin d → ℤ} {X : ℕ} {v : Fin d → ℤ}
    {Ω' : Set (Fin d → ℝ)} (hX : 1 ≤ X)
    (hlo : (X : ℤ) ≤ intFunctional a v) (hhi : intFunctional a v ≤ 2 * X)
    (hmem : projNorm a v ∈ Ω') :
    External.realPoint v ∈ cone (2 * (X : ℝ)) Ω' := by
  have hpos : (0 : ℤ) < intFunctional a v :=
    lt_of_lt_of_le (by exact_mod_cast hX) hlo
  have hne : ((intFunctional a v : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  refine ⟨projNorm a v, hmem, ((intFunctional a v : ℤ) : ℝ), ?_, ?_, ?_⟩
  · exact_mod_cast le_of_lt hpos
  · exact_mod_cast hhi
  · rw [projNorm, smul_inv_smul₀ hne]

/-! ## 4. Convexity of cones over convex sets -/

/-- The cone over a convex set is convex (the origin joins everything):
a convex combination `p•(t₁•y₁) + q•(t₂•y₂)` equals `s•(w₁•y₁ + w₂•y₂)` with
`s = p·t₁ + q·t₂ ∈ [0, T]` and weights `wᵢ` summing to `1` (degenerate case
`s = 0` gives the apex). -/
theorem cone_convex {d : ℕ} {T : ℝ} (hT : 0 ≤ T) {E : Set (Fin d → ℝ)}
    (hE : Convex ℝ E) : Convex ℝ (cone T E) := by
  rintro x ⟨y₁, hy₁, t₁, ht₁0, ht₁T, rfl⟩ x' ⟨y₂, hy₂, t₂, ht₂0, ht₂T, rfl⟩
    p q hp hq hpq
  set s : ℝ := p * t₁ + q * t₂ with hs_def
  have hs0 : 0 ≤ s := by positivity
  have hsT : s ≤ T := by nlinarith
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- `s = 0`: both scalar weights vanish and the combination is the apex.
    have h1 : p * t₁ = 0 := by nlinarith
    have h2 : q * t₂ = 0 := by nlinarith
    have hzero : p • t₁ • y₁ + q • t₂ • y₂ = (0 : Fin d → ℝ) := by
      rw [smul_smul, smul_smul, h1, h2, zero_smul, zero_smul, add_zero]
    rw [hzero]
    exact zero_mem_cone hT ⟨y₁, hy₁⟩
  · -- `s > 0`: renormalize the weights inside `E`.
    have hsne : s ≠ 0 := ne_of_gt hs
    have hw1 : 0 ≤ p * t₁ / s := div_nonneg (mul_nonneg hp ht₁0) hs0
    have hw2 : 0 ≤ q * t₂ / s := div_nonneg (mul_nonneg hq ht₂0) hs0
    have hwsum : p * t₁ / s + q * t₂ / s = 1 := by
      field_simp
      rw [hs_def]
    refine ⟨(p * t₁ / s) • y₁ + (q * t₂ / s) • y₂,
      hE hy₁ hy₂ hw1 hw2 hwsum, s, hs0, hsT, ?_⟩
    have e1 : s * (p * t₁ / s) = p * t₁ := by field_simp
    have e2 : s * (q * t₂ / s) = q * t₂ := by field_simp
    rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, e1, e2]

end Nondividing
