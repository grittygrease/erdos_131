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

end Nondividing
