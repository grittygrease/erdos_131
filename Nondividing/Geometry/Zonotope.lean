import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
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

/-- **Zonotope separation** (`lem:robust-zonotope`, separation step): a point
outside the symmetric zonotope admits a linear functional `f` with
`f(y) > ∑_v θ_v·|f(v)|`.  Hahn–Banach separation from the compact convex
zonotope plus the support-function identity. -/
theorem symZonotope_separation {d : ℕ} {C : Finset (Fin d → ℤ)}
    {θ : (Fin d → ℤ) → ℝ} (hθ : ∀ v ∈ C, 0 ≤ θ v) {y : Fin d → ℝ}
    (hy : y ∉ symZonotope C θ) :
    ∃ f : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∑ v ∈ C, θ v * |f (External.realPoint v)|) < f y := by
  classical
  have hclosed : IsClosed (symZonotope C θ) :=
    (symZonotope_isCompact C θ hθ).isClosed
  have hconv : Convex ℝ (symZonotope C θ) := symZonotope_convex C θ
  obtain ⟨f, u, hfu, huy⟩ :=
    geometric_hahn_banach_closed_point hconv hclosed hy
  refine ⟨(f : (Fin d → ℝ) →ₗ[ℝ] ℝ), ?_⟩
  -- The zonotope contains the reflected coefficient choice achieving the
  -- support value; measure it against the separation level `u`.
  set tstar : (Fin d → ℤ) → ℝ :=
    fun v => if 0 ≤ f (External.realPoint v) then θ v else -(θ v) with htstar
  have hxstar : (fun j => ∑ v ∈ C, tstar v * (v j : ℝ)) ∈ symZonotope C θ := by
    refine ⟨tstar, fun v hv => ?_, rfl⟩
    have hθv := hθ v hv
    simp only [htstar]
    by_cases hs : 0 ≤ f (External.realPoint v)
    · rw [if_pos hs, abs_of_nonneg hθv]
    · rw [if_neg hs, abs_neg, abs_of_nonneg hθv]
  have hfx : f (fun j => ∑ v ∈ C, tstar v * (v j : ℝ))
      = ∑ v ∈ C, θ v * |f (External.realPoint v)| := by
    rw [show (fun j => ∑ v ∈ C, tstar v * (v j : ℝ))
        = ∑ v ∈ C, tstar v • External.realPoint v from by
      funext j
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun v _ => by
        simp [External.realPoint, smul_eq_mul]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [map_smul, smul_eq_mul]
    simp only [htstar]
    by_cases hs : 0 ≤ f (External.realPoint v)
    · rw [if_pos hs, abs_of_nonneg hs]
    · push_neg at hs
      rw [if_neg (not_le.mpr hs), abs_of_neg hs]
      ring
  have hsupp := hfu _ hxstar
  rw [hfx] at hsupp
  calc ∑ v ∈ C, θ v * |f (External.realPoint v)| < u := hsupp
    _ < f y := huy

/-- **Robust zonotope, mass-counting core** (`lem:robust-zonotope`).
If the weights have total mass `≥ m`, each `≤ 1/2`, and every thin central slab
(relative width controlled by `κ`) holds fewer than `δn/2` points of `C`, then
the symmetric zonotope `Z⁰` contains the whole box `ε·B_ℝ` as soon as
`ε ≤ κ(m − δn)`.  Proof: separate a missing point `y` by `f`
(`symZonotope_separation`), let `ρ = f(y)/(m−δn)`; the slab `{|f| < ρ}` has
relative width `≤ κ`, so it carries `≤ δn/4` mass, leaving mass `≥ m − δn`
outside, each contributing `≥ ρ`; total `≥ (m−δn)ρ = f(y)`, contradicting the
separation. -/
theorem symZonotope_contains_box_of_slab_bound {d : ℕ}
    {C : Finset (Fin d → ℤ)} {θ : (Fin d → ℤ) → ℝ} {M : Fin d → ℕ}
    (hθ0 : ∀ v ∈ C, 0 ≤ θ v) (hθhalf : ∀ v ∈ C, θ v ≤ 1 / 2)
    {m δn ε κ : ℝ}
    (hmass : m ≤ ∑ v ∈ C, θ v)
    (hgap : 0 < m - δn) (hδn : 0 ≤ δn)
    (hεκ : ε ≤ κ * (m - δn))
    (hslab : ∀ (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (ρ : ℝ), 0 < ρ →
      ρ ≤ κ * (∑ i, |f (Pi.single i (1 : ℝ))| * (M i : ℝ)) →
      2 * ((C.filter
        (fun v => |f (External.realPoint v)| < ρ)).card : ℝ) ≤ δn)
    {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ ε * (M i : ℝ)) :
    y ∈ symZonotope C θ := by
  classical
  by_contra hy'
  obtain ⟨f, hsep⟩ := symZonotope_separation hθ0 hy'
  set z : ℝ := f y with hz
  set w : ℝ := ∑ i, |f (Pi.single i (1 : ℝ))| * (M i : ℝ) with hw
  -- `z > 0` since the support sum is nonnegative.
  have hsum0 : 0 ≤ ∑ v ∈ C, θ v * |f (External.realPoint v)| :=
    Finset.sum_nonneg fun v hv => mul_nonneg (hθ0 v hv) (abs_nonneg _)
  have hz0 : 0 < z := lt_of_le_of_lt hsum0 hsep
  -- `z ≤ ε·w` by expanding `y` along the standard basis.
  have hzεw : z ≤ ε * w := by
    have hydecomp : f y = ∑ i, y i * f (Pi.single i (1 : ℝ)) := by
      conv_lhs => rw [pi_eq_sum_univ' y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    calc z = f y := hz
      _ ≤ |f y| := le_abs_self _
      _ = |∑ i, y i * f (Pi.single i (1 : ℝ))| := by rw [hydecomp]
      _ ≤ ∑ i, |y i * f (Pi.single i (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |y i| * |f (Pi.single i (1 : ℝ))| :=
          Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i, (ε * (M i : ℝ)) * |f (Pi.single i (1 : ℝ))| :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hy i) (abs_nonneg _)
      _ = ε * w := by
          rw [hw, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  -- The slab threshold.
  set ρ : ℝ := z / (m - δn) with hρ
  have hρ0 : 0 < ρ := div_pos hz0 hgap
  have hρκw : ρ ≤ κ * w := by
    rw [hρ, div_le_iff₀ hgap]
    calc z ≤ ε * w := hzεw
      _ ≤ (κ * (m - δn)) * w := by
          have hw0 : 0 ≤ w := by
            rw [hw]
            exact Finset.sum_nonneg fun i _ =>
              mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hεκ hw0
      _ = κ * w * (m - δn) := by ring
  have hcard := hslab f ρ hρ0 hρκw
  -- Split the support sum at the slab.
  set H : Finset (Fin d → ℤ) :=
    C.filter (fun v => |f (External.realPoint v)| < ρ) with hH
  have hsplitθ : ∑ v ∈ C, θ v
      = (∑ v ∈ H, θ v) + ∑ v ∈ C.filter
          (fun v => ¬|f (External.realPoint v)| < ρ), θ v := by
    rw [hH]
    exact (Finset.sum_filter_add_sum_filter_not C _ _).symm
  -- Mass on the slab is at most `δn/4 ≤ δn`.
  have hHmass : ∑ v ∈ H, θ v ≤ δn := by
    calc ∑ v ∈ H, θ v ≤ ∑ _v ∈ H, (1 : ℝ) / 2 :=
          Finset.sum_le_sum fun v hv =>
            hθhalf v (Finset.mem_filter.mp (hH ▸ hv)).1
      _ = (H.card : ℝ) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ δn := by linarith [hcard]
  -- Mass outside the slab is at least `m − δn`, each term `≥ ρ`.
  have houtmass : m - δn ≤ ∑ v ∈ C.filter
      (fun v => ¬|f (External.realPoint v)| < ρ), θ v := by
    have := hsplitθ
    linarith [hmass]
  have hsupport : (m - δn) * ρ ≤ ∑ v ∈ C, θ v * |f (External.realPoint v)| := by
    have hterm : ∀ v ∈ C.filter (fun v => ¬|f (External.realPoint v)| < ρ),
        θ v * ρ ≤ θ v * |f (External.realPoint v)| := by
      intro v hv
      obtain ⟨hvC, hvρ⟩ := Finset.mem_filter.mp hv
      push_neg at hvρ
      exact mul_le_mul_of_nonneg_left hvρ (hθ0 v hvC)
    calc (m - δn) * ρ
        ≤ (∑ v ∈ C.filter (fun v => ¬|f (External.realPoint v)| < ρ), θ v) * ρ :=
          mul_le_mul_of_nonneg_right houtmass (le_of_lt hρ0)
      _ = ∑ v ∈ C.filter (fun v => ¬|f (External.realPoint v)| < ρ), θ v * ρ := by
          rw [Finset.sum_mul]
      _ ≤ ∑ v ∈ C.filter (fun v => ¬|f (External.realPoint v)| < ρ),
            θ v * |f (External.realPoint v)| := Finset.sum_le_sum hterm
      _ ≤ ∑ v ∈ C, θ v * |f (External.realPoint v)| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro v hv _
          exact mul_nonneg (hθ0 v hv) (abs_nonneg _)
  -- Contradiction: `z ≤ (m−δn)ρ = z` beats the separation.
  have hfinal : z ≤ ∑ v ∈ C, θ v * |f (External.realPoint v)| := by
    have : (m - δn) * ρ = z := by
      rw [hρ]
      field_simp
    linarith [hsupport]
  exact absurd hsep (not_lt_of_ge hfinal)

end Nondividing
