import Nondividing.Geometry.CoordProjection
import Nondividing.External.ZonotopeRounding

open scoped BigOperators

namespace Nondividing

/-!
# One-sided filling around a zonotope (Phase D, `lem:one-sided-filling`)

The manuscript rounds a lattice point of the zonotope `Z(C̄)` to a subset sum
using the Conlon–Fox–Pham rounding lemma (E3) *in coefficient space*: for a
full-rank GAP the steps are a ℤ-basis, so the coefficient map ψ is a bijection
onto the step lattice, and all boxes transfer coordinatewise.
-/

/-- Cast compatibility: the real linear combination of the cast steps at cast
integer coefficients is the cast of `evalHom`. -/
theorem realEval_intCast {d e : ℕ} (P : GAP d e) (n : Fin e → ℤ) :
    (Fintype.linearCombination ℝ
        (fun i : Fin e => (fun j : Fin d => (P.step i j : ℝ))))
      (fun i => (n i : ℝ)) = fun j => ((P.evalHom n j : ℤ) : ℝ) := by
  funext j
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, GAP.evalHom_apply]
  push_cast
  rfl

/-- **ψ-transferred zonotope rounding** (core of `lem:one-sided-filling`).
Let `P` be a full-rank GAP, `C̄ ⊆ P.carrier`, and let `w` be a point of the
step lattice whose real image lies in the zonotope `Z(C̄)`.  Then some subset
sum of `C̄` approximates `w` with error in the `3√(e(|C̄|+1))`-dilate of `P`:
the E3 rounding applied in coefficient space, pulled back through ψ. -/
theorem zonotope_rounding_carrier {d e : ℕ} (P : GAP d e) (hrank : P.realRank = e)
    (Cbar : Finset (Fin d → ℤ)) (hC : Cbar ⊆ P.carrier)
    {w : Fin d → ℤ} {nw : Fin e → ℤ} (hnw : P.evalHom nw = w)
    (hz : External.InZonotope Cbar (fun j => (w j : ℝ))) :
    ∃ S : Finset (Fin d → ℤ), S ⊆ Cbar ∧
      w - ∑ v ∈ S, v ∈
        P.dilatedCarrier (Real.sqrt (e * (Cbar.card + 1)) * 3) := by
  classical
  set t : ℝ := Real.sqrt (e * (Cbar.card + 1)) * 3 with ht
  -- Choose coefficient vectors for the elements of `C̄`.
  have hchoice : ∀ c : {x // x ∈ Cbar}, ∃ n ∈ P.coeffBox, P.evalHom n = c.1 :=
    fun c => (GAP.mem_carrier P).mp (hC c.2)
  choose κ hκbox hκeval using hchoice
  have hκinj : Function.Injective κ := by
    intro c c' hcc'
    have : c.1 = c'.1 := by rw [← hκeval c, ← hκeval c', hcc']
    exact Subtype.ext this
  set A : Finset (Fin e → ℤ) := Cbar.attach.image κ with hA
  have hAsub : A ⊆ coordinateBox P.radius := by
    intro a ha
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
    exact hκbox c
  have hAcard : A.card = Cbar.card := by
    rw [hA, Finset.card_image_of_injective _ hκinj, Finset.card_attach]
  -- The zonotope weights transfer through ψ.
  obtain ⟨tt, htt01, httz⟩ := hz
  set t' : (Fin e → ℤ) → ℝ := fun n => tt (P.evalHom n) with ht'
  set ζ : Fin e → ℝ := fun i => ∑ a ∈ A, t' a * (a i : ℝ) with hζ
  have hζzon : External.InZonotope A ζ := by
    refine ⟨t', fun a ha => ?_, rfl⟩
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
    have : t' (κ c) = tt c.1 := by simp only [ht', hκeval c]
    rw [this]
    exact htt01 c.1 c.2
  -- Sums over `A` identify with sums over `C̄`.
  have hsumA : ∀ g : (Fin d → ℤ) → ℝ,
      ∑ a ∈ A, t' a * g (P.evalHom a) = ∑ c ∈ Cbar, tt c * g c := by
    intro g
    rw [hA, Finset.sum_image (fun x _ y _ h => hκinj h)]
    rw [← Finset.sum_attach Cbar (fun c => tt c * g c)]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [ht', hκeval c]
  -- `ζ` is the (real) coefficient vector of `w`, hence integral: `ζ = cast nw`.
  have hζw : ζ = fun i => (nw i : ℝ) := by
    apply realEval_injective P hrank
    rw [realEval_intCast P nw, hnw]
    funext j
    simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hζ]
    have hswap : ∑ i, (∑ a ∈ A, t' a * (a i : ℝ)) * (P.step i j : ℝ)
        = ∑ a ∈ A, t' a * ((P.evalHom a j : ℤ) : ℝ) := by
      calc ∑ i, (∑ a ∈ A, t' a * (a i : ℝ)) * (P.step i j : ℝ)
          = ∑ i, ∑ a ∈ A, t' a * (a i : ℝ) * (P.step i j : ℝ) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
        _ = ∑ a ∈ A, ∑ i, t' a * (a i : ℝ) * (P.step i j : ℝ) :=
            Finset.sum_comm
        _ = ∑ a ∈ A, t' a * ((P.evalHom a j : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [GAP.evalHom_apply]
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    rw [hswap, hsumA (fun c => ((c j : ℤ) : ℝ))]
    have := congrFun httz j
    simpa using this.symm
  -- Apply E3 in coefficient space.
  obtain ⟨S', hS'A, hS'err⟩ := External.zonotope_rounding A P.radius hAsub hζzon
  -- Pull the subset back through ψ.
  refine ⟨S'.image P.evalHom, ?_, ?_⟩
  · intro v hv
    obtain ⟨a, haS', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp (hS'A haS')
    rw [hκeval c]; exact c.2
  · -- The error vector has coefficient vector `m = nw − ∑_{a∈S'} a`.
    have hinj : Function.Injective P.evalHom := evalHom_injective P hrank
    have hsumS : ∑ v ∈ S'.image P.evalHom, v = P.evalHom (∑ a ∈ S', a) := by
      rw [Finset.sum_image (fun x _ y _ h => hinj h), map_sum]
    set m : Fin e → ℤ := nw - ∑ a ∈ S', a with hm
    have hwm : w - ∑ v ∈ S'.image P.evalHom, v = P.evalHom m := by
      rw [hsumS, hm, map_sub, hnw]
    rw [hwm]
    rw [GAP.mem_dilatedCarrier]
    refine ⟨m, ?_, rfl⟩
    rw [GAP.dilatedCoeffBox, mem_coordinateBox]
    intro i
    -- Coordinatewise bound from E3, made integral.
    have herr := hS'err i
    have hζi : ζ i = (nw i : ℝ) := congrFun hζw i
    have hmi : ((m i : ℤ) : ℝ) = ζ i - ∑ a ∈ S', (a i : ℝ) := by
      rw [hζi, hm]
      push_cast
      simp [Finset.sum_apply]
    have hcard : ((A ∪ {0}).card : ℝ) ≤ (Cbar.card : ℝ) + 1 := by
      have h1 : (A ∪ {0}).card ≤ A.card + 1 := by
        calc (A ∪ {0}).card ≤ A.card + ({0} : Finset (Fin e → ℤ)).card :=
              Finset.card_union_le _ _
          _ = A.card + 1 := by rw [Finset.card_singleton]
      rw [← hAcard]
      exact_mod_cast h1
    have hrad1 : (1 : ℝ) ≤ (P.radius i : ℝ) := by
      exact_mod_cast P.radius_pos i
    have hsqrt_le : Real.sqrt (e * (A ∪ {0}).card) ≤
        Real.sqrt (e * (Cbar.card + 1)) := by
      apply Real.sqrt_le_sqrt
      have : ((A ∪ {0}).card : ℝ) ≤ (Cbar.card : ℝ) + 1 := hcard
      nlinarith [Nat.cast_nonneg (α := ℝ) e]
    have hsqrt0 : 0 ≤ Real.sqrt (e * (Cbar.card + 1)) := Real.sqrt_nonneg _
    have hbound : |(m i : ℝ)| ≤ t * (P.radius i : ℝ) := by
      rw [hmi]
      calc |ζ i - ∑ a ∈ S', (a i : ℝ)|
          ≤ Real.sqrt (e * (A ∪ {0}).card) * (2 * P.radius i + 1) := by
            simpa using herr
        _ ≤ Real.sqrt (e * (Cbar.card + 1)) * (3 * P.radius i) := by
            apply mul_le_mul hsqrt_le (by linarith) (by linarith) hsqrt0
        _ = t * (P.radius i : ℝ) := by rw [ht]; ring
    -- Integer bound: `|m i| ≤ ⌊t·radius i⌋₊`.
    have hnatabs : ((m i).natAbs : ℝ) = |(m i : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hfloor : (m i).natAbs ≤ P.dilatedRadius t i := by
      rw [GAP.dilatedRadius]
      apply Nat.le_floor
      rw [hnatabs]
      exact hbound
    have h2 : ((m i).natAbs : ℤ) ≤ (P.dilatedRadius t i : ℤ) := by
      exact_mod_cast hfloor
    omega

/-- **One-sided-filling assembly** (`lem:one-sided-filling`, combinatorial core).
Given a subset sum `z̃` of `C̄`, a rounding error `z − z̃` and a shift `t − q`
each in the `(cs/2)`-dilate of `P`, and the structural core inclusion
`q + (cs)·P ⊆ Σ(C₀)`, the point `z + t` is a subset sum of `C`.  The two halves
add coefficientwise into the full `cs`-dilate, the core turns it into a subset
sum of `C₀`, and disjointness of `C̄`, `C₀` glues the two subset sums. -/
theorem filling_assembly {d e : ℕ} (P : GAP d e)
    {C Cbar C0 : Finset (Fin d → ℤ)} {q z zt t : Fin d → ℤ} {cs : ℝ} (hcs : 0 ≤ cs)
    (hzt : zt ∈ subsetSums Cbar)
    (herr : z - zt ∈ P.dilatedCarrier (cs / 2))
    (hshift : t - q ∈ P.dilatedCarrier (cs / 2))
    (hcore : ∀ w ∈ P.dilatedCarrier cs, q + w ∈ subsetSums C0)
    (hdisj : Disjoint Cbar C0) (hsub : Cbar ∪ C0 ⊆ C) :
    z + t ∈ subsetSums C := by
  have hadd : (z - zt) + (t - q) ∈ P.dilatedCarrier (cs / 2 + cs / 2) :=
    P.add_mem_dilatedCarrier (by linarith) (by linarith) herr hshift
  rw [show cs / 2 + cs / 2 = cs by ring] at hadd
  have hcore' : q + ((z - zt) + (t - q)) ∈ subsetSums C0 := hcore _ hadd
  have heq1 : q + ((z - zt) + (t - q)) = (z - zt) + t := by abel
  rw [heq1] at hcore'
  have hunion : zt + ((z - zt) + t) ∈ subsetSums (Cbar ∪ C0) :=
    add_mem_subsetSums_union hdisj hzt hcore'
  have heq2 : zt + ((z - zt) + t) = z + t := by abel
  rw [heq2] at hunion
  exact subsetSums_mono hsub hunion

/-- **Rounding with a homogeneous core** (`lem:one-sided-filling`).
Let `P` be a full-rank GAP with `C̄ ⊆ P.carrier`, let `C₀` be disjoint from `C̄`
with `C̄ ∪ C₀ ⊆ C`, and suppose the structural core inclusion
`q + (cs)·P ⊆ Σ(C₀)` holds, with the rounding radius `3√(d(|C̄|+1))` at most
`cs/2`.  Then every step-lattice point `z = ψ⁻¹(nz)` whose real image lies in the
zonotope `Z(C̄)`, shifted by any `t ∈ q + (cs/2)·P`, is a subset sum of `C`:
\[ L∩(Z(C̄)+q+\tfrac{cs}{2}P) ⊆ Σ(C). \]
This is the full lemma; the only external input is the E3 rounding used inside
`zonotope_rounding_carrier`. -/
theorem one_sided_filling {d : ℕ} (P : GAP d d) (hrank : P.realRank = d)
    {C Cbar C0 : Finset (Fin d → ℤ)} (hC : Cbar ⊆ P.carrier)
    {q : Fin d → ℤ} {cs : ℝ} (hcs : 0 ≤ cs)
    (hthr : Real.sqrt (d * (Cbar.card + 1)) * 3 ≤ cs / 2)
    (hcore : ∀ w ∈ P.dilatedCarrier cs, q + w ∈ subsetSums C0)
    (hdisj : Disjoint Cbar C0) (hsub : Cbar ∪ C0 ⊆ C)
    {nz : Fin d → ℤ}
    (hzon : External.InZonotope Cbar (fun j => ((P.evalHom nz) j : ℝ)))
    {t : Fin d → ℤ} (ht : t - q ∈ P.dilatedCarrier (cs / 2)) :
    P.evalHom nz + t ∈ subsetSums C := by
  obtain ⟨S, hSsub, herr⟩ :=
    zonotope_rounding_carrier P hrank Cbar hC (nw := nz) rfl hzon
  have hzt : (∑ v ∈ S, v) ∈ subsetSums Cbar :=
    mem_subsetSums.mpr ⟨S, hSsub, rfl⟩
  have herr' : P.evalHom nz - ∑ v ∈ S, v ∈ P.dilatedCarrier (cs / 2) :=
    P.dilatedCarrier_mono hthr herr
  exact filling_assembly P hcs hzt herr' ht hcore hdisj hsub

end Nondividing
