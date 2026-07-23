import Nondividing.Box
import Nondividing.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

open scoped BigOperators

namespace Nondividing

structure GAP (d e : ℕ) where
  step : Fin e → (Fin d → ℤ)
  radius : Fin e → ℕ
  radius_pos : ∀ i, 0 < radius i

namespace GAP

variable {d e : ℕ} (P : GAP d e)

def coeffBox : Finset (Fin e → ℤ) :=
  coordinateBox P.radius

def evalHom : (Fin e → ℤ) →+ (Fin d → ℤ) where
  toFun n j := ∑ i, n i * P.step i j
  map_zero' := by
    funext j
    simp
  map_add' n m := by
    funext j
    simp [add_mul, Finset.sum_add_distrib]

@[simp] theorem evalHom_apply (n : Fin e → ℤ) (j : Fin d) :
    P.evalHom n j = ∑ i, n i * P.step i j := rfl

/-- `evalHom` sends the `i`-th standard coefficient vector to the `i`-th step:
the steps are the columns of the coefficient map. -/
@[simp] theorem evalHom_single (i : Fin e) :
    P.evalHom (Pi.single i 1) = P.step i := by
  funext j
  rw [evalHom_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
  · intro k _ hk; rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

noncomputable def carrier : Finset (Fin d → ℤ) := by
  classical
  exact P.coeffBox.image P.evalHom

@[simp] theorem mem_carrier {v : Fin d → ℤ} :
    v ∈ P.carrier ↔ ∃ n ∈ P.coeffBox, P.evalHom n = v := by
  classical
  simp [carrier]

def Proper : Prop :=
  Set.InjOn P.evalHom (P.coeffBox : Set (Fin e → ℤ))

noncomputable def dilatedRadius (t : ℝ) : Fin e → ℕ :=
  fun i => ⌊t * (P.radius i : ℝ)⌋₊

noncomputable def dilatedCoeffBox (t : ℝ) : Finset (Fin e → ℤ) :=
  coordinateBox (P.dilatedRadius t)

noncomputable def dilatedCarrier (t : ℝ) : Finset (Fin d → ℤ) := by
  classical
  exact (P.dilatedCoeffBox t).image P.evalHom

def natDilatedCoeffBox (k : ℕ) : Finset (Fin e → ℤ) :=
  coordinateBox fun i => k * P.radius i

noncomputable def natDilatedCarrier (k : ℕ) : Finset (Fin d → ℤ) := by
  classical
  exact (P.natDilatedCoeffBox k).image P.evalHom

@[simp] theorem mem_dilatedCarrier {t : ℝ} {v : Fin d → ℤ} :
    v ∈ P.dilatedCarrier t ↔
      ∃ n ∈ P.dilatedCoeffBox t, P.evalHom n = v := by
  classical
  simp [dilatedCarrier]

@[simp] theorem mem_natDilatedCarrier {k : ℕ} {v : Fin d → ℤ} :
    v ∈ P.natDilatedCarrier k ↔
      ∃ n ∈ P.natDilatedCoeffBox k, P.evalHom n = v := by
  classical
  simp [natDilatedCarrier]

theorem card_carrier_of_proper (hP : P.Proper) :
    P.carrier.card = P.coeffBox.card := by
  classical
  rw [carrier, Finset.card_image_iff.mpr]
  exact fun x hx y hy hxy => hP hx hy hxy

theorem card_dilatedCarrier_of_injOn (t : ℝ)
    (hP : Set.InjOn P.evalHom
      (P.dilatedCoeffBox t : Set (Fin e → ℤ))) :
    (P.dilatedCarrier t).card = (P.dilatedCoeffBox t).card := by
  classical
  rw [dilatedCarrier, Finset.card_image_iff.mpr]
  exact fun x hx y hy hxy => hP hx hy hxy

theorem dilatedRadius_mono {a b : ℝ} (hab : a ≤ b) (i : Fin e) :
    P.dilatedRadius a i ≤ P.dilatedRadius b i := by
  rw [dilatedRadius, dilatedRadius]
  exact Nat.floor_mono (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))

/-- The real-scale dilate is monotone: `a ≤ b ⟹ aP ⊆ bP`.  Used to place the
`3√(d(|C̄|+1))`-rounding error inside the `(cs/2)`-dilate. -/
theorem dilatedCarrier_mono {a b : ℝ} (hab : a ≤ b) :
    P.dilatedCarrier a ⊆ P.dilatedCarrier b := by
  intro v hv
  rw [mem_dilatedCarrier] at hv ⊢
  obtain ⟨n, hn, rfl⟩ := hv
  refine ⟨n, ?_, rfl⟩
  rw [dilatedCoeffBox, mem_coordinateBox] at hn ⊢
  intro i
  have h := hn i
  have hmono : (P.dilatedRadius a i : ℤ) ≤ P.dilatedRadius b i := by
    exact_mod_cast P.dilatedRadius_mono hab i
  omega

/-- Coefficientwise addition in a symmetric GAP: the `a`-dilate plus the
`b`-dilate lands in the `(a+b)`-dilate.  This is the "coefficientwise addition in
the symmetric GAP" step of `lem:one-sided-filling` (error `+ t ∈ q + csP`). -/
theorem add_mem_dilatedCarrier {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {u v : Fin d → ℤ} (hu : u ∈ P.dilatedCarrier a) (hv : v ∈ P.dilatedCarrier b) :
    u + v ∈ P.dilatedCarrier (a + b) := by
  obtain ⟨nu, hnu, rfl⟩ := (P.mem_dilatedCarrier).mp hu
  obtain ⟨nv, hnv, rfl⟩ := (P.mem_dilatedCarrier).mp hv
  rw [← map_add, P.mem_dilatedCarrier]
  refine ⟨nu + nv, ?_, rfl⟩
  rw [dilatedCoeffBox, mem_coordinateBox] at hnu hnv ⊢
  intro i
  have hfl : (P.dilatedRadius a i : ℤ) + P.dilatedRadius b i
      ≤ P.dilatedRadius (a + b) i := by
    have hnat : P.dilatedRadius a i + P.dilatedRadius b i
        ≤ P.dilatedRadius (a + b) i := by
      rw [dilatedRadius, dilatedRadius, dilatedRadius]
      apply Nat.le_floor
      push_cast
      have h1 : (⌊a * (P.radius i : ℝ)⌋₊ : ℝ) ≤ a * P.radius i :=
        Nat.floor_le (by positivity)
      have h2 : (⌊b * (P.radius i : ℝ)⌋₊ : ℝ) ≤ b * P.radius i :=
        Nat.floor_le (by positivity)
      nlinarith
    exact_mod_cast hnat
  have hui := hnu i
  have hvi := hnv i
  have hadd : (nu + nv) i = nu i + nv i := rfl
  rw [hadd]
  omega

theorem natDilatedCoeffBox_mono {k l : ℕ} (hkl : k ≤ l) :
    P.natDilatedCoeffBox k ⊆ P.natDilatedCoeffBox l := by
  intro n hn
  rw [natDilatedCoeffBox, mem_coordinateBox] at hn ⊢
  intro i
  constructor
  · have hmul : k * P.radius i ≤ l * P.radius i :=
      Nat.mul_le_mul_right (P.radius i) hkl
    have hneg :
        -((l * P.radius i : ℕ) : ℤ) ≤
          -((k * P.radius i : ℕ) : ℤ) := by
      exact neg_le_neg (by exact_mod_cast hmul)
    exact hneg.trans (hn i).1
  · exact (hn i).2.trans (by
      exact_mod_cast Nat.mul_le_mul_right (P.radius i) hkl)

theorem natDilatedCarrier_mono {k l : ℕ} (hkl : k ≤ l) :
    P.natDilatedCarrier k ⊆ P.natDilatedCarrier l := by
  intro v hv
  rw [mem_natDilatedCarrier] at hv ⊢
  obtain ⟨n, hn, rfl⟩ := hv
  exact ⟨n, P.natDilatedCoeffBox_mono hkl hn, rfl⟩

@[simp] theorem card_natDilatedCoeffBox (k : ℕ) :
    (P.natDilatedCoeffBox k).card =
      ∏ i : Fin e, (2 * (k * P.radius i) + 1) := by
  exact card_coordinateBox _

/-- The real rank of the displayed steps; this is deliberately separate from `e`. -/
noncomputable def realRank : ℕ :=
  Module.finrank ℝ
    (Submodule.span ℝ
      (Set.range fun i : Fin e => (fun j : Fin d => (P.step i j : ℝ))))

noncomputable def coeffOf (v : {v // v ∈ P.carrier}) : Fin e → ℤ :=
  Classical.choose ((mem_carrier (P := P)).mp v.property)

theorem coeffOf_mem (v : {v // v ∈ P.carrier}) :
    P.coeffOf v ∈ P.coeffBox :=
  (Classical.choose_spec ((mem_carrier (P := P)).mp v.property)).1

theorem eval_coeffOf (v : {v // v ∈ P.carrier}) :
    P.evalHom (P.coeffOf v) = v :=
  (Classical.choose_spec ((mem_carrier (P := P)).mp v.property)).2

theorem coeffOf_eq_of_eval_eq (hP : P.Proper)
    (v : {v // v ∈ P.carrier}) {n : Fin e → ℤ}
    (hn : n ∈ P.coeffBox) (heval : P.evalHom n = v) :
    P.coeffOf v = n :=
  hP (P.coeffOf_mem v) hn ((P.eval_coeffOf v).trans heval.symm)

theorem eval_coeff_subset_sum (S : Finset {v // v ∈ P.carrier}) :
    P.evalHom (∑ v ∈ S, P.coeffOf v) =
      ∑ v ∈ S, (v.1 : Fin d → ℤ) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _hv
  exact P.eval_coeffOf v

theorem coeff_sum_mem_natDilatedCoeffBox
    (S : Finset {v // v ∈ P.carrier}) :
    (∑ v ∈ S, P.coeffOf v) ∈ P.natDilatedCoeffBox S.card := by
  rw [natDilatedCoeffBox, mem_coordinateBox]
  intro i
  have hbounds (v : {v // v ∈ P.carrier}) (hv : v ∈ S) :
      -(P.radius i : ℤ) ≤ P.coeffOf v i ∧
        P.coeffOf v i ≤ P.radius i := by
    exact (mem_coordinateBox.mp (P.coeffOf_mem v)) i
  constructor
  · calc
      -((S.card * P.radius i : ℕ) : ℤ) =
          ∑ v ∈ S, -(P.radius i : ℤ) := by
            simp
      _ ≤ ∑ v ∈ S, P.coeffOf v i := by
            exact Finset.sum_le_sum fun v hv => (hbounds v hv).1
      _ = (∑ v ∈ S, P.coeffOf v) i := by
            simp
  · calc
      (∑ v ∈ S, P.coeffOf v) i =
          ∑ v ∈ S, P.coeffOf v i := by simp
      _ ≤ ∑ v ∈ S, (P.radius i : ℤ) := by
            exact Finset.sum_le_sum fun v hv => (hbounds v hv).2
      _ = ((S.card * P.radius i : ℕ) : ℤ) := by
            simp

theorem subset_sum_mem_natDilatedCarrier
    (S : Finset {v // v ∈ P.carrier}) :
    ∑ v ∈ S, (v.1 : Fin d → ℤ) ∈ P.natDilatedCarrier S.card := by
  rw [mem_natDilatedCarrier]
  exact ⟨∑ v ∈ S, P.coeffOf v,
    P.coeff_sum_mem_natDilatedCoeffBox S, P.eval_coeff_subset_sum S⟩

theorem ambient_sum_mem_natDilatedCarrier
    (S : Finset (Fin d → ℤ)) (hS : S ⊆ P.carrier) :
    ∑ v ∈ S, v ∈ P.natDilatedCarrier S.card := by
  let f : {v // v ∈ S} ↪ {v // v ∈ P.carrier} :=
    ⟨fun v => ⟨v.1, hS v.2⟩,
      fun x y h => Subtype.ext
        (congrArg (fun z : {v // v ∈ P.carrier} => z.1) h)⟩
  let T : Finset {v // v ∈ P.carrier} := S.attach.map f
  have hcard : T.card = S.card := by
    simp [T]
  have hsum :
      ∑ v ∈ T, (v.1 : Fin d → ℤ) = ∑ v ∈ S, v := by
    simpa [T, f] using
      (Finset.sum_attach S (fun v : Fin d → ℤ => v))
  rw [← hcard, ← hsum]
  exact P.subset_sum_mem_natDilatedCarrier T

theorem subsetSums_subset_natDilatedCarrier
    (A : Finset (Fin d → ℤ)) (hA : A ⊆ P.carrier) :
    subsetSums A ⊆ P.natDilatedCarrier A.card := by
  intro v hv
  obtain ⟨S, hSA, rfl⟩ := mem_subsetSums.mp hv
  exact P.natDilatedCarrier_mono (Finset.card_le_card hSA)
    (P.ambient_sum_mem_natDilatedCarrier S (hSA.trans hA))

theorem card_natDilatedCarrier_le (k : ℕ) :
    (P.natDilatedCarrier k).card ≤ (P.natDilatedCoeffBox k).card := by
  classical
  exact Finset.card_image_le

theorem card_natDilatedCarrier_le_mul (hP : P.Proper) (k : ℕ) :
    (P.natDilatedCarrier k).card ≤
      (2 * k + 1) ^ e * P.carrier.card := by
  rw [P.card_carrier_of_proper hP, coeffBox, card_coordinateBox]
  calc
    (P.natDilatedCarrier k).card ≤
        (P.natDilatedCoeffBox k).card :=
      P.card_natDilatedCarrier_le k
    _ = ∏ i : Fin e, (2 * (k * P.radius i) + 1) :=
      P.card_natDilatedCoeffBox k
    _ ≤
        ∏ i : Fin e, ((2 * k + 1) * (2 * P.radius i + 1)) := by
          exact Finset.prod_le_prod' (fun i _ => by nlinarith [P.radius_pos i])
    _ = (2 * k + 1) ^ e *
        ∏ i : Fin e, (2 * P.radius i + 1) := by
          rw [Finset.prod_mul_distrib]
          simp

theorem scale_card_carrier_le_natDilated (hP : P.Proper) (k : ℕ)
    (hNat : Set.InjOn P.evalHom
      (P.natDilatedCoeffBox k : Set (Fin e → ℤ))) :
    k ^ e * P.carrier.card ≤
      3 ^ e * (P.natDilatedCarrier k).card := by
  rw [P.card_carrier_of_proper hP, coeffBox, card_coordinateBox]
  have hcard :
      (P.natDilatedCarrier k).card =
        ∏ i : Fin e, (2 * (k * P.radius i) + 1) := by
    rw [natDilatedCarrier, Finset.card_image_iff.mpr]
    · exact P.card_natDilatedCoeffBox k
    · exact fun x hx y hy hxy => hNat hx hy hxy
  rw [hcard]
  calc
    k ^ e * ∏ i : Fin e, (2 * P.radius i + 1) =
        ∏ i : Fin e, (k * (2 * P.radius i + 1)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
    _ ≤ ∏ i : Fin e, (3 * (2 * (k * P.radius i) + 1)) := by
          exact Finset.prod_le_prod' fun i _ => by nlinarith [P.radius_pos i]
    _ = 3 ^ e * ∏ i : Fin e, (2 * (k * P.radius i) + 1) := by
          rw [Finset.prod_mul_distrib]
          simp

/-- Lower bound: `2^e·∏Nᵢ ≤ |P|` for a proper GAP (each `2Nᵢ ≤ 2Nᵢ+1`).  This is
the `|P| ≍ 2^d∏Nᵢ` comparison of `lem:index-bound` (needed to relate `|P|` to
the parallelepiped volume `2^d|det M|∏Nᵢ`). -/
theorem two_pow_mul_prod_radius_le_card (hP : P.Proper) :
    2 ^ e * ∏ i : Fin e, P.radius i ≤ P.carrier.card := by
  rw [P.card_carrier_of_proper hP, coeffBox, card_coordinateBox]
  calc 2 ^ e * ∏ i : Fin e, P.radius i
      = ∏ i : Fin e, (2 * P.radius i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i : Fin e, (2 * P.radius i + 1) :=
        Finset.prod_le_prod' fun i _ => by omega

/-- Upper bound: `|P| ≤ 3^e·∏Nᵢ` for a proper GAP (each `2Nᵢ+1 ≤ 3Nᵢ` since
`Nᵢ ≥ 1`).  The other half of the `|P| ≍ 2^d∏Nᵢ` comparison. -/
theorem card_le_three_pow_mul_prod_radius (hP : P.Proper) :
    P.carrier.card ≤ 3 ^ e * ∏ i : Fin e, P.radius i := by
  rw [P.card_carrier_of_proper hP, coeffBox, card_coordinateBox]
  calc ∏ i : Fin e, (2 * P.radius i + 1)
      ≤ ∏ i : Fin e, (3 * P.radius i) :=
        Finset.prod_le_prod' fun i _ => by nlinarith [P.radius_pos i]
    _ = 3 ^ e * ∏ i : Fin e, P.radius i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GAP

end Nondividing
