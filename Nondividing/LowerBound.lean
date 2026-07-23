import Nondividing.Asymptotic
import Nondividing.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Nondividing

/-- The integer version used by the manuscript's translation argument. -/
def NonDividingInt (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℤ, S.Nonempty → S ⊆ A.erase a →
    ¬a ∣ ∑ s ∈ S, s

def natCastEmbedding : ℕ ↪ ℤ where
  toFun n := n
  inj' _ _ := Int.ofNat.inj

@[simp] theorem natCastEmbedding_apply (n : ℕ) : natCastEmbedding n = (n : ℤ) := rfl

theorem nonDividing_of_cast {A : Finset ℕ}
    (hA : NonDividingInt (A.map natCastEmbedding)) :
    NonDividing A := by
  intro a ha S hS hSA hdvd
  apply hA (a : ℤ) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
    (S.map natCastEmbedding)
  · exact Finset.Nonempty.map hS
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hz
    have hserase := hSA hs
    simpa [natCastEmbedding] using hserase
  · obtain ⟨k, hk⟩ := hdvd
    refine ⟨(k : ℤ), ?_⟩
    simp only [Finset.sum_map, natCastEmbedding]
    change (∑ n ∈ S, (n : ℤ)) = (a : ℤ) * (k : ℤ)
    rw [← Nat.cast_sum]
    exact_mod_cast hk

def addEquiv (x : ℤ) : ℤ ≃ ℤ where
  toFun b := x + b
  invFun a := a - x
  left_inv b := by simp
  right_inv a := by simp

def translate (x : ℤ) (B : Finset ℤ) : Finset ℤ :=
  B.map (addEquiv x).toEmbedding

/-- A convenient exact definition of the diameter of a finite integer set. -/
noncomputable def intDiameter (B : Finset ℤ) : ℕ :=
  (B ×ˢ B).sup fun p => (p.1 - p.2).natAbs

theorem natAbs_sub_le_diameter {B : Finset ℤ} {b c : ℤ}
    (hb : b ∈ B) (hc : c ∈ B) :
    (b - c).natAbs ≤ intDiameter B := by
  unfold intDiameter
  exact Finset.le_sup (f := fun p : ℤ × ℤ => (p.1 - p.2).natAbs)
    (show (b, c) ∈ B ×ˢ B by simp [hb, hc])

private theorem eq_zero_of_dvd_of_natAbs_lt {a r : ℤ}
    (hdvd : a ∣ r) (hlt : r.natAbs < a.natAbs) : r = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  by_cases hk : k = 0
  · simp [hk]
  · rw [Int.natAbs_mul] at hlt
    have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
    exact (Nat.not_lt_of_ge (Nat.le_mul_of_pos_right a.natAbs hkpos) hlt).elim

theorem nonDividingInt_of_nonAveraging_of_diameter
    {A : Finset ℤ} {D : ℕ}
    (hna : NonAveraging A)
    (hdiam : ∀ a ∈ A, ∀ b ∈ A, (a - b).natAbs ≤ D)
    (hlarge : ∀ a ∈ A, A.card * D < a.natAbs) :
    NonDividingInt A := by
  intro a ha S hS hSA hdvd
  let R : ℤ := ∑ s ∈ S, (s - a)
  have hRdvd : a ∣ R := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k - S.card, ?_⟩
    simp [R, Finset.sum_sub_distrib, hk]
    ring
  have hRle : R.natAbs ≤ S.card * D := by
    calc
      R.natAbs ≤ ∑ s ∈ S, (s - a).natAbs := by
        simpa [R] using Int.natAbs_sum_le S (fun s => s - a)
      _ ≤ ∑ _s ∈ S, D := by
        apply Finset.sum_le_sum
        intro s hs
        exact hdiam s (Finset.mem_erase.mp (hSA hs)).2 a ha
      _ = S.card * D := by simp
  have hcard : S.card ≤ A.card :=
    Finset.card_le_card (hSA.trans (Finset.erase_subset a A))
  have hRlt : R.natAbs < a.natAbs :=
    lt_of_le_of_lt (hRle.trans (Nat.mul_le_mul_right D hcard)) (hlarge a ha)
  have hRzero := eq_zero_of_dvd_of_natAbs_lt hRdvd hRlt
  apply hna a ha S hS hSA
  have : (∑ s ∈ S, s) - (S.card : ℤ) * a = 0 := by
    simpa [R, Finset.sum_sub_distrib] using hRzero
  exact sub_eq_zero.mp this

theorem nonAveraging_translate {B : Finset ℤ} (x : ℤ)
    (hB : NonAveraging B) :
    NonAveraging (translate x B) := by
  intro a ha S hS hSA
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
  let T := S.map (addEquiv x).symm.toEmbedding
  have hT : T.Nonempty := by
    exact Finset.Nonempty.map hS
  have hTB : T ⊆ B.erase b := by
    intro t ht
    have hxt : addEquiv x t ∈ S := by
      simpa [T] using ht
    have hxerase := hSA hxt
    simpa [translate] using hxerase
  intro hsum
  apply hB b hb T hT hTB
  have hmap : T.map (addEquiv x).toEmbedding = S := by
    ext y
    simp [T]
  rw [← hmap] at hsum
  simp only [Finset.sum_map, Finset.card_map] at hsum
  change (∑ t ∈ T, (x + t)) = (T.card : ℤ) * (x + b) at hsum
  calc
    ∑ t ∈ T, t = (∑ t ∈ T, (x + t)) - (T.card : ℤ) * x := by
      rw [Finset.sum_add_distrib]
      simp
    _ = (T.card : ℤ) * (x + b) - (T.card : ℤ) * x := by rw [hsum]
    _ = (T.card : ℤ) * b := by ring

theorem nonAveraging_map_of_indexed
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (e : ι ↪ ℤ)
    (h : ∀ j ∈ I, ∀ T : Finset ι, T.Nonempty → T ⊆ I.erase j →
      ∑ i ∈ T, e i ≠ T.card * e j) :
    NonAveraging (I.map e) := by
  intro a ha S hS hSA
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
  let T := S.preimage e e.injective.injOn
  have hmap : T.map e = S := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_preimage.mp hi
    · intro hz
      have hzI : z ∈ I.map e :=
        (Finset.erase_subset (e j) (I.map e)) (hSA hz)
      obtain ⟨i, hi, hiz⟩ := Finset.mem_map.mp hzI
      subst z
      exact Finset.mem_map.mpr ⟨i, Finset.mem_preimage.mpr hz, rfl⟩
  have hT : T.Nonempty := by
    rw [← hmap] at hS
    simpa using hS
  have hTI : T ⊆ I.erase j := by
    intro i hi
    have hei : e i ∈ S := Finset.mem_preimage.mp hi
    have := hSA hei
    simpa using this
  intro hsum
  apply h j hj T hT hTI
  rw [← hmap] at hsum
  simpa using hsum

theorem translation_pointwise
    {B : Finset ℤ} (x : ℤ)
    (hna : NonAveraging B)
    (hlarge : ∀ b ∈ B, B.card * intDiameter B < (x + b).natAbs) :
    NonDividingInt (translate x B) := by
  apply nonDividingInt_of_nonAveraging_of_diameter
    (nonAveraging_translate x hna)
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    simpa [addEquiv] using natAbs_sub_le_diameter ha' hb'
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    simpa [translate, addEquiv] using hlarge b hb

/-- Lemma 2.1 (`lem:translation`) of the manuscript, with its diameter made
explicit as `intDiameter`. -/
theorem translation_lemma
    {B : Finset ℤ} (hBne : B.Nonempty) (hna : NonAveraging B) {x : ℤ}
    (hx : (B.card * intDiameter B : ℕ) <
      x + B.inf' hBne (fun b => b)) :
    NonDividingInt (translate x B) := by
  apply translation_pointwise x hna
  intro b hb
  have hmin : B.inf' hBne (fun b => b) ≤ b :=
    Finset.inf'_le (fun b : ℤ => b) hb
  have hcast :
      ((B.card * intDiameter B : ℕ) : ℤ) < x + b :=
    hx.trans_le (by simpa [add_comm] using add_le_add_left hmin x)
  have hpos : 0 ≤ x + b :=
    le_trans (Int.ofNat_nonneg (B.card * intDiameter B))
      (le_of_lt hcast)
  apply Int.ofNat_lt.mp
  rw [Int.natAbs_of_nonneg hpos]
  exact hcast

def parabolaNat (m i : ℕ) : ℕ :=
  (m ^ 3 + 1) * i + i ^ 2

theorem parabolaNat_strictMono (m : ℕ) : StrictMono (parabolaNat m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  simp only [parabolaNat]
  nlinarith [Nat.zero_le (m ^ 3), Nat.zero_le i]

def parabolaEmbedding (m : ℕ) : Fin m ↪ ℤ where
  toFun i := parabolaNat m (i + 1)
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := (parabolaNat_strictMono m).injective (Int.ofNat.inj hij)
    exact Nat.add_right_cancel h

def parabolaSet (m : ℕ) : Finset ℤ :=
  Finset.univ.map (parabolaEmbedding m)

@[simp] theorem parabolaEmbedding_apply (m : ℕ) (i : Fin m) :
    parabolaEmbedding m i = (parabolaNat m ((i : ℕ) + 1) : ℤ) := rfl

@[simp] theorem card_parabolaSet (m : ℕ) : (parabolaSet m).card = m := by
  simp [parabolaSet]

theorem parabolaSet_nonAveraging (m : ℕ) : NonAveraging (parabolaSet m) := by
  apply nonAveraging_map_of_indexed Finset.univ (parabolaEmbedding m)
  intro j _ T hT hTj
  intro havg
  let U : ℕ := ∑ i ∈ T, ((i : ℕ) + 1)
  let A : ℕ := ∑ i ∈ T, ((i : ℕ) + 1) ^ 2
  let B : ℕ := T.card * ((j : ℕ) + 1) ^ 2
  let C : ℕ := m ^ 3 + 1
  have hui (i : Fin m) : (i : ℕ) + 1 ≤ m := Nat.succ_le_iff.mpr i.isLt
  have hcard : T.card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ T)
  have hA : A ≤ m ^ 3 := by
    calc
      A ≤ ∑ _i ∈ T, m ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.pow_le_pow_left (hui i) 2
      _ = T.card * m ^ 2 := by simp
      _ ≤ m * m ^ 2 := Nat.mul_le_mul_right (m ^ 2) hcard
      _ = m ^ 3 := by ring
  have hB : B ≤ m ^ 3 := by
    calc
      B ≤ T.card * m ^ 2 :=
        Nat.mul_le_mul_left T.card (Nat.pow_le_pow_left (hui j) 2)
      _ ≤ m * m ^ 2 := Nat.mul_le_mul_right (m ^ 2) hcard
      _ = m ^ 3 := by ring
  have hformula :
      (∑ i ∈ T, parabolaEmbedding m i) =
        (C : ℤ) * U + (A : ℤ) := by
    simp only [parabolaEmbedding_apply, parabolaNat, C, U, A]
    push_cast
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have heq :
      (C : ℤ) * ((U : ℤ) - (T.card : ℤ) * ((j : ℕ) + 1)) +
        ((A : ℤ) - (B : ℤ)) = 0 := by
    rw [hformula] at havg
    change (C : ℤ) * (U : ℤ) + (A : ℤ) =
      (T.card : ℤ) *
        ((C : ℤ) * (((j : ℕ) + 1 : ℕ) : ℤ) +
          ((((j : ℕ) + 1) ^ 2 : ℕ) : ℤ)) at havg
    dsimp [B]
    push_cast at havg ⊢
    nlinarith
  have hRdvd : (C : ℤ) ∣ (A : ℤ) - (B : ℤ) := by
    refine ⟨-((U : ℤ) - (T.card : ℤ) * ((j : ℕ) + 1)), ?_⟩
    nlinarith [heq]
  have hRle : ((A : ℤ) - (B : ℤ)).natAbs ≤ m ^ 3 :=
    Int.natAbs_coe_sub_coe_le_of_le hA hB
  have hRzero : (A : ℤ) - (B : ℤ) = 0 := by
    apply eq_zero_of_dvd_of_natAbs_lt hRdvd
    have hCabs : (C : ℤ).natAbs = C := by simp
    rw [hCabs]
    exact Nat.lt_succ_of_le hRle
  have hAB : A = B := Int.ofNat.inj (sub_eq_zero.mp hRzero)
  have hU :
      U = T.card * ((j : ℕ) + 1) := by
    have hCpos : (0 : ℤ) < C := by
      exact_mod_cast (Nat.zero_lt_succ (m ^ 3))
    have hL :
        ((U : ℤ) - (T.card : ℤ) * ((j : ℕ) + 1)) = 0 := by
      nlinarith [heq, hRzero]
    exact Int.ofNat.inj (sub_eq_zero.mp hL)
  have hABz :
      (∑ i ∈ T, ((((i : ℕ) + 1) ^ 2 : ℕ) : ℤ)) =
        (T.card : ℤ) * ((((j : ℕ) + 1) ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hAB
  have hUz :
      (∑ i ∈ T, ((((i : ℕ) + 1 : ℕ)) : ℤ)) =
        (T.card : ℤ) * ((((j : ℕ) + 1 : ℕ)) : ℤ) := by
    exact_mod_cast hU
  push_cast at hABz hUz
  have hsq :
      (∑ i ∈ T,
        ((((i : ℕ) + 1 : ℕ) : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ)) ^ 2) = 0 := by
    have hpoint (i : Fin m) :
        ((((i : ℕ) + 1 : ℕ) : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ)) ^ 2 =
          ((((i : ℕ) + 1) ^ 2 : ℕ) : ℤ) -
            (2 * ((((j : ℕ) + 1 : ℕ) : ℤ))) *
              ((((i : ℕ) + 1 : ℕ) : ℤ)) +
            ((((j : ℕ) + 1) ^ 2 : ℕ) : ℤ) := by
      push_cast
      ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    push_cast
    nlinarith [hABz, hUz]
  obtain ⟨i, hi⟩ := hT
  have hij : i ≠ j := (Finset.mem_erase.mp (hTj hi)).1
  have hterm :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_hk : k ∈ T) =>
        sq_nonneg
          (((((k : ℕ) + 1 : ℕ) : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ))))).mp hsq i hi
  have heqij :
      ((((i : ℕ) + 1 : ℕ) : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ)) = 0 :=
    (sq_eq_zero_iff).mp hterm
  apply hij
  apply Fin.ext
  apply Nat.add_right_cancel
  exact Int.ofNat.inj (sub_eq_zero.mp heqij)

def parabolaDelta (m : ℕ) : ℕ :=
  parabolaNat m m - parabolaNat m 1

def lowerValue (m i : ℕ) : ℕ :=
  m * parabolaDelta m + 1 +
    (parabolaNat m i - parabolaNat m 1)

theorem parabola_one_le (m i : ℕ) (hi : 1 ≤ i) :
    parabolaNat m 1 ≤ parabolaNat m i :=
  (parabolaNat_strictMono m).monotone hi

theorem parabola_le_last {m i : ℕ} (hi : i ≤ m) :
    parabolaNat m i ≤ parabolaNat m m :=
  (parabolaNat_strictMono m).monotone hi

def lowerEmbedding (m : ℕ) : Fin m ↪ ℕ where
  toFun i := lowerValue m ((i : ℕ) + 1)
  inj' := by
    intro i j hij
    apply Fin.ext
    have hi1 : parabolaNat m 1 ≤ parabolaNat m ((i : ℕ) + 1) :=
      parabola_one_le m _ (Nat.le_add_left 1 i)
    have hj1 : parabolaNat m 1 ≤ parabolaNat m ((j : ℕ) + 1) :=
      parabola_one_le m _ (Nat.le_add_left 1 j)
    simp only [lowerValue] at hij
    have hsub :
        parabolaNat m ((i : ℕ) + 1) - parabolaNat m 1 =
          parabolaNat m ((j : ℕ) + 1) - parabolaNat m 1 :=
      Nat.add_left_cancel hij
    have hpar :
        parabolaNat m ((i : ℕ) + 1) =
          parabolaNat m ((j : ℕ) + 1) := by
      rw [← Nat.sub_add_cancel hi1, ← Nat.sub_add_cancel hj1, hsub]
    have huv := (parabolaNat_strictMono m).injective hpar
    exact Nat.add_right_cancel huv

def lowerSet (m : ℕ) : Finset ℕ :=
  Finset.univ.map (lowerEmbedding m)

@[simp] theorem lowerEmbedding_apply (m : ℕ) (i : Fin m) :
    lowerEmbedding m i = lowerValue m ((i : ℕ) + 1) := rfl

@[simp] theorem card_lowerSet (m : ℕ) : (lowerSet m).card = m := by
  simp [lowerSet]

def lowerTranslation (m : ℕ) : ℤ :=
  (m * parabolaDelta m : ℕ) - (parabolaNat m 1 : ℤ) + 1

theorem cast_lowerValue {m i : ℕ} (hi : 1 ≤ i) :
    (lowerValue m i : ℤ) =
      lowerTranslation m + (parabolaNat m i : ℤ) := by
  have hbi := parabola_one_le m i hi
  simp only [lowerValue, lowerTranslation]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbi]
  ring

theorem cast_lowerSet (m : ℕ) :
    (lowerSet m).map natCastEmbedding =
      translate (lowerTranslation m) (parabolaSet m) := by
  ext z
  simp only [lowerSet, parabolaSet, translate, Finset.mem_map,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, ⟨i, rfl⟩, rfl⟩
    refine ⟨parabolaEmbedding m i, ⟨i, rfl⟩, ?_⟩
    simpa [natCastEmbedding, addEquiv] using
      (cast_lowerValue (m := m) (i := (i : ℕ) + 1) (Nat.le_add_left 1 i)).symm
  · rintro ⟨b, ⟨i, rfl⟩, rfl⟩
    refine ⟨lowerEmbedding m i, ⟨i, rfl⟩, ?_⟩
    simpa [natCastEmbedding, addEquiv] using
      cast_lowerValue (m := m) (i := (i : ℕ) + 1) (Nat.le_add_left 1 i)

theorem intDiameter_parabolaSet_le (m : ℕ) :
    intDiameter (parabolaSet m) ≤ parabolaDelta m := by
  unfold intDiameter
  apply Finset.sup_le
  intro p hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  obtain ⟨i, _hi, hiEq⟩ := Finset.mem_map.mp ha
  obtain ⟨j, _hj, hjEq⟩ := Finset.mem_map.mp hb
  rw [← hiEq, ← hjEq]
  have hi1 : parabolaNat m 1 ≤ parabolaNat m ((i : ℕ) + 1) :=
    parabola_one_le m _ (Nat.le_add_left 1 i)
  have hj1 : parabolaNat m 1 ≤ parabolaNat m ((j : ℕ) + 1) :=
    parabola_one_le m _ (Nat.le_add_left 1 j)
  have hilast : parabolaNat m ((i : ℕ) + 1) ≤ parabolaNat m m :=
    parabola_le_last (Nat.succ_le_iff.mpr i.isLt)
  have hjlast : parabolaNat m ((j : ℕ) + 1) ≤ parabolaNat m m :=
    parabola_le_last (Nat.succ_le_iff.mpr j.isLt)
  have hiΔ :
      parabolaNat m ((i : ℕ) + 1) - parabolaNat m 1 ≤ parabolaDelta m :=
    Nat.sub_le_sub_right hilast _
  have hjΔ :
      parabolaNat m ((j : ℕ) + 1) - parabolaNat m 1 ≤ parabolaDelta m :=
    Nat.sub_le_sub_right hjlast _
  have heq :
      (parabolaEmbedding m i - parabolaEmbedding m j) =
        ((parabolaNat m ((i : ℕ) + 1) - parabolaNat m 1 : ℕ) : ℤ) -
          ((parabolaNat m ((j : ℕ) + 1) - parabolaNat m 1 : ℕ) : ℤ) := by
    simp only [parabolaEmbedding_apply]
    rw [Nat.cast_sub hi1, Nat.cast_sub hj1]
    ring
  rw [heq]
  exact Int.natAbs_coe_sub_coe_le_of_le hiΔ hjΔ

theorem lowerSet_nonDividing (m : ℕ) : NonDividing (lowerSet m) := by
  apply nonDividing_of_cast
  rw [cast_lowerSet]
  apply translation_pointwise (lowerTranslation m) (parabolaSet_nonAveraging m)
  intro b hb
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hb
  calc
    (parabolaSet m).card * intDiameter (parabolaSet m)
        ≤ m * parabolaDelta m := by
          rw [card_parabolaSet]
          exact Nat.mul_le_mul_left m (intDiameter_parabolaSet_le m)
    _ < lowerValue m ((i : ℕ) + 1) := by
      simp only [lowerValue]
      simpa [add_assoc] using
        Nat.lt_add_of_pos_right
          (a := m * parabolaDelta m)
          (Nat.zero_lt_succ
            (parabolaNat m ((i : ℕ) + 1) - parabolaNat m 1))
    _ = (lowerTranslation m + parabolaEmbedding m i).natAbs := by
      change lowerValue m ((i : ℕ) + 1) =
        (lowerTranslation m + (parabolaNat m ((i : ℕ) + 1) : ℤ)).natAbs
      rw [← cast_lowerValue (m := m) (i := (i : ℕ) + 1)
        (Nat.le_add_left 1 i)]
      simp

theorem parabolaDelta_cast {m : ℕ} (hm : 1 ≤ m) :
    (parabolaDelta m : ℤ) =
      (m : ℤ) ^ 4 - (m : ℤ) ^ 3 + (m : ℤ) ^ 2 + m - 2 := by
  have hb : parabolaNat m 1 ≤ parabolaNat m m :=
    (parabolaNat_strictMono m).monotone hm
  rw [parabolaDelta, Nat.cast_sub hb]
  simp only [parabolaNat]
  push_cast
  ring

theorem translated_max_lt {m : ℕ} (hm : 2 ≤ m) :
    (m + 1) * parabolaDelta m + 1 < 2 * m ^ 5 := by
  apply Int.ofNat_lt.mp
  push_cast
  have hm1 : 1 ≤ m := by omega
  rw [parabolaDelta_cast hm1]
  have hmz : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hcube : (2 : ℤ) * (m : ℤ) ^ 2 ≤ (m : ℤ) ^ 3 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) ^ 2 by positivity)
      (sub_nonneg.mpr hmz)]
  have hcube_fifth : (m : ℤ) ^ 3 ≤ (m : ℤ) ^ 5 := by
    have hmnonneg : (0 : ℤ) ≤ m := by positivity
    have hm2 : (1 : ℤ) ≤ (m : ℤ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) ^ 3 by positivity)
      (sub_nonneg.mpr hm2)]
  nlinarith

theorem lowerSet_subset_Icc {m : ℕ} (hm : 2 ≤ m) :
    lowerSet m ⊆ Finset.Icc 1 (2 * m ^ 5) := by
  intro a ha
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp ha
  rw [Finset.mem_Icc]
  constructor
  · simp only [lowerEmbedding_apply, lowerValue]
    omega
  · have hi1 : parabolaNat m 1 ≤ parabolaNat m ((i : ℕ) + 1) :=
      parabola_one_le m _ (Nat.le_add_left 1 i)
    have hilast : parabolaNat m ((i : ℕ) + 1) ≤ parabolaNat m m :=
      parabola_le_last (Nat.succ_le_iff.mpr i.isLt)
    have hiΔ :
        parabolaNat m ((i : ℕ) + 1) - parabolaNat m 1 ≤ parabolaDelta m :=
      Nat.sub_le_sub_right hilast _
    apply Nat.le_of_lt
    apply lt_of_le_of_lt _ (translated_max_lt hm)
    calc
      lowerEmbedding m i =
          m * parabolaDelta m + 1 +
            (parabolaNat m ((i : ℕ) + 1) - parabolaNat m 1) := rfl
      _ ≤ m * parabolaDelta m + 1 + parabolaDelta m :=
        Nat.add_le_add_left hiΔ _
      _ = (m + 1) * parabolaDelta m + 1 := by ring

/-- Proposition 2.2, finite exact form. -/
theorem lower_construction (m : ℕ) (hm : 2 ≤ m) :
    ∃ A : Finset ℕ, A.card = m ∧
      A ⊆ Finset.Icc 1 (2 * m ^ 5) ∧ NonDividing A :=
  ⟨lowerSet m, card_lowerSet m, lowerSet_subset_Icc hm,
    lowerSet_nonDividing m⟩

theorem lower_F_exact (m : ℕ) (hm : 2 ≤ m) :
    m ≤ F (2 * m ^ 5) := by
  simpa only [card_lowerSet] using
    card_le_F (lowerSet_subset_Icc hm) (lowerSet_nonDividing m)

theorem main_lower_eps :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Real.rpow (N : ℝ) ((1 : ℝ) / 5 - ε) ≤ (F N : ℝ) := by
  intro ε hε
  by_cases ha : 0 < (1 : ℝ) / 5 - ε
  · let a : ℝ := (1 : ℝ) / 5 - ε
    have ha1 : 5 * a < 1 := by
      dsimp [a]
      nlinarith
    have hgrowth :
        ∀ᶠ N : ℕ in Filter.atTop,
          64 * Real.rpow (N : ℝ) (5 * a) ≤ Real.rpow (N : ℝ) 1 :=
      eventually_const_mul_rpow_le_rpow_nat ha1 (by positivity)
    have hrlarge :
        ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ Real.rpow (N : ℝ) a :=
      Filter.tendsto_atTop.1
        ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop) 2
    have hfinal :
        ∀ᶠ N : ℕ in Filter.atTop,
          Real.rpow (N : ℝ) a ≤ (F N : ℝ) := by
      filter_upwards [hgrowth, hrlarge] with N hNgrowth hr
      let m : ℕ := ⌈Real.rpow (N : ℝ) a⌉₊
      have hmcast_low : Real.rpow (N : ℝ) a ≤ (m : ℝ) :=
        Nat.le_ceil _
      have hmcast_high : (m : ℝ) ≤ 2 * Real.rpow (N : ℝ) a := by
        have hceil :
            (m : ℝ) < Real.rpow (N : ℝ) a + 1 :=
          Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) a)
        nlinarith
      have hm : 2 ≤ m := by
        exact_mod_cast hr.trans hmcast_low
      have hpow :
          (2 * m ^ 5 : ℕ) ≤ N := by
        have hpowR : ((2 * m ^ 5 : ℕ) : ℝ) ≤ (N : ℝ) := by
          push_cast
          calc
            (2 : ℝ) * (m : ℝ) ^ 5
                ≤ 2 * (2 * Real.rpow (N : ℝ) a) ^ 5 := by
                  gcongr
            _ = 64 * Real.rpow (N : ℝ) (5 * a) := by
                  have hp :
                      (Real.rpow (N : ℝ) a) ^ 5 =
                        Real.rpow (N : ℝ) (5 * a) := by
                    calc
                      (Real.rpow (N : ℝ) a) ^ 5 =
                          Real.rpow (Real.rpow (N : ℝ) a) (5 : ℝ) :=
                        (Real.rpow_natCast _ 5).symm
                      _ = Real.rpow (N : ℝ) (a * 5) :=
                        (Real.rpow_mul (x := (N : ℝ))
                          (by positivity) a 5).symm
                      _ = Real.rpow (N : ℝ) (5 * a) := by
                        rw [mul_comm a 5]
                  rw [show (2 * Real.rpow (N : ℝ) a) ^ 5 =
                    32 * (Real.rpow (N : ℝ) a) ^ 5 by ring, hp]
                  ring
            _ ≤ Real.rpow (N : ℝ) 1 := hNgrowth
            _ = N := by simp
        exact_mod_cast hpowR
      have hmF : m ≤ F N :=
        (lower_F_exact m hm).trans (F_mono hpow)
      exact hmcast_low.trans (by exact_mod_cast hmF)
    exact Filter.eventually_atTop.1 hfinal
  · have hnonpos : (1 : ℝ) / 5 - ε ≤ 0 := le_of_not_gt ha
    refine ⟨1, ?_⟩
    intro N hN
    calc
      Real.rpow (N : ℝ) ((1 : ℝ) / 5 - ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) hnonpos
      _ ≤ (F N : ℝ) := by exact_mod_cast one_le_F hN

end Nondividing
