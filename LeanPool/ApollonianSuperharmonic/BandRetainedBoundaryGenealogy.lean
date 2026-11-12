/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrientedBoundaryParentChain
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandParentBoundaryGenealogy
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction

-- [TABLET NODE: BandRetainedBoundaryGenealogy]

/-!
# BandRetainedBoundaryGenealogy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RetainedBoundaryProof

private theorem curvatureBound :
    ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ i : Fin 4,
        (r i).1 = 0 ∨ (r i).1 = 1 ∨ 4 ≤ (r i).1 := by
  classical
  intro r hr
  induction hr with
  | base z =>
      intro i
      fin_cases i <;> simp
  | @rotate r hr ih =>
      intro i
      fin_cases i <;> simp_all []
  | @successor r hr ih =>
      intro i
      fin_cases i
      · have forest := SemiProperForestClassification r hr
        rcases forest with ⟨nonneg, cases⟩
        rcases cases with root | root | root | old
        · rcases root with ⟨z, hz⟩
          rw [hz]
          simp
        · rcases root with ⟨z, hz⟩
          rw [hz]
          simp
        · rcases root with ⟨z, hz⟩
          rw [hz]
          simp
        · have curv := ProperBandCurvatureStructure r old
          have hpos : 0 < (r 0).1 := curv.1
          have h1 : (r 1).1 < (r 0).1 := old.2 0
          have h2lt : (r 2).1 < (r 0).1 := old.2 1
          have h3lt : (r 3).1 < (r 0).1 := old.2 2
          have h2 : 0 ≤ (r 2).1 := curv.2.1 1
          have h3 : 0 ≤ (r 3).1 := curv.2.1 2
          have hposNew : 0 <
              2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1 := by
            omega
          have hnotone0 : (r 0).1 ≠ 1 := by
            intro hone
            have hz2 : (r 2).1 = 0 := by omega
            have hz3 : (r 3).1 = 0 := by omega
            have e : (1 : Fin 3) = 2 := curv.2.2 1 2 hz2 hz3
            have ev := congrArg Fin.val e
            omega
          have hlarge0 : 4 ≤ (r 0).1 := by
            rcases ih 0 with hz | hone | hlarge
            · omega
            · exact (hnotone0 hone).elim
            · exact hlarge
          have hd : 4 ≤ 2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1 := by
            omega
          exact Or.inr (Or.inr hd)
      · simpa using ih 0
      · simpa using ih 2
      · simpa using ih 3

private theorem buildConfiguration :
    (∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → ∀ i : Fin 4, (r i).1 ≠ 0 → (r i).1
        = 1 ∨ 4 ≤ (r i).1) → (∀ (u : Fin 4 → CircleCoordinates), ∀ (p : Fin 4 →
        CircleCoordinates), ∀ (t : Fin 4 → CircleCoordinates), ProperBandQuadruple u →
      (∀ i : Fin 4, (u i).1 ≠ 0) →
      (∀ i j : Fin 4, (u i).1 = 1 → (u j).1 = 1 → i = j) →
      ProperBandQuadruple p →
      u = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3] →
      p 0 = u 1 → p 2 = u 2 → p 3 = u 3 →
      (u 2).1 < (u 1).1 → (u 3).1 < (u 1).1 →
      ProperBandQuadruple t → t 0 = u 2 → t 1 = u 3 →
      (u 3).1 < (u 2).1 →
      Nonempty (BandOrderedGeneralConfiguration u)) := by
  classical
  intro positiveLarge u p t hu hnl haum hp hs h0 h2 h3 hlt2 hlt3 ht ht0 ht1 horder
  have cu := ProperBandCurvatureStructure u hu
  have cp := ProperBandCurvatureStructure p hp
  have hp1nonneg : 0 ≤ (p 1).1 := by simpa using cp.2.1 0
  have hp2nonneg : 0 ≤ (p 2).1 := by simpa using cp.2.1 1
  have hp3nonneg : 0 ≤ (p 3).1 := by simpa using cp.2.1 2
  have hp3 : 0 < (p 3).1 := by
    have hn : (p 3).1 ≠ 0 := by simpa [h3] using hnl 3
    omega
  have hp2 : 0 < (p 2).1 := by
    have hn : (p 2).1 ≠ 0 := by simpa [h2] using hnl 2
    omega
  have hu0large : 4 < (u 0).1 := by
    have hp0 : 0 < (p 0).1 := by
      have hn : (p 0).1 ≠ 0 := by simpa [h0] using hnl 1
      omega
    have hp1lt : (p 1).1 < (p 0).1 := by simpa using hp.2 0
    have hp2lt : (p 2).1 < (p 0).1 := by simpa using hp.2 1
    have hp3lt : (p 3).1 < (p 0).1 := by simpa using hp.2 2
    have hf := congrArg (fun z : Fin 4 → CircleCoordinates => (z 0).1) hs
    simp at hf
    have hp0c := positiveLarge p hp.1 0 (by omega : (p 0).1 ≠ 0)
    have hp2c := positiveLarge p hp.1 2 (by omega : (p 2).1 ≠ 0)
    have hp3c := positiveLarge p hp.1 3 (by omega : (p 3).1 ≠ 0)
    rcases hp0c with hone | hlarge
    · have hp1z : (p 1).1 = 0 := by omega
      rcases hp2c with hone2 | hlarge2 <;>
        rcases hp3c with hone3 | hlarge3 <;> omega
    · omega
  have hu2large : 4 ≤ (u 2).1 := by
    have hp3lt2 : (p 3).1 < (p 2).1 := by simpa [h2, h3] using horder
    rcases positiveLarge p hp.1 2 (by omega : (p 2).1 ≠ 0) with hone | hlarge
    · omega
    · simpa [h2] using hlarge
  have htwin : p 1 =
      (2 * (u 1).1 + 2 * (u 2).1 + 2 * (u 3).1 - (u 0).1,
        2 * (u 1).2 + 2 * (u 2).2 + 2 * (u 3).2 - (u 0).2) := by
    rw [hs]
    simp [h0, h2, h3]
  have hsmall1 : (p 0).1 < (u 0).1 := by simpa [h0] using hu.2 0
  have hsmall2 : (t 0).1 < (u 0).1 := by
    rw [ht0]
    exact hu.2 1
  have hsoddy :
      2 * (u 1).1 + 2 * (u 2).1 + 2 * (u 3).1 =
        (u 0).1 + (p 1).1 := by
    have hf := congrArg Prod.fst htwin
    omega
  refine ⟨⟨hu, hnl, haum, hu0large, hlt2, hu2large, le_of_lt horder,
    p, t, hp, ht, h0, htwin, h2, h3, ht0, ht1, hsmall1,
    hsmall2, hsoddy, ?_, ?_, ?_, ?_⟩⟩
  · have n0 : ((u 0).1.toNat : Int) = (u 0).1 :=
      Int.toNat_of_nonneg (le_of_lt cu.1)
    have n1 : ((u 1).1.toNat : Int) = (u 1).1 :=
      Int.toNat_of_nonneg (by simpa using cu.2.1 0)
    have n2 : ((u 2).1.toNat : Int) = (u 2).1 :=
      Int.toNat_of_nonneg (by simpa using cu.2.1 1)
    have n3 : ((u 3).1.toNat : Int) = (u 3).1 :=
      Int.toNat_of_nonneg (by simpa using cu.2.1 2)
    have np : ((p 1).1.toNat : Int) = (p 1).1 :=
      Int.toNat_of_nonneg (by simpa using cp.2.1 0)
    omega
  · simp [h0, h2]
  · simp [h0, h3]
  · simp [ht0, ht1]

private theorem hq0large :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → ((∀ r : Fin 4 →
        CircleCoordinates, SemiProperQuadruple r → ∀ i : Fin 4, (r i).1 ≠ 0 → (r i).1 = 1 ∨ 4 ≤
        (r i).1) → (∀ (p : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple p) → ((q =
        ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p
        (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 :
        ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4
        : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin
        (4 : ℕ))]) → ((p (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))) → (((p (3 : Fin (4 : ℕ))).1 <
        (p (2 : Fin (4 : ℕ))).1) → (((0 : ℤ) < (q (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0
        : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) →
        (q j.succ).1 = (0 : ℤ) → i = j) → (((0 : ℤ) < (p (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 :
        ℕ)), (0 : ℤ) ≤ (p i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), (p i.succ).1 =
        (0 : ℤ) → (p j.succ).1 = (0 : ℤ) → i = j) → ((0 ≤ (p 1).1) → (((p 1).1 < (p 0).1) → ((0 <
        (p 3).1) → ((0 < (p 2).1) → (4 < (q 0).1)))))))))))) := by
  classical
  intro q hnoLine positiveLarge p hp hsucc h0 hlt cq cp hp1nonneg' hp1lt' hp3 hp2
  have hp0 : 0 < (p 0).1 := by
    have hn : (p 0).1 ≠ 0 := by simpa [h0] using hnoLine 1
    omega
  have hp1nonneg := cp.2.1 0
  have hp1lt := hp.2 0
  have hqformula := congrArg
    (fun z : Fin 4 → CircleCoordinates => (z 0).1) hsucc
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero]
      at hqformula
  have hqformula' : (q 0).1 =
      2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1 := by
    simpa using hqformula
  have hp0case := positiveLarge p hp.1 0 (by omega : (p 0).1 ≠ 0)
  have hp2case := positiveLarge p hp.1 2 (by omega : (p 2).1 ≠ 0)
  have hp3case := positiveLarge p hp.1 3 (by omega : (p 3).1 ≠ 0)
  rcases hp0case with hone | hlarge
  · have hp1zero : (p 1).1 = 0 := by omega
    norm_num [hone, hp1zero] at hqformula'
    rcases hp2case with hone2 | hlarge2 <;>
      rcases hp3case with hone3 | hlarge3 <;> omega
  · omega

private theorem config :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((∀ (i : Fin (4 : ℕ)), (q i).1 ≠
        (0 : ℤ)) → ((∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 : ℤ) → (q j).1 = (1 :
        ℤ) → i = j) → (∀ (p : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple p ∧ q =
        ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p
        (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 :
        ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4
        : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin
        (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 : ℕ)) = q (2 : Fin
        (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ (q (2 : Fin (4 : ℕ))).1 < (q (1 :
        Fin (4 : ℕ))).1 ∧ (q (3 : Fin (4 : ℕ))).1 < (q (1 : Fin (4 : ℕ))).1) →
        ((ProperBandQuadruple p) → ((p (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))) → ((p (2 : Fin (4
        : ℕ)) = q (2 : Fin (4 : ℕ))) → ((p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ))) → (∀ (t : Fin
        (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple t) → ((t (0 : Fin (4 : ℕ)) = p (2 :
        Fin (4 : ℕ))) → ((t (1 : Fin (4 : ℕ)) = p (3 : Fin (4 : ℕ))) → (((0 : ℤ) < (q (0 : Fin (4
        : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j :
            Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) → (((0 : ℤ) < (p
        (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (p i.succ).1) ∧ ∀ (i : Fin (3 :
        ℕ)), ∀ (j : Fin (3 : ℕ)), (p i.succ).1 = (0 : ℤ) → (p j.succ).1 = (0 : ℤ) → i = j) → ((4
        < (q 0).1) → ((4 ≤ (q 2).1) → ((p 1 = (2 * (q 1).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 0).1,
        2 * (q 1).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 0).2)) → (((p 0).1 < (q 0).1) → (((t 0).1 <
        (q 0).1) → (((q 3).1 ≤ (q 2).1) → ((2 * (q 1).1 + 2 * (q 2).1 + 2 * (q 3).1 = (q 0).1 +
        (p 1).1) → (Nonempty (BandOrderedGeneralConfiguration q))))))))))))))))))))) := by
  classical
  intro q hq hnoLine hatMostOneUnit p hfirst hp h0 h2 h3 t ht hb0 hb1 cq cp hq0large hq2large
      htwin hfirstsmall hsecondsmall horder23 hsoddy
  refine ⟨⟨hq, hnoLine, hatMostOneUnit, hq0large,
    hfirst.2.2.2.2.2.1, hq2large, horder23, p, t, hp, ht, h0, htwin,
    h2, h3, hb0.trans h2, hb1.trans h3, hfirstsmall,
    hsecondsmall, hsoddy, ?_, ?_, ?_, ?_⟩⟩
  · have hnat0 : ((q 0).1.toNat : Int) = (q 0).1 :=
      Int.toNat_of_nonneg (le_of_lt cq.1)
    have hnat1 : ((q 1).1.toNat : Int) = (q 1).1 :=
      Int.toNat_of_nonneg (by simpa using cq.2.1 0)
    have hnat2 : ((q 2).1.toNat : Int) = (q 2).1 :=
      Int.toNat_of_nonneg (by simpa using cq.2.1 1)
    have hnat3 : ((q 3).1.toNat : Int) = (q 3).1 :=
      Int.toNat_of_nonneg (by simpa using cq.2.1 2)
    have hnatt : ((p 1).1.toNat : Int) = (p 1).1 :=
      Int.toNat_of_nonneg (by simpa using cp.2.1 0)
    omega
  · simp [h0, h2]
  · simp [h0, h3]
  · simp [hb0, hb1, h2, h3]

private theorem haum'At397 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 :
        ℤ) → (q j).1 = (1 : ℤ) → i = j) → (
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    ∀ i j : Fin 4, (u i).1 = 1 → (u j).1 = 1 → i = j) := by
  classical
  intro q hatMostOneUnit u
  let index : Fin 4 → Fin 4 := ![0, 1, 3, 2]
  have negOne : (-1 : Fin 3) = 2 := by decide
  have negTwo : (-2 : Fin 3) = 1 := by decide
  have hiMap : ∀ i : Fin 4, (u i).1 = (q (index i)).1 := by
    intro i
    fin_cases i <;> simp [index, u, BandPackingSymmetryQuadrupleAction,
      BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction,
      negOne, negTwo]
  intro i j hi hj
  have hi' : (q (index i)).1 = 1 := by rw [← hiMap i]; exact hi
  have hj' : (q (index j)).1 = 1 := by rw [← hiMap j]; exact hj
  have he := hatMostOneUnit (index i) (index j) hi' hj'
  fin_cases i <;> fin_cases j <;> simp [index] at he ⊢

private theorem hs'At413 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (q = ![((2 : ℤ) *
        (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
        ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p
        (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let pr : Fin 4 → CircleCoordinates := p
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    let pp := BandPackingSymmetryQuadrupleAction .conjugate pr
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (u = ![(2 * (pp 0).1 + 2 * (pp 2).1 + 2
        * (pp 3).1 - (pp 1).1,
      2 * (pp 0).2 + 2 * (pp 2).2 + 2 * (pp 3).2 - (pp 1).2), pp 0, pp 2, pp 3]))) := by
  classical
  intro q p hsucc pr u pp negOneSucc negTwoSucc
  have hss := congrArg
    (fun z => BandPackingSymmetryQuadrupleAction .conjugate z) hsucc
  change BandPackingSymmetryQuadrupleAction .conjugate q = _
  convert hss using 1;
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, Fin.isValue, GaussianReflection, Int.reduceNeg,
        BandPackingSymmetryReversesOrientation, ↓reduceIte, neg_zero, Fin.succ_zero_eq_one,
        negOneSucc, negTwoSucc, Matrix.cons_val_zero, Matrix.cons_val, Matrix.cons_val_one,
        Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_ofNat, Nat.cast_ofNat,
        Zsqrtd.im_ofNat, mul_zero, zero_mul, add_zero, Zsqrtd.im_sub, Zsqrtd.im_add,
        Zsqrtd.im_mul, neg_sub, Matrix.vecCons_inj, Prod.mk.injEq, sub_left_inj, and_true, pp,
        pr];
    try { constructor
          · ring
          · ext <;> simp [] <;> ring }

private theorem hs'At528 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (![q (0 : Fin (4
        : ℕ)), q (2 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p
        (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
        ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p
        (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (u = ![(2 * (pp 0).1 + 2 * (pp 2).1 + 2
        * (pp 3).1 - (pp 1).1,
      2 * (pp 0).2 + 2 * (pp 2).2 + 2 * (pp 3).2 - (pp 1).2), pp 0, pp 2, pp 3]))) := by
  classical
  intro q p hsucc base u pp negOneSucc negTwoSucc
  have hss := congrArg (fun z => BandPackingSymmetryQuadrupleAction .conjugate z) hsucc
  change BandPackingSymmetryQuadrupleAction .conjugate base = _
  convert hss using 1;
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, Fin.isValue, GaussianReflection, Int.reduceNeg,
        BandPackingSymmetryReversesOrientation, ↓reduceIte, neg_zero, Fin.succ_zero_eq_one,
        negOneSucc, negTwoSucc, Matrix.cons_val_zero, Matrix.cons_val, Matrix.cons_val_one,
        Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_ofNat, Nat.cast_ofNat,
        Zsqrtd.im_ofNat, mul_zero, zero_mul, add_zero, Zsqrtd.im_sub, Zsqrtd.im_add,
        Zsqrtd.im_mul, neg_sub, Matrix.vecCons_inj, Prod.mk.injEq, sub_left_inj, and_true, pp];
    try { constructor
          · ring
          · ext <;> simp [] <;> ring }

private theorem hs'At631 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (![q (0 : Fin (4
        : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 : ℕ)), q (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p
        (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
        ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p
        (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (u = ![(2 * (pp 0).1 + 2 * (pp 2).1 + 2
        * (pp 3).1 - (pp 1).1,
      2 * (pp 0).2 + 2 * (pp 2).2 + 2 * (pp 3).2 - (pp 1).2), pp 0, pp 2, pp 3]))) := by
  classical
  intro q p hsucc base u pp negOneSucc negTwoSucc
  have hss := congrArg (fun z => BandPackingSymmetryQuadrupleAction .conjugate z) hsucc
  change BandPackingSymmetryQuadrupleAction .conjugate base = _
  convert hss using 1;
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction, Fin.isValue, GaussianReflection, Int.reduceNeg,
        BandPackingSymmetryReversesOrientation, ↓reduceIte, neg_zero, Fin.succ_zero_eq_one,
        negOneSucc, negTwoSucc, Matrix.cons_val_zero, Matrix.cons_val, Matrix.cons_val_one,
        Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_ofNat, Nat.cast_ofNat,
        Zsqrtd.im_ofNat, mul_zero, zero_mul, add_zero, Zsqrtd.im_sub, Zsqrtd.im_add,
        Zsqrtd.im_mul, neg_sub, Matrix.vecCons_inj, Prod.mk.injEq, sub_left_inj, and_true, pp];
    try { constructor
          · ring
          · ext <;> simp [] <;> ring }

end RetainedBoundaryProof

namespace RetainedBoundaryDetails

private theorem positiveLarge :
    (∀ (r : Fin (4 : ℕ) → CircleCoordinates), SemiProperQuadruple r → ∀ (i : Fin (4 : ℕ)), (r
        i).1 = (0 : ℤ) ∨ (r i).1 = (1 : ℤ) ∨ (4 : ℤ) ≤ (r i).1) → (∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ i : Fin 4, (r i).1 ≠ 0 →
        (r i).1 = 1 ∨ 4 ≤ (r i).1) := by
  classical
  intro curvatureBound r hr i hi
  rcases curvatureBound r hr i with hz | hone | hlarge
  · exact (hi hz).elim
  · exact Or.inl hone
  · exact Or.inr hlarge

private theorem hp3 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → (∀ (p : Fin (4
        : ℕ) → CircleCoordinates), (p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ))) → (((0 : ℤ) < (p
        (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (p i.succ).1) ∧ ∀ (i : Fin (3 :
        ℕ)), ∀ (j : Fin (3 : ℕ)), (p i.succ).1 = (0 : ℤ) → (p j.succ).1 = (0 : ℤ) → i = j) → ((0
        ≤ (p 3).1) → (0 < (p 3).1)))) := by
  classical
  intro q hnoLine p h3 cp hp3nonneg'
  have hn : (p 3).1 ≠ 0 := by simpa [h3] using hnoLine 3
  have hn' : 0 ≤ (p 3).1 := by simpa using cp.2.1 2
  omega

private theorem hp2 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → (∀ (p : Fin (4
        : ℕ) → CircleCoordinates), (p (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))) → (((p (3 : Fin (4
        : ℕ))).1 < (p (2 : Fin (4 : ℕ))).1) → (((0 : ℤ) < (p (0 : Fin (4 : ℕ))).1 ∧ (∀ (i : Fin
        (3 : ℕ)), (0 : ℤ) ≤ (p i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j : Fin (3 : ℕ)), (p
        i.succ).1 = (0 : ℤ) → (p j.succ).1 = (0 : ℤ) → i = j) → ((0 ≤ (p 2).1) → ((0 < (p 3).1) →
        (0 < (p 2).1)))))) := by
  classical
  intro q hnoLine p h2 hlt cp hp2nonneg' hp3
  have hn : (p 2).1 ≠ 0 := by simpa [h2] using hnoLine 2
  have hn' : 0 ≤ (p 2).1 := by simpa using cp.2.1 1
  omega

private theorem hq2large :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r →
        ∀ i : Fin 4, (r i).1 ≠ 0 → (r i).1 = 1 ∨ 4 ≤ (r i).1) → (∀ (p : Fin (4 : ℕ) →
        CircleCoordinates), (ProperBandQuadruple p) → ((p (2 : Fin (4 : ℕ)) = q (2 : Fin (4 :
        ℕ))) → (((p (3 : Fin (4 : ℕ))).1 < (p (2 : Fin (4 : ℕ))).1) → ((0 < (p 3).1) → ((0 < (p
        2).1) → (4 ≤ (q 2).1)))))) := by
  classical
  intro q positiveLarge p hp h2 hlt hp3 hp2
  rcases positiveLarge p hp.1 2 (by omega : (p 2).1 ≠ 0) with hone | hlarge
  · omega
  · simpa [h2] using hlarge

private theorem htwin :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (q = ![((2 : ℤ) *
        (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
        ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p
        (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) →
        ((p (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))) → ((p (2 : Fin (4 : ℕ)) = q (2 : Fin (4 :
        ℕ))) → ((p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ))) → (p 1 =
      (2 * (q 1).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 0).1,
        2 * (q 1).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 0).2))))) := by
  classical
  intro q p hsucc h0 h2 h3
  rw [hsucc]
  simp [h0, h2, h3]

private theorem hsecondsmall :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (p : Fin (4 : ℕ) →
        CircleCoordinates), (p (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))) → (∀ (t : Fin (4 : ℕ) →
        CircleCoordinates), (t (0 : Fin (4 : ℕ)) = p (2 : Fin (4 : ℕ))) → ((t 0).1 < (q 0).1)))
            := by
  classical
  intro q hq p h2 t hb0
  calc
    (t 0).1 = (q 2).1 := congrArg Prod.fst (hb0.trans h2)
    _ < (q 0).1 := hq.2 1

private theorem horder23 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (2 : Fin (4 : ℕ))) → ((p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ))) → (((p (3 : Fin
        (4 : ℕ))).1 < (p (2 : Fin (4 : ℕ))).1) → ((q 3).1 ≤ (q 2).1))) := by
  classical
  intro q p h2 h3 hlt
  have hle := le_of_lt hlt
  simpa [h2, h3] using hle

private theorem hsoddy :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (Fin (4 : ℕ) →
        CircleCoordinates) → ((p 1 = (2 * (q 1).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 0).1, 2 * (q
        1).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 0).2)) → (2 * (q 1).1 + 2 * (q 2).1 + 2 * (q 3).1 =
        (q 0).1 + (p 1).1)) := by
  classical
  intro q p t htwin
  have hf := congrArg Prod.fst htwin
  omega

private theorem htuple :
    ∀ (q : Fin 4 → CircleCoordinates), ![q 0, q 1, q 2, q 3] = q := by
  classical
  intro q
  funext i
  fin_cases i <;> rfl

private theorem hnl'At549 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → (
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    ∀ i : Fin 4, (u i).1 ≠ 0) := by
  classical
  intro q hnoLine u i
  fin_cases i <;> simp only [BandPackingSymmetryQuadrupleAction,
      BandPackingSymmetryCircleAction, Fin.isValue, BandPackingSymmetryReversesOrientation,
      ↓reduceIte, neg_zero, Fin.succ_zero_eq_one, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, ne_eq, u, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta] <;>
    apply hnoLine

private theorem h0'At562 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (0 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ))) → (
    let pr : Fin 4 → CircleCoordinates := p
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    let pp := BandPackingSymmetryQuadrupleAction .conjugate pr
    ((-1 : Fin 3) = 2) → (((-2 : Fin 3) = 1) → (
    pp 0 = u 1))) := by
  classical
  intro q p h0 pr u pp negOne negTwo
  let reflect : CircleCoordinates → CircleCoordinates :=
    fun C => (C.1, GaussianReflection C.2)
  simpa [u, pp, pr, BandPackingSymmetryQuadrupleAction,
    BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction,
    negOne, negTwo, reflect] using congrArg reflect h0

private theorem h2'At566 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (3 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ))) → (
    let pr : Fin 4 → CircleCoordinates := p
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    let pp := BandPackingSymmetryQuadrupleAction .conjugate pr
    ((-1 : Fin 3) = 2) → (((-2 : Fin 3) = 1) → (
    pp 2 = u 2))) := by
  classical
  intro q p h3 pr u pp negOne negTwo
  let reflect : CircleCoordinates → CircleCoordinates :=
    fun C => (C.1, GaussianReflection C.2)
  simpa [u, pp, pr, BandPackingSymmetryQuadrupleAction,
    BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction,
    negOne, negTwo, reflect] using congrArg reflect h3

private theorem h3'At570 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (2 : Fin (4 : ℕ))) → (
    let pr : Fin 4 → CircleCoordinates := p
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    let pp := BandPackingSymmetryQuadrupleAction .conjugate pr
    ((-1 : Fin 3) = 2) → (((-2 : Fin 3) = 1) → (
    pp 3 = u 3))) := by
  classical
  intro q p h2 pr u pp negOne negTwo
  let reflect : CircleCoordinates → CircleCoordinates :=
    fun C => (C.1, GaussianReflection C.2)
  simpa [u, pp, pr, BandPackingSymmetryQuadrupleAction,
    BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction,
    negOne, negTwo, reflect] using congrArg reflect h2

private theorem ht0'At574 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (3 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ))) → (∀ (t : Fin (4 : ℕ) → CircleCoordinates), (t (0 : Fin (4 :
        ℕ)) = p (3 : Fin (4 : ℕ))) → (
    let tr : Fin 4 → CircleCoordinates := t
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    let tt := BandPackingSymmetryQuadrupleAction .conjugate tr
    ((-1 : Fin 3) = 2) → (((-2 : Fin 3) = 1) → (tt 0 = u 2)))) := by
  classical
  intro q p h3 t ht0 tr u tt negOne negTwo
  simp [u, tt, tr, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, ht0, h3,
         negOne, negTwo]

private theorem ht1'At577 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (2 : Fin (4 : ℕ))) → (∀ (t : Fin (4 : ℕ) → CircleCoordinates), (t (1 : Fin (4 :
        ℕ)) = p (2 : Fin (4 : ℕ))) → (
    let tr : Fin 4 → CircleCoordinates := t
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    let tt := BandPackingSymmetryQuadrupleAction .conjugate tr
    ((-1 : Fin 3) = 2) → (((-2 : Fin 3) = 1) → (tt 1 = u 3)))) := by
  classical
  intro q p h2 t ht1 tr u tt negOne negTwo
  simp [u, tt, tr, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, ht1, h2,
         negOne, negTwo]

private theorem hlt2'At580 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        (ProperBandQuadruple p ∧ q = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin
        (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 :
        GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2
        : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)),
        p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p
        (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ (q
        (2 : Fin (4 : ℕ))).1 < (q (1 : Fin (4 : ℕ))).1 ∧ (q (3 : Fin (4 : ℕ))).1 < (q (1 : Fin (4
        : ℕ))).1) → (
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → ((u 2).1 < (u 1).1))) := by
  classical
  intro q p hfirst u negOneSucc negTwoSucc
  simpa [u, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc] using hfirst.2.2.2.2.2.2

private theorem hlt3'At583 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        (ProperBandQuadruple p ∧ q = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin
        (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 :
        GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2
        : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)),
        p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p
        (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ (q
        (2 : Fin (4 : ℕ))).1 < (q (1 : Fin (4 : ℕ))).1 ∧ (q (3 : Fin (4 : ℕ))).1 < (q (1 : Fin (4
        : ℕ))).1) → (
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → ((u 3).1 < (u 1).1))) := by
  classical
  intro q p hfirst u negOneSucc negTwoSucc
  simpa [u, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc] using hfirst.2.2.2.2.2.1

private theorem hord'At586 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (2 : Fin (4 : ℕ))) → ((p (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ))) → (((p (2 : Fin
        (4 : ℕ))).1 < (p (3 : Fin (4 : ℕ))).1) → (
    let u := BandPackingSymmetryQuadrupleAction .conjugate q
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → ((u 3).1 < (u 2).1))))) := by
  classical
  intro q p h2 h3 hlt u negOneSucc negTwoSucc
  simpa [u, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, h2, h3] using hlt

private theorem tupleEq :
    ∀ (q : Fin 4 → CircleCoordinates), ![q 0, q 1, q 2, q 3] = q := by
  classical
  intro q
  funext i
  fin_cases i <;> rfl

private theorem huAt613 :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (
    let u : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    ProperBandQuadruple u) := by
  classical
  intro q hq u
  refine ⟨SemiProperQuadruple.rotate hq.1, ?_⟩
  intro i
  fin_cases i
  · simpa [u] using hq.2 1
  · simpa [u] using hq.2 2
  · simpa [u] using hq.2 0

private theorem hnl'At620 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → (
    let u : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    ∀ i : Fin 4, (u i).1 ≠ 0) := by
  classical
  intro q hnoLine u i
  fin_cases i <;> simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, ne_eq, u, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta] <;> apply
          hnoLine

private theorem haum'At623 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 :
        ℤ) → (q j).1 = (1 : ℤ) → i = j) → (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (2 : Fin (4 : ℕ)), q (3 : Fin (4 :
            ℕ)),
        q (1 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ (q (3 : Fin (4 :
        ℕ))).1 < (q (2 : Fin (4 : ℕ))).1 ∧ (q (1 : Fin (4 : ℕ))).1 < (q (2 : Fin (4 : ℕ))).1) → (
    let u : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    ∀ i j : Fin 4, (u i).1 = 1 → (u j).1 = 1 → i = j)) := by
  classical
  intro q hatMostOneUnit p hsecond u i j hi hj
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, u, Fin.zero_eta,
      one_ne_zero, zero_ne_one] at hi hj ⊢ <;>
    (exfalso; have e := hatMostOneUnit _ _ hi hj; omega)

private theorem huAt646 :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    ProperBandQuadruple u) := by
  classical
  intro q hq base u
  simpa [u] using BandPackingSymmetryProperCovariance .conjugate _
    (by simpa [base] using (show ProperBandQuadruple base from
      ⟨SemiProperQuadruple.rotate hq.1, by
        intro i; fin_cases i
        · simpa [base] using hq.2 1
        · simpa [base] using hq.2 2
        · simpa [base] using hq.2 0⟩))

private theorem hnl'At656 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    ∀ i : Fin 4, (u i).1 ≠ 0) := by
  classical
  intro q hnoLine base u i; fin_cases i <;> simp only [BandPackingSymmetryQuadrupleAction,
      BandPackingSymmetryCircleAction, Fin.isValue, Matrix.cons_val_zero,
      BandPackingSymmetryReversesOrientation, ↓reduceIte, neg_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val, Fin.mk_one, ne_eq, u, base,
      Fin.reduceFinMk, Fin.zero_eta] <;> apply hnoLine

private theorem haum'At660 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 :
        ℤ) → (q j).1 = (1 : ℤ) → i = j) → (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (2 : Fin (4 : ℕ)), q (3 : Fin (4 :
            ℕ)),
        q (1 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ (q (3 : Fin (4 :
        ℕ))).1 < (q (2 : Fin (4 : ℕ))).1 ∧ (q (1 : Fin (4 : ℕ))).1 < (q (2 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    ∀ i j : Fin 4, (u i).1 = 1 → (u j).1 = 1 → i = j)) := by
  classical
  intro q hatMostOneUnit p hsecond base u i j hi hj
  fin_cases i <;> fin_cases j <;> simp only [BandPackingSymmetryQuadrupleAction,
      BandPackingSymmetryCircleAction, Fin.isValue, Matrix.cons_val_zero,
      BandPackingSymmetryReversesOrientation, ↓reduceIte, neg_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceEq, u, base, Fin.zero_eta, one_ne_zero, zero_ne_one] at hi hj ⊢ <;>
    (exfalso; have e := hatMostOneUnit _ _ hi hj; omega)

private theorem h0'At670 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (0 : Fin (4 :
        ℕ)) = q (2 : Fin (4 : ℕ))) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (
    pp 0 = u 1))) := by
  classical
  intro q p h0 base u pp negOneSucc negTwoSucc
  let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
      C.2)
  simpa [u, pp, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, reflect] using congrArg reflect h0

private theorem h2'At673 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (3 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ))) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (
    pp 2 = u 2))) := by
  classical
  intro q p h3 base u pp negOneSucc negTwoSucc
  let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
      C.2)
  simpa [u, pp, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, reflect] using congrArg reflect h3

private theorem h3'At676 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ))) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (
    pp 3 = u 3))) := by
  classical
  intro q p h2 base u pp negOneSucc negTwoSucc
  let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
      C.2)
  simpa [u, pp, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, reflect] using congrArg reflect h2

private theorem hlt2'At683 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (2 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)),
        q (1 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ (q (3 : Fin (4 :
        ℕ))).1 < (q (2 : Fin (4 : ℕ))).1 ∧ (q (1 : Fin (4 : ℕ))).1 < (q (2 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    (u 2).1 < (u 1).1) := by
  classical
  intro q p hsecond base u
  simpa [u, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction] using
         hsecond.2.2.2.2.2.2

private theorem hlt3'At686 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (2 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)),
        q (1 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ (q (3 : Fin (4 :
        ℕ))).1 < (q (2 : Fin (4 : ℕ))).1 ∧ (q (1 : Fin (4 : ℕ))).1 < (q (2 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    (u 3).1 < (u 1).1) := by
  classical
  intro q p hsecond base u
  simpa [u, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction] using
         hsecond.2.2.2.2.2.1

private theorem hord'At689 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ))) → ((p (3 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ))) → (((p (2 : Fin
        (4 : ℕ))).1 < (p (3 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → ((u 3).1 < (u 2).1))))) := by
  classical
  intro q p h2 h3 hlt base u negOneSucc negTwoSucc
  simpa [u, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, h2, h3] using hlt

private theorem huAt713 :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (
    let u : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    ProperBandQuadruple u) := by
  classical
  intro q hq u
  refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1), ?_⟩
  intro i
  fin_cases i
  · simpa [u] using hq.2 2
  · simpa [u] using hq.2 0
  · simpa [u] using hq.2 1

private theorem hnl'At720 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → (
    let u : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    ∀ i : Fin 4, (u i).1 ≠ 0) := by
  classical
  intro q hnoLine u i
  fin_cases i <;> simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, ne_eq, u, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta] <;> apply
          hnoLine

private theorem haum'At723 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 :
        ℤ) → (q j).1 = (1 : ℤ) → i = j) → (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 :
            ℕ)),
        q (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ (q (1 : Fin (4 :
        ℕ))).1 < (q (3 : Fin (4 : ℕ))).1 ∧ (q (2 : Fin (4 : ℕ))).1 < (q (3 : Fin (4 : ℕ))).1) → (
    let u : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    ∀ i j : Fin 4, (u i).1 = 1 → (u j).1 = 1 → i = j)) := by
  classical
  intro q hatMostOneUnit p hthird u i j hi hj
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, u, Fin.zero_eta,
      one_ne_zero, zero_ne_one] at hi hj ⊢ <;>
    (exfalso; have e := hatMostOneUnit _ _ hi hj; omega)

private theorem hs'At727 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (![q (0 : Fin (4
        : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 : ℕ)), q (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p
        (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
        ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p
        (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))]) → (
    let u : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    u = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
      2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3]) := by
  classical
  intro q p hsucc u
  simpa [u] using hsucc

private abbrev hb :=
  ApollonianSuperharmonic.RetainedBoundaryDetails.huAt713

private theorem hnl'At757 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), (q i).1 ≠ (0 : ℤ)) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    ∀ i : Fin 4, (u i).1 ≠ 0) := by
  classical
  intro q hnoLine base u i; fin_cases i <;> simp only [BandPackingSymmetryQuadrupleAction,
      BandPackingSymmetryCircleAction, Fin.isValue, Matrix.cons_val_zero,
      BandPackingSymmetryReversesOrientation, ↓reduceIte, neg_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val, Fin.mk_one, ne_eq, u, base,
      Fin.reduceFinMk, Fin.zero_eta] <;> apply hnoLine

private theorem haum'At761 :
    ∀ (q : Fin 4 → CircleCoordinates), (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 :
        ℤ) → (q j).1 = (1 : ℤ) → i = j) → (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 :
            ℕ)),
        q (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ (q (1 : Fin (4 :
        ℕ))).1 < (q (3 : Fin (4 : ℕ))).1 ∧ (q (2 : Fin (4 : ℕ))).1 < (q (3 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    ∀ i j : Fin 4, (u i).1 = 1 → (u j).1 = 1 → i = j)) := by
  classical
  intro q hatMostOneUnit p hthird base u i j hi hj
  fin_cases i <;> fin_cases j <;> simp only [BandPackingSymmetryQuadrupleAction,
      BandPackingSymmetryCircleAction, Fin.isValue, Matrix.cons_val_zero,
      BandPackingSymmetryReversesOrientation, ↓reduceIte, neg_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceEq, u, base, Fin.zero_eta, one_ne_zero, zero_ne_one] at hi hj ⊢ <;>
    (exfalso; have e := hatMostOneUnit _ _ hi hj; omega)

private theorem h0'At771 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (0 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ))) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (
    pp 0 = u 1))) := by
  classical
  intro q p h0 base u pp negOneSucc negTwoSucc
  let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
      C.2)
  simpa [u, pp, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, reflect] using congrArg reflect h0

private theorem h2'At774 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (3 : Fin (4 :
        ℕ)) = q (2 : Fin (4 : ℕ))) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (
    pp 2 = u 2))) := by
  classical
  intro q p h3 base u pp negOneSucc negTwoSucc
  let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
      C.2)
  simpa [u, pp, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, reflect] using congrArg reflect h3

private theorem h3'At777 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ))) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    let pp := BandPackingSymmetryQuadrupleAction .conjugate p
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → (
    pp 3 = u 3))) := by
  classical
  intro q p h2 base u pp negOneSucc negTwoSucc
  let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
      C.2)
  simpa [u, pp, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, reflect] using congrArg reflect h2

private theorem hlt2'At784 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 : ℕ)),
        q (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ (q (1 : Fin (4 :
        ℕ))).1 < (q (3 : Fin (4 : ℕ))).1 ∧ (q (2 : Fin (4 : ℕ))).1 < (q (3 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    (u 2).1 < (u 1).1) := by
  classical
  intro q p hthird base u
  simpa [u, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction] using
         hthird.2.2.2.2.2.2

private theorem hlt3'At787 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates),
        (ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 : ℕ)),
        q (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ (q (1 : Fin (4 :
        ℕ))).1 < (q (3 : Fin (4 : ℕ))).1 ∧ (q (2 : Fin (4 : ℕ))).1 < (q (3 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    (u 3).1 < (u 1).1) := by
  classical
  intro q p hthird base u
  simpa [u, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction] using
         hthird.2.2.2.2.2.1

private theorem hord'At790 :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (p : Fin (4 : ℕ) → CircleCoordinates), (p (2 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ))) → ((p (3 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ))) → (((p (2 : Fin
        (4 : ℕ))).1 < (p (3 : Fin (4 : ℕ))).1) → (
    let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
    let u := BandPackingSymmetryQuadrupleAction .conjugate base
    ((-1 : Fin 3).succ = 3) → (((-2 : Fin 3).succ = 2) → ((u 3).1 < (u 2).1))))) := by
  classical
  intro q p h2 h3 hlt base u negOneSucc negTwoSucc
  simpa [u, base, BandPackingSymmetryQuadrupleAction,
     BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, negOneSucc,
         negTwoSucc, h2, h3] using hlt

end RetainedBoundaryDetails

namespace RetainedBoundaryCases

private theorem firstParentCase :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((∀ (i : Fin (4 : ℕ)), (q i).1 ≠
        (0 : ℤ)) → ((∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 : ℤ) → (q j).1 = (1 :
        ℤ) → i = j) → ((∀ (r : Fin (4 : ℕ) → CircleCoordinates), SemiProperQuadruple r → ∀ (i :
            Fin (4 : ℕ)), (r i).1 ≠ (0 : ℤ) → (r i).1 = (1 : ℤ) ∨ (4 : ℤ) ≤ (r i).1) → ((∀ (u :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (p : Fin (4 : ℕ) →
        CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple u → (∀
            (i : Fin (4 : ℕ)), (u i).1 ≠ (0 : ℤ)) → (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (u
        i).1 = (1 : ℤ) → (u j).1 = (1 : ℤ) → i = j) → ProperBandQuadruple p → u = ![((2 : ℤ) * (p
        (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
        ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p
        (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))] → p
        (0 : Fin (4 : ℕ)) = u (1 : Fin (4 : ℕ)) → p (2 : Fin (4 : ℕ)) = u (2 : Fin (4 : ℕ)) → p
        (3 : Fin (4 : ℕ)) = u (3 : Fin (4 : ℕ)) → (u (2 : Fin (4 : ℕ))).1 < (u (1 : Fin (4 :
        ℕ))).1 → (u (3 : Fin (4 : ℕ))).1 < (u (1 : Fin (4 : ℕ))).1 → ProperBandQuadruple t → t (0
        : Fin (4 : ℕ)) = u (2 : Fin (4 : ℕ)) → t (1 : Fin (4 : ℕ)) = u (3 : Fin (4 : ℕ)) → (u (3
        : Fin (4 : ℕ))).1 < (u (2 : Fin (4 : ℕ))).1 → Nonempty (BandOrderedGeneralConfiguration
        u)) → ((∃ (p : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple p ∧ q = ![((2 : ℤ) *
        (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 :
        ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 : Fin (4 : ℕ))).2 - (p
        (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p
        (0 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p
        (3 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ (q (2 : Fin (4 : ℕ))).1 < (q (1 : Fin (4 :
        ℕ))).1 ∧ (q (3 : Fin (4 : ℕ))).1 < (q (1 : Fin (4 : ℕ))).1) → (∃ (r : Fin 3) (g :
        BandPackingSymmetry), Nonempty (BandOrderedGeneralConfiguration
        (BandPackingSymmetryQuadrupleAction g ![q 0, q r.succ, q (r + 1).succ, q (r +
        2).succ])))))))) := by
  classical
  intro q hq hnoLine hatMostOneUnit positiveLarge buildConfiguration first
  rcases first with ⟨p, hfirst⟩
  have hp := hfirst.1
  have hsucc := hfirst.2.1
  have h0 := hfirst.2.2.1
  have h2 := hfirst.2.2.2.1
  have h3 := hfirst.2.2.2.2.1
  rcases BandOrientedBoundaryParentChain p hp with hsmall | horient
  · rcases hsmall with ⟨hroot2, hroot3⟩
    have hone2 := hroot2.resolve_left (by rw [h2]; exact hnoLine 2)
    have hone3 := hroot3.resolve_left (by rw [h3]; exact hnoLine 3)
    rw [h2] at hone2
    rw [h3] at hone3
    have bad := hatMostOneUnit 2 3 hone2 hone3
    omega
  · rcases horient with bd | db
    · refine ⟨0, ?_⟩
      rcases bd with ⟨t, ht, hb0, hb1, hlt⟩
      refine ⟨.identity, ?_⟩
      have cq := ProperBandCurvatureStructure q hq
      have cp := ProperBandCurvatureStructure p hp
      have hp1nonneg' : 0 ≤ (p 1).1 := by simpa using cp.2.1 0
      have hp1lt' : (p 1).1 < (p 0).1 := by simpa using hp.2 0
      have hp2nonneg' : 0 ≤ (p 2).1 := by simpa using cp.2.1 1
      have hp3nonneg' : 0 ≤ (p 3).1 := by simpa using cp.2.1 2
      have hq2nonneg := cq.2.1 1
      have hp2nonneg := cp.2.1 1
      have hp3nonneg := cp.2.1 2
      have hp3 := RetainedBoundaryDetails.hp3 q hnoLine p h3 cp hp3nonneg'
      have hp2 := RetainedBoundaryDetails.hp2 q hnoLine p h2 hlt cp hp2nonneg' hp3
      have hq0large := RetainedBoundaryProof.hq0large q hnoLine positiveLarge p
          hp hsucc h0 hlt cq cp hp1nonneg' hp1lt' hp3 hp2
      have hq2large := RetainedBoundaryDetails.hq2large q positiveLarge p hp h2
          hlt hp3 hp2
      have htwin := RetainedBoundaryDetails.htwin
                q p hsucc h0 h2 h3
      have hfirstsmall : (p 0).1 < (q 0).1 := by
        simpa [h0] using hq.2 0
      have hsecondsmall := RetainedBoundaryDetails.hsecondsmall q hq p h2 t
          hb0
      have horder23 := RetainedBoundaryDetails.horder23 q p h2 h3 hlt
      have hsoddy := RetainedBoundaryDetails.hsoddy q p t htwin
      have config := RetainedBoundaryProof.config q hq hnoLine hatMostOneUnit p hfirst hp h0 h2
          h3 t ht
          hb0 hb1 cq cp hq0large hq2large htwin hfirstsmall hsecondsmall horder23 hsoddy
      have htuple := RetainedBoundaryDetails.htuple q
      rw [← htuple] at config
      simpa [BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryReversesOrientation,
        BandPackingSymmetryCircleAction] using config
    · refine ⟨0, ?_⟩
      rcases db with ⟨t, ht, ht0, ht1, hlt⟩
      let pr : Fin 4 → CircleCoordinates := p
      let tr : Fin 4 → CircleCoordinates := t
      have hpr : ProperBandQuadruple pr := by
        simpa [pr] using hp
      have htr : ProperBandQuadruple tr := by
        simpa [tr] using ht
      have hqr : ProperBandQuadruple q := hq
      let u := BandPackingSymmetryQuadrupleAction .conjugate q
      let pp := BandPackingSymmetryQuadrupleAction .conjugate pr
      let tt := BandPackingSymmetryQuadrupleAction .conjugate tr
      have hu : ProperBandQuadruple u := by
        simpa [u] using BandPackingSymmetryProperCovariance .conjugate _ hqr
      have hp' : ProperBandQuadruple pp := by
        simpa [pp] using BandPackingSymmetryProperCovariance .conjugate _ hpr
      have ht' : ProperBandQuadruple tt := by
        simpa [tt] using BandPackingSymmetryProperCovariance .conjugate _ htr
      have hnl' := RetainedBoundaryDetails.hnl'At549 q hnoLine
      have haum' := RetainedBoundaryProof.haum'At397 q hatMostOneUnit
      have negOneSucc : (-1 : Fin 3).succ = 3 := by decide
      have negTwoSucc : (-2 : Fin 3).succ = 2 := by decide
      have hs' := RetainedBoundaryProof.hs'At413 q p hsucc negOneSucc negTwoSucc
      have negOne : (-1 : Fin 3) = 2 := by decide
      have negTwo : (-2 : Fin 3) = 1 := by decide
      let reflect : CircleCoordinates → CircleCoordinates :=
        fun C => (C.1, GaussianReflection C.2)
      have h0' := RetainedBoundaryDetails.h0'At562 q p h0 negOne negTwo
      have h2' := RetainedBoundaryDetails.h2'At566 q p h3 negOne negTwo
      have h3' := RetainedBoundaryDetails.h3'At570 q p h2 negOne negTwo
      have ht0' := RetainedBoundaryDetails.ht0'At574 q p h3 t ht0 negOne negTwo
      have ht1' := RetainedBoundaryDetails.ht1'At577 q p h2 t ht1 negOne negTwo
      have hlt2' := RetainedBoundaryDetails.hlt2'At580 q p hfirst
          negOneSucc negTwoSucc
      have hlt3' := RetainedBoundaryDetails.hlt3'At583 q p hfirst
          negOneSucc negTwoSucc
      have hord' := RetainedBoundaryDetails.hord'At586 q p h2 h3 hlt
          negOneSucc negTwoSucc
      have tupleEq := RetainedBoundaryDetails.tupleEq q
      refine ⟨.conjugate, ?_⟩
      simpa [u, tupleEq] using buildConfiguration u pp tt hu hnl' haum' hp' hs' h0' h2' h3'
        hlt2' hlt3' ht' ht0' ht1' hord'

private theorem secondParentCase :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((∀ (i : Fin (4 : ℕ)), (q i).1 ≠
        (0 : ℤ)) → ((∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 : ℤ) → (q j).1 = (1 :
        ℤ) → i = j) → ((∀ (u : Fin (4 : ℕ) → CircleCoordinates), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple u →
            (∀ (i : Fin (4 : ℕ)), (u i).1 ≠ (0 : ℤ)) → (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)),
            (u i).1 = (1 : ℤ) → (u j).1 = (1 : ℤ) → i = j) → ProperBandQuadruple
        p → u = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 :
        ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin
        (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 :
        Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p
        (3 : Fin (4 : ℕ))] → p (0 : Fin (4 : ℕ)) = u (1 : Fin (4 : ℕ)) → p (2 : Fin (4 : ℕ)) = u
        (2 : Fin (4 : ℕ)) → p (3 : Fin (4 : ℕ)) = u (3 : Fin (4 : ℕ)) → (u (2 : Fin (4 : ℕ))).1 <
        (u (1 : Fin (4 : ℕ))).1 → (u (3 : Fin (4 : ℕ))).1 < (u (1 : Fin (4 : ℕ))).1 →
        ProperBandQuadruple t → t (0 : Fin (4 : ℕ)) = u (2 : Fin (4 : ℕ)) → t (1 : Fin (4 : ℕ)) =
        u (3 : Fin (4 : ℕ)) → (u (3 : Fin (4 : ℕ))).1 < (u (2 : Fin (4 : ℕ))).1 → Nonempty
        (BandOrderedGeneralConfiguration u)) → ((∃ (p : Fin (4 : ℕ) → CircleCoordinates),
        ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (2 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)),
        q (1 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (1 : Fin (4 : ℕ)) ∧ (q (3 : Fin (4 :
        ℕ))).1 < (q (2 : Fin (4 : ℕ))).1 ∧ (q (1 : Fin (4 : ℕ))).1 < (q (2 : Fin (4 : ℕ))).1) →
        (∃ (r : Fin 3) (g : BandPackingSymmetry), Nonempty (BandOrderedGeneralConfiguration
        (BandPackingSymmetryQuadrupleAction g ![q 0, q r.succ, q (r + 1).succ, q (r +
        2).succ]))))))) := by
  classical
  intro q hq hnoLine hatMostOneUnit buildConfiguration second
  rcases second with ⟨p, hsecond⟩
  have hp := hsecond.1
  have hsucc := hsecond.2.1
  have h0 := hsecond.2.2.1
  have h2 := hsecond.2.2.2.1
  have h3 := hsecond.2.2.2.2.1
  rcases BandOrientedBoundaryParentChain p hp with hsmall | horient
  · rcases hsmall with ⟨hroot2, hroot3⟩
    have hone3 := hroot2.resolve_left (by rw [h2]; exact hnoLine 3)
    have hone1 := hroot3.resolve_left (by rw [h3]; exact hnoLine 1)
    rw [h2] at hone3
    rw [h3] at hone1
    have bad := hatMostOneUnit 3 1 hone3 hone1
    omega
  · rcases horient with bd | db
    · refine ⟨1, ?_⟩
      rcases bd with ⟨t, ht, ht0, ht1, hlt⟩
      let u : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
      have hu := RetainedBoundaryDetails.huAt613 q hq
      have hnl' := RetainedBoundaryDetails.hnl'At620 q hnoLine
      have haum' := RetainedBoundaryDetails.haum'At623 q hatMostOneUnit p hsecond
      have hs' : u = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3] := hsucc
      have h0' : p 0 = u 1 := by simpa [u] using h0
      have h2' : p 2 = u 2 := by simpa [u] using h2
      have h3' : p 3 = u 3 := by simpa [u] using h3
      have hlt2' : (u 2).1 < (u 1).1 := by simpa [u] using hsecond.2.2.2.2.2.1
      have hlt3' : (u 3).1 < (u 1).1 := by simpa [u] using hsecond.2.2.2.2.2.2
      have hord' : (u 3).1 < (u 2).1 := by simpa [u, h2, h3] using hlt
      have hc := buildConfiguration u p t hu hnl' haum' hp hs' h0' h2' h3'
        hlt2' hlt3' ht (by simpa [u, h2] using ht0) (by simpa [u, h3] using ht1) hord'
      refine ⟨.identity, ?_⟩
      simpa [u, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction] using hc
    · refine ⟨1, ?_⟩
      rcases db with ⟨t, ht, ht0, ht1, hlt⟩
      let base : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
      let u := BandPackingSymmetryQuadrupleAction .conjugate base
      let pp := BandPackingSymmetryQuadrupleAction .conjugate p
      let tt := BandPackingSymmetryQuadrupleAction .conjugate t
      have hu := RetainedBoundaryDetails.huAt646 q hq
      have hp' : ProperBandQuadruple pp := BandPackingSymmetryProperCovariance .conjugate p hp
      have ht' : ProperBandQuadruple tt := BandPackingSymmetryProperCovariance .conjugate t ht
      have hnl' := RetainedBoundaryDetails.hnl'At656 q hnoLine
      have haum' := RetainedBoundaryDetails.haum'At660 q hatMostOneUnit p hsecond
      have negOneSucc : (-1 : Fin 3).succ = 3 := by decide
      have negTwoSucc : (-2 : Fin 3).succ = 2 := by decide
      have hs' := RetainedBoundaryProof.hs'At528 q p hsucc negOneSucc negTwoSucc
      let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
          C.2)
      have h0' := RetainedBoundaryDetails.h0'At670 q p h0 negOneSucc negTwoSucc
      have h2' := RetainedBoundaryDetails.h2'At673 q p h3 negOneSucc negTwoSucc
      have h3' := RetainedBoundaryDetails.h3'At676 q p h2 negOneSucc negTwoSucc
      have ht0' : tt 0 = u 2 := by simp [u, tt, base, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, ht0, h3]
      have ht1' : tt 1 = u 3 := by simp [u, tt, base, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, ht1, h2]
      have hlt2' := RetainedBoundaryDetails.hlt2'At683 q p hsecond
      have hlt3' := RetainedBoundaryDetails.hlt3'At686 q p hsecond
      have hord' := RetainedBoundaryDetails.hord'At689 q p h2 h3 hlt
          negOneSucc negTwoSucc
      refine ⟨.conjugate, ?_⟩
      simpa [u, base] using buildConfiguration u pp tt hu hnl' haum' hp' hs' h0' h2' h3'
        hlt2' hlt3' ht' ht0' ht1' hord'

private theorem thirdParentCase :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((∀ (i : Fin (4 : ℕ)), (q i).1 ≠
        (0 : ℤ)) → ((∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), (q i).1 = (1 : ℤ) → (q j).1 = (1 :
        ℤ) → i = j) → ((∀ (u : Fin (4 : ℕ) → CircleCoordinates), ∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (t : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple u →
            (∀ (i : Fin (4 : ℕ)), (u i).1 ≠ (0 : ℤ)) → (∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)),
            (u i).1 = (1 : ℤ) → (u j).1 = (1 : ℤ) → i = j) → ProperBandQuadruple
        p → u = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 : ℕ))).1 + (2 :
        ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (p (0 : Fin
        (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (3 :
        Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4 : ℕ)), p
        (3 : Fin (4 : ℕ))] → p (0 : Fin (4 : ℕ)) = u (1 : Fin (4 : ℕ)) → p (2 : Fin (4 : ℕ)) = u
        (2 : Fin (4 : ℕ)) → p (3 : Fin (4 : ℕ)) = u (3 : Fin (4 : ℕ)) → (u (2 : Fin (4 : ℕ))).1 <
        (u (1 : Fin (4 : ℕ))).1 → (u (3 : Fin (4 : ℕ))).1 < (u (1 : Fin (4 : ℕ))).1 →
        ProperBandQuadruple t → t (0 : Fin (4 : ℕ)) = u (2 : Fin (4 : ℕ)) → t (1 : Fin (4 : ℕ)) =
        u (3 : Fin (4 : ℕ)) → (u (3 : Fin (4 : ℕ))).1 < (u (2 : Fin (4 : ℕ))).1 → Nonempty
        (BandOrderedGeneralConfiguration u)) → ((∃ (p : Fin (4 : ℕ) → CircleCoordinates),
        ProperBandQuadruple p ∧ ![q (0 : Fin (4 : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 : ℕ)),
        q (2 : Fin (4 : ℕ))] = ![((2 : ℤ) * (p (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (p (2 : Fin (4 :
        ℕ))).1 + (2 : ℤ) * (p (3 : Fin (4 : ℕ))).1 - (p (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) *
        (p (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (p (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt)
        * (p (3 : Fin (4 : ℕ))).2 - (p (1 : Fin (4 : ℕ))).2), p (0 : Fin (4 : ℕ)), p (2 : Fin (4
        : ℕ)), p (3 : Fin (4 : ℕ))] ∧ p (0 : Fin (4 : ℕ)) = q (3 : Fin (4 : ℕ)) ∧ p (2 : Fin (4 :
        ℕ)) = q (1 : Fin (4 : ℕ)) ∧ p (3 : Fin (4 : ℕ)) = q (2 : Fin (4 : ℕ)) ∧ (q (1 : Fin (4 :
        ℕ))).1 < (q (3 : Fin (4 : ℕ))).1 ∧ (q (2 : Fin (4 : ℕ))).1 < (q (3 : Fin (4 : ℕ))).1) →
        (∃ (r : Fin 3) (g : BandPackingSymmetry), Nonempty (BandOrderedGeneralConfiguration
        (BandPackingSymmetryQuadrupleAction g ![q 0, q r.succ, q (r + 1).succ, q (r +
        2).succ]))))))) := by
  classical
  intro q hq hnoLine hatMostOneUnit buildConfiguration third
  rcases third with ⟨p, hthird⟩
  have hp := hthird.1
  have hsucc := hthird.2.1
  have h0 := hthird.2.2.1
  have h2 := hthird.2.2.2.1
  have h3 := hthird.2.2.2.2.1
  rcases BandOrientedBoundaryParentChain p hp with hsmall | horient
  · rcases hsmall with ⟨hroot2, hroot3⟩
    have hone1 := hroot2.resolve_left (by rw [h2]; exact hnoLine 1)
    have hone2 := hroot3.resolve_left (by rw [h3]; exact hnoLine 2)
    rw [h2] at hone1
    rw [h3] at hone2
    have bad := hatMostOneUnit 1 2 hone1 hone2
    omega
  · rcases horient with bd | db
    · refine ⟨2, ?_⟩
      rcases bd with ⟨t, ht, ht0, ht1, hlt⟩
      let u : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
      have hu := RetainedBoundaryDetails.huAt713 q hq
      have hnl' := RetainedBoundaryDetails.hnl'At720 q hnoLine
      have haum' := RetainedBoundaryDetails.haum'At723 q hatMostOneUnit p hthird
      have hs' := RetainedBoundaryDetails.hs'At727 q p hsucc
      have h0' : p 0 = u 1 := by simpa [u] using h0
      have h2' : p 2 = u 2 := by simpa [u] using h2
      have h3' : p 3 = u 3 := by simpa [u] using h3
      have hlt2' : (u 2).1 < (u 1).1 := by simpa [u] using hthird.2.2.2.2.2.1
      have hlt3' : (u 3).1 < (u 1).1 := by simpa [u] using hthird.2.2.2.2.2.2
      have hord' : (u 3).1 < (u 2).1 := by simpa [u, h2, h3] using hlt
      have hc := buildConfiguration u p t hu hnl' haum' hp hs' h0' h2' h3'
        hlt2' hlt3' ht (by simpa [u, h2] using ht0) (by simpa [u, h3] using ht1) hord'
      refine ⟨.identity, ?_⟩
      simpa [u, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction] using hc
    · refine ⟨2, ?_⟩
      rcases db with ⟨t, ht, ht0, ht1, hlt⟩
      let base : Fin 4 → CircleCoordinates := ![q 0, q 3, q 1, q 2]
      let u := BandPackingSymmetryQuadrupleAction .conjugate base
      let pp := BandPackingSymmetryQuadrupleAction .conjugate p
      let tt := BandPackingSymmetryQuadrupleAction .conjugate t
      have hb := RetainedBoundaryDetails.hb q hq
      have hu : ProperBandQuadruple u := BandPackingSymmetryProperCovariance .conjugate base hb
      have hp' : ProperBandQuadruple pp := BandPackingSymmetryProperCovariance .conjugate p hp
      have ht' : ProperBandQuadruple tt := BandPackingSymmetryProperCovariance .conjugate t ht
      have hnl' := RetainedBoundaryDetails.hnl'At757 q hnoLine
      have haum' := RetainedBoundaryDetails.haum'At761 q hatMostOneUnit p hthird
      have negOneSucc : (-1 : Fin 3).succ = 3 := by decide
      have negTwoSucc : (-2 : Fin 3).succ = 2 := by decide
      have hs' := RetainedBoundaryProof.hs'At631 q p hsucc negOneSucc negTwoSucc
      let reflect : CircleCoordinates → CircleCoordinates := fun C => (C.1, GaussianReflection
          C.2)
      have h0' := RetainedBoundaryDetails.h0'At771 q p h0 negOneSucc negTwoSucc
      have h2' := RetainedBoundaryDetails.h2'At774 q p h3 negOneSucc negTwoSucc
      have h3' := RetainedBoundaryDetails.h3'At777 q p h2 negOneSucc negTwoSucc
      have ht0' : tt 0 = u 2 := by simp [u, tt, base, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, ht0, h3]
      have ht1' : tt 1 = u 3 := by simp [u, tt, base, BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryReversesOrientation, BandPackingSymmetryCircleAction, ht1, h2]
      have hlt2' := RetainedBoundaryDetails.hlt2'At784 q p hthird
      have hlt3' := RetainedBoundaryDetails.hlt3'At787 q p hthird
      have hord' := RetainedBoundaryDetails.hord'At790 q p h2 h3 hlt
          negOneSucc negTwoSucc
      refine ⟨.conjugate, ?_⟩
      simpa [u, base] using buildConfiguration u pp tt hu hnl' haum' hp' hs' h0' h2' h3'
        hlt2' hlt3' ht' ht0' ht1' hord'

end RetainedBoundaryCases

theorem BandRetainedBoundaryGenealogy
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hnoLine : ∀ i : Fin 4, (q i).1 ≠ 0)
    (hatMostOneUnit : ∀ i j : Fin 4,
      (q i).1 = 1 → (q j).1 = 1 → i = j) :
    ∃ (r : Fin 3) (g : BandPackingSymmetry),
      Nonempty (BandOrderedGeneralConfiguration
        (BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ])) := by
-- BODY
  have curvatureBound := RetainedBoundaryProof.curvatureBound
  have positiveLarge := RetainedBoundaryDetails.positiveLarge curvatureBound
  have buildConfiguration := RetainedBoundaryProof.buildConfiguration
          positiveLarge
  rcases BandParentBoundaryGenealogy q hq with roots | first | second | third
  · rcases roots with roots | roots | roots
    · exact (hnoLine 2 roots.2.1).elim
    · exact (hnoLine 3 roots.2.2).elim
    · exact (hnoLine 1 roots.1).elim
  · have firstParentCase :
      ∃ (r : Fin 3) (g : BandPackingSymmetry),
      Nonempty (BandOrderedGeneralConfiguration
      (BandPackingSymmetryQuadrupleAction g
      ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ])) := RetainedBoundaryCases.firstParentCase
          q hq hnoLine hatMostOneUnit positiveLarge buildConfiguration first
    exact firstParentCase
  · have secondParentCase :
      ∃ (r : Fin 3) (g : BandPackingSymmetry),
      Nonempty (BandOrderedGeneralConfiguration
      (BandPackingSymmetryQuadrupleAction g
      ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ])) :=
          RetainedBoundaryCases.secondParentCase q hq hnoLine hatMostOneUnit buildConfiguration
              second
    exact secondParentCase
  · have thirdParentCase :
      ∃ (r : Fin 3) (g : BandPackingSymmetry),
      Nonempty (BandOrderedGeneralConfiguration
      (BandPackingSymmetryQuadrupleAction g
      ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ])) := RetainedBoundaryCases.thirdParentCase
          q hq hnoLine hatMostOneUnit buildConfiguration third
    exact thirdParentCase
end ApollonianSuperharmonic
end
