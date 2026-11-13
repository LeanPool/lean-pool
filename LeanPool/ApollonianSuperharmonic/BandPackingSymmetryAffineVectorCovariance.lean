/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProjectiveVectorCovariance

-- [TABLET NODE: BandPackingSymmetryAffineVectorCovariance]

/-!
# BandPackingSymmetryAffineVectorCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace AffineSymmetryCoordinates

private theorem circleCurvature :
    (by
      classical
      exact
        ∀ h : BandPackingSymmetry, ∀ C : CircleCoordinates, (BandPackingSymmetryCircleAction h
            C).1 = C.1 ) := by
  classical
  intro h
  induction h with
  | identity => intro C; rfl
  | negate => intro C; rfl
  | conjugate => intro C; rfl
  | shift w => intro C; rfl
  | comp h k ih ih' =>
      intro C
      simp [BandPackingSymmetryCircleAction, ih, ih']

private theorem affineFacts :
    (by
      classical
      exact
        (∀ h : BandPackingSymmetry, ∀ C : CircleCoordinates, (BandPackingSymmetryCircleAction h
            C).1 = C.1) → (∀ (h : BandPackingSymmetry), ∀ (D : CircleCoordinates), ∀ (E :
            CircleCoordinates), ∀ (v : GaussianInt), ∀ (a : GaussianInt), Zsqrtd.norm v = D.1 +
            E.1 → 2 * v * a = D.2 + E.2 → (BandPackingSymmetryAffineVectorAction h (v, a)).1 =
            BandPackingSymmetryVectorAction h v ∧ Zsqrtd.norm
            (BandPackingSymmetryAffineVectorAction h (v, a)).1 = D.1 + E.1 ∧ 2 *
            (BandPackingSymmetryAffineVectorAction h (v, a)).1 *
            (BandPackingSymmetryAffineVectorAction h (v, a)).2 = (BandPackingSymmetryCircleAction
            h D).2 + (BandPackingSymmetryCircleAction h E).2) ) := by
  classical
  intro circleCurvature h
  induction h with
  | identity =>
      intro D E v a hv ha
      simpa [BandPackingSymmetryAffineVectorAction,
        BandPackingSymmetryVectorAction, BandPackingSymmetryCircleAction] using
        ⟨hv, ha⟩
  | shift w =>
      intro D E v a hv ha
      simp only [BandPackingSymmetryAffineVectorAction, BandPackingSymmetryVectorAction,
          Int.reduceNeg, BandPackingSymmetryCircleAction, true_and]
      constructor
      · exact hv
      · have reflectionProduct : v * GaussianReflection v =
            (Zsqrtd.norm v : GaussianInt) := by
            ext <;> simp [GaussianReflection, Zsqrtd.norm]; ring
        rw [mul_add, ha]
        calc
          D.2 + E.2 + 2 * v * (w * GaussianReflection v) =
              D.2 + E.2 + 2 * w * (v * GaussianReflection v) := by ring
          _ = D.2 + E.2 + 2 * w * (D.1 + E.1) := by
            rw [reflectionProduct, hv]
            simp only [Int.cast_add]
          _ = D.2 + 2 * (D.1 : GaussianInt) * w +
              (E.2 + 2 * (E.1 : GaussianInt) * w) := by
            ring
  | negate =>
      intro D E v a hv ha
      have quarterNorm : Zsqrtd.norm (GaussianQuarterTurn v) =
            Zsqrtd.norm v := by
            simp [GaussianQuarterTurn, Zsqrtd.norm]
            ring
      have quarterProduct :
            2 * GaussianQuarterTurn v * GaussianQuarterTurn a = -(2 * v * a) := by
            ext <;> simp [GaussianQuarterTurn]
      have quarterSum : 2 * GaussianQuarterTurn v * GaussianQuarterTurn a =
            -D.2 + -E.2 := by
        rw [quarterProduct, ha]
        ring
      simpa [BandPackingSymmetryAffineVectorAction,
        BandPackingSymmetryVectorAction, BandPackingSymmetryCircleAction] using
        ⟨by rw [quarterNorm, hv], quarterSum⟩
  | conjugate =>
      intro D E v a hv ha
      have reflectionNorm : Zsqrtd.norm (GaussianReflection v) =
            Zsqrtd.norm v := by
            simp [GaussianReflection, Zsqrtd.norm]
      have reflectionProduct : 2 * GaussianReflection v * GaussianReflection a =
              GaussianReflection (2 * v * a) := by
            ext <;> simp [GaussianReflection]; ring_nf
      have reflectionSum : 2 * GaussianReflection v * GaussianReflection a =
            GaussianReflection D.2 + GaussianReflection E.2 := by
        rw [reflectionProduct, ha]
        ext <;> simp [GaussianReflection]; ring
      simpa [BandPackingSymmetryAffineVectorAction,
        BandPackingSymmetryVectorAction, BandPackingSymmetryCircleAction] using
        ⟨by rw [reflectionNorm, hv], reflectionSum⟩
  | comp h k ih ih' =>
      intro D E v a hv ha
      have first := ih' D E v a hv ha
      have second := ih (BandPackingSymmetryCircleAction k D)
          (BandPackingSymmetryCircleAction k E)
          (BandPackingSymmetryAffineVectorAction k (v, a)).1
          (BandPackingSymmetryAffineVectorAction k (v, a)).2
          (by
            calc
              Zsqrtd.norm (BandPackingSymmetryAffineVectorAction k (v, a)).1 =
                  D.1 + E.1 := first.2.1
              _ = (BandPackingSymmetryCircleAction k D).1 +
                  (BandPackingSymmetryCircleAction k E).1 := by
                rw [circleCurvature k D, circleCurvature k E]) first.2.2
      have secondFirst := second.1
      have secondVector :
          (BandPackingSymmetryAffineVectorAction h
            ((BandPackingSymmetryAffineVectorAction k (v, a)).1,
              (BandPackingSymmetryAffineVectorAction k (v, a)).2)).1 =
            BandPackingSymmetryVectorAction h
              (BandPackingSymmetryVectorAction k v) := by
        calc
          _ = BandPackingSymmetryVectorAction h
              (BandPackingSymmetryAffineVectorAction k (v, a)).1 := secondFirst
          _ = _ := by rw [first.1]
      have secondNorm : Zsqrtd.norm
          (BandPackingSymmetryAffineVectorAction h
            ((BandPackingSymmetryAffineVectorAction k (v, a)).1,
              (BandPackingSymmetryAffineVectorAction k (v, a)).2)).1 =
          D.1 + E.1 := by
        rw [second.2.1, circleCurvature k D, circleCurvature k E]
      have secondProduct := second.2.2
      have pairEta : ∀ x : GaussianInt × GaussianInt, (x.1, x.2) = x := by
        intro x
        cases x
        rfl
      rw [pairEta] at secondVector secondNorm secondProduct
      simpa [BandPackingSymmetryAffineVectorAction,
        BandPackingSymmetryVectorAction, BandPackingSymmetryCircleAction,
        Prod.eta] using ⟨secondVector, secondNorm, secondProduct⟩

private theorem epsilonSquare :
    (by
      classical
      exact
        ∀ (negative : Bool),
        let epsilon : GaussianInt := if negative then -1 else 1
        epsilon * epsilon = 1 ) := by
  classical
  intro negative epsilon
  dsimp [epsilon]
  split <;> simp

private theorem slopeCancel :
    (by
      classical
      exact
        ∀ (negative : Bool),
        let epsilon : GaussianInt := if negative then -1 else 1
        (epsilon * epsilon = 1) → (∀ (V : GaussianInt), ∀ (A : GaussianInt), ∀ (b : GaussianInt),
            V ≠ 0 → 2 * V * A = 2 * (epsilon * V) * b → b = epsilon * A) ) := by
  classical
  intro negative epsilon epsilonSquare V A b hV hprod
  have htwo : (2 : GaussianInt) * V ≠ 0 := by
    exact mul_ne_zero (by norm_num) hV
  have hmain : ((2 : GaussianInt) * V) * (epsilon * b) =
      ((2 : GaussianInt) * V) * A := by
    calc
      ((2 : GaussianInt) * V) * (epsilon * b) =
          2 * (epsilon * V) * b := by ring
      _ = 2 * V * A := hprod.symm
      _ = ((2 : GaussianInt) * V) * A := by ring
  have hmain' := (mul_left_cancel₀ htwo hmain)
  calc
    b = 1 * b := by simp
    _ = (epsilon * epsilon) * b := by rw [epsilonSquare]
    _ = epsilon * (epsilon * b) := by ring
    _ = epsilon * A := by rw [hmain']

private theorem sourceNorm :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (i : Fin 4), ∀ (j : Fin
            4), i ≠ j → 0 < (q i).1 + (q j).1 → Zsqrtd.norm (BandVectors.1 (q i) (q j)) = (q i).1
            + (q j).1) ) := by
  classical
  intro q hq i j hij hpos
  have hs := (VectorSquareProduct q hq.1 i j hij).1
  have ht := TangencyCoordinateIdentity q hq.1 i j hij
  have heq : Zsqrtd.norm (BandVectors.1 (q i) (q j)) ^ 2 =
      ((q i).1 + (q j).1) ^ 2 := by
    calc
      Zsqrtd.norm (BandVectors.1 (q i) (q j)) ^ 2 =
          Zsqrtd.norm (BandVectors.1 (q i) (q j) ^ 2) := by
            simpa only [pow_two] using (Zsqrtd.norm_mul
              (BandVectors.1 (q i) (q j)) (BandVectors.1 (q i) (q j))).symm
      _ = Zsqrtd.norm ((q j).1 • (q i).2 - (q i).1 • (q j).2) := by rw [hs]
      _ = _ := ht
  have hn : 0 ≤ Zsqrtd.norm (BandVectors.1 (q i) (q j)) :=
    Zsqrtd.norm_nonneg (by norm_num) _
  nlinarith

private theorem parentPositive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (r : Fin 3), ∀ (s : Fin
            3), r ≠ s → 0 < (q r.succ).1 + (q s.succ).1) ) := by
  classical
  intro q hq r s hrs
  have hc := ProperBandCurvatureStructure q hq
  have hr := hc.2.1 r
  have hs := hc.2.1 s
  by_contra bad
  have hrz : (q r.succ).1 = 0 := by omega
  have hsz : (q s.succ).1 = 0 := by omega
  exact hrs (hc.2.2 r s hrz hsz)

private theorem incomingFacts :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
            ((∀ (h : BandPackingSymmetry), ∀ (D : CircleCoordinates), ∀ (E : CircleCoordinates),
            ∀ (v : GaussianInt), ∀ (a : GaussianInt), Zsqrtd.norm v = D.1 + E.1 → 2 * v * a = D.2
            + E.2 → (BandPackingSymmetryAffineVectorAction h (v, a)).1 =
            BandPackingSymmetryVectorAction h v ∧ Zsqrtd.norm
            (BandPackingSymmetryAffineVectorAction h (v, a)).1 = D.1 + E.1 ∧ 2 *
            (BandPackingSymmetryAffineVectorAction h (v, a)).1 *
            (BandPackingSymmetryAffineVectorAction h (v, a)).2 = (BandPackingSymmetryCircleAction
            h D).2 + (BandPackingSymmetryCircleAction h E).2) → ((∀ (i : Fin 4), ∀ (j : Fin 4), i
            ≠ j → 0 < (q i).1 + (q j).1 → Zsqrtd.norm (BandVectors.1 (q i) (q j)) = (q i).1 + (q
            j).1) → (∀ (j : Fin 4), j ≠ 0 → (BandPackingSymmetryAffineVectorAction g
            (BandVectors.1 (q j) (q 0), BandVectors.2 (q j) (q 0))).1 ≠ 0))) ) := by
  classical
  intro g q hq affineFacts sourceNorm j hj
  have hc := ProperBandCurvatureStructure q hq
  have hpos : 0 < (q j).1 + (q 0).1 := by
    have hnon : 0 ≤ (q j).1 := by
      obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      exact hc.2.1 k
    omega
  have hv := affineFacts g (q j) (q 0)
    (BandVectors.1 (q j) (q 0)) (BandVectors.2 (q j) (q 0))
    (sourceNorm j 0 hj hpos)
    (VectorSquareProduct q hq.1 j 0 hj).2
  intro hz
  have := hv.2.1
  rw [hz] at this
  have : Zsqrtd.norm (0 : GaussianInt) = 0 := by simp
  omega

private theorem cyclicFacts :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) →
            ((∀ (h : BandPackingSymmetry), ∀ (D : CircleCoordinates), ∀ (E : CircleCoordinates),
            ∀ (v : GaussianInt), ∀ (a : GaussianInt), Zsqrtd.norm v = D.1 + E.1 → 2 * v * a = D.2
            + E.2 → (BandPackingSymmetryAffineVectorAction h (v, a)).1 =
            BandPackingSymmetryVectorAction h v ∧ Zsqrtd.norm
            (BandPackingSymmetryAffineVectorAction h (v, a)).1 = D.1 + E.1 ∧ 2 *
            (BandPackingSymmetryAffineVectorAction h (v, a)).1 *
            (BandPackingSymmetryAffineVectorAction h (v, a)).2 = (BandPackingSymmetryCircleAction
            h D).2 + (BandPackingSymmetryCircleAction h E).2) → ((∀ (i : Fin 4), ∀ (j : Fin 4), i
            ≠ j → 0 < (q i).1 + (q j).1 → Zsqrtd.norm (BandVectors.1 (q i) (q j)) = (q i).1 + (q
            j).1) → (∀ (j : Fin 4), ∀ (k : Fin 4), j ≠ k → (BandPackingSymmetryAffineVectorAction
            g (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).1 ≠ 0))) ) := by
  classical
  intro g q hq affineFacts sourceNorm j k hjk
  have hc := ProperBandCurvatureStructure q hq
  have hpos : 0 < (q j).1 + (q k).1 := by
    by_cases hj : j = 0
    · subst j
      by_cases hk : k = 0
      · exact (hjk hk.symm).elim
      · obtain ⟨s, rfl⟩ := Fin.eq_succ_of_ne_zero hk
        have hp := hc.1
        have hs := hc.2.1 s
        exact add_pos_of_pos_of_nonneg hp hs
    · by_cases hk : k = 0
      · subst k
        obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hj
        have hp := hc.1
        have hr := hc.2.1 r
        simpa [add_comm] using add_pos_of_pos_of_nonneg hp hr
      · obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hj
        obtain ⟨s, rfl⟩ := Fin.eq_succ_of_ne_zero hk
        have hr := hc.2.1 r
        have hs := hc.2.1 s
        by_contra bad
        have hrz : (q r.succ).1 = 0 := by omega
        have hsz : (q s.succ).1 = 0 := by omega
        have : r = s := hc.2.2 r s hrz hsz
        exact hjk (by simp [this])
  have hv := affineFacts g (q j) (q k)
    (BandVectors.1 (q j) (q k)) (BandVectors.2 (q j) (q k))
    (sourceNorm j k hjk hpos)
    (VectorSquareProduct q hq.1 j k hjk).2
  intro hz
  have hnorm := hv.2.1
  rw [hz] at hnorm
  have hz0 : Zsqrtd.norm (0 : GaussianInt) = 0 := by simp
  omega

private theorem incomingSlope :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (negative : Bool), ∀ (i
            : Fin (3 : ℕ)),
        let epsilon : GaussianInt := if negative then -1 else 1
        (∀ (V : GaussianInt), ∀ (A : GaussianInt), ∀ (b : GaussianInt), V ≠ 0 → 2 * V * A = 2 *
            (epsilon * V) * b → b = epsilon * A) → ((∀ (j : Fin 4), j ≠ 0 →
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q j) (q 0), BandVectors.2 (q
            j) (q 0))).1 ≠ 0) → ((BandVectors.1 (BandPackingSymmetryQuadrupleAction g q ((fun (i
            : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true then -i else i)
            i).succ) (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) = (if negative =
            true then (-1 : GaussianInt) else (1 : GaussianInt)) *
            BandPackingSymmetryVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) ∧
            (BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i).succ) = (if
            negative = true then (-1 : GaussianInt) else (1 : GaussianInt)) * if
            BandPackingSymmetryReversesOrientation g = true then -BandPackingSymmetryVectorAction
            g (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)) else
            BandPackingSymmetryVectorAction g (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) ∧
            BandVectors.1 (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i + (2 : Fin (3 :
            ℕ))).succ) (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i + (1 : Fin (3 :
            ℕ))).succ) = (if negative = true then (-1 : GaussianInt) else (1 : GaussianInt)) * if
            BandPackingSymmetryReversesOrientation g = true then GaussianQuarterTurn
            (BandPackingSymmetryVectorAction g (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q
            (i + (1 : Fin (3 : ℕ))).succ))) else BandPackingSymmetryVectorAction g (BandVectors.1
            (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))) → ((BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            = true then -i else i).succ) (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 :
            ℕ))) ^ (2 : ℕ) = (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))).1 •
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            = true then -i else i).succ).2 - (BandPackingSymmetryQuadrupleAction g q (if
            BandPackingSymmetryReversesOrientation g = true then -i else i).succ).1 •
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))).2 ∧ (2 : GaussianInt) *
            BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (if
            BandPackingSymmetryReversesOrientation g = true then -i else i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) * BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            = true then -i else i).succ) (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 :
            ℕ))) = (BandPackingSymmetryQuadrupleAction g q (if
            BandPackingSymmetryReversesOrientation g = true then -i else i).succ).2 +
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))).2) →
            (((BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).1 =
            BandPackingSymmetryVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) ∧
            Zsqrtd.norm (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0
            : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).1 = (q i.succ).1 +
            (q (0 : Fin (4 : ℕ))).1 ∧ (2 : GaussianInt) * (BandPackingSymmetryAffineVectorAction
            g (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 :
            Fin (4 : ℕ))))).1 * (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2 =
            (BandPackingSymmetryCircleAction g (q i.succ)).2 + (BandPackingSymmetryCircleAction g
            (q (0 : Fin (4 : ℕ)))).2) → (BandVectors.2 (BandPackingSymmetryQuadrupleAction g q
            (if BandPackingSymmetryReversesOrientation g = true then -i else i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) = epsilon *
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2))))) ) := by
  classical
  intro g q negative i epsilon slopeCancel incomingFacts hspatial incomingProduct incomingAffine
  exact slopeCancel
    (BandPackingSymmetryAffineVectorAction g
      (BandVectors.1 (q i.succ) (q 0), BandVectors.2 (q i.succ) (q 0))).1
    (BandPackingSymmetryAffineVectorAction g
      (BandVectors.1 (q i.succ) (q 0), BandVectors.2 (q i.succ) (q 0))).2
    (BandVectors.2 (BandPackingSymmetryQuadrupleAction g q
      (if BandPackingSymmetryReversesOrientation g then -i else i).succ)
      (BandPackingSymmetryQuadrupleAction g q 0))
    (incomingFacts i.succ (by simp))
    (by
      calc
        2 * _ * _ = (BandPackingSymmetryCircleAction g (q i.succ)).2 +
            (BandPackingSymmetryCircleAction g (q 0)).2 := incomingAffine.2.2
        _ = (BandPackingSymmetryQuadrupleAction g q
            (if BandPackingSymmetryReversesOrientation g then -i else i).succ).2 +
            (BandPackingSymmetryQuadrupleAction g q 0).2 := by
              cases hrev : BandPackingSymmetryReversesOrientation g <;>
                fin_cases i <;>
                simp [hrev, BandPackingSymmetryQuadrupleAction] <;>
                congr 1
        _ = 2 * (epsilon * _) * _ := by
          rw [← incomingProduct.2, hspatial.1, incomingAffine.1]
          )

private theorem unitCancel :
    (by
      classical
      exact
        ∀ (V : GaussianInt), ∀ (A : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d
            : GaussianInt), V ≠ 0 → c * d = 1 → 2 * V * A = 2 * (c * V) * b → b = d * A ) := by
  classical
  intro V A b c d hV hcd hp
  have htwo : (2 : GaussianInt) * V ≠ 0 := mul_ne_zero (by norm_num) hV
  have hh : ((2 : GaussianInt) * V) * (c * b) =
      ((2 : GaussianInt) * V) * A := by
    calc
      ((2 : GaussianInt) * V) * (c * b) = 2 * (c * V) * b := by ring
      _ = 2 * V * A := hp.symm
      _ = ((2 : GaussianInt) * V) * A := by ring
  have hh' := mul_left_cancel₀ htwo hh
  have hdc : d * c = 1 := by simpa [mul_comm] using hcd
  calc
    b = 1 * b := by simp
    _ = (d * c) * b := by rw [hdc]
    _ = d * (c * b) := by ring
    _ = d * A := by rw [hh']

private theorem hprodAt446 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (negative : Bool),
            (BandPackingSymmetryScopedPhase g q negative) → (∀ (i : Fin (3 : ℕ)),
        let epsilon : GaussianInt := if negative then -1 else 1
        (epsilon * epsilon = 1) → ((∀ (V : GaussianInt), ∀ (A : GaussianInt), ∀ (b :
            GaussianInt), V ≠ 0 → 2 * V * A = 2 * (epsilon * V) * b → b = epsilon * A) →
            ((BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (if
            BandPackingSymmetryReversesOrientation g = true then -i else i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) ^ (2 : ℕ) =
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))).1 •
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            = true then -i else i).succ).2 - (BandPackingSymmetryQuadrupleAction g q (if
            BandPackingSymmetryReversesOrientation g = true then -i else i).succ).1 •
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))).2 ∧ (2 : GaussianInt) *
            BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (if
            BandPackingSymmetryReversesOrientation g = true then -i else i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) * BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            = true then -i else i).succ) (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 :
            ℕ))) = (BandPackingSymmetryQuadrupleAction g q (if
            BandPackingSymmetryReversesOrientation g = true then -i else i).succ).2 +
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))).2) →
            (((BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).1 =
            BandPackingSymmetryVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) ∧
            Zsqrtd.norm (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0
            : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).1 = (q i.succ).1 +
            (q (0 : Fin (4 : ℕ))).1 ∧ (2 : GaussianInt) * (BandPackingSymmetryAffineVectorAction
            g (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 :
            Fin (4 : ℕ))))).1 * (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2 =
            (BandPackingSymmetryCircleAction g (q i.succ)).2 + (BandPackingSymmetryCircleAction g
            (q (0 : Fin (4 : ℕ)))).2) → ((BandVectors.2 (BandPackingSymmetryQuadrupleAction g q
            (if BandPackingSymmetryReversesOrientation g = true then -i else i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) = epsilon *
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2) →
            ((BandPackingSymmetryReversesOrientation g = true) → (((BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q (-i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) = if negative = true then
            -BandPackingSymmetryVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))
            else BandPackingSymmetryVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))))) ∧ (BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q (-i).succ) = -if negative = true then
            -BandPackingSymmetryVectorAction g (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))
            else BandPackingSymmetryVectorAction g (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            i.succ))) ∧ BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (-i + (2 : Fin (3 :
            ℕ))).succ) (BandPackingSymmetryQuadrupleAction g q (-i + (1 : Fin (3 : ℕ))).succ) =
            if negative = true then -GaussianQuarterTurn (BandPackingSymmetryVectorAction g
            (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))
            else GaussianQuarterTurn (BandPackingSymmetryVectorAction g (BandVectors.1 (q (i + (2
            : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let j : Fin 4 := (i + 2).succ
        let k : Fin 4 := (i + 1).succ
        let V := (BandPackingSymmetryAffineVectorAction g
          (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).1
        let A := (BandPackingSymmetryAffineVectorAction g
          (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).2
        (j ≠ k) → (((BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q j) (q k),
            BandVectors.2 (q j) (q k))).1 = BandPackingSymmetryVectorAction g (BandVectors.1 (q
            j) (q k)) ∧ Zsqrtd.norm (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q j)
            (q k), BandVectors.2 (q j) (q k))).1 = (q j).1 + (q k).1 ∧ (2 : GaussianInt) *
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q j) (q k), BandVectors.2 (q
            j) (q k))).1 * (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q j) (q k),
            BandVectors.2 (q j) (q k))).2 = (BandPackingSymmetryCircleAction g (q j)).2 +
            (BandPackingSymmetryCircleAction g (q k)).2) → ((BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q (-i + (2 : Fin (3 : ℕ))).succ)
            (BandPackingSymmetryQuadrupleAction g q (-i + (1 : Fin (3 : ℕ))).succ) ^ (2 : ℕ) =
            (BandPackingSymmetryQuadrupleAction g q (-i + (1 : Fin (3 : ℕ))).succ).1 •
            (BandPackingSymmetryQuadrupleAction g q (-i + (2 : Fin (3 : ℕ))).succ).2 -
            (BandPackingSymmetryQuadrupleAction g q (-i + (2 : Fin (3 : ℕ))).succ).1 •
            (BandPackingSymmetryQuadrupleAction g q (-i + (1 : Fin (3 : ℕ))).succ).2 ∧ (2 :
            GaussianInt) * BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (-i + (2 : Fin
            (3 : ℕ))).succ) (BandPackingSymmetryQuadrupleAction g q (-i + (1 : Fin (3 :
            ℕ))).succ) * BandVectors.2 (BandPackingSymmetryQuadrupleAction g q (-i + (2 : Fin (3
            : ℕ))).succ) (BandPackingSymmetryQuadrupleAction g q (-i + (1 : Fin (3 : ℕ))).succ) =
            (BandPackingSymmetryQuadrupleAction g q (-i + (2 : Fin (3 : ℕ))).succ).2 +
            (BandPackingSymmetryQuadrupleAction g q (-i + (1 : Fin (3 : ℕ))).succ).2) → (2 * V *
            A = 2 * (epsilon * GaussianQuarterTurn V) * (BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (-i + 2).succ)
            (BandPackingSymmetryQuadrupleAction g q (-i + 1).succ))))))))))))) ) := by
  classical
  intro g q negative hphase i epsilon epsilonSquare slopeCancel incomingProduct incomingAffine
      incomingSlope hrev hspatial j k V A hjk aff prod
  calc
    2 * V * A = (BandPackingSymmetryCircleAction g (q j)).2 +
        (BandPackingSymmetryCircleAction g (q k)).2 := aff.2.2
    _ = (BandPackingSymmetryQuadrupleAction g q (-i + 2).succ).2 +
        (BandPackingSymmetryQuadrupleAction g q (-i + 1).succ).2 := by
          fin_cases i
          · have firstIndex : (-(0 : Fin 3) + 2) = 2 := by decide
            have secondIndex : (-(0 : Fin 3) + 1) = 1 := by decide
            have negativeOne : (-(1 : Fin 3)) = 2 := by decide
            have negativeTwo : (-(2 : Fin 3)) = 1 := by decide
            simp [j, k, BandPackingSymmetryQuadrupleAction, hrev,
              negativeOne, negativeTwo]; ring
          · have firstIndex : (-(1 : Fin 3) + 2) = 1 := by decide
            have secondIndex : (-(1 : Fin 3) + 1) = 0 := by decide
            have negativeOne : (-(1 : Fin 3)) = 2 := by decide
            simp [j, k, BandPackingSymmetryQuadrupleAction, hrev,
              negativeOne]; ring
          · have firstIndex : (-(2 : Fin 3) + 2) = 0 := by decide
            have secondIndex : (-(2 : Fin 3) + 1) = 2 := by decide
            have negativeTwo : (-(2 : Fin 3)) = 1 := by decide
            simp [j, k, BandPackingSymmetryQuadrupleAction, hrev,
              negativeTwo]; ring
    _ = 2 * (epsilon * GaussianQuarterTurn V) * _ := by
      rw [← prod.2]
      let W := GaussianQuarterTurn (BandPackingSymmetryVectorAction g
          (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ)))
      have hf : (if negative then -W else W) =
          epsilon * GaussianQuarterTurn V := by
        have hqv : GaussianQuarterTurn
            (BandPackingSymmetryVectorAction g
              (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ))) =
            GaussianQuarterTurn V := by
          congr 1
          simpa [V] using aff.1.symm
        dsimp [W]
        rw [hqv]
        cases negative <;> simp [epsilon]
      rw [hspatial.2.2]
      rw [hf]

private theorem hu :
    (by
      classical
      exact
        ∀ (negative : Bool),
          let epsilon :=
            if negative = true then (-1 : GaussianInt) else (1 : GaussianInt);
          epsilon * GaussianQuarterTurn (1 : GaussianInt) *
              (-epsilon *
                GaussianQuarterTurn (1 : GaussianInt)) =
            (1 : GaussianInt)) := by
  classical
  intro negative epsilon
  cases negative <;> ext <;> norm_num [epsilon, GaussianQuarterTurn]

private theorem quarterMul :
    (by
      classical
      exact
        ∀ z : GaussianInt, GaussianQuarterTurn z = GaussianQuarterTurn 1 * z ) := by
  classical
  intro z
  ext <;> simp [GaussianQuarterTurn]

private theorem slopeIndex :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin (3 : ℕ)),
        let j : Fin 4 := (i + 2).succ
        let k : Fin 4 := (i + 1).succ
        let A := (BandPackingSymmetryAffineVectorAction g
          (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).2
        (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q (i + 2).succ) (q (i +
            1).succ), BandVectors.2 (q (i + 2).succ) (q (i + 1).succ))).2 = A ) := by
  classical
  intro g q i j k A
  rfl

private theorem hprodAt542 :
    (by
      classical
        exact
        ∀ (g : BandPackingSymmetry),
          ∀ (q : Fin 4 → CircleCoordinates),
            ∀ (negative : Bool),
              (∀ (i : Fin (3 : ℕ)),
                let epsilon : GaussianInt := if negative then -1 else 1;
                ((¬BandPackingSymmetryReversesOrientation g = true) →
                  (((BandVectors.1 (BandPackingSymmetryQuadrupleAction g q i.succ)
                          (BandPackingSymmetryQuadrupleAction g q
                            (0 : Fin (4 : ℕ))) =
                        if negative = true then
                          -BandPackingSymmetryVectorAction g
                              (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))
                        else
                          BandPackingSymmetryVectorAction g
                            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) ∧
                      (BandVectors.1
                            (BandPackingSymmetryQuadrupleAction g q
                              (0 : Fin (4 : ℕ)))
                            (BandPackingSymmetryQuadrupleAction g q i.succ) =
                          if negative = true then
                            -BandPackingSymmetryVectorAction g
                                (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))
                          else
                            BandPackingSymmetryVectorAction g
                              (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) ∧
                        BandVectors.1
                            (BandPackingSymmetryQuadrupleAction g q
                              (i + (2 : Fin (3 : ℕ))).succ)
                            (BandPackingSymmetryQuadrupleAction g q
                              (i + (1 : Fin (3 : ℕ))).succ) =
                          if negative = true then
                            -BandPackingSymmetryVectorAction g
                                (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
                                  (q (i + (1 : Fin (3 : ℕ))).succ))
                          else
                            BandPackingSymmetryVectorAction g
                              (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ)
                                (q (i + (1 : Fin (3 : ℕ))).succ))) →
                    (let j : Fin 4 := (i + 2).succ;
                    let k : Fin 4 := (i + 1).succ;
                    let V :=
                      (BandPackingSymmetryAffineVectorAction g
                          (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).1;
                    let A :=
                      (BandPackingSymmetryAffineVectorAction g
                          (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).2;
                    (((BandPackingSymmetryAffineVectorAction g
                              (BandVectors.1 (q j) (q k),
                                BandVectors.2 (q j) (q k))).1 =
                          BandPackingSymmetryVectorAction g
                            (BandVectors.1 (q j) (q k)) ∧
                        Zsqrtd.norm
                              (BandPackingSymmetryAffineVectorAction g
                                  (BandVectors.1 (q j) (q k),
                                    BandVectors.2 (q j) (q k))).1 =
                            (q j).1 + (q k).1 ∧
                          (2 : GaussianInt) *
                                (BandPackingSymmetryAffineVectorAction g
                                    (BandVectors.1 (q j) (q k),
                                      BandVectors.2 (q j) (q k))).1 *
                              (BandPackingSymmetryAffineVectorAction g
                                  (BandVectors.1 (q j) (q k),
                                    BandVectors.2 (q j) (q k))).2 =
                            (BandPackingSymmetryCircleAction g (q j)).2 +
                              (BandPackingSymmetryCircleAction g (q k)).2) →
                      ((BandVectors.1
                                (BandPackingSymmetryQuadrupleAction g q
                                  (i + (2 : Fin (3 : ℕ))).succ)
                                (BandPackingSymmetryQuadrupleAction g q
                                  (i + (1 : Fin (3 : ℕ))).succ) ^
                              (2 : ℕ) =
                            (BandPackingSymmetryQuadrupleAction g q
                                    (i + (1 : Fin (3 : ℕ))).succ).1 •
                                (BandPackingSymmetryQuadrupleAction g q
                                    (i + (2 : Fin (3 : ℕ))).succ).2 -
                              (BandPackingSymmetryQuadrupleAction g q
                                    (i + (2 : Fin (3 : ℕ))).succ).1 •
                                (BandPackingSymmetryQuadrupleAction g q
                                    (i + (1 : Fin (3 : ℕ))).succ).2 ∧
                          (2 : GaussianInt) *
                                BandVectors.1
                                  (BandPackingSymmetryQuadrupleAction g q
                                    (i + (2 : Fin (3 : ℕ))).succ)
                                  (BandPackingSymmetryQuadrupleAction g q
                                    (i + (1 : Fin (3 : ℕ))).succ) *
                              BandVectors.2
                                (BandPackingSymmetryQuadrupleAction g q
                                  (i + (2 : Fin (3 : ℕ))).succ)
                                (BandPackingSymmetryQuadrupleAction g q
                                  (i + (1 : Fin (3 : ℕ))).succ) =
                            (BandPackingSymmetryQuadrupleAction g q
                                  (i + (2 : Fin (3 : ℕ))).succ).2 +
                              (BandPackingSymmetryQuadrupleAction g q
                                  (i + (1 : Fin (3 : ℕ))).succ).2) →
                        (2 * V * A =
                          2 * (epsilon * V) *
                            (BandVectors.2
                              (BandPackingSymmetryQuadrupleAction g q (i + 2).succ)
                              (BandPackingSymmetryQuadrupleAction g q
                                (i + 1).succ)))))))))) := by
  classical
  intro g q negative i epsilon hrev hspatial j k V A aff prod
  calc
    2 * V * A = (BandPackingSymmetryCircleAction g (q j)).2 +
        (BandPackingSymmetryCircleAction g (q k)).2 := aff.2.2
    _ = (BandPackingSymmetryQuadrupleAction g q (i + 2).succ).2 +
        (BandPackingSymmetryQuadrupleAction g q (i + 1).succ).2 := by
        fin_cases i <;> simp [j, k, BandPackingSymmetryQuadrupleAction, hrev,
          ]
    _ = 2 * (epsilon * V) * _ := by
      rw [← prod.2]
      have hf : ((if negative then
          -BandPackingSymmetryVectorAction g
            (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ))
        else BandPackingSymmetryVectorAction g
          (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ)))) =
          epsilon * V := by
        have hv' : BandPackingSymmetryVectorAction g
            (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ)) = V := by
          simpa [V, j, k] using aff.1.symm
        rw [hv']
        cases negative <;> simp [epsilon]
      rw [hspatial.2.2]
      rw [hf]

end AffineSymmetryCoordinates

theorem BandPackingSymmetryAffineVectorCovariance
    (g : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    let q' := BandPackingSymmetryQuadrupleAction g q
    let sigma : Fin 3 → Fin 3 := fun i =>
      if BandPackingSymmetryReversesOrientation g then -i else i
    ∃ negative : Bool,
      BandPackingSymmetryScopedPhase g q negative ∧
      ∀ i : Fin 3,
        let e : GaussianInt := if negative then -1 else 1
        let incoming := BandPackingSymmetryAffineVectorAction g
          (BandVectors.1 (q i.succ) (q 0),
            BandVectors.2 (q i.succ) (q 0))
        let cyclic := BandPackingSymmetryAffineVectorAction g
          (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)),
            BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ)))
        BandVectors.2 (q' (sigma i).succ) (q' 0) = e * incoming.2 ∧
        BandVectors.2 (q' ((sigma i + 2).succ))
            (q' ((sigma i + 1).succ)) =
          e * (if BandPackingSymmetryReversesOrientation g then
            -GaussianQuarterTurn cyclic.2 else cyclic.2) := by
-- BODY
  dsimp
  have circleCurvature := AffineSymmetryCoordinates.circleCurvature
  have affineFacts : ∀ (h : BandPackingSymmetry) (D E : CircleCoordinates)
      (v a : GaussianInt),
      Zsqrtd.norm v = D.1 + E.1 → 2 * v * a = D.2 + E.2 →
      (BandPackingSymmetryAffineVectorAction h (v, a)).1 =
          BandPackingSymmetryVectorAction h v ∧
      Zsqrtd.norm (BandPackingSymmetryAffineVectorAction h (v, a)).1 = D.1 + E.1 ∧
      2 * (BandPackingSymmetryAffineVectorAction h (v, a)).1 *
          (BandPackingSymmetryAffineVectorAction h (v, a)).2 =
        (BandPackingSymmetryCircleAction h D).2 +
          (BandPackingSymmetryCircleAction h E).2 := AffineSymmetryCoordinates.affineFacts
              circleCurvature
  obtain ⟨negative, hphase, _⟩ :=
    BandPackingSymmetryProjectiveVectorCovariance g q hq
  refine ⟨negative, hphase, ?_⟩
  intro i
  let epsilon : GaussianInt := if negative then -1 else 1
  have epsilonSquare : epsilon * epsilon = 1 := AffineSymmetryCoordinates.epsilonSquare negative
  have slopeCancel : ∀ (V A b : GaussianInt),
      V ≠ 0 → 2 * V * A = 2 * (epsilon * V) * b → b = epsilon * A :=
          AffineSymmetryCoordinates.slopeCancel negative epsilonSquare
  have sourceNorm : ∀ (i j : Fin 4), i ≠ j →
      0 < (q i).1 + (q j).1 →
      Zsqrtd.norm (BandVectors.1 (q i) (q j)) = (q i).1 + (q j).1 :=
          AffineSymmetryCoordinates.sourceNorm q hq
  have parentPositive : ∀ (r s : Fin 3), r ≠ s →
      0 < (q r.succ).1 + (q s.succ).1 := AffineSymmetryCoordinates.parentPositive q hq
  have incomingFacts := AffineSymmetryCoordinates.incomingFacts g q hq affineFacts sourceNorm
  have cyclicFacts : ∀ (j k : Fin 4), j ≠ k →
      (BandPackingSymmetryAffineVectorAction g
        (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).1 ≠ 0 :=
            AffineSymmetryCoordinates.cyclicFacts g q hq affineFacts sourceNorm
  have hproper := BandPackingSymmetryProperCovariance g q hq
  have hspatial := hphase i
  have incomingProduct :=
    VectorSquareProduct (BandPackingSymmetryQuadrupleAction g q) hproper.1
      ((if BandPackingSymmetryReversesOrientation g then -i else i).succ) 0 (by
        fin_cases i <;> simp)
  have incomingAffine := affineFacts g (q i.succ) (q 0)
    (BandVectors.1 (q i.succ) (q 0)) (BandVectors.2 (q i.succ) (q 0))
    (sourceNorm i.succ 0 (by simp) (by
      have hc := ProperBandCurvatureStructure q hq
      have hn := hc.2.1 i
      omega))
    (VectorSquareProduct q hq.1 i.succ 0 (by simp)).2
  have incomingSlope := AffineSymmetryCoordinates.incomingSlope g q negative i slopeCancel
      incomingFacts hspatial incomingProduct incomingAffine
  refine ⟨?_, ?_⟩
  · simpa [epsilon] using incomingSlope
  · have unitCancel : ∀ (V A b c d : GaussianInt),
        V ≠ 0 → c * d = 1 → 2 * V * A = 2 * (c * V) * b →
        b = d * A := AffineSymmetryCoordinates.unitCancel
    by_cases hrev : BandPackingSymmetryReversesOrientation g = true
    · simp only [hrev, ↓reduceIte, Fin.isValue, ite_mul, neg_mul, one_mul, mul_neg]
        at hspatial
      let j : Fin 4 := (i + 2).succ
      let k : Fin 4 := (i + 1).succ
      let V := (BandPackingSymmetryAffineVectorAction g
        (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).1
      let A := (BandPackingSymmetryAffineVectorAction g
        (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).2
      have hjk : j ≠ k := by
        dsimp [j, k]
        fin_cases i <;> simp
      have aff := affineFacts g (q j) (q k)
        (BandVectors.1 (q j) (q k)) (BandVectors.2 (q j) (q k))
        (sourceNorm j k hjk (by
          dsimp [j, k]
          exact parentPositive (i + 2) (i + 1) (by fin_cases i <;> simp)))
        (VectorSquareProduct q hq.1 j k hjk).2
      have prod := VectorSquareProduct (BandPackingSymmetryQuadrupleAction g q)
        hproper.1 ((-i + 2).succ) ((-i + 1).succ) (by
          fin_cases i <;> decide)
      have hprod : 2 * V * A =
          2 * (epsilon * GaussianQuarterTurn V) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction g q
              (-i + 2).succ) (BandPackingSymmetryQuadrupleAction g q
              (-i + 1).succ)) := AffineSymmetryCoordinates.hprodAt446 g q negative hphase i
                  epsilonSquare slopeCancel incomingProduct incomingAffine incomingSlope hrev
                  hspatial hjk aff prod
      have hv : V ≠ 0 := by
        exact cyclicFacts j k hjk
      have hu : (epsilon * GaussianQuarterTurn 1) *
          (-epsilon * GaussianQuarterTurn 1) = 1 := AffineSymmetryCoordinates.hu negative
      have qmul : GaussianQuarterTurn V = GaussianQuarterTurn 1 * V := by
        ext <;> simp [GaussianQuarterTurn]
      have quarterMul : ∀ z : GaussianInt,
          GaussianQuarterTurn z = GaussianQuarterTurn 1 * z := AffineSymmetryCoordinates.quarterMul
      have final := unitCancel V A
        (BandVectors.2 (BandPackingSymmetryQuadrupleAction g q
          (-i + 2).succ) (BandPackingSymmetryQuadrupleAction g q
          (-i + 1).succ))
        (epsilon * GaussianQuarterTurn 1) (-epsilon * GaussianQuarterTurn 1)
        hv hu (by simpa [qmul, mul_assoc, mul_left_comm, mul_comm] using hprod)
      have hi1 : ((if BandPackingSymmetryReversesOrientation g then -i else i) + 2).succ =
          (-i + 2).succ := by simp [hrev]
      have hi2 : ((if BandPackingSymmetryReversesOrientation g then -i else i) + 1).succ =
          (-i + 1).succ := by simp [hrev]
      rw [hi1, hi2]
      have slopeIndex :
          (BandPackingSymmetryAffineVectorAction g
            (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ),
              BandVectors.2 (q (i + 2).succ) (q (i + 1).succ))).2 = A :=
                  AffineSymmetryCoordinates.slopeIndex g q i
      rw [slopeIndex]
      cases negative <;> simp only [Fin.isValue, Bool.false_eq_true, ↓reduceIte, mul_comm,
          mul_neg, one_mul, neg_mul, hrev, epsilon, j, neg_neg] at final ⊢
      · rw [quarterMul A]
        exact final
      · rw [quarterMul A]
        exact final
    · simp only [hrev, Bool.false_eq_true, ↓reduceIte, Fin.isValue, ite_mul, neg_mul, one_mul]
        at hspatial
      let j : Fin 4 := (i + 2).succ
      let k : Fin 4 := (i + 1).succ
      let V := (BandPackingSymmetryAffineVectorAction g
        (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).1
      let A := (BandPackingSymmetryAffineVectorAction g
        (BandVectors.1 (q j) (q k), BandVectors.2 (q j) (q k))).2
      have hjk : j ≠ k := by
        dsimp [j, k]
        fin_cases i <;> simp
      have aff := affineFacts g (q j) (q k)
        (BandVectors.1 (q j) (q k)) (BandVectors.2 (q j) (q k))
        (sourceNorm j k hjk (by
          dsimp [j, k]
          exact parentPositive (i + 2) (i + 1) (by fin_cases i <;> simp)))
        (VectorSquareProduct q hq.1 j k hjk).2
      have prod := VectorSquareProduct (BandPackingSymmetryQuadrupleAction g q)
        hproper.1 (i + 2).succ (i + 1).succ (by fin_cases i <;> decide)
      have hprod : 2 * V * A =
          2 * (epsilon * V) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction g q
              (i + 2).succ) (BandPackingSymmetryQuadrupleAction g q
              (i + 1).succ)) := AffineSymmetryCoordinates.hprodAt542 g q negative i hrev
                  hspatial aff prod
      have final := slopeCancel V A
        (BandVectors.2 (BandPackingSymmetryQuadrupleAction g q
          (i + 2).succ) (BandPackingSymmetryQuadrupleAction g q
          (i + 1).succ)) (cyclicFacts j k hjk) hprod
      have hi1 : ((if BandPackingSymmetryReversesOrientation g then -i else i) + 2).succ =
          (i + 2).succ := by simp [hrev]
      have hi2 : ((if BandPackingSymmetryReversesOrientation g then -i else i) + 1).succ =
          (i + 1).succ := by simp [hrev]
      rw [hi1, hi2]
      cases negative <;> simp only [Fin.isValue, Bool.false_eq_true, ↓reduceIte, one_mul,
          hrev, epsilon, neg_mul] at final ⊢
      · exact final
      · exact final

end ApollonianSuperharmonic

end
