/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn

-- [TABLET NODE: P5472T1FordNormalization]

/-!
# P5472T1FordNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordNormalizationProof

private theorem hridx :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            (cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ) →
              let t := cfg.firstPredecessor;
              ((0 : ℤ) < (t (0 : Fin (4 : ℕ))).1 ∧
                  (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (t i.succ).1) ∧
                    ∀ (i : Fin (3 : ℕ)),
                      ∀ (j : Fin (3 : ℕ)),
                        (t i.succ).1 = (0 : ℤ) → (t j.succ).1 = (0 : ℤ) → i = j) →
                ∀ (ridx : Fin (3 : ℕ)),
                  (t (ridx + (2 : Fin (3 : ℕ))).succ).1 = (0 : ℤ) → ridx = 1
    ) := by
  classical
  intro q cfg hzero t hcurv ridx hline
  fin_cases ridx
  · have hzero3 : (t 3).1 = 0 := by simpa using hline
    have eq := hcurv.2.2 2 0 hzero3 hzero
    exact False.elim ((by decide : (2 : Fin 3) ≠ 0) eq)
  · rfl
  · have hzero2 : (t 2).1 = 0 := by simpa using hline
    have eq := hcurv.2.2 1 0 hzero2 hzero
    exact False.elim ((by decide : (1 : Fin 3) ≠ 0) eq)

private theorem hqSucc :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        let succ (a : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
          ![(2 * (a 0).1 + 2 * (a 2).1 + 2 * (a 3).1 - (a 1).1,
              2 * (a 0).2 + 2 * (a 2).2 + 2 * (a 3).2 - (a 1).2),
            a 0, a 2, a 3]
        q = succ t ) := by
  classical
  intro q cfg t succ
  have htwin := cfg.firstTwin
  rw [← cfg.firstChild, ← cfg.firstParentTwo, ← cfg.firstParentThree] at htwin
  change t 1 =
    (2 * (t 0).1 + 2 * (t 2).1 + 2 * (t 3).1 - (q 0).1,
      2 * (t 0).2 + 2 * (t 2).2 + 2 * (t 3).2 - (q 0).2) at htwin
  have hroot : q 0 =
      (2 * (t 0).1 + 2 * (t 2).1 + 2 * (t 3).1 - (t 1).1,
        2 * (t 0).2 + 2 * (t 2).2 + 2 * (t 3).2 - (t 1).2) := by
    apply Prod.ext
    · have hh := congrArg Prod.fst htwin
      dsimp at hh ⊢
      linear_combination hh
    · have hh := congrArg Prod.snd htwin
      dsimp at hh ⊢
      linear_combination hh
  funext i
  fin_cases i
  · change q 0 = succ t 0
    exact hroot
  · change q 1 = succ t 1
    exact cfg.firstChild.symm
  · change q 2 = succ t 2
    exact cfg.firstParentTwo.symm
  · change q 3 = succ t 3
    exact cfg.firstParentThree.symm

private theorem hsuccCov :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        ∀ (s : BandPackingSymmetry), (∃ (w : GaussianInt), s = BandPackingSymmetry.shift w ∨ s =
            (BandPackingSymmetry.shift w).comp BandPackingSymmetry.negate) → (
        let succ (a : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
          ![(2 * (a 0).1 + 2 * (a 2).1 + 2 * (a 3).1 - (a 1).1,
              2 * (a 0).2 + 2 * (a 2).2 + 2 * (a 3).2 - (a 1).2),
            a 0, a 2, a 3]
        BandPackingSymmetryQuadrupleAction s (succ t) = succ (BandPackingSymmetryQuadrupleAction
            s t)) ) := by
  classical
  intro q cfg t s hword succ
  rcases hword with ⟨w, hs | hs⟩
  · rw [hs]
    funext i
    fin_cases i <;>
      simp only [BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
          Fin.isValue, Matrix.cons_val_zero, Int.cast_sub, Int.cast_add, Int.cast_mul,
          Int.cast_ofNat, BandPackingSymmetryReversesOrientation, Bool.false_eq_true,
          ↓reduceIte, Fin.succ_zero_eq_one, Matrix.cons_val_one, Fin.succ_one_eq_two,
          Matrix.cons_val, Fin.reduceSucc, Fin.mk_one, succ, Fin.reduceFinMk, Fin.zero_eta,
          Prod.mk.injEq, true_and];
      (try ext) <;> simp [] <;> ring
  · rw [hs]
    funext i
    fin_cases i <;>
      simp only [BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
          Fin.isValue, Matrix.cons_val_zero, neg_sub, Int.cast_sub, Int.cast_add,
          Int.cast_mul, Int.cast_ofNat, BandPackingSymmetryReversesOrientation,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Fin.succ_zero_eq_one,
          Matrix.cons_val_one, Fin.succ_one_eq_two, Matrix.cons_val, Fin.reduceSucc,
          Fin.mk_one, succ, Fin.reduceFinMk, Fin.zero_eta, Prod.mk.injEq, true_and]; (try ext) <;>
      simp [] <;> ring

private theorem hF0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        ∀ (s : BandPackingSymmetry), ∀ (F : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation s = false) →
            ((BandPackingSymmetryQuadrupleAction s ![cfg.firstPredecessor 0, cfg.firstPredecessor
            2, cfg.firstPredecessor 3, cfg.firstPredecessor 1] = FordRecursiveQuadruple F) →
            (BandPackingSymmetryCircleAction s (t 0) = FordRecursiveQuadruple F 0)) ) := by
  classical
  intro q cfg t s F hrev hford'
  have hh := congrArg (fun z : Fin 4 → CircleCoordinates => z 0) hford'
  simpa [BandPackingSymmetryQuadrupleAction, hrev] using hh

private theorem hF1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        ∀ (s : BandPackingSymmetry), ∀ (F : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation s = false) →
            ((BandPackingSymmetryQuadrupleAction s ![cfg.firstPredecessor 0, cfg.firstPredecessor
            2, cfg.firstPredecessor 3, cfg.firstPredecessor 1] = FordRecursiveQuadruple F) →
            (BandPackingSymmetryCircleAction s (t 2) = FordRecursiveQuadruple F 1)) ) := by
  classical
  intro q cfg t s F hrev hford'
  have hh := congrArg (fun z : Fin 4 → CircleCoordinates => z 1) hford'
  simpa [BandPackingSymmetryQuadrupleAction, hrev] using hh

private theorem hF2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        ∀ (s : BandPackingSymmetry), ∀ (F : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation s = false) →
            ((BandPackingSymmetryQuadrupleAction s ![cfg.firstPredecessor 0, cfg.firstPredecessor
            2, cfg.firstPredecessor 3, cfg.firstPredecessor 1] = FordRecursiveQuadruple F) →
            (BandPackingSymmetryCircleAction s (t 3) = FordRecursiveQuadruple F 2)) ) := by
  classical
  intro q cfg t s F hrev hford'
  have hh := congrArg (fun z : Fin 4 → CircleCoordinates => z 2) hford'
  simpa [BandPackingSymmetryQuadrupleAction, hrev] using hh

private theorem hF3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        ∀ (s : BandPackingSymmetry), ∀ (F : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation s = false) →
            ((BandPackingSymmetryQuadrupleAction s ![cfg.firstPredecessor 0, cfg.firstPredecessor
            2, cfg.firstPredecessor 3, cfg.firstPredecessor 1] = FordRecursiveQuadruple F) →
            (BandPackingSymmetryCircleAction s (t 1) = FordRecursiveQuadruple F 3)) ) := by
  classical
  intro q cfg t s F hrev hford'
  have hh := congrArg (fun z : Fin 4 → CircleCoordinates => z 3) hford'
  simpa [BandPackingSymmetryQuadrupleAction, hrev] using hh

private theorem hsF1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        ∀ (s : BandPackingSymmetry), ∀ (F : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation s = false) →
            ((BandPackingSymmetryCircleAction s (t 1) = FordRecursiveQuadruple F 3) →
            (BandPackingSymmetryQuadrupleAction s t 1 = FordRecursiveQuadruple F 3)) ) := by
  classical
  intro q cfg t s F hrev hF3
  simpa [BandPackingSymmetryQuadrupleAction, hrev] using hF3

private theorem houter :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let t := cfg.firstPredecessor
        ∀ (s : BandPackingSymmetry), ∀ (F : FordFareyParameter),
        let succ (a : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
          ![(2 * (a 0).1 + 2 * (a 2).1 + 2 * (a 3).1 - (a 1).1,
              2 * (a 0).2 + 2 * (a 2).2 + 2 * (a 3).2 - (a 1).2),
            a 0, a 2, a 3]
        (q = succ t) → ((BandPackingSymmetryQuadrupleAction s (succ t) = succ
            (BandPackingSymmetryQuadrupleAction s t)) → ((BandPackingSymmetryQuadrupleAction s t
            0 = FordRecursiveQuadruple F 0) → ((BandPackingSymmetryQuadrupleAction s t 1 =
            FordRecursiveQuadruple F 3) → ((BandPackingSymmetryQuadrupleAction s t 2 =
            FordRecursiveQuadruple F 1) → ((BandPackingSymmetryQuadrupleAction s t 3 =
            FordRecursiveQuadruple F 2) → (BandPackingSymmetryQuadrupleAction s q = ![(2 *
            (FordRecursiveQuadruple F 0).1 + 2 * (FordRecursiveQuadruple F 1).1 + 2 *
            (FordRecursiveQuadruple F 2).1 - (FordRecursiveQuadruple F 3).1, 2 *
            (FordRecursiveQuadruple F 0).2 + 2 * (FordRecursiveQuadruple F 1).2 + 2 *
            (FordRecursiveQuadruple F 2).2 - (FordRecursiveQuadruple F 3).2),
            FordRecursiveQuadruple F 0, FordRecursiveQuadruple F 1, FordRecursiveQuadruple F
            2])))))) ) := by
  classical
  intro q cfg t s F succ hqSucc hsuccCov hsF0 hsF1 hsF2 hsF3
  rw [hqSucc, hsuccCov]
  funext i
  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, Nat.succ_eq_add_one,
      Nat.reduceAdd, Prod.mk.injEq, succ]
    constructor
    · rw [hsF0, hsF2, hsF3, hsF1]
    · rw [hsF0, hsF2, hsF3, hsF1]
  · simpa [succ] using hsF0
  · simpa [succ] using hsF2
  · simpa [succ] using hsF3

private theorem hW :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (s : BandPackingSymmetry), ∀ (F :
            FordFareyParameter), ((1 : ℕ) < F.q) → ((BandPackingSymmetryQuadrupleAction s q =
            ![(2 * (FordRecursiveQuadruple F 0).1 + 2 * (FordRecursiveQuadruple F 1).1 + 2 *
            (FordRecursiveQuadruple F 2).1 - (FordRecursiveQuadruple F 3).1, 2 *
            (FordRecursiveQuadruple F 0).2 + 2 * (FordRecursiveQuadruple F 1).2 + 2 *
            (FordRecursiveQuadruple F 2).2 - (FordRecursiveQuadruple F 3).2),
            FordRecursiveQuadruple F 0, FordRecursiveQuadruple F 1, FordRecursiveQuadruple F 2])
            → (BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2) = ⟨-(F.q₁ : Int), (F.q₂ : Int)⟩)) ) := by
  classical
  intro q s F hFq houter
  have fc := (FordCoordinateConfiguration F).2 hFq
  have laws := VectorRecursionLaws (FordRecursiveQuadruple F) fc.1.1
  have hv10 := fc.2.1
  have hv20 := fc.2.2.1
  have hsum : (F.q : Int) = (F.q₁ : Int) + F.q₂ := by exact_mod_cast F.sum_q
  let rot : Fin 4 → CircleCoordinates :=
    ![FordRecursiveQuadruple F 0, FordRecursiveQuadruple F 2,
      FordRecursiveQuadruple F 3, FordRecursiveQuadruple F 1]
  have hrot : SemiProperQuadruple rot := by
    simpa [rot] using SemiProperQuadruple.rotate fc.1.1
  have lawsRot := VectorRecursionLaws rot hrot
  let rot2 : Fin 4 → CircleCoordinates :=
    ![FordRecursiveQuadruple F 0, FordRecursiveQuadruple F 3,
      FordRecursiveQuadruple F 1, FordRecursiveQuadruple F 2]
  have hrot2 : SemiProperQuadruple rot2 := by
    simpa [rot2] using
      SemiProperQuadruple.rotate (SemiProperQuadruple.rotate fc.1.1)
  have lawsRot2 := VectorRecursionLaws rot2 hrot2
  rw [houter]
  change BandVectors.1 (FordRecursiveQuadruple F 2)
    (FordRecursiveQuadruple F 1) = _
  have e1 := laws.2.2.1
  have e2 : BandVectors.1 (FordRecursiveQuadruple F 2)
      (FordRecursiveQuadruple F 0) =
      BandVectors.1 (FordRecursiveQuadruple F 2)
          (FordRecursiveQuadruple F 1) -
        (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 (FordRecursiveQuadruple F 3)
            (FordRecursiveQuadruple F 2) := by
    simpa [rot] using lawsRot.2.2.1
  have e4 : BandVectors.1 (FordRecursiveQuadruple F 3)
      (FordRecursiveQuadruple F 0) =
      BandVectors.1 (FordRecursiveQuadruple F 3)
          (FordRecursiveQuadruple F 2) -
        (⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 (FordRecursiveQuadruple F 1)
            (FordRecursiveQuadruple F 3) := by
    simpa [rot2] using lawsRot2.2.2.1
  have e3 := laws.1
  have hv30 := fc.2.2.2.1
  rw [hv10] at e1
  rw [hv20] at e2
  rw [hv30] at e4
  have imul (z : GaussianInt) :
      (⟨0, 1⟩ : GaussianInt) * z = GaussianQuarterTurn z := by
    ext <;> simp [GaussianQuarterTurn]
  rw [imul] at e1 e2 e4
  have e1r := congrArg (fun z : GaussianInt => z.re) e1
  have e1i := congrArg (fun z : GaussianInt => z.im) e1
  have e2r := congrArg (fun z : GaussianInt => z.re) e2
  have e2i := congrArg (fun z : GaussianInt => z.im) e2
  have e4r := congrArg (fun z : GaussianInt => z.re) e4
  have e4i := congrArg (fun z : GaussianInt => z.im) e4
  have e3r := congrArg (fun z : GaussianInt => z.re) e3
  have e3i := congrArg (fun z : GaussianInt => z.im) e3
  simp [GaussianQuarterTurn] at e1r e1i e2r e2i e3r e3i e4r e4i
  apply Zsqrtd.ext
  · nlinarith [e1r, e2r, e3r, e4r]
  · nlinarith [e1i, e2i, e3i, e4i, hsum]

private theorem hA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (s : BandPackingSymmetry), ∀ (F :
            FordFareyParameter), ((1 : ℕ) < F.q) → ((BandPackingSymmetryQuadrupleAction s q =
            ![(2 * (FordRecursiveQuadruple F 0).1 + 2 * (FordRecursiveQuadruple F 1).1 + 2 *
            (FordRecursiveQuadruple F 2).1 - (FordRecursiveQuadruple F 3).1, 2 *
            (FordRecursiveQuadruple F 0).2 + 2 * (FordRecursiveQuadruple F 1).2 + 2 *
            (FordRecursiveQuadruple F 2).2 - (FordRecursiveQuadruple F 3).2),
            FordRecursiveQuadruple F 0, FordRecursiveQuadruple F 1, FordRecursiveQuadruple F 2])
            → (BandVectors.2 (BandPackingSymmetryQuadrupleAction s q 3)
            (BandPackingSymmetryQuadrupleAction s q 2) = ⟨F.p₂, -F.p₁⟩)) ) := by
  classical
  intro q s F hFq houter
  have fc := (FordCoordinateConfiguration F).2 hFq
  have laws := VectorRecursionLaws (FordRecursiveQuadruple F) fc.1.1
  have ha32 := fc.2.2.2.2.2.2.2.1
  have ha13 := fc.2.2.2.2.2.2.2.2
  rw [houter]
  change BandVectors.2 (FordRecursiveQuadruple F 2)
    (FordRecursiveQuadruple F 1) = _
  calc
    BandVectors.2 (FordRecursiveQuadruple F 2) (FordRecursiveQuadruple F 1) =
        -(BandVectors.2 (FordRecursiveQuadruple F 3)
            (FordRecursiveQuadruple F 2) +
          BandVectors.2 (FordRecursiveQuadruple F 1)
            (FordRecursiveQuadruple F 3)) := by linear_combination laws.2.1
    _ = _ := by rw [ha32, ha13]; ext <;> simp

private theorem hrootCircle :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (s :
            BandPackingSymmetry), ∀ (F : FordFareyParameter),
            (BandPackingSymmetryReversesOrientation s = false) →
            ((BandPackingSymmetryQuadrupleAction s ![cfg.firstPredecessor 0, cfg.firstPredecessor
            2, cfg.firstPredecessor 3, cfg.firstPredecessor 1] = FordRecursiveQuadruple F) →
            (BandPackingSymmetryCircleAction s (q 1) = FordCircleCoordinate F.p F.q)) ) := by
  classical
  intro q cfg s F hrev hford'
  have hh := congrFun hford' 0
  simpa [BandPackingSymmetryQuadrupleAction, BandPackingSymmetryReversesOrientation,
    hrev, cfg.firstChild, FordRecursiveQuadruple] using hh

end FordNormalizationProof

theorem P5472T1FordNormalization
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (hzero : (cfg.firstPredecessor 1).1 = 0) :
    ∃ (F : FordFareyParameter) (s : BandPackingSymmetry),
      1 < F.q ∧
      BandPackingSymmetryReversesOrientation s = false ∧
      (∃ w : GaussianInt, s = .shift w ∨ s = (BandPackingSymmetry.shift w).comp .negate) ∧
      BandPackingSymmetryQuadrupleAction s
        ![cfg.firstPredecessor 0, cfg.firstPredecessor 2,
          cfg.firstPredecessor 3, cfg.firstPredecessor 1] =
        FordRecursiveQuadruple F ∧
      BandPackingSymmetryCircleAction s (q 1) = FordCircleCoordinate F.p F.q ∧
      BandVectors.1 (BandPackingSymmetryQuadrupleAction s q 3)
        (BandPackingSymmetryQuadrupleAction s q 2) =
        ⟨-(F.q₁ : Int), (F.q₂ : Int)⟩ ∧
      BandVectors.2 (BandPackingSymmetryQuadrupleAction s q 3)
        (BandPackingSymmetryQuadrupleAction s q 2) = ⟨F.p₂, -F.p₁⟩ := by
-- BODY
  let t := cfg.firstPredecessor
  have htproper : ProperBandQuadruple t := cfg.firstProper
  have hcurv := ProperBandCurvatureStructure t htproper
  obtain ⟨ridx, s, F, hFq, hrev, hword, hline, hford⟩ :=
    FordRegimeConverse t htproper ⟨1, hzero⟩
  have hridx := FordNormalizationProof.hridx q cfg hzero hcurv ridx hline
  subst ridx
  have hford' := hford
  have hqSucc := FordNormalizationProof.hqSucc q cfg
  have hsuccCov := FordNormalizationProof.hsuccCov q cfg s hword
  have hF0 : BandPackingSymmetryCircleAction s (t 0) =
      FordRecursiveQuadruple F 0 := FordNormalizationProof.hF0 q cfg s F hrev hford'
  have hF1 : BandPackingSymmetryCircleAction s (t 2) =
      FordRecursiveQuadruple F 1 := FordNormalizationProof.hF1 q cfg s F hrev hford'
  have hF2 : BandPackingSymmetryCircleAction s (t 3) =
      FordRecursiveQuadruple F 2 := FordNormalizationProof.hF2 q cfg s F hrev hford'
  have hF3 := FordNormalizationProof.hF3 q cfg s F hrev hford'
  have hsF0 : BandPackingSymmetryQuadrupleAction s t 0 =
      FordRecursiveQuadruple F 0 := by simpa [BandPackingSymmetryQuadrupleAction, hrev] using hF0
  have hsF1 := FordNormalizationProof.hsF1 q cfg s F hrev hF3
  have hsF2 : BandPackingSymmetryQuadrupleAction s t 2 =
      FordRecursiveQuadruple F 1 := by simpa [BandPackingSymmetryQuadrupleAction, hrev] using hF1
  have hsF3 : BandPackingSymmetryQuadrupleAction s t 3 =
      FordRecursiveQuadruple F 2 := by simpa [BandPackingSymmetryQuadrupleAction, hrev] using hF2
  have houter := FordNormalizationProof.houter q cfg s F hqSucc hsuccCov hsF0 hsF1 hsF2 hsF3
  have hW := FordNormalizationProof.hW q s F hFq houter
  have hA := FordNormalizationProof.hA q s F hFq houter
  have hrootCircle := FordNormalizationProof.hrootCircle q cfg s F hrev hford'
  exact ⟨F, s, hFq, hrev, hword, hford', hrootCircle, hW, hA⟩

end ApollonianSuperharmonic

end
