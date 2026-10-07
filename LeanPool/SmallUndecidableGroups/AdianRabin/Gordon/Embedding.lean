/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Amalgam
public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.LeftNormalForm
public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.RightNormalForm

/-! The free-product embeddings needed for Gordon's nontriviality direction. -/

@[expose] public section

namespace Undecidability.Gordon

namespace LeftBridge

open Monoid

/-- The inclusion of the original group into the separated free factors. -/
def oldToSplit (P : FP n m) :
    P.Group →* LeftNormalForm.SplitLeft P.Group :=
  CoprodI.of (M := MillerTancer.LeftNormalForm.LeftFactor P.Group)
    (i := MillerTancer.LeftNormalForm.LeftIndex.old)

/-- The homomorphism assigning the new free generators to their separated factors. -/
def newToSplit (P : FP n m) :
    FreeGroup (Fin 2) →* LeftNormalForm.SplitLeft P.Group :=
  FreeGroup.lift ![LeftNormalForm.a, LeftNormalForm.auxiliaryAlpha]

/-- The homomorphism comparing the two bracketings of the free product. -/
def comparison (P : FP n m) :
    Amalgam.LeftFactor P →* LeftNormalForm.SplitLeft P.Group :=
  Monoid.Coprod.lift (oldToSplit P) (newToSplit P)

@[simp] theorem comparison_old (P : FP n m) (g : P.Group) :
    comparison P (Amalgam.oldLeft P g) = MillerTancer.LeftNormalForm.old g := rfl

@[simp] theorem comparison_a (P : FP n m) :
    comparison P (Amalgam.aLeft P) = LeftNormalForm.a := by
  simp [comparison, Amalgam.aLeft, newToSplit]

@[simp] theorem comparison_alpha (P : FP n m) :
    comparison P (Amalgam.alphaLeft P) =
      LeftNormalForm.auxiliaryAlpha := by
  simp [comparison, Amalgam.alphaLeft, newToSplit]

theorem comparison_leftBasis (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : BasisIndex n) :
    comparison P (Amalgam.leftBasis P data w i) =
      LeftNormalForm.splitBasis data.degree
        (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w) i := by
  cases i <;>
    simp [Amalgam.leftBasis, LeftNormalForm.splitBasis,
      LeftNormalForm.oldElement, LeftNormalForm.degreeInt,
      LeftNormalForm.a, LeftNormalForm.auxiliaryAlpha,
      map_mul, map_inv, map_pow, zpow_neg, zpow_natCast, mul_assoc]

theorem comparison_comp_leftMap (P : FP n m) (data : TorsionData P)
    (w : Word n) :
    (comparison P).comp (Amalgam.leftMap P data w) =
      FreeGroup.lift
        (LeftNormalForm.splitBasis data.degree
          (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w)) := by
  ext i
  simp [Amalgam.leftMap, comparison_leftBasis]

theorem leftMap_injective (P : FP n m) (data : TorsionData P)
    (w : Word n) (hw : P.evalWord w ≠ 1) :
    Function.Injective (Amalgam.leftMap P data w) := by
  have hinj : Function.Injective
      (FreeGroup.lift
        (LeftNormalForm.splitBasis data.degree
          (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w))) :=
    LeftNormalForm.splitBasis_lift_injective data.degree
      data.degree_pos data.degree_injective
      (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w) hw
  intro x y hxy
  apply hinj
  rw [← comparison_comp_leftMap P data w]
  exact congrArg (comparison P) hxy

end LeftBridge

theorem amalgam_rightMap_eq (n : ℕ) :
    Amalgam.rightMap n = rightBasisMap n := rfl

theorem amalgam_rightMap_injective (n : ℕ) :
    Function.Injective (Amalgam.rightMap n) :=
  rightBasisMap_injective n

/-- The hard implication in Gordon's Lemma 2.1: a nontrivial input word
remains visible in the amalgamated-product witness. -/
theorem transform_not_trivial_of_not_wordProblem
    (P : FP n m) (data : TorsionData P) (w : Word n)
    (hw : ¬ P.wordProblem w) :
    ¬ (transform P data w).presentsTrivial := by
  have hwEval : P.evalWord w ≠ 1 := by
    intro h
    exact hw ((P.wordProblem_iff_evalWord_eq_one w).mpr h)
  exact Amalgam.transform_not_trivial_of_basis_injective P data w
    (LeftBridge.leftMap_injective P data w hwEval)
    (amalgam_rightMap_injective n) hw

end Undecidability.Gordon
