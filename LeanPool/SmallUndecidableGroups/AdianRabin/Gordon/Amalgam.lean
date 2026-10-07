/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Construction
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.Tactic.FinCases

public import Mathlib.Data.Fin.VecNotation

/-! Gordon's uncompressed presentation as a free product with amalgamation. -/

@[expose] public section

namespace Undecidability.Gordon.Amalgam

open Monoid

/-- The left factor of the free product used to construct the amalgam. -/
abbrev LeftFactor (P : FP n m) :=
  Monoid.Coprod P.Group (FreeGroup (Fin 2))

/-- The right free factor used to construct the amalgam. -/
abbrev RightFactor := FreeGroup (Fin 2)

/-- The inclusion of the original presented group into the left factor. -/
def oldLeft (P : FP n m) : P.Group →* LeftFactor P :=
  Monoid.Coprod.inl

/-- The element `a` in the left factor. -/
def aLeft (P : FP n m) : LeftFactor P :=
  Monoid.Coprod.inr (FreeGroup.of 0)

/-- The element `alpha` in the left factor. -/
def alphaLeft (P : FP n m) : LeftFactor P :=
  Monoid.Coprod.inr (FreeGroup.of 1)

/-- The element `b` in the right factor. -/
def bRight : RightFactor := FreeGroup.of 0
/-- The element `beta` in the right factor. -/
def betaRight : RightFactor := FreeGroup.of 1

/-- The conjugate of `b` by the indicated power of `beta`. -/
def rightConjugate (r : ℕ) : RightFactor :=
  (betaRight ^ r)⁻¹ * bRight * betaRight ^ r

/-- The left-hand amalgamating words in Gordon's Lemma 2.1. -/
def leftBasis (P : FP n m) (data : TorsionData P)
    (w : Word n) : BasisIndex n → LeftFactor P
  | .conjugateA => aLeft P * alphaLeft P * (aLeft P)⁻¹
  | .conjugateAlpha => alphaLeft P * aLeft P * (alphaLeft P)⁻¹
  | .old i =>
      (aLeft P ^ data.degree i)⁻¹ *
        oldLeft P (PresentedGroup.of i) *
          alphaLeft P ^ data.degree i
  | .commutator =>
      oldLeft P (P.evalWord w) * alphaLeft P ^ 2 *
        (oldLeft P (P.evalWord w))⁻¹ * (alphaLeft P ^ 2)⁻¹

/-- The corresponding right-hand free basis. -/
def rightBasis (n : ℕ) : BasisIndex n → RightFactor
  | .conjugateA => bRight ^ 2
  | .conjugateAlpha => bRight * betaRight * bRight⁻¹
  | .old i => rightConjugate (i.1 + 1)
  | .commutator => rightConjugate (n + 1)

/-- The homomorphism freely extending the left amalgamating basis. -/
def leftMap (P : FP n m) (data : TorsionData P) (w : Word n) :
    FreeGroup (BasisIndex n) →* LeftFactor P :=
  FreeGroup.lift (leftBasis P data w)

/-- The homomorphism freely extending the right amalgamating basis. -/
def rightMap (n : ℕ) : FreeGroup (BasisIndex n) →* RightFactor :=
  FreeGroup.lift (rightBasis n)

/-- The two sides of the amalgamation diagram. -/
inductive Side
  | left
  | right
/-- The free-product factor on the chosen side of the diagram. -/
def Factor (P : FP n m) : Side → Type
  | .left => LeftFactor P
  | .right => RightFactor

instance factorGroup (P : FP n m) (s : Side) : Group (Factor P s) := by
  cases s <;> simp only [Factor] <;> infer_instance

/-- The two homomorphisms identifying the amalgamating subgroup. -/
def diagram (P : FP n m) (data : TorsionData P) (w : Word n) :
    (s : Side) → FreeGroup (BasisIndex n) →* Factor P s
  | .left => leftMap P data w
  | .right => rightMap n

/-- The group obtained by taking the pushout of the amalgamation diagram. -/
abbrev Pushout (P : FP n m) (data : TorsionData P) (w : Word n) :=
  Monoid.PushoutI (diagram P data w)

/-- The canonical homomorphism from the left factor into the pushout. -/
def pushLeft (P : FP n m) (data : TorsionData P) (w : Word n) :
    LeftFactor P →* Pushout P data w :=
  Monoid.PushoutI.of (φ := diagram P data w) Side.left

/-- The canonical homomorphism from the right factor into the pushout. -/
def pushRight (P : FP n m) (data : TorsionData P) (w : Word n) :
    RightFactor →* Pushout P data w :=
  Monoid.PushoutI.of (φ := diagram P data w) Side.right

theorem identifies_basis (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : BasisIndex n) :
    pushLeft P data w (leftBasis P data w i) =
      pushRight P data w (rightBasis n i) := by
  have hl := Monoid.PushoutI.of_apply_eq_base
    (diagram P data w) Side.left (FreeGroup.of i)
  have hr := Monoid.PushoutI.of_apply_eq_base
    (diagram P data w) Side.right (FreeGroup.of i)
  change pushLeft P data w ((leftMap P data w) (FreeGroup.of i)) = _ at hl
  change pushRight P data w (rightMap n (FreeGroup.of i)) = _ at hr
  simpa [leftMap, rightMap] using hl.trans hr.symm

/-- Interpret the two generators of the compressed presentation. -/
def witnessGenerator (P : FP n m) (data : TorsionData P)
    (w : Word n) : Fin 2 → Pushout P data w :=
  ![pushLeft P data w (aLeft P), pushRight P data w bRight]

@[simp] theorem witnessGenerator_a (P : FP n m) (data : TorsionData P)
    (w : Word n) :
    witnessGenerator P data w 0 = pushLeft P data w (aLeft P) := rfl

@[simp] theorem witnessGenerator_b (P : FP n m) (data : TorsionData P)
    (w : Word n) :
    witnessGenerator P data w 1 = pushRight P data w bRight := rfl

theorem eval_alpha_witness (P : FP n m) (data : TorsionData P)
    (w : Word n) :
    Word.eval (witnessGenerator P data w) alphaWord =
      pushLeft P data w (alphaLeft P) := by
  have h :
      pushLeft P data w (aLeft P * alphaLeft P * (aLeft P)⁻¹) =
        pushRight P data w (bRight ^ 2) := by
    simpa [leftBasis, rightBasis] using
      identifies_basis P data w (BasisIndex.conjugateA : BasisIndex n)
  have h' :
      pushLeft P data w (aLeft P) * pushLeft P data w (alphaLeft P) *
          (pushLeft P data w (aLeft P))⁻¹ =
        (pushRight P data w bRight) ^ 2 := by
    simpa [map_mul, map_inv, map_pow] using h
  calc
    Word.eval (witnessGenerator P data w) alphaWord =
        (pushLeft P data w (aLeft P))⁻¹ *
          (pushRight P data w bRight) ^ 2 *
            pushLeft P data w (aLeft P) := by
              simp [alphaWord, aWord, bWord, mul_assoc]
    _ = pushLeft P data w (alphaLeft P) := by
      rw [← h']
      group

theorem eval_beta_witness (P : FP n m) (data : TorsionData P)
    (w : Word n) :
    Word.eval (witnessGenerator P data w) betaWord =
      pushRight P data w betaRight := by
  have h :
      pushLeft P data w
          (alphaLeft P * aLeft P * (alphaLeft P)⁻¹) =
        pushRight P data w (bRight * betaRight * bRight⁻¹) := by
    simpa [leftBasis, rightBasis] using
      identifies_basis P data w
        (BasisIndex.conjugateAlpha : BasisIndex n)
  have h' :
      pushLeft P data w (alphaLeft P) * pushLeft P data w (aLeft P) *
          (pushLeft P data w (alphaLeft P))⁻¹ =
        pushRight P data w bRight * pushRight P data w betaRight *
          (pushRight P data w bRight)⁻¹ := by
    simpa [map_mul, map_inv] using h
  calc
    Word.eval (witnessGenerator P data w) betaWord =
        (pushRight P data w bRight)⁻¹ *
          pushLeft P data w (alphaLeft P) *
            pushLeft P data w (aLeft P) *
              (pushLeft P data w (alphaLeft P))⁻¹ *
                pushRight P data w bRight := by
                  simp [betaWord, aWord, bWord, eval_alpha_witness,
                    mul_assoc]
    _ = pushRight P data w betaRight := by
      calc
        (pushRight P data w bRight)⁻¹ *
              pushLeft P data w (alphaLeft P) *
                pushLeft P data w (aLeft P) *
                  (pushLeft P data w (alphaLeft P))⁻¹ *
                    pushRight P data w bRight =
            (pushRight P data w bRight)⁻¹ *
              (pushLeft P data w (alphaLeft P) *
                pushLeft P data w (aLeft P) *
                  (pushLeft P data w (alphaLeft P))⁻¹) *
                    pushRight P data w bRight := by group
        _ = pushRight P data w betaRight := by rw [h']; group

theorem eval_rightConjugateWord_witness
    (P : FP n m) (data : TorsionData P) (w : Word n) (r : ℕ) :
    Word.eval (witnessGenerator P data w) (rightConjugateWord r) =
      pushRight P data w (rightConjugate r) := by
  simp [rightConjugateWord, rightConjugate, bWord,
    eval_beta_witness, witnessGenerator_b, map_mul, map_inv, map_pow,
    mul_assoc]

theorem eval_encodedGenerator_witness
    (P : FP n m) (data : TorsionData P) (w : Word n) (i : Fin n) :
    Word.eval (witnessGenerator P data w) (encodedGenerator data i) =
      pushLeft P data w (oldLeft P (PresentedGroup.of i)) := by
  have h :
      pushLeft P data w
          ((aLeft P ^ data.degree i)⁻¹ *
            oldLeft P (PresentedGroup.of i) *
              alphaLeft P ^ data.degree i) =
        pushRight P data w (rightConjugate (i.1 + 1)) := by
    simpa [leftBasis, rightBasis] using
      identifies_basis P data w (BasisIndex.old i)
  have h' :
      (pushLeft P data w (aLeft P) ^ data.degree i)⁻¹ *
          pushLeft P data w (oldLeft P (PresentedGroup.of i)) *
            pushLeft P data w (alphaLeft P) ^ data.degree i =
        pushRight P data w (rightConjugate (i.1 + 1)) := by
    simpa [map_mul, map_inv, map_pow] using h
  calc
    Word.eval (witnessGenerator P data w) (encodedGenerator data i) =
        pushLeft P data w (aLeft P) ^ data.degree i *
          pushRight P data w (rightConjugate (i.1 + 1)) *
            (pushLeft P data w (alphaLeft P) ^ data.degree i)⁻¹ := by
              simp [encodedGenerator, aWord, eval_alpha_witness,
                eval_rightConjugateWord_witness, mul_assoc]
    _ = pushLeft P data w (oldLeft P (PresentedGroup.of i)) := by
      rw [← h']
      group

theorem eval_encodeWord_witness (P : FP n m) (data : TorsionData P)
    (w u : Word n) :
    Word.eval (witnessGenerator P data w) (encodeWord data u) =
      pushLeft P data w (oldLeft P (P.evalWord u)) := by
  rw [eval_encodeWord]
  have hfun :
      (fun i ↦ Word.eval (witnessGenerator P data w)
        (encodedGenerator data i)) =
        ((pushLeft P data w).comp (oldLeft P) ∘
          (PresentedGroup.of : Fin n → P.Group)) := by
    funext i
    exact eval_encodedGenerator_witness P data w i
  rw [hfun]
  rw [← Word.map_eval ((pushLeft P data w).comp (oldLeft P))
    (PresentedGroup.of : Fin n → P.Group) u]
  rfl

theorem eval_additional (P : FP n m) (data : TorsionData P)
    (w : Word n) :
    Word.eval (witnessGenerator P data w)
      (additionalRelator data w) = 1 := by
  change Word.eval (witnessGenerator P data w)
    (Word.relation
      (paperCommutator (encodeWord data w) (Word.pow alphaWord 2))
      (rightConjugateWord (n + 1))) = 1
  rw [Word.eval_relation_eq_one_iff]
  calc
    Word.eval (witnessGenerator P data w)
        (paperCommutator (encodeWord data w) (Word.pow alphaWord 2)) =
        pushLeft P data w (oldLeft P (P.evalWord w)) *
          (pushLeft P data w (alphaLeft P)) ^ 2 *
            (pushLeft P data w (oldLeft P (P.evalWord w)))⁻¹ *
              ((pushLeft P data w (alphaLeft P)) ^ 2)⁻¹ := by
      rw [show paperCommutator (encodeWord data w)
          (Word.pow alphaWord 2) =
        Word.product [encodeWord data w, Word.pow alphaWord 2,
          Word.inverse (encodeWord data w),
          Word.inverse (Word.pow alphaWord 2)] from rfl]
      rw [Word.eval_product]
      simp only [List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, Word.eval_pow, Word.eval_inverse, mul_one]
      rw [eval_encodeWord_witness, eval_alpha_witness]
      group
    _ = pushRight P data w (rightConjugate (n + 1)) := by
      simpa [leftBasis, rightBasis, map_mul, map_inv, map_pow,
        mul_assoc] using
          identifies_basis P data w
            (BasisIndex.commutator : BasisIndex n)
    _ = Word.eval (witnessGenerator P data w)
        (rightConjugateWord (n + 1)) :=
      (eval_rightConjugateWord_witness P data w (n + 1)).symm

theorem transformed_relator_eq_one (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : Fin (m + 1)) :
    Word.eval (witnessGenerator P data w)
      ((transform P data w).relator i) = 1 := by
  cases i using Fin.addCases with
  | left j =>
      rw [transform_old, eval_encodeWord_witness, P.relator_eq_one]
      simp
  | right j =>
      rw [transform_additional]
      exact eval_additional P data w

/-- The relator-preserving homomorphism from the transformed presentation into the amalgam. -/
def witnessHom (P : FP n m) (data : TorsionData P) (w : Word n) :
    (transform P data w).Group →* Pushout P data w :=
  (transform P data w).homOfRelators (witnessGenerator P data w)
    (transformed_relator_eq_one P data w)

@[simp]
theorem witnessHom_of (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : Fin 2) :
    witnessHom P data w (PresentedGroup.of i) =
      witnessGenerator P data w i :=
  (transform P data w).homOfRelators_of _ _ i

/-- The amalgamated-product argument, conditional on the two free-basis
injectivity lemmas. -/
theorem transform_not_trivial_of_basis_injective
    (P : FP n m) (data : TorsionData P) (w : Word n)
    (hleft : Function.Injective (leftMap P data w))
    (hright : Function.Injective (rightMap n))
    (hw : ¬ P.wordProblem w) :
    ¬ (transform P data w).presentsTrivial := by
  intro htrivial
  have hwT : (transform P data w).wordProblem (encodeWord data w) :=
    htrivial (encodeWord data w)
  have hwEval : (transform P data w).evalWord (encodeWord data w) = 1 :=
    ((transform P data w).wordProblem_iff_evalWord_eq_one
      (encodeWord data w)).mp hwT
  have heval :
      witnessHom P data w
          ((transform P data w).evalWord (encodeWord data w)) =
        Word.eval (witnessGenerator P data w) (encodeWord data w) := by
    calc
      witnessHom P data w
          ((transform P data w).evalWord (encodeWord data w)) =
          Word.eval
            ((witnessHom P data w) ∘
              (PresentedGroup.of : Fin 2 → (transform P data w).Group))
            (encodeWord data w) :=
              Word.map_eval (witnessHom P data w)
                (PresentedGroup.of :
                  Fin 2 → (transform P data w).Group)
                (encodeWord data w)
      _ = Word.eval (witnessGenerator P data w)
          (encodeWord data w) := by
        congr 1
        funext i
        exact witnessHom_of P data w i
  have hwWitness :
      Word.eval (witnessGenerator P data w) (encodeWord data w) = 1 := by
    rw [← heval, hwEval, map_one]
  rw [eval_encodeWord_witness] at hwWitness
  have hdiagram : ∀ s, Function.Injective (diagram P data w s) := by
    intro s
    cases s with
    | left => exact hleft
    | right => exact hright
  have hpushLeft : Function.Injective (pushLeft P data w) :=
    Monoid.PushoutI.of_injective hdiagram Side.left
  have holdLeft : Function.Injective (oldLeft P) :=
    Monoid.Coprod.inl_injective
  have hwOld : P.evalWord w = 1 := by
    apply holdLeft
    apply hpushLeft
    simpa using hwWitness
  exact hw ((P.wordProblem_iff_evalWord_eq_one w).mpr hwOld)

end Undecidability.Gordon.Amalgam
