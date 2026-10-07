/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.Construction
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.Tactic.FinCases

/-!
# Amalgam

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability
namespace MillerTancer
namespace Amalgam

open Monoid

/-- The factor containing the old presented group and the new letters `alpha`, `beta`. -/
abbrev LeftFactor (P : FP n m) :=
  Monoid.Coprod P.Group (FreeGroup (Fin 2))

/-- The free factor on the separate copies of `beta` and `gamma`. -/
abbrev RightFactor := FreeGroup (Fin 2)

/-- The inclusion of the original presented group into the left factor. -/
def oldLeft (P : FP n m) : P.Group →* LeftFactor P :=
  Monoid.Coprod.inl

/-- The element `alpha` in the left factor. -/
def alphaLeft (P : FP n m) : LeftFactor P :=
  Monoid.Coprod.inr (FreeGroup.of (0 : Fin 2))

/-- The element `beta` in the left factor. -/
def betaLeft (P : FP n m) : LeftFactor P :=
  Monoid.Coprod.inr (FreeGroup.of (1 : Fin 2))

/-- The element `beta` in the right factor. -/
def betaRight : RightFactor :=
  FreeGroup.of (0 : Fin 2)

/-- The element `gamma` in the right factor. -/
def gammaRight : RightFactor :=
  FreeGroup.of (1 : Fin 2)

/-- The five proposed free generators in the left factor. -/
def leftBasis (P : FP n m) (z w : Word n) : Fin 5 → LeftFactor P :=
  ![betaLeft P,
    (alphaLeft P)⁻¹ * betaLeft P * alphaLeft P,
    ((alphaLeft P) ^ 2)⁻¹ * (betaLeft P)⁻¹ * alphaLeft P *
      betaLeft P * (alphaLeft P) ^ 2,
    ((alphaLeft P) ^ 3)⁻¹ *
      ((oldLeft P (P.evalWord w))⁻¹ * (betaLeft P)⁻¹ *
        oldLeft P (P.evalWord w) * betaLeft P) *
      (alphaLeft P) ^ 3,
    ((alphaLeft P) ^ 2)⁻¹ * oldLeft P (P.evalWord z) * betaLeft P *
      (alphaLeft P) ^ 4]

/-- The five proposed free generators in the right factor. -/
def rightBasis : Fin 5 → RightFactor :=
  ![betaRight,
    gammaRight⁻¹ * betaRight⁻¹ * gammaRight * betaRight * gammaRight,
    (gammaRight ^ 2)⁻¹ * betaRight⁻¹ * gammaRight * betaRight * gammaRight ^ 2,
    (gammaRight ^ 3)⁻¹ * betaRight * gammaRight ^ 3,
    (gammaRight ^ 4)⁻¹ * betaRight * gammaRight ^ 4]

/-- The homomorphism freely extending the left amalgamating basis. -/
def leftMap (P : FP n m) (z w : Word n) :
    FreeGroup (Fin 5) →* LeftFactor P :=
  FreeGroup.lift (leftBasis P z w)

/-- The homomorphism freely extending the right amalgamating basis. -/
def rightMap : FreeGroup (Fin 5) →* RightFactor :=
  FreeGroup.lift rightBasis

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
def diagram (P : FP n m) (z w : Word n) :
    (s : Side) → FreeGroup (Fin 5) →* Factor P s
  | .left => leftMap P z w
  | .right => rightMap

/-- The group obtained by taking the pushout of the amalgamation diagram. -/
abbrev Pushout (P : FP n m) (z w : Word n) :=
  Monoid.PushoutI (diagram P z w)

/-- The canonical homomorphism from the left factor into the pushout. -/
def pushLeft (P : FP n m) (z w : Word n) :
    LeftFactor P →* Pushout P z w :=
  Monoid.PushoutI.of (φ := diagram P z w) Side.left

/-- The canonical homomorphism from the right factor into the pushout. -/
def pushRight (P : FP n m) (z w : Word n) :
    RightFactor →* Pushout P z w :=
  Monoid.PushoutI.of (φ := diagram P z w) Side.right

theorem identifies_basis (P : FP n m) (z w : Word n) (i : Fin 5) :
    pushLeft P z w (leftBasis P z w i) =
      pushRight P z w (rightBasis i) := by
  have hleft := Monoid.PushoutI.of_apply_eq_base
    (diagram P z w) Side.left (FreeGroup.of i)
  have hright := Monoid.PushoutI.of_apply_eq_base
    (diagram P z w) Side.right (FreeGroup.of i)
  change pushLeft P z w ((leftMap P z w) (FreeGroup.of i)) = _ at hleft
  change pushRight P z w (rightMap (FreeGroup.of i)) = _ at hright
  simpa [leftMap, rightMap] using hleft.trans hright.symm

theorem identifies_beta (P : FP n m) (z w : Word n) :
    pushLeft P z w (betaLeft P) = pushRight P z w betaRight := by
  simpa [leftBasis, rightBasis] using identifies_basis P z w (0 : Fin 5)

/-- Interpretation of the generators of the transformed presentation in the amalgam. -/
def witnessGenerator (P : FP n m) (z w : Word n) :
    Fin (n + 3) → Pushout P z w :=
  Fin.addCases
    (fun i => pushLeft P z w (oldLeft P (PresentedGroup.of i)))
    ![pushLeft P z w (alphaLeft P),
      pushLeft P z w (betaLeft P),
      pushRight P z w gammaRight]

@[simp]
theorem witnessGenerator_old (P : FP n m) (z w : Word n) (i : Fin n) :
    witnessGenerator P z w (oldGenerator i) =
      pushLeft P z w (oldLeft P (PresentedGroup.of i)) := by
  simp [witnessGenerator, oldGenerator]

@[simp]
theorem witnessGenerator_alpha (P : FP n m) (z w : Word n) :
    witnessGenerator P z w (Fin.natAdd n 0) =
      pushLeft P z w (alphaLeft P) := by
  simp [witnessGenerator]

@[simp]
theorem witnessGenerator_beta (P : FP n m) (z w : Word n) :
    witnessGenerator P z w (Fin.natAdd n 1) =
      pushLeft P z w (betaLeft P) := by
  simp [witnessGenerator]

@[simp]
theorem witnessGenerator_gamma (P : FP n m) (z w : Word n) :
    witnessGenerator P z w (Fin.natAdd n 2) =
      pushRight P z w gammaRight := by
  simp [witnessGenerator]

theorem eval_oldWord_witness (P : FP n m) (z w u : Word n) :
    Word.eval (witnessGenerator P z w) (oldWord u) =
      pushLeft P z w (oldLeft P (P.evalWord u)) := by
  rw [oldWord, Word.eval_mapGenerators]
  have hfun : witnessGenerator P z w ∘ oldGenerator =
      ((pushLeft P z w).comp (oldLeft P) ∘
        (PresentedGroup.of : Fin n → P.Group)) := by
    funext i
    exact witnessGenerator_old P z w i
  rw [hfun]
  rw [← Word.map_eval ((pushLeft P z w).comp (oldLeft P))
    (PresentedGroup.of : Fin n → P.Group) u]
  rfl

theorem eval_oldGenerators_witness (P : FP n m) (z w u : Word n) :
    Word.eval
        (fun i => pushLeft P z w (oldLeft P (PresentedGroup.of i))) u =
      pushLeft P z w (oldLeft P (P.evalWord u)) := by
  convert (Word.map_eval ((pushLeft P z w).comp (oldLeft P))
    (PresentedGroup.of : Fin n → P.Group) u).symm using 1 <;>
    simp [Function.comp_def, FP.evalWord]

theorem eval_sigma₁_witness (P : FP n m) (z w : Word n) :
    Word.eval (witnessGenerator P z w) (sigma₁ n) = 1 := by
  rw [sigma₁, Word.eval_relation_eq_one_iff]
  simpa [sigma₁, leftBasis, rightBasis, alphaWord, betaWord, gammaWord,
    Word.product, identifies_beta P z w, mul_assoc] using
      identifies_basis P z w (1 : Fin 5)

theorem eval_sigma₂_witness (P : FP n m) (z w : Word n) :
    Word.eval (witnessGenerator P z w) (sigma₂ n) = 1 := by
  rw [sigma₂, Word.eval_relation_eq_one_iff]
  simpa [sigma₂, leftBasis, rightBasis, alphaWord, betaWord, gammaWord,
    Word.product, identifies_beta P z w, mul_assoc] using
      identifies_basis P z w (2 : Fin 5)

theorem eval_sigma₃_witness (P : FP n m) (z w : Word n) :
    Word.eval (witnessGenerator P z w) (sigma₃ w) = 1 := by
  rw [sigma₃, Word.eval_relation_eq_one_iff]
  simpa [sigma₃, leftBasis, rightBasis, alphaWord, betaWord, gammaWord,
    Word.product, identifies_beta P z w, eval_oldWord_witness,
    eval_oldGenerators_witness, mul_assoc] using
      identifies_basis P z w (3 : Fin 5)

theorem eval_sigma₄_witness (P : FP n m) (z w : Word n) :
    Word.eval (witnessGenerator P z w) (sigma₄ z) = 1 := by
  rw [sigma₄, Word.eval_relation_eq_one_iff]
  simpa [sigma₄, leftBasis, rightBasis, alphaWord, betaWord, gammaWord,
    Word.product, identifies_beta P z w, eval_oldWord_witness,
    eval_oldGenerators_witness, mul_assoc] using
      identifies_basis P z w (4 : Fin 5)

theorem transformed_relator_eq_one (P : FP n m) (z w : Word n)
    (i : Fin (m + 4)) :
    Word.eval (witnessGenerator P z w) ((transform P z w).relator i) = 1 := by
  cases i using Fin.addCases with
  | left j =>
      rw [transform_old, eval_oldWord_witness, P.relator_eq_one]
      simp
  | right j =>
      rw [transform_additional]
      fin_cases j
      · exact eval_sigma₁_witness P z w
      · exact eval_sigma₂_witness P z w
      · exact eval_sigma₃_witness P z w
      · exact eval_sigma₄_witness P z w

/-- The relator-preserving homomorphism from the transformed presentation into the amalgam. -/
def witnessHom (P : FP n m) (z w : Word n) :
    (transform P z w).Group →* Pushout P z w :=
  (transform P z w).homOfRelators (witnessGenerator P z w)
    (transformed_relator_eq_one P z w)

@[simp]
theorem witnessHom_of (P : FP n m) (z w : Word n) (i : Fin (n + 3)) :
    witnessHom P z w (PresentedGroup.of i) = witnessGenerator P z w i :=
  (transform P z w).homOfRelators_of _ _ i

/--
The amalgamated-product half of the Miller--Tancer construction, conditional only on
the two separated-conjugates maps being injective.
-/
theorem transform_not_trivial_of_basis_injective
    (P : FP n m) (z w : Word n)
    (hleft : Function.Injective (leftMap P z w))
    (hright : Function.Injective rightMap)
    (hw : ¬ P.wordProblem w) :
    ¬ (transform P z w).presentsTrivial := by
  intro htrivial
  have hwT : (transform P z w).wordProblem (oldWord w) :=
    htrivial (oldWord w)
  have hwEval : (transform P z w).evalWord (oldWord w) = 1 :=
    ((transform P z w).wordProblem_iff_evalWord_eq_one (oldWord w)).mp hwT
  have heval :
      witnessHom P z w ((transform P z w).evalWord (oldWord w)) =
        Word.eval (witnessGenerator P z w) (oldWord w) :=
    (transform P z w).homOfRelators_evalWord (witnessGenerator P z w)
      (transformed_relator_eq_one P z w) (oldWord w)
  have hwWitness : Word.eval (witnessGenerator P z w) (oldWord w) = 1 := by
    rw [← heval, hwEval, map_one]
  rw [eval_oldWord_witness] at hwWitness
  have hdiagram : ∀ s, Function.Injective (diagram P z w s) := by
    intro s
    cases s with
    | left => exact hleft
    | right => exact hright
  have hpushLeft : Function.Injective (pushLeft P z w) :=
    Monoid.PushoutI.of_injective hdiagram Side.left
  have holdLeft : Function.Injective (oldLeft P) :=
    Monoid.Coprod.inl_injective
  have hwOld : P.evalWord w = 1 := by
    apply holdLeft
    apply hpushLeft
    simpa using hwWitness
  exact hw ((P.wordProblem_iff_evalWord_eq_one w).mpr hwOld)

end Amalgam
end MillerTancer
end Undecidability
