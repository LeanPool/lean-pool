/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Mod5.Quotient

/-!
# Free-product syllables in the mod-five Borisov quotient

This file computes the base coordinate of a positive displayed rank-five
word in `BorisovModFiveQuotient.QuotientGroup`.  Every rule letter contributes
one nontrivial `d` syllable followed by one nontrivial `e` syllable.  Stable
letters change only the inversion parity and hence never remove a syllable.
-/

@[expose] public section

namespace Undecidability
namespace BorisovModFiveBaseWords

open Monoid
open BorisovHNNModel
open BorisovCStage
open BorisovModFiveQuotient

noncomputable section

/-- The two stable-generator indices and the three rewriting-rule indices. -/
abbrev Basis := BorisovCStage.RuleBasis
/-- A cyclic group of order five assigned to each base-factor label. -/
abbrev Factor5 (_ : Fin 2) := C5
/-- A nonidentity base-factor letter paired with its factor label. -/
abbrev BaseLetter := Σ i : Fin 2, Factor5 i

/-- Inversion of the cyclic factor, as an automorphism. -/
def invertC5 : MulAut C5 where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x
  map_mul' x y := by simp [mul_comm]

@[simp] theorem invertFactors_pow_of (n : ℕ) (i : Fin 2) (x : C5) :
    (invertFactors ^ n) (CoprodI.of (M := Factor5) (i := i) x) =
      CoprodI.of (M := Factor5) (i := i) ((invertC5 ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change (invertFactors ^ n)
          (invertFactors (CoprodI.of (M := Factor5) (i := i) x)) =
        CoprodI.of (M := Factor5) (i := i) ((invertC5 ^ n) (invertC5 x))
      rw [show invertFactors (CoprodI.of (M := Factor5) (i := i) x) =
        CoprodI.of (M := Factor5) (i := i) x⁻¹ by simp [invertFactors]]
      rw [ih (x⁻¹)]
      rfl

/-- Apply the parity accumulated in `n` stable letters to one base syllable. -/
def twistLetter (n : ℕ) : BaseLetter → BaseLetter
  | ⟨i, x⟩ => ⟨i, (invertC5 ^ n) x⟩

@[simp] theorem twistLetter_fst (n : ℕ) (x : BaseLetter) :
    (twistLetter n x).1 = x.1 := by cases x; rfl

theorem twistLetter_ne_one (n : ℕ) (x : BaseLetter) (hx : x.2 ≠ 1) :
    (twistLetter n x).2 ≠ 1 := by
  rcases x with ⟨i, x⟩
  change (invertC5 ^ n) x ≠ 1
  intro h
  apply hx
  apply (invertC5 ^ n).injective
  simpa using h

/-- Product of a list of free-product letters. -/
def letterProd (letters : List BaseLetter) : ModFiveBase :=
  (letters.map fun x => CoprodI.of (M := Factor5) (i := x.1) x.2).prod

@[simp] theorem letterProd_cons (x : BaseLetter) (xs : List BaseLetter) :
    letterProd (x :: xs) =
      CoprodI.of (M := Factor5) (i := x.1) x.2 * letterProd xs := by
  simp [letterProd]

@[simp] theorem letterProd_append (xs ys : List BaseLetter) :
    letterProd (xs ++ ys) = letterProd xs * letterProd ys := by
  simp [letterProd, List.map_append]

@[simp] theorem invertFactors_pow_letterProd (n : ℕ)
    (letters : List BaseLetter) :
    (invertFactors ^ n) (letterProd letters) =
      letterProd (letters.map (twistLetter n)) := by
  induction letters with
  | nil => simp [letterProd]
  | cons x xs ih =>
      rcases x with ⟨i, x⟩
      rw [letterProd_cons, map_mul, invertFactors_pow_of, ih]
      simp [letterProd]
      rfl

/-- Stable-letter weight of a displayed basis letter in the source or target
system determined by `rules`. -/
def stableWeight (rules : Fin 3 → List (Fin 2)) : Basis → ℕ
  | .inl _ => 1
  | .inr i => (rules i).length

/-- Number of rule letters in a positive displayed word. -/
def basisRuleCount : List Basis → ℕ
  | [] => 0
  | .inl _ :: rest => basisRuleCount rest
  | .inr _ :: rest => basisRuleCount rest + 1

/-- The two alternating base syllables contributed by one rule letter. -/
def rulePair (rules : Fin 3 → List (Fin 2)) (i : Fin 3) :
    List BaseLetter :=
  [⟨0, c5Generator ^ (i.val + 1)⟩,
    ⟨1, (invertC5 ^ (rules i).length) (c5Generator ^ (i.val + 1))⟩]

/-- Reduced base-syllable trace of the evaluation of a positive displayed
word.  The tail is twisted by the stable weight of its head. -/
def baseLetters (rules : Fin 3 → List (Fin 2)) : List Basis → List BaseLetter
  | [] => []
  | .inl _ :: rest =>
      (baseLetters rules rest).map (twistLetter 1)
  | .inr i :: rest =>
      rulePair rules i ++
        (baseLetters rules rest).map (twistLetter (rules i).length)

@[simp] theorem baseLetters_length (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    (baseLetters rules letters).length = 2 * basisRuleCount letters := by
  induction letters with
  | nil => rfl
  | cons q rest ih =>
      cases q with
      | inl beta => simp [baseLetters, basisRuleCount, ih]
      | inr i => simp [baseLetters, basisRuleCount, rulePair, ih, Nat.mul_add]

/-- Image in the quotient of one positive displayed basis letter. -/
def quotientBasis (rules : Fin 3 → List (Fin 2)) : Basis → QuotientGroup
  | .inl _ => quotientStable
  | .inr i =>
      quotientBase (modD ^ (i.val + 1)) *
        quotientStable ^ (rules i).length *
        quotientBase (modE ^ (i.val + 1))

/-- The quotient-group product of the indicated rule-basis letters. -/
def quotientEval (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) : QuotientGroup :=
  (letters.map (quotientBasis rules)).prod

@[simp] theorem quotientStable_pow_left (n : ℕ) :
    (quotientStable ^ n).left = 1 := by
  let g : Multiplicative ℤ := Multiplicative.ofAdd 1
  have hp : (SemidirectProduct.inr g : QuotientGroup) ^ n =
      SemidirectProduct.inr (g ^ n) :=
    (map_pow (SemidirectProduct.inr : Multiplicative ℤ →* QuotientGroup) g n).symm
  change ((SemidirectProduct.inr g : QuotientGroup) ^ n).left = 1
  rw [hp]
  rfl

@[simp] theorem quotientStable_pow_right (n : ℕ) :
    (quotientStable ^ n).right = Multiplicative.ofAdd (n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, SemidirectProduct.mul_right, ih]
      apply Multiplicative.toAdd.injective
      simp [quotientStable]

@[simp] theorem quotientBase_left (x : ModFiveBase) :
    (quotientBase x).left = x := rfl

@[simp] theorem quotientBase_right (x : ModFiveBase) :
    (quotientBase x).right = 1 := rfl

@[simp] theorem quotientBase_pow_right (x : ModFiveBase) (n : ℕ) :
    (quotientBase x ^ n).right = 1 := by
  have hp : (SemidirectProduct.inl x : QuotientGroup) ^ n =
      SemidirectProduct.inl (x ^ n) :=
    (map_pow (SemidirectProduct.inl : ModFiveBase →* QuotientGroup) x n).symm
  change ((SemidirectProduct.inl x : QuotientGroup) ^ n).right = _
  rw [hp]
  rfl

@[simp] theorem inversionAction_nat (n : ℕ) :
    inversionAction (Multiplicative.ofAdd (n : ℤ)) = invertFactors ^ n := by
  simp [inversionAction]

@[simp] theorem invertFactors_pow_modE (n : ℕ) :
    (invertFactors ^ n) modE =
      CoprodI.of (M := Factor5) (i := (1 : Fin 2))
        ((invertC5 ^ n) c5Generator) := by
  simp [modE]

@[simp] theorem quotientBasis_right
    (rules : Fin 3 → List (Fin 2)) (q : Basis) :
    (quotientBasis rules q).right =
      Multiplicative.ofAdd (stableWeight rules q : ℤ) := by
  cases q with
  | inl beta => simp [quotientBasis, stableWeight, quotientStable]
  | inr i =>
      simp only [quotientBasis, SemidirectProduct.mul_right,
        quotientBase_right, quotientStable_pow_right,
        one_mul, mul_one, stableWeight]

@[simp] theorem quotientBasis_left_stable
    (rules : Fin 3 → List (Fin 2)) (beta : Fin 2) :
    (quotientBasis rules (.inl beta)).left = 1 := by
  simp [quotientBasis, quotientStable]

@[simp] theorem quotientBasis_left_rule
    (rules : Fin 3 → List (Fin 2)) (i : Fin 3) :
    (quotientBasis rules (.inr i)).left = letterProd (rulePair rules i) := by
  simp only [quotientBasis, SemidirectProduct.mul_left,
    quotientBase_left, quotientBase_right,
    quotientStable_pow_left]
  simp [rulePair, letterProd, invertFactors_pow_modE, modD, map_pow]

/-- Exact base-coordinate evaluation formula. -/
@[simp] theorem quotientEval_left
    (rules : Fin 3 → List (Fin 2)) (letters : List Basis) :
    (quotientEval rules letters).left = letterProd (baseLetters rules letters) := by
  induction letters with
  | nil => rfl
  | cons q rest ih =>
      cases q with
      | inl beta =>
          change (quotientBasis rules (.inl beta) *
            quotientEval rules rest).left = _
          rw [SemidirectProduct.mul_left, quotientBasis_left_stable,
            quotientBasis_right, ih, one_mul]
          simp only [stableWeight, baseLetters]
          simpa using (invertFactors_pow_letterProd 1 (baseLetters rules rest))
      | inr i =>
          change (quotientBasis rules (.inr i) *
            quotientEval rules rest).left = _
          rw [SemidirectProduct.mul_left, quotientBasis_left_rule,
            quotientBasis_right, ih]
          simp only [stableWeight, inversionAction_nat,
            baseLetters, letterProd_append]
          rw [invertFactors_pow_letterProd]

end

end BorisovModFiveBaseWords
end Undecidability
