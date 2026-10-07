/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Mod5.BaseWords
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.CoefficientSigns
public import LeanPool.SmallUndecidableGroups.Borisov.Mod5.WordLength
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.ConditionalConverse

/-!
# Evaluating positive rank-five words in the mod-five quotient

This file connects the displayed `u`- and `v`-basis lifts in Borisov's
two-HNN group with the explicit evaluator in
`GroupUndecidability.Borisov.Mod5.BaseWords`.
For a positive freely reduced word, inverses do not occur, so evaluation is
just the product of the corresponding quotient basis elements.
-/

@[expose] public section

namespace Undecidability
namespace BorisovModFiveEvalBridge

open BorisovHNNModel
open BorisovCStage
open BorisovCoefficientShapes
open BorisovCoefficientSignComparison
open BorisovModFiveQuotient
open BorisovModFiveBaseWords

noncomputable section

/-- The indices of the stable and rewriting-rule basis elements. -/
abbrev Basis := BorisovCStage.RuleBasis

@[simp] theorem gamma3ToQuotient_stable3 (beta : Fin 2) :
    gamma3ToQuotient (stable3 beta) = quotientStable := by
  fin_cases beta <;> simp [stable3]

@[simp] theorem gamma3ToQuotient_positive3 (word : List (Fin 2)) :
    gamma3ToQuotient (positive3 word) = quotientStable ^ word.length := by
  induction word with
  | nil => simp [positive3, Thue.evalPositive]
  | cons beta word ih =>
      have hcons : positive3 (beta :: word) =
          stable3 beta * positive3 word := by
        simp [positive3, Thue.evalPositive, stable3]
      rw [hcons, map_mul, gamma3ToQuotient_stable3, ih,
        List.length_cons, pow_succ']

@[simp] theorem gamma3ToQuotient_uBasis
    (datum : Thue.StandingDatum) (q : Basis) :
    gamma3ToQuotient (uBasis datum q) = quotientBasis datum.F q := by
  cases q with
  | inl beta => simp [uBasis, quotientBasis]
  | inr i =>
      simp [uBasis, a3, quotientBasis, map_mul, map_pow]

@[simp] theorem gamma3ToQuotient_vBasis
    (datum : Thue.StandingDatum) (q : Basis) :
    gamma3ToQuotient (vBasis datum q) = quotientBasis datum.E q := by
  cases q with
  | inl beta => simp [vBasis, quotientBasis]
  | inr i =>
      simp [vBasis, b3, quotientBasis, map_mul, map_pow]

/-- A positive source-basis word is evaluated by the explicit mod-five
quotient evaluator after forgetting its (necessarily positive) signs. -/
theorem gamma3ToQuotient_uLift_of_allPositive
    (datum : Thue.StandingDatum) (w : FreeGroup Basis)
    (hpositive : AllPositive w.toWord) :
    gamma3ToQuotient (uLift datum w) =
      quotientEval datum.F (w.toWord.map Prod.fst) := by
  calc
    gamma3ToQuotient (uLift datum w) =
        gamma3ToQuotient (uLift datum (FreeGroup.mk w.toWord)) := by
      rw [FreeGroup.mk_toWord]
    _ = quotientEval datum.F (w.toWord.map Prod.fst) := by
      simp only [uLift, FreeGroup.lift_mk, map_list_prod, List.map_map,
        quotientEval]
      apply congrArg List.prod
      apply List.map_congr_left
      rintro ⟨q, sign⟩ hmem
      have hsign : sign = true :=
        (allPositive_iff_forall_sign w.toWord).mp hpositive
          (q, sign) hmem
      subst sign
      simp

/-- Target-basis counterpart of
`gamma3ToQuotient_uLift_of_allPositive`. -/
theorem gamma3ToQuotient_vLift_of_allPositive
    (datum : Thue.StandingDatum) (w : FreeGroup Basis)
    (hpositive : AllPositive w.toWord) :
    gamma3ToQuotient (vLift datum w) =
      quotientEval datum.E (w.toWord.map Prod.fst) := by
  calc
    gamma3ToQuotient (vLift datum w) =
        gamma3ToQuotient (vLift datum (FreeGroup.mk w.toWord)) := by
      rw [FreeGroup.mk_toWord]
    _ = quotientEval datum.E (w.toWord.map Prod.fst) := by
      simp only [vLift, FreeGroup.lift_mk, map_list_prod, List.map_map,
        quotientEval]
      apply congrArg List.prod
      apply List.map_congr_left
      rintro ⟨q, sign⟩ hmem
      have hsign : sign = true :=
        (allPositive_iff_forall_sign w.toWord).mp hpositive
          (q, sign) hmem
      subst sign
      simp

end

end BorisovModFiveEvalBridge
end Undecidability

/-!
# Rule sparsity from the mod-five Borisov quotient

In the quotient `(C₅ * C₅) ⋊ ℤ`, both stable letters act by factorwise
inversion.  A positive displayed rule contributes two alternating nonzero
free-product syllables.  The padded coefficient `d^f Q e^r`, on the other
hand, has at most one syllable in each free factor.  Equality therefore forces
the displayed rank-five word to contain at most one rule letter.
-/

namespace Undecidability
namespace BorisovModFiveSparsity

open Monoid
open BorisovHNNModel
open BorisovCStage
open BorisovCoefficientShapes
open BorisovCoefficientSignComparison
open BorisovModFiveQuotient
open BorisovModFiveBaseWords
open BorisovModFiveEvalBridge
open BorisovModFiveWordLength
open CoprodIWordLength

noncomputable section

/-- The indices of the stable and rewriting-rule basis elements. -/
abbrev Basis := BorisovCStage.RuleBasis

@[simp] theorem basisRuleCount_map_fst
    (letters : List (Basis × Bool)) :
    basisRuleCount (letters.map Prod.fst) = ruleCount letters := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨q, sign⟩
      cases q <;> simp [basisRuleCount, ruleCount, ih]

@[simp] theorem quotientBase_zpow_left (x : ModFiveBase) (n : ℤ) :
    (quotientBase x ^ n).left = x ^ n := by
  rw [← map_zpow]
  rfl

@[simp] theorem quotientBase_zpow_right (x : ModFiveBase) (n : ℤ) :
    (quotientBase x ^ n).right = 1 := by
  rw [← map_zpow]
  rfl

theorem quotient_coefficient_left
    (Q : List (Fin 2)) (f r : ℤ) :
    (gamma3ToQuotient (d3 ^ f * positive3 Q * e3 ^ r)).left =
      modD ^ f * (invertFactors ^ Q.length) (modE ^ r) := by
  simp only [map_mul, map_zpow, gamma3ToQuotient_d3,
    gamma3ToQuotient_positive3, gamma3ToQuotient_e3,
    SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    quotientBase_zpow_left, quotientBase_zpow_right,
    quotientStable_pow_left, quotientStable_pow_right,
    inversionAction_nat, one_mul]
  simp

theorem modD_zpow_as_letter (f : ℤ) :
    modD ^ f =
      CoprodI.of (M := Factor5) (i := (0 : Fin 2)) (c5Generator ^ f) := by
  change (CoprodI.of (M := Factor5) (i := (0 : Fin 2))
      c5Generator) ^ f = _
  rw [← map_zpow]

theorem twisted_modE_zpow_as_letter (n : ℕ) (r : ℤ) :
    (invertFactors ^ n) (modE ^ r) =
      CoprodI.of (M := Factor5) (i := (1 : Fin 2))
        ((invertC5 ^ n) (c5Generator ^ r)) := by
  rw [show modE = CoprodI.of (M := Factor5) (i := (1 : Fin 2))
    c5Generator by rfl, ← map_zpow]
  exact invertFactors_pow_of n (1 : Fin 2) (c5Generator ^ r)

theorem coefficient_normalForm_length_le_two
    (Q : List (Fin 2)) (f r : ℤ) :
    (CoprodI.Word.equiv
      (modD ^ f * (invertFactors ^ Q.length) (modE ^ r))).toList.length ≤ 2 := by
  rw [modD_zpow_as_letter, twisted_modE_zpow_as_letter]
  exact normalForm_length_factor_zero_one_le_two
    (c5Generator ^ f) ((invertC5 ^ Q.length) (c5Generator ^ r))

/-! ## The source and target parsers -/

/-- The source-basis word representing a padded positive coefficient contains
at most one displayed Thue-rule letter. -/
theorem u_ruleCount_le_one
    (datum : Thue.StandingDatum)
    (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis)
    (heval : uLift datum w = d3 ^ f * positive3 Q * e3 ^ r) :
    ruleCount w.toWord ≤ 1 := by
  have hpositive :=
    u_allPositive_of_coefficient_eq datum Q f r w heval
  have hquot := congrArg gamma3ToQuotient heval
  rw [gamma3ToQuotient_uLift_of_allPositive datum w hpositive] at hquot
  have hleft := congrArg SemidirectProduct.left hquot
  rw [quotientEval_left, quotient_coefficient_left] at hleft
  have hlength := congrArg
    (fun x : ModFiveBase ↦
      (CoprodI.Word.equiv x).toList.length) hleft
  rw [normalForm_letterProd_length, basisRuleCount_map_fst] at hlength
  have hright := coefficient_normalForm_length_le_two Q f r
  omega

/-- Target-basis counterpart of `u_ruleCount_le_one`. -/
theorem v_ruleCount_le_one
    (datum : Thue.StandingDatum)
    (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis)
    (heval : vLift datum w = d3 ^ f * positive3 Q * e3 ^ r) :
    ruleCount w.toWord ≤ 1 := by
  have hpositive :=
    v_allPositive_of_coefficient_eq datum Q f r w heval
  have hquot := congrArg gamma3ToQuotient heval
  rw [gamma3ToQuotient_vLift_of_allPositive datum w hpositive] at hquot
  have hleft := congrArg SemidirectProduct.left hquot
  rw [quotientEval_left, quotient_coefficient_left] at hleft
  have hlength := congrArg
    (fun x : ModFiveBase ↦
      (CoprodI.Word.equiv x).toList.length) hleft
  rw [normalForm_letterProd_length, basisRuleCount_map_fst] at hlength
  have hright := coefficient_normalForm_length_le_two Q f r
  omega

/-- Borisov's converse criterion obtained from the mod-five free-product
rule-count bound. -/
theorem criterion_converse
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  BorisovConditionalConverse.criterion_converse_of_sparse_parsers datum
    (u_ruleCount_le_one datum) (v_ruleCount_le_one datum) Q

end

end BorisovModFiveSparsity
end Undecidability
