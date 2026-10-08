/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.Lemma4Pinch
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.AssertionIVBoundary

/-!
# Concrete one-rule cases of Borisov's pinch classifier

`BorisovLemma4Pinch.PinchClassification` asks for a classification of every
coefficient of the form `d^f Q e^r` lying in one of the two rank-five
subgroups.  The central normal-form step shows that its unique
rank-five preimage contains either no rule letter or exactly one rule letter.

This file proves the complete coefficient calculation in the latter case:
if the coefficient is a positive stable prefix, followed by one displayed
rule generator, followed by a positive stable suffix, then conjugating by
the `c`-HNN equivalence performs exactly the corresponding Thue rewrite and
again has the required `d^f Q e^r` shape.
-/

@[expose] public section

namespace Undecidability
namespace BorisovPinchCoefficientClassification

open BorisovCStage
open BorisovHNNModel

noncomputable section

/-! ## Moving padding powers across positive stable words -/

private theorem stable3_mul_d (beta : Fin 2) :
    stable3 beta * d3 = d3 ^ 4 * stable3 beta := by
  fin_cases beta
  · simpa [stable3] using gamma3_d_four_mul_s1.symm
  · simpa [stable3] using gamma3_s2_mul_d

private theorem e_mul_stable3 (beta : Fin 2) :
    e3 * stable3 beta = stable3 beta * e3 ^ 4 := by
  fin_cases beta
  · simpa [stable3] using gamma3_e_mul_s1
  · simpa [stable3] using gamma3_e_mul_s2

theorem stable3_mul_d_zpow (beta : Fin 2) (n : ℤ) :
    stable3 beta * d3 ^ n = d3 ^ (4 * n) * stable3 beta := by
  have hconj :
      stable3 beta * d3 * (stable3 beta)⁻¹ = d3 ^ 4 := by
    calc
      stable3 beta * d3 * (stable3 beta)⁻¹ =
          (d3 ^ 4 * stable3 beta) * (stable3 beta)⁻¹ := by
            rw [stable3_mul_d]
      _ = d3 ^ 4 := by simp
  have hzpow :
      stable3 beta * d3 ^ n * (stable3 beta)⁻¹ =
        (stable3 beta * d3 * (stable3 beta)⁻¹) ^ n := by
    simp
  calc
    stable3 beta * d3 ^ n =
        (stable3 beta * d3 ^ n * (stable3 beta)⁻¹) * stable3 beta := by
          group
    _ = (stable3 beta * d3 * (stable3 beta)⁻¹) ^ n * stable3 beta := by
          rw [hzpow]
    _ = (d3 ^ 4) ^ n * stable3 beta := by rw [hconj]
    _ = d3 ^ (4 * n) * stable3 beta :=
      congrArg (fun x => x * stable3 beta) (zpow_mul d3 4 n).symm

theorem e_zpow_mul_stable3 (beta : Fin 2) (n : ℤ) :
    e3 ^ n * stable3 beta = stable3 beta * e3 ^ (4 * n) := by
  have hconj :
      (stable3 beta)⁻¹ * e3 * stable3 beta = e3 ^ 4 := by
    calc
      (stable3 beta)⁻¹ * e3 * stable3 beta =
          (stable3 beta)⁻¹ * (stable3 beta * e3 ^ 4) := by
            simp only [mul_assoc]
            rw [← e_mul_stable3]
      _ = e3 ^ 4 := by simp
  have hzpow :
      (stable3 beta)⁻¹ * e3 ^ n * stable3 beta =
        ((stable3 beta)⁻¹ * e3 * stable3 beta) ^ n := by
    simpa [MulAut.conj_apply] using
      (map_zpow (MulAut.conj (stable3 beta)⁻¹) e3 n)
  calc
    e3 ^ n * stable3 beta = stable3 beta *
        ((stable3 beta)⁻¹ * e3 ^ n * stable3 beta) := by
          group
    _ = stable3 beta *
        (((stable3 beta)⁻¹ * e3 * stable3 beta) ^ n) := by
          rw [hzpow]
    _ = stable3 beta * (e3 ^ 4) ^ n := by rw [hconj]
    _ = stable3 beta * e3 ^ (4 * n) :=
      congrArg (fun x => stable3 beta * x) (zpow_mul e3 4 n).symm

theorem positive3_mul_d_zpow (w : List (Fin 2)) (n : ℤ) :
    positive3 w * d3 ^ n =
      d3 ^ ((4 : ℤ) ^ w.length * n) * positive3 w := by
  induction w generalizing n with
  | nil => simp [positive3, Thue.evalPositive]
  | cons beta w ih =>
      have hcons : positive3 (beta :: w) = stable3 beta * positive3 w := by
        fin_cases beta <;> simp [positive3, stable3, Thue.evalPositive]
      rw [hcons, mul_assoc, ih, ← mul_assoc,
        stable3_mul_d_zpow, mul_assoc]
      congr 2
      simp only [List.length_cons, pow_succ]
      ring

theorem e_zpow_mul_positive3 (w : List (Fin 2)) (n : ℤ) :
    e3 ^ n * positive3 w =
      positive3 w * e3 ^ ((4 : ℤ) ^ w.length * n) := by
  induction w generalizing n with
  | nil => simp [positive3, Thue.evalPositive]
  | cons beta w ih =>
      have hcons : positive3 (beta :: w) = stable3 beta * positive3 w := by
        fin_cases beta <;> simp [positive3, stable3, Thue.evalPositive]
      rw [hcons, ← mul_assoc, e_zpow_mul_stable3, mul_assoc, ih (4 * n),
        ← mul_assoc]
      congr 2
      simp only [List.length_cons, pow_succ]
      ring

theorem positive3_mul_d_pow (w : List (Fin 2)) (n : ℕ) :
    positive3 w * d3 ^ n =
      d3 ^ ((4 : ℤ) ^ w.length * (n : ℤ)) * positive3 w := by
  simpa only [zpow_natCast] using
    positive3_mul_d_zpow w (n : ℤ)

theorem e_pow_mul_positive3 (w : List (Fin 2)) (n : ℕ) :
    e3 ^ n * positive3 w =
      positive3 w * e3 ^ ((4 : ℤ) ^ w.length * (n : ℤ)) := by
  simpa only [zpow_natCast] using
    e_zpow_mul_positive3 w (n : ℤ)

/-! ## The displayed bases as elements of their range subgroups -/

/-- A generator of the source rewriting-rule subgroup, with its subgroup membership witness. -/
def sourceBasis (datum : Thue.StandingDatum) (q : RuleBasis) : U datum :=
  ⟨uBasis datum q, ⟨FreeGroup.of q, by simp [uLift]⟩⟩

/-- The corresponding generator of the target rewriting-rule subgroup. -/
def targetBasis (datum : Thue.StandingDatum) (q : RuleBasis) : V datum :=
  ⟨vBasis datum q, ⟨FreeGroup.of q, by simp [vLift]⟩⟩

/-- Evaluate a positive stable-letter word inside the source rewriting-rule subgroup. -/
def sourcePositive (datum : Thue.StandingDatum) (w : List (Fin 2)) :
    U datum :=
  Thue.evalPositive (sourceBasis datum (.inl 0))
    (sourceBasis datum (.inl 1)) w

/-- Evaluate a positive stable-letter word inside the target rewriting-rule subgroup. -/
def targetPositive (datum : Thue.StandingDatum) (w : List (Fin 2)) :
    V datum :=
  Thue.evalPositive (targetBasis datum (.inl 0))
    (targetBasis datum (.inl 1)) w

@[simp] theorem coe_sourceBasis (datum : Thue.StandingDatum)
    (q : RuleBasis) :
    ((sourceBasis datum q : U datum) : Gamma3) = uBasis datum q := rfl

@[simp] theorem coe_targetBasis (datum : Thue.StandingDatum)
    (q : RuleBasis) :
    ((targetBasis datum q : V datum) : Gamma3) = vBasis datum q := rfl

@[simp] theorem coe_sourcePositive (datum : Thue.StandingDatum)
    (w : List (Fin 2)) :
    ((sourcePositive datum w : U datum) : Gamma3) = positive3 w := by
  induction w with
  | nil => rfl
  | cons beta w ih =>
      change
        (((if beta = 0 then sourceBasis datum (.inl 0)
            else sourceBasis datum (.inl 1)) * sourcePositive datum w : U datum) :
          Gamma3) =
        (if beta = 0 then firstStableInStageThree else secondStableInStageThree) * positive3 w
      rw [Subgroup.coe_mul, ih]
      fin_cases beta <;> simp [sourceBasis, uBasis, stable3]

@[simp] theorem coe_targetPositive (datum : Thue.StandingDatum)
    (w : List (Fin 2)) :
    ((targetPositive datum w : V datum) : Gamma3) = positive3 w := by
  induction w with
  | nil => rfl
  | cons beta w ih =>
      change
        (((if beta = 0 then targetBasis datum (.inl 0)
            else targetBasis datum (.inl 1)) * targetPositive datum w : V datum) :
          Gamma3) =
        (if beta = 0 then firstStableInStageThree else secondStableInStageThree) * positive3 w
      rw [Subgroup.coe_mul, ih]
      fin_cases beta <;> simp [targetBasis, vBasis, stable3]

theorem cEquiv_sourceBasis (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (q : RuleBasis) :
    cEquiv datum hfree (sourceBasis datum q) = targetBasis datum q := by
  apply Subtype.ext
  simp [sourceBasis, targetBasis]

theorem cEquiv_sourcePositive (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (w : List (Fin 2)) :
    cEquiv datum hfree (sourcePositive datum w) = targetPositive datum w := by
  induction w with
  | nil => simp [sourcePositive, targetPositive, Thue.evalPositive]
  | cons beta w ih =>
      change cEquiv datum hfree
          ((if beta = 0 then sourceBasis datum (.inl 0)
            else sourceBasis datum (.inl 1)) * sourcePositive datum w) =
        (if beta = 0 then targetBasis datum (.inl 0)
          else targetBasis datum (.inl 1)) * targetPositive datum w
      rw [map_mul, ih]
      fin_cases beta <;> simp [cEquiv_sourceBasis]

theorem cEquiv_symm_targetPositive (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (w : List (Fin 2)) :
    (cEquiv datum hfree).symm (targetPositive datum w) =
      sourcePositive datum w := by
  rw [← cEquiv_sourcePositive datum hfree w]
  simp

theorem cEquiv_symm_targetBasis (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) (q : RuleBasis) :
    (cEquiv datum hfree).symm (targetBasis datum q) =
      sourceBasis datum q := by
  rw [← cEquiv_sourceBasis datum hfree q]
  simp

@[simp] theorem positive3_append (u v : List (Fin 2)) :
    positive3 (u ++ v) = positive3 u * positive3 v := by
  simp [positive3, Thue.evalPositive, List.map_append]

@[simp] theorem positiveFree_append (u v : List (Fin 2)) :
    positiveFree (u ++ v) = positiveFree u * positiveFree v := by
  simp [positiveFree, List.map_append, FreeGroup.mul_mk]

/-! ## Reading the middle positive word from a one-rule coefficient -/

theorem positive_word_eq_of_source_one_rule
    (datum : Thue.StandingDatum) (Q left right : List (Fin 2))
    (f r : ℤ) (i : Fin 3)
    (hshape :
      d3 ^ f * positive3 Q * e3 ^ r =
        positive3 left * a3 datum i * positive3 right) :
    Q = left ++ datum.F i ++ right := by
  have hproj := congrArg stableProjection3 hshape
  have hfree : positiveFree Q =
      positiveFree (left ++ datum.F i ++ right) := by
    simpa [a3, positiveFree_append, stableProjection3_positive,
      mul_assoc] using hproj
  exact positiveFree_injective hfree

theorem positive_word_eq_of_target_one_rule
    (datum : Thue.StandingDatum) (Q left right : List (Fin 2))
    (f r : ℤ) (i : Fin 3)
    (hshape :
      d3 ^ f * positive3 Q * e3 ^ r =
        positive3 left * b3 datum i * positive3 right) :
    Q = left ++ datum.E i ++ right := by
  have hproj := congrArg stableProjection3 hshape
  have hfree : positiveFree Q =
      positiveFree (left ++ datum.E i ++ right) := by
    simpa [b3, positiveFree_append, stableProjection3_positive,
      mul_assoc] using hproj
  exact positiveFree_injective hfree

/-! ## Exact one-rule transport calculations -/

theorem source_one_rule_transport_value
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (left right : List (Fin 2)) (i : Fin 3) :
    ((cEquiv datum hfree
      (sourcePositive datum left * sourceBasis datum (.inr i) *
        sourcePositive datum right) : V datum) : Gamma3) =
      d3 ^ ((4 : ℤ) ^ left.length * ((i.val : ℤ) + 1)) *
        positive3 (left ++ datum.E i ++ right) *
          e3 ^ ((4 : ℤ) ^ right.length * ((i.val : ℤ) + 1)) := by
  rw [map_mul, map_mul, cEquiv_sourcePositive, cEquiv_sourceBasis,
    cEquiv_sourcePositive]
  simp only [Subgroup.coe_mul, coe_targetPositive, coe_targetBasis]
  simp only [vBasis]
  rw [b3]
  calc
    positive3 left *
          (d3 ^ (i.val + 1) * positive3 (datum.E i) * e3 ^ (i.val + 1)) *
        positive3 right =
      (positive3 left * d3 ^ (i.val + 1)) * positive3 (datum.E i) *
        (e3 ^ (i.val + 1) * positive3 right) := by group
    _ =
      (d3 ^ ((4 : ℤ) ^ left.length * ((i.val + 1 : ℕ) : ℤ)) *
          positive3 left) * positive3 (datum.E i) *
        (positive3 right *
          e3 ^ ((4 : ℤ) ^ right.length * ((i.val + 1 : ℕ) : ℤ))) := by
            rw [positive3_mul_d_pow, e_pow_mul_positive3]
    _ = _ := by
      simp only [positive3_append, Int.natCast_add, Int.natCast_one]
      group

theorem target_one_rule_transport_value
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (left right : List (Fin 2)) (i : Fin 3) :
    (((cEquiv datum hfree).symm
      (targetPositive datum left * targetBasis datum (.inr i) *
        targetPositive datum right) : U datum) : Gamma3) =
      d3 ^ ((4 : ℤ) ^ left.length * ((i.val : ℤ) + 1)) *
        positive3 (left ++ datum.F i ++ right) *
          e3 ^ ((4 : ℤ) ^ right.length * ((i.val : ℤ) + 1)) := by
  rw [map_mul, map_mul, cEquiv_symm_targetPositive,
    cEquiv_symm_targetBasis, cEquiv_symm_targetPositive]
  simp only [Subgroup.coe_mul, coe_sourcePositive, coe_sourceBasis]
  simp only [uBasis]
  rw [a3]
  calc
    positive3 left *
          (d3 ^ (i.val + 1) * positive3 (datum.F i) * e3 ^ (i.val + 1)) *
        positive3 right =
      (positive3 left * d3 ^ (i.val + 1)) * positive3 (datum.F i) *
        (e3 ^ (i.val + 1) * positive3 right) := by group
    _ =
      (d3 ^ ((4 : ℤ) ^ left.length * ((i.val + 1 : ℕ) : ℤ)) *
          positive3 left) * positive3 (datum.F i) *
        (positive3 right *
          e3 ^ ((4 : ℤ) ^ right.length * ((i.val + 1 : ℕ) : ℤ))) := by
            rw [positive3_mul_d_pow, e_pow_mul_positive3]
    _ = _ := by
      simp only [positive3_append, Int.natCast_add, Int.natCast_one]
      group

/-! ## Partial fields of `PinchClassification` -/

/-- The `source` field of `PinchClassification` for a coefficient whose
rank-five normal form has one positive rule letter, with arbitrary positive
stable-letter contexts on the two sides. -/
theorem source_classification_one_rule
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (Q : List (Fin 2)) (f r : ℤ)
    (left right : List (Fin 2)) (i : Fin 3)
    (hmem : d3 ^ f * positive3 Q * e3 ^ r ∈ U datum)
    (hshape :
      d3 ^ f * positive3 Q * e3 ^ r =
        positive3 left * a3 datum i * positive3 right) :
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      ThueEq (Thue.systemOf datum.F datum.E) Q Q' ∧
      ((cEquiv datum hfree
        ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩ : V datum) : Gamma3) =
        d3 ^ f' * positive3 Q' * e3 ^ r' := by
  have hQ : Q = left ++ datum.F i ++ right :=
    positive_word_eq_of_source_one_rule datum Q left right f r i hshape
  let f' : ℤ := (4 : ℤ) ^ left.length * ((i.val : ℤ) + 1)
  let r' : ℤ := (4 : ℤ) ^ right.length * ((i.val : ℤ) + 1)
  refine ⟨left ++ datum.E i ++ right, f', r', ?_, ?_⟩
  · rw [hQ]
    exact Relation.ReflTransGen.single
      (thueStep_rule_forward datum left right i)
  · let coefficient : U datum :=
      ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩
    have hcoefficient : coefficient =
        sourcePositive datum left * sourceBasis datum (.inr i) *
          sourcePositive datum right := by
      apply Subtype.ext
      simpa [coefficient, uBasis] using hshape
    change ((cEquiv datum hfree coefficient : V datum) : Gamma3) = _
    rw [hcoefficient]
    exact source_one_rule_transport_value datum hfree left right i

/-- The symmetric `target` field for a coefficient with one positive rule
letter.  It performs the reverse Thue rewrite `E_i ↦ F_i`. -/
theorem target_classification_one_rule
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (Q : List (Fin 2)) (f r : ℤ)
    (left right : List (Fin 2)) (i : Fin 3)
    (hmem : d3 ^ f * positive3 Q * e3 ^ r ∈ V datum)
    (hshape :
      d3 ^ f * positive3 Q * e3 ^ r =
        positive3 left * b3 datum i * positive3 right) :
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      ThueEq (Thue.systemOf datum.F datum.E) Q Q' ∧
      (((cEquiv datum hfree).symm
        ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩ : U datum) : Gamma3) =
        d3 ^ f' * positive3 Q' * e3 ^ r' := by
  have hQ : Q = left ++ datum.E i ++ right :=
    positive_word_eq_of_target_one_rule datum Q left right f r i hshape
  let f' : ℤ := (4 : ℤ) ^ left.length * ((i.val : ℤ) + 1)
  let r' : ℤ := (4 : ℤ) ^ right.length * ((i.val : ℤ) + 1)
  refine ⟨left ++ datum.F i ++ right, f', r', ?_, ?_⟩
  · rw [hQ]
    exact Relation.ReflTransGen.single
      (thueStep_rule_backward datum left right i)
  · let coefficient : V datum :=
      ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩
    have hcoefficient : coefficient =
        targetPositive datum left * targetBasis datum (.inr i) *
          targetPositive datum right := by
      apply Subtype.ext
      simpa [coefficient, vBasis] using hshape
    change (((cEquiv datum hfree).symm coefficient : U datum) : Gamma3) = _
    rw [hcoefficient]
    exact target_one_rule_transport_value datum hfree left right i

/-! ## The zero-rule shape and the exact classification interface -/

theorem source_classification_stable_shape
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (Q : List (Fin 2)) (f r : ℤ) (w : List (Fin 2))
    (hmem : d3 ^ f * positive3 Q * e3 ^ r ∈ U datum)
    (hshape : d3 ^ f * positive3 Q * e3 ^ r = positive3 w) :
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      ThueEq (Thue.systemOf datum.F datum.E) Q Q' ∧
      ((cEquiv datum hfree
        ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩ : V datum) : Gamma3) =
        d3 ^ f' * positive3 Q' * e3 ^ r' := by
  have hproj := congrArg stableProjection3 hshape
  have hQ : Q = w := positiveFree_injective (by
    simpa [stableProjection3_positive] using hproj)
  refine ⟨w, 0, 0, ?_, ?_⟩
  · rw [hQ]
    exact Relation.ReflTransGen.refl
  · let coefficient : U datum :=
      ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩
    have hcoefficient : coefficient = sourcePositive datum w := by
      apply Subtype.ext
      simpa [coefficient] using hshape
    change ((cEquiv datum hfree coefficient : V datum) : Gamma3) = _
    rw [hcoefficient, cEquiv_sourcePositive]
    simp

theorem target_classification_stable_shape
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (Q : List (Fin 2)) (f r : ℤ) (w : List (Fin 2))
    (hmem : d3 ^ f * positive3 Q * e3 ^ r ∈ V datum)
    (hshape : d3 ^ f * positive3 Q * e3 ^ r = positive3 w) :
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      ThueEq (Thue.systemOf datum.F datum.E) Q Q' ∧
      (((cEquiv datum hfree).symm
        ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩ : U datum) : Gamma3) =
        d3 ^ f' * positive3 Q' * e3 ^ r' := by
  have hproj := congrArg stableProjection3 hshape
  have hQ : Q = w := positiveFree_injective (by
    simpa [stableProjection3_positive] using hproj)
  refine ⟨w, 0, 0, ?_, ?_⟩
  · rw [hQ]
    exact Relation.ReflTransGen.refl
  · let coefficient : V datum :=
      ⟨d3 ^ f * positive3 Q * e3 ^ r, hmem⟩
    have hcoefficient : coefficient = targetPositive datum w := by
      apply Subtype.ext
      simpa [coefficient] using hshape
    change (((cEquiv datum hfree).symm coefficient : U datum) : Gamma3) = _
    rw [hcoefficient, cEquiv_symm_targetPositive]
    simp

/-- The two coefficient shapes used by the Assertion-V normal-form
classification. -/
def SourceCoefficientShape (datum : Thue.StandingDatum)
    (Q : List (Fin 2)) (f r : ℤ) : Prop :=
  (∃ w : List (Fin 2),
      d3 ^ f * positive3 Q * e3 ^ r = positive3 w) ∨
    ∃ (left right : List (Fin 2)) (i : Fin 3),
      d3 ^ f * positive3 Q * e3 ^ r =
        positive3 left * a3 datum i * positive3 right

/-- The classified shape of a coefficient after transport through the rewriting-rule isomorphism. -/
def TargetCoefficientShape (datum : Thue.StandingDatum)
    (Q : List (Fin 2)) (f r : ℤ) : Prop :=
  (∃ w : List (Fin 2),
      d3 ^ f * positive3 Q * e3 ^ r = positive3 w) ∨
    ∃ (left right : List (Fin 2)) (i : Fin 3),
      d3 ^ f * positive3 Q * e3 ^ r =
        positive3 left * b3 datum i * positive3 right

/-- The two normal-form shape classifications yield the full coefficient
classifier. -/
theorem pinchClassification_of_shapes
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (hsource : ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ U datum →
        SourceCoefficientShape datum Q f r)
    (htarget : ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ V datum →
        TargetCoefficientShape datum Q f r) :
    BorisovLemma4Pinch.PinchClassification datum hfree := by
  constructor
  · intro Q f r hmem
    rcases hsource Q f r hmem with ⟨w, hshape⟩ | ⟨left, right, i, hshape⟩
    · exact source_classification_stable_shape
        datum hfree Q f r w hmem hshape
    · exact source_classification_one_rule
        datum hfree Q f r left right i hmem hshape
  · intro Q f r hmem
    rcases htarget Q f r hmem with ⟨w, hshape⟩ | ⟨left, right, i, hshape⟩
    · exact target_classification_stable_shape
        datum hfree Q f r w hmem hshape
    · exact target_classification_one_rule
        datum hfree Q f r left right i hmem hshape

end

end BorisovPinchCoefficientClassification
end Undecidability
