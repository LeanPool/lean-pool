/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.PinchCoefficientClassification

/-!
# A syntactic endpoint for Borisov's coefficient-shape argument

This part of Assertion V compares the canonical rank-five preimage
of a coefficient `d^f Q e^r` with its literal two-HNN normal form.  This file
isolates the exact output of that comparison: the canonical word has either
only positive stable letters, or one positive rule letter between two
positive stable contexts.

The resulting syntactic alternatives imply the semantic
`SourceCoefficientShape` and `TargetCoefficientShape` consumed by the proof
of Borisov's Lemma 4.
-/

@[expose] public section

namespace Undecidability
namespace BorisovCoefficientShapes

open BorisovCStage
open BorisovHNNModel
open BorisovPinchCoefficientClassification

noncomputable section

/-- The indices of the two stable generators and the three rule generators. -/
abbrev Basis := BorisovCStage.RuleBasis

/-- The freely reduced word consisting of a positive stable word. -/
def stableLetters (w : List (Fin 2)) : List (Basis × Bool) :=
  w.map fun beta ↦ (.inl beta, true)

/-- A positive stable context, one positive rule letter, and another positive
stable context. -/
def oneRuleLetters (left right : List (Fin 2)) (i : Fin 3) :
    List (Basis × Bool) :=
  stableLetters left ++ [(.inr i, true)] ++ stableLetters right

/-- Every letter is positive.  This recursive presentation is convenient for
the normal-form parser, which consumes the canonical list from left to right. -/
def AllPositive : List (Basis × Bool) → Prop
  | [] => True
  | (_, sign) :: rest => sign = true ∧ AllPositive rest

/-- Number of displayed rule letters, irrespective of sign. -/
def ruleCount : List (Basis × Bool) → ℕ
  | [] => 0
  | (.inl _, _) :: rest => ruleCount rest
  | (.inr _, _) :: rest => ruleCount rest + 1

/-- A positive list containing no rule letter is exactly a positive stable
word. -/
theorem eq_stableLetters_of_ruleCount_zero
    (letters : List (Basis × Bool))
    (hpositive : AllPositive letters) (hzero : ruleCount letters = 0) :
    ∃ stable : List (Fin 2), letters = stableLetters stable := by
  induction letters with
  | nil => exact ⟨[], rfl⟩
  | cons x rest ih =>
      rcases x with ⟨q, sign⟩
      have hsign : sign = true := hpositive.1
      subst sign
      cases q with
      | inl beta =>
          rcases ih hpositive.2 (by simpa [ruleCount] using hzero) with
            ⟨stable, rfl⟩
          exact ⟨beta :: stable, rfl⟩
      | inr i => simp [ruleCount] at hzero

/-- Pure list-theoretic form of Borisov's page-771 dichotomy: if all letters
are positive and at most one is a rule letter, the word is either stable-only
or has a unique rule letter in positive stable contexts. -/
theorem letters_eq_stable_or_oneRule
    (letters : List (Basis × Bool))
    (hpositive : AllPositive letters) (hsparse : ruleCount letters ≤ 1) :
    (∃ stable : List (Fin 2), letters = stableLetters stable) ∨
      ∃ (left right : List (Fin 2)) (i : Fin 3),
        letters = oneRuleLetters left right i := by
  induction letters with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons x rest ih =>
      rcases x with ⟨q, sign⟩
      have hsign : sign = true := hpositive.1
      subst sign
      cases q with
      | inl beta =>
          have hsparseRest : ruleCount rest ≤ 1 := by
            simpa [ruleCount] using hsparse
          rcases ih hpositive.2 hsparseRest with
            ⟨stable, rfl⟩ | ⟨left, right, i, rfl⟩
          · exact Or.inl ⟨beta :: stable, rfl⟩
          · exact Or.inr ⟨beta :: left, right, i, by
              simp [oneRuleLetters, stableLetters]⟩
      | inr i =>
          have hzero : ruleCount rest = 0 := by
            simp only [ruleCount] at hsparse
            omega
          rcases eq_stableLetters_of_ruleCount_zero rest hpositive.2 hzero with
            ⟨right, rfl⟩
          exact Or.inr ⟨[], right, i, rfl⟩

@[simp] theorem uLift_mk_stableLetters
    (datum : Thue.StandingDatum) (w : List (Fin 2)) :
    uLift datum (FreeGroup.mk (stableLetters w)) = positive3 w := by
  rw [uLift, FreeGroup.lift_mk]
  unfold positive3 Thue.evalPositive stableLetters
  rw [List.map_map]
  congr 1

@[simp] theorem vLift_mk_stableLetters
    (datum : Thue.StandingDatum) (w : List (Fin 2)) :
    vLift datum (FreeGroup.mk (stableLetters w)) = positive3 w := by
  rw [vLift, FreeGroup.lift_mk]
  unfold positive3 Thue.evalPositive stableLetters
  rw [List.map_map]
  congr 1

@[simp] theorem uLift_mk_oneRuleLetters
    (datum : Thue.StandingDatum) (left right : List (Fin 2)) (i : Fin 3) :
    uLift datum (FreeGroup.mk (oneRuleLetters left right i)) =
      positive3 left * a3 datum i * positive3 right := by
  rw [show oneRuleLetters left right i =
      stableLetters left ++ ((.inr i, true) :: stableLetters right) by
        simp [oneRuleLetters]]
  rw [← FreeGroup.mul_mk, map_mul, uLift_mk_stableLetters]
  rw [show ((.inr i, true) :: stableLetters right) =
      [(.inr i, true)] ++ stableLetters right by rfl]
  rw [← FreeGroup.mul_mk, map_mul, uLift_mk_stableLetters]
  simp [uLift, uBasis, mul_assoc]

@[simp] theorem vLift_mk_oneRuleLetters
    (datum : Thue.StandingDatum) (left right : List (Fin 2)) (i : Fin 3) :
    vLift datum (FreeGroup.mk (oneRuleLetters left right i)) =
      positive3 left * b3 datum i * positive3 right := by
  rw [show oneRuleLetters left right i =
      stableLetters left ++ ((.inr i, true) :: stableLetters right) by
        simp [oneRuleLetters]]
  rw [← FreeGroup.mul_mk, map_mul, vLift_mk_stableLetters]
  rw [show ((.inr i, true) :: stableLetters right) =
      [(.inr i, true)] ++ stableLetters right by rfl]
  rw [← FreeGroup.mul_mk, map_mul, vLift_mk_stableLetters]
  simp [vLift, vBasis, mul_assoc]

/-! ## Canonical sparse coefficient words -/

/-- The precise syntactic alternative established by the normal-form
comparison for a canonical rank-five preimage. -/
def CanonicalCoefficientWordShape (w : FreeGroup Basis) : Prop :=
  (∃ stable : List (Fin 2), w.toWord = stableLetters stable) ∨
    ∃ (left right : List (Fin 2)) (i : Fin 3),
      w.toWord = oneRuleLetters left right i

theorem canonicalCoefficientWordShape_of_positive_sparse
    (w : FreeGroup Basis) (hpositive : AllPositive w.toWord)
    (hsparse : ruleCount w.toWord ≤ 1) :
    CanonicalCoefficientWordShape w :=
  letters_eq_stable_or_oneRule w.toWord hpositive hsparse

/-- A canonical source preimage of the stated syntactic form gives the exact
semantic source shape. -/
theorem sourceCoefficientShape_of_preimage
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) (f r : ℤ)
    (w : FreeGroup Basis)
    (heval : uLift datum w = d3 ^ f * positive3 Q * e3 ^ r)
    (hshape : CanonicalCoefficientWordShape w) :
    SourceCoefficientShape datum Q f r := by
  have hmk : FreeGroup.mk w.toWord = w := FreeGroup.mk_toWord
  rcases hshape with ⟨stable, hword⟩ | ⟨left, right, i, hword⟩
  · left
    refine ⟨stable, ?_⟩
    calc
      d3 ^ f * positive3 Q * e3 ^ r = uLift datum w := heval.symm
      _ = uLift datum (FreeGroup.mk w.toWord) := by rw [hmk]
      _ = uLift datum (FreeGroup.mk (stableLetters stable)) := by rw [hword]
      _ = positive3 stable := uLift_mk_stableLetters datum stable
  · right
    refine ⟨left, right, i, ?_⟩
    calc
      d3 ^ f * positive3 Q * e3 ^ r = uLift datum w := heval.symm
      _ = uLift datum (FreeGroup.mk w.toWord) := by rw [hmk]
      _ = uLift datum (FreeGroup.mk (oneRuleLetters left right i)) := by
        rw [hword]
      _ = positive3 left * a3 datum i * positive3 right :=
        uLift_mk_oneRuleLetters datum left right i

/-- The target analogue of `sourceCoefficientShape_of_preimage`. -/
theorem targetCoefficientShape_of_preimage
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) (f r : ℤ)
    (w : FreeGroup Basis)
    (heval : vLift datum w = d3 ^ f * positive3 Q * e3 ^ r)
    (hshape : CanonicalCoefficientWordShape w) :
    TargetCoefficientShape datum Q f r := by
  have hmk : FreeGroup.mk w.toWord = w := FreeGroup.mk_toWord
  rcases hshape with ⟨stable, hword⟩ | ⟨left, right, i, hword⟩
  · left
    refine ⟨stable, ?_⟩
    calc
      d3 ^ f * positive3 Q * e3 ^ r = vLift datum w := heval.symm
      _ = vLift datum (FreeGroup.mk w.toWord) := by rw [hmk]
      _ = vLift datum (FreeGroup.mk (stableLetters stable)) := by rw [hword]
      _ = positive3 stable := vLift_mk_stableLetters datum stable
  · right
    refine ⟨left, right, i, ?_⟩
    calc
      d3 ^ f * positive3 Q * e3 ^ r = vLift datum w := heval.symm
      _ = vLift datum (FreeGroup.mk w.toWord) := by rw [hmk]
      _ = vLift datum (FreeGroup.mk (oneRuleLetters left right i)) := by
        rw [hword]
      _ = positive3 left * b3 datum i * positive3 right :=
        vLift_mk_oneRuleLetters datum left right i

/-- If the normal-form parser establishes the source syntactic alternative
for every preimage, then the public source coefficient-shape theorem follows
from subgroup membership. -/
theorem sourceCoefficientShape_of_parser
    (datum : Thue.StandingDatum)
    (hparse : ∀ (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis),
      uLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        CanonicalCoefficientWordShape w) :
    ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ U datum →
        SourceCoefficientShape datum Q f r := by
  intro Q f r hmem
  rcases hmem with ⟨w, heval⟩
  exact sourceCoefficientShape_of_preimage datum Q f r w heval
    (hparse Q f r w heval)

/-- Target version of `sourceCoefficientShape_of_parser`. -/
theorem targetCoefficientShape_of_parser
    (datum : Thue.StandingDatum)
    (hparse : ∀ (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis),
      vLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        CanonicalCoefficientWordShape w) :
    ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ V datum →
        TargetCoefficientShape datum Q f r := by
  intro Q f r hmem
  rcases hmem with ⟨w, heval⟩
  exact targetCoefficientShape_of_preimage datum Q f r w heval
    (hparse Q f r w heval)

/-- A local source interface for the Britton comparison.  It
is enough to prove that the canonical preimage has no negative letters and
at most one displayed rule letter. -/
theorem sourceCoefficientShape_of_positive_sparse_parser
    (datum : Thue.StandingDatum)
    (hpositive : ∀ (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis),
      uLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        AllPositive w.toWord)
    (hsparse : ∀ (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis),
      uLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        ruleCount w.toWord ≤ 1) :
    ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ U datum →
        SourceCoefficientShape datum Q f r := by
  apply sourceCoefficientShape_of_parser datum
  intro Q f r w heval
  exact canonicalCoefficientWordShape_of_positive_sparse w
    (hpositive Q f r w heval) (hsparse Q f r w heval)

/-- Target counterpart of
`sourceCoefficientShape_of_positive_sparse_parser`. -/
theorem targetCoefficientShape_of_positive_sparse_parser
    (datum : Thue.StandingDatum)
    (hpositive : ∀ (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis),
      vLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        AllPositive w.toWord)
    (hsparse : ∀ (Q : List (Fin 2)) (f r : ℤ) (w : FreeGroup Basis),
      vLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        ruleCount w.toWord ≤ 1) :
    ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ V datum →
        TargetCoefficientShape datum Q f r := by
  apply targetCoefficientShape_of_parser datum
  intro Q f r w heval
  exact canonicalCoefficientWordShape_of_positive_sparse w
    (hpositive Q f r w heval) (hsparse Q f r w heval)

end

end BorisovCoefficientShapes
end Undecidability
