/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalCodeOperations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerSyntax
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumClosure

/-!
# Ordinal Code Operations
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

/-- Place the omega-power definition in the specified input and output slots. -/
noncomputable def codePowerAt (y x : ℕ) : SentenceForm :=
  omegaPowerSentence.rename (fun i => if i = 0 then y else x)

/-- Place the ordinal-sum definition in the specified input and output slots. -/
noncomputable def codeSumAt (c a b : ℕ) : SentenceForm :=
  sumSentence.rename (fun i => if i = 0 then c else if i = 1 then a else b)

/-- Either equate the two slots or assert that the output is twice the input ordinal. -/
noncomputable def codeScaleAt (twice : Bool) (y x : ℕ) : SentenceForm :=
  if twice then doubleSentence.rename (fun i => if i = 0 then y else x) else .equal y x

/-- Double the ordinal when the branch flag is true, and leave it unchanged otherwise. -/
noncomputable def codeScale (twice : Bool) (a : Ordinal.{u}) : Ordinal.{u} :=
  if twice then a*2 else a

theorem codePowerAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (codePowerAt y x).Sat (M : Set ZFSet) e →
      (e x).IsOrdinal ∧ e y = (Ordinal.omega0 ^ (e x).rank).toZFSet := by
  rw [codePowerAt,SentenceForm.sat_rename]
  exact omegaPowerSentence_sound M hM hω _ (fun i => he _)

theorem codePowerAt_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (codePowerAt y x).Sat (M : Set ZFSet) e ↔
      (e x).IsOrdinal ∧ e y = (Ordinal.omega0 ^ (e x).rank).toZFSet := by
  rw [codePowerAt,SentenceForm.sat_rename]
  exact omegaPowerSentence_sourceT M hM hT _ (fun i => he _)

theorem codeSumAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (c a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet) :
    (codeSumAt c a b).Sat (M : Set ZFSet) e → e c = (α+β).toZFSet := by
  rw [codeSumAt,SentenceForm.sat_rename]
  exact sumSentence_sound M hM _ (fun i => he _) α β ha hb

theorem codeSumAt_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (c a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet) :
    (codeSumAt c a b).Sat (M : Set ZFSet) e ↔ e c = (α+β).toZFSet := by
  rw [codeSumAt,SentenceForm.sat_rename]
  exact sumSentence_sourceT M hM hT _ (fun i => he _) α β ha hb

theorem codeScaleAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (twice : Bool) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : Ordinal.{u}) (ha : e x = a.toZFSet) :
    (codeScaleAt twice y x).Sat (M : Set ZFSet) e → e y = (codeScale twice a).toZFSet := by
  cases twice with
  | false => exact fun h => h.trans ha
  | true =>
    rw [codeScaleAt,ite_eq_left rfl,SentenceForm.sat_rename]
    exact doubleSentence_sound M hM _ (fun i => he _) a ha

theorem codeScaleAt_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (twice : Bool) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : Ordinal.{u}) (ha : e x = a.toZFSet) :
    (codeScaleAt twice y x).Sat (M : Set ZFSet) e ↔ e y = (codeScale twice a).toZFSet := by
  cases twice with
  | false => change e y = e x ↔ _; rw [ha]; rfl
  | true =>
    rw [codeScaleAt,ite_eq_left rfl,SentenceForm.sat_rename]
    exact doubleSentence_sourceT M hM hT _ (fun i => he _) a ha

theorem codeScale_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (twice : Bool) (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    (codeScale twice a).toZFSet ∈ M := by
  cases twice
  · exact ha
  · exact ordinal_mul_two_internal M hM hT a ha

end TuringRigidity.OrdinalCoding

end OAI
