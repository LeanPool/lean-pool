/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/CodeOperationCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.SumCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalCodeOperations

/-!
# Code Operation Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem codePowerAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hc : OmegaPowerCertificates M (e x)) (hy : e y = (Ordinal.omega0 ^ (e x).rank).toZFSet) :
    (codePowerAt y x).Sat (M : Set ZFSet) e := by
  rw [codePowerAt,SentenceForm.sat_rename]
  exact omegaPowerSentence_of_certificates M hM hω _ (fun i => he _) hc hy

theorem codeSumAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (c a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet)
    (hc : SumCertificates M α β) (hy : e c = (α + β).toZFSet) :
    (codeSumAt c a b).Sat (M : Set ZFSet) e := by
  rw [codeSumAt,SentenceForm.sat_rename]
  exact sumSentence_of_certificates M hM hω _ (fun i => he _) α β ha hb hc hy


theorem codeScaleAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (y x : ℕ)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : Ordinal.{u}) (ha : e x = a.toZFSet)
    (hc : twice = true → SumCertificates M a a) (hy : e y = (codeScale twice a).toZFSet) :
    (codeScaleAt twice y x).Sat (M : Set ZFSet) e := by
  cases twice with
  | false => exact hy.trans ha.symm
  | true =>
    change (doubleSentence.rename (fun i => if i = 0 then y else x)).Sat (M : Set ZFSet) e
    rw [SentenceForm.sat_rename]
    rw [doubleSentence,SentenceForm.sat_rename]
    exact sumSentence_of_certificates M hM hω
      (fun i => e (if (if i = 0 then 0 else 1) = 0 then y else x))
      (fun i => he _) a a ha ha (hc rfl)
      (by simpa only [codeScale,↓reduceIte,Ordinal.mul_two] using hy)

end TuringRigidity.OrdinalCoding

end OAI
