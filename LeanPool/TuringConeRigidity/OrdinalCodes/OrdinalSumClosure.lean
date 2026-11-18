/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalSumClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumSyntax

/-!
# Ordinal Sum Closure
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem ordinal_add_internal_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a+b).toZFSet ∈ M ∧ ∃ f ∈ M,
      OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
        (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f := by
  obtain ⟨hc,f,hf,hg,ho⟩ := orderType_internal M _ _ hM hP hU hPow hS hR
    (sumDomain_mem M _ _ hM hP hU hPow hS h0 ha hb)
    (sumRelation_mem M _ _ hM hP hU hPow hS h0 ha hb)
    (sumRelation_wellFounded a b) (sumRelation_transitive a b)
  rw [sum_orderType] at hc hg ho
  exact ⟨hc,f,hf,ZFSet.isOrdinal_toZFSet _,hg,ho⟩

theorem ordinal_mul_nat_internal_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) (n : ℕ) : (a*n).toZFSet ∈ M := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    simpa only [Nat.cast_add_one,mul_add_one] using
      (ordinal_add_internal_schemas M hM hP hU hPow hS hR h0 (a*n) a ih ha).1

theorem ordinal_mul_two_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (a*2).toZFSet ∈ M := by
  rw [Ordinal.mul_two]
  exact (ordinal_add_internal M hM hT a a ha ha).1

/-- The ordinal-sum formula specialized to two equal inputs. -/
noncomputable def doubleSentence : SentenceForm :=
  sumSentence.rename (fun i => if i = 0 then 0 else 1)

theorem doubleSentence_bound : doubleSentence.bound = 2 := by rfl

theorem doubleSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a : Ordinal.{u}) (ha : e 1 = a.toZFSet) :
    doubleSentence.Sat (A : Set ZFSet) e → e 0 = (a*2).toZFSet := by
  rw [doubleSentence,SentenceForm.sat_rename,Ordinal.mul_two]
  exact sumSentence_sound A hA _ (fun i => he _) a a ha ha

theorem doubleSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a : Ordinal.{u}) (ha : e 1 = a.toZFSet) :
    doubleSentence.Sat (M : Set ZFSet) e ↔ e 0 = (a*2).toZFSet := by
  rw [doubleSentence,SentenceForm.sat_rename,Ordinal.mul_two]
  exact sumSentence_sourceT M hM hT _ (fun i => he _) a a ha ha

end TuringRigidity.OrdinalArithmetic

end OAI
