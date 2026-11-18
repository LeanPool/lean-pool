/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SatisfactionCertificateBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SatisfactionRecursion

/-!
# Satisfaction Certificate Bound
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem satisfactionSet_subset_product (A : ZFSet.{u}) :
    satisfactionSet A ⊆ ZFSet.prod ZFSet.omega (tupleSpace A) := by
  intro z hz
  obtain ⟨⟨⟨n,p,v⟩,_,_⟩,rfl⟩ := ZFSet.mem_range.mp hz
  exact ZFSet.mem_prod.mpr ⟨natSet (Encodable.encode p),(mem_omega _).mpr ⟨_,rfl⟩,
    tupleCode (fun i => label A (v i)),
    (mem_tupleSpace A _).mpr ⟨n,_,fun i => label_mem A (v i),rfl⟩,rfl⟩

/-- Closure under the explicit bounded model axioms and internal omega. -/
theorem internal_certificate_bound_of_axioms (M A : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) (hA : A ∈ M) :
    ∃ Q ∈ M,
      (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ ZFSet.prod ZFSet.omega (tupleSpace A)) ∧
      ∀ ps : List SentenceForm, finiteSatisfaction A ps ∈ Q := by
  obtain ⟨Q,hQ,hdef⟩ := internal_power M hM hPow
    (product_mem M hM hP hU hPow hS
      hω (tupleSpace_mem_of_axioms M A hM hP hU hPow hS hω hA))
  refine ⟨Q,hQ,hdef,fun ps => (hdef _).mpr ⟨finiteSatisfaction_mem_of_axioms M A hM hP hU hPow
    hS hω hA ps,?_⟩⟩
  exact fun z hz => satisfactionSet_subset_product A (finiteSatisfaction_subset A ps hz)


theorem internal_certificate_bound (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) :
    ∃ Q ∈ M,
      (∀ S, S ∈ Q ↔ S ∈ M ∧ S ⊆ ZFSet.prod ZFSet.omega (tupleSpace A)) ∧
      ∀ ps : List SentenceForm, finiteSatisfaction A ps ∈ Q := by
  exact internal_certificate_bound_of_axioms M A hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hA

theorem satisfaction_iff_bounded_recursion (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) :
    ∃ Q ∈ M, ∀ (p : SentenceForm) (n : ℕ) (v : Fin n → ZFSet.{u}), (∀ i, v i ∈ A) →
      (accepts (satisfactionSet A) p v ↔ ∃ S ∈ Q, TruthRecursion A p S ∧ accepts S p v) := by
  obtain ⟨Q,hQ,hdef,hfinite⟩ := internal_certificate_bound M A hM hT hA
  refine ⟨Q,hQ,fun p n v hv => ?_⟩
  constructor
  · intro hs
    exact ⟨finiteSatisfaction A (subformulas p),hfinite _,finiteSatisfaction_recursion A p,
      (finiteSatisfaction_covers A p v hv).mpr hs⟩
  · rintro ⟨S,hS,hrec,haccept⟩
    exact (satisfaction_iff_internal_recursion M A hM hT hA p v hv).mpr
      ⟨S,(hdef S).mp hS |>.1,hrec,haccept⟩

end TuringRigidity.RelativeConstructible

end OAI
