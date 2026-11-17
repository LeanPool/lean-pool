/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformDefinedSubsetName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformSeparationName
public import LeanPool.TuringConeRigidity.Syntax.SetSatisfactionBounded
public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Uniform Defined Subset Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel RecursiveNames
open BoundedForcing AtomicForcing CountableForcing
universe u

theorem uniform_definedSubset_name (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r t : Conditions c, ZFSet.pair (label c r) (label c t) ∈ o ↔ r ≤ t)
    (A a : Name (Conditions c)) (hA : A.encode (label c) ∈ M)
    (ha : a.encode (label c) ∈ M) (φ : SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        f.val G.carrier = definedSubset (A.val G.carrier) φ
          (fun _ : Fin φ.bound => a.val G.carrier) := by
  let e := push A (fun _ => a)
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    cases i
    · exact hA
    · exact ha
  let ψ := setBounded φ 1 (fun i => if i = 0 then 0 else 2)
  obtain ⟨B,hB,hBS,hval⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity
      hc hoM ho ψ A hA e he
  refine ⟨A.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG
    apply ZFSet.ext; intro x
    rw [hval G hG x,mem_definedSubset]
    apply and_congr_right; intro _
    rw [setBounded_eval]
    apply φ.finite_support
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      change a.val G.carrier = tupleEnv (fun _ : Fin φ.bound => a.val G.carrier) i
      simp only [tupleEnv,dite_eq_left (show i < φ.bound by omega)]

theorem uniform_checked_definition_name (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r t : Conditions c, ZFSet.pair (label c r) (label c t) ∈ o ↔ r ≤ t)
    (A : Name (Conditions c)) (hA : A.encode (label c) ∈ M)
    (X : ZFSet.{u}) (hX : X ∈ M) (φ : SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        f.val G.carrier = definedSubset (A.val G.carrier) φ
          (fun _ : Fin φ.bound => X) := by
  have hcX := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hX
  obtain ⟨f,hf,hval⟩ := uniform_definedSubset_name M hM hT hc hoM ho
    A (Name.check X) hA hcX φ
  refine ⟨f,hf,?_⟩
  intro G hG ht
  simpa only [Name.val_check G.carrier ht X] using hval G hG

end TuringRigidity.RelativeConstructible

end OAI
