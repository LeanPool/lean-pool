/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalPositiveNameFamily.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalNaturalCheckSequence
public import LeanPool.TuringConeRigidity.SetModels.InternalSubsetSequence
public import LeanPool.TuringConeRigidity.Syntax.AtomicDefinability

/-!
# Internal Positive Name Family
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalPositiveNameFamily
open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing
variable {c : ZFSet.{0}} [Preorder (Conditions c)] [Top (Conditions c)]

noncomputable def positive (τ : Name (Conditions c)) (n : ℕ) : ZFSet.{0} :=
  c.sep (fun p => ∃ q : Conditions c, label c q = p ∧ MemForces (Name.check (natSet n)) τ q)

theorem label_positive (τ : Name (Conditions c)) (n : ℕ) (p : Conditions c) :
    label c p ∈ positive τ n ↔ MemForces (Name.check (natSet n)) τ p := by
  rw [positive,ZFSet.mem_sep]
  exact ⟨fun ⟨_,q,hq,h⟩ => label_injective c hq ▸ h,
    fun h => ⟨label_mem c p,p,rfl,h⟩⟩

theorem internal_positive_family (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) {o : ZFSet.{0}} (hoM : o ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (τ : Name (Conditions c)) (hτ : τ.encode (label c) ∈ M) :
    orbitGraph (positive τ) ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  let B := orbitGraph (fun n => checkedCode (label c ⊤) (natSet n))
  have hBM : B ∈ M := InternalNaturalCheckSequence.natural_check_sequence M _ hM hT
    (hM c hc _ (label_mem c ⊤))
  have hrM := iterUnion_mem M hM hT.union hBM 2
  obtain ⟨d,hdM,hd,hboth⟩ := internal_transitive_container M hM hT.pairing hT.union hS
    hT.replacement.finitePrefix hT.infinity (pair_mem M hM hT.pairing hrM hτ)
  have hrd : iterUnion 2 B ∈ d := hd _ hboth _ (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hτd : τ.encode (label c) ∈ d := hd _ hboth _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hn (n : ℕ) : (Name.check (natSet n) : Name (Conditions c)).encode (label c) ∈ d := by
    rw [encode_check]
    exact hd _ hrd _ (second_mem_doubleUnion ((orbitGraph_pair _ n _).mpr rfl))
  obtain ⟨f,hfM,hf⟩ := internal_atomic_graph M hM hT.pairing hT.union hT.powerSet hS hdM hc hoM
  let k := ZFSet.prod d d
  have hkM := product_mem M hM hT.pairing hT.union hT.powerSet hS hdM hdM
  let e := cons d (cons c (cons k (cons o (cons f (cons B (fun _ => τ.encode (label c)))))))
  let φ : BoundedSetTheory.Formula := .existsMem 2 (.conj (.pairMem 2 0 8)
    (AtomicFormula.membership 3 4 5 6 7 0 9 1))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|i
    · exact hdM
    · exact hc
    · exact hkM
    · exact hoM
    · exact hfM
    · exact hBM
    · exact hτ
  have hφ (n : ℕ) (p : Conditions c) :
      φ.Eval (cons (label c p) (cons (natSet n) e)) ↔ MemForces (Name.check (natSet n)) τ p := by
    simp only
      [φ,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨v,_,hnv,hquery⟩
      have hv := (orbitGraph_pair _ n v).mp hnv
      have hv' : v = (Name.check (natSet n) : Name (Conditions c)).encode (label c) := by
        rw [encode_check]; exact hv
      clear hv
      subst v
      exact (eval_membership hd ho hf (Name.check (natSet n)) τ (hn n) hτd p
        _ 3 4 5 6 7 0 9 1 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩).mp hquery
    · intro h
      refine ⟨(Name.check (natSet n) : Name (Conditions c)).encode (label c),hn n,?_,?_⟩
      · apply (orbitGraph_pair _ n _).mpr
        exact encode_check _ _
      · exact (eval_membership hd ho hf (Name.check (natSet n)) τ (hn n) hτd p
          _ 3 4 5 6 7 0 9 1 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩).mpr h
  apply InternalSubsetSequence.subset_sequence M c hM hT hc φ e he (positive τ)
    (fun n p hp => (ZFSet.mem_sep.mp hp).1)
  intro n p hp
  obtain ⟨p,rfl⟩ := label_surjective c hp
  exact (hφ n p).trans (label_positive τ n p).symm

end TuringRigidity.InternalPositiveNameFamily

end OAI
