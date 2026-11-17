/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenInternalSupport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenCountedAntichain

/-!
# Cohen Internal Support
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenInternalSupport
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenGroundPoset CohenConditionCode CohenSymmetry CohenCoordinates InternalCohen

/-- The set of coordinates in `A` assigned a Boolean value by the graph `p`. -/
noncomputable def supportSet (A p : ZFSet.{0}) : ZFSet.{0} :=
  A.sep (fun x => ∃ b ∈ alphabet, ZFSet.pair x b ∈ p)

theorem support_graph (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    supportSet A (graph A p) = ZFSet.range (fun i : ↥(support p) => label A i.val) := by
  apply ZFSet.ext; intro x
  rw [supportSet,ZFSet.mem_sep,ZFSet.mem_range]
  constructor
  · rintro ⟨hx,b,hb,hpb⟩
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    let i : Conditions A := equivShrink A ⟨x,hx⟩
    have hi : label A i = x := by simp [i,label]
    rw [←hi,pair_mem_graph] at hpb
    exact ⟨⟨i,(mem_support p i).mpr (by simp [hpb])⟩,hi⟩
  · rintro ⟨i,rfl⟩
    have hi := (mem_support p i.val).mp i.property
    cases hv : p.val i.val with
    | none => exact False.elim (hi hv)
    | some b => exact ⟨label_mem A i.val,bitSet b,(mem_alphabet _).mpr ⟨b,rfl⟩,
        (pair_mem_graph A p i.val b).mpr hv⟩

theorem support_finite (A p : ZFSet.{0}) (hp : p ∈ conditions A) :
    supportSet A p ∈ finiteSubsets A := by
  obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp hp)
  apply (mem_finiteSubsets_iff _ _).mpr
  refine ⟨fun _ h => (ZFSet.mem_sep.mp h).1, ?_⟩
  rw [support_graph, ZFSet.coe_range]
  exact Set.finite_range _

/-- Bounded formula identifying the domain of a set-coded condition graph. -/
def supportFormula (A B p S : ℕ) : Formula := .conj (.subset S A)
  (.allMem A (.iff (.member 0 (S+1)) (.existsMem (B+1) (.pairMem 1 0 (p+2)))))

theorem supportFormula_spec (A B p S : ℕ) (e : ℕ → ZFSet.{0}) (hB : e B = alphabet) :
    (supportFormula A B p S).Eval e ↔ e S = supportSet (e A) (e p) := by
  simp only [supportFormula,Formula.eval_subset,Formula.eval_allMem,Formula.eval_iff,
    Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,hB]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro x
    exact ⟨fun hx => ZFSet.mem_sep.mpr ⟨hsub hx,(h x (hsub hx)).mp hx⟩,
      fun hx => (h x (ZFSet.mem_sep.mp hx).1).mpr (ZFSet.mem_sep.mp hx).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hx => (ZFSet.mem_sep.mp hx).1,
      fun x hx => ZFSet.mem_sep.trans (and_iff_right hx)⟩

/-- The coordinates used by some condition in the family `E`. -/
noncomputable def used (A E : ZFSet.{0}) : ZFSet.{0} :=
  A.sep (fun x => ∃ p ∈ E, x ∈ supportSet A p)

theorem used_mem (M A E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hE : E ∈ M) : used A E ∈ M := by
  let e := cons E (fun _ => alphabet)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hE
    · exact alphabet_mem M hM hT
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 3 (.pairMem 2 0 1))) e he hA
  have heq : A.sep (fun x => (Formula.existsMem 1 (.existsMem 3 (.pairMem 2 0 1))).Eval (cons x
    e)) = used A E := by
    apply ZFSet.ext; intro x
    simp only
      [ZFSet.mem_sep,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e,used,supportSet]
    constructor
    · rintro ⟨hx,p,hp,b,hb,hpb⟩; exact ⟨hx,p,hp,hx,b,hb,hpb⟩
    · rintro ⟨hx,p,hp,_,hb⟩; exact ⟨hx,p,hp,hb⟩
  exact heq ▸ hs

theorem used_counted (M A E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hE : E ∈ M) (hEc : E ⊆ conditions A)
    (hct : InternallyCountable M E) :
    used A E = ∅ ∨ InternallyCountable M (used A E) := by
  classical
  obtain ⟨B,hBM,hB,honto⟩ := hct
  have hvals (n : ℕ) := hB.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
  choose p hp hnp hpu using hvals
  let S := finiteSubsets A
  let v : ℕ → ZFSet.{0} := fun n => supportSet A (p n)
  have hv : ∀ n, v n ∈ S := fun n => support_finite A (p n) (hEc (hp n))
  have hS := finiteSubsets_mem M A hM hT hA
  have hω := sourceT_omega_mem M hM hT
  let e := cons ZFSet.omega (cons S (cons E (cons B (cons A (fun _ => alphabet)))))
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.conj (.pairMem 2 0 7) (supportFormula 8 9 0 1)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    · exact hω
    · exact hS
    · exact hE
    · exact hBM
    · exact hA
    · exact alphabet_mem M hM hT
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph v := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,T,_,hz,q,hq,hnq,hT⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hq' := hpu n q hq hnq
      have ht := (supportFormula_spec 8 9 0 1 _ rfl).mp hT
      change T = supportSet A q at ht
      exact (mem_orbitGraph v z).mpr ⟨n,by rw [hz,ht,hq']⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph v z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,v n,hv n,rfl,p n,hp n,hnp n,
        (supportFormula_spec 8 9 0 1 _ rfl).mpr rfl⟩
  have hV : orbitGraph v ∈ M := by
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hS)
    have heq : (ZFSet.prod ZFSet.omega S).sep (fun z => φ.Eval (cons z e)) = orbitGraph v := by
      apply ZFSet.ext; intro z
      rw [ZFSet.mem_sep,hφ]
      exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function S v hv).1 z hz),hz⟩⟩
    exact heq ▸ hs
  by_cases hempty : used A E = ∅
  · exact Or.inl hempty
  · right
    apply InternalCountableFiniteUnion.internally_countable_union M (used A E) hM hT
      (used_mem M A E hM hT hA hE) v
    · intro n
      exact (mem_finiteSubsets_iff _ _).mpr ⟨fun x hx => ZFSet.mem_sep.mpr
        ⟨(ZFSet.mem_sep.mp hx).1,p n,hp n,hx⟩,((mem_finiteSubsets_iff A (v n)).mp (hv n)).2⟩
    · exact hV
    · intro x hx
      obtain ⟨_,q,hq,hxq⟩ := ZFSet.mem_sep.mp hx
      obtain ⟨n,hn,hnq⟩ := honto q hq
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      refine ⟨n,?_⟩
      change x ∈ supportSet A (p n)
      rwa [hpu n q hq hnq] at hxq
    · by_contra h
      apply hempty
      apply ZFSet.ext; intro x
      exact ⟨fun hx => False.elim (h ⟨x,hx⟩),fun hx => False.elim (ZFSet.notMem_empty x hx)⟩

theorem antichain_support_counted (M A E : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hE : E ∈ M) (hEc : E ⊆ conditions A)
    (ha : CohenAntichainStages.Anti (conditions A) E) :
    used A E ∈ M ∧ (used A E = ∅ ∨ InternallyCountable M (used A E)) := by
  refine ⟨used_mem M A E hM hT hA hE,?_⟩
  rcases CohenCountedAntichain.every_internal_antichain_counted M A E hM hT hA hE hEc ha with he|hc
  · left
    apply ZFSet.ext; intro x
    simp only [used,he,ZFSet.mem_sep,ZFSet.notMem_empty,false_and,exists_false,and_false]
  · exact used_counted M A E hM hT hA hE hEc hc

end TuringRigidity.CohenInternalSupport

end OAI
