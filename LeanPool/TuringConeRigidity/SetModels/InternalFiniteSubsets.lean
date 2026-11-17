/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalFiniteSubsets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleTupleSpace
public import LeanPool.TuringConeRigidity.SetModels.CollapsePrefixAbsolute

/-!
# Internal Finite Subsets
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalFiniteSubsets
open Set TransitiveNameModel BoundedSetTheory InternalCollapse RelativeConstructible
universe u

noncomputable def finiteSubsets (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun t : Σ n : ℕ, Fin n → Conditions A =>
    ZFSet.range (fun i => label A (t.2 i)))

theorem mem_finiteSubsets (A x : ZFSet.{u}) :
    x ∈ finiteSubsets A ↔ ∃ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) ∧ x = ZFSet.range v := by
  rw [finiteSubsets,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨n,v⟩,hx⟩
    exact ⟨n,fun i => label A (v i),fun i => label_mem A (v i),hx.symm⟩
  · rintro ⟨n,v,hv,rfl⟩
    refine ⟨⟨n,fun i => equivShrink A ⟨v i,hv i⟩⟩,?_⟩
    congr 1; funext i; simp [label]

theorem mem_finiteSubsets_iff (A x : ZFSet.{u}) :
    x ∈ finiteSubsets A ↔ x ⊆ A ∧ (x : Set ZFSet.{u}).Finite := by
  rw [mem_finiteSubsets]
  constructor
  · rintro ⟨n,v,hv,rfl⟩
    exact ⟨fun z hz => by obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz; exact hv i,
      by rw [ZFSet.coe_range]; exact Set.finite_range v⟩
  · rintro ⟨hx,hfin⟩
    let : Fintype x := hfin.fintype
    let v : Fin (Fintype.card x) → ZFSet.{u} := fun i => ((Fintype.equivFin x).symm i).val
    refine ⟨_,v,fun i => hx ((Fintype.equivFin x).symm i).property,?_⟩
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_range]
    exact ⟨fun hz => ⟨(Fintype.equivFin x) ⟨z,hz⟩,by simp [v]⟩,
      fun ⟨i,hi⟩ => hi ▸ ((Fintype.equivFin x).symm i).property⟩

theorem finite_subset_mem (M A x : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hx : x ∈ finiteSubsets A) : x ∈ M := by
  obtain ⟨n,v,hv,rfl⟩ := (mem_finiteSubsets A x).mp hx
  exact finite_range_mem M hM hT.pairing hT.union
    (hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero) n v
    (fun i => hM A hA _ (hv i))

def rangeFormula (o A x g : ℕ) : Formula :=
  .conj (.subset x A) (.allMem A
    (.iff (.member 0 (x+1)) (.existsMem (o+1) (.pairMem 0 1 (g+2)))))

theorem rangeFormula_spec (o A x g : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) {n : ℕ} {v : Fin n → ZFSet.{u}}
    (hv : ∀ i, v i ∈ e A) (hg : e g = tupleGraph v) :
    (rangeFormula o A x g).Eval e ↔ e x = ZFSet.range v := by
  simp only [rangeFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ]
  rw [ho,hg]
  have hr (z : ZFSet.{u}) : (∃ i ∈ ZFSet.omega, ZFSet.pair i z ∈ tupleGraph v) ↔
      z ∈ ZFSet.range v := by
    constructor
    · rintro ⟨i,_,hi⟩
      obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hi
      exact ZFSet.mem_range.mpr ⟨j,(ZFSet.pair_inj.mp hj).2⟩
    · rintro hz
      obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
      exact ⟨natSet i.val,(mem_omega _).mpr ⟨i.val,rfl⟩,(tupleGraph_pair v i _).mpr rfl⟩
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro z
    constructor
    · intro hz; exact (hr z).mp ((h z (hsub hz)).mp hz)
    · intro hz
      have hzA : z ∈ e A := by obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz; exact hv i
      exact (h z hzA).mpr ((hr z).mpr hz)
  · intro he
    refine ⟨fun z hz => ?_,fun z _ => ?_⟩
    · rw [he] at hz; obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz; exact hv i
    · rw [he]; exact (hr z).symm

theorem finiteSubsets_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : finiteSubsets A ∈ M := by
  obtain ⟨C,hC,hCdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing
    hT.union hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hA
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hA
  let e := cons ZFSet.omega (cons A (fun _ => C))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact sourceT_omega_mem M hM hT
    · exact hA
    · exact hC
  let φ : Formula := .existsMem 3 (rangeFormula 2 3 1 0)
  have hφ (x : ZFSet.{u}) : φ.Eval (cons x e) ↔ x ∈ finiteSubsets A := by
    change (∃ g ∈ C, (rangeFormula 2 3 1 0).Eval (cons g (cons x e))) ↔ _
    constructor
    · rintro ⟨g,hg,h⟩
      obtain ⟨n,hn⟩ := (hCdef g).mp hg
      obtain ⟨v,hv,rfl⟩ := functionGraph_tuple A g n hn
      exact (mem_finiteSubsets A x).mpr ⟨n,v,hv,
        (rangeFormula_spec 2 3 1 0 _ rfl hv rfl).mp h⟩
    · intro hx
      obtain ⟨n,v,hv,rfl⟩ := (mem_finiteSubsets A x).mp hx
      exact ⟨tupleGraph v,(hCdef _).mpr ⟨n,tupleGraph_function A v hv⟩,
        (rangeFormula_spec 2 3 1 0 _ rfl hv rfl).mpr rfl⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he hQ
  have heq : Q.sep (fun x => φ.Eval (cons x e)) = finiteSubsets A := by
    apply ZFSet.ext; intro x
    rw [ZFSet.mem_sep,hφ,hQdef]
    exact ⟨fun h => h.2,fun hx => ⟨⟨finite_subset_mem M A x hM hT hA hx,
      ((mem_finiteSubsets_iff A x).mp hx).1⟩,hx⟩⟩
  exact heq ▸ hs

end TuringRigidity.InternalFiniteSubsets

end OAI
