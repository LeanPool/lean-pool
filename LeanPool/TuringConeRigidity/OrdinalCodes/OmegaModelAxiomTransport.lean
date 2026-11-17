/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaModelAxiomTransport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaModelSyntax
public import LeanPool.TuringConeRigidity.SetModels.SetModelFunctionGraphs

/-!
# Omega Model Axiom Transport
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OmegaModelCore.OmegaData
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u
noncomputable section
variable {α : Type u} (S : OmegaData α)

theorem collapsed_pairing (hP : S.PairingAxiom) : Pairing S.collapsedModel := by
  intro a ha b hb
  obtain ⟨x,rfl⟩ := (S.mem_collapsedModel a).mp ha
  obtain ⟨y,rfl⟩ := (S.mem_collapsedModel b).mp hb
  obtain ⟨c,hc⟩ := hP x.val y.val
  let v : S.Core := ⟨c,S.pair_core x.property y.property hc⟩
  refine ⟨S.collapse v,(S.mem_collapsedModel _).mpr ⟨v,rfl⟩,?_⟩
  intro z hz
  obtain ⟨z,rfl⟩ := (S.mem_collapsedModel z).mp hz
  rw [S.collapse_mem_iff]
  change S.mem z.val c ↔ _
  rw [hc]
  constructor
  · intro h
    exact h.elim (fun h => Or.inl (congrArg S.collapse (Subtype.ext h)))
      (fun h => Or.inr (congrArg S.collapse (Subtype.ext h)))
  · intro h
    exact h.elim (fun h => Or.inl (congrArg Subtype.val (S.collapse_injective h)))
      (fun h => Or.inr (congrArg Subtype.val (S.collapse_injective h)))

theorem collapsed_union (hU : S.UnionAxiom) : BoundedSetTheory.Union S.collapsedModel := by
  intro a ha
  obtain ⟨a,rfl⟩ := (S.mem_collapsedModel a).mp ha
  obtain ⟨b,hb⟩ := hU a.val
  let v : S.Core := ⟨b,S.union_core a.property hb⟩
  refine ⟨S.collapse v,(S.mem_collapsedModel _).mpr ⟨v,rfl⟩,?_⟩
  intro z hz
  obtain ⟨z,rfl⟩ := (S.mem_collapsedModel z).mp hz
  constructor
  · intro h
    obtain ⟨y,hy,hzy⟩ := (hb z.val).mp ((S.collapse_mem_iff z v).mp h)
    let y' : S.Core := ⟨y,S.core_transitive a.property hy⟩
    exact ⟨S.collapse y',(S.mem_collapsedModel _).mpr ⟨y',rfl⟩,
      (S.collapse_mem_iff y' a).mpr hy,(S.collapse_mem_iff z y').mpr hzy⟩
  · rintro ⟨y,hy,hya,hzy⟩
    obtain ⟨y,rfl⟩ := (S.mem_collapsedModel y).mp hy
    exact (S.collapse_mem_iff z v).mpr ((hb z.val).mpr
      ⟨y.val,(S.collapse_mem_iff y a).mp hya,(S.collapse_mem_iff z y).mp hzy⟩)

theorem collapsed_power : PowerSet S.collapsedModel := by
  intro a ha
  obtain ⟨a,rfl⟩ := (S.mem_collapsedModel a).mp ha
  let v : S.Core := ⟨S.power a.val,S.power_core a.property⟩
  refine ⟨S.collapse v,(S.mem_collapsedModel _).mpr ⟨v,rfl⟩,?_⟩
  intro x hx
  obtain ⟨x,rfl⟩ := (S.mem_collapsedModel x).mp hx
  constructor
  · intro h y hy hyx
    have hs := (S.mem_power a.val x.val).mp ((S.collapse_mem_iff x v).mp h)
    exact (S.collapse_subset_iff x a).mpr hs hyx
  · intro h
    apply (S.collapse_mem_iff x v).mpr
    apply (S.mem_power a.val x.val).mpr
    apply (S.collapse_subset_iff x a).mp
    intro y hy
    exact h y (S.collapsedModel_transitive _ ((S.mem_collapsedModel _).mpr ⟨x,rfl⟩) _ hy) hy

theorem collapsed_separation (hS : S.SeparationAxiom) : Separation S.collapsedModel := by
  intro p e he a ha
  have hex (i : ℕ) : ∃ x : S.Core, e i = S.collapse x := (S.mem_collapsedModel _).mp (he i)
  choose d hd using hex
  obtain ⟨a,ha⟩ := (S.mem_collapsedModel a).mp ha
  obtain ⟨b,hb⟩ := hS p (fun i => (d i).val) a.val
  let v : S.Core := ⟨b,S.core_subset a.property (fun y hy => ((hb y).mp hy).1)⟩
  refine ⟨S.collapse v,(S.mem_collapsedModel _).mpr ⟨v,rfl⟩,?_⟩
  intro z hz
  obtain ⟨z,rfl⟩ := (S.mem_collapsedModel z).mp hz
  have ee : (fun i => S.collapse (push z d i)) = cons (S.collapse z) e := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact (hd i).symm
  have er : p.Realize S.collapsedModel (cons (S.collapse z) e) ↔
      S.Eval (push z.val (fun i => (d i).val)) p := by
    rw [←ee]
    apply (p.absolute S.collapsedModel S.collapsedModel_transitive _
      (fun i => (S.mem_collapsedModel _).mpr ⟨push z d i,rfl⟩)).trans
    have hv : (fun i => (push z d i).val) = push z.val (fun i => (d i).val) := by
      funext i
      cases i <;> rfl
    simpa only [hv] using S.collapse_eval p (push z d)
  rw [ha,S.collapse_mem_iff,S.collapse_mem_iff,er]
  exact hb z.val

theorem collapsed_infinity : Infinity S.collapsedModel := by
  have hn (n : ℕ) : natSet.{u} n ∈ S.collapsedModel :=
    (S.mem_collapsedModel _).mpr ⟨S.numNode n,(S.collapse_num n).symm⟩
  refine ⟨ZFSet.omega,S.collapsedModel_omega,?_,?_⟩
  · exact ⟨natSet 0,hn 0,(mem_omega _).mpr ⟨0,rfl⟩,fun z _ => ZFSet.notMem_empty z⟩
  · intro x hx hω
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hω
    refine ⟨natSet (n+1),hn (n+1),(mem_omega _).mpr ⟨n+1,rfl⟩,?_⟩
    intro z hz
    exact ZFSet.mem_insert_iff

theorem collapsed_context (hP : S.PairingAxiom) (hU : S.UnionAxiom) (hS : S.SeparationAxiom) :
    Context S.collapsedModel :=
  ⟨S.collapsedModel_transitive,S.collapsed_pairing hP,S.collapsed_union hU,
    S.collapsed_power,S.collapsed_separation hS,S.collapsed_infinity⟩

end
end TuringRigidity.OmegaModelCore.OmegaData

end OAI
