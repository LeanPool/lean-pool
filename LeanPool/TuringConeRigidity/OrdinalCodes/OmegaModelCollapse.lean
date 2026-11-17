/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaModelCollapse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaModelCore

/-!
# Omega Model Collapse
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OmegaModelCore
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section
namespace OmegaData
variable {α : Type u} (S : OmegaData α)

def collapse : S.Core → ZFSet.{u} := S.core_wellFounded.fix
  (fun x rec => ZFSet.range (fun y : {y : S.Core // S.Rel y x} => rec y.val y.property))

theorem collapse_eq (x : S.Core) :
    S.collapse x = ZFSet.range (fun y : {y : S.Core // S.Rel y x} => S.collapse y.val) := by
  rw [collapse,WellFounded.fix_eq]

@[simp] theorem mem_collapse (x : S.Core) (z : ZFSet.{u}) :
    z ∈ S.collapse x ↔ ∃ y : S.Core, S.Rel y x ∧ z = S.collapse y := by
  rw [S.collapse_eq,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨y,hy⟩,he⟩
    exact ⟨y,hy,he.symm⟩
  · rintro ⟨y,hy,he⟩
    exact ⟨⟨y,hy⟩,he.symm⟩

theorem collapse_injective : Function.Injective S.collapse := by
  intro x
  induction x using S.core_wellFounded.induction with
  | h x ih =>
    intro y he
    apply S.core_extensional
    intro z
    constructor
    · intro hz
      have hm : S.collapse z ∈ S.collapse y := he ▸ (S.mem_collapse x _).mpr ⟨z,hz,rfl⟩
      obtain ⟨w,hw,hew⟩ := (S.mem_collapse y _).mp hm
      have hzw := ih z hz hew
      exact hzw ▸ hw
    · intro hz
      have hm : S.collapse z ∈ S.collapse x := he.symm ▸ (S.mem_collapse y _).mpr ⟨z,hz,rfl⟩
      obtain ⟨w,hw,hew⟩ := (S.mem_collapse x _).mp hm
      have hwz := ih w hw hew.symm
      exact hwz ▸ hw

@[simp] theorem collapse_mem_iff (x y : S.Core) : S.collapse x ∈ S.collapse y ↔ S.Rel x y := by
  rw [S.mem_collapse]
  constructor
  · rintro ⟨z,hz,he⟩
    exact S.collapse_injective he ▸ hz
  · intro h
    exact ⟨x,h,rfl⟩

def collapsedModel : ZFSet.{u} := ZFSet.range S.collapse

@[simp] theorem mem_collapsedModel (z : ZFSet.{u}) :
    z ∈ S.collapsedModel ↔ ∃ x : S.Core, z = S.collapse x := by
  rw [collapsedModel,ZFSet.mem_range]
  exact exists_congr (fun x => eq_comm)

theorem collapsedModel_transitive : Transitive S.collapsedModel := by
  intro x hx y hy
  obtain ⟨a,rfl⟩ := (S.mem_collapsedModel x).mp hx
  obtain ⟨b,hb,rfl⟩ := (S.mem_collapse a y).mp hy
  exact (S.mem_collapsedModel _).mpr ⟨b,rfl⟩

def numNode (n : ℕ) : S.Core := ⟨S.num n,0,(S.omega_mem _).mpr ⟨n,rfl⟩⟩

theorem rel_numNode (x : S.Core) (n : ℕ) :
    S.Rel x (S.numNode n) ↔ ∃ k < n, x = S.numNode k := by
  change S.mem x.val (S.num n) ↔ _
  rw [S.num_mem]
  constructor
  · rintro ⟨k,hk,he⟩
    exact ⟨k,hk,Subtype.ext he⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨k,hk,rfl⟩

theorem collapse_num (n : ℕ) : S.collapse (S.numNode n) = natSet n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply ZFSet.ext
    intro z
    rw [S.mem_collapse,mem_natSet]
    constructor
    · rintro ⟨x,hx,hz⟩
      obtain ⟨k,hk,rfl⟩ := (S.rel_numNode x n).mp hx
      exact ⟨k,hk,hz.trans (ih k hk)⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨S.numNode k,(S.rel_numNode _ n).mpr ⟨k,hk,rfl⟩,(ih k hk).symm⟩

def omegaNode : S.Core := ⟨S.omega,1,(S.mem_power S.omega S.omega).mpr (fun _ h => h)⟩

theorem collapse_omega : S.collapse S.omegaNode = ZFSet.omega := by
  apply ZFSet.ext
  intro z
  rw [S.mem_collapse,mem_omega]
  constructor
  · rintro ⟨x,hx,hz⟩
    obtain ⟨n,hn⟩ := (S.omega_mem x.val).mp hx
    have he : x = S.numNode n := Subtype.ext hn
    exact ⟨n,by rw [hz,he,S.collapse_num]⟩
  · rintro ⟨n,rfl⟩
    exact ⟨S.numNode n,(S.omega_mem _).mpr ⟨n,rfl⟩,(S.collapse_num n).symm⟩

theorem collapsedModel_omega : ZFSet.omega.{u} ∈ S.collapsedModel :=
  (S.mem_collapsedModel _).mpr ⟨S.omegaNode,S.collapse_omega.symm⟩

theorem collapse_real (x : α) (hx : S.mem x (S.power S.omega)) :
    ∃ A : TuringRigidity.Oracle,
      S.collapse (⟨x,1,hx⟩ : S.Core) = realSet A ∧
      ∀ n, A n = true ↔ S.mem (S.num n) x := by
  let c : S.Core := ⟨x,1,hx⟩
  have hsub : S.collapse c ⊆ ZFSet.omega := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := (S.mem_collapse c z).mp hz
    have hyω := (S.mem_power _ _).mp hx y.val hy
    rw [←S.collapse_omega,S.collapse_mem_iff]
    exact hyω
  refine ⟨oracleOf (S.collapse c),(realSet_oracleOf hsub).symm,?_⟩
  intro n
  simp only [oracleOf,decide_eq_true_eq]
  rw [←S.collapse_num,S.collapse_mem_iff]
  rfl

end OmegaData
end
end TuringRigidity.OmegaModelCore

end OAI
