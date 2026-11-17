/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaModelCore.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelReals

/-!
# Omega Model Core
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OmegaModelCore
universe u
noncomputable section

structure OmegaData (α : Type u) where
  mem : α → α → Prop
  extensional : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  num : ℕ → α
  num_mem : ∀ x n, mem x (num n) ↔ ∃ k < n, x = num k
  omega : α
  omega_mem : ∀ x, mem x omega ↔ ∃ n, x = num n
  power_exists : ∀ a, ∃ b, ∀ x, mem x b ↔ ∀ y, mem y x → mem y a

namespace OmegaData
variable {α : Type u} (S : OmegaData α)

def power (a : α) : α := (S.power_exists a).choose

theorem mem_power (a x : α) : S.mem x (S.power a) ↔ ∀ y, S.mem y x → S.mem y a :=
  (S.power_exists a).choose_spec x

def level : ℕ → α
  | 0 => S.omega
  | n+1 => S.power (level n)

def InCore (x : α) : Prop := ∃ n, S.mem x (S.level n)

theorem num_accessible (n : ℕ) : Acc S.mem (S.num n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    constructor
    intro x hx
    obtain ⟨k,hk,rfl⟩ := (S.num_mem x n).mp hx
    exact ih k hk

theorem level_accessible (n : ℕ) : ∀ x, S.mem x (S.level n) → Acc S.mem x := by
  induction n with
  | zero =>
    intro x hx
    obtain ⟨k,rfl⟩ := (S.omega_mem x).mp hx
    exact S.num_accessible k
  | succ n ih =>
    intro x hx
    constructor
    intro y hy
    exact ih y ((S.mem_power _ x).mp hx y hy)

theorem core_accessible {x : α} (hx : S.InCore x) : Acc S.mem x := by
  obtain ⟨n,hn⟩ := hx
  exact S.level_accessible n x hn

theorem core_transitive {x y : α} (hx : S.InCore x) (hy : S.mem y x) : S.InCore y := by
  obtain ⟨n,hn⟩ := hx
  cases n with
  | zero =>
    obtain ⟨k,rfl⟩ := (S.omega_mem x).mp hn
    obtain ⟨j,hj,rfl⟩ := (S.num_mem y k).mp hy
    exact ⟨0,(S.omega_mem _).mpr ⟨j,rfl⟩⟩
  | succ n => exact ⟨n,(S.mem_power _ x).mp hn y hy⟩

abbrev Core := {x : α // S.InCore x}
def Rel (x y : S.Core) : Prop := S.mem x.val y.val

theorem core_wellFounded : WellFounded S.Rel := by
  have lift (x : α) (h : Acc S.mem x) : ∀ hx, Acc S.Rel (⟨x,hx⟩ : S.Core) := by
    induction h with
    | intro x h ih =>
      intro hx
      constructor
      intro y hy
      exact ih y.val hy y.property
  exact ⟨fun x => lift x.val (S.core_accessible x.property) x.property⟩

theorem core_extensional (x y : S.Core) (h : ∀ z : S.Core, S.Rel z x ↔ S.Rel z y) : x = y := by
  apply Subtype.ext
  apply S.extensional
  intro z
  constructor
  · intro hz
    exact (h ⟨z,S.core_transitive x.property hz⟩).mp hz
  · intro hz
    exact (h ⟨z,S.core_transitive y.property hz⟩).mpr hz

theorem core_is_wellFounded_extensional :
    WellFounded S.Rel ∧ ∀ x y : S.Core, (∀ z, S.Rel z x ↔ S.Rel z y) → x = y :=
  ⟨S.core_wellFounded,S.core_extensional⟩

end OmegaData
end
end TuringRigidity.OmegaModelCore

end OAI
