/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaModelCoreClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaModelCollapse

/-!
# Omega Model Core Closure
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OmegaModelCore.OmegaData
universe u
noncomputable section
variable {α : Type u} (S : OmegaData α)

def TransitiveAt (a : α) : Prop := ∀ x, S.mem x a → ∀ y, S.mem y x → S.mem y a

theorem omega_transitive : S.TransitiveAt S.omega := by
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (S.omega_mem x).mp hx
  obtain ⟨k,hk,rfl⟩ := (S.num_mem y n).mp hy
  exact (S.omega_mem _).mpr ⟨k,rfl⟩

theorem power_transitive {a : α} (ha : S.TransitiveAt a) : S.TransitiveAt (S.power a) := by
  intro x hx y hy
  apply (S.mem_power a y).mpr
  intro z hz
  exact ha y ((S.mem_power a x).mp hx y hy) z hz

theorem level_transitive (n : ℕ) : S.TransitiveAt (S.level n) := by
  induction n with
  | zero => exact S.omega_transitive
  | succ n ih => exact S.power_transitive ih

theorem level_succ {n : ℕ} {x : α} (hx : S.mem x (S.level n)) :
    S.mem x (S.level (n+1)) :=
  (S.mem_power _ x).mpr (fun y hy => S.level_transitive n x hx y hy)

theorem level_mono {n m : ℕ} (hnm : n ≤ m) {x : α} (hx : S.mem x (S.level n)) :
    S.mem x (S.level m) := by
  induction hnm with
  | refl => exact hx
  | step h ih => exact S.level_succ ih

theorem core_of_subset_level {x : α} {n : ℕ}
    (hx : ∀ y, S.mem y x → S.mem y (S.level n)) : S.InCore x :=
  ⟨n+1,(S.mem_power _ _).mpr hx⟩

theorem core_subset {x a : α} (ha : S.InCore a) (hx : ∀ y, S.mem y x → S.mem y a) :
    S.InCore x := by
  obtain ⟨n,hn⟩ := ha
  exact S.core_of_subset_level (fun y hy => S.level_transitive n a hn y (hx y hy))

theorem power_core {a : α} (ha : S.InCore a) : S.InCore (S.power a) := by
  obtain ⟨n,hn⟩ := ha
  apply S.core_of_subset_level (n := n+1)
  intro x hx
  apply (S.mem_power _ x).mpr
  intro y hy
  exact S.level_transitive n a hn y ((S.mem_power a x).mp hx y hy)

theorem pair_core {a b c : α} (ha : S.InCore a) (hb : S.InCore b)
    (hc : ∀ x, S.mem x c ↔ x = a ∨ x = b) : S.InCore c := by
  obtain ⟨n,hn⟩ := ha
  obtain ⟨m,hm⟩ := hb
  apply S.core_of_subset_level (n := max n m)
  intro x hx
  rcases (hc x).mp hx with rfl|rfl
  · exact S.level_mono (Nat.le_max_left _ _) hn
  · exact S.level_mono (Nat.le_max_right _ _) hm

theorem union_core {a b : α} (ha : S.InCore a)
    (hb : ∀ x, S.mem x b ↔ ∃ y, S.mem y a ∧ S.mem x y) : S.InCore b := by
  obtain ⟨n,hn⟩ := ha
  apply S.core_of_subset_level (n := n)
  intro x hx
  obtain ⟨y,hy,hxy⟩ := (hb x).mp hx
  exact S.level_transitive n y (S.level_transitive n a hn y hy) x hxy

theorem collapse_subset_iff (x y : S.Core) :
    S.collapse x ⊆ S.collapse y ↔ ∀ z, S.mem z x.val → S.mem z y.val := by
  constructor
  · intro h z hz
    let c : S.Core := ⟨z,S.core_transitive x.property hz⟩
    exact (S.collapse_mem_iff c y).mp (h ((S.collapse_mem_iff c x).mpr hz))
  · intro h z hz
    obtain ⟨c,hc,rfl⟩ := (S.mem_collapse x z).mp hz
    exact (S.collapse_mem_iff c y).mpr (h c.val hc)

end
end TuringRigidity.OmegaModelCore.OmegaData

end OAI
