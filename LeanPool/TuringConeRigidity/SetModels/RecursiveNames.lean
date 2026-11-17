/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RecursiveNames.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CountableForcing
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Recursive Names
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u}

inductive Name (P : Type u) : Type (u + 1) where
  | mk (ι : Type u) (child : ι → Name P) (tag : ι → P) : Name P

namespace Name
noncomputable def val (G : Set P) : Name P → ZFSet.{u}
  | .mk _ child tag => ZFSet.range (fun i : {i // tag i ∈ G} => val G (child i.val))

theorem mem_val (G : Set P) (ι : Type u) (child : ι → Name P) (tag : ι → P)
    (x : ZFSet.{u}) : x ∈ val G (.mk ι child tag) ↔
      ∃ i, tag i ∈ G ∧ val G (child i) = x := by
  simp only [val, ZFSet.mem_range]
  exact ⟨fun ⟨i,h⟩ => ⟨i.val,i.property,h⟩, fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩⟩

def rename {Q : Type u} (e : P → Q) : Name P → Name Q
  | .mk ι child tag => .mk ι (fun i => rename e (child i)) (e ∘ tag)

theorem val_rename {Q : Type u} (e : P → Q) (G : Set P) (H : Set Q)
    (h : ∀ p, e p ∈ H ↔ p ∈ G) (τ : Name P) :
    val H (rename e τ) = val G τ := by
  induction τ with
  | mk ι child tag ih =>
    apply ZFSet.ext
    intro x
    simp only [rename, mem_val, Function.comp_apply, h, ih]

def checkPSet [Top P] : PSet.{u} → Name P
  | .mk ι child => .mk ι (fun i => checkPSet (child i)) (fun _ => ⊤)

noncomputable def check [Top P] (x : ZFSet.{u}) : Name P := checkPSet x.out

theorem val_checkPSet [Top P] (G : Set P) (hG : ⊤ ∈ G) (x : PSet.{u}) :
    val G (checkPSet x : Name P) = ZFSet.mk x := by
  induction x with
  | mk ι child ih =>
    apply ZFSet.ext
    intro y
    induction y using Quotient.inductionOn with
    | h y =>
      change ZFSet.mk y ∈ val G (.mk ι (fun index => checkPSet (child index))
        (fun _ => ⊤)) ↔ ZFSet.mk y ∈ ZFSet.mk (.mk ι child)
      rw [mem_val]
      simp only [hG, true_and, ih]
      change (∃ i, ZFSet.mk (child i) = ZFSet.mk y) ↔
        ∃ i, PSet.Equiv y (child i)
      simp only [ZFSet.eq]
      exact exists_congr (fun i => PSet.Equiv.comm)

theorem val_check [Top P] (G : Set P) (hG : ⊤ ∈ G) (x : ZFSet.{u}) :
    val G (check x : Name P) = x := by
  rw [check, val_checkPSet G hG, ZFSet.mk_out]

theorem rename_checkPSet {Q : Type u} [Top P] [Top Q]
    (e : P → Q) (he : e ⊤ = ⊤) (x : PSet.{u}) :
    rename e (checkPSet x) = checkPSet x := by
  induction x with
  | mk ι child ih =>
    simp only [checkPSet, rename, Function.comp_def, he, ih]

theorem rename_check {Q : Type u} [Top P] [Top Q]
    (e : P → Q) (he : e ⊤ = ⊤) (x : ZFSet.{u}) :
    rename e (check x) = check x := rename_checkPSet e he x.out

end Name
end TuringRigidity.RecursiveNames

end OAI
