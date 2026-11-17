/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameValidity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalFixedPoint
public import LeanPool.TuringConeRigidity.SetModels.NameUnionCode

/-!
# Name Validity
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.NameValidity
open RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

def Step (c h x : ZFSet.{u}) : Prop :=
  ∀ z ∈ x, ∃ y ∈ h, ∃ q ∈ c, z = ZFSet.pair y q

def Certificate (d c h : ZFSet.{u}) : Prop :=
  h ⊆ d ∧ ∀ x ∈ d, x ∈ h ↔ Step c h x

def Child (y x : ZFSet.{u}) : Prop := ∃ q, ZFSet.pair y q ∈ x

theorem child_wellFounded : WellFounded (Child : ZFSet.{u} → ZFSet.{u} → Prop) := by
  apply ZFSet.mem_wf.transGen.mono
  intro y x h
  obtain ⟨q,hq⟩ := h
  exact Relation.TransGen.tail
    (Relation.TransGen.tail (Relation.TransGen.single (ZFSet.mem_singleton.mpr rfl))
      (show ({y} : ZFSet.{u}) ∈ ZFSet.pair y q from ZFSet.mem_pair.mpr (Or.inl rfl))) hq

theorem Certificate.decode {d c h : ZFSet.{u}} (hh : Certificate d c h)
    (x : ZFSet.{u}) (hx : x ∈ h) :
    ∃ a : Name (Conditions c), a.encode (label c) = x := by
  classical
  induction x using child_wellFounded.induction with
  | h x ih =>
    have step := (hh.2 x (hh.1 hx)).mp hx
    have entry (i : Conditions x) : ∃ a : Name (Conditions c), ∃ q : Conditions c,
        label x i = ZFSet.pair (a.encode (label c)) (label c q) := by
      obtain ⟨y,hy,q,hq,heq⟩ := step _ (label_mem x i)
      obtain ⟨a,rfl⟩ := ih y ⟨q,heq ▸ label_mem x i⟩ hy
      obtain ⟨r,rfl⟩ := label_surjective c hq
      exact ⟨a,r,heq⟩
    let a : Conditions x → Name (Conditions c) := fun i => (entry i).choose
    let q : Conditions x → Conditions c := fun i => (entry i).choose_spec.choose
    have heq (i : Conditions x) : label x i = ZFSet.pair ((a i).encode (label c)) (label c (q i)) :=
      (entry i).choose_spec.choose_spec
    refine ⟨.mk (Conditions x) a q,?_⟩
    apply ZFSet.ext
    intro z
    change z ∈ ZFSet.range _ ↔ z ∈ x
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨i,rfl⟩
      rw [←heq i]
      exact label_mem x i
    · intro hz
      obtain ⟨i,rfl⟩ := label_surjective x hz
      exact ⟨i,(heq i).symm⟩

theorem Certificate.encode_mem {d c h : ZFSet.{u}} (hd : Transitive d)
    (hh : Certificate d c h) (a : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) : a.encode (label c) ∈ h := by
  induction a with
  | mk ι a q ih =>
    apply (hh.2 _ ha).mpr
    intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    have hai : (a i).encode (label c) ∈ d :=
      names_childClosed d c hd (.mk ι a q) ha (a i) ⟨i,rfl⟩
    exact ⟨_,ih i hai,_,label_mem c (q i),rfl⟩

theorem Certificate.correct {d c h : ZFSet.{u}} (hd : Transitive d)
    (hh : Certificate d c h) {x : ZFSet.{u}} (hx : x ∈ d) :
    x ∈ h ↔ ∃ a : Name (Conditions c), a.encode (label c) = x := by
  constructor
  · exact hh.decode x
  · rintro ⟨a,rfl⟩
    exact hh.encode_mem hd a hx

namespace Code
open Formula
def step (c h x : ℕ) : Formula :=
  allMem x (.existsMem (h+1) (.existsMem (c+2) (orderedPair 2 1 0)))

theorem eval_step (c h x : ℕ) (e : ℕ → ZFSet.{u}) :
    (step c h x).Eval e ↔ Step (e c) (e h) (e x) := by
  simp only [step,Step,eval_allMem,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]

def certificate (d c h : ℕ) : Formula :=
  .conj (subset h d) (allMem d (iff (.member 0 (h+1)) (step (c+1) (h+1) 0)))

theorem eval_certificate (d c h : ℕ) (e : ℕ → ZFSet.{u}) :
    (certificate d c h).Eval e ↔ Certificate (e d) (e c) (e h) := by
  simp only [certificate,Certificate,Formula.Eval,eval_subset,eval_allMem,eval_iff,
    eval_step,cons_zero,cons_succ]
end Code

theorem internal_certificate (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d c : ZFSet.{u}} (hd : d ∈ M) (hc : c ∈ M) :
    ∃ h ∈ M, Certificate d c h := by
  obtain ⟨h,hh,hs,hdef⟩ := internal_fixed_point M hM hU hPow hS
    (Code.step 2 1 0) (fun _ => c) (fun _ => hc) d hd (by
      intro f g _ _ hfg x _ hf
      rw [Code.eval_step] at hf ⊢
      intro z hz
      obtain ⟨y,hy,q,hq,heq⟩ := hf z hz
      exact ⟨y,hfg hy,q,hq,heq⟩)
  exact ⟨h,hh,hs,fun x hx => (hdef x hx).trans (Code.eval_step 2 1 0 _)⟩

end TuringRigidity.NameValidity

end OAI
