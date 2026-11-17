/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/ProgramTopology.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.OracleCode
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Instances.Nat

/-!
# Program Topology
-/


@[expose] public section

namespace OAI

open Set
namespace TuringRigidity

def OpenFiber {X α : Type*} [TopologicalSpace X] (f : X → Part α) : Prop :=
  ∀ a, IsOpen {x | a ∈ f x}

namespace OpenFiber
variable {X : Type*} {α β : Type} [TopologicalSpace X]

theorem const (p : Part α) : OpenFiber (fun _ : X => p) := by
  intro a
  by_cases h : a ∈ p <;> simp [h]

theorem map {f : X → Part α} (hf : OpenFiber f) (g : α → β) :
    OpenFiber (fun x => (f x).map g) := by
  intro b
  have heq : {x | b ∈ (f x).map g} =
      ⋃ a : α, {x : X | g a = b} ∩ {x | a ∈ f x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Part.mem_map_iff]
    exact ⟨fun ⟨a,ha,hg⟩ => ⟨a,hg,ha⟩, fun ⟨a,hg,ha⟩ => ⟨a,ha,hg⟩⟩
  rw [heq]
  apply isOpen_iUnion
  intro a
  have hg : IsOpen {x : X | g a = b} := by by_cases h : g a = b <;> simp [h]
  exact hg.inter (hf a)

theorem bind {f : X → Part α} {g : X → α → Part β}
    (hf : OpenFiber f) (hg : ∀ a, OpenFiber (fun x => g x a)) :
    OpenFiber (fun x => (f x).bind (g x)) := by
  intro b
  have heq : {x | b ∈ (f x).bind (g x)} =
      ⋃ a : α, {x | a ∈ f x} ∩ {x | b ∈ g x a} := by
    ext x
    simp [Part.mem_bind_iff]
  rw [heq]
  exact isOpen_iUnion (fun a => (hf a).inter (hg a b))

theorem seq {f : X → Part (α → β)} {g : X → Part α}
    (hf : OpenFiber f) (hg : OpenFiber g) :
    OpenFiber (fun x => f x <*> g x) := by
  exact hf.bind (fun k => hg.map k)

theorem some [TopologicalSpace α] [DiscreteTopology α] {f : X → α} (hf : Continuous f) :
    OpenFiber (fun x => Part.some (f x)) := by
  intro a
  simpa [Set.preimage, Part.mem_some_iff, eq_comm] using
    (isOpen_discrete ({a} : Set α)).preimage hf

theorem rfind {p : X → ℕ → Part Bool} (hp : ∀ n, OpenFiber (fun x => p x n)) :
    OpenFiber (fun x => Nat.rfind (p x)) := by
  intro n
  have heq : {x | n ∈ Nat.rfind (p x)} =
      {x | true ∈ p x n} ∩ ⋂ k : Fin n, {x | false ∈ p x k.val} := by
    ext x
    constructor
    · intro h
      have hr := Nat.mem_rfind.mp h
      exact ⟨hr.1, Set.mem_iInter.mpr (fun k => hr.2 k.isLt)⟩
    · rintro ⟨h,hmin⟩
      exact Nat.mem_rfind.mpr ⟨h,fun {k} hk => Set.mem_iInter.mp hmin ⟨k,hk⟩⟩
  rw [heq]
  exact (hp n true).inter (isOpen_iInter_of_finite (fun k : Fin n => hp k.val false))
end OpenFiber

namespace OracleCode

theorem eval_openFiber {X : Type*} [TopologicalSpace X] (O : X → ℕ → ℕ)
    (hO : ∀ n, Continuous (fun x => O x n)) (c : OracleCode) :
    ∀ n, OpenFiber (fun x => eval (fun k => Part.some (O x k)) c n) := by
  induction c with
  | zero => intro n; exact OpenFiber.const _
  | succ => intro n; exact OpenFiber.const _
  | left => intro n; exact OpenFiber.const _
  | right => intro n; exact OpenFiber.const _
  | query => intro n; exact OpenFiber.some (hO n)
  | pair c d hc hd => intro n; exact (OpenFiber.map (hc n) Nat.pair).seq (hd n)
  | comp c d hc hd => intro n; exact (hd n).bind (fun k => hc k)
  | prec c d hc hd =>
      intro p
      have hrec : ∀ k : ℕ, OpenFiber (fun x =>
          Nat.rec (eval (fun j => Part.some (O x j)) c (Nat.unpair p).1)
            (fun y ih => ih.bind (fun i =>
              eval (fun j => Part.some (O x j)) d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k)
                := by
        intro k
        induction k with
        | zero => exact hc _
        | succ k ih => exact ih.bind (fun i => hd _)
      exact hrec (Nat.unpair p).2
  | find c hc =>
      intro n
      exact OpenFiber.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

theorem halting_set_open (c : OracleCode) (n m : ℕ) :
    IsOpen {A : Oracle | m ∈ eval (oracleFunction A) c n} := by
  have hO : ∀ n : ℕ, Continuous (fun A : Oracle => if A n then (1 : ℕ) else 0) := by
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℕ) else
      0)).comp
      (continuous_apply n)
  exact eval_openFiber _ hO c n m

theorem eval_eq_oracle_iff (c : OracleCode) (A B : Oracle) :
    eval (oracleFunction A) c = oracleFunction B ↔
      ∀ n, (if B n then 1 else 0) ∈ eval (oracleFunction A) c n := by
  constructor
  · intro h n
    rw [h]
    exact Part.mem_some _
  · intro h
    funext n
    exact Part.eq_some_iff.mpr (h n)

theorem success_measurable {X : Type*} [MeasurableSpace X]
    (c : OracleCode) (A B : X → Oracle) (hA : Measurable A) (hB : Measurable B) :
    MeasurableSet {x | eval (oracleFunction (A x)) c = oracleFunction (B x)} := by
  have hv : ∀ n, Measurable (fun x => if B x n then (1 : ℕ) else 0) := by
    intro n
    exact (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      ((measurable_pi_apply n).comp hB)
  have hh (n m : ℕ) : MeasurableSet {x | m ∈ eval (oracleFunction (A x)) c n} :=
    (halting_set_open c n m).measurableSet.preimage hA
  simp_rw [eval_eq_oracle_iff]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  have heq : {x | (if B x n then 1 else 0) ∈ eval (oracleFunction (A x)) c n} =
      ⋃ m : ℕ, {x | (if B x n then 1 else 0) = m} ∩
        {x | m ∈ eval (oracleFunction (A x)) c n} := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun m => (measurableSet_eq_fun (hv n) measurable_const).inter (hh n
    m))
end OracleCode

end TuringRigidity

end OAI
