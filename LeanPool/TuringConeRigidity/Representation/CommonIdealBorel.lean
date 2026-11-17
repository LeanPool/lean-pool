/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CommonIdealBorel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CommonIdeal

/-!
# Common Ideal Borel
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OracleCode
theorem eval_partial_openFiber {X : Type*} [TopologicalSpace X] (O : X → ℕ →. ℕ)
    (hO : ∀ n, OpenFiber (fun x => O x n)) (c : OracleCode) :
    ∀ n, OpenFiber (fun x => eval (O x) c n) := by
  induction c with
  | zero => intro n; exact OpenFiber.const _
  | succ => intro n; exact OpenFiber.const _
  | left => intro n; exact OpenFiber.const _
  | right => intro n; exact OpenFiber.const _
  | query => intro n; exact hO n
  | pair c d hc hd => intro n; exact (OpenFiber.map (hc n) Nat.pair).seq (hd n)
  | comp c d hc hd => intro n; exact (hd n).bind (fun k => hc k)
  | prec c d hc hd =>
      intro p
      have hrec : ∀ k : ℕ, OpenFiber (fun x =>
          Nat.rec (eval (O x) c (Nat.unpair p).1)
            (fun y ih => ih.bind (fun i =>
              eval (O x) d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k) := by
        intro k
        induction k with
        | zero => exact hc _
        | succ k ih => exact ih.bind (fun i => hd _)
      exact hrec (Nat.unpair p).2
  | find c hc =>
      intro n
      exact OpenFiber.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

end TuringRigidity.OracleCode
namespace TuringRigidity.CommonIdeal
open Set

theorem run_open (p : OracleCode) (s : List Bool) (n a : ℕ) :
    IsOpen {A : Oracle | a ∈ run A p s n} := by
  apply OracleCode.eval_partial_openFiber
  intro k
  unfold partialJoin
  split
  · exact OpenFiber.const _
  · apply OpenFiber.some
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℕ) else
      0)).comp
      (continuous_apply (k/2))

theorem disagree_measurable (p q : OracleCode) (s t : List Bool) :
    MeasurableSet {A | Disagree A p q s t} := by
  simp only [Disagree, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  by_cases h : a ≠ b
  · have he : {A : Oracle | a ≠ b ∧ a ∈ run A p s n ∧ b ∈ run A q t n} =
        {A | a ∈ run A p s n} ∩ {A | b ∈ run A q t n} := by
      ext A
      exact ⟨fun hx => hx.2,fun hx => ⟨h,hx⟩⟩
    rw [he]
    exact (run_open p s n a).measurableSet.inter (run_open q t n b).measurableSet
  · simp [h]

theorem agree_measurable (p q : OracleCode) (s t : List Bool) :
    MeasurableSet {A | Agree A p q s t} := by
  have he : {A | Agree A p q s t} =
      (⋃ (u : List Bool) (v : List Bool), {A | s <+: u ∧ t <+: v ∧ Disagree A p q u v})ᶜ := by
    ext A
    simp only [mem_compl_iff,mem_iUnion,mem_ofPred_eq]
    constructor
    · intro h ⟨u,v,hu,hv,n,a,b,hab,ha,hb⟩
      exact hab (h u v n a b hu hv ha hb)
    · intro h u v n a b hu hv ha hb
      by_contra hab
      exact h ⟨u,v,hu,hv,n,a,b,hab,ha,hb⟩
  rw [he]
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro u
  apply MeasurableSet.iUnion
  intro v
  by_cases hs : s <+: u ∧ t <+: v
  · simpa [hs.1,hs.2] using disagree_measurable p q u v
  · have hfalse : ¬ (s <+: u ∧ t <+: v) := hs
    convert MeasurableSet.empty (α := Oracle) using 1
    ext A
    simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,not_and]
    intro hsu htv
    exact False.elim (hfalse ⟨hsu,htv⟩)

theorem requirement_measurable (p q : OracleCode) (s t : List Bool) :
    MeasurableSet {A | Requirement A p q s t} :=
  (disagree_measurable p q s t).union (agree_measurable p q s t)

end TuringRigidity.CommonIdeal

end OAI
