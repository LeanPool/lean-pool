/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.ActivationAlgorithm
import LeanPool.Parikh.BoundedFamilySupport

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Executable adapters for witness compilation

Structural equality compares trees with an explicit height budget. List-based
components preserve context identities and avoid classical finite-set listing.
Source: `sec:effective`, `eq:component`, `lem:activation-test`.
-/
namespace Parikh
namespace ParseTree
variable {T N : Type*} [DecidableEq T] [DecidableEq N]

/-- Compare tree syntax through a fixed production height, without recursive
runtime helpers or a classical equality decision. -/
@[expose] def equalAt (H : ℕ) : ParseTree T N → ParseTree T N → Bool :=
  Nat.rec
    (fun t u => match t, u with
      | .terminal a, .terminal b => decide (a = b)
      | .hole A, .hole B => decide (A = B)
      | _, _ => false)
    (fun _ next t u => match t, u with
      | .terminal a, .terminal b => decide (a = b)
      | .hole A, .hole B => decide (A = B)
      | .node r cs, .node s ds => decide (r = s) && cs.isEqv ds next
      | _, _ => false) H

/-- Sufficient height makes the structural comparison exact. -/
theorem equalAt_correct (H : ℕ) (t u : ParseTree T N)
    (ht : t.height ≤ H) (hu : u.height ≤ H) : equalAt H t u = true ↔ t = u := by
  induction H generalizing t u with
  | zero =>
    cases t <;> cases u <;> simp [equalAt]
    all_goals rw [height.eq_3] at ht; omega
  | succ H ih =>
    have hlist : ∀ cs ds : List (ParseTree T N),
        (∀ c ∈ cs, c.height ≤ H) → (∀ d ∈ ds, d.height ≤ H) →
        (cs.isEqv ds (equalAt H) = true ↔ cs = ds) := by
      intro cs ds hc hd
      induction cs generalizing ds with
      | nil => cases ds <;> simp [List.isEqv]
      | cons c cs hcs =>
        cases ds with
        | nil => simp [List.isEqv]
        | cons d ds =>
          simp only [List.isEqv, Bool.and_eq_true]
          rw [ih c d (hc c (by simp)) (hd d (by simp)),
            hcs ds (fun x hx => hc x (by simp [hx]))
              (fun x hx => hd x (by simp [hx]))]
          simp only [List.cons.injEq]
    cases t with
    | terminal a => cases u <;> simp [equalAt]
    | hole A => cases u <;> simp [equalAt]
    | node r cs =>
      cases u with
      | terminal a => simp [equalAt]
      | hole A => simp [equalAt]
      | node s ds =>
        have hc : ∀ c ∈ cs, c.height ≤ H := fun c hc => by
          have := height_child_lt r cs c hc
          omega
        have hd : ∀ d ∈ ds, d.height ≤ H := fun d hd => by
          have := height_child_lt s ds d hd
          omega
        change (decide (r = s) && cs.isEqv ds (equalAt H)) = true ↔ _
        simp only [Bool.and_eq_true, decide_eq_true_eq, hlist cs ds hc hd, node.injEq]

/-- A computable equality decision for the existing nested parse-tree syntax.
It is supplied explicitly by the compiler, without a new global instance. -/
@[expose] def decEq : DecidableEq (ParseTree T N) := fun t u =>
  decidable_of_iff (equalAt (t.height + u.height) t u = true)
    (equalAt_correct _ t u (by omega) (by omega))
end ParseTree

/-- Assemble in list order: each context pays once in the base and retains its
own period position, even when weights coincide or vanish. -/
@[expose] def listComponent {T N : Type*} [DecidableEq T]
    (B : ParseTree T N) (D : List (ParseTree T N)) : Component T :=
  ⟨B.weight + (D.map ParseTree.weight).sum, D.map ParseTree.weight⟩

/-- Listing a context set in any duplicate-free order preserves its exact
linear-set denotation. No equality or deduplication of weights is required. -/
theorem listComponent_denotation {T N : Type*} [DecidableEq T]
    [DecidableEq (ParseTree T N)]
    (B : ParseTree T N) (D : List (ParseTree T N)) (hD : D.Nodup) :
    (listComponent B D).denotation = (contextComponent B D.toFinset).denotation := by
  classical
  have hbase : (listComponent B D).base = (contextComponent B D.toFinset).base := by
    change B.weight + (D.map ParseTree.weight).sum = B.weight + ∑ C ∈ D.toFinset, C.weight
    rw [List.sum_toFinset ParseTree.weight hD]
  have hrange : Set.range (listComponent B D).periods.get =
      Set.range (contextComponent B D.toFinset).periods.get := by
    ext w
    simp [listComponent, contextComponent]
  rw [Component.denotation_eq_vadd_closure, Component.denotation_eq_vadd_closure,
    hbase, hrange]

namespace ParseTree
/-- Extract a nonterminal root; the default is irrelevant for certified cycles. -/
@[expose] def rootLabel {T N : Type*} (default : N) (t : ParseTree T N) : N :=
  match t.root with
  | .terminal _ => default
  | .nonterminal A => A
end ParseTree

/-- Run the existing activation algorithm on actual context identities and
finite production-label supports. -/
@[expose] def contextActivation {T : Type*} (g : ContextFreeGrammar T)
    [DecidableEq g.NT] [DecidableEq (ParseTree T g.NT)]
    (B : ParseTree T g.NT) (D : List (ParseTree T g.NT)) : Bool :=
  (activationTest g.NT (ParseTree T g.NT)).run (ParseTree.rootLabel g.initial)
    (fun C => C.productionLabels.toFinset) B.productionLabels.toFinset D.toFinset

/-- For a family of cycles, the executable support test is exactly the accepted
grammar activation predicate. -/
theorem contextActivation_correct {T : Type*} (g : ContextFreeGrammar T)
    [DecidableEq g.NT] [DecidableEq (ParseTree T g.NT)]
    (B : ParseTree T g.NT) (D : List (ParseTree T g.NT))
    (hD : ∀ C ∈ D, ∃ A, Cycle g C A) :
    contextActivation g B D = true ↔ ContextsActivatable g B D.toFinset := by
  have hroot (C : ParseTree T g.NT) (A : g.NT) (h : Cycle g C A) :
      ParseTree.rootLabel g.initial C = A := by
    unfold ParseTree.rootLabel
    rw [h.2.1]
  have hcycles : ∀ C ∈ D.toFinset, Cycle g C (ParseTree.rootLabel g.initial C) := by
    intro C hC
    obtain ⟨A, ha⟩ := hD C (List.mem_toFinset.mp hC)
    simpa only [hroot C A ha] using ha
  have hsupport (C : ParseTree T g.NT) :
      (C.productionLabels.toFinset : Set g.NT) = C.support := by
    ext A
    simp [ParseTree.support]
  rw [contextActivation, (activationTest g.NT (ParseTree T g.NT)).correct]
  simp only [hsupport]
  constructor
  · rintro ⟨order, hn, hm, ho⟩
    exact ⟨order, hn, hm, ParseTree.rootLabel g.initial, hcycles, ho⟩
  · rintro ⟨order, hn, hm, roots, hc, ho⟩
    refine ⟨order, hn, hm, ?_⟩
    have heq : ∀ C ∈ order, ParseTree.rootLabel g.initial C = roots C :=
      fun C hC => hroot C (roots C) (hc C ((hm C).mp hC))
    have hcongr : ∀ (U : Set g.NT) (cs : List (ParseTree T g.NT)),
        (∀ c ∈ cs, ParseTree.rootLabel g.initial c = roots c) →
        (ActivationOrder roots ParseTree.support U cs ↔
          ActivationOrder (ParseTree.rootLabel g.initial) ParseTree.support U cs) := by
      intro U cs he
      induction cs generalizing U with
      | nil => rfl
      | cons c cs ih =>
        simp only [ActivationOrder, he c (by simp)]
        rw [ih (U ∪ c.support) (fun d hd => he d (by simp [hd]))]
    exact (hcongr _ order heq).mp ho
end Parikh
