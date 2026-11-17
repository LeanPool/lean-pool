/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/FiniteGraphSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.SetSatisfactionBounded
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleTupleSpace

/-!
# Finite Graph Satisfaction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- Prepend the first `n` values of `w` to the environment in their original order. -/
def prependValues (w : ℕ → ZFSet.{u}) : ℕ → (ℕ → ZFSet.{u}) → ℕ → ZFSet.{u}
  | 0, e => e
  | n+1, e => prependValues w n (cons (w n) e)

theorem prependValues_tail (w : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u}) (i : ℕ) :
    prependValues w n e (n+i) = e i := by
  induction n generalizing e i with
  | zero => simp [prependValues]
  | succ n ih =>
    change prependValues w n (cons (w n) e) (n+1+i) = e i
    rw [show n+1+i = n+(i+1) by omega,ih]
    rfl

theorem prependValues_lt (w : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u})
    (i : ℕ) (hi : i < n) : prependValues w n e i = w i := by
  induction n generalizing e with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · exact ih _ hin
    · have he : i = n := by omega
      subst i
      exact prependValues_tail w n (cons (w n) e) 0

/-- Read the selected finite sequence of values from a graph before evaluating the body. -/
def readGraph : ℕ → ℕ → ℕ → (ℕ → ℕ) → Formula → Formula
  | 0, _, _, _, ψ => ψ
  | n+1, a, g, idx, ψ => .existsMem a
      (.conj (.pairMem (idx n+1) 0 (g+1))
        (readGraph n (a+1) (g+1) (fun i => idx i+1) ψ))

theorem readGraph_eval (n a g : ℕ) (idx : ℕ → ℕ) (ψ : Formula)
    (e w : ℕ → ZFSet.{u}) (hw : ∀ i, i < n → w i ∈ e a)
    (hg : ∀ i, i < n → ∀ y ∈ e a,
      (ZFSet.pair (e (idx i)) y ∈ e g ↔ y = w i)) :
    (readGraph n a g idx ψ).Eval e ↔ ψ.Eval (prependValues w n e) := by
  induction n generalizing a g idx e with
  | zero => rfl
  | succ n ih =>
    simp only [readGraph,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]
    constructor
    · rintro ⟨x,hx,hpair,hbody⟩
      have he : x = w n := (hg n (by omega) x hx).mp hpair
      subst x
      exact (ih (a+1) (g+1) (fun i => idx i+1) (cons (w n) e)
        (fun i hi => hw i (by omega)) (fun i hi => hg i (by omega))).mp hbody
    · intro h
      refine ⟨w n,hw n (by omega),(hg n (by omega) _ (hw n (by omega))).mpr rfl,?_⟩
      exact (ih (a+1) (g+1) (fun i => idx i+1) (cons (w n) e)
        (fun i hi => hw i (by omega)) (fun i hi => hg i (by omega))).mpr h

/-- Interpret a full formula through its finite tuple graph and an explicitly bounded domain. -/
def graphTruth (p : SentenceForm) (a g : ℕ) (idx : ℕ → ℕ) : Formula :=
  readGraph p.bound a g idx (setBounded p (p.bound+a) id)

theorem graphTruth_spec (p : SentenceForm) (a g : ℕ) (idx : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ e a) (hb : p.bound ≤ n) (hg : e g = tupleGraph v)
    (hi : ∀ i, i < p.bound → e (idx i) = natSet i) :
    (graphTruth p a g idx).Eval e ↔ p.Sat (e a : Set ZFSet) (tupleEnv v) := by
  have hw (i : ℕ) (h : i < p.bound) : tupleEnv v i ∈ e a := by
    simpa [tupleEnv,show i < n by omega] using hv ⟨i,by omega⟩
  have hlookup (i : ℕ) (h : i < p.bound) (y : ZFSet.{u}) (_hy : y ∈ e a) :
      ZFSet.pair (e (idx i)) y ∈ e g ↔ y = tupleEnv v i := by
    rw [hg,hi i h]
    simpa [tupleEnv,show i < n by omega] using tupleGraph_pair v ⟨i,by omega⟩ y
  rw [graphTruth,readGraph_eval p.bound a g idx _ e (tupleEnv v) hw hlookup,setBounded_eval,
    prependValues_tail]
  exact p.finite_support _ _ _ (fun i h => prependValues_lt _ _ _ i h)

end TuringRigidity.RelativeConstructible

end OAI
