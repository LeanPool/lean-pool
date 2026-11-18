/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticWitnessTree.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTestApproximation
public import Mathlib.SetTheory.Descriptive.Tree

/-!
# Arithmetic Witness Tree
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Regard a finite list as a partial witness function. -/
abbrev listApprox (s : List ℕ) : Approx := fun i => s[i]?

theorem listApprox_append (s t : List ℕ) : Extends (listApprox s) (listApprox (s ++ t)) := by
  intro i a ha
  obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp ha
  simpa only [listApprox,List.getElem?_append_left hi] using ha

/-- The list of the first `n` values of a witness function. -/
def initialSegment (f : ℕ → ℕ) (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => f i.val)

@[simp] theorem prefix_length (f : ℕ → ℕ) (n : ℕ) : (initialSegment f n).length = n := by
  simp [initialSegment]

theorem prefix_succ (f : ℕ → ℕ) (n : ℕ) : initialSegment f (n+1) = initialSegment f n ++ [f n] := by
  unfold initialSegment
  rw [List.ofFn_succ_last]
  rfl

theorem prefix_captures (f : ℕ → ℕ) (n : ℕ) : Captures (listApprox (initialSegment f n)) f n := by
  intro i hi
  simp [listApprox,initialSegment,hi]

theorem prefix_extends (f : ℕ → ℕ) (n : ℕ) :
    Extends (listApprox (initialSegment f n)) (fun i => some (f i)) := by
  intro i a ha
  obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp ha
  simp only [prefix_length] at hi
  have hb := prefix_captures f n i hi
  exact hb.symm.trans ha

namespace Test

/-- No test indexed below the node length is rejected by the finite witness approximation. -/
def accepts (t : Test) (O : Oracles) (v : ℕ) (s : List ℕ) : Prop :=
  ∀ n < s.length, t.approx O (listApprox s) (Nat.pair v n) ≠ some false

/-- The prefix-closed tree of finite witness approximations not rejected by the arithmetic
test. -/
def tree (t : Test) (O : Oracles) (v : ℕ) : Descriptive.tree ℕ :=
  ⟨{s | t.accepts O v s},by
    intro s a h n hn he
    exact h n (by simp; omega) (t.rejection_mono O (listApprox_append s [a]) _ he)⟩

theorem branch_iff (t : Test) (O : Oracles) (v : ℕ) (f : ℕ → ℕ) :
    (∀ N, initialSegment f N ∈ t.tree O v) ↔ ∀ n, t.eval O f (Nat.pair v n) := by
  constructor
  · intro h n
    obtain ⟨N,hN⟩ := t.approx_complete O f (Nat.pair v n)
    let K := max N (n+1)
    have he := hN (listApprox (initialSegment f K)) ((prefix_captures f K).mono (le_max_left _ _))
    have hn : n < (initialSegment f K).length := by simp [K]
    have hh := h K n hn
    by_contra hp
    exact hh (he.trans (by simp [hp]))
  · intro h N n hn he
    have ha := (t.approx_sound O (prefix_extends f N) _ false he).mp (h n)
    exact Bool.false_ne_true ha

/-- The first accepted node extends the second by one witness value. -/
def Child (t : Test) (O : Oracles) (v : ℕ) (s r : t.tree O v) : Prop :=
  ∃ a, s.val = r.val ++ [a]

private theorem chain_extends (s : ℕ → List ℕ)
    (h : ∀ n, ∃ a, s (n + 1) = s n ++ [a]) {i j : ℕ} (hij : i ≤ j) :
    Extends (listApprox (s i)) (listApprox (s j)) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ h => h
  | succ j hj ih =>
    obtain ⟨a,ha⟩ := h j
    intro k b hb
    rw [ha]
    exact listApprox_append _ _ k b (ih k b hb)

private theorem chain_length (s : ℕ → List ℕ)
    (h : ∀ n, ∃ a, s (n + 1) = s n ++ [a]) (n : ℕ) : n ≤ (s n).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨a,ha⟩ := h n
    simp only [ha,List.length_append,List.length_singleton]
    omega

private theorem chain_union (s : ℕ → List ℕ)
    (h : ∀ n, ∃ a, s (n + 1) = s n ++ [a]) :
    ∃ f : ℕ → ℕ, ∀ n, Captures (listApprox (s n)) f n := by
  have hex : ∀ i, ∃ a, (s (i+1))[i]? = some a := by
    intro i
    have hi : i < (s (i+1)).length := lt_of_lt_of_le (Nat.lt_succ_self _) (chain_length s h _)
    exact ⟨(s (i+1))[i],List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩⟩
  choose f hf using hex
  refine ⟨f,fun n i hi => ?_⟩
  exact chain_extends s h (Nat.succ_le_of_lt hi) i (f i) (hf i)

theorem wellFounded_iff (t : Test) (O : Oracles) (v : ℕ) :
    WellFounded (t.Child O v) ↔ ¬ ∃ f : ℕ → ℕ, ∀ n, t.eval O f (Nat.pair v n) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  · intro hw ⟨f,hf⟩
    let nodes : ℕ → t.tree O v := fun n => ⟨initialSegment f n,(t.branch_iff O v f).mpr hf n⟩
    exact hw.false ⟨nodes,fun n => ⟨f n,prefix_succ f n⟩⟩
  · intro h
    refine ⟨fun ⟨nodes,hn⟩ => ?_⟩
    let s : ℕ → List ℕ := fun n => (nodes n).val
    have hs : ∀ n, ∃ a, s (n+1) = s n ++ [a] := hn
    obtain ⟨f,hf⟩ := chain_union s hs
    apply h
    refine ⟨f,fun n => ?_⟩
    obtain ⟨N,hN⟩ := t.approx_complete O f (Nat.pair v n)
    let K := max N (n+1)
    have he := hN (listApprox (s K)) ((hf K).mono (le_max_left _ _))
    have hnK : n < (s K).length :=
      lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) (chain_length s hs K)
    have hh := (nodes K).property n hnK
    by_contra hp
    exact hh (he.trans (by simp [hp]))
end Test

end
end TuringRigidity.ArithmeticTree

end OAI
