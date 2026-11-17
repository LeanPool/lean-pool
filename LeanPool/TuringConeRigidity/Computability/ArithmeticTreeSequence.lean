/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticTreeSequence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTreeDefinability

/-!
# Arithmetic Tree Sequence
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticTree
open UniformArithmetic Encodable
noncomputable section

def Test.codeChild (t : Test) (O : Oracles) (v x y : ℕ) : Prop :=
  t.accepts O v (decodeNode x) ∧ t.accepts O v (decodeNode y) ∧
    ∃ a, decodeNode x = decodeNode y ++ [a]

theorem Test.codeChild_arith (t : Test) (v : ℕ) :
    Arith (fun O k => t.codeChild O v (left k) (right k)) := by
  have hx := t.accepts_arith (decodeNode_primrec.comp left_primrec) (Primrec.const v)
  have hy := t.accepts_arith (decodeNode_primrec.comp right_primrec) (Primrec.const v)
  have he : Arith (fun _ k => decodeNode (left (left k)) = decodeNode (right (left k)) ++ [right
    k]) :=
    .pure _ (Primrec.eq.comp (decodeNode_primrec.comp (left_primrec.comp left_primrec))
      (Primrec.list_append.comp (decodeNode_primrec.comp (right_primrec.comp left_primrec))
        (Primrec.list_cons.comp right_primrec (Primrec.const []))))
  exact (hx.and (hy.and he.ex)).congr (fun _ _ => by
    simp only [Test.codeChild,left,right,Nat.unpair_pair])

def chainValue (s : ℕ → ℕ) (i : ℕ) : ℕ := ((decodeNode (s (i+1)))[i]?).getD 0

theorem code_chain_extends (s : ℕ → ℕ)
    (h : ∀ n, ∃ a, decodeNode (s (n + 1)) = decodeNode (s n) ++ [a])
    {i j : ℕ} (hij : i ≤ j) :
    Extends (listApprox (decodeNode (s i))) (listApprox (decodeNode (s j))) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ h => h
  | succ j hj ih =>
    obtain ⟨a,ha⟩ := h j
    intro k b hb
    rw [ha]
    exact listApprox_append _ _ k b (ih k b hb)

theorem code_chain_length (s : ℕ → ℕ)
    (h : ∀ n, ∃ a, decodeNode (s (n + 1)) = decodeNode (s n) ++ [a]) (n : ℕ) :
    n ≤ (decodeNode (s n)).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨a,ha⟩ := h n
    simp only [ha,List.length_append,List.length_singleton]
    omega

theorem code_chain_captures (s : ℕ → ℕ)
    (h : ∀ n, ∃ a, decodeNode (s (n + 1)) = decodeNode (s n) ++ [a]) (n : ℕ) :
    Captures (listApprox (decodeNode (s n))) (chainValue s) n := by
  intro i hi
  have hil : i < (decodeNode (s (i+1))).length :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (code_chain_length s h _)
  have he : (decodeNode (s (i+1)))[i]? = some (chainValue s i) := by
    simp only [chainValue,List.getElem?_eq_getElem hil,Option.getD_some]
  exact code_chain_extends s h (Nat.succ_le_of_lt hi) i _ he

theorem Test.code_chain_eval (t : Test) (O : Oracles) (v : ℕ) (s : ℕ → ℕ)
    (h : ∀ n, t.codeChild O v (s (n + 1)) (s n)) :
    ∀ n, t.eval O (chainValue s) (Nat.pair v n) := by
  intro n
  have hstep := fun k => (h k).2.2
  obtain ⟨N,hN⟩ := t.approx_complete O (chainValue s) (Nat.pair v n)
  let K := max N (n+1)
  have he := hN (listApprox (decodeNode (s K)))
    ((code_chain_captures s hstep K).mono (le_max_left _ _))
  have hn : n < (decodeNode (s K)).length :=
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
      (code_chain_length s hstep K)
  have hh := (h K).2.1 n hn
  by_contra hp
  exact hh (he.trans (by simp [hp]))

theorem Test.code_chain_exists (t : Test) (O : Oracles) (v : ℕ)
    (h : ∃ f : ℕ → ℕ, ∀ n, t.eval O f (Nat.pair v n)) :
    ∃ s : ℕ → ℕ, ∀ n, t.codeChild O v (s (n+1)) (s n) := by
  obtain ⟨f,hf⟩ := h
  refine ⟨fun n => encode (initialSegment f n),fun n => ?_⟩
  simp only [Test.codeChild,decodeNode_encode]
  exact ⟨(t.branch_iff O v f).mpr hf (n+1),(t.branch_iff O v f).mpr hf n,
    f n,prefix_succ f n⟩

end
end TuringRigidity.ArithmeticTree

end OAI
