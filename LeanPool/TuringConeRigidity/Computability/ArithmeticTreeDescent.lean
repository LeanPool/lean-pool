/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticTreeDescent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelTreeRelations
public import LeanPool.TuringConeRigidity.Constructibility.PersistenceWitnessTree

/-!
# Arithmetic Tree Descent
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic SetModelReals SetModelSyntax SetModelFunctions
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Read coordinate `i` from the decoded node at stage `i + 1` of a chain. -/
def unionRead (c : ℕ → ℕ) (i : ℕ) : ℕ := (decodeNode (c (i+1)))[i]?.getD 0

private theorem length_chain (c : ℕ → ℕ)
    (hs : ∀ n, ∃ a, decodeNode (c (n + 1)) = decodeNode (c n) ++ [a]) (n : ℕ) :
    n ≤ (decodeNode (c n)).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨a,ha⟩ := hs n
    simp only [ha,List.length_append,List.length_singleton]
    omega

private theorem extends_chain (c : ℕ → ℕ)
    (hs : ∀ n, ∃ a, decodeNode (c (n + 1)) = decodeNode (c n) ++ [a])
    {i j : ℕ} (hij : i ≤ j) : Extends (listApprox (decodeNode (c i))) (listApprox (decodeNode (c
      j))) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ h => h
  | succ j hj ih =>
    obtain ⟨a,ha⟩ := hs j
    intro k b hb
    rw [ha]
    exact listApprox_append _ _ k b (ih k b hb)

theorem unionRead_captures (c : ℕ → ℕ)
    (hs : ∀ n, ∃ a, decodeNode (c (n + 1)) = decodeNode (c n) ++ [a]) (n : ℕ) :
    Captures (listApprox (decodeNode (c n))) (unionRead c) n := by
  intro i hi
  have hil : i < (decodeNode (c (i+1))).length :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (length_chain c hs _)
  have he : (decodeNode (c (i+1)))[i]? = some ((decodeNode (c (i+1)))[i]) :=
    List.getElem?_eq_some_iff.mpr ⟨hil,rfl⟩
  have hv : unionRead c i = (decodeNode (c (i+1)))[i] := by simp [unionRead,he]
  rw [hv]
  exact extends_chain c hs (Nat.succ_le_of_lt hi) i _ he

theorem Test.eval_of_descent (t : Test) (O : Oracles) (v : ℕ) (c : ℕ → ℕ)
    (hc : ∀ n, t.edgePredicate O v (c (n + 1)) (c n)) :
    ∀ n, t.eval O (unionRead c) (Nat.pair v n) := by
  have hs : ∀ n, ∃ a, decodeNode (c (n+1)) = decodeNode (c n) ++ [a] := fun n => (hc n).2.2
  intro n
  obtain ⟨N,hN⟩ := t.approx_complete O (unionRead c) (Nat.pair v n)
  let K := max N (n+1)
  have he := hN (listApprox (decodeNode (c K))) ((unionRead_captures c hs K).mono (le_max_left _ _))
  have hnK : n < (decodeNode (c K)).length :=
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) (length_chain c hs K)
  have hh := (hc K).2.1.2 n hnK
  by_contra hp
  exact hh (he.trans (by simp [hp]))

private theorem read_primrec : Primrec (fun p : ℕ × ℕ => (decodeNode p.1)[p.2]?.getD 0) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (decodeNode_primrec.comp Primrec.fst)
    Primrec.snd)
    (Primrec.const 0)

theorem union_real_mem {M : ZFSet.{u}} (C : Context M) (G : Oracle) (hG : G ∈ reals M)
    (c : ℕ → ℕ) (hc : ∀ n k, G (Nat.pair n k) = true ↔ k = c n) :
    Test.realPart (unionRead c) ∈ reals M := by
  let idx : ℕ → ℕ := fun n => Nat.pair 0 n
  have hi : Primrec idx := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id
  have hq := (Arith.query 0).comp
    (fun n => Nat.pair (idx (left n)+1) (right n))
    (Primrec₂.natPair.comp (Primrec.succ.comp (hi.comp left_primrec)) right_primrec)
  have hr : Arith (fun _ n => (decodeNode (right n))[idx (left n)]?.getD 0 = 1) :=
    .pure _ (Primrec.eq.comp (read_primrec.comp (right_primrec.pair (hi.comp left_primrec)))
      (Primrec.const 1))
  apply arithmetic_comprehension C (hq.and hr).ex (fun _ => G) (fun _ => hG) _
  intro n
  simp only [left,right,Nat.unpair_pair]
  change (∃ k, G (Nat.pair (idx n + 1) k) = true ∧ (decodeNode k)[idx n]?.getD 0 = 1) ↔ _
  simp only [hc,exists_eq_left,Test.realPart,unionRead,idx]
  exact ⟨decide_eq_true,of_decide_eq_true⟩

end
end TuringRigidity.ArithmeticTree

end OAI
