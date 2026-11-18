/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformCohenIteration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformCohenJump
public import LeanPool.TuringConeRigidity.Effective.UniformJumpSimulation

/-!
# Uniform Cohen Iteration
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.UniformCohenJump
open UniformPrograms OracleJump EffectiveCohen

theorem iterate_join_program (Y : Oracle) (k : ℕ) :
    ∃ p : OracleCode, ∀ G : Oracle, (∀ j < k, OneGeneric (iterate Y j) G) →
      OracleCode.eval (oracleFunction (join (iterate Y k) G)) p =
        oracleFunction (iterate (join Y G) k) := by
  induction k with
  | zero => exact ⟨.query,fun _ _ => rfl⟩
  | succ k ih =>
    let X := {G : Oracle // ∀ j < k+1, OneGeneric (iterate Y j) G}
    obtain ⟨p,hp⟩ := ih
    have hprev : Runs (fun G : X => oracleFunction (join (iterate Y k) G.val))
        (fun G => oracleFunction (iterate (join Y G.val) k)) :=
      ⟨p,fun G => hp G.val (fun j hj => G.property j (Nat.lt_succ_of_lt hj))⟩
    obtain ⟨q,hq⟩ := oneGeneric_jump_program (iterate Y k)
    have hstep : Runs (fun G : X => oracleFunction (join (iterate Y (k+1)) G.val))
        (fun G => oracleFunction (jump (join (iterate Y k) G.val))) :=
      ⟨q,fun G => hq G.val (G.property k (Nat.lt_succ_self k))⟩
    obtain ⟨r,hr⟩ := hstep.trans hprev.jump
    exact ⟨r,fun G hG => hr ⟨G,hG⟩⟩

theorem swap_program {X : Type*} (A B : X → Oracle) :
    Runs (fun x => oracleFunction (join (A x) (B x)))
      (fun x => oracleFunction (join (B x) (A x))) := by
  have hq := @query X (fun x => oracleFunction (join (A x) (B x)))
  have hs := primrec (O := fun x => oracleFunction (join (A x) (B x)))
    (Primrec.ite (Primrec.eq.comp Primrec.nat_bodd (Primrec.const true))
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)) Primrec.succ)
  apply (hq.comp hs).of_eq
  intro x n
  change (Part.some (if n.bodd = true then n - 1 else n.succ)).bind
    (fun index => oracleFunction (join (A x) (B x)) index) = _
  rw [Part.bind_some]
  rcases Nat.mod_two_eq_zero_or_one n with hn|hn
  · have hform : n = 2*(n/2) := by omega
    conv_lhs => rw [hform]
    conv_rhs => rw [hform]
    simp [oracleFunction,join,Nat.add_div]
  · have hform : n = 2*(n/2)+1 := by omega
    conv_lhs => rw [hform]
    conv_rhs => rw [hform]
    simp [oracleFunction,join,Nat.add_div]

theorem iterate_generic_join_program (Y : Oracle) (k : ℕ) :
    ∃ p : OracleCode, ∀ G : Oracle, (∀ j < k, OneGeneric (iterate Y j) G) →
      OracleCode.eval (oracleFunction (join G (iterate Y k))) p =
        oracleFunction (iterate (join G Y) k) := by
  let X := {G : Oracle // ∀ j < k, OneGeneric (iterate Y j) G}
  obtain ⟨p,hp⟩ := iterate_join_program Y k
  have hi : Runs (fun G : X => oracleFunction (join (iterate Y k) G.val))
      (fun G => oracleFunction (iterate (join Y G.val) k)) :=
    ⟨p,fun G => hp G.val G.property⟩
  have hfirst := swap_program (fun G : X => G.val) (fun _ => iterate Y k)
  have hlast := (swap_program (fun _ : X => Y) (fun G => G.val)).iterate_jump k
  obtain ⟨q,hq⟩ := (hfirst.trans hi).trans hlast
  exact ⟨q,fun G hG => hq ⟨G,hG⟩⟩

end TuringRigidity.UniformCohenJump

end OAI
