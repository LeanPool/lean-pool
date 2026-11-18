/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeCohenJump.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenLowness

/-!
# Relative Cohen Jump
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeCohenJump
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenHalting EffectiveCohen EffectiveWitness CohenLowness

theorem deciding_recursive_join (Y G : Oracle) :
    RecursivePred (join (jump Y) G) (Deciding Y G) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := recursive_comp (recursive_transfer (CohenLowness.prefix_recursive G)
    (reduces_join_right (jump Y) G)) r
  have hh := recursive_comp (recursive_transfer (form_recursive (openHalts_sigma Y))
    (reduces_join_left (jump Y) G))
    (Primrec₂.natPair.comp f (Primrec.encode.comp (word_primrec.comp r)))
  have hn := recursive_not (recursive_transfer (form_recursive (extension_sigma Y))
    (reduces_join_left (jump Y) G))
  unfold Deciding
  simpa only [Nat.unpair_pair] using recursive_and hp (Form.or (n := 0) (s := true) hh hn)

theorem oneGeneric_jump_reduces {Y G : Oracle} (hgen : OneGeneric Y G) :
    Reduces (jump (join Y G)) (join (jump Y) G) := by
  let D := Deciding Y G
  let ht := deciding_total hgen
  let pick : ℕ → ℕ := least D ht
  have hpick : Nat.RecursiveIn {oracleFunction (join (jump Y) G)} (fun x => Part.some (pick x)) :=
    least_recursive (deciding_recursive_join Y G) ht
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hin := total_pair (total_primrec Primrec.id)
    (total_comp (total_primrec (Primrec.encode.comp word_primrec)) hpick)
  have hh := recursive_comp_total (recursive_transfer (form_recursive (openHalts_sigma Y))
    (reduces_join_left (jump Y) G)) hin
  apply RecursiveIn.iff_nat.mpr
  apply hh.of_eq
  intro x
  have he := deciding_correct (least_spec D ht x)
  classical
  simp only [Nat.unpair_pair]
  change Part.some (if OpenHalts Y x (encode (word (pick x))) then 1 else 0) = _
  simp only [pick,he,oracleFunction,jump,Bool.decide_iff]

theorem oneGeneric_jump_degree (Y G : Oracle) (hgen : OneGeneric Y G) :
    degree (jump (join Y G)) = degree (join (jump Y) G) := by
  apply (degree_eq_iff _ _).mpr
  exact ⟨oneGeneric_jump_reduces hgen,join_reduces
    (jump_mono (reduces_join_left Y G))
    (reduces_trans (reduces_join_right Y G) (reduces_jump (join Y G)))⟩

theorem iterate_join_degree (Y G : Oracle) (k : ℕ)
    (hgen : ∀ j < k, OneGeneric (iterate Y j) G) :
    degree (iterate (join Y G) k) = degree (join (iterate Y k) G) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := ih (fun j hj => hgen j (Nat.lt_succ_of_lt hj))
    calc
      degree (iterate (join Y G) (k+1)) = degree (jump (join (iterate Y k) G)) :=
        congrArg degreeJump hk
      _ = degree (join (iterate Y (k+1)) G) :=
        oneGeneric_jump_degree (iterate Y k) G (hgen k (Nat.lt_succ_self k))

theorem iterate_generic_join_degree (G Y : Oracle) (k : ℕ)
    (hgen : ∀ j < k, OneGeneric (iterate Y j) G) :
    degree (iterate (join G Y) k) = degree (join G (iterate Y k)) := by
  have hswap : degree (join G Y) = degree (join Y G) := sup_comm (degree G) (degree Y)
  obtain ⟨h₁,h₂⟩ := (degree_eq_iff _ _).mp hswap
  calc
    degree (iterate (join G Y) k) = degree (iterate (join Y G) k) :=
      (degree_eq_iff _ _).mpr ⟨iterate_mono h₁ k,iterate_mono h₂ k⟩
    _ = degree (join (iterate Y k) G) := iterate_join_degree Y G k hgen
    _ = degree (join G (iterate Y k)) := sup_comm (degree (iterate Y k)) (degree G)

end TuringRigidity.RelativeCohenJump

end OAI
