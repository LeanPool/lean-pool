/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformCohenJump.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformCohenPrefix
public import LeanPool.TuringConeRigidity.Constructibility.RelativeCohenJump

/-!
# Uniform Cohen Jump
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.UniformCohenJump
open Encodable UniformPrograms CommonIdeal EncodedForcing OracleJump
open ArithmeticHierarchy CohenHalting CohenLowness EffectiveCohen
noncomputable section
attribute [local instance] Classical.propDecidable

def searchTrial (Y G : Oracle) (x p : ℕ) : Option ℕ :=
  if Deciding Y G (Nat.pair x p) then
    some (if OpenHalts Y x (encode (word p)) then 1 else 0) else none

def trialAnswer (v : ℕ) : Option ℕ :=
  if (Nat.unpair v).1 = 1 ∧
      ((Nat.unpair (Nat.unpair v).2).1 = 1 ∨ (Nat.unpair (Nat.unpair v).2).2 = 0)
    then some (Nat.unpair (Nat.unpair v).2).1 else none

theorem trialAnswer_primrec : Primrec trialAnswer := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  exact Primrec.ite ((Primrec.eq.comp f (Primrec.const 1)).and
    ((Primrec.eq.comp (f.comp r) (Primrec.const 1)).or
      (Primrec.eq.comp (r.comp r) (Primrec.const 0))))
    (Primrec.option_some.comp (f.comp r)) (Primrec.const none)

theorem searchTrial_program (Y : Oracle) :
    Runs (fun G => oracleFunction (join (jump Y) G))
      (fun G v => Part.some (encode (searchTrial Y G (Nat.unpair v).1 (Nat.unpair v).2))) := by
  let O := fun G => oracleFunction (join (jump Y) G)
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hground : Runs O (fun _ => oracleFunction (jump Y)) := join_left_program (fun _ => jump Y) id
  have hG : Runs O oracleFunction := join_right_program (fun _ => jump Y) id
  have hp := total_comp (UniformCohenPrefix.prefix_program id hG) (primrec r)
  have hhalt := fixed_recursive (form_recursive (openHalts_sigma Y)) hground
  have hh := total_comp hhalt (primrec
    (Primrec₂.natPair.comp f (Primrec.encode.comp (word_primrec.comp r))))
  have he := fixed_recursive (form_recursive (extension_sigma Y)) hground
  have ht := total_comp (primrec (Primrec.encode.comp trialAnswer_primrec))
    (total_pair hp (total_pair hh he))
  apply ht.of_eq
  intro G v
  simp only [Nat.unpair_pair]
  by_cases hp : Prefix G (word (Nat.unpair v).2) <;>
    by_cases hh : OpenHalts Y (Nat.unpair v).1 (encode (word (Nat.unpair v).2)) <;>
    by_cases he : Extension Y (Nat.unpair v).1 (Nat.unpair v).2 <;>
    simp [trialAnswer,searchTrial,Deciding,hp,hh,he]

theorem oneGeneric_jump_program (Y : Oracle) :
    ∃ p : OracleCode, ∀ G : Oracle, OneGeneric Y G →
      OracleCode.eval (oracleFunction (join (jump Y) G)) p =
        oracleFunction (jump (join Y G)) := by
  let X := {G : Oracle // OneGeneric Y G}
  let O := fun G : X => oracleFunction (join (jump Y) G.val)
  let f := fun (G : X) x => if Halts (join Y G.val) (Nat.unpair x).1 (Nat.unpair x).2 then 1 else 0
  have ht : Runs O (fun G v => Part.some
      (encode (searchTrial Y G.val (Nat.unpair v).1 (Nat.unpair v).2))) :=
    (searchTrial_program Y).reindex (fun G : X => G.val)
  have hs (G : X) (x p a : ℕ) (ha : a ∈ searchTrial Y G.val x p) : a = f G x := by
    by_cases hd : Deciding Y G.val (Nat.pair x p)
    · have ha' : a = (if OpenHalts Y x (encode (word p)) then 1 else 0) := by
        exact (by simpa only [searchTrial,ite_eq_left hd,Option.mem_some_iff] using ha :
          (if OpenHalts Y x (encode (word p)) then 1 else 0) = a).symm
      rw [ha',deciding_correct hd]
    · simp [searchTrial,hd] at ha
  have hc (G : X) (x : ℕ) : ∃ p a, a ∈ searchTrial Y G.val x p := by
    obtain ⟨p,hp⟩ := deciding_total G.property x
    exact ⟨p,(if OpenHalts Y x (encode (word p)) then 1 else 0),by
      simp only [searchTrial,ite_eq_left hp,Option.mem_some_iff]⟩
  obtain ⟨p,hp⟩ := total_search ht f hs hc
  refine ⟨p,fun G hG => ?_⟩
  have h := hp (⟨G,hG⟩ : X)
  funext n
  exact (congrFun h n).trans (by simp [f,oracleFunction,jump])

end
end TuringRigidity.UniformCohenJump

end OAI
