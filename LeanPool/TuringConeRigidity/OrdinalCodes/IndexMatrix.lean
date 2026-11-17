/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/IndexMatrix.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.TableIndices
public import LeanPool.TuringConeRigidity.Representation.CommonIdealSearch

/-!
# Index Matrix
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IndexMatrix
open Encodable UniformOracle CommonIdeal TableIndices

/-- Decode a partial-recursive machine code, using the zero program for an invalid code. -/
def machine (e : ℕ) : Nat.Partrec.Code := (decode e).getD .zero

theorem machine_primrec : Primrec machine :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const Nat.Partrec.Code.zero)

@[simp] theorem machine_encode (d : Nat.Partrec.Code) : machine (encode d) = d := by
  simp [machine]

theorem run_uniform_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (encode (run Y (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let e := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let n := Primrec.fst.comp (Primrec.unpair.comp rest)
  let z := Primrec.snd.comp (Primrec.unpair.comp rest)
  have he := total_primrec (O := O) e
  have hn := total_primrec (O := O) n
  have hm := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp z))
  have ht := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp z))
  have hL := total_comp (prefix_recursive (fun k => bit (Y k))) hm
  let r := Primrec.snd.comp Primrec.unpair
  have hdecode := total_primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair
      (machine_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp r)))).pair
      (Primrec.snd.comp (Primrec.unpair.comp r)))))
  exact (total_comp hdecode (total_pair ht (total_pair he (total_pair hL hn)))).of_eq
    (fun v => by simp [TableIndices.run, trial])

/-- A challenge-response matrix for total Boolean output and agreement of trial values. -/
def validMatrix (Y : Oracle) (e q r : ℕ) : Prop :=
  run Y (machine e) (Nat.unpair q).1 (Nat.unpair r).1 =
      some (bit (Nat.unpair r).2.bodd) ∧
    let a := run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).1
    let b := run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).2
    a = none ∨ b = none ∨ a = b

instance (Y : Oracle) (e q r : ℕ) : Decidable (validMatrix Y e q r) := by
  unfold validMatrix
  infer_instance

theorem valid_normal_form (Y : Oracle) (e : ℕ) :
    Valid Y (machine e) ↔ ∀ q, ∃ r, validMatrix Y e q r := by
  constructor
  · rintro ⟨ht, hc⟩ q
    obtain ⟨z, b, hb⟩ := ht (Nat.unpair q).1
    refine ⟨Nat.pair z (if b then 1 else 0), ?_, ?_⟩
    · cases b <;> simpa [Nat.unpair_pair] using hb
    · dsimp only
      cases ha : run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).1 with
      | none => exact Or.inl rfl
      | some a =>
        cases hb : run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).2 with
        | none => exact Or.inr (Or.inl rfl)
        | some b => exact Or.inr (Or.inr (congrArg some
            (hc _ _ _ _ _ (Option.mem_def.mpr ha) (Option.mem_def.mpr hb))))
  · intro h
    constructor
    · intro n
      obtain ⟨r, hr, _⟩ := h (Nat.pair n (Nat.pair 0 0))
      exact ⟨(Nat.unpair r).1, (Nat.unpair r).2.bodd, by simpa using hr⟩
    · intro n z w a b ha hb
      obtain ⟨r, _, hc⟩ := h (Nat.pair n (Nat.pair z w))
      simp only [Nat.unpair_pair] at hc
      rcases hc with hc | hc | hc
      · rw [hc] at ha; simp at ha
      · rw [hc] at hb; simp at hb
      · rw [Option.mem_def.mp ha, Option.mem_def.mp hb] at hc
        exact Option.some.inj hc

/-- Decide the coded Boolean-output and trial-agreement checks as a natural-number Boolean. -/
def checkMatrix (v : ℕ) : ℕ :=
  let wanted := (Nat.unpair v).1
  let s := (decode (α := Option ℕ) (Nat.unpair (Nat.unpair v).2).1).getD none
  let a := (decode (α := Option ℕ) (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1).getD none
  let b := (decode (α := Option ℕ) (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).getD none
  if s = some (bit wanted.bodd) ∧ (a = none ∨ b = none ∨ a = b) then 1 else 0

theorem checkMatrix_primrec : Primrec checkMatrix := by
  let first := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let dec : Primrec (fun v : ℕ => (decode (α := Option ℕ) v).getD none) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const none)
  let s := dec.comp (first.comp rest)
  let a := dec.comp (first.comp (rest.comp rest))
  let b := dec.comp (rest.comp (rest.comp rest))
  let want := Primrec.option_some.comp (bit_primrec.comp (Primrec.nat_bodd.comp first))
  exact Primrec.ite ((Primrec.eq.comp s want).and
    (((Primrec.eq.comp a (Primrec.const none)).or (Primrec.eq.comp b (Primrec.const none))).or
      (Primrec.eq.comp a b))) (Primrec.const 1) (Primrec.const 0) |>.of_eq (fun v => by
        simp only [checkMatrix, or_assoc])

theorem validMatrix_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (if validMatrix Y (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair v).2).2 then 1 else 0)) := by
  classical
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  let e := fst
  let q := fst.comp snd
  let r := snd.comp snd
  let n := fst.comp q
  have mk : ∀ (f : ℕ → ℕ), Primrec f → Nat.RecursiveIn O
      (fun v => Part.some (encode (run Y (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).1 (f v)))) := by
    intro f hf
    have hin := total_pair (O := O) (total_primrec e) (total_pair (total_primrec n) (total_primrec
      hf))
    exact (total_comp (run_uniform_recursive Y) hin).of_eq (fun v => by simp)
  have hs := mk _ (fst.comp r)
  have ha := mk _ (fst.comp (snd.comp q))
  have hb := mk _ (snd.comp (snd.comp q))
  exact (total_comp (total_primrec checkMatrix_primrec)
    (total_pair (total_primrec (snd.comp r)) (total_pair hs (total_pair ha hb)))).of_eq (fun v => by
      simp [checkMatrix, validMatrix])

end TuringRigidity.IndexMatrix

end OAI
