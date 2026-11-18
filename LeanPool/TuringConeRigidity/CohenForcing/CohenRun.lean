/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenRun.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.EncodedForcing
public import LeanPool.TuringConeRigidity.Computability.JumpProperties

/-!
# Cohen Run
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenRun
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing CommonIdeal IndexMatrix

theorem form_transfer {Y Z : Oracle} {n s P} (h : Form Y n s P) (hYZ : Reduces Y Z) :
    Form Z n s P := by
  induction n generalizing s P with
  | zero => exact recursive_transfer h hYZ
  | succ n ih =>
    obtain ⟨Q,hQ,he⟩ := h
    exact ⟨Q,ih hQ,he⟩

theorem run_table (A : Oracle) (e : OracleCode) : ∃ d : Nat.Partrec.Code,
    ∀ p n a, a ∈ CommonIdeal.run A e (word p) n ↔
      ∃ z, a ∈ TableIndices.run A d (Nat.pair (encode (word p)) n) z := by
  obtain ⟨d,hd⟩ := finiteRun_code e []
  refine ⟨d,fun p n a => ?_⟩
  have ha := finiteRun_approximates A e [] (encode (word p)) n
  simp only [BorelGeneric.word,encodek,Option.getD_some,List.nil_append] at ha
  constructor
  · intro h
    obtain ⟨m,hm⟩ := ha.2 a h
    have hh := hm m le_rfl
    dsimp only at hh
    rw [← hd] at hh
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp hh
    exact ⟨Nat.pair m t,by simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht⟩
  · rintro ⟨z,hz⟩
    have hh := Nat.Partrec.Code.evaln_sound hz
    rw [hd] at hh
    exact ha.1 (Nat.unpair z).1 a hh

theorem run_mem_sigma (A : Oracle) (e : OracleCode) : Sigma A 1 (fun v =>
    (Nat.unpair (Nat.unpair v).2).2 ∈ CommonIdeal.run A e (word (Nat.unpair v).1)
      (Nat.unpair (Nat.unpair v).2).1) := by
  obtain ⟨d,hd⟩ := run_table A e
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := total_comp (run_uniform_recursive A) (total_primrec
    (Primrec₂.natPair.comp (Primrec.const (encode d))
      (Primrec₂.natPair.comp (Primrec₂.natPair.comp
        (Primrec.encode.comp (word_primrec.comp (f.comp f))) (f.comp (r.comp f))) r)))
  have heq : Primrec (fun v : ℕ => if (decode (α := Option ℕ) (Nat.unpair v).1).getD none =
      some (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.option_getD.comp (Primrec.decode.comp f) (Primrec.const
      none))
      (Primrec.option_some.comp r)) (Primrec.const 1) (Primrec.const 0)
  have hcert : RecursivePred A (fun v => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 ∈
      TableIndices.run A d (Nat.pair (encode (word (Nat.unpair (Nat.unpair v).1).1))
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1) (Nat.unpair v).2) := by
    exact (total_comp (total_primrec heq) (total_pair hr (total_primrec (r.comp (r.comp f))))).of_eq
      (fun v => by simp [Option.mem_def])
  apply Form.congr (exists_form (n := 0) hcert)
  intro v
  simp only [Nat.unpair_pair]
  exact (hd _ _ _).symm

theorem run_dom_sigma (A : Oracle) (e : OracleCode) : Sigma A 1 (fun v =>
    (CommonIdeal.run A e (word (Nat.unpair v).1) (Nat.unpair v).2).Dom) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have h := ((run_mem_sigma A e).comp
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (r.comp f) r))).ex
  apply h.congr
  intro v
  simp only [Nat.unpair_pair]
  exact Part.dom_iff_mem.symm

end TuringRigidity.CohenRun

end OAI
