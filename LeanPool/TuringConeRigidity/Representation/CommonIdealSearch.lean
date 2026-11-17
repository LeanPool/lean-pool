/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CommonIdealSearch.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CommonIdeal

/-!
# Common Ideal Search
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CommonIdeal
open Encodable Computable UniformOracle

theorem bit_primrec : Primrec bit := by
  apply (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq
  intro b
  cases b <;> rfl

theorem table_partrec : Partrec₂ table :=
  BranchMachine.lookup_partrec.comp
    ((Primrec.list_map Primrec.id (bit_primrec.comp Primrec.snd).to₂).to_comp.comp fst) snd

def finiteRun (p : OracleCode) (s : List Bool) (L : List ℕ) (w : ℕ) : Part ℕ :=
  OracleCode.eval (partialJoin (BranchMachine.lookup L)
    (table (s ++ BorelGeneric.word (Nat.unpair w).1))) p (Nat.unpair w).2

theorem finiteRun_partrec (p : OracleCode) (s : List Bool) : Partrec₂ (finiteRun p s) := by
  let α := List ℕ × ℕ
  have hword : Computable (fun z : α => s ++ BorelGeneric.word (Nat.unpair z.2).1) :=
    (Primrec.list_append.comp (Primrec.const s)
      (Primrec.option_getD_default.comp (Primrec.decode.comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))).to_comp
  have hA : Partrec₂ (fun z : α => BranchMachine.lookup z.1) :=
    BranchMachine.lookup_partrec.comp (fst.comp fst) snd
  have hG : Partrec₂ (fun z : α => table (s ++ BorelGeneric.word (Nat.unpair z.2).1)) :=
    table_partrec.comp (hword.comp fst) snd
  exact (OracleCode.eval_partrec (BranchMachine.partialJoin_partrec hA hG) p).comp
    Computable.id (snd.comp (Computable.unpair.comp snd))

theorem finiteRun_code (p : OracleCode) (s : List Bool) :
    ∃ d : Nat.Partrec.Code, ∀ L w, d.eval (Nat.pair (encode L) w) = finiteRun p s L w := by
  obtain ⟨d,hd⟩ := partrec_code (finiteRun_partrec p s)
  exact ⟨d,fun L w => hd (L,w)⟩

theorem finiteRun_approximates (A : Oracle) (p : OracleCode) (s : List Bool) (w n : ℕ) :
    Approximates (run A p (s ++ BorelGeneric.word w) n)
      (fun m => finiteRun p s (oraclePrefix (fun k => bit (A k)) m) (Nat.pair w n)) := by
  simp only [finiteRun,Nat.unpair_pair]
  apply OracleCode.eval_approximates
  intro k
  apply BranchMachine.partialJoin_approximates
  · exact prefix_approximates (fun k => bit (A k))
  · intro k; exact Approximates.const _

def searchTrial (A : Oracle) (d : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  d.evaln (Nat.unpair (Nat.unpair z).2).2
    (Nat.pair (encode (oraclePrefix (fun k => bit (A k)) (Nat.unpair z).1))
      (Nat.pair (Nat.unpair (Nat.unpair z).2).1 n))

theorem searchTrial_recursive (A : Oracle) (d : Nat.Partrec.Code) :
    Nat.RecursiveIn {oracleFunction A}
      (fun z => Part.some (encode (searchTrial A d (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction A}
  have hn := total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hz := Primrec.snd.comp Primrec.unpair
  have hm := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp hz))
  have hw := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp hz))))
  have hk := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp hz))))
  have hL := total_comp (prefix_recursive (fun k => bit (A k))) hm
  have he := total_primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair (Primrec.const d)).pair
      (Primrec.snd.comp Primrec.unpair))))
  exact (total_comp he (total_pair hk (total_pair hL (total_pair hw hn)))).of_eq (fun z => by
    simp [searchTrial])

theorem common_output_reduces {A G H Y : Oracle} {p q : OracleCode} {s t : List Bool}
    (hs : Extends G s) (ht : Extends H t) (hR : Requirement A p q s t)
    (hp : OracleCode.eval (oracleFunction (join A G)) p = oracleFunction Y)
    (hq : OracleCode.eval (oracleFunction (join A H)) q = oracleFunction Y) :
    Reduces Y A := by
  have hag := agree_of_common_output hs ht hR hp hq
  obtain ⟨d,hd⟩ := finiteRun_code p s
  apply RecursiveIn.iff_nat.mpr
  apply total_search (searchTrial_recursive A d) (fun n => bit (Y n))
  · intro n z a ha
    have hfinite := Nat.Partrec.Code.evaln_sound ha
    rw [hd] at hfinite
    have hactual := (finiteRun_approximates A p s
      (Nat.unpair (Nat.unpair z).2).1 n).1 (Nat.unpair z).1 a hfinite
    exact agreeing_search_sound ht hag hq _ n a hactual
  · intro n
    obtain ⟨w,a,ha⟩ := agreeing_search_complete hs hp n
    obtain ⟨wcode,hw⟩ := BorelGeneric.word_surjective w
    rw [←hw] at ha
    obtain ⟨m,hm⟩ := (finiteRun_approximates A p s wcode n).2 a ha
    have hfinite := hm m le_rfl
    dsimp only at hfinite
    rw [←hd] at hfinite
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp hfinite
    exact ⟨Nat.pair m (Nat.pair wcode k),a,by simpa [searchTrial] using hk⟩

theorem ideal_of_meets (A G H : Oracle)
    (h : ∀ p q : OracleCode, ∃ s t, Extends G s ∧ Extends H t ∧ Requirement A p q s t) :
    ∀ b : Degree, b ≤ degree A ↔ b ≤ degree (join A G) ∧ b ≤ degree (join A H) := by
  intro b
  obtain ⟨Y,rfl⟩ := degree_surjective b
  constructor
  · intro hY
    exact ⟨reduces_trans hY (reduces_join_left A G),reduces_trans hY (reduces_join_left A H)⟩
  · rintro ⟨hG,hH⟩
    obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hG
    obtain ⟨q,hq⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hH
    obtain ⟨s,t,hs,ht,hR⟩ := h p q
    exact common_output_reduces hs ht hR hp hq

end TuringRigidity.CommonIdeal

end OAI
