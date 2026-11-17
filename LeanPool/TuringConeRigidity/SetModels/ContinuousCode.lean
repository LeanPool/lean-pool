/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ContinuousCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformPrograms
public import LeanPool.TuringConeRigidity.Representation.GenericTopology

/-!
# Continuous Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ContinuousCode
open UniformPrograms UniformOracle BinarySeries FiniteShuffle GenericTopology Set Encodable

theorem table_agreement {A B : Oracle} {n : ℕ}
    (h : oraclePrefix (bit A) n = oraclePrefix (bit B) n) : Agree n A B := by
  intro i hi
  have hh := congrArg (fun L : List ℕ => L.getD i 0) h
  have hb : bit A i = bit B i := by simpa [oraclePrefix,List.getD,hi] using hh
  cases ha : A i <;> cases hb' : B i <;> simp_all [bit]

def LocalAnswer (U : Set Oracle) (f : Oracle → Oracle) (n : ℕ) (L : List ℕ) (a : ℕ) : Prop :=
  ∀ A ∈ U, oraclePrefix (bit A) L.length = L → bit (f A) n = a

noncomputable def parameter (U : Set Oracle) (f : Oracle → Oracle) : Oracle := by
  classical
  exact fun k => decide (LocalAnswer U f (Nat.unpair k).1
    ((decode (α := List ℕ) (Nat.unpair (Nat.unpair k).2).1).getD [])
    (Nat.unpair (Nat.unpair k).2).2)

def queryIndex (A : Oracle) (n k : ℕ) : ℕ :=
  Nat.pair n (Nat.pair (encode (oraclePrefix (bit A) (Nat.unpair k).1)) (Nat.unpair k).2)

def trial (A P : Oracle) (n k : ℕ) : Option ℕ :=
  if P (queryIndex A n k) then some (Nat.unpair k).2 else none

theorem trial_sound (U : Set Oracle) (f : Oracle → Oracle) (A : Oracle) (hA : A ∈ U)
    (n k a : ℕ) (ha : a ∈ trial A (parameter U f) n k) : a = bit (f A) n := by
  unfold trial at ha
  split at ha
  · rename_i hp
    have hval : a = (Nat.unpair k).2 := by symm; simpa using ha
    have hl : LocalAnswer U f n (oraclePrefix (bit A) (Nat.unpair k).1) (Nat.unpair k).2 := by
      simp only [parameter, decide_eq_true_eq] at hp
      simpa [queryIndex] using hp
    have hs := hl A hA (by simp [oraclePrefix])
    exact hval.trans hs.symm
  · simp at ha

private def choiceValue (z : ℕ × ℕ) : Option ℕ := if z.1=1 then some z.2 else none
private theorem choiceValue_primrec : Primrec choiceValue :=
  Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.const 1)))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

theorem trial_program (P : Oracle) :
    Runs (fun A : Oracle => oracleFunction (join A P))
      (fun A z => Part.some (encode (trial A P (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Oracle → ℕ →. ℕ := fun A => oracleFunction (join A P)
  have hO : Runs O (fun A n => Part.some (bit (join A P) n)) := query
  have hA : Runs O (fun A n => Part.some (bit A n)) :=
    (UniformPrograms.total_comp hO (primrec (Primrec.nat_mul.comp (Primrec.const 2)
      Primrec.id))).of_eq
      (fun A n => by simp [bit])
  have hP : Runs O (fun _ n => Part.some (bit P n)) :=
    (UniformPrograms.total_comp hO (primrec (Primrec.succ.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))).of_eq
      (fun A n => by simp [bit])
  have hn := primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hm := primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have ha := primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hL := UniformPrograms.total_comp (initial_program (fun A => bit A) hA) hm
  have hq := UniformPrograms.total_pair hn (UniformPrograms.total_pair hL ha)
  have hb := UniformPrograms.total_comp hP hq
  have hd := primrec (O := O) (Primrec.encode.comp (choiceValue_primrec.comp Primrec.unpair))
  exact (UniformPrograms.total_comp hd (UniformPrograms.total_pair hb ha)).of_eq (fun A z => by
    cases hp : P (queryIndex A (Nat.unpair z).1 (Nat.unpair z).2) <;>
      simp [trial,choiceValue,queryIndex,bit] at hp ⊢ <;> rfl)

theorem local_answer_exists (U : Set Oracle) (f : Oracle → Oracle) (hf : ContinuousOn f U)
    (A : Oracle) (hA : A ∈ U) (n : ℕ) :
    ∃ m, LocalAnswer U f n (oraclePrefix (bit A) m) (bit (f A) n) := by
  have hc : ContinuousWithinAt (fun B => f B n) U A :=
    (continuous_apply n).continuousAt.comp_continuousWithinAt (hf A hA)
  have hp : {B | f B n = f A n} ∈ nhdsWithin A U :=
    hc ((isOpen_discrete ({f A n} : Set Bool)).mem_nhds (by simp))
  obtain ⟨V,hV,hAV,hsub⟩ := mem_nhdsWithin.mp hp
  obtain ⟨m,hm⟩ := cylinder_basis V hV A hAV
  refine ⟨m,?_⟩
  intro B hB htable
  have ht : oraclePrefix (bit B) m = oraclePrefix (bit A) m := by
    simpa only [oraclePrefix,List.length_map,List.length_range] using htable
  have he : f B n = f A n := hsub ⟨hm B (table_agreement ht).symm,hB⟩
  simp [bit,he]

theorem trial_complete (U : Set Oracle) (f : Oracle → Oracle) (hf : ContinuousOn f U)
    (A : Oracle) (hA : A ∈ U) (n : ℕ) :
    ∃ k a, a ∈ trial A (parameter U f) n k := by
  obtain ⟨m,hm⟩ := local_answer_exists U f hf A hA n
  refine ⟨Nat.pair m (bit (f A) n),bit (f A) n,?_⟩
  have hp : parameter U f (queryIndex A n (Nat.pair m (bit (f A) n))) = true := by
    simp only [parameter, decide_eq_true_eq]
    simpa [queryIndex] using hm
  simp [trial,hp]

theorem continuous_uniform_program (U : Set Oracle) (f : Oracle → Oracle) (hf : ContinuousOn f U) :
    ∃ P : Oracle, ∃ p : OracleCode, ∀ A ∈ U,
      OracleCode.eval (oracleFunction (join A P)) p = oracleFunction (f A) := by
  let P := parameter U f
  let O : U → ℕ →. ℕ := fun A => oracleFunction (join A.val P)
  have he : Runs O (fun A z => Part.some (encode (trial A.val P (Nat.unpair z).1 (Nat.unpair
    z).2))) := by
    obtain ⟨p,hp⟩ := trial_program P
    exact ⟨p,fun A => hp A.val⟩
  obtain ⟨p,hp⟩ := UniformPrograms.total_search he (fun A => bit (f A.val))
    (fun A => trial_sound U f A.val A.property)
    (fun A => trial_complete U f hf A.val A.property)
  exact ⟨P,p,fun A hA => hp ⟨A,hA⟩⟩

end TuringRigidity.ContinuousCode

end OAI
