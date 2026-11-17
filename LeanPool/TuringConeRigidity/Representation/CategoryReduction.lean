/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CategoryReduction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CategoryMachine

/-!
# Category Reduction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CategorySearch
open Encodable Set

def trialInput (z : ℕ) : ℕ :=
  let n := (Nat.unpair z).1
  let s := (Nat.unpair z).2
  let i := (Nat.unpair s).1
  let j := (Nat.unpair (Nat.unpair s).2).1
  let t := (Nat.unpair (Nat.unpair s).2).2
  Nat.pair (Nat.pair i (Nat.pair j n)) t

theorem trialInput_primrec : Primrec trialInput := by
  have hn := Primrec.fst.comp Primrec.unpair
  have hs := Primrec.snd.comp Primrec.unpair
  have hi := Primrec.fst.comp (Primrec.unpair.comp hs)
  have hj := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hs)))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hs)))
  exact Primrec₂.natPair.comp (Primrec₂.natPair.comp hi (Primrec₂.natPair.comp hj hn)) ht

noncomputable def searchTrial (A : Oracle) (d : Nat.Partrec.Code) (n s : ℕ) : Option ℕ :=
  UniformOracle.trial (Avalue A) d
    (Nat.unpair (trialInput (Nat.pair n s))).1
    (Nat.unpair (trialInput (Nat.pair n s))).2

theorem searchTrial_recursive (A : Oracle) (d : Nat.Partrec.Code) :
    Nat.RecursiveIn {oracleFunction A}
      (fun z => Part.some (encode (searchTrial A d (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have h := UniformOracle.total_comp (UniformOracle.trial_recursive (Avalue A) d)
    (UniformOracle.total_primrec trialInput_primrec)
  have hO : (fun n => Part.some (Avalue A n)) = oracleFunction A := rfl
  rw [hO] at h
  exact h.of_eq (fun z => by simp only [searchTrial,Nat.pair_unpair])

theorem searchTrial_pair (A : Oracle) (d : Nat.Partrec.Code) (n i j m k : ℕ) :
    searchTrial A d n (Nat.pair i (Nat.pair j (Nat.pair m k))) =
      d.evaln k (Nat.pair (encode (UniformOracle.oraclePrefix (Avalue A) m))
        (Nat.pair i (Nat.pair j n))) := by
  simp [searchTrial,trialInput,UniformOracle.trial]

theorem reduces_of_dense (A Y : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (hne : (rectangle l r).Nonempty)
    (hd : rectangle l r ⊆ closure (success A Y c)) : Reduces Y A := by
  obtain ⟨d,hdcode⟩ := finiteRun_code c l r
  apply RecursiveIn.iff_nat.mpr
  apply UniformOracle.total_search (searchTrial_recursive A d) (Avalue Y)
  · intro n s a ha
    have hs := Nat.pair_unpair s
    generalize hi : (Nat.unpair s).1 = i at *
    generalize ht : (Nat.unpair s).2 = t at *
    subst s
    have ht := Nat.pair_unpair t
    generalize hj : (Nat.unpair t).1 = j at *
    generalize hu : (Nat.unpair t).2 = u at *
    subst t
    have hu := Nat.pair_unpair u
    generalize hm : (Nat.unpair u).1 = m at *
    generalize hk : (Nat.unpair u).2 = k at *
    subst u
    rw [searchTrial_pair] at ha
    have hrun := Nat.Partrec.Code.evaln_sound ha
    rw [hdcode] at hrun
    simp only [finiteRun,Nat.unpair_pair] at hrun
    split at hrun
    next hin =>
      exact dense_sound A Y c l r hd (sample i j) ((inside_iff l r i j).mp hin) n a
        ((OracleCode.eval_approximates (finiteOracle_approximates A i j) c n).1 m a hrun)
    next => simp at hrun
  · intro n
    obtain ⟨p,hp⟩ := hne
    obtain ⟨z,hzR,hzS⟩ := mem_closure_iff.mp (hd hp) (rectangle l r)
      (isOpen_Ioo.prod isOpen_Ioo) hp
    have hz : Avalue Y n ∈ OracleCode.eval (oracleFunction (pairOracle A z)) c n := by
      rw [hzS]
      exact Part.mem_some _
    obtain ⟨q,hqR,hq⟩ := rational_halting A c l r z hzR n (Avalue Y n) hz
    let i := encode q.1
    let j := encode q.2
    have hs : sample i j = ((q.1 : ℝ),(q.2 : ℝ)) := by simp [sample,i,j,rationalEnumeration]
    have hin : inside l r i j := (inside_iff l r i j).mpr (hs.symm ▸ hqR)
    rw [← hs] at hq
    obtain ⟨m,hm⟩ := (OracleCode.eval_approximates (finiteOracle_approximates A i j) c n).2
      (Avalue Y n) hq
    have hf : Avalue Y n ∈ d.eval (Nat.pair (encode (UniformOracle.oraclePrefix (Avalue A) m))
        (Nat.pair i (Nat.pair j n))) := by
      rw [hdcode]
      simpa [finiteRun,hin] using hm m le_rfl
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp hf
    exact ⟨Nat.pair i (Nat.pair j (Nat.pair m k)), Avalue Y n,by rwa [searchTrial_pair]⟩

theorem source_irrational_dense_reduces (A Y : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (hne : (rectangle l r).Nonempty)
    (hd : rectangle l r ⊆ closure {p : ℝ × ℝ |
      Irrational p.1 ∧ Irrational p.2 ∧ p ∈ success A Y c}) : Reduces Y A := by
  apply reduces_of_dense A Y c l r hne
  exact hd.trans (closure_mono (fun _ hp => hp.2.2))

theorem dense_single_program (A Y : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (hne : (rectangle l r).Nonempty)
    (hd : rectangle l r ⊆ closure (success A Y c)) :
    ∃ d : OracleCode, OracleCode.eval (oracleFunction A) d = oracleFunction Y :=
  (OracleCode.turingReducible_iff_exists_code _ _).mp (reduces_of_dense A Y c l r hne hd)

end TuringRigidity.CategorySearch

end OAI
