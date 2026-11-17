/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformOracle.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BranchMachine

/-!
# Uniform Oracle
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
open Encodable

namespace UniformOracle
variable {O : Set (ℕ →. ℕ)}

theorem total_comp {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) := by
  simpa using Nat.RecursiveIn.comp hf hg

theorem total_pair {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
  simpa [Seq.seq] using Nat.RecursiveIn.pair hf hg

theorem total_primrec {f : ℕ → ℕ} (hf : Primrec f) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

/-- The finite list of the first `m` values of a numerical oracle. -/
def oraclePrefix (g : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map g

/-- Decode a finite numerical list, append a value, and re-encode it. -/
def appendEncoded (a b : ℕ) : ℕ := encode ((decode (α := List ℕ) a).getD [] ++ [b])

theorem appendEncoded_primrec : Primrec₂ appendEncoded :=
  Primrec.encode.comp (Primrec.list_append.comp
    (Primrec.option_getD_default.comp (Primrec.decode.comp Primrec.fst))
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

theorem prefix_recursive (g : ℕ → ℕ) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun m => Part.some (encode (oraclePrefix g m))) :=
      by
  have hquery : Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (g n)) :=
    .oracle _ (Set.mem_singleton _)
  have hy := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp
    (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.snd.comp
    (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp ((total_primrec (O := {fun n => Part.some (g n)}))
    (appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hquery hy))
  have hp := Nat.RecursiveIn.prec ((total_primrec (O := {fun n => Part.some (g n)}))
    (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair ((total_primrec (O := {fun n => Part.some (g n)})) (Primrec.const 0))
      ((total_primrec (O := {fun n => Part.some (g n)})) Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [appendEncoded, oraclePrefix, List.range_succ]

theorem prefix_approximates (g : ℕ → ℕ) (k : ℕ) :
    Approximates (Part.some (g k)) (fun m => BranchMachine.lookup (oraclePrefix g m) k) := by
  have he (m : ℕ) : (oraclePrefix g m)[k]? = if k < m then some (g k) else none := by
    simp only [oraclePrefix, List.getElem?_map]
    by_cases hk : k < m
    · rw [List.getElem?_range hk, ite_eq_left hk]
      rfl
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk), ite_eq_right hk]
      rfl
  constructor
  · intro m a ha
    change a ∈ ((oraclePrefix g m)[k]? : Part ℕ) at ha
    rw [he] at ha
    split at ha
    · simpa using ha
    · simp at ha
  · intro a ha
    have ha' : a = g k := Part.mem_some_iff.mp ha
    subst a
    refine ⟨k+1,fun m hm => ?_⟩
    change g k ∈ ((oraclePrefix g m)[k]? : Part ℕ)
    rw [he, ite_eq_left (by omega)]
    exact Part.mem_some _

private def flag (e : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) e).getD none).isSome then 0 else 1
private def answer (e : ℕ) : ℕ := ((decode (α := Option ℕ) e).getD none).getD 0

private theorem flag_primrec : Primrec flag := by
  apply (Primrec.cond (Primrec.option_isSome.comp (Primrec.option_getD_default.comp
    (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases hh : ((decode (α := Option ℕ) n).getD none).isSome <;> simp only [flag,hh] <;> rfl
private theorem answer_primrec : Primrec answer :=
  Primrec.option_getD_default.comp (Primrec.option_getD_default.comp Primrec.decode)

theorem total_search {E : ℕ → ℕ → Option ℕ}
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : ℕ → ℕ) (hsound : ∀ n m a, a ∈ E n m → a = f n)
    (hcomplete : ∀ n, ∃ m a, a ∈ E n m) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) := by
  have hflag := total_comp (total_primrec flag_primrec) hE
  have hfind := Nat.RecursiveIn.rfind hflag
  have hpair := Nat.RecursiveIn.pair (total_primrec Primrec.id) hfind
  have hrun := Nat.RecursiveIn.comp (total_primrec answer_primrec)
    (Nat.RecursiveIn.comp hE hpair)
  apply hrun.of_eq_tot
  intro n
  have hex : ∃ m, (E n m).isSome = true := by
    obtain ⟨m,a,ha⟩ := hcomplete n
    exact ⟨m, Option.isSome_iff_exists.mpr ⟨a,ha⟩⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hm
  have hval : a = f n := hsound n m a ha
  have hmem : m ∈ Nat.rfind (fun k =>
      (fun v : ℕ => decide (v=0)) <$> Part.some (flag (encode (E n k)))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · simp [flag, m, hm]
    · intro k hk
      have hk' : (E n k).isSome = false := Bool.eq_false_iff.mpr (Nat.find_min hex hk)
      simp [flag, hk']
  apply Part.mem_bind_iff.mpr
  refine ⟨encode (E n m), ?_, ?_⟩
  · apply Part.mem_bind_iff.mpr
    refine ⟨Nat.pair n m, ?_, ?_⟩
    · simp only [Seq.seq]
      apply Part.mem_bind_iff.mpr
      refine ⟨Nat.pair n, (Part.mem_map_iff _).mpr ⟨n,Part.mem_some _,rfl⟩, ?_⟩
      exact (Part.mem_map_iff _).mpr ⟨m,by simpa only [Nat.unpair_pair] using hmem,rfl⟩
    · simp
  · have hea : E n m = some a := Option.mem_def.mp ha
    apply Part.mem_some_iff.mpr
    rw [hea]
    simpa only [answer, Encodable.encodek, Option.getD_some] using hval.symm

/-- Run the program for a bounded time using the finite oracle prefix specified by the trial
code. -/
def trial (g : ℕ → ℕ) (c : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  c.evaln (Nat.unpair z).2 (Nat.pair (encode (oraclePrefix g (Nat.unpair z).1)) n)

theorem trial_recursive (g : ℕ → ℕ) (c : Nat.Partrec.Code) :
    Nat.RecursiveIn {fun n => Part.some (g n)}
      (fun z => Part.some (encode (trial g c (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have hm := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp
    (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hk := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.snd.comp
    (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hn := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp Primrec.unpair)
  have hp := total_comp (prefix_recursive g) hm
  have he := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.encode.comp
    (Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.unpair).pair (Primrec.const c)).pair
        (Primrec.snd.comp Primrec.unpair))))
  exact (total_comp he (total_pair hk (total_pair hp hn))).of_eq (fun z => by
    simp [trial])

theorem compute_of_finite (g f : ℕ → ℕ) (c : Nat.Partrec.Code)
    (ha : ∀ n, Approximates (Part.some (f n))
      (fun m => c.eval (Nat.pair (encode (oraclePrefix g m)) n))) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (f n)) := by
  apply total_search (trial_recursive g c) f
  · intro n z a h
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a
      (Nat.Partrec.Code.evaln_sound h))
  · intro n
    obtain ⟨M,hM⟩ := (ha n).2 (f n) (Part.mem_some _)
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp (hM M le_rfl)
    exact ⟨Nat.pair M k,f n,by simpa [trial] using hk⟩

theorem stage_recursive (p q : OracleCode) (j h : ℕ) (g f : ℕ → ℕ)
    (hf : ∀ n k, BranchMachine.stage p q j h (fun x => Part.some (g x)) n k =
      Part.some (f (Nat.pair n k))) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (f n)) := by
  obtain ⟨c,hc⟩ := partrec_code (BranchMachine.stage_finite_partrec p q j h)
  have hc' (L : List ℕ) (z : ℕ) :
      c.eval (Nat.pair (encode L) z) =
        BranchMachine.stage p q j h (BranchMachine.lookup L) (Nat.unpair z).1 (Nat.unpair z).2 := by
    have hh := hc (L,(Nat.unpair z).1,(Nat.unpair z).2)
    change c.eval (Nat.pair (encode L) (Nat.pair (Nat.unpair z).1 (Nat.unpair z).2)) = _ at hh
    simpa only [Nat.pair_unpair] using hh
  apply compute_of_finite g f c
  intro z
  have hh := BranchMachine.stage_approximates p q j h (prefix_approximates g)
    (Nat.unpair z).1 (Nat.unpair z).2
  simpa only [← hc', hf, Nat.pair_unpair] using hh

end UniformOracle
end TuringRigidity

end OAI
