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
public import LeanPool.TuringConeRigidity.Effective.PrefixComputability

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
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) :=
  PrefixComputability.total_comp hf hg

theorem total_pair {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) :=
  PrefixComputability.total_pair hf hg

theorem total_primrec {f : ℕ → ℕ} (hf : Primrec f) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  PrefixComputability.total_primrec hf

/-- The finite list of the first `m` values of a numerical oracle. -/
def oraclePrefix (g : ℕ → ℕ) (m : ℕ) : List ℕ :=
  PrefixComputability.oraclePrefix g m

/-- Decode a finite numerical list, append a value, and re-encode it. -/
def appendEncoded (a b : ℕ) : ℕ :=
  PrefixComputability.appendEncoded a b

theorem appendEncoded_primrec : Primrec₂ appendEncoded :=
  PrefixComputability.appendEncoded_primrec

theorem prefix_recursive (g : ℕ → ℕ) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun m => Part.some (encode (oraclePrefix g m))) :=
  PrefixComputability.prefix_recursive g

theorem prefix_approximates (g : ℕ → ℕ) (k : ℕ) :
    Approximates (Part.some (g k)) (fun m => BranchMachine.lookup (oraclePrefix g m) k) := by
  have he (m : ℕ) : (oraclePrefix g m)[k]? = if k < m then some (g k) else none := by
    simp only [oraclePrefix, PrefixComputability.oraclePrefix, List.getElem?_map]
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

theorem total_search {E : ℕ → ℕ → Option ℕ}
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : ℕ → ℕ) (hsound : ∀ n m a, a ∈ E n m → a = f n)
    (hcomplete : ∀ n, ∃ m a, a ∈ E n m) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  PrefixComputability.total_search hE f hsound hcomplete

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
