/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BranchFrequency
public import LeanPool.TuringConeRigidity.Computability.BinarySeries

/-!
# Generic Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericCoding
open UniformOracle BinarySeries Encodable

/-- Count the true odd-coordinate bits before index `n`. -/
def count (G : Oracle) : ℕ → ℕ := runningSum (fun n => bit G (2*n+1))

/-- Interleave bits of `A` at true odd markers with the unused even-channel bits of `G`. -/
def code (A G : Oracle) (n : ℕ) : Bool :=
  if G (2*n+1) then A (count G n) else G (2*(n-count G n))

theorem count_le (G : Oracle) (n : ℕ) : count G n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count G n + bit G (2*n+1) ≤ n+1
    unfold bit
    split <;> omega

theorem count_mono (G : Oracle) : Monotone (count G) := by
  apply monotone_nat_of_le_succ
  intro n
  change count G n ≤ count G n + bit G (2*n+1)
  omega

/-- True odd-coordinate markers occur arbitrarily far out in `G`. -/
def InfiniteOdd (G : Oracle) : Prop := ∀ N, ∃ n, N ≤ n ∧ G (2*n+1) = true

theorem infiniteOdd_iff (G : Oracle) : InfiniteOdd G ↔ {n | G (2*n+1) = true}.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n,hn,hb⟩ := h (N+1)
    exact ⟨n,hb,by omega⟩
  · intro h N
    obtain ⟨n,hb,hn⟩ := h.exists_gt N
    exact ⟨n,by omega,hb⟩

theorem count_unbounded (G : Oracle) (hG : InfiniteOdd G) (k : ℕ) :
    ∃ n, k ≤ count G n := by
  induction k with
  | zero => exact ⟨0,by simp [count,runningSum]⟩
  | succ k ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,hm,hb⟩ := hG n
    have hc := count_mono G hm
    refine ⟨m+1,?_⟩
    change k+1 ≤ count G m + bit G (2*m+1)
    simp only [bit,hb,↓reduceIte]
    omega

theorem exists_insertion (G : Oracle) (hG : InfiniteOdd G) (k : ℕ) :
    ∃ n, count G n = k ∧ G (2*n+1) = true := by
  have hi : ∀ m, k < count G m → ∃ n, count G n = k ∧ G (2*n+1) = true := by
    intro m
    induction m with
    | zero => simp [count,runningSum]
    | succ m ih =>
      intro hm
      by_cases hk : k < count G m
      · exact ih hk
      · change k < count G m + bit G (2*m+1) at hm
        cases hb : G (2*m+1) with
        | false => simp [bit,hb] at hm; omega
        | true => exact ⟨m,by simp [bit,hb] at hm; omega,hb⟩
  obtain ⟨m,hm⟩ := count_unbounded G hG (k+1)
  exact hi m (by omega)

theorem count_recursive {O : Set (ℕ →. ℕ)} (G : Oracle)
    (hG : Nat.RecursiveIn O (oracleFunction G)) :
    Nat.RecursiveIn O (fun n => Part.some (count G n)) :=
  runningSum_recursive (total_comp hG (total_primrec
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))))

theorem code_recursive {O : Set (ℕ →. ℕ)} (A G : Oracle)
    (hA : Nat.RecursiveIn O (oracleFunction A)) (hG : Nat.RecursiveIn O (oracleFunction G)) :
    Nat.RecursiveIn O (oracleFunction (code A G)) := by
  have hc := count_recursive G hG
  have ho := total_comp hG (total_primrec
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))
  have ha := total_comp hA hc
  have hi := total_comp (total_primrec (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))))
    (total_pair (total_primrec Primrec.id) hc)
  have he := total_comp hG hi
  have hd : Primrec (fun z : ℕ => if (Nat.unpair z).1=1 then
      (Nat.unpair (Nat.unpair z).2).1 else (Nat.unpair (Nat.unpair z).2).2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  exact (total_comp (total_primrec hd) (total_pair ho (total_pair ha he))).of_eq (fun n => by
    cases hh : G (2*n+1) <;> simp [code,oracleFunction,hh])

theorem code_reduces (A G : Oracle) : Reduces (code A G) (join A G) := by
  apply RecursiveIn.iff_nat.mpr
  exact code_recursive A G (RecursiveIn.iff_nat.mp (reduces_join_left A G))
    (RecursiveIn.iff_nat.mp (reduces_join_right A G))

/-- Return the coded bit when the requested index matches the marker count and the marker is
true. -/
def recoverDecision (z : ℕ × ℕ × ℕ × ℕ) : Option ℕ :=
  if z.1=z.2.1 ∧ z.2.2.1=1 then some z.2.2.2 else none

theorem recoverDecision_primrec : Primrec recoverDecision :=
  Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).and
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)))
    (Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const
      none)

/-- Try to recover the `k`th bit of `A` from a true marker in its generic code. -/
def recoverTrial (A G : Oracle) (k n : ℕ) : Option ℕ :=
  recoverDecision (k,count G n,bit G (2*n+1),bit (code A G) n)

theorem recoverTrial_recursive (A G : Oracle) :
    Nat.RecursiveIn {oracleFunction (join (code A G) G)}
      (fun z => Part.some (encode (recoverTrial A G (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (join (code A G) G)}
  have hg : Nat.RecursiveIn O (oracleFunction G) := RecursiveIn.iff_nat.mp (reduces_join_right
    (code A G) G)
  have ha : Nat.RecursiveIn O (oracleFunction (code A G)) := RecursiveIn.iff_nat.mp
    (reduces_join_left (code A G) G)
  have hk := total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hn := total_primrec (O := O) (Primrec.snd.comp Primrec.unpair)
  have hc := total_comp (count_recursive G hg) hn
  have ho := total_comp hg (total_primrec (Primrec.succ.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair))))
  have ha' := total_comp ha hn
  have hd := (Primrec.fst.comp Primrec.unpair).pair
    (((Primrec.fst.comp Primrec.unpair).pair
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).comp (Primrec.snd.comp
        Primrec.unpair))
  exact (total_comp (total_primrec (Primrec.encode.comp (recoverDecision_primrec.comp hd)))
    (total_pair hk (total_pair hc (total_pair ho ha')))).of_eq (fun z => by simp [recoverTrial,bit])

theorem recoverTrial_sound (A G : Oracle) (k n a : ℕ) (ha : a ∈ recoverTrial A G k n) :
    a = bit A k := by
  unfold recoverTrial recoverDecision at ha
  split at ha
  · rename_i h
    have hg : G (2*n+1) = true := by cases hh : G (2*n+1) <;> simp_all [bit]
    have hk : k = count G n := h.1
    simpa [bit,code,hg,←hk] using (Option.mem_def.mp ha).symm
  · simp at ha

theorem recoverTrial_complete (A G : Oracle) (hG : InfiniteOdd G) (k : ℕ) :
    ∃ n a, a ∈ recoverTrial A G k n := by
  obtain ⟨n,hn,hg⟩ := exists_insertion G hG k
  exact ⟨n,bit A k,by simp [recoverTrial,recoverDecision,hn,hg,bit,code]⟩

theorem set_reduces_code_join (A G : Oracle) (hG : InfiniteOdd G) :
    Reduces A (join (code A G) G) := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (recoverTrial_recursive A G) (bit A) (recoverTrial_sound A G)
    (recoverTrial_complete A G hG)

theorem join_degree_eq (A G : Oracle) (hG : InfiniteOdd G) :
    degree (join (code A G) G) = degree (join A G) := by
  apply (degree_eq_iff _ _).mpr
  exact ⟨join_reduces (code_reduces A G) (reduces_join_right A G),
    join_reduces (set_reduces_code_join A G hG) (reduces_join_right (code A G) G)⟩

theorem source_join_degree_eq (A G : Oracle) (hG : {n | G (2*n+1) = true}.Infinite) :
    degree (join (code A G) G) = degree (join A G) :=
  join_degree_eq A G ((infiniteOdd_iff G).mpr hG)

theorem forward_single_program (A G : Oracle) :
    ∃ p : OracleCode, ∀ n, OracleCode.eval (oracleFunction (join A G)) p n = oracleFunction (code
      A G) n := by
  obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp (code_reduces A G)
  exact ⟨p,fun n => congrFun hp n⟩

theorem inverse_single_program (A G : Oracle) (hG : InfiniteOdd G) :
    ∃ p : OracleCode, ∀ n, OracleCode.eval (oracleFunction (join (code A G) G)) p n =
      oracleFunction A n := by
  obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp (set_reduces_code_join A G
    hG)
  exact ⟨p,fun n => congrFun hp n⟩

end TuringRigidity.GenericCoding

end OAI
