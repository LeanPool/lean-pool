/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/RecursiveInfiniteSubset.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.OracleEnumeration

/-!
# Recursive Infinite Subset
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RecursiveInfiniteSubset
open Encodable PrefixComputability

def Unbounded (E : ℕ → Option ℕ) : Prop := ∀ n, ∃ z m, n ≤ m ∧ m ∈ E z

theorem accepted_exists (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) :
    ∃ z, E z ≠ none ∧ n ≤ (E z).getD 0 := by
  obtain ⟨z, m, hm, hz⟩ := h n
  exact ⟨z, by simp [Option.mem_def.mp hz, hm]⟩

noncomputable def index (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) : ℕ :=
  Nat.find (accepted_exists E h n)

noncomputable def above (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) : ℕ :=
  (E (index E h n)).getD 0

theorem above_spec (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) :
    n ≤ above E h n ∧ above E h n ∈ E (index E h n) := by
  have hs := Nat.find_spec (accepted_exists E h n)
  refine ⟨hs.2, ?_⟩
  change (E (index E h n)).getD 0 ∈ E (index E h n)
  cases he : E (index E h n) with
  | none => exact False.elim (hs.1 he)
  | some a => simp

private def flag (p : ℕ) : ℕ :=
  let v := (decode (α := Option ℕ) (Nat.unpair p).2).getD none
  if v ≠ none ∧ (Nat.unpair p).1 ≤ v.getD 0 then 0 else 1

private theorem flag_primrec : Primrec flag := by
  let hv := Primrec.option_getD_default.comp ((Primrec.decode (α := Option ℕ)).comp
    (Primrec.snd.comp Primrec.unpair))
  exact Primrec.ite (((Primrec.eq.comp hv (Primrec.const none)).not).and
    (Primrec.nat_le.comp (Primrec.fst.comp Primrec.unpair) (Primrec.option_getD_default.comp hv)))
    (Primrec.const 0) (Primrec.const 1)

theorem index_recursive {O : Set (ℕ →. ℕ)} (E : ℕ → Option ℕ) (h : Unbounded E)
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E z)))) :
    Nat.RecursiveIn O (fun n => Part.some (index E h n)) := by
  have hn := total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hz := total_primrec (O := O) (Primrec.snd.comp Primrec.unpair)
  have hf := total_comp (total_primrec flag_primrec) (total_pair hn (total_comp hE hz))
  apply (Nat.RecursiveIn.rfind hf).of_eq_tot
  intro n
  apply Nat.mem_rfind.mpr
  constructor
  · have hs := Nat.find_spec (accepted_exists E h n)
    simp [flag, index, hs.1, hs.2]
  · intro z hz
    have hm := Nat.find_min (accepted_exists E h n) hz
    simp [flag, hm]

theorem above_recursive {O : Set (ℕ →. ℕ)} (E : ℕ → Option ℕ) (h : Unbounded E)
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E z)))) :
    Nat.RecursiveIn O (fun n => Part.some (above E h n)) := by
  have hv := total_primrec (O := O) (Primrec.option_getD_default.comp
    (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
  exact (total_comp hv (total_comp hE (index_recursive E h hE))).of_eq
    (fun n => by simp [above])

noncomputable def growing (E : ℕ → Option ℕ) (h : Unbounded E) : ℕ → ℕ
  | 0 => above E h 0
  | n+1 => above E h (growing E h n + 1)

theorem growing_strictMono (E : ℕ → Option ℕ) (h : Unbounded E) : StrictMono (growing E h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self _).trans_le (above_spec E h _).1

theorem growing_mem (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) :
    ∃ z, growing E h n ∈ E z := by
  cases n <;> exact ⟨_, (above_spec E h _).2⟩

theorem growing_recursive {O : Set (ℕ →. ℕ)} (E : ℕ → Option ℕ) (h : Unbounded E)
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E z)))) :
    Nat.RecursiveIn O (fun n => Part.some (growing E h n)) := by
  have habove := above_recursive E h hE
  have hbase := total_comp habove (total_primrec (Primrec.const 0))
  have hstep := total_comp habove (total_primrec
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair)))))
  have hrec := Nat.RecursiveIn.prec hbase hstep
  have hr := Nat.RecursiveIn.comp hrec
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply hr.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [growing]

theorem recursive_range (Y : Oracle) (f : ℕ → ℕ) (hf : StrictMono f)
    (hrec : Nat.RecursiveIn {oracleFunction Y} (fun n => Part.some (f n))) :
    ∃ C : Oracle, Reduces C Y ∧ ∀ m, C m = true ↔ ∃ n, f n = m := by
  let E := fun n => some (f n)
  have hE : Nat.RecursiveIn {oracleFunction Y} (fun n => Part.some (encode (E n))) :=
    total_comp (total_primrec (Primrec.encode.comp (Primrec.option_some.comp Primrec.id))) hrec
  have hu : Unbounded E := fun n => ⟨n, f n, hf.id_le n, by simp [E]⟩
  let C : Oracle := fun m => decide (above E hu m = m)
  refine ⟨C, ?_, ?_⟩
  · apply RecursiveIn.iff_nat.mpr
    have heq := total_primrec (O := {oracleFunction Y})
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.snd.comp Primrec.unpair)) (Primrec.const 1) (Primrec.const 0))
    have hh := total_comp heq (total_pair (above_recursive E hu hE) (total_primrec Primrec.id))
    apply hh.of_eq
    intro m
    by_cases he : above E hu m = m <;> simp [oracleFunction, C, he]
  · intro m
    change decide (above E hu m = m) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · intro he
      exact ⟨index E hu m, he⟩
    · rintro ⟨n, hn⟩
      have hi : index E hu m ≤ n := Nat.find_min' (accepted_exists E hu m) (by simp [E, hn])
      have hs := (above_spec E hu m).1
      have he : above E hu m = f (index E hu m) := by simp [above, E]
      rw [he] at hs ⊢
      exact Nat.le_antisymm ((hf.monotone hi).trans (Nat.le_of_eq hn)) hs

theorem infinite_recursive_subset (Y : Oracle) (E : ℕ → Option ℕ)
    (h : Unbounded E)
    (hE : Nat.RecursiveIn {oracleFunction Y} (fun z => Part.some (encode (E z)))) :
    ∃ C : Oracle, Reduces C Y ∧ {m | C m = true}.Infinite ∧
      ∀ m, C m = true → ∃ z, m ∈ E z := by
  obtain ⟨C, hCY, hC⟩ := recursive_range Y (growing E h) (growing_strictMono E h)
    (growing_recursive E h hE)
  refine ⟨C, hCY, ?_, ?_⟩
  · have heq : {m | C m = true} = Set.range (growing E h) := by
      ext m
      exact hC m
    rw [heq]
    exact Set.infinite_range_of_injective (growing_strictMono E h).injective
  · intro m hm
    obtain ⟨n, rfl⟩ := (hC m).mp hm
    exact growing_mem E h n

end TuringRigidity.RecursiveInfiniteSubset

end OAI
