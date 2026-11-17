/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/Introreducible.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Data.Set.Finite.Basic

public import LeanPool.TuringConeRigidity.Effective.PrefixComputability
public import LeanPool.TuringConeRigidity.SetModels.Degrees

/-!
# Introreducible
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
namespace Introreducible
open Encodable PrefixComputability

/-- Read an oracle bit as the natural number zero or one. -/
def bit (X : Oracle) (n : ℕ) : ℕ := if X n then 1 else 0

/-- The natural-number encoding of the first `n` oracle bits. -/
def prefixCode (X : Oracle) (n : ℕ) : ℕ := encode (oraclePrefix (bit X) n)

/-- Decode a finite natural-number list, using the empty list for an invalid code. -/
def codeList (c : ℕ) : List ℕ := (decode (α := List ℕ) c).getD []
/-- The length of the decoded finite list. -/
def codeLength (c : ℕ) : ℕ := (codeList c).length

/-- The characteristic oracle of the codes of finite prefixes of `X`. -/
def prefixSet (X : Oracle) (c : ℕ) : Bool := decide (prefixCode X (codeLength c) = c)

@[simp] theorem codeList_prefix (X : Oracle) (n : ℕ) :
    codeList (prefixCode X n) = oraclePrefix (bit X) n := by
  simp [codeList, prefixCode]

@[simp] theorem codeLength_prefix (X : Oracle) (n : ℕ) :
    codeLength (prefixCode X n) = n := by
  simp [codeLength, oraclePrefix]

@[simp] theorem prefixSet_prefix (X : Oracle) (n : ℕ) :
    prefixSet X (prefixCode X n) = true := by
  simp [prefixSet]

theorem prefixCode_injective (X : Oracle) : Function.Injective (prefixCode X) := by
  intro n m h
  simpa using congrArg codeLength h

theorem prefixSet_infinite (X : Oracle) : {c | prefixSet X c = true}.Infinite := by
  apply (Set.infinite_range_of_injective (prefixCode_injective X)).mono
  rintro _ ⟨n, rfl⟩
  exact prefixSet_prefix X n

theorem subset_unbounded {X Z : Oracle}
    (hsub : ∀ c, Z c = true → prefixSet X c = true)
    (hinf : {c | Z c = true}.Infinite) (n : ℕ) :
    ∃ c, Z c = true ∧ n < codeLength c := by
  by_contra h
  have hb : ∀ c, Z c = true → codeLength c ≤ n := by
    intro c hc
    by_contra hn
    exact h ⟨c, hc, Nat.lt_of_not_ge hn⟩
  apply hinf
  apply ((Set.finite_le_nat n).image (prefixCode X)).subset
  intro c hc
  have he := of_decide_eq_true (hsub c hc)
  exact ⟨codeLength c, hb c hc, he⟩

theorem codeList_primrec : Primrec codeList :=
  Primrec.option_getD_default.comp Primrec.decode

theorem codeLength_primrec : Primrec codeLength :=
  Primrec.list_length.comp codeList_primrec

private def equalBit (c : ℕ) : ℕ :=
  if (Nat.unpair c).1 = (Nat.unpair c).2 then 1 else 0

private theorem equalBit_primrec : Primrec equalBit := by
  apply (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)) (Primrec.const 1) (Primrec.const 0)).of_eq
  intro n
  simp [equalBit]

theorem prefixSet_reduces (X : Oracle) : Reduces (prefixSet X) X := by
  apply RecursiveIn.iff_nat.mpr
  have hp := total_comp (prefix_recursive (bit X)) (total_primrec codeLength_primrec)
  have he := total_comp (total_primrec equalBit_primrec)
    (total_pair hp (total_primrec Primrec.id))
  apply he.of_eq
  intro n
  by_cases h : encode (oraclePrefix (bit X) (codeLength n)) = n
  · simp [oracleFunction, prefixSet, equalBit, prefixCode, h]
  · simp [oracleFunction, prefixSet, equalBit, prefixCode, h]

/-- Read the `n`th entry of a decoded prefix code, using zero outside its range. -/
def codeBit (n c : ℕ) : ℕ := (codeList c).getD n 0

@[simp] theorem codeBit_prefix (X : Oracle) (n m : ℕ) (h : n < m) :
    codeBit n (prefixCode X m) = bit X n := by
  simp [codeBit, oraclePrefix, List.getD_eq_getElem?_getD, List.getElem?_range h]

theorem codeBit_primrec : Primrec₂ codeBit :=
  (Primrec.list_getD 0).comp (codeList_primrec.comp Primrec.snd) Primrec.fst

/-- Read entry `n` from a sufficiently long decoded list whose code is marked true by `Z`. -/
def trial (Z : Oracle) (n c : ℕ) : Option ℕ :=
  if Z c = true ∧ n < codeLength c then some (codeBit n c) else none

private def trialStep (p : ℕ) : ℕ :=
  let n := (Nat.unpair p).1
  let c := (Nat.unpair (Nat.unpair p).2).1
  let b := (Nat.unpair (Nat.unpair p).2).2
  encode (if b = 1 ∧ n < codeLength c then some (codeBit n c) else none)

private theorem trialStep_primrec : Primrec trialStep := by
  let hn := Primrec.fst.comp Primrec.unpair
  let hc := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  let hb := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  apply (Primrec.encode.comp (Primrec.ite
    ((Primrec.eq.comp hb (Primrec.const 1)).and
      (Primrec.nat_lt.comp hn (codeLength_primrec.comp hc)))
    (Primrec.option_some.comp (codeBit_primrec.comp hn hc)) (Primrec.const none))).of_eq
  intro p
  simp [trialStep]

theorem trial_recursive (Z : Oracle) :
    Nat.RecursiveIn {oracleFunction Z}
      (fun p => Part.some (encode (trial Z (Nat.unpair p).1 (Nat.unpair p).2))) := by
  have hq : Nat.RecursiveIn {oracleFunction Z} (oracleFunction Z) :=
    .oracle _ (Set.mem_singleton _)
  have hn := total_primrec (O := {oracleFunction Z}) (Primrec.fst.comp Primrec.unpair)
  have hc := total_primrec (O := {oracleFunction Z}) (Primrec.snd.comp Primrec.unpair)
  have ht := total_comp (total_primrec trialStep_primrec)
    (total_pair hn (total_pair hc (total_comp hq hc)))
  apply ht.of_eq
  intro p
  cases hz : Z (Nat.unpair p).2 <;> simp [trialStep, trial, hz]

theorem reduces_of_infinite_subset {X Z : Oracle}
    (hsub : ∀ c, Z c = true → prefixSet X c = true)
    (hinf : {c | Z c = true}.Infinite) : Reduces X Z := by
  apply RecursiveIn.iff_nat.mpr
  change Nat.RecursiveIn {oracleFunction Z} (fun n => Part.some (bit X n))
  apply total_search (trial_recursive Z) (bit X)
  · intro n c a ha
    simp only [trial] at ha
    split at ha
    next h =>
      have he : prefixCode X (codeLength c) = c := of_decide_eq_true (hsub c h.1)
      have ha' : a = codeBit n c := (Option.mem_some_iff.mp ha).symm
      rw [ha', ← he]
      exact codeBit_prefix X n (codeLength c) h.2
    next h => simp at ha
  · intro n
    obtain ⟨c, hc, hn⟩ := subset_unbounded hsub hinf n
    exact ⟨c, codeBit n c, by simp [trial, hc, hn]⟩

theorem prefixSet_degree (X : Oracle) : degree (prefixSet X) = degree X := by
  apply (degree_eq_iff _ _).mpr
  exact ⟨prefixSet_reduces X, reduces_of_infinite_subset (fun _ h => h)
    (prefixSet_infinite X)⟩

theorem introreducible_representative (X : Oracle) :
    ∃ Y : Oracle, degree Y = degree X ∧ {n | Y n = true}.Infinite ∧
      ∀ Z : Oracle, (∀ n, Z n = true → Y n = true) →
        {n | Z n = true}.Infinite → Reduces Y Z := by
  refine ⟨prefixSet X, prefixSet_degree X, prefixSet_infinite X, ?_⟩
  intro Z hsub hinf
  exact reduces_trans (prefixSet_reduces X) (reduces_of_infinite_subset hsub hinf)

end Introreducible
end TuringRigidity

end OAI
