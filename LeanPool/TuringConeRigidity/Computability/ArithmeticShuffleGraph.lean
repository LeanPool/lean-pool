/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticShuffleGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticOracles
public import LeanPool.TuringConeRigidity.Effective.FiniteShuffleComputation

/-!
# Arithmetic Shuffle Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticShuffleGraph
open Encodable UniformArithmetic FiniteShuffle ShuffleRequirements GenericCoding
open EncodedForcing (word word_primrec)

theorem realizes_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c s : ℕ → ℕ} (hc : Primrec c) (hs : Primrec s) :
    Arith (fun O v => Realizes (word (s v)) (B O (c v))) := by
  have hb := Arith.pure (fun v => (word (s (left v))).getD (right v) false = true)
    (Primrec.eq.comp ((Primrec.list_getD false).comp
      (word_primrec.comp (hs.comp left_primrec)) right_primrec) (Primrec.const true))
  have hq := query_at hB (hc.comp left_primrec) right_primrec
  have hl := less right_primrec
    (Primrec.list_length.comp (word_primrec.comp (hs.comp left_primrec)))
  apply (hl.imp (hb.iff hq)).all.congr
  intro O v
  simp only [left, right, Nat.unpair_pair]
  constructor
  · intro h i hi
    have hh := h i hi
    cases hb : (word (s v)).getD i false <;> cases ho : B O (c v) i <;> simp_all
  · intro h i hi
    rw [show (word (s v)).getD i false = B O (c v) i from h i hi]

theorem code_bit_iff (Y L : Oracle) (n : ℕ) :
    code Y L n = true ↔ ∃ s t : ℕ,
      (word s).length = n + 1 ∧ (word t).length = 2 * (n + 1) ∧
      Realizes (word s) Y ∧ Realizes (word t) L ∧
      code (fun i => (word s).getD i false) (fun i => (word t).getD i false) n = true := by
  constructor
  · intro h
    refine ⟨encode (initial Y (n + 1)), encode (initial L (2 * (n + 1))), ?_⟩
    simp only [word, Encodable.encodek, Option.getD_some, prefix_length]
    have hy : Realizes (initial Y (n + 1)) Y :=
      (realizes_initial _ _ _).mpr (fun _ _ => rfl)
    have hl : Realizes (initial L (2 * (n + 1))) L :=
      (realizes_initial _ _ _).mpr (fun _ _ => rfl)
    have he := code_agree (n := n + 1)
      (show Agree (n + 1) (fun i => (initial Y (n+1)).getD i false) Y from
        fun i hi => prefix_getD Y _ i hi)
      (show Agree (2 * (n + 1)) (fun i => (initial L (2*(n+1))).getD i false) L from
        fun i hi => prefix_getD L _ i hi)
    exact ⟨True.intro, True.intro, hy, hl, (he n (by omega)).trans h⟩
  · rintro ⟨s,t,hs,ht,hy,hl,h⟩
    have hy' : Agree (n + 1) (fun i => (word s).getD i false) Y := by
      simpa only [Realizes, hs] using hy
    have hl' : Agree (2 * (n + 1)) (fun i => (word t).getD i false) L := by
      simpa only [Realizes, ht] using hl
    exact ((code_agree hy' hl') n (by omega)).symm.trans h

theorem code_arith {Y L : OracleFamily}
    (hY : ArithmeticOracle Y) (hL : ArithmeticOracle L) :
    ArithmeticOracle (fun O v => code (Y O v) (L O v)) := by
  let base := left_primrec.comp (left_primrec.comp left_primrec)
  let n := right_primrec.comp (left_primrec.comp left_primrec)
  let s := right_primrec.comp left_primrec
  let t := right_primrec
  have hs := equal (Primrec.list_length.comp (word_primrec.comp s)) (Primrec.succ.comp n)
  have ht := equal (Primrec.list_length.comp (word_primrec.comp t))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp n))
  have hy := realizes_arith hY base s
  have hl := realizes_arith hL base t
  have hb := Arith.pure _ (Primrec.eq.comp
    (FiniteShuffleComputation.wordShuffleBit_primrec.comp
      ((word_primrec.comp s).pair ((word_primrec.comp t).pair n))) (Primrec.const true))
  exact (hs.and (ht.and (hy.and (hl.and hb)))).ex.ex.congr (fun O v => by
    simpa only [base,n,s,t,left,right,Nat.unpair_pair] using
      (code_bit_iff (Y O (left v)) (L O (left v)) (right v)).symm)

end TuringRigidity.ArithmeticShuffleGraph

end OAI
