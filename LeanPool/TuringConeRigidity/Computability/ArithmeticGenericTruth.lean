/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticGenericTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticPrefixForcing

/-!
# Arithmetic Generic Truth
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticGenericTruth
open Encodable UniformArithmetic ArithmeticPrefixForcing FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

theorem open_constant (p : Prop) (G : Oracle) : G ∈ OpenSet (fun _ => p) ↔ p := by
  constructor
  · rintro ⟨_,hp,_⟩; exact hp
  · intro hp
    exact ⟨[],hp,fun i hi => by simp at hi⟩

theorem arithmetic_generic_truth {P : Predicate} (hP : Arith P) :
    ∃ Q : PrefixPredicate, ArithmeticPrefix Q ∧ (∀ O v, Upward (Q O v)) ∧
      ∀ O v G, Generic O G →
        (P (Function.update O 0 G) v ↔ G ∈ OpenSet (Q O v)) := by
  induction hP with
  | pure P hP =>
    refine ⟨fun _ v _ => P v, .pure _ (hP.comp left_primrec),
      fun _ _ _ _ _ h => h, ?_⟩
    intro O v G _
    exact (open_constant _ _).symm
  | query i =>
    by_cases hi : i = 0
    · subst i
      let Q : PrefixPredicate := fun _ v s => v < s.length ∧ s.getD v false = true
      have hQ : ArithmeticPrefix Q :=
        (less left_primrec (Primrec.list_length.comp (word_primrec.comp right_primrec))).and
          (.pure _ (Primrec.eq.comp ((Primrec.list_getD false).comp
            (word_primrec.comp right_primrec) left_primrec) (Primrec.const true)))
      refine ⟨Q,hQ,?_,?_⟩
      · intro O v s t hst hs
        exact ⟨lt_of_lt_of_le hs.1 hst.length_le,
          (getD_of_prefix hst v hs.1).symm.trans hs.2⟩
      · intro O v G _
        simp only [Function.update_self]
        constructor
        · intro hv
          refine ⟨initial G (v+1),⟨?_,?_⟩,
            (realizes_initial _ _ _).mpr (fun _ _ => rfl)⟩
          · simp
          · exact (prefix_getD G _ v (by omega)).trans hv
        · rintro ⟨s,hs,hGs⟩
          exact (hGs v hs.1).symm.trans hs.2
    · refine ⟨fun O v _ => O i v = true, (Arith.query i).comp _ left_primrec,
        fun _ _ _ _ _ h => h, ?_⟩
      intro O v G _
      simpa only [Function.update_of_ne hi] using (open_constant (O i v = true) G).symm
  | neg h ih =>
    obtain ⟨Q,hQ,hup,ht⟩ := ih
    refine ⟨fun O v => Avoid (Q O v), avoids_arith hQ, fun O v => avoids_upward _, ?_⟩
    intro O v G hG
    exact (not_congr (ht O v G hG)).trans (open_avoid hQ hup O v G hG).symm
  | and h k ih ik =>
    obtain ⟨Q,hQ,hQu,hQt⟩ := ih
    obtain ⟨R,hR,hRu,hRt⟩ := ik
    refine ⟨fun O v s => Q O v s ∧ R O v s, hQ.and hR,
      fun O v s t hst hs => ⟨hQu O v s t hst hs.1,hRu O v s t hst hs.2⟩, ?_⟩
    intro O v G hG
    exact (and_congr (hQt O v G hG) (hRt O v G hG)).trans
      (open_and (Q O v) (R O v) (hQu O v) (hRu O v) G).symm
  | ex h ih =>
    obtain ⟨Q,hQ,hup,ht⟩ := ih
    have he : ArithmeticPrefix (fun O v s => ∃ n, Q O (Nat.pair v n) s) :=
      ((hQ.comp _ (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp (left_primrec.comp left_primrec) right_primrec)
        (right_primrec.comp left_primrec))).ex).congr
          (fun _ _ => by simp only [left,right,Nat.unpair_pair])
    refine ⟨fun O v s => ∃ n, Q O (Nat.pair v n) s, he, ?_, ?_⟩
    · rintro O v s t hst ⟨n,hn⟩
      exact ⟨n,hup O _ s t hst hn⟩
    · intro O v G hG
      constructor
      · rintro ⟨n,hn⟩
        obtain ⟨s,hs,hGs⟩ := (ht O _ G hG).mp hn
        exact ⟨s,⟨n,hs⟩,hGs⟩
      · rintro ⟨s,⟨n,hs⟩,hGs⟩
        exact ⟨n,(ht O _ G hG).mpr ⟨s,hs,hGs⟩⟩
  | comp f h hf ih =>
    obtain ⟨Q,hQ,hup,ht⟩ := ih
    refine ⟨fun O v => Q O (f v), ?_, fun O v => hup O (f v),
      fun O v G hG => ht O (f v) G hG⟩
    exact (hQ.comp _ (Primrec₂.natPair.comp (hf.comp left_primrec) right_primrec)).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair])

end TuringRigidity.ArithmeticGenericTruth

end OAI
