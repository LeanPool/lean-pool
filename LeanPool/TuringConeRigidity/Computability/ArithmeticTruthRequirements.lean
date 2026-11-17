/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticTruthRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticPrefixFamilies

/-!
# Arithmetic Truth Requirements
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticTruthRequirements
open UniformArithmetic ArithmeticPrefixForcing ArithmeticPrefixFamilies
open FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

theorem arithmetic_truth_requirements {P : Predicate} (hP : Arith P) :
    ∃ Q D : PrefixPredicate, ArithmeticPrefix Q ∧ ArithmeticPrefix D ∧
      (∀ O v, Upward (Q O v)) ∧
      (∀ O v n, DenseOpen (D O (Nat.pair v n))) ∧
      ∀ O v G, GenericFor (fun n => D O (Nat.pair v n)) G →
        (P (Function.update O 0 G) v ↔ G ∈ OpenSet (Q O v)) := by
  have htrue : ArithmeticPrefix (fun _ _ _ => True) :=
    (equal (Primrec.const 0) (Primrec.const 0)).congr (fun _ _ => by simp)
  induction hP with
  | pure P hP =>
    refine ⟨fun _ v _ => P v, fun _ _ _ => True, .pure _ (hP.comp left_primrec), htrue,
      fun _ _ _ _ _ h => h, fun _ _ _ => dense_true, ?_⟩
    intro O v G _
    exact (ArithmeticPrefixForcing.openSet_constant_iff _ _).symm
  | query i =>
    by_cases hi : i = 0
    · subst i
      let Q : PrefixPredicate := fun _ v s => v < s.length ∧ s.getD v false = true
      have hQ : ArithmeticPrefix Q :=
        (less left_primrec (Primrec.list_length.comp (word_primrec.comp right_primrec))).and
          (.pure _ (Primrec.eq.comp ((Primrec.list_getD false).comp
            (word_primrec.comp right_primrec) left_primrec) (Primrec.const true)))
      refine ⟨Q,fun _ _ _ => True,hQ,htrue,?_,fun _ _ _ => dense_true,?_⟩
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
    · refine ⟨fun O v _ => O i v = true, fun _ _ _ => True, (Arith.query i).comp _ left_primrec,
      htrue,
        fun _ _ _ _ _ h => h, fun _ _ _ => dense_true, ?_⟩
      intro O v G _
      simpa only [Function.update_of_ne hi] using
        (ArithmeticPrefixForcing.openSet_constant_iff (O i v = true) G).symm
  | neg h ih =>
    obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ih
    let E : PrefixPredicate := fun O v s => D O v s ∧ Decides (Q O (left v)) s
    have hE : ArithmeticPrefix E := hD.and (prefix_comp (decides_arith hQ) left_primrec)
    refine ⟨fun O v => Avoid (Q O v),E,avoids_arith hQ,hE,
      fun O v => avoids_upward _,?_,?_⟩
    · intro O v n
      simpa only [E,left,Nat.unpair_pair] using
        dense_and (hden O v n) (decides_dense (Q O v) (hup O v))
    · intro O v G hG
      have hGD : GenericFor (fun n => D O (Nat.pair v n)) G := by
        intro n
        obtain ⟨s,hs,hGs⟩ := hG n
        exact ⟨s,hs.1,hGs⟩
      have hdec : G ∈ OpenSet (Decides (Q O v)) := by
        obtain ⟨s,hs,hGs⟩ := hG 0
        exact ⟨s,by simpa only [left,Nat.unpair_pair] using hs.2,hGs⟩
      exact (not_congr (ht O v G hGD)).trans
        (avoid_truth_of_decides (Q O v) (hup O v) G hdec).symm
  | and h k ih ik =>
    obtain ⟨Q,D,hQ,hD,hQu,hDd,hQt⟩ := ih
    obtain ⟨R,E,hR,hE,hRu,hEd,hRt⟩ := ik
    let F : PrefixPredicate := fun O v s =>
      D O (Nat.pair (left v) (left (right v))) s ∧
      E O (Nat.pair (left v) (right (right v))) s
    have hF : ArithmeticPrefix F :=
      (prefix_comp hD (Primrec₂.natPair.comp left_primrec (left_primrec.comp right_primrec))).and
      (prefix_comp hE (Primrec₂.natPair.comp left_primrec (right_primrec.comp right_primrec)))
    refine ⟨fun O v s => Q O v s ∧ R O v s,F,hQ.and hR,hF,
      fun O v s t hst hs => ⟨hQu O v s t hst hs.1,hRu O v s t hst hs.2⟩,?_,?_⟩
    · intro O v n
      simpa only [F,left,right,Nat.unpair_pair] using
        dense_and (hDd O v (left n)) (hEd O v (right n))
    · intro O v G hG
      have hGD : GenericFor (fun n => D O (Nat.pair v n)) G := by
        intro n
        obtain ⟨s,hs,hGs⟩ := hG (Nat.pair n 0)
        exact ⟨s,by simpa only [left,right,Nat.unpair_pair] using hs.1,hGs⟩
      have hGE : GenericFor (fun n => E O (Nat.pair v n)) G := by
        intro n
        obtain ⟨s,hs,hGs⟩ := hG (Nat.pair 0 n)
        exact ⟨s,by simpa only [left,right,Nat.unpair_pair] using hs.2,hGs⟩
      exact (and_congr (hQt O v G hGD) (hRt O v G hGE)).trans
        (open_and (Q O v) (R O v) (hQu O v) (hRu O v) G).symm
  | ex h ih =>
    obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ih
    let E : PrefixPredicate := fun O v =>
      D O (Nat.pair (Nat.pair (left v) (left (right v))) (right (right v)))
    have hE : ArithmeticPrefix E := prefix_comp hD
      (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp left_primrec (left_primrec.comp right_primrec))
        (right_primrec.comp right_primrec))
    refine ⟨fun O v s => ∃ n, Q O (Nat.pair v n) s,E,prefix_exists hQ,hE,?_,?_,?_⟩
    · rintro O v s t hst ⟨n,hn⟩
      exact ⟨n,hup O _ s t hst hn⟩
    · intro O v n
      simpa only [E,left,right,Nat.unpair_pair] using
        hden O (Nat.pair v (left n)) (right n)
    · intro O v G hG
      have hGD (n : ℕ) : GenericFor (fun k => D O (Nat.pair (Nat.pair v n) k)) G := by
        intro k
        simpa only [E,left,right,Nat.unpair_pair] using hG (Nat.pair n k)
      constructor
      · rintro ⟨n,hn⟩
        obtain ⟨s,hs,hGs⟩ := (ht O _ G (hGD n)).mp hn
        exact ⟨s,⟨n,hs⟩,hGs⟩
      · rintro ⟨s,⟨n,hs⟩,hGs⟩
        exact ⟨n,(ht O _ G (hGD n)).mpr ⟨s,hs,hGs⟩⟩
  | comp f h hf ih =>
    obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ih
    let E : PrefixPredicate := fun O v => D O (Nat.pair (f (left v)) (right v))
    refine ⟨fun O v => Q O (f v),E,prefix_comp hQ hf,
      prefix_comp hD (Primrec₂.natPair.comp (hf.comp left_primrec) right_primrec),
      fun O v => hup O (f v),?_,?_⟩
    · intro O v n
      simpa only [E,left,right,Nat.unpair_pair] using hden O (f v) n
    · intro O v G hG
      apply ht O (f v) G
      simpa only [E,left,right,Nat.unpair_pair] using hG

end TuringRigidity.ArithmeticTruthRequirements

end OAI
