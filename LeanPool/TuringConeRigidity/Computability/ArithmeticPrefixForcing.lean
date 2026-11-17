/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticPrefixForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticCommonRequirement
public import LeanPool.TuringConeRigidity.SetModels.ShuffleRequirements

/-!
# Arithmetic Prefix Forcing
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticPrefixForcing
open Encodable UniformArithmetic FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

/-- Predicates of oracle parameters, a natural-number index, and a finite binary word. -/
abbrev PrefixPredicate := Oracles → ℕ → List Bool → Prop
/-- Arithmetic definability of a prefix predicate after coding its index and word by one
number. -/
abbrev ArithmeticPrefix (Q : PrefixPredicate) :=
  Arith (fun O v => Q O (left v) (word (right v)))

/-- A word property is preserved by extending the word. -/
def Upward (Q : List Bool → Prop) : Prop :=
  ∀ s t, s <+: t → Q s → Q t

/-- No extension of the given word has the property `Q`. -/
def Avoid (Q : List Bool → Prop) (s : List Bool) : Prop :=
  ∀ t, s <+: t → ¬ Q t

/-- The word either satisfies `Q` or excludes `Q` on every extension. -/
def Decides (Q : List Bool → Prop) (s : List Bool) : Prop := Q s ∨ Avoid Q s

/-- The oracle meets every arithmetically definable dense open family of finite words. -/
def Generic (O : Oracles) (G : Oracle) : Prop :=
  ∀ D : Oracles → List Bool → Prop,
    Arith (fun O n => D O (word n)) → DenseOpen (D O) →
    ∃ s, D O s ∧ Realizes s G

theorem avoids_upward (Q : List Bool → Prop) : Upward (Avoid Q) :=
  fun _ _ h hs u hu => hs u (h.trans hu)

theorem decides_dense (Q : List Bool → Prop) (hQ : Upward Q) :
    DenseOpen (Decides Q) := by
  classical
  constructor
  · intro s
    by_cases h : ∃ t, s <+: t ∧ Q t
    · obtain ⟨t,ht,hq⟩ := h
      exact ⟨t,ht,Or.inl hq⟩
    · exact ⟨s,List.prefix_rfl,Or.inr (fun t ht hq => h ⟨t,ht,hq⟩)⟩
  · intro s t h
    exact Or.imp (hQ s t h) (avoids_upward Q s t h)

theorem avoids_arith {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q) :
    ArithmeticPrefix (fun O v => Avoid (Q O v)) := by
  have hp := ArithmeticCommonRequirement.prefix_arith
    (right_primrec.comp left_primrec) right_primrec
  have h := hQ.comp _ (Primrec₂.natPair.comp (left_primrec.comp left_primrec) right_primrec)
  apply (hp.imp h.neg).all.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · intro h t ht
    have hh := h (encode t)
    simpa only [word,Encodable.encodek,Option.getD_some] using hh (by
      simpa only [word,Encodable.encodek,Option.getD_some] using ht)
  · intro h t ht
    exact h (word t) ht

theorem decides_arith {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q) :
    ArithmeticPrefix (fun O v => Decides (Q O v)) := hQ.or (avoids_arith hQ)

theorem realizes_common {s t : List Bool} {G : Oracle}
    (hs : Realizes s G) (ht : Realizes t G) :
    ∃ u, s <+: u ∧ t <+: u ∧ Realizes u G := by
  refine ⟨initial G (max s.length t.length), ?_, ?_,
    (realizes_initial _ _ _).mpr (fun _ _ => rfl)⟩
  · rw [←prefix_default s]
    exact initial_prefix (by simp) hs
  · rw [←prefix_default t]
    exact initial_prefix (by simp) ht

theorem open_and (Q R : List Bool → Prop) (hQ : Upward Q) (hR : Upward R) (G : Oracle) :
    G ∈ OpenSet (fun s => Q s ∧ R s) ↔ G ∈ OpenSet Q ∧ G ∈ OpenSet R := by
  constructor
  · rintro ⟨s,⟨hq,hr⟩,hs⟩
    exact ⟨⟨s,hq,hs⟩,⟨s,hr,hs⟩⟩
  · rintro ⟨⟨s,hq,hs⟩,⟨t,hr,ht⟩⟩
    obtain ⟨u,hsu,htu,hu⟩ := realizes_common hs ht
    exact ⟨u,⟨hQ s u hsu hq,hR t u htu hr⟩,hu⟩

theorem open_avoid {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q)
    (hup : ∀ O v, Upward (Q O v)) (O : Oracles) (v : ℕ) (G : Oracle)
    (hG : Generic O G) :
    G ∈ OpenSet (Avoid (Q O v)) ↔ ¬ G ∈ OpenSet (Q O v) := by
  constructor
  · rintro ⟨s,hs,hGs⟩ ⟨t,ht,hGt⟩
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hGs hGt
    exact hs u hsu (hup O v t u htu ht)
  · intro hn
    have hd : Arith (fun O n => Decides (Q O v) (word n)) :=
      ((decides_arith hQ).comp _ (Primrec₂.natPair.comp (Primrec.const v) Primrec.id)).congr
        (fun _ _ => by simp only [left,right,Nat.unpair_pair,id_eq])
    obtain ⟨s,hs,hGs⟩ := hG (fun O s => Decides (Q O v) s) hd (decides_dense _ (hup O v))
    rcases hs with hs | hs
    · exact False.elim (hn ⟨s,hs,hGs⟩)
    · exact ⟨s,hs,hGs⟩

end TuringRigidity.ArithmeticPrefixForcing

end OAI
