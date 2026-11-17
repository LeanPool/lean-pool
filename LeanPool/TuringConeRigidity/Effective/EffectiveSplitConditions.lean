/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EffectiveSplitConditions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.EffectiveSplit
public import LeanPool.TuringConeRigidity.Effective.CodingLocations

/-!
# Effective Split Conditions
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveSplitConditions
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing OracleJump EffectiveSplit
open CodingForcing CodingAgreement CodingLocations

def update (p w : ℕ) : ℕ :=
  if (Nat.unpair w).1 = 2 then
    code (append (condition p) ((word (item (Nat.unpair w).2 1)).drop (left p).length))
  else code (condition p)

theorem update_primrec : Primrec₂ update := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hc : Primrec (fun p : ℕ => code (condition p)) := Primrec₂.natPair.comp
    (Primrec.encode.comp left_primrec)
    (Primrec₂.natPair.comp (Primrec.encode.comp right_primrec) active_primrec)
  let l : Primrec (fun z : ℕ × ℕ => left z.1) := left_primrec.comp Primrec.fst
  let rr : Primrec (fun z : ℕ × ℕ => right z.1) := right_primrec.comp Primrec.fst
  let tail := Primrec.list_drop.comp (Primrec.list_length.comp l)
    (word_primrec.comp (item_primrec.comp (r.comp Primrec.snd) (Primrec.const 1)))
  have ha := Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.list_append.comp l tail))
    (Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.list_append.comp rr tail))
      (active_primrec.comp Primrec.fst))
  exact Primrec.ite (Primrec.eq.comp (f.comp Primrec.snd) (Primrec.const 2)) ha (hc.comp
    Primrec.fst)

noncomputable def next (Y : Oracle) (e : OracleCode) (p : ℕ) : ℕ :=
  update p (step Y e (encode (left p)))

theorem next_recursive (Y : Oracle) (e : OracleCode) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun p => Part.some (next Y e p)) := by
  have hs := total_comp (step_recursive Y e) (total_primrec (Primrec.encode.comp left_primrec))
  have hu : Primrec (fun v : ℕ => update (Nat.unpair v).1 (Nat.unpair v).2) :=
    update_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  exact (total_comp (total_primrec hu) (total_pair (total_primrec Primrec.id) hs)).of_eq
    (fun p => by simp [next])

theorem noSplit_unique {A : ℕ → Oracle} {Y : Oracle} {e : OracleCode} {p : Condition}
    (h : ¬ ∃ w, SplitCert Y e (Nat.pair (encode p.left) w)) : UniqueValues A Y e p := by
  intro r s hpr hps n a b ha hb
  by_contra hn
  apply h
  refine ⟨encode [n,encode r.left,encode s.left,a,b],?_⟩
  simpa [SplitCert,item,word] using
    And.intro hpr.1 (And.intro hps.1 (And.intro hn (And.intro ha hb)))

theorem next_spec (A : ℕ → Oracle) (Y : Oracle) (e : OracleCode) (p : ℕ) :
    Extends A (condition p) (condition (next Y e p)) ∧
    (condition (next Y e p)).active = (condition p).active ∧
    (UniqueValues A Y e (condition p) ∨
      (∃ m, SplittingLocation Y e (condition p).left m) ∨
      ∃ n, ∀ q, Extends A (condition (next Y e p)) q →
        ∀ a, a ∉ CommonIdeal.run Y e q.left n) := by
  let out := step Y e (encode (left p))
  have hs := step_spec Y e (encode (left p))
  change Accept Y e (Nat.pair (encode (left p)) out) at hs
  simp only [Accept,Nat.unpair_pair] at hs
  rcases hs with ⟨ht,hn⟩ | ⟨ht,hpoint⟩ | ⟨ht,hdiv⟩
  · have htag : (Nat.unpair out).1 ≠ 2 := by omega
    have he : condition (next Y e p) = condition p := by
      simp only [next,← show out = step Y e (encode (left p)) from rfl,update,ite_eq_right
        htag,condition_code]
    rw [he]
    exact ⟨extends_refl A _,rfl,Or.inl (noSplit_unique hn)⟩
  · have htag : (Nat.unpair out).1 ≠ 2 := by omega
    have he : condition (next Y e p) = condition p := by
      simp only [next,← show out = step Y e (encode (left p)) from rfl,update,ite_eq_right
        htag,condition_code]
    rw [he]
    let w := (Nat.unpair out).2
    simp only [PointCert,Nat.unpair_pair,word,encodek,Option.getD_some] at hpoint
    refine ⟨extends_refl A _,rfl,Or.inr (Or.inl ⟨item w 2,?_⟩)⟩
    exact ⟨word (item w 1),(item w 3).bodd,item w 0,item w 4,item w 5,hpoint⟩
  · let w := (Nat.unpair out).2
    let q := word (item w 1)
    have hpq : left p <+: q := by simpa [q,w,DivCert,word] using hdiv.1
    have heq : left p ++ q.drop (left p).length = q := by
      rw [List.prefix_iff_eq_take] at hpq
      conv_lhs => lhs; rw [hpq]
      exact List.take_append_drop _ _
    let r := append (condition p) (q.drop (left p).length)
    have he : condition (next Y e p) = r := by
      simp only [next,← show out = step Y e (encode (left p)) from rfl,update,ite_eq_left
        ht,condition_code]
      rfl
    have hleft : r.left = q := heq
    rw [he]
    refine ⟨append_extends A _ _,rfl,Or.inr (Or.inr ⟨item w 0,?_⟩)⟩
    intro t hrt a ha
    have hn : ¬ ConvergesAbove Y e w := by simpa only [Nat.unpair_pair] using hdiv.2
    apply hn
    refine ⟨encode t.left,?_,?_⟩
    · change q <+: word (encode t.left)
      simpa only [word,encodek,Option.getD_some,← hleft] using hrt.1
    · simpa only [word,encodek,Option.getD_some] using ha.1

end TuringRigidity.EffectiveSplitConditions

end OAI
