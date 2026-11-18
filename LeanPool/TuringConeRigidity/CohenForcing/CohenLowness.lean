/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenLowness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenHalting
public import LeanPool.TuringConeRigidity.CohenForcing.CohenCompleteness

/-!
# Cohen Lowness
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenLowness
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenHalting EffectiveCohen EffectiveWitness

theorem recursive_comp_total {Y : Oracle} {P : ℕ → Prop} {f : ℕ → ℕ}
    (hP : RecursivePred Y P)
    (hf : Nat.RecursiveIn {oracleFunction Y} (fun x => Part.some (f x))) :
    RecursivePred Y (fun x => P (f x)) := by
  classical
  exact total_comp hP hf

theorem prefix_recursive (G : Oracle) : RecursivePred G (fun p => Prefix G (word p)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hquery : Nat.RecursiveIn {oracleFunction G} (fun v => Part.some (bit (G (Nat.unpair v).2)))
    := by
    have hq : Nat.RecursiveIn {oracleFunction G} (oracleFunction G) := .oracle _
      (Set.mem_singleton _)
    exact total_comp (f := fun input => bit (G input)) hq (total_primrec r)
  have hv := total_pair hquery (total_primrec (bit_primrec.comp
    ((Primrec.list_getD false).comp (word_primrec.comp f) r)))
  have he : Primrec (fun v : ℕ => if (Nat.unpair v).1 = (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp f r) (Primrec.const 1) (Primrec.const 0)
  have hh : RecursivePred G (fun v => G (Nat.unpair v).2 = (word (Nat.unpair v).1).getD
    (Nat.unpair v).2 false) := by
    exact (total_comp (total_primrec he) hv).of_eq (fun v => by
      simp only [Nat.unpair_pair]
      have hb (a b : Bool) : bit a = bit b ↔ a = b := by cases a <;> cases b <;> simp [bit]
      simp only [hb]
      split <;> rfl)
  simpa only [Prefix,Nat.unpair_pair] using
    recursive_bounded_all hh (Primrec.list_length.comp word_primrec)

/-- Some extension of the coded word admits a halting computation certificate. -/
def Extension (Y : Oracle) (x p : ℕ) : Prop :=
  ∃ q, word p <+: word q ∧ OpenHalts Y x (encode (word q))

theorem extension_sigma (Y : Oracle) : Sigma Y 1 (fun v => Extension Y (Nat.unpair v).1
  (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := EncodedForcing.prefix_recursive Y (word_primrec.comp (r.comp f)) (word_primrec.comp r)
  have hh := (openHalts_sigma Y).comp (Primrec₂.natPair.comp (f.comp f)
    (Primrec.encode.comp (word_primrec.comp r)))
  simpa only [Extension,Nat.unpair_pair] using ((Form.raise (n := 0) (s := true) hp).and hh).ex

/-- The oracle has a finite prefix that either certifies halting or excludes every halting
extension. -/
def Deciding (Y G : Oracle) (v : ℕ) : Prop :=
  Prefix G (word (Nat.unpair v).2) ∧
    (OpenHalts Y (Nat.unpair v).1 (encode (word (Nat.unpair v).2)) ∨
      ¬ Extension Y (Nat.unpair v).1 (Nat.unpair v).2)

theorem deciding_recursive {Y G : Oracle} (hG : Reduces G (jump Y)) :
    RecursivePred (jump Y) (Deciding Y G) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := recursive_comp (recursive_transfer (prefix_recursive G) hG) r
  have hh := recursive_comp (form_recursive (openHalts_sigma Y))
    (Primrec₂.natPair.comp f (Primrec.encode.comp (word_primrec.comp r)))
  have hn := recursive_not (form_recursive (extension_sigma Y))
  unfold Deciding
  simpa only [Nat.unpair_pair] using recursive_and hp (Form.or (n := 0) (s := true) hh hn)

theorem deciding_total {Y G : Oracle} (hG : OneGeneric Y G) : ∀ x, ∃ p, Deciding Y G (Nat.pair x
  p) := by
  intro x
  have hh := (openHalts_sigma Y).comp (Primrec₂.natPair.comp (Primrec.const x) Primrec.id)
  obtain ⟨p,hp,hd⟩ := hG.decides hh
  refine ⟨encode p,?_,?_⟩
  · simpa only [Prefix,Nat.unpair_pair,word,encodek,Option.getD_some] using hp
  · simp only [Nat.unpair_pair] at hd
    simp only [Nat.unpair_pair,word,encodek,Option.getD_some]
    rcases hd with hd | hd
    · exact Or.inl hd
    · refine Or.inr ?_
      rintro ⟨q,hpq,hq⟩
      exact hd (word q) (by simpa [word] using hpq) hq

theorem deciding_correct {Y G : Oracle} {x p : ℕ} (h : Deciding Y G (Nat.pair x p)) :
    OpenHalts Y x (encode (word p)) ↔ Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2 := by
  obtain ⟨hp,hd⟩ := h
  simp only [Nat.unpair_pair] at hp hd
  refine ⟨openHalts_sound hp,fun hh => ?_⟩
  rcases hd with hd | hd
  · exact hd
  · exfalso
    apply hd
    obtain ⟨m,hm⟩ := openHalts_complete hh
    let n := max m (word p).length
    have hpm : word p <+: initial G n := by
      rw [prefix_initial hp]
      exact initial_mono G (le_max_right _ _)
    exact ⟨encode (initial G n),by simpa [word] using hpm,
      by simpa [word] using openHalts_mono (initial_mono G (le_max_left _ _)) hm⟩

theorem oneGeneric_low {Y G : Oracle} (hrec : Reduces G (jump Y)) (hgen : OneGeneric Y G) :
    Reduces (jump (join Y G)) (jump Y) := by
  let D := Deciding Y G
  let ht := deciding_total hgen
  let pick : ℕ → ℕ := least D ht
  have hpick : Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (pick x)) :=
    least_recursive (deciding_recursive hrec) ht
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hin := total_pair (total_primrec Primrec.id)
    (total_comp (total_primrec (Primrec.encode.comp word_primrec)) hpick)
  have hh := recursive_comp_total (form_recursive (openHalts_sigma Y)) hin
  apply RecursiveIn.iff_nat.mpr
  apply hh.of_eq
  intro x
  have he := deciding_correct (least_spec D ht x)
  classical
  simp only [Nat.unpair_pair]
  change Part.some (if OpenHalts Y x (encode (word (pick x))) then 1 else 0) = _
  simp only [pick,he,oracleFunction,jump,Bool.decide_iff]

theorem relative_low_generic (Y : Oracle) : ∃ G : Oracle,
    Reduces G (jump Y) ∧ OneGeneric Y G ∧ degree (jump (join Y G)) = degree (jump Y) := by
  refine ⟨generic Y,generic_reduces Y,generic_oneGeneric Y,?_⟩
  exact (degree_eq_iff _ _).mpr ⟨oneGeneric_low (generic_reduces Y) (generic_oneGeneric Y),
    jump_mono (reduces_join_left Y (generic Y))⟩

end TuringRigidity.CohenLowness

end OAI
