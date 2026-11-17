/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingSplitSearch.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingLocations
public import LeanPool.TuringConeRigidity.Effective.PrefixComputability

/-!
# Coding Split Search
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingSplitSearch
open Encodable PrefixComputability CodingLocations

/-- A finite splitting-search witness: word, changed position and bit, input, and two
execution bounds. -/
abbrev Witness := (List Bool × (ℕ × Bool)) × (ℕ × (ℕ × ℕ))

/-- Test two bounded executions for a one-bit output disagreement and return its absolute
position. -/
def finiteTrial (d : Nat.Partrec.Code) (base : List Bool) (L : List ℕ) (w : Witness) : Option ℕ :=
  let a := d.evaln w.2.2.1 (Nat.pair (encode L) (Nat.pair (encode w.1.1) w.2.1))
  let b := d.evaln w.2.2.2 (Nat.pair (encode L) (Nat.pair (encode (w.1.1.set w.1.2.1 w.1.2.2))
    w.2.1))
  if w.1.2.1 < w.1.1.length ∧ a ≠ none ∧ b ≠ none ∧ a.getD 0 ≠ b.getD 0
  then some (base.length + w.1.2.1) else none

theorem finiteTrial_primrec (d : Nat.Partrec.Code) (base : List Bool) : Primrec₂ (finiteTrial d
  base) := by
  let hL : Primrec (fun z : List ℕ × Witness => z.1) := Primrec.fst
  let hu : Primrec (fun z : List ℕ × Witness => z.2.1.1) := Primrec.fst.comp (Primrec.fst.comp
    Primrec.snd)
  let hi : Primrec (fun z : List ℕ × Witness => z.2.1.2.1) := Primrec.fst.comp (Primrec.snd.comp
    (Primrec.fst.comp Primrec.snd))
  let hb : Primrec (fun z : List ℕ × Witness => z.2.1.2.2) := Primrec.snd.comp (Primrec.snd.comp
    (Primrec.fst.comp Primrec.snd))
  let hn : Primrec (fun z : List ℕ × Witness => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp
    Primrec.snd)
  let ht₀ : Primrec (fun z : List ℕ × Witness => z.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))
  let ht₁ : Primrec (fun z : List ℕ × Witness => z.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))
  let hu' := Primrec.list_set.comp hu (hi.pair hb)
  let ha₀ := Nat.Partrec.Code.primrec_evaln.comp
    ((ht₀.pair (Primrec.const d)).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp hL) (Primrec₂.natPair.comp (Primrec.encode.comp
        hu) hn)))
  let ha₁ := Nat.Partrec.Code.primrec_evaln.comp
    ((ht₁.pair (Primrec.const d)).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp hL) (Primrec₂.natPair.comp (Primrec.encode.comp
        hu') hn)))
  exact Primrec.ite ((Primrec.nat_lt.comp hi (Primrec.list_length.comp hu)).and
    (((Primrec.eq.comp ha₀ (Primrec.const none)).not).and
      (((Primrec.eq.comp ha₁ (Primrec.const none)).not).and
        (Primrec.eq.comp (Primrec.option_getD_default.comp ha₀)
          (Primrec.option_getD_default.comp ha₁)).not)))
    (Primrec.option_some.comp (Primrec.nat_add.comp (Primrec.const base.length) hi))
    (Primrec.const none)

/-- Try a coded splitting witness using a finite prefix of the oracle `Y`. -/
def trial (Y : Oracle) (d : Nat.Partrec.Code) (base : List Bool) (z : ℕ) : Option ℕ :=
  finiteTrial d base (oraclePrefix (fun n => CommonIdeal.bit (Y n)) (Nat.unpair z).1)
    ((decode (α := Witness) (Nat.unpair z).2).getD default)

theorem trial_recursive (Y : Oracle) (d : Nat.Partrec.Code) (base : List Bool) :
    Nat.RecursiveIn {oracleFunction Y} (fun z => Part.some (encode (trial Y d base z))) := by
  have hpre := total_comp (prefix_recursive (fun n => CommonIdeal.bit (Y n)))
    (total_primrec (Primrec.fst.comp Primrec.unpair))
  have hw := total_primrec (O := {oracleFunction Y}) (Primrec.snd.comp Primrec.unpair)
  have hrun := total_primrec (O := {oracleFunction Y}) (Primrec.encode.comp
    ((finiteTrial_primrec d base).comp
      (Primrec.option_getD_default.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.option_getD_default.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)))))
  exact (total_comp hrun (total_pair hpre hw)).of_eq (fun z => by simp [trial])

theorem trial_sound (Y : Oracle) (e : OracleCode) (base : List Bool)
    (d : Nat.Partrec.Code)
    (hd : ∀ L w, d.eval (Nat.pair (encode L) w) = CommonIdeal.finiteRun e base L w)
    (z m : ℕ) (h : m ∈ trial Y d base z) : SplittingLocation Y e base m := by
  let L := oraclePrefix (fun n => CommonIdeal.bit (Y n)) (Nat.unpair z).1
  let w := ((decode (α := Witness) (Nat.unpair z).2).getD default)
  change m ∈ finiteTrial d base L w at h
  dsimp only [finiteTrial] at h
  split at h
  next hg =>
    have hm : m = base.length + w.1.2.1 := (Option.mem_some_iff.mp h).symm
    let a := d.evaln w.2.2.1 (Nat.pair (encode L) (Nat.pair (encode w.1.1) w.2.1))
    let b := d.evaln w.2.2.2 (Nat.pair (encode L) (Nat.pair (encode (w.1.1.set w.1.2.1 w.1.2.2))
      w.2.1))
    have ha : a.getD 0 ∈ a := by
      cases ha' : a with
      | none => exact False.elim (hg.2.1 ha')
      | some v => simp
    have hb : b.getD 0 ∈ b := by
      cases hb' : b with
      | none => exact False.elim (hg.2.2.1 hb')
      | some v => simp
    have hva := Nat.Partrec.Code.evaln_sound ha
    have hvb := Nat.Partrec.Code.evaln_sound hb
    rw [hd] at hva hvb
    have hA := (CommonIdeal.finiteRun_approximates Y e base (encode w.1.1) w.2.1).1
      (Nat.unpair z).1 (a.getD 0) hva
    have hB := (CommonIdeal.finiteRun_approximates Y e base
      (encode (w.1.1.set w.1.2.1 w.1.2.2)) w.2.1).1 (Nat.unpair z).1 (b.getD 0) hvb
    rw [hm]
    refine ⟨base ++ w.1.1, w.1.2.2, w.2.1, a.getD 0, b.getD 0,
      List.prefix_append _ _, by omega, by simp; omega, hg.2.2.2, ?_, ?_⟩
    · simpa [BorelGeneric.word] using hA
    · simpa [BorelGeneric.word, List.set_append_right] using hB
  next hg => simp at h

theorem trial_complete (Y : Oracle) (e : OracleCode) (base : List Bool)
    (d : Nat.Partrec.Code)
    (hd : ∀ L w, d.eval (Nat.pair (encode L) w) = CommonIdeal.finiteRun e base L w)
    {m : ℕ} (hm : SplittingLocation Y e base m) : ∃ z, m ∈ trial Y d base z := by
  obtain ⟨s, b, n, a, c, ⟨u, rfl⟩, hbase, hms, hac, ha, hc⟩ := hm
  let i := m - base.length
  have hmi : m = base.length + i := by omega
  have hi : i < u.length := by simp only [List.length_append] at hms; omega
  have hc' : c ∈ CommonIdeal.run Y e (base ++ u.set i b) n := by
    simpa [List.set_append_right _ _ hbase] using hc
  have hau : a ∈ CommonIdeal.run Y e (base ++ BorelGeneric.word (encode u)) n := by
    simpa [BorelGeneric.word] using ha
  have hcu : c ∈ CommonIdeal.run Y e (base ++ BorelGeneric.word (encode (u.set i b))) n := by
    simpa [BorelGeneric.word] using hc'
  obtain ⟨M₀, hM₀⟩ := (CommonIdeal.finiteRun_approximates Y e base (encode u) n).2 a hau
  obtain ⟨M₁, hM₁⟩ := (CommonIdeal.finiteRun_approximates Y e base (encode (u.set i b)) n).2 c hcu
  let M := max M₀ M₁
  have hfa := hM₀ M (Nat.le_max_left _ _)
  have hfc := hM₁ M (Nat.le_max_right _ _)
  dsimp only at hfa hfc
  rw [← hd] at hfa hfc
  obtain ⟨t₀, ht₀⟩ := Nat.Partrec.Code.evaln_complete.mp hfa
  obtain ⟨t₁, ht₁⟩ := Nat.Partrec.Code.evaln_complete.mp hfc
  let w : Witness := ((u, i, b), (n, t₀, t₁))
  refine ⟨Nat.pair M (encode w), ?_⟩
  have ht₀' := Option.mem_def.mp ht₀
  have ht₁' := Option.mem_def.mp ht₁
  simp only [UniformOracle.oraclePrefix] at ht₀' ht₁'
  simp [trial, finiteTrial, oraclePrefix, w, ht₀', ht₁', hi, hac, hmi]

theorem splittingLocations_enumerable (Y : Oracle) (e : OracleCode) (base : List Bool) :
    ∃ E : ℕ → Option ℕ,
      Nat.RecursiveIn {oracleFunction Y} (fun z => Part.some (encode (E z))) ∧
      ∀ m, SplittingLocation Y e base m ↔ ∃ z, m ∈ E z := by
  obtain ⟨d, hd⟩ := CommonIdeal.finiteRun_code e base
  refine ⟨trial Y d base, trial_recursive Y d base, ?_⟩
  intro m
  exact ⟨trial_complete Y e base d hd, fun ⟨z, hz⟩ => trial_sound Y e base d hd z m hz⟩

end TuringRigidity.CodingSplitSearch

end OAI
