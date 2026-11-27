/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineCodePrefix
public import LeanPool.KLRandomness.AffineCodeCoverage
public import LeanPool.KLRandomness.DescriptionBudget
public import LeanPool.KLRandomness.EffectiveNormalization
public import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A concrete affine-description Martin-Löf test

Plain binary strings are interpreted as binary natural numbers encoding a
pair of a Mathlib partial-recursive program and its natural input. A halting
program's output decodes to finite affine data. The verifier, rank threshold and finite
prefix checker are total computable functions. They give a uniformly c.e.
description family with the required measure budget.

This construction supplies the interpreter and test, but makes no short
description claim for the particular systems chosen by the paper's stages.
-/

@[expose] public section

namespace Klr.AffineDescription

open MeasureTheory
open scoped ENNReal

/-- Binary numeral value, with the least significant bit first. -/
def binaryValue (p : List Bool) : ℕ := p.reverse.foldl (fun n b => Nat.bit b n) 0

@[simp] theorem binaryValue_nil : binaryValue [] = 0 := rfl

@[simp] theorem binaryValue_cons (b : Bool) (p : List Bool) :
    binaryValue (b :: p) = Nat.bit b (binaryValue p) := by
  simp [binaryValue, List.foldl_append]

@[simp] theorem binaryValue_bits (n : ℕ) : binaryValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => simp [Nat.bits_append_bit _ _ h, ih]

theorem computable_binaryValue : Computable binaryValue := by
  have hn : Computable (fun p : ℕ × Bool => p.1) := Computable.fst
  have hb : Computable (fun p : ℕ × Bool => p.2) := Computable.snd
  have hdouble := Primrec.nat_mul.to_comp.comp (Computable.const 2) hn
  have hone := Primrec.nat_add.to_comp.comp hdouble (Computable.const 1)
  have hs : Computable₂ (fun n b => Nat.bit b n) := by
    apply (hb.cond hone hdouble).of_eq
    intro p
    cases p.2 <;> simp [Nat.bit]
  exact (computable_list_foldl (fun n b => Nat.bit b n) hs 0).comp
    Primrec.list_reverse.to_comp

/-- The actual Mathlib partial-recursive code designated by the binary program. -/
def programCode (p : List Bool) : Nat.Partrec.Code :=
  Denumerable.ofNat Nat.Partrec.Code (binaryValue p).unpair.1

/-- Numerical input supplied alongside the fixed program header. -/
def programInput (p : List Bool) : ℕ := (binaryValue p).unpair.2

/-- Package a fixed partial-recursive algorithm and a numerical parameter as plain bits. -/
def programFor (e : Nat.Partrec.Code) (n : ℕ) : List Bool :=
  (Nat.pair (Encodable.encode e) n).bits

@[simp] theorem programCode_programFor (e : Nat.Partrec.Code) (n : ℕ) :
    programCode (programFor e n) = e := by
  simp [programCode, programFor, Denumerable.ofNat_encode]

@[simp] theorem programInput_programFor (e : Nat.Partrec.Code) (n : ℕ) :
    programInput (programFor e n) = n := by
  simp [programInput, programFor]

theorem computable_programCode : Computable programCode :=
  (Computable.ofNat Nat.Partrec.Code).comp
    (Computable.fst.comp (Primrec.unpair.to_comp.comp computable_binaryValue))

theorem computable_programInput : Computable programInput :=
  Computable.snd.comp (Primrec.unpair.to_comp.comp computable_binaryValue)

/-- Interpret a natural output as affine data; unused encodings decode to zero data. -/
def decodeOutput (n : ℕ) : AffineCode.Data :=
  (Encodable.decode (α := AffineCode.Data) n).getD default

theorem computable_decodeOutput : Computable decodeOutput :=
  Primrec.option_getD_default.to_comp.comp Computable.decode

@[simp] theorem decodeOutput_encode (c : AffineCode.Data) :
    decodeOutput (Encodable.encode c) = c := by
  simp [decodeOutput]

/-- Run the designated partial-recursive code on its designated input and decode the output. -/
def run (p : List Bool) : Part AffineCode.Data :=
  ((programCode p).eval (programInput p)).map decodeOutput

@[simp] theorem run_programFor (e : Nat.Partrec.Code) (n : ℕ) :
    run (programFor e n) = (e.eval n).map decodeOutput := by
  simp [run]

theorem partrec_run : Partrec run := by
  have he := Nat.Partrec.Code.eval_part.comp computable_programCode computable_programInput
  have hd : Computable₂ (fun (_ : List Bool) (n : ℕ) => decodeOutput n) :=
    computable_decodeOutput.comp Computable.snd
  exact he.map hd

/-- Every finite affine code is the output of some plain binary program.
No length bound is asserted here. -/
theorem exists_program (c : AffineCode.Data) : ∃ p : List Bool, c ∈ run p := by
  refine ⟨programFor Nat.Partrec.Code.id (Encodable.encode c), ?_⟩
  simp

/-- Every finite-support affine block has a successfully evaluated exact description.
The later stage construction must additionally prove a sufficiently small program length. -/
theorem exists_program_of_affineBlock (B : AffineBlock) :
    ∃ (p : List Bool) (c : AffineCode.Data), c ∈ run p ∧
      AffineCode.valid c = true ∧ AffineCode.rank c = B.rank ∧
      AffineCode.event c = B.event := by
  obtain ⟨c, hr, hv, he⟩ := AffineCode.exists_valid_code_of_affineBlock B
  obtain ⟨p, hp⟩ := exists_program c
  exact ⟨p, c, hp, hv, hr, he⟩

/-- The wholly finite filter following a successful program evaluation. -/
def check (a : ℕ × List Bool × List Bool) (c : AffineCode.Data) : Bool :=
  AffineCode.valid c && (decide (2 * a.2.1.length + a.1 + 1 ≤ AffineCode.rank c) &&
    AffineCode.accepts c a.2.2)

theorem check_eq_true (a : ℕ × List Bool × List Bool) (c : AffineCode.Data) :
    check a c = true ↔ AffineCode.valid c = true ∧
      2 * a.2.1.length + a.1 + 1 ≤ AffineCode.rank c ∧
      AffineCode.accepts c a.2.2 = true := by
  simp [check]

theorem computable_check : Computable₂ check := by
  have hd : Computable (fun p : (ℕ × List Bool × List Bool) × AffineCode.Data => p.2) :=
    Computable.snd
  have hn : Computable (fun p : (ℕ × List Bool × List Bool) × AffineCode.Data => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hp : Computable (fun p : (ℕ × List Bool × List Bool) × AffineCode.Data => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun p : (ℕ × List Bool × List Bool) × AffineCode.Data => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hlen := Computable.list_length.comp hp
  have htwice := Primrec.nat_mul.to_comp.comp (Computable.const 2) hlen
  have hbudget := Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp htwice hn) (Computable.const 1)
  have hrank := Primrec.nat_le.decide.to_comp.comp hbudget (AffineCode.computable_rank.comp hd)
  have ha := AffineCode.computable_accepts.comp hd hs
  have hc := Primrec.and.to_comp.comp (AffineCode.computable_valid.comp hd)
    (Primrec.and.to_comp.comp hrank ha)
  exact hc.of_eq fun _ => rfl

/-- The affine-description cylinder enumeration. -/
def W (a : ℕ × List Bool × List Bool) : Prop :=
  ∃ c : AffineCode.Data, c ∈ run a.2.1 ∧ AffineCode.valid c = true ∧
    2 * a.2.1.length + a.1 + 1 ≤ AffineCode.rank c ∧
    AffineCode.accepts c a.2.2 = true

/-- Uniform enumerability follows from actual partial evaluation and the total finite filter. -/
theorem rePred_W : REPred W := by
  let accept (a : ℕ × List Bool × List Bool) : Part Unit :=
    (run a.2.1).bind fun c => if check a c then Part.some () else Part.none
  have hp : Computable (fun a : ℕ × List Bool × List Bool => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hfilter : Partrec (fun p : (ℕ × List Bool × List Bool) × AffineCode.Data =>
      if check p.1 p.2 then Part.some () else Part.none) := by
    have ht : Partrec (fun _ : (ℕ × List Bool × List Bool) × AffineCode.Data =>
        Part.some ()) := (Computable.const ()).partrec
    have hf : Partrec (fun _ : (ℕ × List Bool × List Bool) × AffineCode.Data =>
        (Part.none : Part Unit)) := Partrec.none
    have hc := Partrec.cond (c := fun p : (ℕ × List Bool × List Bool) × AffineCode.Data =>
      check p.1 p.2) computable_check ht hf
    exact hc.of_eq fun p => by cases check p.1 p.2 <;> rfl
  have he : Partrec accept := (partrec_run.comp hp).bind
    (g := fun a c => if check a c then Part.some () else Part.none) hfilter.to₂
  apply he.dom_re.of_eq
  intro a
  simp only [accept, Part.dom_iff_mem, Part.mem_bind_iff]
  constructor
  · rintro ⟨u, c, hc, hu⟩
    have hcheck : check a c = true := by
      cases hh : check a c <;> simp [hh] at hu ⊢
    exact ⟨c, hc, (check_eq_true a c).mp hcheck⟩
  · rintro ⟨c, hc, hv, hr, hs⟩
    refine ⟨(), c, hc, ?_⟩
    simp [(check_eq_true a c).mpr ⟨hv, hr, hs⟩]

/-- A successful verified program enumerates exactly its affine event at every eligible level. -/
theorem cylinderUnion_W_eq {n : ℕ} {p : List Bool} {c : AffineCode.Data}
    (hc : c ∈ run p) (hv : AffineCode.valid c = true)
    (hr : 2 * p.length + n + 1 ≤ AffineCode.rank c) :
    cylinderUnion (fun s => W (n, p, s)) = AffineCode.event c := by
  rw [← AffineCode.cylinderUnion_accepts c]
  congr 1
  funext s
  apply propext
  constructor
  · rintro ⟨d, hd, _, _, hs⟩
    have hdc : d = c := Part.mem_unique hd hc
    simpa only [hdc] using hs
  · intro hs
    exact ⟨c, hc, hv, hr, hs⟩

/-- Every program receives its declared plain-description measure budget. -/
theorem per_program_bound (n : ℕ) (p : List Bool) :
    fairCoin (cylinderUnion (fun s => W (n, p, s))) ≤
      (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1) := by
  classical
  by_cases h : ∃ c : AffineCode.Data, c ∈ run p ∧ AffineCode.valid c = true ∧
      2 * p.length + n + 1 ≤ AffineCode.rank c
  · obtain ⟨c, hc, hv, hr⟩ := h
    rw [cylinderUnion_W_eq hc hv hr, AffineCode.fairCoin_event c hv]
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) hr
  · have hempty : cylinderUnion (fun s => W (n, p, s)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨s, ⟨c, hc, hv, hr, _⟩, _⟩
      exact h ⟨c, hc, hv, hr⟩
    rw [hempty, measure_empty]
    positivity

theorem uniformlyEffectivelyOpen : IsUniformlyEffectivelyOpen (descriptionLevel W) :=
  descriptionLevel_uniform rePred_W

theorem measure_level_le (n : ℕ) :
    fairCoin (descriptionLevel W n) ≤ (1 / 2 : ℝ≥0∞) ^ n :=
  descriptionLevel_measure_le W n (per_program_bound n)

/-- The concrete family is a genuine Martin-Löf test with no decoder or rank-check hypothesis. -/
theorem exists_martinLofTest :
    ∃ T : MartinLofTest, ∀ n, T.level n = descriptionLevel W n :=
  exists_martinLofTest_of_description_family rePred_W per_program_bound

/-- Fix one actual partial-recursive test code representing the description family. -/
noncomputable def test : MartinLofTest := Classical.choose exists_martinLofTest

theorem test_level (n : ℕ) : test.level n = descriptionLevel W n :=
  Classical.choose_spec exists_martinLofTest n

theorem event_subset_level {n : ℕ} {p : List Bool} {c : AffineCode.Data}
    (hc : c ∈ run p) (hv : AffineCode.valid c = true)
    (hr : 2 * p.length + n + 1 ≤ AffineCode.rank c) :
    AffineCode.event c ⊆ descriptionLevel W n := by
  rw [← cylinderUnion_W_eq hc hv hr]
  exact Set.subset_iUnion (fun p : List Bool => cylinderUnion (fun s => W (n, p, s))) p

/-- The remaining application obligation is to produce sufficiently short stage programs. -/
theorem not_martinLofRandom_of_programs {X : Cantor}
    (hX : ∀ n, ∃ (p : List Bool) (c : AffineCode.Data), c ∈ run p ∧
      AffineCode.valid c = true ∧ 2 * p.length + n + 1 ≤ AffineCode.rank c ∧
      X ∈ AffineCode.event c) : ¬MartinLofRandom X := by
  apply not_martinLofRandom_of_descriptions rePred_W per_program_bound
  intro n
  obtain ⟨p, c, hc, hv, hr, hmem⟩ := hX n
  exact ⟨p, by rwa [cylinderUnion_W_eq hc hv hr]⟩

end Klr.AffineDescription
