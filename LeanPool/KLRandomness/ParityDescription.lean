/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineDescription
public import LeanPool.KLRandomness.StageCodeSearch
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Affine-description tests on the two coordinate halves

A finite truth-table check verifies that an affine event depends only on
one parity of coordinates. Its pullback to that coordinate half has the
same fair-coin measure. The resulting Martin-Löf tests use the original
description strings, without a compiler or an increase in description length.
-/

@[expose] public section

namespace Klr.ParityDescription

open MeasureTheory AffineCode SparseSearch
open scoped ENNReal

/-- One of the two coordinate halves of a binary sequence. -/
def half (b : Fin 2) (X : Cantor) : Cantor := fun n => X (2 * n + b.val)

/-- Insert a sequence in the indicated parity and put zeroes elsewhere. -/
def fill (b : Fin 2) (Y : Cantor) : Cantor :=
  fun k => if k % 2 = b.val then Y (k / 2) else false

/-- Retain one parity of a sequence and put zeroes elsewhere. -/
def mask (b : Fin 2) (X : Cantor) : Cantor :=
  fun k => if k % 2 = b.val then X k else false

theorem fill_half (b : Fin 2) (X : Cantor) : fill b (half b X) = mask b X := by
  funext k
  simp only [fill, half, mask]
  split_ifs with hk
  · congr 1
    omega
  · rfl

theorem half_fill (b : Fin 2) (X : Cantor) : half b (fill b X) = X := by
  funext n
  have hb := b.isLt
  have hm : (2 * n + b.val) % 2 = b.val := by omega
  have hd : (2 * n + b.val) / 2 = n := by omega
  simp [half, fill, hm, hd]

theorem measurable_half (b : Fin 2) : Measurable (half b) := by
  unfold half
  fun_prop

theorem measurable_fill (b : Fin 2) : Measurable (fill b) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k % 2 = b.val <;> simp only [fill, hk, ite_true, ite_false] <;> fun_prop

/-- Injective coordinate selection preserves the fair product law. -/
theorem fairCoin_map_half (b : Fin 2) : fairCoin.map (half b) = fairCoin := by
  unfold fairCoin half
  exact Measure.map_infinitePi_infinitePi_of_inj (by
    intro i j hij
    change 2 * i + b.val = 2 * j + b.val at hij
    omega)

/-- The finite version of `mask`. -/
def maskWord (b : Fin 2) (s : List Bool) : List Bool :=
  ScanRule.inputPrefix (mask b (fun k => s.getD k false)) s.length

/-- Interleave a finite word with zeroes in the other parity. -/
def expandWord (b : Fin 2) (s : List Bool) : List Bool :=
  ScanRule.inputPrefix (fill b (fun k => s.getD k false)) (2 * s.length)

@[simp] theorem length_maskWord (b : Fin 2) (s : List Bool) :
    (maskWord b s).length = s.length := by simp [maskWord]

@[simp] theorem length_expandWord (b : Fin 2) (s : List Bool) :
    (expandWord b s).length = 2 * s.length := by simp [expandWord]

theorem computable_maskWord (b : Fin 2) : Computable (maskWord b) := by
  have hc : PrimrecPred (fun p : List Bool × ℕ => p.2 % 2 = b.val) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
      (Primrec.const b.val)
  have hg : Primrec (fun p : List Bool × ℕ =>
      if p.2 % 2 = b.val then p.1.getD p.2 false else false) :=
    Primrec.ite hc ((Primrec.list_getD false).comp Primrec.fst Primrec.snd)
      (Primrec.const false)
  exact (Primrec.list_map (Primrec.list_range.comp Primrec.list_length) hg.to₂).to_comp

theorem computable_expandWord (b : Fin 2) : Computable (expandWord b) := by
  have hc : PrimrecPred (fun p : List Bool × ℕ => p.2 % 2 = b.val) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
      (Primrec.const b.val)
  have hg : Primrec (fun p : List Bool × ℕ =>
      if p.2 % 2 = b.val then p.1.getD (p.2 / 2) false else false) :=
    Primrec.ite hc ((Primrec.list_getD false).comp Primrec.fst
      (Primrec.nat_div.comp Primrec.snd (Primrec.const 2))) (Primrec.const false)
  exact (Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length))
    hg.to₂).to_comp

private theorem inputPrefix_congr (X Y : Cantor) (n : ℕ)
    (h : ∀ k < n, X k = Y k) : ScanRule.inputPrefix X n = ScanRule.inputPrefix Y n := by
  unfold ScanRule.inputPrefix
  apply List.map_congr_left
  intro k hk
  exact h k (List.mem_range.mp hk)

theorem maskWord_inputPrefix (b : Fin 2) (X : Cantor) (n : ℕ) :
    maskWord b (ScanRule.inputPrefix X n) = ScanRule.inputPrefix (mask b X) n := by
  unfold maskWord
  rw [ScanRule.length_inputPrefix]
  apply inputPrefix_congr
  intro k hk
  simp only [mask]
  split_ifs
  · exact ScanRule.getD_inputPrefix X hk
  · rfl

theorem expandWord_inputPrefix (b : Fin 2) (X : Cantor) (n : ℕ) :
    expandWord b (ScanRule.inputPrefix X n) = ScanRule.inputPrefix (fill b X) (2 * n) := by
  unfold expandWord
  rw [ScanRule.length_inputPrefix]
  apply inputPrefix_congr
  intro k hk
  have hd : k / 2 < n := by omega
  simp only [fill]
  split_ifs
  · exact ScanRule.getD_inputPrefix X hd
  · rfl

theorem fill_mem_cylinder_expandWord (b : Fin 2) {X : Cantor} {s : List Bool}
    (hX : X ∈ cylinder s) : fill b X ∈ cylinder (expandWord b s) := by
  intro k hk
  have hk' : k < 2 * s.length := by simpa using hk
  change fill b X k =
    (ScanRule.inputPrefix (fill b (fun j => s.getD j false)) (2 * s.length)).getD k false
  rw [ScanRule.getD_inputPrefix _ hk']
  simp only [fill]
  split_ifs
  · exact (mem_cylinder.mp hX) (k / 2) (by omega)
  · rfl

/-- A finite exhaustive check that deleting the opposite parity preserves acceptance. -/
def supported (b : Fin 2) (c : Data) : Bool :=
  (words (width c)).all (fun s => decide (accepts c s = accepts c (maskWord b s)))

theorem supported_eq_true (b : Fin 2) (c : Data) :
    supported b c = true ↔
      ∀ s : List Bool, s.length = width c → accepts c s = accepts c (maskWord b s) := by
  simp [supported, List.all_eq_true, mem_words_iff]

theorem computable_supported (b : Fin 2) : Computable (supported b) := by
  have ht : Computable (fun p : Data × List Bool =>
      decide (accepts p.1 p.2 = accepts p.1 (maskWord b p.2))) :=
    Primrec.eq.decide.to_comp.comp computable_accepts
      (computable_accepts.comp Computable.fst ((computable_maskWord b).comp Computable.snd))
  exact computable_list_all (computable_words.comp computable_width) ht.to₂

/-- The finite filter implies the corresponding invariance of the infinite event. -/
theorem event_mask_iff (b : Fin 2) {c : Data} (hs : supported b c = true) (X : Cantor) :
    X ∈ event c ↔ mask b X ∈ event c := by
  have h := (supported_eq_true b c).mp hs (ScanRule.inputPrefix X (width c))
    (ScanRule.length_inputPrefix X (width c))
  rw [maskWord_inputPrefix] at h
  rw [← StageFiniteProbability.accepts_code_inputPrefix c (width c) le_rfl X,
    ← StageFiniteProbability.accepts_code_inputPrefix c (width c) le_rfl (mask b X)]
  exact iff_of_eq (congrArg (fun q : Bool => q = true) h)

/-- Event equality suffices for the filter; no special output matrix representation is needed. -/
theorem supported_of_event_eq (b : Fin 2) {c : Data} {B : AffineBlock}
    (he : event c = B.event) (hB : ∀ k ∈ B.support, k % 2 = b.val) :
    supported b c = true := by
  apply (supported_eq_true b c).mpr
  intro s hs
  let X : Cantor := fun k => s.getD k false
  have hp : ScanRule.inputPrefix X (width c) = s := by
    rw [← hs]
    exact StageCodeSearch.inputPrefix_getD s
  rw [← hp, maskWord_inputPrefix]
  apply Bool.eq_iff_iff.mpr
  rw [StageFiniteProbability.accepts_code_inputPrefix c (width c) le_rfl X,
    StageFiniteProbability.accepts_code_inputPrefix c (width c) le_rfl (mask b X), he]
  apply iff_of_eq
  apply B.dependsOn_event
  intro k hk
  simp [mask, hB k hk]

/-- The event on a coordinate half obtained by zero filling the other coordinates. -/
def halfEvent (b : Fin 2) (c : Data) : Set Cantor := fill b ⁻¹' event c

theorem measurableSet_halfEvent (b : Fin 2) (c : Data) : MeasurableSet (halfEvent b c) :=
  (measurableSet_event c).preimage (measurable_fill b)

theorem event_eq_preimage_halfEvent (b : Fin 2) {c : Data} (hs : supported b c = true) :
    event c = half b ⁻¹' halfEvent b c := by
  ext X
  change X ∈ event c ↔ fill b (half b X) ∈ event c
  rw [fill_half]
  exact event_mask_iff b hs X

/-- Deleting irrelevant coordinates preserves the exact probability, not just an upper bound. -/
theorem fairCoin_halfEvent (b : Fin 2) {c : Data} (hs : supported b c = true) :
    fairCoin (halfEvent b c) = fairCoin (event c) := by
  rw [event_eq_preimage_halfEvent b hs,
    ← Measure.map_apply (measurable_half b) (measurableSet_halfEvent b c), fairCoin_map_half]

theorem cylinderUnion_expanded_accepts (b : Fin 2) (c : Data) :
    cylinderUnion (fun s => accepts c (expandWord b s) = true) = halfEvent b c := by
  ext X
  constructor
  · rintro ⟨s, hs, hX⟩
    exact cylinder_subset_event hs (fill_mem_cylinder_expandWord b hX)
  · intro hX
    refine ⟨ScanRule.inputPrefix X (width c), ?_, ScanRule.mem_cylinder_inputPrefix _ _⟩
    change accepts c (expandWord b (ScanRule.inputPrefix X (width c))) = true
    rw [expandWord_inputPrefix]
    exact (StageFiniteProbability.accepts_code_inputPrefix c (2 * width c) (by omega)
      (fill b X)).mpr hX

/-- The finite postprocessing check keeps the original program and its original rank budget. -/
def check (b : Fin 2) (a : ℕ × List Bool × List Bool) (c : Data) : Bool :=
  supported b c && AffineDescription.check (a.1, a.2.1, expandWord b a.2.2) c

theorem check_eq_true (b : Fin 2) (a : ℕ × List Bool × List Bool) (c : Data) :
    check b a c = true ↔ supported b c = true ∧ valid c = true ∧
      2 * a.2.1.length + a.1 + 1 ≤ rank c ∧ accepts c (expandWord b a.2.2) = true := by
  simp [check, AffineDescription.check_eq_true]

theorem computable_check (b : Fin 2) : Computable₂ (check b) := by
  have ht : Computable (fun a : ℕ × List Bool × List Bool =>
      (a.1, a.2.1, expandWord b a.2.2)) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((computable_expandWord b).comp (Computable.snd.comp Computable.snd)))
  exact Primrec.and.to_comp.comp ((computable_supported b).comp Computable.snd)
    (AffineDescription.computable_check.comp (ht.comp Computable.fst) Computable.snd)

/-- The cylinder enumeration for the test on parity `b`. -/
def W (b : Fin 2) (a : ℕ × List Bool × List Bool) : Prop :=
  ∃ c : Data, c ∈ AffineDescription.run a.2.1 ∧ supported b c = true ∧ valid c = true ∧
    2 * a.2.1.length + a.1 + 1 ≤ rank c ∧ accepts c (expandWord b a.2.2) = true

theorem rePred_W (b : Fin 2) : REPred (W b) := by
  let accept (a : ℕ × List Bool × List Bool) : Part Unit :=
    (AffineDescription.run a.2.1).bind fun c =>
      if check b a c then Part.some () else Part.none
  have hp : Computable (fun a : ℕ × List Bool × List Bool => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hfilter : Partrec (fun p : (ℕ × List Bool × List Bool) × Data =>
      if check b p.1 p.2 then Part.some () else Part.none) := by
    have ht : Partrec (fun _ : (ℕ × List Bool × List Bool) × Data => Part.some ()) :=
      (Computable.const ()).partrec
    have hf : Partrec (fun _ : (ℕ × List Bool × List Bool) × Data =>
        (Part.none : Part Unit)) := Partrec.none
    have hc := Partrec.cond (c := fun p : (ℕ × List Bool × List Bool) × Data =>
      check b p.1 p.2) (computable_check b) ht hf
    exact hc.of_eq fun p => by cases check b p.1 p.2 <;> rfl
  have he : Partrec accept := (AffineDescription.partrec_run.comp hp).bind
    (g := fun a c => if check b a c then Part.some () else Part.none) hfilter.to₂
  apply he.dom_re.of_eq
  intro a
  simp only [accept, Part.dom_iff_mem, Part.mem_bind_iff]
  constructor
  · rintro ⟨u, c, hc, hu⟩
    have hcheck : check b a c = true := by
      cases hh : check b a c <;> simp [hh] at hu ⊢
    exact ⟨c, hc, (check_eq_true b a c).mp hcheck⟩
  · rintro ⟨c, hc, hs, hv, hr, ha⟩
    refine ⟨(), c, hc, ?_⟩
    simp [(check_eq_true b a c).mpr ⟨hs, hv, hr, ha⟩]

theorem cylinderUnion_W_eq (b : Fin 2) {n : ℕ} {p : List Bool} {c : Data}
    (hc : c ∈ AffineDescription.run p) (hs : supported b c = true) (hv : valid c = true)
    (hr : 2 * p.length + n + 1 ≤ rank c) :
    cylinderUnion (fun s => W b (n, p, s)) = halfEvent b c := by
  rw [← cylinderUnion_expanded_accepts b c]
  congr 1
  funext s
  apply propext
  constructor
  · rintro ⟨d, hd, _, _, _, ha⟩
    have hdc : d = c := Part.mem_unique hd hc
    simpa only [hdc] using ha
  · intro ha
    exact ⟨c, hc, hs, hv, hr, ha⟩

/-- Each original program retains precisely its original description-measure budget. -/
theorem per_program_bound (b : Fin 2) (n : ℕ) (p : List Bool) :
    fairCoin (cylinderUnion (fun s => W b (n, p, s))) ≤
      (1 / 2 : ℝ≥0∞) ^ (2 * p.length + n + 1) := by
  classical
  by_cases h : ∃ c : Data, c ∈ AffineDescription.run p ∧ supported b c = true ∧
      valid c = true ∧ 2 * p.length + n + 1 ≤ rank c
  · obtain ⟨c, hc, hs, hv, hr⟩ := h
    rw [cylinderUnion_W_eq b hc hs hv hr, fairCoin_halfEvent b hs, fairCoin_event c hv]
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) hr
  · have hempty : cylinderUnion (fun s => W b (n, p, s)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨s, ⟨c, hc, hs, hv, hr, _⟩, _⟩
      exact h ⟨c, hc, hs, hv, hr⟩
    rw [hempty, measure_empty]
    positivity

/-- Both parity-indexed families are actual Martin-Löf tests. -/
theorem exists_martinLofTest (b : Fin 2) :
    ∃ T : MartinLofTest, ∀ n, T.level n = descriptionLevel (W b) n :=
  exists_martinLofTest_of_description_family (rePred_W b) (per_program_bound b)

theorem not_martinLofRandom_half_of_descriptions (b : Fin 2) (X : Cantor)
    (hX : ∀ n, ∃ (p : List Bool) (c : Data), c ∈ AffineDescription.run p ∧
      supported b c = true ∧ valid c = true ∧
      2 * p.length + n + 1 ≤ rank c ∧ X ∈ event c) :
    ¬MartinLofRandom (half b X) := by
  apply not_martinLofRandom_of_descriptions (rePred_W b) (per_program_bound b)
  intro n
  obtain ⟨p, c, hc, hs, hv, hr, hmem⟩ := hX n
  refine ⟨p, ?_⟩
  rw [cylinderUnion_W_eq b hc hs hv hr]
  change fill b (half b X) ∈ event c
  rw [fill_half]
  exact (event_mask_iff b hs X).mp hmem

/-- Alternating parity-supported blocks with the original stage descriptions
make either coordinate half fail its own effective test. -/
theorem not_martinLofRandom_half_of_blocks (B : ℕ → AffineBlock)
    (hparity : ∀ j, ∀ k ∈ (B j).support, k % 2 = j % 2)
    (hprogram : ∀ j, ∃ (p : List Bool) (c : Data), c ∈ AffineDescription.run p ∧
      valid c = true ∧ 2 * p.length + j + 1 ≤ rank c ∧ event c = (B j).event)
    (X : Cantor) (hX : ∀ j, X ∈ (B j).event) (b : Fin 2) :
    ¬MartinLofRandom (half b X) := by
  apply not_martinLofRandom_half_of_descriptions b X
  intro n
  obtain ⟨p, c, hc, hv, hr, he⟩ := hprogram (2 * n + b.val)
  have hb := b.isLt
  refine ⟨p, c, hc, supported_of_event_eq b he ?_, hv, ?_, ?_⟩
  · intro k hk
    have hp := hparity (2 * n + b.val) k hk
    omega
  · omega
  · rw [he]
    exact hX _

theorem both_halves_not_martinLofRandom_of_blocks (B : ℕ → AffineBlock)
    (hparity : ∀ j, ∀ k ∈ (B j).support, k % 2 = j % 2)
    (hprogram : ∀ j, ∃ (p : List Bool) (c : Data), c ∈ AffineDescription.run p ∧
      valid c = true ∧ 2 * p.length + j + 1 ≤ rank c ∧ event c = (B j).event)
    (X : Cantor) (hX : ∀ j, X ∈ (B j).event) :
    ¬MartinLofRandom (half 0 X) ∧ ¬MartinLofRandom (half 1 X) :=
  ⟨not_martinLofRandom_half_of_blocks B hparity hprogram X hX 0,
    not_martinLofRandom_half_of_blocks B hparity hprogram X hX 1⟩

end Klr.ParityDescription
