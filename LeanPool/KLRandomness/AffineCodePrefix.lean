/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineCode

/-!
# Finite-prefix acceptance for affine-system codes

The checker reads a prefix covering all coordinates of the encoded system.
Its accepted cylinders have union exactly the actual affine event.
-/

@[expose] public section

namespace Klr.AffineCode

open FiniteMeasure

theorem parity_congr (p q : ℕ → Bool) (n : ℕ)
    (h : ∀ k < n, p k = q k) : parity p n = parity q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parity, parity, ih (fun k hk => h k (by omega)), h n (by omega)]

/-- Left-hand side of one parity equation evaluated on an infinite input. -/
def equationValue (c : Data) (X : Cantor) (i : ℕ) : Bool :=
  parity (fun k => entry (rows c) i k && X k) (width c)

theorem value_equationValue (c : Data) (X : Cantor) (i : Fin (rank c)) :
    boolEquivF2 (equationValue c X i.val) =
      (matrix c).mulVecLin (coordinateValues (fun j : Fin (width c) => j.val) X) i := by
  simp only [equationValue, value_parity, value_and, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, matrix, coordinateValues_apply]

theorem mem_event_iff (c : Data) (X : Cantor) :
    X ∈ event c ↔ ∀ i < rank c,
      equationValue c X i = (syndrome c).getD i false := by
  change (matrix c).mulVecLin (coordinateValues _ X) = syndromeVector c ↔ _
  constructor
  · intro h i hi
    apply boolEquivF2.injective
    rw [value_equationValue c X ⟨i, hi⟩, h]
    rfl
  · intro h
    funext i
    rw [← value_equationValue, h i.val i.isLt]
    rfl

/-- Left-hand side on the extension of a finite prefix by zero bits. -/
def rowValue (c : Data) (s : List Bool) (i : ℕ) : Bool :=
  equationValue c (fun k => s.getD k false) i

theorem computable_rowValue :
    Computable (fun p : (Data × List Bool) × ℕ => rowValue p.1.1 p.1.2 p.2) := by
  have hd : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hk : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.2) := Computable.snd
  have hs : Computable (fun p : ((Data × List Bool) × ℕ) × ℕ => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have ha := computable_entry.comp ((computable_rows.comp hd).pair (hi.pair hk))
  have hb := (Primrec.list_getD false).to_comp.comp hs hk
  have hand := Primrec.and.to_comp.comp ha hb
  have hw : Computable (fun p : (Data × List Bool) × ℕ => width p.1.1) :=
    computable_width.comp (Computable.fst.comp Computable.fst)
  have hc := (computable_parity (p := fun p : (Data × List Bool) × ℕ => fun k =>
    entry (rows p.1.1) p.2 k && p.1.2.getD k false) hand).comp
      (Computable.id.pair hw)
  exact hc.of_eq fun _ => rfl

/-- The prefix covers the width and satisfies every encoded equation. -/
def accepts (c : Data) (s : List Bool) : Bool :=
  decide (width c ≤ s.length) && EffectiveScan.boundedAll
    (fun i => decide (rowValue c s i = (syndrome c).getD i false)) (rank c)

theorem accepts_eq_true (c : Data) (s : List Bool) :
    accepts c s = true ↔ width c ≤ s.length ∧
      ∀ i < rank c, rowValue c s i = (syndrome c).getD i false := by
  simp only [accepts, Bool.and_eq_true, decide_eq_true_eq,
    EffectiveScan.boundedAll_eq_true]

theorem computable_accepts : Computable₂ accepts := by
  have hd : Computable (fun p : (Data × List Bool) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hi : Computable (fun p : (Data × List Bool) × ℕ => p.2) := Computable.snd
  have hy := (Primrec.list_getD false).to_comp.comp (computable_syndrome.comp hd) hi
  have he := Primrec.eq.decide.to_comp.comp computable_rowValue hy
  have hr : Computable (fun p : Data × List Bool => rank p.1) :=
    computable_rank.comp Computable.fst
  have hall := (EffectiveScan.computable_boundedAll
    (p := fun p : Data × List Bool => fun i =>
      decide (rowValue p.1 p.2 i = (syndrome p.1).getD i false)) he).comp
        (Computable.id.pair hr)
  have hw : Computable (fun p : Data × List Bool => width p.1) :=
    computable_width.comp Computable.fst
  have hl : Computable (fun p : Data × List Bool => p.2.length) :=
    Computable.list_length.comp Computable.snd
  have hwidth := Primrec.nat_le.decide.to_comp.comp hw hl
  exact (Primrec.and.to_comp.comp hwidth hall).of_eq fun _ => rfl

theorem cylinder_subset_event {c : Data} {s : List Bool} (hs : accepts c s = true) :
    cylinder s ⊆ event c := by
  obtain ⟨hwidth, heq⟩ := (accepts_eq_true c s).mp hs
  intro X hX
  apply (mem_event_iff c X).mpr
  intro i hi
  rw [← heq i hi]
  apply parity_congr
  intro k hk
  rw [(mem_cylinder.mp hX) k (lt_of_lt_of_le hk hwidth)]

theorem accepts_inputPrefix {c : Data} {X : Cantor} (hX : X ∈ event c) :
    accepts c (ScanRule.inputPrefix X (width c)) = true := by
  apply (accepts_eq_true _ _).mpr
  refine ⟨by simp, ?_⟩
  intro i hi
  rw [← (mem_event_iff c X).mp hX i hi]
  apply parity_congr
  intro k hk
  dsimp only
  rw [ScanRule.getD_inputPrefix X hk]

theorem cylinderUnion_accepts (c : Data) :
    cylinderUnion (fun s => accepts c s = true) = event c := by
  ext X
  constructor
  · rintro ⟨s, hs, hX⟩
    exact cylinder_subset_event hs hX
  · intro hX
    exact ⟨ScanRule.inputPrefix X (width c), accepts_inputPrefix hX,
      ScanRule.mem_cylinder_inputPrefix X (width c)⟩

end Klr.AffineCode
