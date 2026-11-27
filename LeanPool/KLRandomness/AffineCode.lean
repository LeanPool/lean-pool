/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.EffectiveScan
public import LeanPool.KLRandomness.FiniteStage
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum

/-!
# Effective finite affine-system codes

A code gives a width, a row count, Boolean matrix rows, a syndrome, and Boolean
rows of a right-inverse certificate. Missing entries are zero.
A finite Boolean computation checks `A * R = 1`, which proves
full row rank. Equations use the initial input segment; arbitrary finite
supports are represented by inserting zero columns.
-/

@[expose] public section

namespace Klr.AffineCode

open FiniteMeasure MeasureTheory
open scoped ENNReal

/-- An encoding of a binary matrix with its dimensions, syndrome and right inverse. -/
abbrev Data := (ℕ × ℕ) × (List (List Bool) × (List Bool × List (List Bool)))

/-- Number of columns in the encoded parity matrix. -/
def width (c : Data) : ℕ := c.1.1
/-- Rows of the encoded parity matrix. -/
def rows (c : Data) : List (List Bool) := c.2.1
/-- Right-hand side of the encoded affine system. -/
def syndrome (c : Data) : List Bool := c.2.2.1
/-- Rows of the encoded candidate right inverse. -/
def certificate (c : Data) : List (List Bool) := c.2.2.2
/-- Number of equations claimed to be independent by the certificate. -/
def rank (c : Data) : ℕ := c.1.2

/-- Matrix entry with zero returned outside the encoded rows or columns. -/
def entry (a : List (List Bool)) (i j : ℕ) : Bool := (a.getD i []).getD j false

/-- Exclusive-or of the first `n` Boolean values. -/
def parity (p : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => Bool.xor (parity p n) (p n)

theorem value_xor (a b : Bool) :
    boolEquivF2 (Bool.xor a b) = boolEquivF2 a + boolEquivF2 b := by
  cases a <;> cases b <;> decide

theorem value_and (a b : Bool) :
    boolEquivF2 (a && b) = boolEquivF2 a * boolEquivF2 b := by
  cases a <;> cases b <;> simp

theorem value_parity (p : ℕ → Bool) (n : ℕ) :
    boolEquivF2 (parity p n) = ∑ i : Fin n, boolEquivF2 (p i.val) := by
  induction n with
  | zero => simp [parity]
  | succ n ih =>
    rw [parity, value_xor, ih, Fin.sum_univ_castSucc]
    rfl

theorem computable_parity {α : Type*} [Primcodable α] {p : α → ℕ → Bool}
    (hp : Computable₂ p) : Computable (fun a : α × ℕ => parity (p a.1) a.2) := by
  have hs : Computable₂ (fun (a : α × ℕ) (b : ℕ × Bool) => Bool.xor b.2 (p a.1 b.1)) :=
    ((Primrec.dom_bool₂ Bool.xor).to_comp.comp (Computable.snd.comp Computable.snd)
      (hp.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec Computable.snd (Computable.const false) hs).of_eq
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih =>
    simpa only [parity, Nat.rec_add_one] using congrArg (fun b => Bool.xor b (p a.1 n)) ih

theorem computable_entry :
    Computable (fun p : List (List Bool) × (ℕ × ℕ) => entry p.1 p.2.1 p.2.2) := by
  have hr := (Primrec.list_getD ([] : List Bool)).to_comp.comp
    (Computable.fst : Computable (fun p : List (List Bool) × (ℕ × ℕ) => p.1))
    (Computable.fst.comp Computable.snd)
  have hc := (Primrec.list_getD false).to_comp.comp hr (Computable.snd.comp Computable.snd)
  exact hc.of_eq fun _ => rfl

theorem computable_width : Computable width := Computable.fst.comp Computable.fst
theorem computable_rows : Computable rows := Computable.fst.comp Computable.snd
theorem computable_syndrome : Computable syndrome :=
  Computable.fst.comp (Computable.snd.comp Computable.snd)
theorem computable_certificate : Computable certificate :=
  Computable.snd.comp (Computable.snd.comp Computable.snd)
theorem computable_rank : Computable rank := Computable.snd.comp Computable.fst

/-- Entry of the encoded product of the matrix and its right-inverse certificate. -/
def productEntry (c : Data) (i j : ℕ) : Bool :=
  parity (fun k => entry (rows c) i k && entry (certificate c) k j) (width c)

theorem computable_productEntry :
    Computable (fun p : Data × (ℕ × ℕ) => productEntry p.1 p.2.1 p.2.2) := by
  have ha : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ =>
      entry (rows p.1.1) p.1.2.1 p.2) := by
    have hd : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ => p.1.1) :=
      Computable.fst.comp Computable.fst
    have hi : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ => p.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hk : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ => p.2) := Computable.snd
    have hc := computable_entry.comp ((computable_rows.comp hd).pair (hi.pair hk))
    exact hc.of_eq fun _ => rfl
  have hb : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ =>
      entry (certificate p.1.1) p.2 p.1.2.2) := by
    have hd : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ => p.1.1) :=
      Computable.fst.comp Computable.fst
    have hj : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ => p.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hk : Computable (fun p : (Data × (ℕ × ℕ)) × ℕ => p.2) := Computable.snd
    have hc := computable_entry.comp ((computable_certificate.comp hd).pair (hk.pair hj))
    exact hc.of_eq fun _ => rfl
  have hp := Primrec.and.to_comp.comp ha hb
  have hw : Computable (fun p : Data × (ℕ × ℕ) => width p.1) :=
    computable_width.comp Computable.fst
  have hc := (computable_parity (p := fun p : Data × (ℕ × ℕ) => fun k =>
    entry (rows p.1) p.2.1 k && entry (certificate p.1) k p.2.2) hp).comp
      (Computable.id.pair hw)
  exact hc.of_eq fun _ => rfl

/-- Finite verification of a supplied right inverse. -/
def valid (c : Data) : Bool :=
  EffectiveScan.boundedAll (fun i => EffectiveScan.boundedAll
    (fun j => decide (productEntry c i j = decide (i = j))) (rank c)) (rank c)

theorem valid_eq_true (c : Data) : valid c = true ↔
    ∀ i < rank c, ∀ j < rank c, productEntry c i j = decide (i = j) := by
  simp only [valid, EffectiveScan.boundedAll_eq_true, decide_eq_true_eq]

theorem computable_valid : Computable valid := by
  have hp : Computable (fun p : (Data × ℕ) × ℕ =>
      decide (productEntry p.1.1 p.1.2 p.2 = decide (p.1.2 = p.2))) := by
    have hd : Computable (fun p : (Data × ℕ) × ℕ => p.1.1) :=
      Computable.fst.comp Computable.fst
    have hrow : Computable (fun p : (Data × ℕ) × ℕ => p.1.2) :=
      Computable.snd.comp Computable.fst
    have hcol : Computable (fun p : (Data × ℕ) × ℕ => p.2) := Computable.snd
    have he := computable_productEntry.comp (hd.pair (hrow.pair hcol))
    have hi := Primrec.eq.decide.to_comp.comp hrow hcol
    have hc := Primrec.eq.decide.to_comp.comp he hi
    exact hc.of_eq fun _ => rfl
  have hr : Computable (fun p : Data × ℕ => rank p.1) :=
    computable_rank.comp Computable.fst
  have inner := (EffectiveScan.computable_boundedAll
    (p := fun p : Data × ℕ => fun j =>
      decide (productEntry p.1 p.2 j = decide (p.2 = j))) hp).comp (Computable.id.pair hr)
  have hc := (EffectiveScan.computable_boundedAll
    (p := fun c : Data => fun i => EffectiveScan.boundedAll
      (fun j => decide (productEntry c i j = decide (i = j))) (rank c)) inner).comp
    (Computable.id.pair computable_rank)
  exact hc.of_eq fun _ => rfl

/-- Parity matrix over the two-element field read from the code. -/
def matrix (c : Data) : Matrix (Fin (rank c)) (Fin (width c)) (ZMod 2) :=
  fun i j => boolEquivF2 (entry (rows c) i.val j.val)

/-- Candidate right inverse over the two-element field read from the code. -/
def rightMatrix (c : Data) : Matrix (Fin (width c)) (Fin (rank c)) (ZMod 2) :=
  fun i j => boolEquivF2 (entry (certificate c) i.val j.val)

/-- Encoded syndrome interpreted as a vector over the two-element field. -/
def syndromeVector (c : Data) : Fin (rank c) → ZMod 2 :=
  fun i => boolEquivF2 ((syndrome c).getD i.val false)

theorem value_productEntry (c : Data) (i j : Fin (rank c)) :
    boolEquivF2 (productEntry c i.val j.val) = (matrix c * rightMatrix c) i j := by
  simp only [productEntry, value_parity, value_and, Matrix.mul_apply, matrix, rightMatrix]

theorem valid_iff_right_inverse (c : Data) :
    valid c = true ↔ matrix c * rightMatrix c = 1 := by
  rw [valid_eq_true]
  constructor
  · intro h
    ext i j
    rw [← value_productEntry, h i.val i.isLt j.val j.isLt]
    by_cases he : i = j
    · subst j
      simp
    · have hv : i.val ≠ j.val := fun h => he (Fin.ext h)
      simp [hv, he]
  · intro h i hi j hj
    apply boolEquivF2.injective
    rw [value_productEntry c ⟨i, hi⟩ ⟨j, hj⟩, h]
    by_cases he : i = j
    · subst j
      simp
    · simp [he, Fin.ext_iff]

theorem surjective_of_valid (c : Data) (hc : valid c = true) :
    Function.Surjective (matrix c).mulVecLin := by
  intro y
  refine ⟨Matrix.mulVec (rightMatrix c) y, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, (valid_iff_right_inverse c).mp hc,
    Matrix.one_mulVec]

/-- The actual finite affine event decoded from this system. -/
def event (c : Data) : Set Cantor :=
  FiniteStage.affineEvent (fun i : Fin (width c) => i.val) (matrix c).mulVecLin (syndromeVector c)

theorem measurableSet_event (c : Data) : MeasurableSet (event c) :=
  FiniteStage.measurableSet_affineEvent _ _ _

/-- The verified rank determines the exact measure of every decoded syndrome event. -/
theorem fairCoin_event (c : Data) (hc : valid c = true) :
    fairCoin (event c) = (1 / 2 : ℝ≥0∞) ^ rank c := by
  have hs := surjective_of_valid c hc
  have hd := (matrix c).mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hd
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hr : rank c ≤ width c := by omega
  change fairCoin {X | coordinateValues (fun i : Fin (width c) => i.val) X ∈
    {x | (matrix c).mulVecLin x = syndromeVector c}} = _
  rw [fairCoin_coordinate_event_f2 _ Fin.val_injective]
  simp only [Fintype.card_fin]
  change (Nat.card (Affine.Fiber (matrix c).mulVecLin (syndromeVector c)) : ℝ≥0∞) * _ = _
  rw [Affine.card_binary_fiber _ hs, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (1 / 2 : ℝ≥0∞) ^ width c =
      (1 / 2 : ℝ≥0∞) ^ (width c - rank c) * (1 / 2 : ℝ≥0∞) ^ rank c := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [hp, ← mul_assoc, ← mul_pow]
  have htwo : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
    simpa only [one_div] using ENNReal.mul_inv_cancel
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  rw [htwo, one_pow, one_mul]

end Klr.AffineCode
