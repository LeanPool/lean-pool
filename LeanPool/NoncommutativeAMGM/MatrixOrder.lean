/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic
public import Mathlib.Analysis.Matrix.Order

/-!
# Loewner order and matrix target statements

The Loewner order on square matrices is Mathlib's scoped matrix order.
The target predicates state the bounds proved in the main theorem modules.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators MatrixOrder

/-- The Mathlib Loewner order on real square matrices. -/
abbrev LoewnerLE {ι : Type*} (A B : Matrix ι ι ℝ) : Prop := A ≤ B

/-- The matrix comparison agrees with Mathlib's scoped order. -/
theorem loewnerLE_iff_le {ι : Type*} {A B : Matrix ι ι ℝ} :
    LoewnerLE A B ↔ A ≤ B :=
  Iff.rfl

theorem loewner_refl {ι : Type*} (A : Matrix ι ι ℝ) : A ≤ A := le_rfl

theorem loewner_trans {ι : Type*} {A B C : Matrix ι ι ℝ}
    (hAB : A ≤ B) (hBC : B ≤ C) : A ≤ C := hAB.trans hBC

theorem loewner_smul {ι : Type*} {A B : Matrix ι ι ℝ} {c : ℝ}
    (h : LoewnerLE A B) (hc : 0 ≤ c) : LoewnerLE (c • A) (c • B) := by
  simpa only [Matrix.le_iff, smul_sub] using h.smul hc

/-- The hypotheses of equation (1), with no commutativity or mean-identity assumption. -/
def Admissible {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i, (A i).PosSemidef) ∧ (∑ i, A i) ≤ (n : ℝ) • 1

/-- Theorem 1.1's full mathematical target. This definition is not a proof of it. -/
def LowerBoundTarget : Prop :=
  ∀ (n m d : ℕ), 1 ≤ m → m ≤ n → 4 * m ^ 2 ≤ n →
    ∀ A : Fin n → Matrix (Fin d) (Fin d) ℝ, Admissible A →
      (-(1 - 1 / (2 * (m : ℝ)))) • 1 ≤ withoutReplacementMean n m A

/-- Theorem 1.2's full mathematical target, with `⌈m/2⌉ = (m+1)/2`. -/
def QuadraticBoundTarget : Prop :=
  ∀ (n m d : ℕ), 1 ≤ m → m ≤ n → 2 * ((m + 1) / 2) ^ 2 ≤ n →
    ∀ A : Fin n → Matrix (Fin d) (Fin d) ℝ, Admissible A →
      (-(1 : Matrix (Fin d) (Fin d) ℝ) ≤ withoutReplacementMean n m A) ∧
      (withoutReplacementMean n m A ≤ 1)

/-- The normalized one-factor sum is PSD. -/
theorem mean_one_posSemidef {n d : ℕ} (hn : 0 < n)
    (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ i, (A i).PosSemidef) :
    (withoutReplacementMean n 1 A).PosSemidef := by
  rw [withoutReplacementMean_one hn]
  exact (Matrix.posSemidef_sum _ (fun i _ ↦ hA i)).smul (by positivity)

/-- The full two-sided inequality at length one, for arbitrary PSD input matrices. -/
theorem mean_one_bounds {n d : ℕ} (hn : 0 < n)
    (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (hA : Admissible A) :
    LoewnerLE (-(1 : Matrix (Fin d) (Fin d) ℝ)) (withoutReplacementMean n 1 A) ∧
    LoewnerLE (withoutReplacementMean n 1 A) 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  constructor
  · simpa [Matrix.le_iff, sub_neg_eq_add] using
      (mean_one_posSemidef hn A hA.1).add Matrix.PosSemidef.one
  · have h := loewner_smul hA.2 (show 0 ≤ (n : ℝ)⁻¹ by positivity)
    simpa [withoutReplacementMean_one hn, smul_smul, hn0] using h

end NoncommutativeAMGM
