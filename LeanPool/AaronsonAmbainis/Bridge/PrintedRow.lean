/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Positivity
public import LeanPool.AaronsonAmbainis.Bridge.Poly
public import LeanPool.AaronsonAmbainis.Bridge.Transport
public import LeanPool.AaronsonAmbainis.Bridge.ZeroOne

/-!
# `RowBound` and Theorem 1.7 of arXiv:2410.19062 as printed

Source: A. Agarwal and S. Ben-David, *Oracle separations for the quantum-classical polynomial
hierarchy*, arXiv:2410.19062 (version 2), Theorem 1.7:

  Let `f : {0,1}^n → [0,1]` be a real-valued function which can be expressed as a polynomial of
  degree at most `d`. Then there is an assignment of weights `{c_{x,i}}_{x∈{0,1}^n, i∈[n]}` to
  inputs `x` and positions `i ∈ [n]` such that for all `x, y ∈ {0,1}^n`, we have
  `∑_{i : x_i ≠ y_i} c_{x,i} ≥ |f(x) - f(y)|`  and  `∑_{i=1}^n c_{x,i} ≤ (π²/4) d²`.

`FbsDegPrinted` transcribes this sentence with Mathlib notions only (no definition of `Defs.lean`
is used) and in its weakest reading: only `n ≥ 1`, only `d ≥ 1`, no sign condition on the weights
in the conclusion. `FbsDegPrintedML` is the same with the narrowest reading of the hypothesis (a
multilinear polynomial in the `0/1` variables with no monomial of size `> d`).

Result: `RowBound ↔ FbsDegPrinted ↔ FbsDegPrintedML`. So the hypothesis `RowBound` asks for
nothing beyond the printed theorem. Also: a `RowBound` weight system is automatically nonnegative
(`weights_nonneg_of_row`).
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

/-- The conclusion of the printed theorem for one function, written with Mathlib notions only. -/
def PrintedConcl {n : ℕ} (f : (Fin n → Bool) → ℝ) (d : ℕ) : Prop :=
  ∃ c : (Fin n → Bool) → Fin n → ℝ,
    (∀ x y, ∑ i ∈ univ.filter (fun i => x i ≠ y i), c x i ≥ |f x - f y|) ∧
    (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

/-- Theorem 1.7 of arXiv:2410.19062 as printed, for `n ≥ 1` and `d ≥ 1` ("can be expressed as a
polynomial of degree at most `d`": some real polynomial of total degree `≤ d` agrees with `f` on
`{0,1}^n`). -/
def FbsDegPrinted : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
      ∀ x, f x = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) →
    PrintedConcl f d

/-- Theorem 1.7 of arXiv:2410.19062 with the narrowest reading of the hypothesis: `f` is a
multilinear polynomial in the `0/1` variables with no monomial of size `> d`. -/
def FbsDegPrintedML : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ a : Finset (Fin n) → ℝ, (∀ S, d < S.card → a S = 0) ∧
      ∀ x, f x = ∑ S, a S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)) →
    PrintedConcl f d

/-- The printed conclusion is literally the conclusion of `RowBound`. -/
theorem printedConcl_iff {n : ℕ} (f : Cube (Fin n) → ℝ) (d : ℕ) :
    PrintedConcl f d ↔ ∃ c : Cube (Fin n) → Fin n → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2) :=
  Iff.rfl

/-- For a constant function the conclusion holds with zero weights, for every `d`. -/
theorem printedConcl_of_const {n : ℕ} {f : (Fin n → Bool) → ℝ} (h : ∀ x y, f x = f y) (d : ℕ) :
    PrintedConcl f d := by
  refine ⟨fun _ _ => 0, fun x y => ?_, fun x => ?_⟩
  · rw [h x y, sub_self, abs_zero]
    simp
  · simp only [Finset.sum_const_zero]
    positivity

/-- The cases `n = 0` and `d = 0` of `RowBoundFin` are trivially true, so the statement
restricted to `n ≥ 1`, `d ≥ 1` already gives `RowBoundFin`. -/
theorem rowBoundFin_of_restricted
    (h : ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : Cube (Fin n) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      HasDegreeLE f d → PrintedConcl f d) : RowBoundFin := by
  intro n d f hf hdeg
  refine (printedConcl_iff f d).mp ?_
  by_cases hd : d = 0
  · subst hd
    exact printedConcl_of_const (hasDegreeLE_zero_const hdeg) 0
  by_cases hn : n = 0
  · subst hn
    exact printedConcl_of_const (fun x y => congrArg f (Subsingleton.elim x y)) d
  exact h n d (Nat.one_le_iff_ne_zero.mpr hn) (Nat.one_le_iff_ne_zero.mpr hd) f hf hdeg

/-- The printed theorem implies the hypothesis `RowBound`. -/
theorem rowBound_of_printed (h : FbsDegPrinted) : RowBound :=
  rowBound_of_fin (rowBoundFin_of_restricted
    (fun n d hn hd f hf hdeg => h n d hn hd f hf (hasDegreeLE_iff_poly_zo.mp hdeg)))

/-- The printed theorem in its narrowest reading implies the hypothesis `RowBound`. -/
theorem rowBound_of_printedML (h : FbsDegPrintedML) : RowBound :=
  rowBound_of_fin (rowBoundFin_of_restricted
    (fun n d hn hd f hf hdeg => h n d hn hd f hf (hasDegreeLE_iff_01.mp hdeg)))

/-- Conversely `RowBound` gives the printed theorem (so it says neither more nor less). -/
theorem printed_of_rowBound (h : RowBound) : FbsDegPrinted :=
  fun n d _ _ f hf hp =>
    (printedConcl_iff f d).mpr (h (Fin n) d f hf (hasDegreeLE_iff_poly_zo.mpr hp))

theorem printedML_of_rowBound (h : RowBound) : FbsDegPrintedML :=
  fun n d _ _ f hf hp =>
    (printedConcl_iff f d).mpr (h (Fin n) d f hf (hasDegreeLE_iff_01.mpr hp))

/-- `RowBound` is equivalent to Theorem 1.7 of arXiv:2410.19062 as printed. -/
theorem rowBound_iff_printed : RowBound ↔ FbsDegPrinted :=
  ⟨printed_of_rowBound, rowBound_of_printed⟩

/-- `RowBound` is equivalent to the printed theorem in its narrowest reading. -/
theorem rowBound_iff_printedML : RowBound ↔ FbsDegPrintedML :=
  ⟨printedML_of_rowBound, rowBound_of_printedML⟩

/-- Weights satisfying the first condition of `RowBound` are nonnegative (take `y = x^i`). -/
theorem weights_nonneg_of_row {ι : Type*} [Fintype ι] {f : Cube ι → ℝ}
    {c : Cube ι → ι → ℝ} (h : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) (x : Cube ι)
    (i : ι) : 0 ≤ c x i := by
  classical
  have h1 := h x (flipSet x {i})
  rw [diffSet_flipSet, Finset.sum_singleton] at h1
  exact (abs_nonneg _).trans h1

/-- So `RowBound` implies its own strengthening with nonnegative weights. -/
theorem rowBound_nonneg (h : RowBound) (ι : Type) [Fintype ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hdeg : HasDegreeLE f d) :
    ∃ c : Cube ι → ι → ℝ, (∀ x i, 0 ≤ c x i) ∧
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2) := by
  classical
  obtain ⟨c, h1, h2⟩ := h ι d f hf hdeg
  exact ⟨c, weights_nonneg_of_row h1, h1, h2⟩

end AaronsonAmbainis.Bridge
