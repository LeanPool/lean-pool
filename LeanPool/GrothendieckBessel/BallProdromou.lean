/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.RealConvex
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Matrix.PosDef

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The Ball--Prodromou cube quadratic maximum
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Set

namespace OlevskiiGram

/--
A Parseval family spans the whole coordinate space.  This is the frame identity
used in the Ball--Prodromou proof.
-/
theorem parsevalFrame_span_top
    {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ)
    (hparseval : ∀ x : n → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i) :
    Submodule.span ℝ (Set.range u) = ⊤ := by
  apply le_antisymm le_top
  intro x _hx
  have hxsum : (∑ j, realDot x (u j) • u j) = x := by
    ext i
    simpa [Pi.smul_apply] using hparseval x i
  rw [← hxsum]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Parseval identity for the squared norm expressed using `realDot`. -/
theorem parsevalFrame_realDot_self
    {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ)
    (hparseval : ∀ x : n → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i)
    (x : n → ℝ) :
    realDot x x = ∑ j, (realDot x (u j)) ^ 2 := by
  calc
    realDot x x
        = ∑ i, x i * x i := by
          rfl
    _ = ∑ i, x i * (∑ j, realDot x (u j) * u j i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [hparseval x i]
    _ = ∑ i, ∑ j, x i * (realDot x (u j) * u j i) := by
          simp [Finset.mul_sum]
    _ = ∑ j, ∑ i, x i * (realDot x (u j) * u j i) := by
          rw [Finset.sum_comm]
    _ = ∑ j, realDot x (u j) * realDot x (u j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [realDot, Finset.mul_sum, mul_comm, mul_left_comm]
    _ = ∑ j, (realDot x (u j)) ^ 2 := by
          simp [pow_two]

/--
If the active constraints span the whole coordinate space, then at least
`dim` constraints are active.
-/
theorem activeConstraintCount_ge_card_of_span_top
    {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ) (x : n → ℝ)
    (hspan : activeConstraintSpan u x = ⊤) :
    Fintype.card n ≤ activeConstraintCount u x := by
  classical
  let s : Finset ι := activeConstraintIndexSet u x
  let vset : Finset (n → ℝ) := s.image u
  have hactive_eq : activeConstraintVectors u x = (vset : Set (n → ℝ)) := by
    ext v
    constructor
    · rintro ⟨j, rfl, hj⟩
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr
          ⟨j, by simpa [s] using (mem_activeConstraintIndexSet_iff u x j).mpr hj, rfl⟩)
    · intro hv
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hv) with ⟨j, hj, rfl⟩
      exact ⟨j, rfl, (mem_activeConstraintIndexSet_iff u x j).mp (by simpa [s] using hj)⟩
  have hfinrank :
      Module.finrank ℝ (n → ℝ) ≤ vset.card := by
    calc
      Module.finrank ℝ (n → ℝ)
          = Module.finrank ℝ (activeConstraintSpan u x) := by
              rw [hspan, finrank_top]
      _ = Module.finrank ℝ (Submodule.span ℝ (vset : Set (n → ℝ))) := by
              rw [activeConstraintSpan, hactive_eq]
      _ ≤ vset.card := by
              simpa [Set.finrank] using
                (finrank_span_finset_le_card (R := ℝ) vset)
  calc
    Fintype.card n = Module.finrank ℝ (n → ℝ) := by
      rw [Module.finrank_fintype_fun_eq_card]
    _ ≤ vset.card := hfinrank
    _ ≤ s.card := Finset.card_image_le
    _ = activeConstraintCount u x := by
      simp [activeConstraintCount, s]

/-- On the active set, the squared frame coefficients sum to the active count. -/
theorem activeConstraint_sum_sq_eq_count
    {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ) (x : n → ℝ) :
    (∑ j ∈ activeConstraintIndexSet u x, (realDot x (u j)) ^ 2) =
      (activeConstraintCount u x : ℝ) := by
  classical
  calc
    (∑ j ∈ activeConstraintIndexSet u x, (realDot x (u j)) ^ 2)
        = ∑ j ∈ activeConstraintIndexSet u x, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hactive := (mem_activeConstraintIndexSet_iff u x j).mp hj
            calc
              (realDot x (u j)) ^ 2 = |realDot x (u j)| ^ 2 := by
                rw [sq_abs]
              _ = 1 := by
                rw [hactive]
                norm_num
    _ = (activeConstraintCount u x : ℝ) := by
        simp [activeConstraintCount]

/--
The norm-lower step in Ball--Prodromou: a Parseval family and a point whose
active constraints span force `dim ≤ ‖x‖²`.
-/
theorem parsevalFrame_active_norm_lower
    {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ)
    (hparseval : ∀ x : n → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i)
    (x : n → ℝ)
    (hspan : activeConstraintSpan u x = ⊤) :
    (Fintype.card n : ℝ) ≤ realDot x x := by
  classical
  have hcount_nat : Fintype.card n ≤ activeConstraintCount u x :=
    activeConstraintCount_ge_card_of_span_top u x hspan
  have hcount : (Fintype.card n : ℝ) ≤ (activeConstraintCount u x : ℝ) := by
    exact_mod_cast hcount_nat
  have hactive_sum :
      (∑ j ∈ activeConstraintIndexSet u x, (realDot x (u j)) ^ 2) =
        (activeConstraintCount u x : ℝ) :=
    activeConstraint_sum_sq_eq_count u x
  have hsubset_sum :
      (∑ j ∈ activeConstraintIndexSet u x, (realDot x (u j)) ^ 2) ≤
        ∑ j, (realDot x (u j)) ^ 2 := by
    exact Finset.sum_le_univ_sum_of_nonneg fun j => sq_nonneg (realDot x (u j))
  calc
    (Fintype.card n : ℝ) ≤ (activeConstraintCount u x : ℝ) := hcount
    _ = ∑ j ∈ activeConstraintIndexSet u x, (realDot x (u j)) ^ 2 := hactive_sum.symm
    _ ≤ ∑ j, (realDot x (u j)) ^ 2 := hsubset_sum
    _ = realDot x x := (parsevalFrame_realDot_self u hparseval x).symm

/--
Existence form of the Ball--Prodromou norm-lower step.  This is obtained from
the active-constraint maximizer already proved in `RealConvex.lean`.
-/
theorem exists_parseval_polytope_point_norm_ge_card
    {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ)
    (hparseval : ∀ x : n → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i) :
    ∃ w : n → ℝ,
      (∀ j, |realDot w (u j)| ≤ 1) ∧
      (Fintype.card n : ℝ) ≤ realDot w w := by
  classical
  have hspan : Submodule.span ℝ (Set.range u) = ⊤ :=
    parsevalFrame_span_top u hparseval
  have hconv :
      ConvexOn ℝ (constraintPolytope u) (fun _ : n → ℝ => (0 : ℝ)) :=
    convexOn_const (0 : ℝ) (constraintPolytope_convex u)
  rcases activeConstraintMaximizer u (fun _ : n → ℝ => (0 : ℝ))
      hspan continuous_const hconv with
    ⟨w, hwpoly, _hwmax, hwactive⟩
  exact ⟨w, hwpoly, parsevalFrame_active_norm_lower u hparseval w hwactive⟩

/-- Weighted diagonal quadratic form used for the Ball--Prodromou functions `Φ_m`. -/
def weightedSquareSum {n : Type*} [Fintype n] (c : n → ℝ) (x : n → ℝ) : ℝ :=
  ∑ i, c i * x i ^ 2

/-- The finite weighted diagonal quadratic form is continuous. -/
theorem continuous_weightedSquareSum
    {n : Type*} [Fintype n] (c : n → ℝ) :
    Continuous (weightedSquareSum c) := by
  unfold weightedSquareSum
  fun_prop

/-- A weighted diagonal quadratic form with nonnegative weights is convex. -/
theorem convexOn_weightedSquareSum_nonneg
    {n : Type*} [Fintype n] (c : n → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    ConvexOn ℝ Set.univ (weightedSquareSum c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  unfold weightedSquareSum
  calc
    (∑ i, c i * (a • x + b • y) i ^ 2)
        ≤ ∑ i, (a * (c i * x i ^ 2) + b * (c i * y i ^ 2)) := by
          apply Finset.sum_le_sum
          intro i _hi
          have hsq :
              (a * x i + b * y i) ^ 2 ≤ a * x i ^ 2 + b * y i ^ 2 := by
            have hnonneg : 0 ≤ a * b * (x i - y i) ^ 2 :=
              mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
            nlinarith
          change c i * (a * x i + b * y i) ^ 2 ≤
            a * (c i * x i ^ 2) + b * (c i * y i ^ 2)
          calc
            c i * (a * x i + b * y i) ^ 2
                ≤ c i * (a * x i ^ 2 + b * y i ^ 2) :=
                  mul_le_mul_of_nonneg_left hsq (hc i)
            _ = a * (c i * x i ^ 2) + b * (c i * y i ^ 2) := by
                  ring
    _ = a * (∑ i, c i * x i ^ 2) + b * (∑ i, c i * y i ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/--
The same convexity statement restricted to a constraint polytope, in the exact
shape needed by `activeConstraintMaximizer`.
-/
theorem convexOn_constraintPolytope_weightedSquareSum_nonneg
    {n ι : Type*} [Fintype n]
    (u : ι → n → ℝ) (c : n → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    ConvexOn ℝ (constraintPolytope u) (weightedSquareSum c) :=
  (convexOn_weightedSquareSum_nonneg c hc).subset
    (Set.subset_univ _) (constraintPolytope_convex u)

/--
For a Parseval family, every nonnegative weighted diagonal quadratic has a
maximizer on the constraint polytope whose active constraints span and whose
norm has the Ball--Prodromou lower bound.
-/
theorem exists_parseval_weightedSquareSum_maximizer
    {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → n → ℝ)
    (hparseval : ∀ x : n → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i)
    (c : n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ w : n → ℝ,
      w ∈ constraintPolytope u ∧
      (∀ y : n → ℝ, y ∈ constraintPolytope u →
        weightedSquareSum c y ≤ weightedSquareSum c w) ∧
      activeConstraintSpan u w = ⊤ ∧
      (Fintype.card n : ℝ) ≤ realDot w w := by
  classical
  have hspan : Submodule.span ℝ (Set.range u) = ⊤ :=
    parsevalFrame_span_top u hparseval
  rcases activeConstraintMaximizer u (weightedSquareSum c)
      hspan (continuous_weightedSquareSum c)
      (convexOn_constraintPolytope_weightedSquareSum_nonneg u c hc) with
    ⟨w, hwpoly, hwmax, hwactive⟩
  exact ⟨w, hwpoly, hwmax, hwactive,
    parsevalFrame_active_norm_lower u hparseval w hwactive⟩

/--
The coefficient vector for the Ball--Prodromou functional
`Φ_m(x) = ∑_{i<m} (s_i - s_m) x_i^2` on `Fin (m+1)`.
-/
def bpPhiWeights (s : ℕ → ℝ) (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => if (i : ℕ) < m then s i - s m else 0

/-- The Ball--Prodromou coefficient vector is nonnegative under eigenvalue monotonicity. -/
theorem bpPhiWeights_nonneg
    (s : ℕ → ℝ) (m : ℕ)
    (hmono : ∀ i : ℕ, i < m → s m ≤ s i) :
    ∀ i, 0 ≤ bpPhiWeights s m i := by
  intro i
  by_cases hi : (i : ℕ) < m
  · simp [bpPhiWeights, hi, sub_nonneg.mpr (hmono i hi)]
  · simp [bpPhiWeights, hi]

/-- The last coefficient in `bpPhiWeights` is zero. -/
theorem bpPhiWeights_last (s : ℕ → ℝ) (m : ℕ) :
    bpPhiWeights s m ⟨m, Nat.lt_succ_self m⟩ = 0 := by
  simp [bpPhiWeights]

/-- A coefficient before the last index has the expected spectral-gap value. -/
theorem bpPhiWeights_of_lt
    (s : ℕ → ℝ) {i m : ℕ} (hi : i < m) :
    bpPhiWeights s m ⟨i, Nat.lt_trans hi (Nat.lt_succ_self m)⟩ = s i - s m := by
  simp [bpPhiWeights, hi]

/--
The active-constraint maximizer specialized to the Ball--Prodromou functional
on `Fin (m+1)`.
-/
theorem exists_bpPhiMaximizer
    {ι : Type*} [Fintype ι]
    (u : ι → Fin (m + 1) → ℝ)
    (hparseval : ∀ x : Fin (m + 1) → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i)
    (s : ℕ → ℝ)
    (hmono : ∀ i : ℕ, i < m → s m ≤ s i) :
    ∃ w : Fin (m + 1) → ℝ,
      w ∈ constraintPolytope u ∧
      (∀ y : Fin (m + 1) → ℝ, y ∈ constraintPolytope u →
        weightedSquareSum (bpPhiWeights s m) y ≤
          weightedSquareSum (bpPhiWeights s m) w) ∧
      activeConstraintSpan u w = ⊤ ∧
      ((m + 1 : ℕ) : ℝ) ≤ realDot w w := by
  classical
  rcases exists_parseval_weightedSquareSum_maximizer u hparseval
      (bpPhiWeights s m) (bpPhiWeights_nonneg s m hmono) with
    ⟨w, hwpoly, hwmax, hwactive, hnorm⟩
  refine ⟨w, hwpoly, hwmax, hwactive, ?_⟩
  simpa using hnorm

/-- Coordinate form of `realDot x x` on `Fin n`. -/
theorem realDot_self_fin_eq_sum_univ {n : ℕ} (x : Fin n → ℝ) :
    realDot x x = ∑ i : Fin n, x i ^ 2 := by
  simp [realDot, pow_two]

/-- `bpPhiWeights` turns `weightedSquareSum` into the expected prefix sum. -/
theorem weightedSquareSum_bpPhiWeights
    (s : ℕ → ℝ) (m : ℕ) (x : Fin (m + 1) → ℝ) :
    weightedSquareSum (bpPhiWeights s m) x =
      ∑ i : Fin m,
        (s i - s m) * x i.castSucc ^ 2 := by
  unfold weightedSquareSum
  rw [Fin.sum_univ_castSucc]
  simp [bpPhiWeights]

/-- Drop the last coordinate from each constraint vector. -/
def dropLastConstraints {ι : Type*} {m : ℕ}
    (u : ι → Fin (m + 1) → ℝ) : ι → Fin m → ℝ :=
  fun j i => u j i.castSucc

/-- Extend a vector by a zero final coordinate. -/
def extendByZero {m : ℕ} (x : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc x 0

@[simp]
theorem extendByZero_castSucc {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    extendByZero x i.castSucc = x i := by
  simp [extendByZero]

@[simp]
theorem extendByZero_last {m : ℕ} (x : Fin m → ℝ) :
    extendByZero x (Fin.last m) = 0 := by
  simp [extendByZero]

/-- The previous Ball--Prodromou functional evaluated on a zero-extension. -/
theorem weightedSquareSum_bpPhiWeights_extendByZero
    (s : ℕ → ℝ) (m : ℕ) (x : Fin m → ℝ) :
    weightedSquareSum (bpPhiWeights s m) (extendByZero x) =
      ∑ i : Fin m, (s i - s m) * x i ^ 2 := by
  rw [weightedSquareSum_bpPhiWeights]
  simp

/--
The dot product of a zero-extension with a full constraint vector is the dot
product against the truncated constraint vector.
-/
theorem realDot_extendByZero_dropLastConstraints
    {ι : Type*} {m : ℕ}
    (u : ι → Fin (m + 1) → ℝ) (x : Fin m → ℝ) (j : ι) :
    realDot (extendByZero x) (u j) =
      realDot x (dropLastConstraints u j) := by
  unfold realDot dropLastConstraints
  rw [Fin.sum_univ_castSucc]
  simp

/-- Truncating the final coordinate preserves the Parseval identity. -/
theorem parseval_dropLastConstraints
    {ι : Type*} [Fintype ι] {m : ℕ}
    (u : ι → Fin (m + 1) → ℝ)
    (hparseval : ∀ x : Fin (m + 1) → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i) :
    ∀ x : Fin m → ℝ, ∀ i,
      (∑ j, realDot x (dropLastConstraints u j) *
        dropLastConstraints u j i) = x i := by
  intro x i
  have h := hparseval (extendByZero x) i.castSucc
  simpa [dropLastConstraints, realDot_extendByZero_dropLastConstraints u x] using h

/--
The TeX inclusion `C_{m-1} ⊆ C_m`: a feasible point for the truncated
constraints remains feasible after adding a zero last coordinate.
-/
theorem extendByZero_mem_constraintPolytope
    {ι : Type*} {m : ℕ}
    (u : ι → Fin (m + 1) → ℝ) {x : Fin m → ℝ}
    (hx : x ∈ constraintPolytope (dropLastConstraints u)) :
    extendByZero x ∈ constraintPolytope u := by
  intro j
  simpa [realDot_extendByZero_dropLastConstraints] using hx j

/--
The maximizer comparison used in the Ball--Prodromou induction: a maximizer on
`C_m` dominates the zero-extension of any feasible point from `C_{m-1}`.
-/
theorem bpPhi_maximizer_comparison_dropLast
    {ι : Type*} {m : ℕ}
    (u : ι → Fin (m + 1) → ℝ) (s : ℕ → ℝ)
    {wCur : Fin (m + 1) → ℝ} {wPrev : Fin m → ℝ}
    (hmax : ∀ y : Fin (m + 1) → ℝ, y ∈ constraintPolytope u →
      weightedSquareSum (bpPhiWeights s m) y ≤
        weightedSquareSum (bpPhiWeights s m) wCur)
    (hPrev : wPrev ∈ constraintPolytope (dropLastConstraints u)) :
    weightedSquareSum (bpPhiWeights s m) (extendByZero wPrev) ≤
      weightedSquareSum (bpPhiWeights s m) wCur :=
  hmax (extendByZero wPrev) (extendByZero_mem_constraintPolytope u hPrev)

/--
The same comparison in explicit coordinate-sum form:
`∑_{i<m} (s_i-s_m) wPrev_i^2 ≤ ∑_{i<m} (s_i-s_m) wCur_i^2`.
-/
theorem bpPhi_maximizer_comparison_dropLast_sum
    {ι : Type*} {m : ℕ}
    (u : ι → Fin (m + 1) → ℝ) (s : ℕ → ℝ)
    {wCur : Fin (m + 1) → ℝ} {wPrev : Fin m → ℝ}
    (hmax : ∀ y : Fin (m + 1) → ℝ, y ∈ constraintPolytope u →
      weightedSquareSum (bpPhiWeights s m) y ≤
        weightedSquareSum (bpPhiWeights s m) wCur)
    (hPrev : wPrev ∈ constraintPolytope (dropLastConstraints u)) :
    (∑ i : Fin m, (s i - s m) * wPrev i ^ 2) ≤
      ∑ i : Fin m, (s i - s m) * wCur i.castSucc ^ 2 := by
  have hcomp :=
    bpPhi_maximizer_comparison_dropLast u s (wCur := wCur) (wPrev := wPrev)
      hmax hPrev
  rwa [weightedSquareSum_bpPhiWeights_extendByZero,
    weightedSquareSum_bpPhiWeights] at hcomp

/--
Algebraic identity behind the Ball--Prodromou induction step, left-hand side.
It rewrites the next weighted quadratic sum as the previous weights plus the
new spectral gap times the full squared norm.
-/
theorem bp_induction_lhs_identity
    (s y : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (s i - s (m + 1)) * y i ^ 2) =
      (∑ i ∈ Finset.range m, (s i - s m) * y i ^ 2) +
        (s m - s (m + 1)) *
          (∑ i ∈ Finset.range (m + 1), y i ^ 2) := by
  rw [Finset.sum_range_succ]
  rw [show (∑ i ∈ Finset.range (m + 1), y i ^ 2) =
      (∑ i ∈ Finset.range m, y i ^ 2) + y m ^ 2 by
        rw [Finset.sum_range_succ]]
  rw [mul_add, Finset.mul_sum]
  rw [← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/--
Algebraic identity behind the Ball--Prodromou induction step, right-hand side.
-/
theorem bp_induction_rhs_identity
    (s : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (s i - s (m + 1))) =
      (∑ i ∈ Finset.range m, (s i - s m)) +
        (s m - s (m + 1)) * (m + 1 : ℝ) := by
  rw [Finset.sum_range_succ]
  calc
    (∑ i ∈ Finset.range m, (s i - s (m + 1))) + (s m - s (m + 1))
        = (∑ i ∈ Finset.range m, ((s i - s m) + (s m - s (m + 1)))) +
            (s m - s (m + 1)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = ((∑ i ∈ Finset.range m, (s i - s m)) +
            ∑ _i ∈ Finset.range m, (s m - s (m + 1))) +
            (s m - s (m + 1)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ Finset.range m, (s i - s m)) +
          (s m - s (m + 1)) * (m + 1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
          ring_nf

/--
`Fin`-indexed version of the Ball--Prodromou left-hand induction identity.
-/
theorem bp_induction_lhs_identity_fin
    (s : ℕ → ℝ) {m : ℕ} (x : Fin (m + 1) → ℝ) :
    (∑ i : Fin (m + 1), (s i - s (m + 1)) * x i ^ 2) =
      (∑ i : Fin m, (s i - s m) * x i.castSucc ^ 2) +
        (s m - s (m + 1)) *
          (∑ i : Fin (m + 1), x i ^ 2) := by
  rw [Fin.sum_univ_castSucc]
  rw [show (∑ i : Fin (m + 1), x i ^ 2) =
      (∑ i : Fin m, x i.castSucc ^ 2) + x (Fin.last m) ^ 2 by
        rw [Fin.sum_univ_castSucc]]
  rw [mul_add, Finset.mul_sum]
  rw [← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [Fin.val_castSucc]
  ring

/--
`Fin`-indexed version of the Ball--Prodromou right-hand induction identity.
-/
theorem bp_induction_rhs_identity_fin
    (s : ℕ → ℝ) (m : ℕ) :
    (∑ i : Fin (m + 1), (s i - s (m + 1))) =
      (∑ i : Fin m, (s i - s m)) +
        (s m - s (m + 1)) * (m + 1 : ℝ) := by
  rw [Fin.sum_univ_castSucc]
  calc
    (∑ i : Fin m, (s i - s (m + 1))) + (s m - s (m + 1))
        = (∑ i : Fin m, ((s i - s m) + (s m - s (m + 1)))) +
            (s m - s (m + 1)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = ((∑ i : Fin m, (s i - s m)) +
            ∑ _i : Fin m, (s m - s (m + 1))) +
            (s m - s (m + 1)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, (s i - s m)) +
          (s m - s (m + 1)) * (m + 1 : ℝ) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
          ring_nf

/--
One numerical step in the Ball--Prodromou induction.

The hypotheses correspond exactly to the TeX proof:
* the maximizer comparison for `Φ_m`;
* the induction hypothesis at level `m`;
* the norm-lower estimate for the current maximizer;
* nonnegativity of the spectral gap `s_m - s_{m+1}`.
-/
theorem bp_induction_step
    (s xPrev xCur : ℕ → ℝ) (m : ℕ)
    (hmax :
      (∑ i ∈ Finset.range m, (s i - s m) * xCur i ^ 2) ≥
        ∑ i ∈ Finset.range m, (s i - s m) * xPrev i ^ 2)
    (hprev :
      (∑ i ∈ Finset.range m, (s i - s m) * xPrev i ^ 2) ≥
        ∑ i ∈ Finset.range m, (s i - s m))
    (hnorm :
      (m + 1 : ℝ) ≤ ∑ i ∈ Finset.range (m + 1), xCur i ^ 2)
    (hgap : 0 ≤ s m - s (m + 1)) :
    (∑ i ∈ Finset.range (m + 1), (s i - s (m + 1)) * xCur i ^ 2) ≥
      ∑ i ∈ Finset.range (m + 1), (s i - s (m + 1)) := by
  rw [bp_induction_lhs_identity s xCur m]
  rw [bp_induction_rhs_identity s m]
  exact add_le_add (hprev.trans hmax)
    (mul_le_mul_of_nonneg_left hnorm hgap)

/--
One numerical Ball--Prodromou induction step in the `Fin`-indexed form used by
the coordinate theorem.
-/
theorem bp_induction_step_fin
    (s : ℕ → ℝ) {m : ℕ}
    (xPrev : Fin m → ℝ) (xCur : Fin (m + 1) → ℝ)
    (hmax :
      (∑ i : Fin m, (s i - s m) * xPrev i ^ 2) ≤
        ∑ i : Fin m, (s i - s m) * xCur i.castSucc ^ 2)
    (hprev :
      (∑ i : Fin m, (s i - s m)) ≤
        ∑ i : Fin m, (s i - s m) * xPrev i ^ 2)
    (hnorm :
      (m + 1 : ℝ) ≤ ∑ i : Fin (m + 1), xCur i ^ 2)
    (hgap : 0 ≤ s m - s (m + 1)) :
    (∑ i : Fin (m + 1), (s i - s (m + 1)) * xCur i ^ 2) ≥
      ∑ i : Fin (m + 1), (s i - s (m + 1)) := by
  rw [bp_induction_lhs_identity_fin s xCur]
  rw [bp_induction_rhs_identity_fin s m]
  exact add_le_add (hprev.trans hmax)
    (mul_le_mul_of_nonneg_left hnorm hgap)

/--
Existential form of the Ball--Prodromou induction in diagonal coordinates.

For a decreasing sequence `s`, this constructs a feasible point satisfying the
induction inequality `(2)` from the TeX proof.
-/
theorem exists_bpInductionWitness
    {ι : Type*} [Fintype ι] (m : ℕ)
    (u : ι → Fin (m + 1) → ℝ)
    (hparseval : ∀ x : Fin (m + 1) → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i)
    (s : ℕ → ℝ)
    (hanti : ∀ {i k : ℕ}, i ≤ k → s k ≤ s i) :
    ∃ w : Fin (m + 1) → ℝ,
      w ∈ constraintPolytope u ∧
      (∑ i : Fin (m + 1), (s i - s (m + 1))) ≤
        ∑ i : Fin (m + 1), (s i - s (m + 1)) * w i ^ 2 := by
  classical
  induction m with
  | zero =>
      have hmono0 : ∀ i : ℕ, i < 0 → s 0 ≤ s i := by
        intro i hi
        exact False.elim (Nat.not_lt_zero i hi)
      rcases exists_bpPhiMaximizer u hparseval s hmono0 with
        ⟨w, hwpoly, _hwmax, _hwactive, hnorm⟩
      refine ⟨w, hwpoly, ?_⟩
      have hnormsum : (((0 : ℕ) : ℝ) + 1) ≤ ∑ i : Fin (0 + 1), w i ^ 2 := by
        simpa [realDot_self_fin_eq_sum_univ] using hnorm
      have hgap : 0 ≤ s 0 - s 1 := sub_nonneg.mpr (hanti (Nat.zero_le 1))
      have hmaxEmpty :
          (∑ i : Fin 0, (s i - s 0) * (fun _ : Fin 0 => (0 : ℝ)) i ^ 2) ≤
            ∑ i : Fin 0, (s i - s 0) * w i.castSucc ^ 2 := by
        simp
      have hprevEmpty :
          (∑ i : Fin 0, (s i - s 0)) ≤
            ∑ i : Fin 0, (s i - s 0) * (fun _ : Fin 0 => (0 : ℝ)) i ^ 2 := by
        simp
      simpa using
        bp_induction_step_fin s (fun _ : Fin 0 => (0 : ℝ)) w
          hmaxEmpty hprevEmpty hnormsum hgap
  | succ m ih =>
      have hprevParseval :
          ∀ x : Fin (m + 1) → ℝ, ∀ i,
            (∑ j, realDot x (dropLastConstraints u j) *
              dropLastConstraints u j i) = x i :=
        parseval_dropLastConstraints u hparseval
      rcases ih (dropLastConstraints u) hprevParseval with
        ⟨wPrev, hwPrevPoly, hprev⟩
      have hmono : ∀ i : ℕ, i < m + 1 → s (m + 1) ≤ s i := by
        intro i hi
        exact hanti (Nat.le_of_lt hi)
      rcases exists_bpPhiMaximizer u hparseval s hmono with
        ⟨wCur, hwCurPoly, hwCurMax, _hwCurActive, hCurNorm⟩
      refine ⟨wCur, hwCurPoly, ?_⟩
      have hmaxsum :
          (∑ i : Fin (m + 1), (s i - s (m + 1)) * wPrev i ^ 2) ≤
            ∑ i : Fin (m + 1),
              (s i - s (m + 1)) * wCur i.castSucc ^ 2 :=
        bpPhi_maximizer_comparison_dropLast_sum u s
          (wCur := wCur) (wPrev := wPrev) hwCurMax hwPrevPoly
      have hnormsum :
          (((m + 1 : ℕ) : ℝ) + 1) ≤
            ∑ i : Fin ((m + 1) + 1), wCur i ^ 2 := by
        simpa [realDot_self_fin_eq_sum_univ] using hCurNorm
      have hgap : 0 ≤ s (m + 1) - s ((m + 1) + 1) :=
        sub_nonneg.mpr (hanti (Nat.le_succ (m + 1)))
      simpa [Nat.succ_eq_add_one, add_assoc] using
        bp_induction_step_fin s wPrev wCur hmaxsum hprev hnormsum hgap

/--
Diagonal Ball--Prodromou theorem in coordinates.

This is the core of the paper's Ball--Prodromou proof after choosing an
orthonormal eigenbasis and setting the next eigenvalue to zero.
-/
theorem ballProdromou_diagonal
    {ι : Type*} [Fintype ι] (m : ℕ)
    (u : ι → Fin (m + 1) → ℝ)
    (hparseval : ∀ x : Fin (m + 1) → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i)
    (s : ℕ → ℝ)
    (hanti : ∀ {i k : ℕ}, i ≤ k → s k ≤ s i)
    (hs_last : s (m + 1) = 0) :
    ∃ w : Fin (m + 1) → ℝ,
      w ∈ constraintPolytope u ∧
      (∑ i : Fin (m + 1), s i) ≤
        ∑ i : Fin (m + 1), s i * w i ^ 2 := by
  rcases exists_bpInductionWitness m u hparseval s hanti with
    ⟨w, hwpoly, hineq⟩
  refine ⟨w, hwpoly, ?_⟩
  simpa [hs_last] using hineq

/--
The spectral-coordinate data needed to turn the diagonal Ball--Prodromou theorem
into the cube quadratic maximum.

In the paper this data comes from the positive spectral subspace of a symmetric
matrix `A`: `u j` are the coordinates of the projected standard basis vectors,
`s` is the decreasing eigenvalue list with one terminal zero, and `τ` is the
trace of the positive part.
-/
def HasBallProdromouDiagonalModel
    {d : Type*} [Fintype d] (A : Matrix d d ℝ) (τ : ℝ) : Prop :=
  ∃ (m : ℕ) (u : d → Fin (m + 1) → ℝ) (s : ℕ → ℝ),
    (∀ x : Fin (m + 1) → ℝ, ∀ i,
      (∑ j, realDot x (u j) * u j i) = x i) ∧
    (∀ {i k : ℕ}, i ≤ k → s k ≤ s i) ∧
    s (m + 1) = 0 ∧
    τ = ∑ i : Fin (m + 1), s i ∧
    ∀ w : Fin (m + 1) → ℝ,
      realQuadraticForm A (fun j => realDot w (u j)) =
        ∑ i : Fin (m + 1), s i * w i ^ 2

/--
Ball--Prodromou implies the cube quadratic maximum once the positive spectral
subspace has been expressed in diagonal coordinates.
-/
theorem cubeQuadraticMaximum_from_diagonalBP
    {d : Type*} [Fintype d] (A : Matrix d d ℝ) (τ : ℝ)
    (hmodel : HasBallProdromouDiagonalModel A τ) :
    ∃ x : d → ℝ, InRealUnitCube x ∧ τ ≤ realQuadraticForm A x := by
  classical
  rcases hmodel with
    ⟨m, u, s, hparseval, hanti, hs_last, htrace, hquad⟩
  rcases ballProdromou_diagonal m u hparseval s hanti hs_last with
    ⟨w, hwpoly, hineq⟩
  let x : d → ℝ := fun j => realDot w (u j)
  refine ⟨x, ?_, ?_⟩
  · intro j
    exact hwpoly j
  · calc
      τ = ∑ i : Fin (m + 1), s i := htrace
      _ ≤ ∑ i : Fin (m + 1), s i * w i ^ 2 := hineq
      _ = realQuadraticForm A x := (hquad w).symm

/--
For a fixed symmetric test matrix, the positive-part support-function bound and
the Ball--Prodromou diagonal model give the support inequality needed for the
convex-hull separation argument.
-/
theorem supportInequality_from_diagonalBP
    {d : Type*} [Fintype d] [DecidableEq d]
    (A Apos : Matrix d d ℝ)
    (hsupport : HasPositivePartSupportFunction A Apos)
    (hmodel : HasBallProdromouDiagonalModel A Apos.trace) :
    ∃ x : d → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix d d ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  rcases cubeQuadraticMaximum_from_diagonalBP A Apos.trace hmodel with
    ⟨x, hcube, hx⟩
  refine ⟨x, hcube, ?_⟩
  intro G hGsym hG
  exact (hsupport.1 G hGsym hG).trans hx

/-- Ambient vector represented by coordinates in an orthonormal row system. -/
def ambientOfEigenCoordinates
    {d : Type*} {m : ℕ}
    (v : Fin (m + 1) → d → ℝ) (w : Fin (m + 1) → ℝ) : d → ℝ :=
  fun j => ∑ i, w i * v i j

/-- Constraint vectors obtained from rows of an ambient orthonormal system. -/
def coordinateConstraintVectors
    {d : Type*} {m : ℕ}
    (v : Fin (m + 1) → d → ℝ) : d → Fin (m + 1) → ℝ :=
  fun j i => v i j

/-- The project coordinate dot product agrees with the Euclidean inner product. -/
theorem realDot_euclidean_eq_inner
    {d : Type*} [Fintype d]
    (x y : EuclideanSpace ℝ d) :
    realDot (fun i => x i) (fun i => y i) = inner ℝ x y := by
  simp [realDot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- Coordinate form of the matrix action `A.toEuclideanLin`. -/
theorem toEuclideanLin_apply_eq_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (x : EuclideanSpace ℝ d) (i : d) :
    (A.toEuclideanLin x) i = ∑ j, A i j * x j := by
  have h := congrFun (Matrix.ofLp_toLpLin (p := 2) (q := 2) A x) i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] at h ⊢

/-- Coordinate quadratic forms are Euclidean inner products against `A.toEuclideanLin`. -/
theorem realQuadraticForm_euclidean_eq_inner
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (x : EuclideanSpace ℝ d) :
    realQuadraticForm A (fun i => x i) = inner ℝ x (A.toEuclideanLin x) := by
  calc
    realQuadraticForm A (fun i => x i)
        = ∑ i, x i * (A.toEuclideanLin x) i := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [toEuclideanLin_apply_eq_sum A x i]
    _ = realDot (fun i => x i) (fun i => (A.toEuclideanLin x) i) := by
          rfl
    _ = inner ℝ x (A.toEuclideanLin x) :=
          realDot_euclidean_eq_inner x (A.toEuclideanLin x)

/--
The projected standard-basis vectors form a Parseval family when the coordinate
rows are orthonormal.
-/
theorem parseval_coordinateConstraintVectors
    {d : Type*} [Fintype d] {m : ℕ}
    (v : Fin (m + 1) → d → ℝ)
    (horth : ∀ i k, realDot (v i) (v k) = if i = k then 1 else 0) :
    ∀ x : Fin (m + 1) → ℝ, ∀ i,
      (∑ j, realDot x (coordinateConstraintVectors v j) *
        coordinateConstraintVectors v j i) = x i := by
  classical
  intro x i
  calc
    (∑ j, realDot x (coordinateConstraintVectors v j) *
        coordinateConstraintVectors v j i)
        = ∑ j, ∑ k, (x k * v k j) * v i j := by
          simp [coordinateConstraintVectors, realDot, Finset.sum_mul]
    _ = ∑ k, ∑ j, (x k * v k j) * v i j := by
          rw [Finset.sum_comm]
    _ = ∑ k, x k * realDot (v k) (v i) := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp [realDot, Finset.mul_sum, mul_assoc]
    _ = ∑ k, x k * (if k = i then 1 else 0) := by
          simp [horth]
    _ = x i := by
          simp

/--
If the rows are orthonormal eigenvectors of `A`, then the quadratic form of `A`
is diagonal on their span.
-/
theorem realQuadraticForm_ambientOfEigenCoordinates
    {d : Type*} [Fintype d] {m : ℕ}
    (A : Matrix d d ℝ) (v : Fin (m + 1) → d → ℝ) (s : ℕ → ℝ)
    (horth : ∀ i k, realDot (v i) (v k) = if i = k then 1 else 0)
    (heigen : ∀ r j, (∑ k, A j k * v r k) = s r * v r j)
    (w : Fin (m + 1) → ℝ) :
    realQuadraticForm A (ambientOfEigenCoordinates v w) =
      ∑ r : Fin (m + 1), s r * w r ^ 2 := by
  classical
  have hmul :
      ∀ j, (∑ k, A j k * (∑ t, w t * v t k)) =
        ∑ t, w t * (s t * v t j) := by
    intro j
    calc
      (∑ k, A j k * (∑ t, w t * v t k))
          = ∑ k, ∑ t, A j k * (w t * v t k) := by
            simp [Finset.mul_sum]
      _ = ∑ t, ∑ k, A j k * (w t * v t k) := by
            rw [Finset.sum_comm]
      _ = ∑ t, w t * (∑ k, A j k * v t k) := by
            apply Finset.sum_congr rfl
            intro t _ht
            calc
              (∑ k, A j k * (w t * v t k))
                  = ∑ k, w t * (A j k * v t k) := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    ring
              _ = w t * (∑ k, A j k * v t k) := by
                    rw [Finset.mul_sum]
      _ = ∑ t, w t * (s t * v t j) := by
            simp [heigen]
  have hexpand :
      (∑ j, (∑ r, w r * v r j) *
          (∑ t, w t * (s t * v t j))) =
        ∑ r, ∑ t, w r * (w t * s t) * realDot (v r) (v t) := by
    calc
      (∑ j, (∑ r, w r * v r j) *
          (∑ t, w t * (s t * v t j)))
          = ∑ j, ∑ t, ∑ r,
              (w r * v r j) * (w t * (s t * v t j)) := by
            simp [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ j, ∑ r, ∑ t,
              (w r * v r j) * (w t * (s t * v t j)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [Finset.sum_comm]
      _ = ∑ r, ∑ t, ∑ j,
              (w r * v r j) * (w t * (s t * v t j)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r _hr
            rw [Finset.sum_comm]
      _ = ∑ r, ∑ t, w r * (w t * s t) * realDot (v r) (v t) := by
            apply Finset.sum_congr rfl
            intro r _hr
            apply Finset.sum_congr rfl
            intro t _ht
            simp [realDot, Finset.mul_sum, mul_comm, mul_left_comm]
  unfold realQuadraticForm ambientOfEigenCoordinates
  calc
    (∑ j, (∑ r, w r * v r j) *
        ∑ k, A j k * (∑ t, w t * v t k))
        = ∑ j, (∑ r, w r * v r j) *
            (∑ t, w t * (s t * v t j)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hmul j]
    _ = ∑ r, ∑ t, w r * (w t * s t) * realDot (v r) (v t) := hexpand
    _ = ∑ r : Fin (m + 1), s r * w r ^ 2 := by
          simp [horth, pow_two, mul_comm, mul_left_comm]

/--
Explicit finite-dimensional spectral-coordinate data sufficient for the
Ball--Prodromou diagonal model.
-/
def HasPositiveEigenCoordinateData
    {d : Type*} [Fintype d] (A : Matrix d d ℝ) (τ : ℝ) : Prop :=
  ∃ (m : ℕ) (v : Fin (m + 1) → d → ℝ) (s : ℕ → ℝ),
    (∀ i k, realDot (v i) (v k) = if i = k then 1 else 0) ∧
    (∀ r j, (∑ k, A j k * v r k) = s r * v r j) ∧
    (∀ {i k : ℕ}, i ≤ k → s k ≤ s i) ∧
    s (m + 1) = 0 ∧
    τ = ∑ i : Fin (m + 1), s i

/--
For a positive semidefinite real symmetric matrix indexed by `Fin (m+1)`,
Mathlib's Hermitian spectral theorem supplies the explicit eigen-coordinate data
needed by the Ball--Prodromou diagonal model.
-/
theorem hasPositiveEigenCoordinateData_of_realPSD_fin
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A)
    (hantiEig : Antitone (realSymmetric_isHermitian A hSym).eigenvalues) :
    HasPositiveEigenCoordinateData A A.trace := by
  classical
  have hHerm : A.IsHermitian := realSymmetric_isHermitian A hSym
  have hPos : A.PosSemidef := realPSD_posSemidef A hSym hPSD
  let v : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i => ⇑(hHerm.eigenvectorBasis i)
  let s : ℕ → ℝ :=
    fun k => if hk : k ≤ m then hHerm.eigenvalues ⟨k, Nat.lt_succ_of_le hk⟩ else 0
  refine ⟨m, v, s, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    have horth := (orthonormal_iff_ite.mp hHerm.eigenvectorBasis.orthonormal) i k
    simpa [v, realDot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      mul_comm] using horth
  · intro r j
    have h := congrFun (hHerm.mulVec_eigenvectorBasis r) j
    have hr : (r : ℕ) ≤ m := Nat.lt_succ_iff.mp r.isLt
    simpa [v, s, hr, Matrix.mulVec, dotProduct, Pi.smul_apply] using h
  · have hantiFin : Antitone hHerm.eigenvalues := hantiEig
    intro i k hik
    by_cases hk : k ≤ m
    · have hi : i ≤ m := le_trans hik hk
      have hfin : (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (m + 1)) ≤
          ⟨k, Nat.lt_succ_of_le hk⟩ := by
        exact hik
      simpa [s, hi, hk] using hantiFin hfin
    · by_cases hi : i ≤ m
      · have hnonneg : 0 ≤ hHerm.eigenvalues ⟨i, Nat.lt_succ_of_le hi⟩ :=
          hPos.eigenvalues_nonneg ⟨i, Nat.lt_succ_of_le hi⟩
        simpa [s, hi, hk] using hnonneg
      · simp [s, hi, hk]
  · simp [s]
  · have htrace := hHerm.trace_eq_sum_eigenvalues
    rw [htrace]
    apply Finset.sum_congr rfl
    intro i _hi
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    simp [s, hi]

/-- The sorted self-adjoint eigenvalues supplied by Mathlib are antitone. -/
theorem symmetricToEuclidean_eigenvalues_antitone_fin
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) :
    Antitone
      ((Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)).eigenvalues
          (finrank_euclideanSpace_fin :
            Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1)) := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (realSymmetric_isHermitian A hSym)).eigenvalues_antitone finrank_euclideanSpace_fin

/--
Mathlib's sorted self-adjoint eigenbasis consists of eigenvectors for
`A.toEuclideanLin`.
-/
theorem symmetricToEuclidean_apply_eigenvectorBasis_fin
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (i : Fin (m + 1)) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (realSymmetric_isHermitian A hSym)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
      finrank_euclideanSpace_fin
    A.toEuclideanLin (hT.eigenvectorBasis hn i) =
      (hT.eigenvalues hn i : ℝ) • hT.eigenvectorBasis hn i := by
  intro hT hn
  exact hT.apply_eigenvectorBasis hn i

/-- Coordinate orthonormality of Mathlib's sorted Euclidean eigenbasis. -/
theorem symmetricToEuclidean_eigenvectorBasis_realDot
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (realSymmetric_isHermitian A hSym)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
      finrank_euclideanSpace_fin
    ∀ i k,
      realDot (fun j => (hT.eigenvectorBasis hn i) j)
        (fun j => (hT.eigenvectorBasis hn k) j) =
        if i = k then 1 else 0 := by
  intro hT hn i k
  have horth := (orthonormal_iff_ite.mp (hT.eigenvectorBasis hn).orthonormal) i k
  rw [realDot_euclidean_eq_inner]
  exact horth

/-- Coordinate form of the sorted Euclidean eigenvector equation. -/
theorem symmetricToEuclidean_eigenvectorBasis_coord
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (realSymmetric_isHermitian A hSym)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
      finrank_euclideanSpace_fin
    ∀ r j,
      (∑ k, A j k * (hT.eigenvectorBasis hn r) k) =
        hT.eigenvalues hn r * (hT.eigenvectorBasis hn r) j := by
  intro hT hn r j
  have h := congrArg (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y j)
    (hT.apply_eigenvectorBasis hn r)
  rw [toEuclideanLin_apply_eq_sum A (hT.eigenvectorBasis hn r) j] at h
  simpa [Pi.smul_apply, smul_eq_mul] using h

/-- Sorted Euclidean eigenvalues are nonnegative under the project PSD predicate. -/
theorem symmetricToEuclidean_eigenvalues_nonneg_of_realPSD_fin
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (realSymmetric_isHermitian A hSym)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
      finrank_euclideanSpace_fin
    ∀ i, 0 ≤ hT.eigenvalues hn i := by
  intro hT hn i
  let y : EuclideanSpace ℝ (Fin (m + 1)) := hT.eigenvectorBasis hn i
  have horth := (orthonormal_iff_ite.mp (hT.eigenvectorBasis hn).orthonormal) i i
  have hinner_self : inner ℝ y y = 1 := by
    simp [y]
  have hnorm_sq : ‖y‖ ^ 2 = 1 := by
    simpa [real_inner_self_eq_norm_sq] using hinner_self
  have heig : A.toEuclideanLin y = (hT.eigenvalues hn i : ℝ) • y := by
    simp [y, hT.apply_eigenvectorBasis hn i]
  have hquad : realQuadraticForm A (fun j => y j) = hT.eigenvalues hn i := by
    calc
      realQuadraticForm A (fun j => y j)
          = inner ℝ y (A.toEuclideanLin y) :=
            realQuadraticForm_euclidean_eq_inner A y
      _ = inner ℝ y ((hT.eigenvalues hn i : ℝ) • y) := by
            rw [heig]
      _ = hT.eigenvalues hn i := by
            rw [inner_smul_right, real_inner_self_eq_norm_sq, hnorm_sq]
            simp
  simpa [hquad] using hPSD (fun j => y j)

/-- The trace of a real matrix agrees with the sum of Mathlib's sorted eigenvalues. -/
theorem symmetricToEuclidean_trace_eq_sum_eigenvalues_fin
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (realSymmetric_isHermitian A hSym)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
      finrank_euclideanSpace_fin
    A.trace = ∑ i, hT.eigenvalues hn i := by
  intro hT hn
  have hmatrix_trace :
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (m + 1))) A.toEuclideanLin =
        A.trace := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    simp
  calc
    A.trace =
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (m + 1))) A.toEuclideanLin :=
      hmatrix_trace.symm
    _ = ∑ i, hT.eigenvalues hn i := by
      simpa using hT.trace_eq_sum_eigenvalues hn

/--
Mathlib's sorted Euclidean spectral data gives the project's positive
eigen-coordinate data once the trace has been identified with the sorted
eigenvalue sum.
-/
theorem hasPositiveEigenCoordinateData_of_realPSD_fin_sorted_of_trace
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A)
    (htraceSorted :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
        finrank_euclideanSpace_fin
      A.trace = ∑ i, hT.eigenvalues hn i) :
    HasPositiveEigenCoordinateData A A.trace := by
  classical
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (realSymmetric_isHermitian A hSym)
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
    finrank_euclideanSpace_fin
  let v : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i => ⇑(hT.eigenvectorBasis hn i)
  let s : ℕ → ℝ :=
    fun k => if hk : k ≤ m then hT.eigenvalues hn ⟨k, Nat.lt_succ_of_le hk⟩ else 0
  refine ⟨m, v, s, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    simpa [v] using symmetricToEuclidean_eigenvectorBasis_realDot A hSym i k
  · intro r j
    have hr : (r : ℕ) ≤ m := Nat.lt_succ_iff.mp r.isLt
    simpa [v, s, hr] using symmetricToEuclidean_eigenvectorBasis_coord A hSym r j
  · intro i k hik
    by_cases hk : k ≤ m
    · have hi : i ≤ m := le_trans hik hk
      have hfin : (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (m + 1)) ≤
          ⟨k, Nat.lt_succ_of_le hk⟩ := by
        exact hik
      have hanti :=
        symmetricToEuclidean_eigenvalues_antitone_fin A hSym hfin
      simpa [s, hi, hk] using hanti
    · by_cases hi : i ≤ m
      · have hnonneg :=
          symmetricToEuclidean_eigenvalues_nonneg_of_realPSD_fin A hSym hPSD
            ⟨i, Nat.lt_succ_of_le hi⟩
        simpa [s, hi, hk] using hnonneg
      · simp [s, hi, hk]
  · simp [s]
  · rw [htraceSorted]
    apply Finset.sum_congr rfl
    intro i _hi
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    simp [s, hi]

/-- Mathlib's sorted Euclidean spectral data gives the positive eigen-coordinate data. -/
theorem hasPositiveEigenCoordinateData_of_realPSD_fin_sorted
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A) :
    HasPositiveEigenCoordinateData A A.trace :=
  hasPositiveEigenCoordinateData_of_realPSD_fin_sorted_of_trace A hSym hPSD
    (symmetricToEuclidean_trace_eq_sum_eigenvalues_fin A hSym)

/--
For a finite sequence, if an initial block is nonnegative and the remaining tail
is nonpositive, then the sum of positive parts is the sum over the initial
block.
-/
theorem sum_posPart_eq_sum_initialSegment_of_signs
    {N m : ℕ} (hN : m + 1 ≤ N) (lam : Fin N → ℝ)
    (hpos : ∀ r : Fin (m + 1), 0 ≤ lam (Fin.castLE hN r))
    (hnonpos : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → lam i ≤ 0) :
    (∑ i : Fin N, (lam i)⁺) =
      ∑ r : Fin (m + 1), lam (Fin.castLE hN r) := by
  let f : ℕ → ℝ := fun k => if hk : k < N then (lam ⟨k, hk⟩)⁺ else 0
  let g : ℕ → ℝ := fun k => if hk : k < N then lam ⟨k, hk⟩ else 0
  have htotal_fin_to_range :
      (∑ i : Fin N, (lam i)⁺) = ∑ k ∈ Finset.range N, f k := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [f]
  have hinitial_fin_to_range :
      (∑ r : Fin (m + 1), lam (Fin.castLE hN r)) =
        ∑ k ∈ Finset.range (m + 1), g k := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _hi
    have hltN : (i : ℕ) < N := lt_of_lt_of_le i.isLt hN
    simp [g, hltN, Fin.castLE]
  rw [htotal_fin_to_range, hinitial_fin_to_range]
  have hsplit := Finset.sum_range_add f (m + 1) (N - (m + 1))
  have hNadd : m + 1 + (N - (m + 1)) = N := Nat.add_sub_of_le hN
  rw [hNadd] at hsplit
  rw [hsplit]
  have hfirst :
      ∑ x ∈ Finset.range (m + 1), f x =
        ∑ x ∈ Finset.range (m + 1), g x := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkltm : k < m + 1 := Finset.mem_range.mp hk
    have hkltN : k < N := lt_of_lt_of_le hkltm hN
    have hrpos := hpos ⟨k, hkltm⟩
    have hrpos' : 0 ≤ lam ⟨k, hkltN⟩ := by
      simpa [Fin.castLE] using hrpos
    simp [f, g, hkltN, posPart_eq_self.mpr hrpos']
  have htail : ∑ x ∈ Finset.range (N - (m + 1)), f (m + 1 + x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxlt : x < N - (m + 1) := Finset.mem_range.mp hx
    have hkltN : m + 1 + x < N := by omega
    have hnon := hnonpos ⟨m + 1 + x, hkltN⟩ (by simp)
    simp [f, hkltN, posPart_eq_zero.mpr hnon]
  rw [hfirst, htail, add_zero]

/--
A decreasing finite real sequence is either everywhere nonpositive, or its
nonnegative entries form a nonempty initial segment.
-/
theorem antitone_fin_nonpos_or_initial_nonneg_segment
    {N : ℕ} (lam : Fin N → ℝ) (hanti : Antitone lam) :
    (∀ i : Fin N, lam i ≤ 0) ∨
      ∃ m : ℕ, ∃ hN : m + 1 ≤ N,
        (∀ r : Fin (m + 1), 0 ≤ lam (Fin.castLE hN r)) ∧
        (∀ i : Fin N, m + 1 ≤ (i : ℕ) → lam i ≤ 0) := by
  classical
  by_cases hall : ∀ i : Fin N, lam i ≤ 0
  · exact Or.inl hall
  · right
    have hExistsNot : ∃ i : Fin N, ¬ lam i ≤ 0 := not_forall.mp hall
    rcases hExistsNot with ⟨i0, hi0⟩
    have hi0nonneg : 0 ≤ lam i0 := le_of_lt (lt_of_not_ge hi0)
    let S : Finset (Fin N) := Finset.univ.filter fun i => 0 ≤ lam i
    have hSnonempty : S.Nonempty := by
      refine ⟨i0, ?_⟩
      simp [S, hi0nonneg]
    rcases Finset.exists_max_image S (fun i : Fin N => (i : ℕ)) hSnonempty with
      ⟨imax, himax_mem, himax_max⟩
    let m : ℕ := imax
    have hmN : m + 1 ≤ N := Nat.succ_le_of_lt imax.isLt
    refine ⟨m, hmN, ?_, ?_⟩
    · intro r
      have hrle : (Fin.castLE hmN r : Fin N) ≤ imax := by
        exact Nat.lt_succ_iff.mp r.isLt
      have himax_nonneg : 0 ≤ lam imax := by
        have := (Finset.mem_filter.mp himax_mem).2
        simpa [S] using this
      exact himax_nonneg.trans (hanti hrle)
    · intro i hi
      by_contra hnot
      have hinonneg : 0 ≤ lam i := le_of_lt (lt_of_not_ge hnot)
      have hi_mem : i ∈ S := by
        simp [S, hinonneg]
      have hile : (i : ℕ) ≤ m := himax_max i hi_mem
      omega

private theorem positiveEigenCoordinateData_of_sorted_segment
    {d : Type*} [Fintype d] [DecidableEq d] {N m : ℕ}
    (hN : m + 1 ≤ N)
    (A : Matrix d d ℝ) (hSym : RealSymmetric A)
    (τ : ℝ)
    (hn : Module.finrank ℝ (EuclideanSpace ℝ d) = N)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (htrace :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      τ = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r)) :
    HasPositiveEigenCoordinateData A τ := by
  classical
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (realSymmetric_isHermitian A hSym)
  let embed : Fin (m + 1) → Fin (N) := Fin.castLE hN
  let v : Fin (m + 1) → d → ℝ :=
    fun i => ⇑(hT.eigenvectorBasis hn (embed i))
  let s : ℕ → ℝ :=
    fun k =>
      if hk : k ≤ m then
        hT.eigenvalues hn (embed ⟨k, Nat.lt_succ_of_le hk⟩)
      else 0
  refine ⟨m, v, s, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    have horth := (orthonormal_iff_ite.mp (hT.eigenvectorBasis hn).orthonormal)
      (embed i) (embed k)
    rw [realDot_euclidean_eq_inner]
    simpa [v, embed, Fin.ext_iff] using horth
  · intro r j
    have hr : (r : ℕ) ≤ m := Nat.lt_succ_iff.mp r.isLt
    have hidx : embed ⟨(r : ℕ), Nat.lt_succ_of_le hr⟩ = embed r := by
      ext
      simp [embed]
    have h := congrArg (fun y : EuclideanSpace ℝ d => y j)
      (hT.apply_eigenvectorBasis hn (embed r))
    rw [toEuclideanLin_apply_eq_sum A (hT.eigenvectorBasis hn (embed r)) j] at h
    simpa [v, s, hr, hidx, Pi.smul_apply, smul_eq_mul] using h
  · intro i k hik
    by_cases hk : k ≤ m
    · have hi : i ≤ m := le_trans hik hk
      have hfin : (embed ⟨i, Nat.lt_succ_of_le hi⟩ : Fin (N)) ≤
          embed ⟨k, Nat.lt_succ_of_le hk⟩ := by
        exact hik
      have hanti := hT.eigenvalues_antitone hn hfin
      simpa [s, hi, hk] using hanti
    · by_cases hi : i ≤ m
      · have hnonneg := hpos ⟨i, Nat.lt_succ_of_le hi⟩
        change 0 ≤ hT.eigenvalues hn
          (Fin.castLE hN (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (m + 1))) at hnonneg
        simpa [s, hi, hk, embed] using hnonneg
      · simp [s, hi, hk]
  · simp [s]
  · rw [htrace]
    apply Finset.sum_congr rfl
    intro i _hi
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    have hidx :
        embed ⟨(i : ℕ), Nat.lt_succ_of_le hi⟩ = Fin.castLE hN i := by
      ext
      simp [embed]
    simp [s, hi, hidx]

/--
Positive initial segment construction for an arbitrary finite coordinate
type, indexed through Mathlib's canonical sorted eigenvalue list.
-/
theorem hasPositiveEigenCoordinateData_of_sorted_positiveInitialSegment_card
    {d : Type*} [Fintype d] [DecidableEq d] {m : ℕ}
    (hN : m + 1 ≤ Fintype.card d)
    (A : Matrix d d ℝ) (hSym : RealSymmetric A)
    (τ : ℝ)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
        finrank_euclideanSpace
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (htrace :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
        finrank_euclideanSpace
      τ = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r)) :
    HasPositiveEigenCoordinateData A τ := by
  exact positiveEigenCoordinateData_of_sorted_segment hN A hSym τ
    finrank_euclideanSpace hpos htrace

/--
An initial segment of Mathlib's sorted Euclidean eigenbasis gives the positive
eigen-coordinate data consumed by Ball--Prodromou.  The hypotheses say that the
selected `m+1` sorted eigenvalues are nonnegative and have total `τ`.
-/
theorem hasPositiveEigenCoordinateData_of_sorted_positiveInitialSegment
    {N m : ℕ} (hN : m + 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hSym : RealSymmetric A)
    (τ : ℝ)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (htrace :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      τ = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r)) :
    HasPositiveEigenCoordinateData A τ := by
  exact positiveEigenCoordinateData_of_sorted_segment hN A hSym τ
    finrank_euclideanSpace_fin hpos htrace

/--
The explicit eigen-coordinate data obtained from a positive spectral subspace
supplies the diagonal model consumed by Ball--Prodromou.
-/
theorem hasBallProdromouDiagonalModel_of_eigenCoordinateData
    {d : Type*} [Fintype d] (A : Matrix d d ℝ) (τ : ℝ)
    (hdata : HasPositiveEigenCoordinateData A τ) :
    HasBallProdromouDiagonalModel A τ := by
  classical
  rcases hdata with ⟨m, v, s, horth, heigen, hanti, hs_last, htrace⟩
  refine ⟨m, coordinateConstraintVectors v, s, ?_, hanti, hs_last, htrace, ?_⟩
  · exact parseval_coordinateConstraintVectors v horth
  · intro w
    have hamb :
        (fun j => realDot w (coordinateConstraintVectors v j)) =
          ambientOfEigenCoordinates v w := by
      funext j
      simp [coordinateConstraintVectors, ambientOfEigenCoordinates, realDot]
    rw [hamb]
    exact realQuadraticForm_ambientOfEigenCoordinates A v s horth heigen w

/-- Eigen-coordinate data feeds directly into the BP cube quadratic maximum. -/
theorem cubeQuadraticMaximum_from_eigenCoordinateData
    {d : Type*} [Fintype d] (A : Matrix d d ℝ) (τ : ℝ)
    (hdata : HasPositiveEigenCoordinateData A τ) :
    ∃ x : d → ℝ, InRealUnitCube x ∧ τ ≤ realQuadraticForm A x :=
  cubeQuadraticMaximum_from_diagonalBP A τ
    (hasBallProdromouDiagonalModel_of_eigenCoordinateData A τ hdata)

/--
Any support-function upper bound `tr(AG) ≤ τ`, together with
Ball--Prodromou eigen-coordinate data proving `τ ≤ qᵀAq` for some cube vector,
gives the support inequality needed by the convex-hull argument.
-/
theorem supportInequality_from_upperBound_and_eigenCoordinateData
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (τ : ℝ)
    (hupper : ∀ G : Matrix d d ℝ,
      RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
        (A * G).trace ≤ τ)
    (hdata : HasPositiveEigenCoordinateData A τ) :
    ∃ x : d → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix d d ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  rcases cubeQuadraticMaximum_from_eigenCoordinateData A τ hdata with
    ⟨x, hcube, hx⟩
  refine ⟨x, hcube, ?_⟩
  intro G hGsym hGbetween
  exact (hupper G hGsym hGbetween).trans hx

/--
Positive spectral-coordinate data plus the positive-part support-function
property gives the support inequality used in the convex-hull argument.
-/
theorem supportInequality_from_eigenCoordinateData
    {d : Type*} [Fintype d] [DecidableEq d]
    (A Apos : Matrix d d ℝ)
    (hsupport : HasPositivePartSupportFunction A Apos)
    (hdata : HasPositiveEigenCoordinateData A Apos.trace) :
    ∃ x : d → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix d d ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  exact supportInequality_from_upperBound_and_eigenCoordinateData A Apos.trace
    (fun G hGsym hGbetween => hsupport.1 G hGsym hGbetween) hdata

/--
The same support inequality, using the abstract positive/negative spectral-part
criterion for the support-function property.
-/
theorem supportInequality_from_posNegProjection_and_eigenData
    {d : Type*} [Fintype d] [DecidableEq d]
    (A Apos Aneg Ppos : Matrix d d ℝ)
    (hAeq : A = Apos - Aneg)
    (hAposSym : RealSymmetric Apos) (hAnegSym : RealSymmetric Aneg)
    (hAposPSD : RealPSD Apos) (hAnegPSD : RealPSD Aneg)
    (hPposSym : RealSymmetric Ppos)
    (hPposBetween : RealLoewnerBetweenZeroAndOne Ppos)
    (hApos_mul_Ppos : Apos * Ppos = Apos)
    (hAneg_mul_Ppos : Aneg * Ppos = 0)
    (hdata : HasPositiveEigenCoordinateData A Apos.trace) :
    ∃ x : d → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix d d ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  exact supportInequality_from_eigenCoordinateData A Apos
    (hasPositivePartSupportFunction_of_posNegProjection
      A Apos Aneg Ppos hAeq hAposSym hAnegSym hAposPSD hAnegPSD
      hPposSym hPposBetween hApos_mul_Ppos hAneg_mul_Ppos)
    hdata

/--
CFC positive part plus a nonnegative sorted initial eigenvalue segment gives
the support inequality for the symmetric test matrix `A`.
-/
theorem supportInequality_from_cfc_posPart_initialSegment
    {N m : ℕ} (hN : m + 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hSym : RealSymmetric A)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (htrace :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      (A⁺).trace = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r)) :
    ∃ x : Fin N → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix (Fin N) (Fin N) ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x :=
  supportInequality_from_upperBound_and_eigenCoordinateData A (A⁺).trace
    (supportUpperBound_cfc_posPart A hSym)
    (hasPositiveEigenCoordinateData_of_sorted_positiveInitialSegment
      hN A hSym (A⁺).trace hpos htrace)

/--
If the CFC positive-part trace is known to be the sum of positive parts of the
sorted eigenvalues, then a sign pattern for an initial segment identifies that
trace with the initial segment sum.
-/
theorem trace_posPart_eq_sum_initialSegment_of_sorted_signs
    {N m : ℕ} (hN : m + 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hSym : RealSymmetric A)
    (htracePosParts :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      (A⁺).trace = ∑ i : Fin N, (hT.eigenvalues hn i)⁺)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (hnonpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      ∀ i : Fin N, m + 1 ≤ (i : ℕ) → hT.eigenvalues hn i ≤ 0) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (realSymmetric_isHermitian A hSym)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
      finrank_euclideanSpace_fin
    (A⁺).trace = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r) := by
  intro hT hn
  rw [htracePosParts]
  exact sum_posPart_eq_sum_initialSegment_of_signs hN
    (fun i : Fin N => hT.eigenvalues hn i) hpos hnonpos

/--
The support inequality follows from a sorted eigenvalue sign pattern, once the
CFC positive-part trace has been identified with the sorted positive-part sum.
-/
theorem supportInequality_from_cfc_posPart_sorted_signs
    {N m : ℕ} (hN : m + 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hSym : RealSymmetric A)
    (htracePosParts :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      (A⁺).trace = ∑ i : Fin N, (hT.eigenvalues hn i)⁺)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (hnonpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      ∀ i : Fin N, m + 1 ≤ (i : ℕ) → hT.eigenvalues hn i ≤ 0) :
    ∃ x : Fin N → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix (Fin N) (Fin N) ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  have htrace :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N :=
        finrank_euclideanSpace_fin
      (A⁺).trace = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r) :=
    trace_posPart_eq_sum_initialSegment_of_sorted_signs
      hN A hSym htracePosParts hpos hnonpos
  exact supportInequality_from_cfc_posPart_initialSegment hN A hSym hpos htrace

/--
For an arbitrary finite coordinate type, a sorted eigenvalue sign pattern
identifies the CFC positive-part trace with the nonnegative initial segment.
-/
theorem trace_posPart_eq_sum_initialSegment_of_sorted_signs_card
    {d : Type*} [Fintype d] [DecidableEq d] {m : ℕ}
    (hN : m + 1 ≤ Fintype.card d)
    (A : Matrix d d ℝ) (hSym : RealSymmetric A)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
        finrank_euclideanSpace
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (hnonpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
        finrank_euclideanSpace
      ∀ i : Fin (Fintype.card d), m + 1 ≤ (i : ℕ) →
        hT.eigenvalues hn i ≤ 0) :
    let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (realSymmetric_isHermitian A hSym)
    let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
      finrank_euclideanSpace
    (A⁺).trace = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r) := by
  intro hT hn
  rw [trace_posPart_eq_sum_eigenvalues₀ A hSym]
  exact sum_posPart_eq_sum_initialSegment_of_signs hN
    (fun i : Fin (Fintype.card d) => hT.eigenvalues hn i) hpos hnonpos

/--
For an arbitrary finite coordinate type, the CFC positive-part support
inequality follows from a sorted eigenvalue sign pattern.
-/
theorem supportInequality_from_cfc_posPart_sorted_signs_card
    {d : Type*} [Fintype d] [DecidableEq d] {m : ℕ}
    (hN : m + 1 ≤ Fintype.card d)
    (A : Matrix d d ℝ) (hSym : RealSymmetric A)
    (hpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
        finrank_euclideanSpace
      ∀ r : Fin (m + 1), 0 ≤ hT.eigenvalues hn (Fin.castLE hN r))
    (hnonpos :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
        finrank_euclideanSpace
      ∀ i : Fin (Fintype.card d), m + 1 ≤ (i : ℕ) →
        hT.eigenvalues hn i ≤ 0) :
    ∃ x : d → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix d d ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  have htrace :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
        finrank_euclideanSpace
      (A⁺).trace = ∑ r : Fin (m + 1), hT.eigenvalues hn (Fin.castLE hN r) :=
    trace_posPart_eq_sum_initialSegment_of_sorted_signs_card
      hN A hSym hpos hnonpos
  exact supportInequality_from_upperBound_and_eigenCoordinateData A (A⁺).trace
    (supportUpperBound_cfc_posPart A hSym)
    (hasPositiveEigenCoordinateData_of_sorted_positiveInitialSegment_card
      hN A hSym (A⁺).trace hpos htrace)

/--
If the CFC positive part has zero trace, the support inequality is witnessed by
the zero cube vector, for any finite coordinate type.
-/
theorem supportInequality_of_cfc_posPart_trace_zero_card
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (hSym : RealSymmetric A)
    (htrace0 : (A⁺).trace = 0) :
    ∃ x : d → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix d d ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  refine ⟨0, ?_, ?_⟩
  · intro i
    simp
  · intro G hGsym hGbetween
    have hupper := supportUpperBound_cfc_posPart A hSym G hGsym hGbetween
    rw [htrace0] at hupper
    simpa [realQuadraticForm] using hupper

/--
Ball--Prodromou plus the CFC positive part gives the support inequality for
every real symmetric test matrix on an arbitrary finite coordinate type.
-/
theorem supportInequality_from_cfc_posPart_card
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (hSym : RealSymmetric A) :
    ∃ x : d → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix d d ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  classical
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (realSymmetric_isHermitian A hSym)
  let hn : Module.finrank ℝ (EuclideanSpace ℝ d) = Fintype.card d :=
    finrank_euclideanSpace
  have hcut :=
    antitone_fin_nonpos_or_initial_nonneg_segment
      (fun i : Fin (Fintype.card d) => hT.eigenvalues hn i)
      (hT.eigenvalues_antitone hn)
  rcases hcut with hall | ⟨m, hN, hpos, hnonpos⟩
  · refine supportInequality_of_cfc_posPart_trace_zero_card A hSym ?_
    rw [trace_posPart_eq_sum_eigenvalues₀ A hSym]
    apply Finset.sum_eq_zero
    intro i _hi
    exact posPart_eq_zero.mpr (hall i)
  · exact supportInequality_from_cfc_posPart_sorted_signs_card
      hN A hSym hpos hnonpos

/--
Ball--Prodromou and separation put every real symmetric `0 ≤ T ≤ I` into the
closed convex hull of flattened rank-one cube matrices.

The remaining step toward `HasRealConvexDecomposition` is to replace this
closed-hull membership by ordinary convex-hull membership for the compact
rank-one cube image.
-/
theorem matrixToEuclidean_mem_closedConvexHull_rankOneCube_of_loewner
    {d : Type*} [Fintype d] [DecidableEq d]
    (T : Matrix d d ℝ) (hT : RealSymmetric T)
    (hTbetween : RealLoewnerBetweenZeroAndOne T) :
    matrixToEuclidean T ∈
      closedConvexHull ℝ (realRankOneCubeEuclideanSet d) := by
  classical
  by_contra hnot
  rcases geometric_hahn_banach_point_closed
      (convex_closedConvexHull (𝕜 := ℝ) (s := realRankOneCubeEuclideanSet d))
      (isClosed_closedConvexHull (𝕜 := ℝ) (s := realRankOneCubeEuclideanSet d))
      hnot with ⟨f, u, hTf, hsep⟩
  let y : EuclideanSpace ℝ (d × d) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (d × d))).symm f
  let Aflat : EuclideanSpace ℝ (d × d) := -y
  let A : Matrix d d ℝ := euclideanToMatrix Aflat
  rcases supportInequality_from_cfc_posPart_card (realSymmPart A)
      (realSymmetric_realSymmPart A) with ⟨q, hq, hsupport⟩
  have htrace := hsupport T hT hTbetween
  have hflatA : matrixToEuclidean A = Aflat :=
    matrixToEuclidean_euclideanToMatrix Aflat
  have hinnerT_trace :
      inner ℝ Aflat (matrixToEuclidean T) =
        (realSymmPart A * T).trace := by
    rw [← hflatA]
    rw [inner_matrixToEuclidean_eq_trace_transpose_mul]
    exact trace_transpose_mul_eq_trace_realSymmPart_mul_of_realSymmetric A T hT
  have hinnerQ_trace :
      inner ℝ Aflat (matrixToEuclidean (realRankOne q)) =
        realQuadraticForm (realSymmPart A) q := by
    rw [← hflatA]
    rw [inner_matrixToEuclidean_realRankOne_eq_realQuadraticForm]
    exact (realQuadraticForm_realSymmPart A q).symm
  have hinner :
      inner ℝ Aflat (matrixToEuclidean T) ≤
        inner ℝ Aflat (matrixToEuclidean (realRankOne q)) := by
    simpa [hinnerT_trace, hinnerQ_trace] using htrace
  have hA_T :
      inner ℝ Aflat (matrixToEuclidean T) = -f (matrixToEuclidean T) := by
    simp [Aflat, y, InnerProductSpace.toDual_symm_apply]
  have hA_q :
      inner ℝ Aflat (matrixToEuclidean (realRankOne q)) =
        -f (matrixToEuclidean (realRankOne q)) := by
    simp [Aflat, y, InnerProductSpace.toDual_symm_apply]
  have hf_le :
      f (matrixToEuclidean (realRankOne q)) ≤ f (matrixToEuclidean T) := by
    rw [hA_T, hA_q] at hinner
    linarith
  have hqclosed :
      matrixToEuclidean (realRankOne q) ∈
        closedConvexHull ℝ (realRankOneCubeEuclideanSet d) := by
    exact subset_closedConvexHull ⟨realRankOne q, ⟨q, hq, rfl⟩, rfl⟩
  have hsepq :
      u < f (matrixToEuclidean (realRankOne q)) :=
    hsep (matrixToEuclidean (realRankOne q)) hqclosed
  linarith

/--
For the compact rank-one cube image, the closed-convex-hull membership from
separation is ordinary convex-hull membership.
-/
theorem matrixToEuclidean_mem_convexHull_rankOneCube_of_loewner
    {d : Type*} [Fintype d] [DecidableEq d]
    (T : Matrix d d ℝ) (hT : RealSymmetric T)
    (hTbetween : RealLoewnerBetweenZeroAndOne T) :
    matrixToEuclidean T ∈ convexHull ℝ (realRankOneCubeEuclideanSet d) := by
  have hclosed :=
    matrixToEuclidean_mem_closedConvexHull_rankOneCube_of_loewner T hT hTbetween
  rwa [closedConvexHull_eq_convexHull_of_isCompact
    (isCompact_realRankOneCubeEuclideanSet (d := d))] at hclosed

/--
Real convex decomposition of every symmetric matrix satisfying `0 ≤ T ≤ I`.

This is the finite-dimensional convex-hull extraction step in the paper:
membership of `T` in the convex hull of the rank-one cube matrices is unpacked
into explicit weights and cube vectors.
-/
theorem hasRealConvexDecomposition
    (d : Type*) [Fintype d] [DecidableEq d] :
    HasRealConvexDecomposition d := by
  classical
  intro T hT hTbetween
  have hconv :=
    matrixToEuclidean_mem_convexHull_rankOneCube_of_loewner T hT hTbetween
  rw [mem_convexHull_iff_exists_fintype] at hconv
  rcases hconv with ⟨ι, hι, w, z, hw, hsum, hz, hcenter⟩
  let : Fintype ι := hι
  let m := Fintype.card ι
  have hm : 0 < m := by
    by_contra hnot
    have hzero : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos hnot
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hzero
    simp at hsum
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let p : Fin m → ℝ := fun r => w (e.symm r)
  have hz_rank :
      ∀ r : Fin m, ∃ q : d → ℝ,
        InRealUnitCube q ∧ z (e.symm r) = matrixToEuclidean (realRankOne q) := by
    intro r
    rcases hz (e.symm r) with ⟨R, ⟨q, hq, hR⟩, hzR⟩
    exact ⟨q, hq, by rw [← hzR, hR]⟩
  let q : Fin m → d → ℝ := fun r => Classical.choose (hz_rank r)
  have hqcube : ∀ r, InRealUnitCube (q r) :=
    fun r => (Classical.choose_spec (hz_rank r)).1
  have hz_eq : ∀ r, z (e.symm r) = matrixToEuclidean (realRankOne (q r)) :=
    fun r => (Classical.choose_spec (hz_rank r)).2
  have hp : ∀ r, 0 ≤ p r := fun r => hw (e.symm r)
  have hpsum : ∑ r, p r = 1 := by
    rw [← hsum]
    symm
    simpa [p] using Equiv.sum_comp e
      (fun r : Fin m => w (e.symm r))
  have hcenter_fin :
      ∑ r : Fin m, p r • z (e.symm r) = matrixToEuclidean T := by
    rw [← hcenter]
    symm
    simpa [p] using Equiv.sum_comp e
      (fun r : Fin m => w (e.symm r) • z (e.symm r))
  have hvec :
      ∑ r : Fin m, p r • matrixToEuclidean (realRankOne (q r)) =
        matrixToEuclidean T := by
    simpa [hz_eq] using hcenter_fin
  refine ⟨m, hm, p, q, hp, hpsum, hqcube, ?_⟩
  intro a b
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (d × d) => v (a, b)) hvec
  simpa [matrixToEuclidean, realRankOne, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm] using hcoord.symm

/--
If the CFC positive part has zero trace, the support inequality is witnessed by
the zero cube vector.
-/
theorem supportInequality_of_cfc_posPart_trace_zero
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hSym : RealSymmetric A)
    (htrace0 : (A⁺).trace = 0) :
    ∃ x : Fin N → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix (Fin N) (Fin N) ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  refine ⟨0, ?_, ?_⟩
  · intro i
    simp
  · intro G hGsym hGbetween
    have hupper := supportUpperBound_cfc_posPart A hSym G hGsym hGbetween
    rw [htrace0] at hupper
    simpa [realQuadraticForm] using hupper

/--
Ball--Prodromou in matrix form for a positive semidefinite real symmetric matrix
whose eigenvalues are indexed in decreasing order.
-/
theorem cubeQuadraticMaximum_of_realPSD_fin
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A)
    (hantiEig : Antitone (realSymmetric_isHermitian A hSym).eigenvalues) :
    ∃ x : Fin (m + 1) → ℝ,
      InRealUnitCube x ∧ A.trace ≤ realQuadraticForm A x :=
  cubeQuadraticMaximum_from_eigenCoordinateData A A.trace
    (hasPositiveEigenCoordinateData_of_realPSD_fin A hSym hPSD hantiEig)

/--
Ball--Prodromou cube quadratic maximum from Mathlib's sorted Euclidean spectral
data, with the remaining trace-identification hypothesis explicit.
-/
theorem cubeQuadraticMaximum_of_realPSD_fin_sorted_of_trace
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A)
    (htraceSorted :
      let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
        (realSymmetric_isHermitian A hSym)
      let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
        finrank_euclideanSpace_fin
      A.trace = ∑ i, hT.eigenvalues hn i) :
    ∃ x : Fin (m + 1) → ℝ,
      InRealUnitCube x ∧ A.trace ≤ realQuadraticForm A x :=
  cubeQuadraticMaximum_from_eigenCoordinateData A A.trace
    (hasPositiveEigenCoordinateData_of_realPSD_fin_sorted_of_trace
      A hSym hPSD htraceSorted)

/--
Ball--Prodromou in matrix form for a positive semidefinite real symmetric matrix,
using Mathlib's sorted Euclidean spectral data directly.
-/
theorem cubeQuadraticMaximum_of_realPSD_fin_sorted
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A) :
    ∃ x : Fin (m + 1) → ℝ,
      InRealUnitCube x ∧ A.trace ≤ realQuadraticForm A x :=
  cubeQuadraticMaximum_from_eigenCoordinateData A A.trace
    (hasPositiveEigenCoordinateData_of_realPSD_fin_sorted A hSym hPSD)

/--
For a positive semidefinite real symmetric test matrix, Ball--Prodromou gives a
single cube vector whose quadratic value dominates all trace pairings
`tr(AG)` with `0 ≤ G ≤ I`.
-/
theorem supportInequality_of_realPSD_fin_sorted
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hSym : RealSymmetric A) (hPSD : RealPSD A) :
    ∃ x : Fin (m + 1) → ℝ,
      InRealUnitCube x ∧
      ∀ G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
        RealSymmetric G → RealLoewnerBetweenZeroAndOne G →
          (A * G).trace ≤ realQuadraticForm A x := by
  rcases cubeQuadraticMaximum_of_realPSD_fin_sorted A hSym hPSD with
    ⟨x, hcube, hx⟩
  refine ⟨x, hcube, ?_⟩
  intro G hGsym hGbetween
  exact ((hasPositivePartSupportFunction_of_realPSD A hSym hPSD).1
    G hGsym hGbetween).trans hx

end OlevskiiGram
