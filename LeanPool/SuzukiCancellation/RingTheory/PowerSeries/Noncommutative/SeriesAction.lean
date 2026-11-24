/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ScalarSubstitution
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Cauchy action of operator series

A formal series of rational linear endomorphisms acts by finite Cauchy
convolution on vector-valued series. Associativity lets scalar functional
calculus act on locally degree-raising operators.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Cauchy convolution of an operator series with a vector-valued series. -/
def seriesLinearAction (P : PowerSeries (Module.End ℚ A)) (V : PowerSeries A) :
    PowerSeries A :=
  mk fun n ↦ ∑ ij ∈ antidiagonal n, (coeff ij.1 P) (coeff ij.2 V)

@[simp]
theorem coeff_seriesLinearAction (P : PowerSeries (Module.End ℚ A))
    (V : PowerSeries A) (n : ℕ) :
    coeff n (seriesLinearAction P V) =
      ∑ ij ∈ antidiagonal n, (coeff ij.1 P) (coeff ij.2 V) := by
  simp [seriesLinearAction]

/-- Operator convolution acts associatively. -/
theorem seriesLinearAction_mul (P Q : PowerSeries (Module.End ℚ A)) (V : PowerSeries A) :
    seriesLinearAction (P * Q) V = seriesLinearAction P (seriesLinearAction Q V) := by
  ext n
  simp only [coeff_seriesLinearAction, coeff_mul, LinearMap.sum_apply,
    mul_apply_eq_comp, map_sum, sum_sigma']
  apply sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
      aesop (add simp [mem_antidiagonal, add_assoc])

@[simp]
theorem seriesLinearAction_one (V : PowerSeries A) : seriesLinearAction 1 V = V := by
  ext n
  rw [coeff_seriesLinearAction, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [sum_eq_single 0]
  · simp
  · intro i hi hin
    simp [coeff_one, hin]
  · simp

theorem seriesLinearAction_add (P Q : PowerSeries (Module.End ℚ A)) (V : PowerSeries A) :
    seriesLinearAction (P + Q) V = seriesLinearAction P V + seriesLinearAction Q V := by
  ext n
  simp only [coeff_seriesLinearAction, map_add, LinearMap.add_apply, sum_add_distrib]

theorem seriesLinearAction_smul (r : ℚ) (P : PowerSeries (Module.End ℚ A))
    (V : PowerSeries A) : seriesLinearAction (r • P) V = r • seriesLinearAction P V := by
  ext n
  simp only [coeff_seriesLinearAction, coeff_smul, LinearMap.smul_apply, smul_sum]

theorem seriesLinearAction_sum {ι : Type*} (s : Finset ι)
    (f : ι → PowerSeries (Module.End ℚ A)) (V : PowerSeries A) :
    seriesLinearAction (∑ i ∈ s, f i) V = ∑ i ∈ s, seriesLinearAction (f i) V := by
  ext n
  simp only [coeff_seriesLinearAction, map_sum, LinearMap.sum_apply]
  rw [sum_comm]

/-- A coefficient of the Cauchy action only reads a finite operator prefix. -/
theorem coeff_seriesLinearAction_congr (P Q : PowerSeries (Module.End ℚ A))
    (V : PowerSeries A) (n : ℕ) (h : ∀ k, k ≤ n → coeff k P = coeff k Q) :
    coeff n (seriesLinearAction P V) = coeff n (seriesLinearAction Q V) := by
  simp only [coeff_seriesLinearAction]
  apply sum_congr rfl
  intro ij hij
  rw [h ij.1 (by have := mem_antidiagonal.mp hij; lia)]

/-- Scalar functional calculus of an operator series acts by a finite sum in each degree. -/
theorem coeff_seriesLinearAction_scalarSeriesApply (c : PowerSeries ℚ)
    (P : PowerSeries (Module.End ℚ A)) (hP : constantCoeff P = 0)
    (V : PowerSeries A) (n : ℕ) :
    coeff n (seriesLinearAction (scalarSeriesApply c (fun k ↦ coeff k P)) V) =
      ∑ j ∈ range (n + 1), coeff j c • coeff n (seriesLinearAction (P ^ j) V) := by
  calc
    _ = coeff n (seriesLinearAction
        (Polynomial.aeval P (trunc (n + 1) c)) V) := by
      apply coeff_seriesLinearAction_congr
      intro k hk
      rw [coeff_scalarSeriesApply_eq_aeval_trunc c _ k (n + 1) (by lia),
        positiveSeries_coeff P hP]
    _ = _ := by
      rw [Polynomial.aeval_def, eval₂_trunc_eq_sum_range]
      simp only [← Algebra.smul_def, seriesLinearAction_sum, seriesLinearAction_smul,
        map_sum, coeff_smul]

end FQFP
