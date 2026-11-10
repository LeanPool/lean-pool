/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.MvPowerSeriesPDeriv
public import LeanPool.HyperellipticCurves.Log.Ftau.FtauAssoc
public import LeanPool.HyperellipticCurves.Log.Ftau.FtauBasic
public import LeanPool.HyperellipticCurves.Log.Trace.TracePipeline
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Trace-form inputs on the chart blocks

The per-block inputs of the trace-form invariance identity, in the form the fold route
consumes (`Log/Fold/FoldTrace`, `Log/Fold/FoldAssemble`):

* the chart coordinates of a transported chart datum are exactly the variables of its side
  (`ChabautyColeman.chartU_map_rename_eq`), so the `X`-side block is `∂/∂Y_k`-constant
  (`ChabautyColeman.traceDiff_ftauUX_eq_zero`) and the `Y`-side block contributes the `k`-th
  column of the trace matrix (`ChabautyColeman.traceDiff_ftauUY`);
* at `Y = 0` the right-hand side of the invariance identity is the **constant** trace matrix
  of the `τ`-datum itself over `O` (`ChabautyColeman.traceMat_map_setYZero_eq_C`);
* residue bookkeeping for polynomials over `MvPowerSeries` with prescribed center
  (`ChabautyColeman.map_residue_eq'`).

The invariance identity itself is run along the fold pipeline
(`ChabautyColeman.sum_traceMat_ftauFoldPipe`).

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section Ftau

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}

/-- The transported chart `u`-polynomial, in chart form: the center displaced by the
variables of the chosen side. -/
theorem chartU_map_rename_eq (e : Fin n → Fin n ⊕ Fin n) [Filter.TendstoCofinite e] (u : O[X]) :
    (chartU u n).map (MvPowerSeries.rename (R := O) e).toRingHom
      = u.map MvPowerSeries.C
        + ∑ i : Fin n, C (MvPowerSeries.X (e i)) * X ^ (i : ℕ) := by
  rw [chartU, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_map, rename_comp_C]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  simp

variable (k : Fin n)

/-- The coefficients of a polynomial over the constants are killed by every `∂/∂X_s`. -/
theorem pderiv_coeff_map_C_eq_zero (p : O[X]) (i : ℕ) :
    MvPowerSeries.pderiv (Sum.inr k)
      ((p.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).coeff i) = 0 := by
  rw [coeff_map]
  simp

/-- The trace-form differential of a transported chart datum, expanded along its chart
coordinates: those are the variables of the chosen side, so only their `∂/∂Y_k`-derivatives
remain. -/
theorem traceDiff_chartU_map_rename (e : Fin n → Fin n ⊕ Fin n) [Filter.TendstoCofinite e]
    (s : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) (i : ℕ) :
    traceDiff (MvPowerSeries.pderiv (Sum.inr k))
        ((chartU u n).map (MvPowerSeries.rename (R := O) e).toRingHom) s i
      = ∑ j : Fin n, traceMat ((chartU u n).map (MvPowerSeries.rename (R := O) e).toRingHom) s i j
          * MvPowerSeries.pderiv (Sum.inr k) (MvPowerSeries.X (e j)) :=
  traceDiff_eq_sum _ (pderiv_coeff_map_C_eq_zero k u) (chartU_map_rename_eq e u) s i

/-- The `X`-side block is `∂/∂Y_k`-constant: its chart coordinates are the `X`-variables. -/
theorem traceDiff_ftauUX_eq_zero (s : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) (i : ℕ) :
    traceDiff (MvPowerSeries.pderiv (Sum.inr k)) (ftauUX u n) s i = 0 := by
  classical
  rw [ftauUX, traceDiff_chartU_map_rename k Sum.inl s i]
  exact Finset.sum_eq_zero fun j _ ↦ by simp

/-- The `Y`-side block contributes the `k`-th column of the trace matrix. -/
theorem traceDiff_ftauUY (s : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) (i : ℕ) :
    traceDiff (MvPowerSeries.pderiv (Sum.inr k)) (ftauUY u n) s i
      = traceMat (ftauUY u n) s i k := by
  classical
  rw [ftauUY, traceDiff_chartU_map_rename k Sum.inr s i,
    Finset.sum_eq_single_of_mem k (Finset.mem_univ k) fun j _ hj ↦ by
      simp [hj]]
  simp

end Ftau

section YZero

variable {O : Type*} [CommRing O] [Nontrivial O] {n : ℕ} {f u v w c₁ c₂ : O[X]}
  {hu : u.Monic} {hne : u.natDegree = n} {hv : v.degree < u.degree} {hw : v ^ 2 - f = u * w}
  {hbez : c₁ * u + c₂ * (2 * v) = 1} {dt : CantorCertData (MvPowerSeries (Fin n ⊕ Fin n) O)}

variable {i : ℕ} {cY sY : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)}

/-- The right-hand side of the invariance identity at `Y = 0` is a **constant** matrix: the
trace matrix of the `τ`-datum itself, over `O`. Its cofactor is the one from the datum's own
Bézout certificate, the trace matrix not depending on that choice. -/
theorem traceMat_map_setYZero_eq_C
    (hsY : cY * ftauUY u n + sY * (2 * ftauVY hu hne hv hw hbez) = 1) (j : ℕ) :
    traceMat (u.map MvPowerSeries.C) (sY.map setYZero) i j
      = MvPowerSeries.C (traceMat u c₂ i j) := by
  have h1 : cY.map setYZero * u.map MvPowerSeries.C
      + sY.map setYZero * (2 * v.map MvPowerSeries.C) = 1 := by
    have h := map_bezout
      (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O) hsY
    rwa [ftauUY_map_setYZero, ftauVY_map_setYZero] at h
  have h2 : c₁.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) * u.map MvPowerSeries.C
      + c₂.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)
        * (2 * v.map MvPowerSeries.C) = 1 :=
    map_bezout (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) hbez
  rw [traceMat_congr (hu.map _) h1 h2 i j, ← traceMat_map MvPowerSeries.C hu c₂ i j]

section Residue

variable {σ O : Type*} [CommRing O] [IsLocalRing O]

/-- Two multivariate power series whose constant coefficients differ by an element of the
maximal ideal have the same residue. -/
theorem residue_eq_of_constantCoeff_sub_mem' {x y : MvPowerSeries σ O}
    (h : MvPowerSeries.constantCoeff x - MvPowerSeries.constantCoeff y ∈ maximalIdeal O) :
    residue (MvPowerSeries σ O) x = residue (MvPowerSeries σ O) y := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff, map_sub]
  exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp h)

/-- A polynomial over `MvPowerSeries σ O` with prescribed center has the residue of that
center. -/
theorem map_residue_eq' {P : Polynomial (MvPowerSeries σ O)} {q : O[X]}
    (h : P.map (MvPowerSeries.constantCoeff : MvPowerSeries σ O →+* O) = q) :
    P.map (residue (MvPowerSeries σ O))
      = (q.map (MvPowerSeries.C : O →+* MvPowerSeries σ O)).map (residue (MvPowerSeries σ O)) :=
  Polynomial.ext fun k ↦ by
    simp only [Polynomial.coeff_map]
    refine residue_eq_of_constantCoeff_sub_mem' ?_
    rw [MvPowerSeries.constantCoeff_C, ← h, Polynomial.coeff_map, sub_self]
    exact zero_mem _

end Residue

end YZero

end ChabautyColeman

end
