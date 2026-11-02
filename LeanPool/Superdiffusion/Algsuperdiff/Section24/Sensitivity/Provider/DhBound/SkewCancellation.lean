/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.CoarseMatrixDerivativeCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn

/-!
# SkewCancellation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Pointwise skew cancellation for the `D_h` splitting identity

Source: ABK26 (proof of `l.Dh.bound`, `e.sensitivity.basic.split`), first step.
The splitting of the `D_h` quadratic form begins with the purely algebraic
observation that an antisymmetric matrix annihilates its own quadratic form, so
that
  `⨍ ∇w* · h ∇w = ⨍ ∇(w* + w) · h ∇w`.

This step involves **no integration by parts**: it is a pointwise algebraic
cancellation under the integral, valid for the almost-everywhere antisymmetric
carrier.  The genuine weak integration by parts (which requires the response
combination to lie in `H¹₀`) is kept strictly separate, in `WeakIBP.lean`.

This module proves:

* the finite-dimensional algebra (`sum_entry_mul_eq_zero_of_symmPart_eq_zero`,
  `vecDot_matVecMul_self_eq_zero_of_symmPart_eq_zero`);
* the almost-everywhere integrand cancellation
  (`skew_pairing_integrand_ae_eq`);
* the average-level cancellation at arbitrary response maximizers, stated on
  the frozen `coarseMatrixDerivative` quadratic form evaluated at `(p, -q)`
  (`quadForm_coarseMatrixDerivative_eq_average_sum_pairing`), which is the
  exact first step of `e.sensitivity.basic.split` for the frozen target
  `coarseMatrixDerivative_bound`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Entrywise antisymmetry from a vanishing symmetric part. -/
theorem entry_eq_neg_of_symmPart_eq_zero {H : Mat d} (hH : symmPart H = 0)
    (i j : Fin d) : H i j = -H j i := by
  have h : symmPart H i j = 0 := by rw [hH]; rfl
  have h' : (H i j + H j i) / 2 = 0 := h
  linarith

/-- A matrix with vanishing symmetric part annihilates every symmetric
two-index array. -/
theorem sum_entry_mul_eq_zero_of_symmPart_eq_zero {H B : Mat d}
    (hH : symmPart H = 0) (hB : ∀ i j, B i j = B j i) :
    ∑ i, ∑ j, H i j * B i j = 0 := by
  have hswap : (∑ i, ∑ j, H i j * B i j) = ∑ i, ∑ j, H j i * B j i :=
    Finset.sum_comm
  have hneg : (∑ i, ∑ j, H j i * B j i) = -∑ i, ∑ j, H i j * B i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [entry_eq_neg_of_symmPart_eq_zero hH j i, hB j i]
    ring
  have hzero : (∑ i, ∑ j, H i j * B i j) = -∑ i, ∑ j, H i j * B i j :=
    hswap.trans hneg
  linarith

/-- The quadratic form of a matrix with vanishing symmetric part is zero. -/
theorem vecDot_matVecMul_self_eq_zero_of_symmPart_eq_zero {H : Mat d}
    (hH : symmPart H = 0) (g : Vec d) :
    vecDot g (matVecMul H g) = 0 := by
  have hexpand : vecDot g (matVecMul H g) =
      ∑ i, ∑ j, H i j * (g i * g j) := by
    unfold vecDot matVecMul
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexpand]
  exact sum_entry_mul_eq_zero_of_symmPart_eq_zero hH fun i j => mul_comm (g i) (g j)

/-- Adding the second factor to the first factor of the skew pairing does not
change it: the pointwise skew-cancellation identity. -/
theorem vecDot_add_matVecMul_eq_of_symmPart_eq_zero {H : Mat d}
    (hH : symmPart H = 0) (f g : Vec d) :
    vecDot (f + g) (matVecMul H g) = vecDot f (matVecMul H g) := by
  rw [vecDot_add_left, vecDot_matVecMul_self_eq_zero_of_symmPart_eq_zero hH g,
    add_zero]

/-- Almost-everywhere integrand form of the skew cancellation for an a.e.
antisymmetric `L∞` matrix field. -/
theorem skew_pairing_integrand_ae_eq {U : Domain d}
    (h : LInfSkewMatrixFieldOn U) (F G : Vec d → Vec d) :
    (fun x => vecDot (F x) (matVecMul (h.1.1 x) (G x)))
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => vecDot (F x + G x) (matVecMul (h.1.1 x) (G x)) := by
  filter_upwards [h.2] with x hx
  exact (vecDot_add_matVecMul_eq_of_symmPart_eq_zero hx (F x) (G x)).symm

/-- Average-level skew cancellation for the `D_h` integrand: the source display
`⨍ ∇w* · h ∇w = ⨍ ∇(w* + w) · h ∇w`, with no integration by parts. -/
theorem average_skew_pairing_eq_average_sum_pairing (U : Domain d)
    (h : LInfSkewMatrixFieldOn U) (F G : Vec d → Vec d) :
    average U (fun x => vecDot (F x) (matVecMul (h.1.1 x) (G x))) =
      average U (fun x => vecDot (F x + G x) (matVecMul (h.1.1 x) (G x))) := by
  unfold Book.Ch02.average
  congr 1
  exact integral_congr_ae (skew_pairing_integrand_ae_eq h F G)

/-- **Skew-cancellation step of `e.sensitivity.basic.split`.**  At arbitrary
response maximizers `vAdj` (for `(aᵗ, p, -q)`) and `v` (for `(a, p, q)`), the
frozen `D_h` quadratic form at `(p, -q)` equals the average of the pairing with
the *summed* gradient `∇vAdj + ∇v` against `h ∇v`.  This is the pointwise
algebraic cancellation; no integration by parts is used. -/
theorem quadForm_coarseMatrixDerivative_eq_average_sum_pairing
    (U : Domain d) (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U)
    (p q : Vec d) (vAdj : Solution U a.transpose) (v : Solution U a)
    (hvAdj : IsResponseMaximizer U a.transpose p (-q) vAdj)
    (hv : IsResponseMaximizer U a p q v) :
    blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -q)) =
      average U (fun x =>
        vecDot (vAdj.toH1.grad x + v.toH1.grad x)
          (matVecMul (h.1.1 x) (v.toH1.grad x))) := by
  obtain ⟨-, hFormula, -⟩ := coarseMatrixDerivative_characterization U a h.1
  have hv' : IsResponseMaximizer U a p (- -q) v := by
    rwa [neg_neg]
  have hquad := hFormula p (-q) vAdj v hvAdj hv'
  rw [hquad]
  exact average_skew_pairing_eq_average_sum_pairing U h vAdj.toH1.grad v.toH1.grad

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound
