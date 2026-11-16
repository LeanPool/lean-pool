/-
Copyright (c) 2026 Dawid Trela and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela, Lean Pool contributors
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005

/-! # Shared interval arithmetic for the two angle residuals -/

@[expose] public section

namespace GerverSofa.PartE

open LeanCert.Core PartALeanCert

/-- Interval subtraction with the interpreter's original operation order. -/
def certificateSubtract (a b : IntervalRat) : IntervalRat := IntervalRat.add a (IntervalRat.neg b)

/-- Multiply an interval by a singleton rational interval. -/
def certificateScale (q : ℚ) (a : IntervalRat) : IntervalRat :=
  IntervalRat.mul (IntervalRat.singleton q) a

local infixl:65 " +ᵢ " => IntervalRat.add
local infixl:65 " -ᵢ " => certificateSubtract
local infixl:70 " *ᵢ " => IntervalRat.mul

/-- Evaluate the residual arithmetic directly, sharing its trigonometric subexpressions. -/
def certificateResidualsFromTrig (phi theta cp sp ct st : IntervalRat) :
    IntervalRat × IntervalRat :=
  let one := IntervalRat.singleton 1
  let half := IntervalRat.singleton (1 / 2)
  let delta := theta -ᵢ phi
  let base :=
    ((certificateScale (1 / 2) kernelPiInterval -ᵢ phi) -ᵢ theta +ᵢ
      certificateScale (1 / 2) delta) +ᵢ certificateScale (1 / 4) (delta *ᵢ delta)
  let den := cp -ᵢ (one +ᵢ certificateScale (1 / 2) delta) *ᵢ sp
  let num := (sp +ᵢ half +ᵢ IntervalRat.neg (certificateScale (1 / 2) cp)) +ᵢ base *ᵢ sp
  let numB := num *ᵢ (one +ᵢ certificateScale (1 / 2) delta) +ᵢ base *ᵢ den
  let r1 :=
    (num *ᵢ (ct -ᵢ cp) -ᵢ certificateScale 2 numB *ᵢ sp) +ᵢ
      ((delta -ᵢ one) *ᵢ ct) *ᵢ den -ᵢ st *ᵢ den +ᵢ cp *ᵢ den +ᵢ sp *ᵢ den
  let r2 :=
    (num *ᵢ (certificateScale 3 st +ᵢ sp) -ᵢ certificateScale 2 numB *ᵢ cp) +ᵢ
      (certificateScale 3 (delta -ᵢ one) *ᵢ st) *ᵢ den +ᵢ
      certificateScale 3 ct *ᵢ den -ᵢ sp *ᵢ den +ᵢ cp *ᵢ den
  (r1, r2)

/-- The original trigonometric evaluators supplied to the shared residual arithmetic. -/
def certificateResiduals (phi theta : IntervalRat) (depth : ℕ) : IntervalRat × IntervalRat :=
  certificateResidualsFromTrig phi theta
    (IntervalRat.cosComputable phi depth) (IntervalRat.sinComputable phi depth)
    (IntervalRat.cosComputable theta depth) (IntervalRat.sinComputable theta depth)

/-- Substitute certified trigonometric intervals without recomputing their Taylor series. -/
theorem certificateResiduals_eq_fromTrig (phi theta : IntervalRat) (depth : ℕ)
    (cp sp ct st : IntervalRat)
    (hcp : IntervalRat.cosComputable phi depth = cp)
    (hsp : IntervalRat.sinComputable phi depth = sp)
    (hct : IntervalRat.cosComputable theta depth = ct)
    (hst : IntervalRat.sinComputable theta depth = st) :
    certificateResiduals phi theta depth = certificateResidualsFromTrig phi theta cp sp ct st := by
  subst cp
  subst sp
  subst ct
  subst st
  rfl

/-- Either residual interval excludes zero. -/
def certificateRejects (residuals : IntervalRat × IntervalRat) : Bool :=
  intervalExcludesZero residuals.1 || intervalExcludesZero residuals.2

/-- The shared arithmetic agrees exactly with the original expression interpreter. -/
theorem rejected_eq_certificateResiduals (cell : AngleCell) (cfg : LeanCert.Engine.EvalConfig) :
    cell.rejected cfg = certificateRejects
      (certificateResiduals cell.phiI cell.thetaI cfg.taylorDepth) := by
  rfl

/-- A checked residual computation proves the original closed rejection certificate. -/
theorem rejected_of_computations (cell : AngleCell) (cfg : LeanCert.Engine.EvalConfig)
    (residuals : IntervalRat × IntervalRat)
    (evaluation : certificateResiduals cell.phiI cell.thetaI cfg.taylorDepth = residuals)
    (check : certificateRejects residuals = true) : cell.rejected cfg = true := by
  rw [rejected_eq_certificateResiduals, evaluation]
  exact check

end GerverSofa.PartE
