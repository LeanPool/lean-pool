/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileDefectIdentities
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRecentPointwise
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.CheckpointMoment
public import LeanPool.HighContrastHomogenization.Provider.Transport.NearIsometry

/-!
# High-contrast homogenization: Provider.Response.ProfileDefectHistory

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Nonlinear-history bounds for the positive response defects

The scale-`s` term in the terminal nonlinear history controls the relative
mean gain.  Combined with the terminal load estimates, this gives the primal
and adjoint response-defect bounds with their independent loads.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem ofReal_mul_history_bound
    {x C F W : ℝ} {N : ℝ≥0∞} (hC : 0 ≤ C)
    (hx : x ≤ C * F) (hF : ENNReal.ofReal F ≤ ENNReal.ofReal W * N) :
    ENNReal.ofReal x ≤ ENNReal.ofReal (C * W) * N := by
  calc
    ENNReal.ofReal x ≤ ENNReal.ofReal (C * F) :=
      ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal C * ENNReal.ofReal F := ENNReal.ofReal_mul hC
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal W * N) :=
      mul_le_mul_right hF _
    _ = ENNReal.ofReal (C * W) * N := by
      rw [ENNReal.ofReal_mul hC, mul_assoc]

private theorem real_le_of_ofReal_le
    {x C : ℝ} {N : ℝ≥0∞} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hN : N ≠ ⊤) (h : ENNReal.ofReal x ≤ ENNReal.ofReal C * N) :
    x ≤ C * N.toReal := by
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN) h
  rwa [ENNReal.toReal_ofReal hx, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC] at hreal

/-- Stationarity and aligned mean order make the primal response defect
nonnegative. -/
theorem profilePrimalResponseDefect_nonneg_of_stationary [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    0 ≤ profilePrimalResponseDefect P
      (Recurrence.posDef_of_isRoundedGrid hgrid) g hg s t p r := by
  have hmean := Recurrence.adaptedMean_le hP hgrid hls hst hints hintt
  exact profilePrimalResponseDefect_nonneg
    (Recurrence.posDef_of_isRoundedGrid hgrid) hg hints hintt hmean p r

/-- Stationarity and aligned mean order make the coefficient-transpose
response defect nonnegative. -/
theorem profileAdjointResponseDefect_nonneg_of_stationary [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    0 ≤ profileAdjointResponseDefect P
      (Recurrence.posDef_of_isRoundedGrid hgrid) g hg s t p r := by
  have hmean := Recurrence.adaptedMean_le hP hgrid hls hst hints hintt
  exact profileAdjointResponseDefect_nonneg
    (Recurrence.posDef_of_isRoundedGrid hgrid) hg hints hintt hmean p r

end

end HCPolySupport.HighContrast.Response
