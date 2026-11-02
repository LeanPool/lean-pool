/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableAlgebra
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorContinuity

/-!
# ContinuousCoeffBoundedResolvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Bounded measurable resolvents for continuous skew coefficients

This is the freezing-based replacement for the small-contrast representative
used by the whole-space exhaustion.  It assumes `a = nu I + k`, with `k`
continuous and skew, but imposes no size bound on `k`.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open MarkovProcess.Semigroup

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

section Representative

variable (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
  {lam Lam nu : ℝ} (hnu : 0 < nu) (hlam : 0 < lam)
  (hEll : IsEllipticFieldOn lam Lam U a)
  (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
  (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
  (hd : 2 ≤ d)

/-- The representative continuous on `U` of a bounded measurable resolvent,
obtained by freezing the continuous skew part at each point. -/
def continuousCoeffBoundedResolvent [NeZero d] (mu : PositiveShift)
    {f : U → ℝ} (hfmeas : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    Vec d → ℝ :=
  Classical.choose (continuousOn_alphaShiftedResolvent_continuousCoeff hd hU a
    hnu hsymm hcont mu.property hlam hEll
    (boundedMeasurableToScalarL2 hU hfmeas hfD) (abs_nonneg D)
    (abs_boundedMeasurableToScalarL2_le hU hfmeas hfD))

theorem continuousOn_continuousCoeffBoundedResolvent [NeZero d]
    (mu : PositiveShift) {f : U → ℝ} (hfmeas : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    ContinuousOn (continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm
      hcont hd mu hfmeas hfD) U :=
  (Classical.choose_spec
    (continuousOn_alphaShiftedResolvent_continuousCoeff hd hU a hnu hsymm hcont
      mu.property hlam hEll (boundedMeasurableToScalarL2 hU hfmeas hfD)
      (abs_nonneg D) (abs_boundedMeasurableToScalarL2_le hU hfmeas hfD))).1

theorem continuousCoeffBoundedResolvent_ae [NeZero d]
    (mu : PositiveShift) {f : U → ℝ} (hfmeas : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm hcont hd mu
        hfmeas hfD =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a mu.property hlam hEll
        (boundedMeasurableToScalarL2 hU hfmeas hfD) :=
  (Classical.choose_spec
    (continuousOn_alphaShiftedResolvent_continuousCoeff hd hU a hnu hsymm hcont
      mu.property hlam hEll (boundedMeasurableToScalarL2 hU hfmeas hfD)
      (abs_nonneg D) (abs_boundedMeasurableToScalarL2_le hU hfmeas hfD))).2.1

/-- The freezing representative is characterized by continuity and its
almost-everywhere `L²` value. -/
theorem continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq [NeZero d]
    (mu : PositiveShift) {f : U → ℝ} (hfmeas : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) {v : Vec d → ℝ}
    (hv : ContinuousOn v U)
    (hvae : v =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a mu.property hlam hEll
        (boundedMeasurableToScalarL2 hU hfmeas hfD)) :
    Set.EqOn v (continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm hcont
      hd mu hfmeas hfD) U := by
  refine eqOn_of_continuousOn_of_ae_eq hU.isOpen hv
    (continuousOn_continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm
      hcont hd mu hfmeas hfD) ?_
  exact hvae.trans (continuousCoeffBoundedResolvent_ae a hU hnu hlam hEll hsymm
    hcont hd mu hfmeas hfD).symm

/-- Pointwise maximum-principle bound for the freezing representative. -/
theorem abs_continuousCoeffBoundedResolvent_le [NeZero d]
    (mu : PositiveShift) {f : U → ℝ} (hfmeas : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    ∀ x ∈ U, |continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm
      hcont hd mu hfmeas hfD x| ≤ |D| / (mu : ℝ) := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  have hcontinuous := continuousOn_continuousCoeffBoundedResolvent a hU hnu
    hlam hEll hsymm hcont hd mu hfmeas hfD
  have hae : ∀ᵐ x ∂volumeMeasureOn U,
      |continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm hcont hd mu
        hfmeas hfD x| ≤ |D| / (mu : ℝ) := by
    filter_upwards [continuousCoeffBoundedResolvent_ae a hU hnu hlam hEll hsymm
        hcont hd mu hfmeas hfD,
      abs_alpha_mul_alphaShiftedResolvent_le_ae a hU mu.property hlam hEll
        (boundedMeasurableToScalarL2 hU hfmeas hfD) |D| (abs_nonneg D)
        (abs_boundedMeasurableToScalarL2_le hU hfmeas hfD)] with x h1 h2
    rw [abs_mul, abs_of_pos hmu] at h2
    rw [h1, le_div_iff₀ hmu]
    linarith only [h2]
  exact le_of_ae_le_of_continuousOn hU.isOpen
    (continuous_abs.comp_continuousOn hcontinuous) continuousOn_const hae

/-- Additivity of the freezing representative on its domain. -/
theorem continuousCoeffBoundedResolvent_add [NeZero d]
    (mu : PositiveShift) {f g : U → ℝ} (hf : Measurable f)
    (hg : Measurable g) {D E : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hgE : ∀ y, |g y| ≤ E) (hfg : ∀ y, |(f + g) y| ≤ D + E) :
    Set.EqOn (fun x ↦
        continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm hcont hd mu
          hf hfD x +
        continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm hcont hd mu
          hg hgE x)
      (continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm hcont hd mu
        (hf.add hg) hfg) U := by
  refine continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq a hU hnu
    hlam hEll hsymm hcont hd mu (hf.add hg) hfg
    ((continuousOn_continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm
      hcont hd mu hf hfD).add
      (continuousOn_continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm
        hcont hd mu hg hgE)) ?_
  rw [boundedMeasurableToScalarL2_add hU hf hg hfD hgE hfg, map_add]
  filter_upwards [continuousCoeffBoundedResolvent_ae a hU hnu hlam hEll hsymm
      hcont hd mu hf hfD,
    continuousCoeffBoundedResolvent_ae a hU hnu hlam hEll hsymm hcont hd mu hg
      hgE,
    Lp.coeFn_add
      (alphaShiftedResolvent a mu.property hlam hEll
        (boundedMeasurableToScalarL2 hU hf hfD))
      (alphaShiftedResolvent a mu.property hlam hEll
        (boundedMeasurableToScalarL2 hU hg hgE))] with x h1 h2 h3
  rw [h3, Pi.add_apply, h1, h2]

/-- Homogeneity of the freezing representative on its domain. -/
theorem continuousCoeffBoundedResolvent_smul [NeZero d]
    (mu : PositiveShift) (c : ℝ) {f : U → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hcf : ∀ y, |(c • f) y| ≤ |c| * D) :
    Set.EqOn (fun x ↦ c * continuousCoeffBoundedResolvent a hU hnu hlam
        hEll hsymm hcont hd mu hf hfD x)
      (continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm hcont hd mu
        (hf.const_smul c) hcf) U := by
  refine continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq a hU hnu
    hlam hEll hsymm hcont hd mu (hf.const_smul c) hcf
    (continuousOn_const.mul
      (continuousOn_continuousCoeffBoundedResolvent a hU hnu hlam hEll hsymm
        hcont hd mu hf hfD)) ?_
  rw [boundedMeasurableToScalarL2_smul hU c hf hfD hcf, map_smul]
  filter_upwards [continuousCoeffBoundedResolvent_ae a hU hnu hlam hEll hsymm
      hcont hd mu hf hfD,
    Lp.coeFn_smul c (alphaShiftedResolvent a mu.property hlam hEll
      (boundedMeasurableToScalarL2 hU hf hfD))] with x h1 h2
  rw [h2, Pi.smul_apply, h1, smul_eq_mul]

end Representative

end

end DivergenceFormProcess.Form
