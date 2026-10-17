/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Pointwise
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainZeroTrace
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ContinuousCoeffBoundedResolvent
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PotentialBridge
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorContinuity

/-!
# ContinuousCoeffPotentialResolvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Potential resolvents for continuous skew coefficients

The potential resolvent has an interior-continuous representative when
`a = nu I + k` and `k` is continuous, without a size restriction on `k`.
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
  {nu lam Lam C : ℝ} (hnu : 0 < nu) (hlam : 0 < lam)
  (hEll : IsEllipticFieldOn lam Lam U a)
  (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
  (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
  (hd : 2 ≤ d) (q : Vec d → ℝ)
  (hq : IsBoundedNonnegativePotential U q C)

include hU hnu hsymm hcont hd in
/-- A bounded-data potential solution has a continuous representative for a
continuous skew coefficient of arbitrary size. -/
theorem exists_continuousOn_representative_potentialResolvent_continuousCoeff
    [NeZero d] (mu : PositiveShift) (F : ScalarL2 U) {M : ℝ}
    (hM : 0 ≤ M) (hFM : ∀ᵐ x ∂volumeMeasureOn U, |F x| ≤ M) :
    ∃ v : Vec d → ℝ, ContinuousOn v U ∧
      v =ᵐ[volumeMeasureOn U] potentialResolvent a mu.property hlam hEll q hq F := by
  let u : ZeroTraceSobolev U := potentialSolution a mu.property hlam hEll q hq F
  obtain ⟨z, hzValue, hzGrad⟩ := ZeroTraceSobolev.exists_h10Function hU u
  have hzEq : ZeroTraceSobolev.ofH10Function z = u := by
    apply ZeroTraceSobolev.ext
    · exact hzValue
    · exact hzGrad
  have hweak : IsPotentialWeakSolution a (mu : ℝ) q U
      (ZeroTraceSobolev.ofH10Function z) F := by
    rw [hzEq]
    exact potentialSolution_isPotentialWeakSolution a mu.property hlam hEll q hq F
  have hscalar := isScalarForcedWeakSolution_of_isPotentialWeakSolution z hq hweak
  have huBound0 := abs_alpha_mul_potentialResolvent_le_ae a hU mu.property
    hlam hEll q hq F M hM hFM
  have hvalue : z.toH1Function.toScalarL2 =
      potentialResolvent a mu.property hlam hEll q hq F := by
    change z.toH1Function.toScalarL2 = ZeroTraceSobolev.toL2 u
    rw [← ZeroTraceSobolev.toL2_ofH10Function, hzEq]
  have huBound : ∀ᵐ x ∂volumeMeasureOn U,
      |z.toH1Function.toFun x| ≤ M / (mu : ℝ) := by
    have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
    filter_upwards [huBound0, z.toH1Function.coeFn_toScalarL2] with x hx hz
    have heval := congrArg (fun w : ScalarL2 U ↦ w x) hvalue
    have hx' : |(mu : ℝ) * z.toH1Function.toFun x| ≤ M := by
      calc
        |(mu : ℝ) * z.toH1Function.toFun x| =
            |(mu : ℝ) * z.toH1Function.toScalarL2 x| := by rw [hz]
        _ = |(mu : ℝ) *
            (potentialResolvent a mu.property hlam hEll q hq F) x| := by
          exact congrArg (fun t : ℝ ↦ |(mu : ℝ) * t|) heval
        _ ≤ M := hx
    apply (le_div_iff₀ hmu).2
    simpa only [abs_mul, abs_of_pos hmu, mul_comm] using hx'
  let G : ℝ := M + ((mu : ℝ) + |C|) * (M / (mu : ℝ))
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact add_nonneg hM (mul_nonneg (add_nonneg mu.property.le (abs_nonneg C))
      (div_nonneg hM mu.property.le))
  have hsourceBound : ∀ᵐ x ∂volumeMeasureOn U,
      |F x - ((mu : ℝ) + q x) * z.toH1Function.toFun x| ≤ G := by
    filter_upwards [hFM, huBound, hq.2.1, hq.2.2] with x hfx hux hq0 hqC
    have hsum : |(mu : ℝ) + q x| ≤ (mu : ℝ) + |C| := by
      rw [abs_of_nonneg (add_nonneg mu.property.le hq0)]
      exact add_le_add le_rfl (hqC.trans (le_abs_self C))
    calc
      |F x - ((mu : ℝ) + q x) * z.toH1Function.toFun x| ≤
          |F x| + |((mu : ℝ) + q x) * z.toH1Function.toFun x| :=
        abs_sub _ _
      _ = |F x| + |(mu : ℝ) + q x| * |z.toH1Function.toFun x| := by
        rw [abs_mul]
      _ ≤ M + ((mu : ℝ) + |C|) * (M / (mu : ℝ)) :=
        add_le_add hfx (mul_le_mul hsum hux (abs_nonneg _)
          (add_nonneg mu.property.le (abs_nonneg C)))
      _ = G := rfl
  have hsourceMem : MemScalarLInfOn U
      (fun x ↦ F x - ((mu : ℝ) + q x) * z.toH1Function.toFun x) :=
    Decay.memScalarLInfOn_of_ae_abs_le hscalar.1.aestronglyMeasurable hsourceBound
  obtain ⟨v, hvcont, hvae, -⟩ :=
    continuousOn_of_weakSolution_continuousCoeff hd hU.isOpen hnu hsymm hcont
      hsourceMem hscalar
  refine ⟨v, hvcont, ?_⟩
  filter_upwards [hvae, z.toH1Function.coeFn_toScalarL2] with x hv hz
  exact hv.trans (hz.symm.trans (congrArg (fun w : ScalarL2 U ↦ w x) hvalue))

/-- The canonical continuous representative of the bounded-data potential
resolvent for an arbitrary-size continuous skew field. -/
def continuousCoeffPotentialBoundedResolvent [NeZero d] (mu : PositiveShift)
    {f : U → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    Vec d → ℝ :=
  Classical.choose
    (exists_continuousOn_representative_potentialResolvent_continuousCoeff
      a hU hnu hlam hEll hsymm hcont hd q hq mu
      (boundedMeasurableToScalarL2 hU hf hfD) (abs_nonneg D)
      (abs_boundedMeasurableToScalarL2_le hU hf hfD))

theorem continuousOn_continuousCoeffPotentialBoundedResolvent [NeZero d]
    (mu : PositiveShift) {f : U → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    ContinuousOn (continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll
      hsymm hcont hd q hq mu hf hfD) U :=
  (Classical.choose_spec
    (exists_continuousOn_representative_potentialResolvent_continuousCoeff
      a hU hnu hlam hEll hsymm hcont hd q hq mu
      (boundedMeasurableToScalarL2 hU hf hfD) (abs_nonneg D)
      (abs_boundedMeasurableToScalarL2_le hU hf hfD))).1

theorem continuousCoeffPotentialBoundedResolvent_ae [NeZero d]
    (mu : PositiveShift) {f : U → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll hsymm hcont hd
        q hq mu hf hfD =ᵐ[volumeMeasureOn U]
      potentialResolvent a mu.property hlam hEll q hq
        (boundedMeasurableToScalarL2 hU hf hfD) :=
  (Classical.choose_spec
    (exists_continuousOn_representative_potentialResolvent_continuousCoeff
      a hU hnu hlam hEll hsymm hcont hd q hq mu
      (boundedMeasurableToScalarL2 hU hf hfD) (abs_nonneg D)
      (abs_boundedMeasurableToScalarL2_le hU hf hfD))).2

/-- Characterization by continuity and the represented `L²` class. -/
theorem continuousCoeffPotentialBoundedResolvent_eq_of_continuousOn_of_ae_eq
    [NeZero d] (mu : PositiveShift) {f : U → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) {v : Vec d → ℝ}
    (hv : ContinuousOn v U)
    (hvae : v =ᵐ[volumeMeasureOn U]
      potentialResolvent a mu.property hlam hEll q hq
        (boundedMeasurableToScalarL2 hU hf hfD)) :
    Set.EqOn v (continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll
      hsymm hcont hd q hq mu hf hfD) U := by
  refine eqOn_of_continuousOn_of_ae_eq hU.isOpen hv
    (continuousOn_continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll
      hsymm hcont hd q hq mu hf hfD) ?_
  exact hvae.trans
    (continuousCoeffPotentialBoundedResolvent_ae a hU hnu hlam hEll hsymm
      hcont hd q hq mu hf hfD).symm

/-- Pointwise maximum-principle bound for the continuous potential
representative. -/
theorem abs_continuousCoeffPotentialBoundedResolvent_le [NeZero d]
    (mu : PositiveShift) {f : U → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    ∀ x ∈ U, |continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll
      hsymm hcont hd q hq mu hf hfD x| ≤ |D| / (mu : ℝ) := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  have hcontRep := continuousOn_continuousCoeffPotentialBoundedResolvent a hU
    hnu hlam hEll hsymm hcont hd q hq mu hf hfD
  have hae : ∀ᵐ x ∂volumeMeasureOn U,
      |continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll hsymm hcont
        hd q hq mu hf hfD x| ≤ |D| / (mu : ℝ) := by
    filter_upwards [continuousCoeffPotentialBoundedResolvent_ae a hU hnu hlam
        hEll hsymm hcont hd q hq mu hf hfD,
      abs_alpha_mul_potentialResolvent_le_ae a hU mu.property hlam hEll q hq
        (boundedMeasurableToScalarL2 hU hf hfD) |D| (abs_nonneg D)
        (abs_boundedMeasurableToScalarL2_le hU hf hfD)] with x h1 h2
    rw [abs_mul, abs_of_pos hmu] at h2
    rw [h1, le_div_iff₀ hmu]
    linarith only [h2]
  exact le_of_ae_le_of_continuousOn hU.isOpen
    (continuous_abs.comp_continuousOn hcontRep) continuousOn_const hae

/-- Additivity of the continuous potential representative. -/
theorem continuousCoeffPotentialBoundedResolvent_add [NeZero d]
    (mu : PositiveShift) {f g : U → ℝ} (hf : Measurable f)
    (hg : Measurable g) {D E : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hgE : ∀ y, |g y| ≤ E) (hfg : ∀ y, |(f + g) y| ≤ D + E) :
    Set.EqOn (fun x ↦
        continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll hsymm
          hcont hd q hq mu hf hfD x +
        continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll hsymm
          hcont hd q hq mu hg hgE x)
      (continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll hsymm
        hcont hd q hq mu (hf.add hg) hfg) U := by
  refine continuousCoeffPotentialBoundedResolvent_eq_of_continuousOn_of_ae_eq
    a hU hnu hlam hEll hsymm hcont hd q hq mu (hf.add hg) hfg
    ((continuousOn_continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll
      hsymm hcont hd q hq mu hf hfD).add
      (continuousOn_continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll
        hsymm hcont hd q hq mu hg hgE)) ?_
  rw [boundedMeasurableToScalarL2_add hU hf hg hfD hgE hfg, map_add]
  filter_upwards [continuousCoeffPotentialBoundedResolvent_ae a hU hnu hlam
      hEll hsymm hcont hd q hq mu hf hfD,
    continuousCoeffPotentialBoundedResolvent_ae a hU hnu hlam hEll hsymm hcont
      hd q hq mu hg hgE,
    Lp.coeFn_add
      (potentialResolvent a mu.property hlam hEll q hq
        (boundedMeasurableToScalarL2 hU hf hfD))
      (potentialResolvent a mu.property hlam hEll q hq
        (boundedMeasurableToScalarL2 hU hg hgE))] with x h1 h2 h3
  rw [h3, Pi.add_apply, h1, h2]

/-- Homogeneity of the continuous potential representative. -/
theorem continuousCoeffPotentialBoundedResolvent_smul [NeZero d]
    (mu : PositiveShift) (c : ℝ) {f : U → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hcf : ∀ y, |(c • f) y| ≤ |c| * D) :
    Set.EqOn (fun x ↦ c * continuousCoeffPotentialBoundedResolvent a hU
        hnu hlam hEll hsymm hcont hd q hq mu hf hfD x)
      (continuousCoeffPotentialBoundedResolvent a hU hnu hlam hEll hsymm
        hcont hd q hq mu (hf.const_smul c) hcf) U := by
  refine continuousCoeffPotentialBoundedResolvent_eq_of_continuousOn_of_ae_eq
    a hU hnu hlam hEll hsymm hcont hd q hq mu (hf.const_smul c) hcf
    (continuousOn_const.mul
      (continuousOn_continuousCoeffPotentialBoundedResolvent a hU hnu hlam
        hEll hsymm hcont hd q hq mu hf hfD)) ?_
  rw [boundedMeasurableToScalarL2_smul hU c hf hfD hcf, map_smul]
  filter_upwards [continuousCoeffPotentialBoundedResolvent_ae a hU hnu hlam
      hEll hsymm hcont hd q hq mu hf hfD,
    Lp.coeFn_smul c (potentialResolvent a mu.property hlam hEll q hq
      (boundedMeasurableToScalarL2 hU hf hfD))] with x h1 h2
  rw [h2, Pi.smul_apply, h1, smul_eq_mul]

end Representative

end

end DivergenceFormProcess.Form
