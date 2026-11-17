/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation
public import LeanPool.KLS.FunctionalInequalities.Poincare.LocalSlope.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.LocalSlope.Gradient
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Comparison
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Smooth and literature Poincare constants

Proved continuation of the certified weighted approximation lemma.
Source: Blueprint `thm:smooth-lipschitz-constant-equivalence`; the final selected-constant
corollary retains explicit intrinsic absolute continuity, before the separate Borell theorem.
Read finite-constant equivalence, equality of the coordinate infima, the ambient/intrinsic
chain, then the selected/literature corollary. All four proofs are complete.


`Poincare.LocalSlope.Holds ν` tests functions directly on ν. In contrast,
`Poincare.LocalSlope.Intrinsic.constant μ` is
already defined on `Probability.intrinsicMeasure μ`. The coordinate infimum below is printed
explicitly to avoid taking intrinsic coordinates a second time. No alternative constant is defined.
Finite constants include zero; optimal values remain in ENNReal, including infinity.
Only the intrinsic law must be absolutely continuous: the ambient law may be singular.
No log-concavity, second moment, Cheeger identification or raw/core agreement is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Poincare.SmoothTest

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

private theorem ofReal_nnreal_mul (C : NNReal) (a : ℝ) :
    ENNReal.ofReal ((C : ℝ) * a) = (C : ENNReal) * ENNReal.ofReal a := by
  convert! ENNReal.ofReal_mul (q := a) C.2 using 1
  simp

private theorem variance_eq_coe_L2 {α : Type*} [MeasurableSpace α]
    (ν : ProbabilityMeasure α) (f : α → ℝ)
    (hf : MemLp f 2 (ν : Measure α)) :
    ProbabilityTheory.variance f (ν : Measure α) = (L2.variance ν (hf.toLp f) : ℝ) := by
  rw [L2.variance_toLp, Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _)]

private theorem integral_sq_norm_eq_norm_toLp_sq {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (ν : ProbabilityMeasure α) (f : α → V)
    (hf : MemLp f 2 (ν : Measure α)) : (∫ x, ‖f x‖ ^ 2 ∂(ν : Measure α)) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (hf.toLp f), MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

omit [SecondCountableTopology E] in
private theorem literatureEnergy_eq_ofReal_energy (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) (hg : MemLp (gradient f) 2 (ν : Measure E)) :
    Energy.LocalSlope.energy ν f = ENNReal.ofReal (energy (ν : Measure E) f) := by
  rw [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν f hf, energy,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
      (ae_of_all _ fun x => sq_nonneg ‖gradient f x‖)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2]

/-- Step 5: every finite nonnegative smooth-test constant works on exactly the literature
finite-energy test domain. Use the certified approximation theorem with B equal to identity. -/
theorem holds_iff_localSlope (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) (C : NNReal) :
    Holds (ν : Measure E) (C : ℝ) ↔ Poincare.LocalSlope.Holds ν C := by
  have hgradmeas (f : E → ℝ) :=
    Energy.Euclidean.LipschitzApproximation.aestronglyMeasurable_gradient f (ν : Measure E)
  constructor
  · intro h f hf
    obtain ⟨hlip, hL2, hgL2⟩ :=
      (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hν f).mp hf
    obtain ⟨fs, hfs, hconv, hgconv⟩ :=
      Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2
        ν m hν (ContinuousLinearMap.id ℝ E) f hlip hL2 (by simpa using hgL2)
    have hsL2 (j : ℕ) : MemLp (fs j) 2 (ν : Measure E) := (hfs j).2.2.1
    have hgsL2 (j : ℕ) : MemLp (gradient (fs j)) 2 (ν : Measure E) := by
      simpa using (hfs j).2.2.2
    have hval := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hsL2 f hL2).mpr hconv
    have hgrad := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun j => gradient (fs j)) hgsL2 (gradient f) hgL2).mpr (by
        convert! hgconv using 1)
    have hvar : Tendsto (fun j => ProbabilityTheory.variance (fs j) (ν : Measure E)) atTop
        (𝓝 (ProbabilityTheory.variance f (ν : Measure E))) := by
      simp_rw [variance_eq_coe_L2 ν _ (hsL2 _), variance_eq_coe_L2 ν f hL2]
      exact ((NNReal.continuous_coe.comp (L2.continuous_variance ν)).tendsto _).comp hval
    have henergy : Tendsto (fun j => energy (ν : Measure E) (fs j)) atTop
        (𝓝 (energy (ν : Measure E) f)) := by
      simp_rw [energy, integral_sq_norm_eq_norm_toLp_sq ν _ (hgsL2 _),
        integral_sq_norm_eq_norm_toLp_sq ν _ hgL2]
      exact hgrad.norm.pow 2
    have hreal : ProbabilityTheory.variance f (ν : Measure E) ≤ C * energy (ν : Measure E) f :=
      le_of_tendsto_of_tendsto' hvar (tendsto_const_nhds.mul henergy) fun j =>
        h.variance_le ⟨(hfs j).1, hsL2 j,
          (memLp_two_iff_integrable_sq_norm (hgradmeas (fs j))).mp (hgsL2 j)⟩
    rw [← ProbabilityTheory.ofReal_variance hL2,
      literatureEnergy_eq_ofReal_energy ν m hν f hlip hgL2,
      ← ofReal_nnreal_mul C]
    exact ENNReal.ofReal_le_ofReal hreal
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    have hlip : LocallyLipschitz f := (hf.smooth'.of_le (by simp)).locallyLipschitz
    have hgL2 := (memLp_two_iff_integrable_sq_norm (hgradmeas f)).mpr hf.energy_integrable
    have hfLit := (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hν f).mpr
      ⟨hlip, hf.memLp_two, hgL2⟩
    have hb := h f hfLit
    rw [← ProbabilityTheory.ofReal_variance hf.memLp_two,
      literatureEnergy_eq_ofReal_energy ν m hν f hlip hgL2,
      ← ofReal_nnreal_mul C] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.2 (energy_nonneg _ _))).mp hb

/-- Step 6: equality of the infima of valid finite constants on this same coordinate space.
The subtype infimum is the existing Poincare.LocalSlope.Holds definition, without a second intrinsic
map. -/
theorem constant_eq_localSlope_infimum (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) :
    optimalConstant (ν : Measure E) =
      ⨅ C : { C : NNReal // Poincare.LocalSlope.Holds ν C }, (C.1 : ENNReal) := by
  apply le_antisymm
  · refine le_iInf fun C => ?_
    exact constant_le ((holds_iff_localSlope ν m hν C.1).mpr C.2)
  · apply le_constant
    intro C hC
    exact iInf_le_of_le ⟨C, (holds_iff_localSlope ν m hν C).mp hC⟩ le_rfl

/-- Smooth inequalities transport between the ambient law and its intrinsic law without
absolute continuity. Restriction decreases energy, while normal-constant extension preserves it. -/
private theorem holds_iff_intrinsicMeasure (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      Holds (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
        (C : ℝ) := by
  let ν := Probability.intrinsicMeasure μ
  have hvar (f : Energy.SmoothGradient.Test μ) (g : Energy.SmoothGradient.Test ν)
    (heq : ∀ v, g v = f (Probability.reconstruct μ v)) :
    ProbabilityTheory.variance g.toFun (ν : Measure (Probability.affineSupport μ).direction) =
      ProbabilityTheory.variance f.toFun (μ : Measure E) := by
    calc
      _ =
          ProbabilityTheory.variance (fun v => f (Probability.reconstruct μ v))
            (ν : Measure (Probability.affineSupport μ).direction) :=
        congrArg (fun k => ProbabilityTheory.variance k (ν : Measure _)) (funext heq)
      _ = _ :=
        (Probability.measurePreserving_reconstruct μ).variance_fun_comp
          f.contDiff.continuous.aemeasurable
  constructor
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro g hg
    let gt : Energy.SmoothGradient.Test ν := ⟨g, hg.smooth', hg.memLp_two, hg.energy_integrable⟩
    obtain ⟨f, heq, _, henergy⟩ := Energy.SmoothGradient.Test.exists_ambient_extension μ gt
    have he : energy (μ : Measure E) f.toFun = energy (ν : Measure _) gt.toFun :=
      congrArg (fun c : NNReal => (c : ℝ)) henergy
    change
      ProbabilityTheory.variance gt.toFun (ν : Measure _) ≤ C * energy (ν : Measure _) gt.toFun
    rw [hvar f gt (fun v => (heq v).symm), ← he]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let ft : Energy.SmoothGradient.Test μ := ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    obtain ⟨g, heq, _, henergy⟩ := Energy.SmoothGradient.Test.exists_intrinsic_restriction μ ft
    have he : energy (ν : Measure _) g.toFun ≤ energy (μ : Measure E) ft.toFun :=
      NNReal.coe_le_coe.mpr henergy
    have hb := h.variance_le ⟨g.contDiff, g.memLp_two, g.gradient_sq_integrable⟩
    change
      ProbabilityTheory.variance ft.toFun (μ : Measure E) ≤ C * energy (μ : Measure E) ft.toFun
    rw [← hvar ft g heq]
    exact hb.trans (mul_le_mul_of_nonneg_left he C.2)

/-- Step 7: the exact ambient / intrinsic / literature chain from the Blueprint theorem.
Use the proved smooth-test restriction and normal-constant extension for the first equality.
The Haar reference lives on the direction of the affine support; zero dimension is included. -/
theorem constant_eq_intrinsicMeasure_and_localSlope (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hμ :
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    optimalConstant (μ : Measure E) =
        optimalConstant
          (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      optimalConstant
          (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.optimalConstant μ := by
  constructor
  · apply le_antisymm
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mpr hC)
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mp hC)
  · exact constant_eq_localSlope_infimum (Probability.intrinsicMeasure μ) m hμ

end FunctionalInequalities.Poincare.SmoothTest

namespace FunctionalInequalities.Poincare.SmoothGradient.Intrinsic


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- Step 8: connect the selected constant to the literature frontend under the same explicit
intrinsic absolute-continuity premise. `KLS.LogConcave.Poincare` derives this premise for every
compact-set log-concave law. -/
theorem constant_eq_localSlope
    (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
    [Measure.IsAddHaarMeasure m]
    (hμ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    optimalConstant μ = Poincare.LocalSlope.Intrinsic.optimalConstant μ := by
  rw [← Poincare.SmoothTest.constant_eq_intrinsic μ]
  exact (Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ m hμ).1.trans
    (Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ m hμ).2

end FunctionalInequalities.Poincare.SmoothGradient.Intrinsic
