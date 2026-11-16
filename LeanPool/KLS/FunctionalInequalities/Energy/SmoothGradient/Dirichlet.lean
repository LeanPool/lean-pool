/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Dirichlet
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Kernel
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Contraction
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Closed
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed

/-!
# Dirichlet property of the smooth-gradient relaxation

Source: Blueprint `thm:smooth-gradient-relaxation-dirichlet`. Read `NormalContraction.smoothed`,
`SmoothGradient.Test.compSmoothed`, `SmoothGradient.relaxedContractionBound`,
`SmoothGradient.markovian`, `SmoothGradient.dirichlet`, then the intrinsic corollaries
`SmoothGradient.Intrinsic.markovian` and `SmoothGradient.Intrinsic.dirichlet`.

For every Borel probability law `μ` on a finite-dimensional real Hilbert space, the sequential
`L²(μ)` relaxation of the smooth-gradient pre-energy is Markovian: composing an `L²` class with a
normal contraction `φ` of the real line does not increase its relaxed energy. Together with the
closed quadratic structure of `Energy/SmoothGradient/Closed.lean` this makes the relaxation a
Dirichlet energy. The intrinsic-affine relaxation `SmoothGradient.Intrinsic.energy μ`, pulled back
to the ambient `L²(μ)`, is a Dirichlet energy as well.

Proof. Mollify the contraction on the real line: `φ.smoothed j` is `C^∞`, `1`-Lipschitz and
uniformly within `2 / (j + 1)` of `φ`. For a smooth test `f` the composition `φ.smoothed j ∘ f` is
again a smooth test with `‖∇(φ.smoothed j ∘ f)‖ ≤ ‖∇f‖` pointwise, hence with energy at most that
of `f`, and its `L²` class converges to `φ ∘ f`. This gives the relaxed contraction bound on every
realized test, and the certified contraction-transfer theorem extends it to every `L²` class by
lower semicontinuity. The argument mollifies the contraction, not the test, so no absolute
continuity, density or Rademacher input is used and the law may be singular.

What this module does not claim: agreement of the relaxation with the raw energy on tests, the
identification with a Cheeger energy or with `2 Ch_μ`, any Poincaré inequality, or a Markov
property for the covariance-weighted relaxations. The zero-dimensional space is included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Energy

open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

namespace NormalContraction

/-- The normal contraction mollified on the real line at scale `radius j`. -/
def smoothed (φ : NormalContraction) (j : ℕ) : ℝ → ℝ :=
  mollify (volume : Measure ℝ) (radius j) φ

/-- The mollified contraction is smooth. -/
theorem contDiff_smoothed (φ : NormalContraction) (j : ℕ) : ContDiff ℝ ∞ (φ.smoothed j) :=
  contDiff_mollify volume (radius_pos j) φ.lipschitz.continuous

/-- The mollified contraction is still `1`-Lipschitz. -/
theorem lipschitzWith_smoothed (φ : NormalContraction) (j : ℕ) :
    LipschitzWith 1 (φ.smoothed j) :=
  lipschitzWith_mollify volume (radius_pos j) φ.lipschitz

/-- The mollified contraction is uniformly close to the contraction. -/
theorem norm_smoothed_sub_le (φ : NormalContraction) (j : ℕ) (t : ℝ) :
    ‖φ.smoothed j t - φ t‖ ≤ 2 * radius j := by
  have h := norm_mollify_sub_le volume (radius_pos j) φ.lipschitz t
  simpa [smoothed] using h

/-- The derivative of the mollified contraction has norm at most one. -/
theorem norm_fderiv_smoothed_le (φ : NormalContraction) (j : ℕ) (t : ℝ) :
    ‖fderiv ℝ (φ.smoothed j) t‖ ≤ 1 := by
  have h := norm_fderiv_le_of_lipschitz ℝ (φ.lipschitzWith_smoothed j) (x₀ := t)
  simpa using h

end NormalContraction

namespace SmoothGradient.Test

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : ProbabilityMeasure E}

omit [BorelSpace E] [SecondCountableTopology E] in
/-- Composing a smooth test with a smooth `1`-Lipschitz real function does not increase the
gradient norm at any point. -/
theorem norm_gradient_comp_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hlip : ∀ t, ‖fderiv ℝ ψ t‖ ≤ 1) (f : Test μ) (x : E) :
    ‖gradient (fun y ↦ ψ (f y)) x‖ ≤ ‖gradient f.toFun x‖ := by
  rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv]
  have hcomp : fderiv ℝ (ψ ∘ f.toFun) x = (fderiv ℝ ψ (f x)).comp (fderiv ℝ f.toFun x) :=
    fderiv_comp x (hψ.differentiable (by simp) _) (f.contDiff.differentiable (by simp) _)
  change ‖fderiv ℝ (ψ ∘ f.toFun) x‖ ≤ ‖fderiv ℝ f.toFun x‖
  rw [hcomp]
  calc ‖(fderiv ℝ ψ (f x)).comp (fderiv ℝ f.toFun x)‖
      ≤ ‖fderiv ℝ ψ (f x)‖ * ‖fderiv ℝ f.toFun x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ f.toFun x‖ := by gcongr; exact hlip _
    _ = ‖fderiv ℝ f.toFun x‖ := one_mul _

/-- A smooth test composed with the mollified normal contraction is a smooth test. -/
def compSmoothed (f : Test μ) (φ : NormalContraction) (j : ℕ) : Test μ
    where
  toFun := fun x ↦ φ.smoothed j (f x)
  contDiff := (φ.contDiff_smoothed j).comp f.contDiff
  memLp_two := by
    refine
      MemLp.of_le ((memLp_const ‖φ.smoothed j 0‖).add f.memLp_two.norm)
        ((φ.contDiff_smoothed j).continuous.comp f.contDiff.continuous).aestronglyMeasurable
        (ae_of_all _ fun x ↦ ?_)
    change ‖φ.smoothed j (f x)‖ ≤ ‖‖φ.smoothed j 0‖ + ‖f x‖‖
    rw [Real.norm_eq_abs (‖φ.smoothed j 0‖ + ‖f x‖),
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hlip := (φ.lipschitzWith_smoothed j).dist_le_mul (f x) 0
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, sub_zero] at hlip
    calc
      ‖φ.smoothed j (f x)‖ = ‖(φ.smoothed j (f x) - φ.smoothed j 0) + φ.smoothed j 0‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖φ.smoothed j (f x) - φ.smoothed j 0‖ + ‖φ.smoothed j 0‖ := norm_add_le _ _
      _ ≤ ‖f x‖ + ‖φ.smoothed j 0‖ := by gcongr
      _ = ‖φ.smoothed j 0‖ + ‖f x‖ := add_comm _ _
  gradient_sq_integrable := by
    refine
      f.gradient_sq_integrable.mono
        ((aestronglyMeasurable_gradient _ (μ : Measure E)).norm.pow 2) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _)]
    exact
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_gradient_comp_le (φ.contDiff_smoothed j) (φ.norm_fderiv_smoothed_le j) f x) 2

/-- Composition with the mollified contraction does not increase the smooth-gradient energy. -/
theorem energy_compSmoothed_le (f : Test μ) (φ : NormalContraction) (j : ℕ) :
    (f.compSmoothed φ j).energy ≤ f.energy := by
  apply NNReal.coe_le_coe.mp
  simp only [coe_energy]
  exact integral_mono (f.compSmoothed φ j).gradient_sq_integrable f.gradient_sq_integrable
    fun x ↦ pow_le_pow_left₀ (norm_nonneg _)
      (norm_gradient_comp_le (φ.contDiff_smoothed j) (φ.norm_fderiv_smoothed_le j) f x) 2

/-- The class of the composed test is within `2 / (j + 1)` of the class of `φ ∘ f`. -/
theorem norm_toL2_compSmoothed_sub_le (f : Test μ) (φ : NormalContraction) (j : ℕ) :
    ‖(f.compSmoothed φ j).toL2 - φ.compL2 (μ : Measure E) f.toL2‖ ≤ 2 * radius j := by
  have hbound : ∀ᵐ x ∂(μ : Measure E),
      ‖((f.compSmoothed φ j).toL2 - φ.compL2 (μ : Measure E) f.toL2) x‖ ≤ 2 * radius j := by
    filter_upwards [Lp.coeFn_sub (f.compSmoothed φ j).toL2 (φ.compL2 (μ : Measure E) f.toL2),
      (f.compSmoothed φ j).toL2_coeFn, φ.coeFn_compL2 (μ : Measure E) f.toL2, f.toL2_coeFn]
      with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4]
    exact φ.norm_smoothed_sub_le j (f x)
  have h := Lp.norm_le_of_ae_bound (mul_nonneg two_pos.le (radius_pos j).le) hbound
  rw [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one, Real.one_rpow,
    one_mul] at h
  exact h

end SmoothGradient.Test

namespace SmoothGradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

/--
Every normal contraction satisfies the relaxed contraction bound on the realized smooth tests:
the relaxed energy of `φ ∘ f` is at most the raw energy of `f`. -/
theorem relaxedContractionBound (φ : NormalContraction) :
    (preEnergy μ).RelaxedContractionBound (φ.compL2 (μ : Measure E)) := by
  intro f
  have hconv :
    Tendsto (fun j ↦ (preEnergy μ).toAmbient (f.compSmoothed φ j)) atTop
      (𝓝 (φ.compL2 (μ : Measure E) ((preEnergy μ).toAmbient f))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j ↦ norm_nonneg _) (fun j ↦ f.norm_toL2_compSmoothed_sub_le φ j) ?_
    simpa using tendsto_radius.const_mul (2 : ℝ)
  let s :
    (preEnergy μ).ApproximatingSequence
      (φ.compL2 (μ : Measure E) ((preEnergy μ).toAmbient f)) :=
    ⟨fun j ↦ f.compSmoothed φ j, hconv⟩
  refine ((preEnergy μ).sequentialRelaxation_le_sequenceEnergy s).trans ?_
  refine (liminf_le_liminf (Eventually.of_forall fun j ↦ ?_)).trans_eq (liminf_const _)
  exact ENNReal.coe_le_coe.mpr (f.energy_compSmoothed_le φ j)

/-- The smooth-gradient relaxation is Markovian: normal contractions do not increase it. -/
theorem markovian : Markovian (μ : Measure E) (relaxation μ) := by
  intro φ f
  exact PreEnergy.RelaxedContractionBound.sequentialRelaxation_comp_le (preEnergy μ)
    (relaxedContractionBound μ φ) (φ.lipschitz.lipschitzWith_compLp φ.map_zero).continuous f

/-- The smooth-gradient relaxation is a Dirichlet energy on `L²(μ)`. -/
theorem dirichlet : Dirichlet (μ : Measure E) (relaxation μ) :=
  ⟨relaxation_closedQuadratic μ, markovian μ⟩

namespace Intrinsic

open FunctionalInequalities.Energy.Euclidean

section IntrinsicContractions

omit [CompleteSpace E]
/-- Passing to intrinsic coordinates commutes with normal contractions. -/
theorem toIntrinsicL2_compL2 (φ : NormalContraction) (f : Lp ℝ 2 (μ : Measure E)) :
    toIntrinsicL2 μ (φ.compL2 (μ : Measure E) f) =
      φ.compL2
        (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
        (toIntrinsicL2 μ f) := by
  apply Lp.ext
  have h1 :
    ⇑(toIntrinsicL2 μ
          (φ.compL2 (μ : Measure E)
            f)) =ᵐ[(Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction)]
      ⇑(φ.compL2 (μ : Measure E) f) ∘ Probability.reconstruct μ :=
    Lp.coeFn_compMeasurePreserving _ (Probability.measurePreserving_reconstruct μ)
  have h2 :
    ⇑(φ.compL2 (μ : Measure E) f) ∘
        Probability.reconstruct
          μ =ᵐ[(Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction)]
      (fun x ↦ φ (f x)) ∘ Probability.reconstruct μ :=
    (Probability.measurePreserving_reconstruct μ).quasiMeasurePreserving.ae_eq_comp
      (φ.coeFn_compL2 (μ : Measure E) f)
  have h3 :=
    φ.coeFn_compL2
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
      (toIntrinsicL2 μ f)
  have h4 :
    ⇑(toIntrinsicL2 μ
          f) =ᵐ[(Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction)]
      ⇑f ∘ Probability.reconstruct μ :=
    Lp.coeFn_compMeasurePreserving _ (Probability.measurePreserving_reconstruct μ)
  filter_upwards [h1, h2, h3, h4] with v e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  rfl

/-- The intrinsic-affine smooth-gradient relaxation is Markovian on the ambient `L²(μ)`. -/
theorem markovian : Markovian (μ : Measure E) (energy μ) := by
  intro φ f
  rw [energy_apply, energy_apply, toIntrinsicL2_compL2]
  exact SmoothGradient.markovian (Probability.intrinsicMeasure μ) φ (toIntrinsicL2 μ f)

/-- The intrinsic-affine smooth-gradient relaxation is a Dirichlet energy on `L²(μ)`. -/
theorem dirichlet : Dirichlet (μ : Measure E) (energy μ) :=
  ⟨closedQuadratic μ, markovian μ⟩

end IntrinsicContractions

end Intrinsic

end SmoothGradient

end FunctionalInequalities.Energy
