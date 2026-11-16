/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Cheeger.Basic

/-!
# The slope sandwich: smooth tests, the asymptotic Lipschitz constant, and the two relaxations

Read `AsymptoticLipschitz.apply_eq_norm_gradient` first, then
`SmoothGradient.Test.asymptoticLipschitz_*` and `SmoothGradient.asymptoticLipschitz_relaxation_le`,
then `LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient`.

## What is proved

**Smooth functions.**  `AsymptoticLipschitz.apply_eq_norm_gradient` (specialized to smooth tests by
`SmoothGradient.Test.asymptoticLipschitz_apply`): for a continuously differentiable real function
the **two-moving-point** asymptotic Lipschitz constant `Lip_a f (x) = inf_{r > 0} Lip(f, B(x, r))`
equals the canonical Hilbert gradient norm `‖∇f x‖ₑ`, at every point and with no measure in sight.
The lower bound is the one-moving-point slope
(`Energy.LocalSlope.apply_eq_norm_gradient` and `Energy.LocalSlope.apply_le_asymptoticLipschitz`);
the upper bound is the mean value inequality on a ball small enough that `fderiv` stays within `ε`
of its value at the centre, the ball being convex.

**The third side of the sandwich.**  `SmoothGradient.asymptoticLipschitz_relaxation_le`:
consequently a smooth-gradient test is an
asymptotic-Lipschitz test with the *same* energy
(`SmoothGradient.Test.asymptoticLipschitz_energy`), so relaxing over the larger class gives the
smaller functional, `AsymptoticLipschitz.relaxation ν ≤ SmoothGradient.relaxation ν`, for **every**
Borel probability law.  With `Energy.LocalSlope.relaxation_le_asymptoticLipschitz` and
`Energy.SmoothGradient.localSlope_relaxation_le` this closes the sandwich

`    LocalSlope.relaxation ν ≤ AsymptoticLipschitz.relaxation ν ≤ SmoothGradient.relaxation ν.`

**The collapse.**  `LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient`: if the two
ends of the sandwich agree — the hypothesis `SmoothGradient.relaxation ν = LocalSlope.relaxation ν`,
which is the open singular-case obligation and is proved here for no law — then the two Cheeger
conventions relax to the same functional.

## Not claimed

Nothing here proves `SmoothGradient.relaxation ν = LocalSlope.relaxation ν` for a singular law:
the reverse inequality needs density of smooth tests in the local-slope energy and is a separate
obligation.  Nothing here is a Poincaré inequality, a density statement, a statement about the
raw energy of a nonsmooth individual test, or a Cheeger--Buser comparison.  The certified
absolutely continuous scope is unchanged
(`Energy.SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous`).

Dimension zero: on a one-point coordinate space every asymptotic Lipschitz constant vanishes and
the asymptotic-Lipschitz relaxation is identically zero
(`AsymptoticLipschitz.relaxation_eq_zero_of_subsingleton`), so the sandwich collapses
unconditionally there.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy

universe u

namespace AsymptoticLipschitz

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- For a differentiable function with continuous derivative the two-moving-point asymptotic
Lipschitz constant is the canonical Hilbert gradient norm at every point.

The lower bound is the one-moving-point local slope, which is already the gradient norm.  For the
upper bound, continuity of `fderiv` gives a radius `r` on which `‖fderiv f y‖ ≤ ‖fderiv f x‖ + ε`;
the ball is convex, so the mean value inequality makes `f` Lipschitz there with that constant and
the secant supremum over the ball is bounded by it.  No measure, no local Lipschitz hypothesis and
no nontriviality premise are used. -/
theorem apply_eq_norm_gradient {f : V → ℝ} (hf : Differentiable ℝ f)
    (hfd : Continuous fun y ↦ fderiv ℝ f y) (x : V) :
    apply f x = ‖gradient f x‖ₑ := by
  refine le_antisymm ?_ ?_
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ y ∈ Metric.ball x r,
        ‖fderiv ℝ f y‖ ≤ ‖fderiv ℝ f x‖ + ε := by
      have hcont : ContinuousAt (fun y ↦ ‖fderiv ℝ f y‖) x := hfd.norm.continuousAt
      have hev : ∀ᶠ y in nhds x, ‖fderiv ℝ f y‖ < ‖fderiv ℝ f x‖ + ε :=
        hcont (Iio_mem_nhds (by linarith) : Set.Iio (‖fderiv ℝ f x‖ + ε) ∈ _)
      obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp hev
      exact ⟨r, hr, fun y hy ↦ (hsub y hy).le⟩
    have hC : (0 : ℝ) ≤ ‖fderiv ℝ f x‖ + ε := by positivity
    have hlip : ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
        dist (f y) (f z) ≤ (‖fderiv ℝ f x‖ + ε) * dist y z := by
      intro y hy z hz
      have hmv := (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le
        (fun w _ ↦ hf w) (fun w hw ↦ hball w hw) hz hy
      simpa [dist_eq_norm] using hmv
    calc apply f x ≤ ENNReal.ofReal (‖fderiv ℝ f x‖ + ε) := by
          unfold apply
          refine iInf_le_of_le r (iInf_le_of_le hr ?_)
          refine iSup_le fun y ↦ iSup_le fun hy ↦ iSup_le fun z ↦ iSup_le fun hz ↦ ?_
          refine ENNReal.ofReal_le_ofReal ?_
          rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist y z) with h0 | h0
          · rw [← h0, div_zero]; exact hC
          · exact (div_le_iff₀ h0).2 (hlip y (by simpa using hy) z (by simpa using hz))
      _ = ‖gradient f x‖ₑ + ε := by
          rw [ENNReal.ofReal_add (by positivity) hεr.le,
            ← Energy.Euclidean.LipschitzApproximation.norm_gradient_eq_norm_fderiv, ofReal_norm]
          simp
  · rw [← ofReal_norm, ← LocalSlope.apply_eq_norm_gradient f x (hf x)]
    exact LocalSlope.apply_le_asymptoticLipschitz f x

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Dimension zero: on a one-point coordinate space the relaxed squared asymptotic-Lipschitz
energy vanishes identically, exactly as the local-slope relaxation does. -/
theorem relaxation_eq_zero_of_subsingleton [Subsingleton V] (ν : ProbabilityMeasure V)
    (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f = 0 := by
  obtain ⟨c, hf⟩ := L2.exists_eq_const_of_subsingleton ν f
  have hconst : MemLp (fun _ : V ↦ c) 2 (ν : Measure V) := memLp_const c
  have henergy : energy ν (fun _ : V ↦ c) = 0 := by
    unfold energy
    simp
  have hadm : Admissible ν (fun _ : V ↦ c) :=
    ⟨(LipschitzWith.const c).locallyLipschitz, hconst, by
      rw [henergy]; exact ENNReal.zero_ne_top⟩
  have hle := (preEnergy ν).sequentialRelaxation_toAmbient_le
    (⟨fun _ : V ↦ c, hadm⟩ : {g : V → ℝ // Admissible ν g})
  have hzero : ((preEnergy ν).energy ⟨fun _ : V ↦ c, hadm⟩ : ℝ≥0∞) = 0 := by
    change ((energy ν (fun _ : V ↦ c)).toNNReal : ℝ≥0∞) = 0
    rw [henergy]
    simp
  rw [hzero] at hle
  rw [hf]
  exact le_antisymm hle bot_le

end AsymptoticLipschitz

namespace SmoothGradient

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

namespace Test

variable {ν : ProbabilityMeasure V}

section AsymptoticSlope

omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- At a smooth test, the asymptotic Lipschitz constant is the gradient norm at every point.
`ContDiff ℝ ∞` supplies both differentiability everywhere and continuity of `fderiv`. -/
theorem asymptoticLipschitz_apply (f : Test ν) (x : V) :
    AsymptoticLipschitz.apply f.toFun x = ‖gradient f.toFun x‖ₑ :=
  AsymptoticLipschitz.apply_eq_norm_gradient (f.contDiff.differentiable (by simp))
    (f.contDiff.continuous_fderiv (by simp)) x

/-- The squared asymptotic-Lipschitz energy of a smooth test is its smooth-gradient energy; no
absolute-continuity hypothesis, since the pointwise identity holds everywhere. -/
theorem asymptoticLipschitz_energy (f : Test ν) :
    AsymptoticLipschitz.energy ν f.toFun = (f.energy : ℝ≥0∞) := by
  have step1 : AsymptoticLipschitz.energy ν f.toFun =
      ∫⁻ x, ENNReal.ofReal (‖gradient f.toFun x‖ ^ 2) ∂(ν : Measure V) := by
    unfold AsymptoticLipschitz.energy
    refine lintegral_congr fun x ↦ ?_
    rw [asymptoticLipschitz_apply f x, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [step1, ← ofReal_integral_eq_lintegral_ofReal f.gradient_sq_integrable
    (ae_of_all _ fun x ↦ sq_nonneg _), ← Test.coe_energy, ENNReal.ofReal_coe_nnreal]

/-- A smooth-gradient test is an asymptotic-Lipschitz test: it is locally Lipschitz, in `L²(ν)`,
and its asymptotic-Lipschitz energy is the finite smooth-gradient energy. -/
theorem asymptoticLipschitz_admissible (f : Test ν) :
    AsymptoticLipschitz.Admissible ν f.toFun :=
  ⟨(f.contDiff.of_le (by exact_mod_cast le_top)).locallyLipschitz, f.memLp_two, by
    rw [asymptoticLipschitz_energy f]; exact ENNReal.coe_ne_top⟩

end AsymptoticSlope

end Test

/-- The third side of the sandwich.  Every smooth-gradient test is an asymptotic-Lipschitz
test with the same energy, so relaxing over the larger class gives the smaller relaxed functional.
Holds for every Borel probability law, singular laws included. -/
theorem asymptoticLipschitz_relaxation_le (ν : ProbabilityMeasure V)
    (f : Lp ℝ 2 (ν : Measure V)) :
    AsymptoticLipschitz.relaxation ν f ≤ relaxation ν f := by
  have h := (preEnergy ν).sequentialRelaxation_comp_le (AsymptoticLipschitz.preEnergy ν) id
    continuous_id
    (fun g ↦ ⟨⟨g.toFun, Test.asymptoticLipschitz_admissible g⟩, rfl, by
      change (AsymptoticLipschitz.energy ν g.toFun).toNNReal ≤ g.energy
      rw [Test.asymptoticLipschitz_energy g, ENNReal.toNNReal_coe]⟩) f
  exact h

end SmoothGradient

namespace LocalSlope

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The collapse: once the two ends of the sandwich
`LocalSlope.relaxation ν ≤ AsymptoticLipschitz.relaxation ν ≤ SmoothGradient.relaxation ν` agree,
the two Cheeger conventions relax to the same `L²(ν)` functional.  The hypothesis is the open
singular-case obligation; it is assumed, never proved here. -/
theorem relaxation_eq_asymptoticLipschitz_of_smoothGradient (ν : ProbabilityMeasure V)
    (h : SmoothGradient.relaxation ν = relaxation ν) :
    relaxation ν = AsymptoticLipschitz.relaxation ν := by
  refine Functional.ext fun f ↦ le_antisymm (relaxation_le_asymptoticLipschitz ν f) ?_
  calc AsymptoticLipschitz.relaxation ν f ≤ SmoothGradient.relaxation ν f :=
        SmoothGradient.asymptoticLipschitz_relaxation_le ν f
    _ = relaxation ν f := by rw [h]

end LocalSlope

end FunctionalInequalities.Energy
