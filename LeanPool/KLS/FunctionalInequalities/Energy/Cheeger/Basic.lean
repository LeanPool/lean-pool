/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation
public import LeanPool.KLS.FunctionalInequalities.Energy.LocalSlope.Relaxation

/-!
# The metric Cheeger energy and its identification with the smooth-gradient relaxation

Source: Blueprint `cor:absolutely-continuous-relaxation-two-cheeger`, the absolutely continuous
scope of `thm:smooth-gradient-relaxation-two-cheeger`.  Read `Cheeger.energy`,
`Cheeger.Intrinsic.energy`, then
`SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous`,
`SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous`. The log-concave
specialization is in `KLS/LogConcave/Cheeger.lean`.

## The convention made explicit

The Blueprint leaves one statement choice open; this development fixes the Blueprint's own
convention as the selected one:

`Cheeger.energy ν = ½ · (sequential L²(ν)-relaxation of f ↦ ∫ |∇f|² dν over locally Lipschitz
L²(ν) tests of finite slope energy)`,

that is, one half of `LocalSlope.relaxation ν` (`Energy/LocalSlope/Relaxation.lean`).  The
alternative `Cheeger.ofAsymptoticLipschitz ν` is defined alongside; their equality is proved in
`Energy/Cheeger/Identification.lean`, rather than being a definitional identification.

## Affine-support transport

`Cheeger.Intrinsic.energy μ` computes `Cheeger.energy` for the intrinsic law
`Probability.intrinsicMeasure μ` on the direction space of the affine support, with the metric
induced from the ambient space, and pulls it back to ambient `L²(μ)` along the isometry
`Energy.Euclidean.toIntrinsicL2 μ`, exactly as `SmoothGradient.Intrinsic.energy μ` does for the
selected canonical energy.

## Claimed, not claimed, restricted scope, dimension zero

Claimed: the inequality `LocalSlope.relaxation ν ≤ SmoothGradient.relaxation ν` unconditionally
(smooth tests are admissible slope tests with the same energy, `Test.localSlope_energy`); the
reverse inequality, hence `𝓔^can_μ = 2 Ch_μ`, **under absolute continuity** of the intrinsic law
with respect to a Haar measure; and therefore for every compact-set log-concave law, whose
intrinsic law is absolutely continuous (`lem:logconcave-intrinsic-absolute-continuity`).

Beyond this module: `Energy/Cheeger/Identification.lean` proves the identity for all Borel
probability
laws, including singular laws. Neither module claims any Poincaré inequality, finiteness of any
constant,
a Cheeger--Buser comparison, agreement of raw slope energy with the relaxation on individual tests,
or a
Cheeger definition via asymptotic Lipschitz constants. The isoperimetric number
`h_μ` of `def:isoperimetric-cheeger-scale` is a different object.

Dimension zero: on a subsingleton coordinate space every slope is zero and both relaxations
vanish identically (`Cheeger.energy_eq_zero_of_subsingleton`); a one-point affine support gives
`0 = 2 * 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy

universe u

/-! ### The metric Cheeger energy -/

namespace Cheeger

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- Cheeger energy in the local-slope convention: one half of the relaxed squared local slope. -/
def ofLocalSlope (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  ⟨fun f ↦ LocalSlope.relaxation ν f / 2⟩

/-- Cheeger energy in the asymptotic-Lipschitz convention: one half of the relaxed squared
asymptotic Lipschitz constant. -/
def ofAsymptoticLipschitz (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  ⟨fun f ↦ AsymptoticLipschitz.relaxation ν f / 2⟩

/-- The selected metric Cheeger energy `Ch_ν` of the Blueprint: the local-slope convention
`ofLocalSlope`.  The choice is recorded by this definition and nowhere else. -/
def energy (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  ofLocalSlope ν

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Unfolding the selected Cheeger energy. -/
theorem energy_apply (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    energy ν f = LocalSlope.relaxation ν f / 2 :=
  rfl

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Twice the Cheeger energy is the relaxed squared local slope, including the value `⊤`. -/
theorem two_mul_energy (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    2 * energy ν f = LocalSlope.relaxation ν f := by
  rw [energy_apply]
  exact ENNReal.mul_div_cancel' (fun h ↦ absurd h (by norm_num)) (fun h ↦ absurd h (by norm_num))


omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Dimension zero: the Cheeger energy of a law on a one-point space vanishes. -/
theorem energy_eq_zero_of_subsingleton [Subsingleton V] (ν : ProbabilityMeasure V)
    (f : Lp ℝ 2 (ν : Measure V)) :
    energy ν f = 0 := by
  rw [energy_apply, LocalSlope.relaxation_eq_zero_of_subsingleton ν f, ENNReal.zero_div]

namespace Intrinsic

open Energy.Euclidean

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The metric Cheeger energy of the intrinsic law on the affine support, transported to ambient
real `L²(μ)` along the intrinsic `L²` isometry.  Same transport as
`SmoothGradient.Intrinsic.energy`. -/
def energy (μ : ProbabilityMeasure E) : Functional (Lp ℝ 2 (μ : Measure E)) :=
  (Cheeger.energy (Probability.intrinsicMeasure μ)).comap (toIntrinsicL2 μ)

omit [CompleteSpace E] in
/-- Unfolding the transported Cheeger energy exposes the isometric pullback. -/
@[simp]
theorem energy_apply (μ : ProbabilityMeasure E) (f : Lp ℝ 2 (μ : Measure E)) :
    energy μ f = Cheeger.energy (Probability.intrinsicMeasure μ) (toIntrinsicL2 μ f) :=
  rfl

end Intrinsic

end Cheeger

/-! ### Identification with the smooth-gradient relaxation -/

namespace SmoothGradient

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

namespace Test

variable {ν : ProbabilityMeasure V}

section CheegerEnergy

omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The pointwise local slope of a smooth test is the gradient norm, everywhere: no measure or
absolute-continuity hypothesis is needed since `ContDiff` gives differentiability at every
point. -/
private theorem apply_toFun_eq_norm_gradient (f : Test ν) (x : V) :
    LocalSlope.apply f.toFun x = ENNReal.ofReal ‖gradient f.toFun x‖ :=
  LocalSlope.apply_eq_norm_gradient f.toFun x (f.contDiff.differentiable (by simp) x)

/-- The squared local-slope energy of a smooth test is its smooth-gradient energy.  No
absolute-continuity hypothesis: the slope equals the gradient norm at every point. -/
theorem localSlope_energy (f : Test ν) :
    LocalSlope.energy ν f = (f.energy : ℝ≥0∞) := by
  have step1 : LocalSlope.energy ν f.toFun =
      ∫⁻ x, ENNReal.ofReal (‖gradient f.toFun x‖ ^ 2) ∂(ν : Measure V) := by
    unfold LocalSlope.energy
    refine lintegral_congr fun x ↦ ?_
    rw [apply_toFun_eq_norm_gradient f x, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [step1, ← ofReal_integral_eq_lintegral_ofReal f.gradient_sq_integrable
    (ae_of_all _ fun x ↦ sq_nonneg _), ← Test.coe_energy, ENNReal.ofReal_coe_nnreal]

/-- A smooth-gradient test is a local-slope test: it is locally Lipschitz, in `L²(ν)`, and its
local slope is the gradient norm at every point, with square-integrable gradient. -/
theorem localSlope_admissible (f : Test ν) : LocalSlope.Admissible ν f :=
  ⟨(f.contDiff.of_le (by exact_mod_cast le_top)).locallyLipschitz, f.memLp_two, by
    rw [localSlope_energy f]; exact ENNReal.coe_ne_top⟩

end CheegerEnergy

end Test

omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Unconditional direction: relaxing over the larger local-slope test class gives at most the
smooth-gradient relaxation.  Holds for every law, singular laws included. -/
theorem localSlope_relaxation_le (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    LocalSlope.relaxation ν f ≤ relaxation ν f := by
  have h := (preEnergy ν).sequentialRelaxation_comp_le (LocalSlope.preEnergy ν) id continuous_id
    (fun g ↦ ⟨⟨g.toFun, Test.localSlope_admissible g⟩, rfl, by
      change (LocalSlope.energy ν g.toFun).toNNReal ≤ g.energy
      rw [Test.localSlope_energy g, ENNReal.toNNReal_coe]⟩) f
  exact h

/-- Restricted scope: under absolute continuity with respect to a Haar measure, every
local-slope test is approximated in `L²(ν)` by smooth tests whose gradient energies converge to
its slope energy (the certified weighted approximation lemma with unit weight), so the
smooth-gradient relaxation is at most the local-slope relaxation. -/
theorem relaxation_le_localSlope_of_absolutelyContinuous (ν : ProbabilityMeasure V)
    (m : Measure V) [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m)
    (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f ≤ LocalSlope.relaxation ν f := by
  apply (LocalSlope.preEnergy ν).sequentialRelaxation_le_of_recovery_sequences (preEnergy ν)
  rintro ⟨g, hg⟩
  obtain ⟨hlip, hgL2, hgradL2⟩ := (LocalSlope.admissible_iff_memLp_gradient ν m hac g).mp hg
  obtain ⟨gSeq, hgSeq, hconv, hgconv⟩ :=
    Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2
      ν m hac (ContinuousLinearMap.id ℝ V) g hlip hgL2 (by simpa using hgradL2)
  have hsL2 : ∀ j, MemLp (gSeq j) 2 (ν : Measure V) := fun j ↦ (hgSeq j).2.2.1
  have hgsL2 : ∀ j, MemLp (gradient (gSeq j)) 2 (ν : Measure V) := fun j ↦ by
    simpa using (hgSeq j).2.2.2
  have hgs_int : ∀ j, Integrable (fun x ↦ ‖gradient (gSeq j) x‖ ^ 2) (ν : Measure V) :=
    fun j ↦ (memLp_two_iff_integrable_sq_norm (hgsL2 j).aestronglyMeasurable).mp (hgsL2 j)
  set s : ℕ → Test ν := fun j ↦
    { toFun := gSeq j
      contDiff := (hgSeq j).1
      memLp_two := hsL2 j
      gradient_sq_integrable := hgs_int j } with hs_def
  have hval : Tendsto (fun j ↦ (s j).toL2) atTop (𝓝 (hgL2.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j ↦ gSeq j) hsL2 g hgL2).mpr hconv
  have hgrad_tendsto :
      Tendsto (fun j ↦ (hgsL2 j).toLp (gradient (gSeq j))) atTop (𝓝 (hgradL2.toLp (gradient g))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j ↦ gradient (gSeq j)) hgsL2 (gradient g)
      hgradL2).mpr (by
        have h := hgconv
        simp only [ContinuousLinearMap.id_apply] at h
        exact h)
  have henergy_real : Tendsto (fun j ↦ ((s j).energy : ℝ)) atTop
      (𝓝 (∫ x, ‖gradient g x‖ ^ 2 ∂(ν : Measure V))) := by
    have hconv2 := hgrad_tendsto.norm.pow 2
    simp_rw [L2.norm_toLp_sq] at hconv2
    simpa [Test.coe_energy] using hconv2
  have henergy_tendsto : Tendsto (fun j ↦ ((s j).energy : ENNReal)) atTop
      (𝓝 (LocalSlope.energy ν g)) := by
    rw [Energy.LocalSlope.energy_eq_integral_gradient ν m hac g hlip hgradL2]
    have heq : ∀ j, ((s j).energy : ENNReal) = ENNReal.ofReal ((s j).energy : ℝ) :=
      fun _ ↦ ENNReal.ofReal_coe_nnreal.symm
    simp_rw [heq]
    exact ENNReal.tendsto_ofReal henergy_real
  refine ⟨⟨s, hval⟩, le_of_eq ?_⟩
  change liminf (fun j ↦ ((s j).energy : ENNReal)) atTop = _
  rw [henergy_tendsto.liminf_eq, LocalSlope.coe_preEnergy_energy]

/-- Restricted scope: the two relaxations agree for laws absolutely continuous with respect to
Haar measure. -/
theorem relaxation_eq_localSlope_of_absolutelyContinuous (ν : ProbabilityMeasure V)
    (m : Measure V) [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) :
    relaxation ν = LocalSlope.relaxation ν := by
  apply Functional.ext
  intro f
  exact le_antisymm (relaxation_le_localSlope_of_absolutelyContinuous ν m hac f)
    (localSlope_relaxation_le ν f)



namespace Intrinsic

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]


omit [CompleteSpace E] in
/-- Restricted scope: the same identity when the intrinsic law is absolutely continuous with
respect to a Haar measure on the direction space. -/
theorem energy_eq_two_mul_cheeger_of_absolutelyContinuous (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure]
    (hac : (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) ≪ m)
    (f : Lp ℝ 2 (μ : Measure E)) :
    energy μ f = 2 * Cheeger.Intrinsic.energy μ f := by
  rw [SmoothGradient.Intrinsic.energy_apply, Cheeger.Intrinsic.energy_apply,
    relaxation_eq_localSlope_of_absolutelyContinuous (Probability.intrinsicMeasure μ) m hac]
  exact (Cheeger.two_mul_energy (Probability.intrinsicMeasure μ)
    (Energy.Euclidean.toIntrinsicL2 μ f)).symm

end Intrinsic

end SmoothGradient

end FunctionalInequalities.Energy
