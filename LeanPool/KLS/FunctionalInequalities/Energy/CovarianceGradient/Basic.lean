/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Measurable
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Covariance-weighted gradient pre-energy of globally Lipschitz tests

Source: Blueprint `def:affine-poincare-constant`, pre-energy part. Read
`Energy.CovarianceGradient.density`, `Energy.CovarianceGradient.Test`,
`Energy.CovarianceGradient.preEnergy` and
`Energy.CovarianceGradient.relaxation`; the affine specialization to the intrinsic law is
`Energy.CovarianceGradient.Intrinsic.preEnergy`
and `Energy.CovarianceGradient.Intrinsic.energy` at the end.

For a probability law `ν` on a finite-dimensional real Hilbert space `V`, a test is a globally
Lipschitz real function `g ∈ L²(ν)` whose covariance-weighted gradient density
`⟪Σ ∇g, ∇g⟫` is `ν`-integrable, where `Σ = Covariance.operator ν`. Its realization is its `L²(ν)`
class and its finite energy is `∫ ⟪Σ ∇g, ∇g⟫ dν`. The sequential `L²(ν)` relaxation of this
pre-energy is the covariance relaxation. `gradient` is Mathlib's canonical Hilbert gradient,
zero at points of nondifferentiability; the energy is therefore defined for every test without a
differentiability premise.

What this module claims: the objects above, their unfolding identities, and two representative
contracts that hold for every law on `V`:

* if `ν` is absolutely continuous with respect to a Haar measure, a Lipschitz test is
  differentiable `ν`-almost everywhere and `gradient` is its derivative there
  (`Energy.CovarianceGradient.Test.ae_hasGradientAt`, Rademacher);
* if the frontier of the support of `ν` is `ν`-null, continuous representatives of one `L²(ν)`
  class have `ν`-almost everywhere equal gradients, so two tests with the same realization have
  the same energy (`gradient_ae_eq_of_ae_eq`,
  `Energy.CovarianceGradient.Test.energy_eq_of_toL2_eq`).

What this module does not claim: density of the realization, closability, quadraticity,
lower semicontinuity of the relaxation, any Markov property, a Poincaré inequality, or a
comparison with the smooth-gradient or literature energies. Log-concavity is not assumed here;
the log-concave discharge of the two contract hypotheses is in
`KLS/LogConcave/Covariance.lean`. Without a finite second moment Mathlib's convention makes
`Covariance.operator ν = 0`, so the energy is then identically zero; the honest covariance case is
the one with a second moment. The zero-dimensional direction space is included: every test is
constant there and every energy is zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace FunctionalInequalities.Energy

open Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]

namespace CovarianceGradient

/-- The covariance-weighted squared gradient `⟪Σ ∇g x, ∇g x⟫` with `Σ = Covariance.operator ν`. -/
def density (ν : ProbabilityMeasure V) (g : V → ℝ) (x : V) : ℝ :=
  inner ℝ (Covariance.operator (ν : Measure V) (gradient g x)) (gradient g x)

/-- The covariance-weighted gradient density is pointwise nonnegative, because the covariance
bilinear form is positive semidefinite (and zero without a second moment). -/
theorem density_nonneg (ν : ProbabilityMeasure V) (g : V → ℝ) (x : V) :
    0 ≤ density ν g x := by
  unfold density
  rw [Covariance.operator_inner]
  exact covarianceBilin_self_nonneg _

/-- A globally Lipschitz real `L²(ν)` test with integrable covariance-weighted gradient density. -/
structure Test (ν : ProbabilityMeasure V) where
  /-- The real-valued test function. -/
  toFun : V → ℝ
  /-- The test is globally Lipschitz for some finite constant. -/
  lipschitz : ∃ K : NNReal, LipschitzWith K toFun
  /-- The test defines an element of real `L²(ν)`. -/
  memLp_two : MemLp toFun 2 (ν : Measure V)
  /-- The covariance-weighted squared gradient is integrable. -/
  integrable : Integrable (density ν toFun) (ν : Measure V)

end CovarianceGradient

namespace CovarianceGradient.Test

variable {ν : ProbabilityMeasure V}

instance : CoeFun (Test ν) (fun _ ↦ V → ℝ) :=
  ⟨toFun⟩

/-- Every test is continuous, being Lipschitz. -/
theorem continuous (f : Test ν) : Continuous f.toFun := by
  obtain ⟨K, hK⟩ := f.lipschitz
  exact hK.continuous

/-- The finite real integral underlying the covariance energy is nonnegative. -/
theorem integral_nonneg (f : Test ν) :
    0 ≤ ∫ x, Energy.CovarianceGradient.density ν f.toFun x ∂(ν : Measure V) :=
  MeasureTheory.integral_nonneg (Energy.CovarianceGradient.density_nonneg ν f.toFun)

/-- The finite covariance-weighted gradient energy `∫ ⟪Σ ∇g, ∇g⟫ dν`, valued in `NNReal`. -/
def energy (f : Test ν) : NNReal :=
  ⟨∫ x, Energy.CovarianceGradient.density ν f.toFun x ∂(ν : Measure V), f.integral_nonneg⟩

/-- Coercing the finite energy to `ℝ` recovers its defining integral. -/
@[simp, norm_cast]
theorem coe_energy (f : Test ν) :
    (f.energy : ℝ) = ∫ x, Energy.CovarianceGradient.density ν f.toFun x ∂(ν : Measure V) :=
  rfl

/-- The `L²(ν)` element represented by a test. -/
def toL2 (f : Test ν) : Lp ℝ 2 (ν : Measure V) :=
  f.memLp_two.toLp f.toFun

/-- The `L²` realization agrees almost everywhere with the original test function. -/
theorem toL2_coeFn (f : Test ν) :
    f.toL2 =ᵐ[(ν : Measure V)] f.toFun :=
  f.memLp_two.coeFn_toLp

/-- Two tests have the same realization exactly when they agree `ν`-almost everywhere. -/
theorem toL2_eq_toL2_iff (f g : Test ν) :
    f.toL2 = g.toL2 ↔ f.toFun =ᵐ[(ν : Measure V)] g.toFun :=
  MemLp.toLp_eq_toLp_iff f.memLp_two g.memLp_two

end CovarianceGradient.Test

namespace CovarianceGradient

/-- The finite covariance-weighted gradient pre-energy on globally Lipschitz tests, realized in
real `L²(ν)`. -/
def preEnergy (ν : ProbabilityMeasure V) : PreEnergy (Lp ℝ 2 (ν : Measure V)) where
  Test := Test ν
  toAmbient := Test.toL2
  energy := Test.energy

/-- The ambient realization of the covariance pre-energy is the test's `L²` class. -/
@[simp]
theorem preEnergy_toAmbient (ν : ProbabilityMeasure V) (f : Test ν) :
    (preEnergy ν).toAmbient f = f.toL2 :=
  rfl

/-- The covariance pre-energy is exactly the finite covariance-weighted gradient integral. -/
@[simp]
theorem preEnergy_energy (ν : ProbabilityMeasure V) (f : Test ν) :
    (preEnergy ν).energy f = f.energy :=
  rfl

/-- The sequential `L²(ν)` relaxation of the covariance pre-energy. Closability, quadraticity
and agreement with the raw energy on tests are separate theorems, not part of this name. -/
def relaxation (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  (preEnergy ν).sequentialRelaxation

/-- Unfolding the covariance relaxation exposes the generic sequential relaxation. -/
theorem relaxation_apply (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f = (preEnergy ν).sequentialRelaxation f :=
  rfl

end CovarianceGradient

section Representative

variable [SecondCountableTopology V]

namespace Euclidean

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Continuous functions that agree `ν`-almost everywhere agree on the support of `ν`. -/
theorem eqOn_support_of_ae_eq {ν : Measure V} {g₁ g₂ : V → ℝ}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (h : g₁ =ᵐ[ν] g₂) :
    Set.EqOn g₁ g₂ ν.support := by
  have hopen : IsOpen {x | g₁ x ≠ g₂ x} := isOpen_ne_fun h₁ h₂
  have hnull : ν {x | g₁ x ≠ g₂ x} = 0 := h
  intro x hx
  by_contra hne
  exact Measure.subset_compl_support_of_isOpen hopen hnull hne hx

omit [BorelSpace V] in
/-- If the frontier of the support of `ν` is `ν`-null, continuous representatives of one
`ν`-almost everywhere class have `ν`-almost everywhere equal canonical gradients. The gradient
is compared through `fderiv`, which only depends on the germ of the function. -/
theorem gradient_ae_eq_of_ae_eq {ν : Measure V} (hfr : ν (frontier ν.support) = 0)
    {g₁ g₂ : V → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂) (h : g₁ =ᵐ[ν] g₂) :
    gradient g₁ =ᵐ[ν] gradient g₂ := by
  have heq := eqOn_support_of_ae_eq h₁ h₂ h
  have hsupp : ∀ᵐ x ∂ν, x ∈ ν.support := Measure.support_mem_ae
  have hfr' : ∀ᵐ x ∂ν, x ∉ frontier ν.support := compl_mem_ae_iff.mpr hfr
  filter_upwards [hsupp, hfr'] with x hx hxf
  have hint : x ∈ interior ν.support := by
    rw [Measure.isClosed_support.frontier_eq] at hxf
    exact by_contra fun hnot ↦ hxf ⟨hx, hnot⟩
  have hgerm : g₁ =ᶠ[𝓝 x] g₂ := by
    filter_upwards [isOpen_interior.mem_nhds hint] with y hy
    exact heq (interior_subset hy)
  simp only [gradient, hgerm.fderiv_eq]

end Euclidean

namespace CovarianceGradient

/-- Under the same null-frontier hypothesis, the covariance-weighted gradient densities of two
continuous `ν`-almost everywhere equal functions agree `ν`-almost everywhere. -/
theorem density_ae_eq_of_ae_eq (ν : ProbabilityMeasure V)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    {g₁ g₂ : V → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂) (h : g₁ =ᵐ[(ν : Measure V)] g₂) :
    density ν g₁ =ᵐ[(ν : Measure V)] density ν g₂ := by
  filter_upwards [gradient_ae_eq_of_ae_eq hfr h₁ h₂ h] with x hx
  simp only [density, hx]

end CovarianceGradient

namespace CovarianceGradient.Test

/-- The covariance energy depends only on the realized `L²(ν)` class when the frontier of the
support is `ν`-null. This is the representative-independence half of the Blueprint's
"well defined almost everywhere" clause. -/
theorem energy_eq_of_toL2_eq {ν : ProbabilityMeasure V}
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    {f g : Test ν} (hfg : f.toL2 = g.toL2) :
    f.energy = g.energy := by
  apply NNReal.eq
  simp only [coe_energy]
  exact integral_congr_ae (density_ae_eq_of_ae_eq ν hfr f.continuous
    g.continuous ((toL2_eq_toL2_iff f g).mp hfg))

end CovarianceGradient.Test

end Representative

section Rademacher

variable [FiniteDimensional ℝ V]

namespace CovarianceGradient.Test

/-- Rademacher's theorem for a test: if `ν` is absolutely continuous with respect to an additive
Haar measure, the test is differentiable `ν`-almost everywhere and the canonical gradient is its
derivative there. This is the existence half of the Blueprint's "well defined almost everywhere"
clause; it uses the repository's locally Lipschitz Rademacher interface. -/
theorem ae_hasGradientAt {ν : ProbabilityMeasure V}
    (f : Test ν) (m : Measure V) [m.IsAddHaarMeasure]
    (hac : (ν : Measure V) ≪ m) :
    ∀ᵐ x ∂(ν : Measure V), HasGradientAt f.toFun (gradient f.toFun x) x := by
  obtain ⟨K, hK⟩ := f.lipschitz
  filter_upwards [hac.ae_le
    (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hK.locallyLipschitz m)]
    with x hx
  exact hx.hasGradientAt

end CovarianceGradient.Test

end Rademacher

end FunctionalInequalities.Energy

namespace FunctionalInequalities.Energy.CovarianceGradient.Intrinsic

open Energy.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The affine covariance pre-energy `P^aff_μ`: the covariance pre-energy of the intrinsic law
of `μ` on the direction space of its affine support, with `Σ = Covariance.operator ν`. -/
def preEnergy (μ : ProbabilityMeasure E) :
    PreEnergy
      (Lp ℝ 2
        (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)) :=
  Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)

/-- The affine covariance relaxation `𝓔^aff_μ`: the sequential `L²(ν)` relaxation of the
affine covariance pre-energy on the intrinsic law `ν`. -/
def energy (μ : ProbabilityMeasure E) :
    Functional
      (Lp ℝ 2
        (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)) :=
  (preEnergy μ).sequentialRelaxation

omit [CompleteSpace E] in
/-- The affine pre-energy is the covariance pre-energy of the intrinsic law. -/
@[simp]
theorem preEnergy_eq_intrinsicMeasure (μ : ProbabilityMeasure E) :
    preEnergy μ = Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ) :=
  rfl

section IntrinsicEnergy

omit [CompleteSpace E]
/-- The affine relaxation is the covariance relaxation of the intrinsic law. -/
theorem energy_eq_relaxation_intrinsicMeasure (μ : ProbabilityMeasure E) :
    energy μ = Energy.CovarianceGradient.relaxation (Probability.intrinsicMeasure μ) :=
  rfl

/-- Unfolding the affine relaxation exposes the generic sequential relaxation. -/
theorem energy_apply (μ : ProbabilityMeasure E)
    (f :
      Lp ℝ 2
        (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)) :
    energy μ f =
      (Energy.CovarianceGradient.preEnergy
            (Probability.intrinsicMeasure μ)).sequentialRelaxation
        f :=
  rfl

end IntrinsicEnergy

end FunctionalInequalities.Energy.CovarianceGradient.Intrinsic
