/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxUpperFamily
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveBarrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxGeneralDomainTail
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Process
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ProcessInterface

/-!
# CruxUpperProcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The process-side upper resolvent comparison

The exterior penalization dominates the killed resolvent at every penalization
index, and the penalization limit on the target cube is the part resolvent.
Consequently the resolvent of the whole-space process killed on leaving the
part domain is at most the continuous representative of the part resolvent.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess MarkovProcess.Semigroup ProbabilityTheory
open MarkovProcess.SubMarkovKernelSemigroup
open WholeSpaceAnalyticData
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d}

omit [NeZero d] in
/-- The extended-real zero extension of a nonnegative observable is the live
extension of its extended-real form.  Both vanish at the added point. -/
theorem ofReal_onePointRealExtension_eq_onePointLiveExtension (f : Vec d → ℝ) :
    (fun z ↦ ENNReal.ofReal (onePointRealExtension f z)) =
      PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun y ↦ ENNReal.ofReal (f y)) := by
  funext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe y => simp

/-- The continuous zero extension of the part solution is the analytic cube
resolvent on the cube.  Both are continuous there and represent the same
shifted Dirichlet solution. -/
theorem eq_analyticCubeResolvent_of_isRepresentative (A : WholeSpaceAnalyticData d)
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    {u : Vec d → ℝ} (hucont : Continuous u)
    (hurep : u =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a lam.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD)))
    (v : ℕ) (hVcube : V = wholeSpaceCube d v) {x : Vec d} (hx : x ∈ V) :
    u x = A.analyticCubeResolvent lam f hf hfD v x := by
  subst hVcube
  refine eqOn_of_continuousOn_of_ae_eq
    (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen hucont.continuousOn
    (A.continuousOn_analyticCubeResolvent lam hf hfD v) ?_ hx
  filter_upwards [hurep, A.analyticCubeResolvent_ae lam hf hfD v] with y h1 h2
  rw [h1, h2]
  exact congrArg (fun w ↦ ZeroTraceSobolev.toL2 w y)
    (alphaShiftedSolution_congr_ellipticity A.a lam.property A.hnu A.hnu
      (partEllipticity A (isOpenBoundedConvexDomain_wholeSpaceCube d v))
      (A.cubeEllipticity v) (partDatumL2 _ hf hfD))

namespace WholeSpaceBarrierData

variable (P : WholeSpaceBarrierData A)

/-- **The penalization bound for the killed resolvent.**  The resolvent of the
whole-space process killed on leaving the compactified image of the part
domain is at most any real upper bound for the infimum of the exterior-
penalized resolvents.  The domination at each penalization index is the
Feynman-Kac comparison of the process layer; the bound itself is the analytic
input, supplied by the caller. -/
theorem killedResolvent_le_ofReal_of_iInf_le
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ y, |P.f y| ≤ D) {x : Vec d} {c : ℝ}
    (hc : (⨅ n : ℕ, (A.analyticPenalizedResolvent P.hV.isOpen n P.lam P.f
      P.hf hfD x).toReal) ≤ c) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) ≤
      ENNReal.ofReal c := by
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  have hFm : Measurable (onePointRealExtension P.f) :=
    measurable_onePointRealExtension P.hf
  have hF0 : ∀ z, 0 ≤ onePointRealExtension P.f z := by
    intro z
    induction z using OnePoint.rec with
    | infty => simp
    | coe y => simpa using P.hf0 y
  have hFD : ∀ z, |onePointRealExtension P.f z| ≤ D :=
    abs_onePointRealExtension_le hD hfD
  have hrestrict :
      (fun y : Vec d => onePointRealExtension P.f (y : OnePoint (Vec d))) = P.f := rfl
  have hstep : ∀ n : ℕ,
      IsConservative.killedResolvent R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
          (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
          (PositiveC0ContractiveResolvent.onePointLiveExtension
            (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) ≤
        ENNReal.ofReal
          ((A.analyticPenalizedResolvent P.hV.isOpen n P.lam P.f P.hf hfD
            x).toReal) := by
    intro n
    have hqm : Measurable
        (onePointRealExtension (wholeSpacePenalizationPotential P.V n)) :=
      measurable_onePointRealExtension
        (measurable_wholeSpacePenalizationPotential P.hV.isOpen n)
    have hq0 : ∀ z,
        0 ≤ onePointRealExtension (wholeSpacePenalizationPotential P.V n) z := by
      intro z
      induction z using OnePoint.rec with
      | infty => simp
      | coe y => simpa using wholeSpacePenalizationPotential_nonneg P.V n y
    have hqC : ∀ z,
        onePointRealExtension (wholeSpacePenalizationPotential P.V n) z ≤ (n : ℝ) := by
      intro z
      induction z using OnePoint.rec with
      | infty => simp
      | coe y => simpa using wholeSpacePenalizationPotential_le P.V n y
    have hqU : ∀ z ∈ (((↑) : Vec d → OnePoint (Vec d)) '' P.V),
        onePointRealExtension (wholeSpacePenalizationPotential P.V n) z = 0 := by
      rintro z ⟨y, hy, rfl⟩
      simpa using wholeSpacePenalizationPotential_eq_zero n hy
    have hassump : PenalizedResolventFamilyAssumptions R.onePointKernelSemigroup
        (onePointRealExtension (wholeSpacePenalizationPotential P.V n)) (n : ℝ)
        (A.penalizedComparisonFamily P.hV.isOpen n R) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro lam hlam f hf hfb
        obtain ⟨E, hE⟩ := hfb
        exact A.measurable_penalizedComparisonFamily P.hV.isOpen n R hlam hf hE
      · intro lam hlam f hf hfb
        obtain ⟨E, hE⟩ := hfb
        exact ⟨E / lam,
          A.abs_penalizedComparisonFamily_le P.hV.isOpen n R hlam hf hE⟩
      · intro mu lam hmu hlam f hf hfb
        obtain ⟨E, hE⟩ := hfb
        exact A.penalizedComparisonFamily_resolventIdentity P.hV.isOpen n R hmu
          hlam hf hE
      · intro lam hlam f hf hfb
        obtain ⟨E, hE⟩ := hfb
        exact A.penalizedComparisonFamily_perturbation P.hV.isOpen n R hcons hid
          (lt_of_le_of_lt (Nat.cast_nonneg n) hlam) hf hE
    have hdom := killedResolvent_le_of_penalizedResolventFamily
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
      R.isFellerKernelSemigroup_onePointKernelSemigroup hreg.kolmogorovRegular
      (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) hqm hqU hq0 hqC
      (A.penalizedComparisonFamily P.hV.isOpen n R) hassump hFm hF0 hFD
      P.lam.property (x : OnePoint (Vec d))
    rw [ofReal_onePointRealExtension_eq_onePointLiveExtension P.f] at hdom
    refine hdom.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    rw [A.penalizedComparisonFamily_coe P.hV.isOpen n R P.lam.property hFm hFD x,
      A.analyticPenalizedResolventReal_congr P.hV.isOpen n P.lam hrestrict
        (hFm.comp OnePoint.continuous_coe.measurable) P.hf
        (fun y => hFD (y : OnePoint (Vec d))) hfD x]
    exact A.analyticPenalizedResolventReal_eq_toReal P.hV.isOpen n P.lam P.hf
      P.hf0 hfD x
  have hfin : IsConservative.killedResolvent R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
      (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
      (PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hstep 0)
  have hreal : ∀ n : ℕ,
      (IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d))).toReal ≤
        (A.analyticPenalizedResolvent P.hV.isOpen n P.lam P.f P.hf hfD x).toReal := by
    intro n
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hstep n)
    rwa [ENNReal.toReal_ofReal ENNReal.toReal_nonneg] at this
  have hinf := le_ciInf hreal
  exact (ENNReal.le_ofReal_iff_toReal_le hfin
    (le_trans ENNReal.toReal_nonneg (hinf.trans hc))).2 (hinf.trans hc)

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
