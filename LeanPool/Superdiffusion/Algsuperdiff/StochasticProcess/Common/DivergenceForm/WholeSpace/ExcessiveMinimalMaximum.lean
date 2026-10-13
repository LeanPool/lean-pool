/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Continuity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExcessiveCubeMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PositiveC0Resolvent

/-!
# ExcessiveMinimalMaximum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The maximum principle for the whole-space barrier

The truncated barriers increase to the whole-space barrier, and one fixed cube
resolvent is continuous along a uniformly bounded pointwise convergent
sequence of observables.  Applying a fixed cube resolvent to the whole-space
barrier is therefore the limit of applying it to the truncated barriers; each
of those is dominated, by monotonicity in the cube index, by the cube
resolvent at the index of the truncation, where the maximum principle of the
previous step applies.

Taking the supremum over the exhaustion gives the maximum principle for the
analytic minimal resolvent:

`mu R^min_mu v <= mu / (mu - lam) * v`  for every `mu > lam`,

at every point of the whole space.  This is exactly the resolvent hypothesis
of the exponential comparison used to produce `lam`-excessive functions.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- One cube resolvent is continuous along uniformly bounded pointwise
convergent data. -/
theorem tendsto_analyticCubeResolvent_of_tendsto (nu : PositiveShift)
    {gk : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hgk : ∀ k, Measurable (gk k)) (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hgkC : ∀ k y, |gk k y| ≤ C) (hgC : ∀ y, |g y| ≤ C)
    (hconv : ∀ y, Tendsto (fun k => gk k y) atTop (nhds (g y)))
    (m : ℕ) (x : Vec d) :
    Tendsto (fun k => A.analyticCubeResolvent nu (gk k) (hgk k)
        (fun y => hgkC k y) m x) atTop
      (nhds (A.analyticCubeResolvent nu g hg (fun y => hgC y) m x)) := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let Fk : ℕ → ScalarL2 (wholeSpaceCube d m) := fun k =>
      boundedMeasurableToScalarL2 hU ((hgk k).comp measurable_subtype_coe)
        (fun y => hgkC k y)
    let Fl : ScalarL2 (wholeSpaceCube d m) :=
      boundedMeasurableToScalarL2 hU (hg.comp measurable_subtype_coe)
        (fun y => hgC y)
    have hFk : ∀ k, Fk k =ᵐ[volumeMeasureOn (wholeSpaceCube d m)]
        domainExtension (gk k ∘ Subtype.val) := fun k =>
      boundedMeasurableToScalarL2_coeFn hU ((hgk k).comp measurable_subtype_coe)
        (fun y => hgkC k y)
    have hFl := boundedMeasurableToScalarL2_coeFn hU
      (hg.comp measurable_subtype_coe) (fun y => hgC y)
    have hpt : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
        Tendsto (fun k => Fk k y) atTop (nhds (Fl y)) := by
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      rw [hyl, domainExtension_of_mem hyU]
      refine (hconv y).congr' ?_
      filter_upwards with k
      rw [hyk k, domainExtension_of_mem hyU]
      rfl
    have hdiff : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
        ∀ k, |Fk k y - Fl y| ≤ 2 * C := by
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      intro k
      rw [hyk k, hyl, domainExtension_of_mem hyU, domainExtension_of_mem hyU]
      calc
        |gk k y - g y| ≤ |gk k y| + |g y| := abs_sub _ _
        _ ≤ C + C := add_le_add (hgkC k y) (hgC y)
        _ = 2 * C := by ring
    have hnorm : Tendsto (fun k => ‖Fk k - Fl‖) atTop (nhds 0) :=
      tendsto_norm_scalarL2_sub_of_bounded_ae_tendsto hU hdiff hpt
    have hdiff' : ∀ k, ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
        |Fk k y - Fl y| ≤ 2 * C := fun k => hdiff.mono fun _ hy => hy k
    exact tendsto_representative_of_tendsto_norm_continuousCoeff A.a hU
      nu.property A.hnu (A.cubeEllipticity m) A.hsymm
      (A.skewContinuousOnCube m) A.hd
      (M := 2 * C) (by linarith only [hC]) hdiff' hnorm
      (fun k => A.continuousOn_analyticCubeResolvent nu (hgk k)
        (fun y => hgkC k y) m)
      (fun k => A.analyticCubeResolvent_ae nu (hgk k) (fun y => hgkC k y) m)
      (A.continuousOn_analyticCubeResolvent nu hg (fun y => hgC y) m)
      (A.analyticCubeResolvent_ae nu hg (fun y => hgC y) m) hx
  · simp only [analyticCubeResolvent, dite_eq_right hx]
    exact tendsto_const_nhds

/-- One cube resolvent depends only on the almost-everywhere class of its
observable. -/
theorem analyticCubeResolvent_congr_ae (mu : PositiveShift) {f g : Vec d → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (hfg : f =ᵐ[volume] g)
    (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent mu f hf hfD m x =
      A.analyticCubeResolvent mu g hg hgE m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · rw [analyticCubeResolvent, dite_eq_left hx, analyticCubeResolvent, dite_eq_left hx]
    let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    have hdatum : boundedMeasurableToScalarL2 hU
        (hf.comp measurable_subtype_coe) (fun y => hfD y) =
        boundedMeasurableToScalarL2 hU
          (hg.comp measurable_subtype_coe) (fun y => hgE y) := by
      refine (Lp.ext_iff).2 ?_
      filter_upwards [boundedMeasurableToScalarL2_coeFn hU
          (hf.comp measurable_subtype_coe) (fun y => hfD y),
        boundedMeasurableToScalarL2_coeFn hU
          (hg.comp measurable_subtype_coe) (fun y => hgE y),
        ae_restrict_of_ae hfg,
        self_mem_ae_restrict hU.isOpen.measurableSet] with y h1 h2 h3 hy
      rw [h1, h2, domainExtension_of_mem hy, domainExtension_of_mem hy]
      exact h3
    refine continuousCoeffBoundedResolvent_eq_of_continuousOn_of_ae_eq A.a hU
      A.hnu A.hnu (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd
      mu (hg.comp measurable_subtype_coe) (fun y => hgE y)
      (continuousOn_continuousCoeffBoundedResolvent A.a hU A.hnu A.hnu
        (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y)) ?_ hx
    rw [← hdatum]
    exact continuousCoeffBoundedResolvent_ae A.a hU A.hnu A.hnu
      (A.cubeEllipticity m) A.hsymm (A.skewContinuousOnCube m) A.hd mu
      (hf.comp measurable_subtype_coe) (fun y => hfD y)
  · rw [analyticCubeResolvent, dite_eq_right hx, analyticCubeResolvent, dite_eq_right hx]

/-- The minimal resolvent depends only on the almost-everywhere class of its
observable. -/
theorem analyticMinimalResolvent_congr_ae (mu : PositiveShift)
    {f g : Vec d → ℝ} (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (hgE : ∀ x, |g x| ≤ E) (hfg : f =ᵐ[volume] g)
    (x : Vec d) :
    A.analyticMinimalResolvent mu f hf hfD x =
      A.analyticMinimalResolvent mu g hg hgE x := by
  unfold WholeSpaceAnalyticData.analyticMinimalResolvent
  refine iSup_congr fun m => ?_
  unfold WholeSpaceAnalyticData.analyticCubeResolventENN
  exact congrArg ENNReal.ofReal
    (A.analyticCubeResolvent_congr_ae mu hf hg hfD hgE hfg m x)

end WholeSpaceAnalyticData

namespace WholeSpaceBarrierData

variable {A : WholeSpaceAnalyticData d} (P : WholeSpaceBarrierData A)

theorem barrierBound_nonneg : 0 ≤ 2 * (P.D / (P.lam : ℝ)) :=
  mul_nonneg (by norm_num)
    (div_nonneg P.bound_nonneg P.lam.property.le)

/-- **The maximum principle for the whole-space barrier, on one cube.** -/
theorem mul_analyticCubeResolvent_barrier_le (mu : PositiveShift)
    (hmu : (P.lam : ℝ) < (mu : ℝ)) (n : ℕ) (x : Vec d) :
    (mu : ℝ) * A.analyticCubeResolvent mu P.barrier P.measurable_barrier
        (fun y => P.abs_barrier_le y) n x ≤
      (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.barrier x := by
  obtain ⟨M, hVM⟩ :=
    exists_wholeSpaceCube_superset P.hV.isBoundedDomain.isBounded
  have hcoef : 0 ≤ (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) := by
    have h1 : 0 < (mu : ℝ) - (P.lam : ℝ) := by linarith only [hmu]
    exact div_nonneg mu.property.le h1.le
  have hconv : ∀ y, Filter.Tendsto (fun k => P.cubeBarrier (k + M) y)
      Filter.atTop (nhds (P.barrier y)) := fun y =>
    (P.tendsto_cubeBarrier y).comp (Filter.tendsto_add_atTop_nat M)
  have htend := A.tendsto_analyticCubeResolvent_of_tendsto mu
    (fun k => P.measurable_cubeBarrier (k + M)) P.measurable_barrier
    (C := 2 * (P.D / (P.lam : ℝ))) P.barrierBound_nonneg
    (fun k y => P.abs_cubeBarrier_le (k + M) y)
    (fun y => P.abs_barrier_le y) hconv n x
  refine le_of_tendsto (htend.const_mul (mu : ℝ)) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with k hk
  have hVk : P.V ⊆ wholeSpaceCube d (k + M) :=
    hVM.trans (WholeSpaceAnalyticData.wholeSpaceCube_mono (Nat.le_add_left M k))
  have hnk : n ≤ k + M := hk.trans (Nat.le_add_right k M)
  have hmono := A.monotone_analyticCubeResolvent mu
    (P.measurable_cubeBarrier (k + M))
    (fun y => P.cubeBarrier_nonneg (k + M) hVk y)
    (fun y => P.abs_cubeBarrier_le (k + M) y) x hnk
  have hstep := P.mul_analyticCubeResolvent_cubeBarrier_le (k + M) hVk mu hmu x
  have hfinal : (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.cubeBarrier (k + M) x ≤
      (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.barrier x :=
    mul_le_mul_of_nonneg_left (P.cubeBarrier_le_barrier (k + M) x) hcoef
  have hmul : (mu : ℝ) * A.analyticCubeResolvent mu (P.cubeBarrier (k + M))
        (P.measurable_cubeBarrier (k + M))
        (fun y => P.abs_cubeBarrier_le (k + M) y) n x ≤
      (mu : ℝ) * A.analyticCubeResolvent mu (P.cubeBarrier (k + M))
        (P.measurable_cubeBarrier (k + M))
        (fun y => P.abs_cubeBarrier_le (k + M) y) (k + M) x :=
    mul_le_mul_of_nonneg_left hmono mu.property.le
  exact hmul.trans (hstep.trans hfinal)

/-- **The maximum principle for the whole-space barrier.** -/
theorem mul_analyticMinimalResolvent_barrier_le (mu : PositiveShift)
    (hmu : (P.lam : ℝ) < (mu : ℝ)) (x : Vec d) :
    (mu : ℝ) * (A.analyticMinimalResolvent mu P.barrier P.measurable_barrier
        (fun y => P.abs_barrier_le y) x).toReal ≤
      (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.barrier x := by
  have htend := A.tendsto_analyticCubeResolvent mu P.measurable_barrier
    P.barrier_nonneg P.barrierBound_nonneg (fun y => P.abs_barrier_le y) x
  refine le_of_tendsto (htend.const_mul (mu : ℝ)) ?_
  filter_upwards with n
  exact P.mul_analyticCubeResolvent_barrier_le mu hmu n x

/-- The maximum principle in the signed form of the minimal resolvent. -/
theorem mul_analyticMinimalResolventReal_barrier_le (mu : PositiveShift)
    (hmu : (P.lam : ℝ) < (mu : ℝ)) (x : Vec d) :
    (mu : ℝ) * A.analyticMinimalResolventReal mu P.barrier P.measurable_barrier
        (fun y => P.abs_barrier_le y) x ≤
      (mu : ℝ) / ((mu : ℝ) - (P.lam : ℝ)) * P.barrier x := by
  rw [A.analyticMinimalResolventReal_eq_toReal mu P.measurable_barrier
    P.barrier_nonneg (fun y => P.abs_barrier_le y) x]
  exact P.mul_analyticMinimalResolvent_barrier_le mu hmu x

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
