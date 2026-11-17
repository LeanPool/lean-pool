/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.InteriorRegularity
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Convergence
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance

/-!
# Density of compact smooth diffusion images in centered `L²`

For a log-concave probability law `ν = m.tilted (−U)` on a finite-dimensional real inner-product
space, with `U` of class
`C¹` and `m` an additive Haar measure, the literal images `−L f` of compactly supported smooth `f`
under the ordinary
weighted diffusion operator (`compactSmoothDiffusionImage`) are dense in the mean-zero real classes
of `L²(ν)`: every
`g ∈ L²(ν)` with mean `0` lies in their closure
(`centered_mem_closure_compactSmoothDiffusionImage`), and so does the
centering of every `g` (`center_mem_closure_compactSmoothDiffusionImage`). The class `g` is
arbitrary (no operator-domain or
compact-test restriction). Route: the kernel of the closed weighted operator consists of constants,
so the range of
`T†T` is dense in the centered classes, and every element of that range is approximated by the
images of compactly
supported smooth functions. Supporting infrastructure for the finite-energy Brascamp–Lieb inequality
of Letwin,
arXiv:2607.24164v1, Lemma A.6; not Brascamp–Lieb, A.6, the moment map or Theorem 2.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace LinearPMap

namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The literal compactly supported smooth diffusion images used in the range-density statement. -/
def compactSmoothDiffusionImage {ν : ProbabilityMeasure V} {U : V → ℝ}
    (hU : ContDiff ℝ 1 U) : Set (Lp ℝ 2 (ν : Measure V)) :=
  {w | ∃ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f),
    w = (memLp_neg_weightedLaplacian (ν := ν) hU hf hc).toLp
      (fun x => -weightedLaplacian U f x)}

/-- Every mean-zero real `L²` class is approximable by literal compact smooth diffusion images. -/
theorem centered_mem_closure_compactSmoothDiffusionImage
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (g : Lp ℝ 2 (ν : Measure V)) (hg : L2.mean ν g = 0) :
    g ∈ closure (compactSmoothDiffusionImage hU) := by
  have hi : (interior (ν : Measure V).support).Nonempty :=
    interior_support_nonempty_of_eq_tilted m hνU
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let A := adjointComp T
  have hTc : T.IsClosed := by
    dsimp [T]
    exact hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  have hTd : Dense (T.domain : Set (Lp ℝ 2 (ν : Measure V))) := by
    dsimp [T]
    exact hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have horth : ∀ k : A.domain, A k = 0 →
      ⟪g, (k : Lp ℝ 2 (ν : Measure V))⟫ = 0 := by
    intro k hk
    have hkT : T ⟨(k : Lp ℝ 2 (ν : Measure V)), k.2.2⟩ = 0 := by
      exact (adjointComp_eq_zero_iff T hTd k).mp hk
    have hkconst : (k : Lp ℝ 2 (ν : Measure V)) =
        L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) := by
      simpa [T] using
        (eq_const_mean_of_closedWeightedOperator_eq_zero m hν hi hνU hU.continuous
          ⟨(k : Lp ℝ 2 (ν : Measure V)), k.2.2⟩ (by simpa [T] using hkT))
    have hcs : L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) =
        (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) • L2.const ν 1 := by
      simpa using
        (L2.const_smul ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) 1)
    calc
      ⟪g, (k : Lp ℝ 2 (ν : Measure V))⟫ =
          ⟪g, L2.const ν (L2.mean ν (k : Lp ℝ 2 (ν : Measure V)))⟫ :=
        congrArg (fun z => ⟪g, z⟫) hkconst
      _ = (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))) * L2.mean ν g := by
        rw [hcs]
        simpa only [L2.mean] using
          (real_inner_smul_right g (L2.const ν 1)
            (L2.mean ν (k : Lp ℝ 2 (ν : Measure V))))
      _ = 0 := by rw [hg, mul_zero]
  have hgRange : g ∈ closure (Set.range fun y : A.domain => A y) := by
    exact mem_closure_range_of_inner_eq_zero T hTc hTd g horth
  have hsubset : closure (Set.range fun y : A.domain => A y) ⊆
      closure (compactSmoothDiffusionImage hU) := by
    apply closure_minimal
    · rintro z ⟨y, rfl⟩
      obtain ⟨fn, hfn, hfnc, hF, hA⟩ :=
        hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU y
      let yn : ℕ → A.domain := fun n =>
        ⟨(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν
            (hfn n) (hfnc n)).toLp (fn n), by
          simpa [A, T] using
            hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩
      have hAnorm : Tendsto (fun n => ‖A (yn n) - A y‖) atTop (𝓝 0) := by
        simpa [yn, A, T] using hA
      have hAtendsto : Tendsto (fun n => A (yn n)) atTop (𝓝 (A y)) := by
        refine Metric.tendsto_atTop.2 ?_
        intro ε hε
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hAnorm) ε hε
        refine ⟨N, ?_⟩
        intro n hn
        simpa [dist_eq_norm] using hN n hn
      have hyn : ∀ n, A (yn n) ∈ compactSmoothDiffusionImage hU := by
        intro n
        refine ⟨fn n, hfn n, hfnc n, ?_⟩
        simpa [yn, A, T] using
          (hν.adjointComp_toLp_eq m hi hνU hU (hfn n) (hfnc n))
      exact mem_closure_of_tendsto hAtendsto
        (Filter.Eventually.of_forall hyn)
    · exact isClosed_closure
  exact hsubset hgRange

/--
Every centered representative, including an arbitrary input after centering, has the same
approximation property. -/
theorem center_mem_closure_compactSmoothDiffusionImage {ν : ProbabilityMeasure V}
    (m : Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (g : Lp ℝ 2 (ν : Measure V)) : L2.center ν g ∈ closure (compactSmoothDiffusionImage hU) := by
  exact
    centered_mem_closure_compactSmoothDiffusionImage m hν hνU hU (L2.center ν g)
      (L2.mean_center ν g)

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
