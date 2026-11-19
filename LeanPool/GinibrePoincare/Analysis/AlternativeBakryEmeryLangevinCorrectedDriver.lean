/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinCorrectedDriver.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinConfiguration
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltCanonicalMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
/-!
# Alternative Bakry Emery Langevin corrected driver

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryCorrectedCompactDriver_law`, `bakryEmeryCorrectedCompactDriver_zero`,
`bakryEmeryCorrectedCompactDriver_ae_eq`, `bakryEmeryOriginalCompactDriver_ae_eq`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance bakryCorrectedDriverFullPathMeasurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration
    n) := borel _
local instance bakryCorrectedDriver_fullPathBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n) :=
    ⟨rfl⟩
/-- The Borel σ-algebra on continuous Euclidean paths
`C(Icc 0 T, EuclideanSpace ℝ (Fin n × Fin 2))`. -/
local instance bakryCorrectedDriverCompactPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) := borel _
local instance bakryCorrectedDriver_compactPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) := ⟨rfl⟩

lemma bakryEmeryGibbsConfigurationTilt_continuous {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) :
    Continuous (bakryEmeryGibbsConfigurationTilt n W) := by
  have hS : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  exact (ginibreBrownianEmbeddingCLM n ((n : ℝ)^2)).continuous.comp
    (continuous_pi (fun i => bakryEmeryGibbsPotentialTilt_continuous n ((n : ℝ)^2) _ hS i))

/-- The continuous Brownian noise of `B` (with `α = n²`) restricted to `[0, T]` and transported
to Euclidean coordinates by `configurationEuclideanEquiv`. -/
def bakryEmeryOriginalCompactDriver {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) where
  toFun t := configurationEuclideanEquiv n ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2)
      ω).val t)
  continuous_toFun := (configurationEuclideanEquiv n).continuous.comp
    ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) ω).val.continuous.comp
        continuous_subtype_val)

/-- The drift-corrected driver on `[0, T]`: the original Brownian driver minus the time integral
of the configuration tilt of `W` along the path `Y`, in Euclidean coordinates. -/
def bakryEmeryCorrectedCompactDriver {Ω : Type*} (n : ℕ)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ ω, Continuous (fun t => Y t ω)) (ω : Ω) :
    C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) where
  toFun t := bakryEmeryOriginalCompactDriver n B T ω t -
    ∫ s in (0 : ℝ)..(t : ℝ), configurationEuclideanEquiv n
      (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω))
  continuous_toFun := by
    have hc : Continuous (fun s : ℝ => configurationEuclideanEquiv n
        (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω))) :=
      (configurationEuclideanEquiv n).continuous.comp
        ((bakryEmeryGibbsConfigurationTilt_continuous W hW).comp
          ((hYC ω).comp continuous_real_toNNReal))
    exact (bakryEmeryOriginalCompactDriver n B T ω).continuous.sub
      ((intervalIntegral.differentiable_integral_of_continuous hc).continuous.comp
          continuous_subtype_val)

theorem bakryEmeryOriginalCompactDriver_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    Measurable (bakryEmeryOriginalCompactDriver n B T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have heval : Continuous (fun N : GinibreContinuousNoise n =>
      configurationEuclideanEquiv n (N.val (t : ℝ))) :=
    (configurationEuclideanEquiv n).continuous.comp
      ((continuous_eval_const (t : ℝ)).comp continuous_subtype_val)
  exact heval.measurable.comp
    (ginibreBrownianFullContinuousNoise_measurable n B P hB ((n : ℝ)^2))

theorem bakryEmeryCorrectedCompactDriver_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ ω, Continuous (fun t => Y t ω))
    (hY : StronglyAdapted (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) Y) :
    Measurable (bakryEmeryCorrectedCompactDriver n W hW B T Y hYC) := by
  have hYm (t : ℝ≥0) : Measurable (Y t) := (hY t).measurable.mono
    ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).le t) le_rfl
  let v := fun s : ℝ => fun ω => configurationEuclideanEquiv n
    (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω))
  have hvC (ω : Ω) : Continuous (fun s => v s ω) :=
    (configurationEuclideanEquiv n).continuous.comp
      ((bakryEmeryGibbsConfigurationTilt_continuous W hW).comp
        ((hYC ω).comp continuous_real_toNNReal))
  have hvM (s : ℝ) : Measurable (v s) :=
    (configurationEuclideanEquiv n).continuous.measurable.comp
      ((bakryEmeryGibbsConfigurationTilt_continuous W hW).measurable.comp (hYm s.toNNReal))
  have hv := measurable_uncurry_of_continuous_of_measurable hvC hvM
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hm : Measurable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), v s ω) := by
    rw [show (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), v s ω) =
      (fun ω => ∫ s in Ioc (0 : ℝ) (t : ℝ), v s ω) by
      funext ω; rw [intervalIntegral.integral_of_le t.property.1]]
    have hs : StronglyMeasurable (Function.uncurry (fun ω s => v s ω)) := by
      convert (hv.comp measurable_swap).stronglyMeasurable using 1
      funext p
      rfl
    exact hs.integral_prod_right.measurable
  exact ((ContinuousMap.measurable_eval t).comp
    (bakryEmeryOriginalCompactDriver_measurable n B P hB T)).sub hm

/-- Transport of a raw coordinate path `x`, indexed by `Icc 0 T` in `ℝ≥0`, to a Euclidean-valued
function on `Icc 0 T` in `ℝ` through `ginibreBrownianEmbeddingCLM` with `α = n²`. -/
def bakryEmeryRawDriverEmbedding (n : ℕ) (T : ℝ≥0)
    (x : Icc (0 : ℝ≥0) T → (Fin n × Fin 2) → ℝ)
    (t : Icc (0 : ℝ) (T : ℝ)) : EuclideanSpace ℝ (Fin n × Fin 2) :=
  configurationEuclideanEquiv n (ginibreBrownianEmbeddingCLM n ((n : ℝ)^2)
    (x ⟨(t : ℝ).toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.mpr t.property.2⟩⟩))

lemma bakryEmeryRawDriverEmbedding_measurable (n : ℕ) (T : ℝ≥0) :
    Measurable (bakryEmeryRawDriverEmbedding n T) := by
  apply Measurable.of_eval
  intro t
  exact (configurationEuclideanEquiv n).continuous.measurable.comp
    ((ginibreBrownianEmbeddingCLM n ((n : ℝ)^2)).continuous.measurable.comp (measurable_pi_apply _))

lemma bakryEmeryPotentialTilt_time_integral_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ ω, Continuous (fun t => Y t ω))
    (hYm : ∀ t, Measurable (Y t)) (i : Fin n × Fin 2) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun ω => ∫ s in (0 : ℝ)..t,
      bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) (bakryEmeryGibbsRelativePotential W)
        (Y s.toNNReal ω) i) := by
  have hS : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  let v := fun s : ℝ => fun ω => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
    (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal ω) i
  have hc (ω : Ω) : Continuous (fun s => v s ω) :=
    (bakryEmeryGibbsPotentialTilt_continuous n ((n : ℝ)^2) _ hS i).comp
      ((hYC ω).comp continuous_real_toNNReal)
  have hm (s : ℝ) : Measurable (v s) :=
    (bakryEmeryGibbsPotentialTilt_measurable n ((n : ℝ)^2) _ i).comp (hYm s.toNNReal)
  have hv := measurable_uncurry_of_continuous_of_measurable hc hm
  have hs : StronglyMeasurable (Function.uncurry (fun ω s => v s ω)) := by
    convert (hv.comp measurable_swap).stronglyMeasurable using 1
    funext p; rfl
  have hh : Measurable (fun ω => ∫ s in Ioc (0 : ℝ) t, v s ω) := hs.integral_prod_right.measurable
  simpa only [v, intervalIntegral.integral_of_le ht] using hh

lemma bakryEmeryRawDriverEmbedding_corrected_eq {Ω : Type*} (n : ℕ)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ ω, Continuous (fun t => Y t ω))
    (ω : Ω) (t : Icc (0 : ℝ) (T : ℝ)) :
    bakryEmeryRawDriverEmbedding n T (fun u i => B i u.val ω-B i 0 ω-
      ∫ s in (0 : ℝ)..(u.val : ℝ), bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
        (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal ω) i) t =
    configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω t) -
      configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω 0) -
      ∫ s in (0 : ℝ)..(t : ℝ), configurationEuclideanEquiv n
        (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω)) := by
  let F := fun i r ω => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
    (bakryEmeryGibbsRelativePotential W) (Y r ω) i
  have hS : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  have hFc : Continuous (fun s : ℝ => fun i => F i s.toNNReal ω) :=
    continuous_pi (fun i => (bakryEmeryGibbsPotentialTilt_continuous n ((n : ℝ)^2) _ hS i).comp
      ((hYC ω).comp continuous_real_toNNReal))
  have hh := ginibreCorrectedBrownianNoise_eq n ((n : ℝ)^2) B F ω t t.property.1
    (hFc.intervalIntegrable 0 t)
  have he := congrArg (configurationEuclideanEquiv n) hh
  have htilt : Continuous (fun s : ℝ => bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω)) :=
    (bakryEmeryGibbsConfigurationTilt_continuous W hW).comp
      ((hYC ω).comp continuous_real_toNNReal)
  have hc := (configurationEuclideanEquiv n).toContinuousLinearMap.intervalIntegral_comp_comm (μ :=
      volume)
    (htilt.intervalIntegrable 0 t)
  change (∫ s in (0 : ℝ)..(t : ℝ), configurationEuclideanEquiv n
    (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω))) =
    configurationEuclideanEquiv n (∫ s in (0 : ℝ)..(t : ℝ),
      bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω)) at hc
  have he' : configurationEuclideanEquiv n
      (ginibreConfigurationBrownianNoise n
        (fun i r ω => B i r ω-B i 0 ω-∫ s in (0 : ℝ)..(r : ℝ), F i s.toNNReal ω)
        ((n : ℝ)^2) ω t) =
      configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω t) -
      configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω 0) -
      ∫ s in (0 : ℝ)..(t : ℝ), configurationEuclideanEquiv n
        (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω)) := by
    rw [hc]
    simpa only [map_sub, bakryEmeryGibbsConfigurationTilt, F] using he
  convert he' using 1
  simp only [bakryEmeryRawDriverEmbedding]
  apply congrArg (configurationEuclideanEquiv n)
  ext j
  simp only [ginibreConfigurationBrownianNoise, ginibreBrownianEmbeddingCLM_apply,
    Real.coe_toNNReal _ t.property.1, F]

lemma bakryEmeryRawDriverEmbedding_original_eq {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (t : Icc (0 : ℝ) (T : ℝ)) :
    bakryEmeryRawDriverEmbedding n T (fun u i => B i u.val ω-B i 0 ω) t =
      configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω t) -
      configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω 0) := by
  change configurationEuclideanEquiv n (ginibreBrownianEmbeddingCLM n ((n : ℝ)^2)
    ((fun i => B i (t : ℝ).toNNReal ω)-(fun i => B i 0 ω))) = _
  rw [map_sub, map_sub]
  congr 1; apply congrArg (configurationEuclideanEquiv n); ext j;
    simp only [ginibreConfigurationBrownianNoise, ginibreBrownianEmbeddingCLM_apply,
        Real.toNNReal_zero]

/-- Transfer of the actual relative-potential Girsanov whole-driver law to
the measurable compact continuous Hilbert drivers used by the actual flow. -/
theorem bakryEmeryCorrectedCompactDriver_law {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ ω, Continuous (fun t => Y t ω))
    (hY : StronglyAdapted (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) Y) (d : Ω → ENNReal)
    (hLaw : (P.withDensity d).map
      (fun ω (u : Icc (0 : ℝ≥0) T) i => B i u.val ω - B i 0 ω -
        ∫ s in (0 : ℝ)..(u.val : ℝ), bakryEmeryGibbsPotentialTilt n ((n : ℝ) ^ 2)
          (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal ω) i) =
      P.map (fun ω (u : Icc (0 : ℝ≥0) T) i => B i u.val ω - B i 0 ω)) :
    (P.withDensity d).map (bakryEmeryCorrectedCompactDriver n W hW B T Y hYC) =
      P.map (bakryEmeryOriginalCompactDriver n B T) := by
  let : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  let Q := P.withDensity d
  let X := fun ω (u : Icc (0 : ℝ≥0) T) i => B i u.val ω-B i 0 ω-
    ∫ s in (0 : ℝ)..(u.val : ℝ), bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
      (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal ω) i
  let Z := fun ω (u : Icc (0 : ℝ≥0) T) i => B i u.val ω-B i 0 ω
  have hYm (t : ℝ≥0) : Measurable (Y t) := (hY t).measurable.mono
    ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).le t) le_rfl
  have hXm : Measurable X := by
    apply Measurable.of_eval
    intro u
    apply Measurable.of_eval
    intro i
    exact ((aemeasurable_iff_measurable.mp ((hB i).aemeasurable u.val)).sub
      (aemeasurable_iff_measurable.mp ((hB i).aemeasurable 0))).sub
      (bakryEmeryPotentialTilt_time_integral_measurable n W hW Y hYC hYm i u.val u.val.property)
  have hZm : Measurable Z := by
    apply Measurable.of_eval
    intro u
    apply Measurable.of_eval
    intro i
    exact (aemeasurable_iff_measurable.mp ((hB i).aemeasurable u.val)).sub
      (aemeasurable_iff_measurable.mp ((hB i).aemeasurable 0))
  have hC : (fun ω t => bakryEmeryCorrectedCompactDriver n W hW B T Y hYC ω t) =ᵐ[P]
      (fun ω => bakryEmeryRawDriverEmbedding n T (X ω)) := by
    filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB ((n : ℝ)^2),
      ginibreConfigurationBrownianNoise_actual n B P hB ((n : ℝ)^2)] with ω he hz
    funext t
    rw [bakryEmeryRawDriverEmbedding_corrected_eq n W hW B T Y hYC ω t,
      hz.2, map_zero, sub_zero]
    change configurationEuclideanEquiv n ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) ω).val
        t) -
      (∫ s in (0 : ℝ)..(t : ℝ), configurationEuclideanEquiv n
        (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω))) = _
    rw [he]
  have hO : (fun ω t => bakryEmeryOriginalCompactDriver n B T ω t) =ᵐ[P]
      (fun ω => bakryEmeryRawDriverEmbedding n T (Z ω)) := by
    filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB ((n : ℝ)^2),
      ginibreConfigurationBrownianNoise_actual n B P hB ((n : ℝ)^2)] with ω he hz
    funext t
    rw [bakryEmeryRawDriverEmbedding_original_eq n B T ω t, hz.2, map_zero, sub_zero]
    change configurationEuclideanEquiv n ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) ω).val
        t) = _
    rw [he]
  have hmap := congrArg (Measure.map (bakryEmeryRawDriverEmbedding n T)) hLaw
  rw [Measure.map_map (bakryEmeryRawDriverEmbedding_measurable n T) hXm,
    Measure.map_map (bakryEmeryRawDriverEmbedding_measurable n T) hZm] at hmap
  apply actualContinuousMap_law_eq_of_raw_path_law Q P
    (bakryEmeryCorrectedCompactDriver n W hW B T Y hYC) (bakryEmeryOriginalCompactDriver n B T)
    (bakryEmeryCorrectedCompactDriver_measurable n W hW B P hB T Y hYC hY)
    (bakryEmeryOriginalCompactDriver_measurable n B P hB T)
  exact (Measure.map_congr ((withDensity_absolutelyContinuous P d).ae_le hC)).trans
    (hmap.trans (Measure.map_congr hO).symm)

theorem bakryEmeryCorrectedCompactDriver_zero {Ω : Type*} (n : ℕ)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ ω, Continuous (fun t => Y t ω)) (ω : Ω) :
    bakryEmeryCorrectedCompactDriver n W hW B T Y hYC ω ⟨0, ⟨le_rfl, T.property⟩⟩ = 0 := by
  change configurationEuclideanEquiv n ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) ω).val
      0) -
    (∫ s in (0 : ℝ)..0, configurationEuclideanEquiv n
      (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω))) = 0
  rw [(ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) ω).property]
  simp

theorem bakryEmeryCorrectedCompactDriver_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ ω, Continuous (fun t => Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ),
      bakryEmeryCorrectedCompactDriver n W hW B T Y hYC ω t =
      configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n
        (fun i r ω => B i r ω-B i 0 ω-∫ s in (0 : ℝ)..(r : ℝ),
          bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) (bakryEmeryGibbsRelativePotential W)
            (Y s.toNNReal ω) i) ((n : ℝ)^2) ω t) := by
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB ((n : ℝ)^2),
    ginibreConfigurationBrownianNoise_actual n B P hB ((n : ℝ)^2)] with ω he hz
  intro t
  have hh := bakryEmeryRawDriverEmbedding_corrected_eq n W hW B T Y hYC ω t
  rw [hz.2, map_zero, sub_zero] at hh
  have hraw : bakryEmeryCorrectedCompactDriver n W hW B T Y hYC ω t =
      bakryEmeryRawDriverEmbedding n T (fun u i => B i u.val ω-B i 0 ω-
        ∫ s in (0 : ℝ)..(u.val : ℝ), bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
          (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal ω) i) t := by
    rw [hh]
    change configurationEuclideanEquiv n ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) ω).val
        t) -
      (∫ s in (0 : ℝ)..(t : ℝ), configurationEuclideanEquiv n
        (bakryEmeryGibbsConfigurationTilt n W (Y s.toNNReal ω))) = _
    rw [he]
  rw [hraw]
  simp only [bakryEmeryRawDriverEmbedding]
  apply congrArg (configurationEuclideanEquiv n)
  ext j
  simp only [ginibreConfigurationBrownianNoise, ginibreBrownianEmbeddingCLM_apply,
    Real.coe_toNNReal _ t.property.1]

theorem bakryEmeryOriginalCompactDriver_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ), bakryEmeryOriginalCompactDriver n B T ω t =
      configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) ω t) := by
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB ((n : ℝ)^2)] with ω he
  intro t
  exact congrArg (configurationEuclideanEquiv n) (he t)

end
end GinibrePoincare
