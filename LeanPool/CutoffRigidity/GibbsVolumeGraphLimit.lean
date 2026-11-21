/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsCompactApproximation
public import LeanPool.CutoffRigidity.EuclideanL2Translations

/-!
# Passing actual Lebesgue graph approximations into weighted Gibbs H¹

Uniform convexity gives the actual bounded change-of-measure maps, also
for vector-valued gradients. Strong L² approximation by genuine compact C²
functions then places the limit in the actual closed Gibbs gradient graph.
No weak-derivative/domain membership is assumed for the limit.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Send vector-valued `L²` classes for volume to `L²` for the dominated Gibbs measure. -/
@[expose] noncomputable def volumeToGibbsL2Vector
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    (E →₂[volume] E) →L[ℝ] (E →₂[gibbsMeasure volume V] E) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (gibbsMeasure_le_smul_volume hV ρ hρ hHess)

theorem volumeToGibbsL2Vector_coeFn {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (f : E →₂[volume] E) :
    (volumeToGibbsL2Vector hV ρ hρ hHess f : E → E) =ᵐ[gibbsMeasure volume V] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (gibbsMeasure_le_smul_volume hV ρ hρ hHess) f

/-- The volume `L²` class of a compactly supported `C²` function. -/
@[expose] noncomputable def compactC2VolumeLp (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : E →₂[volume] ℝ :=
  (hf.continuous.memLp_of_hasCompactSupport hfc).toLp f

/-- The vector-valued volume `L²` class of the gradient of a compactly supported `C²` function. -/
@[expose] noncomputable def compactC2VolumeGradientLp (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : E →₂[volume] E :=
  (c1_compact_gradient_memLp (hf.of_le (by norm_num)) hfc).toLp (gradient f)

/-- The true change-of-measure maps send each genuine compact C² graph
pair into the actual closed Gibbs gradient graph. -/
theorem compactC2Volume_graph_mem_gibbs {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (volumeToGibbsL2 hV ρ hρ hHess (compactC2VolumeLp f hf hfc),
      volumeToGibbsL2Vector hV ρ hρ hHess (compactC2VolumeGradientLp f hf hfc)) ∈
        (closedGibbsGradient hV hprob).graph := by
  let S := volumeToGibbsL2 hV ρ hρ hHess
  let W := volumeToGibbsL2Vector hV ρ hρ hHess
  have hfa : (S (compactC2VolumeLp f hf hfc) : E → ℝ) =ᵐ[gibbsMeasure volume V] f :=
    (volumeToGibbsL2_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq (hf.continuous.memLp_of_hasCompactSupport
        hfc).coeFn_toLp)
  have hga : (W (compactC2VolumeGradientLp f hf hfc) : E → E) =ᵐ[gibbsMeasure volume V] gradient f
    :=
    (volumeToGibbsL2Vector_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq
        (c1_compact_gradient_memLp (hf.of_le (by norm_num)) hfc).coeFn_toLp)
  have hfm : MemLp f 2 (gibbsMeasure volume V) :=
    (memLp_congr_ae hfa).mp (Lp.memLp (S (compactC2VolumeLp f hf hfc)))
  have hgm : MemLp (gradient f) 2 (gibbsMeasure volume V) :=
    (memLp_congr_ae hga).mp (Lp.memLp (W (compactC2VolumeGradientLp f hf hfc)))
  have hfeq : S (compactC2VolumeLp f hf hfc) = hfm.toLp f :=
    Lp.ext (hfa.trans hfm.coeFn_toLp.symm)
  have hgeq : W (compactC2VolumeGradientLp f hf hfc) = hgm.toLp (gradient f) :=
    Lp.ext (hga.trans hgm.coeFn_toLp.symm)
  change (S (compactC2VolumeLp f hf hfc), W (compactC2VolumeGradientLp f hf hfc)) ∈ _
  rw [hfeq, hgeq]
  exact c2_function_mem_closedGibbsGradient_graph hV hprob hf hfm hgm

/-- Strong actual Lebesgue graph approximation yields membership in the
actual weighted closed-gradient graph, through proved bounded maps. -/
theorem closedGibbsGradient_mem_of_volume_L2_graph_limit {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (f : ℕ → E → ℝ) (hf : ∀ n, ContDiff ℝ 2 (f n)) (hfc : ∀ n, HasCompactSupport (f n))
    (u : E →₂[volume] ℝ) (G : E →₂[volume] E)
    (hu : Tendsto (fun n => compactC2VolumeLp (f n) (hf n) (hfc n)) atTop (𝓝 u))
    (hG : Tendsto (fun n => compactC2VolumeGradientLp (f n) (hf n) (hfc n)) atTop (𝓝 G)) :
    (volumeToGibbsL2 hV ρ hρ hHess u, volumeToGibbsL2Vector hV ρ hρ hHess G) ∈
      (closedGibbsGradient hV hprob).graph := by
  have hlim := ((volumeToGibbsL2 hV ρ hρ hHess).continuous.tendsto _ |>.comp hu).prodMk_nhds
    ((volumeToGibbsL2Vector hV ρ hρ hHess).continuous.tendsto _ |>.comp hG)
  exact (closedGibbsGradient_isClosed hV hprob).mem_of_tendsto hlim
    (Eventually.of_forall (fun n => compactC2Volume_graph_mem_gibbs hV hprob ρ hρ hHess (hf n) (hfc
      n)))

/-- The same graph-limit result as an actual Sobolev element with both
inclusion and derivative specified, rather than an abstract existence claim. -/
theorem exists_gibbsSobolev_of_volume_L2_graph_limit {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (f : ℕ → E → ℝ) (hf : ∀ n, ContDiff ℝ 2 (f n)) (hfc : ∀ n, HasCompactSupport (f n))
    (u : E →₂[volume] ℝ) (G : E →₂[volume] E)
    (hu : Tendsto (fun n => compactC2VolumeLp (f n) (hf n) (hfc n)) atTop (𝓝 u))
    (hG : Tendsto (fun n => compactC2VolumeGradientLp (f n) (hf n) (hfc n)) atTop (𝓝 G)) :
    ∃ v : gibbsSobolevGraph hV hprob,
      gibbsSobolevInclusion hV hprob v = volumeToGibbsL2 hV ρ hρ hHess u ∧
      gibbsSobolevDerivative hV hprob v = volumeToGibbsL2Vector hV ρ hρ hHess G := by
  refine ⟨⟨WithLp.toLp 2 (volumeToGibbsL2 hV ρ hρ hHess u,
    volumeToGibbsL2Vector hV ρ hρ hHess G),
    closedGibbsGradient_mem_of_volume_L2_graph_limit hV hprob ρ hρ hHess f hf hfc u G hu hG⟩, rfl,
      rfl⟩

end CutoffRigidity
