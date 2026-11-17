/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.MaximumComparison
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Coercivity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.SecondOrder.Difference

/-!
# The C^{1,1} estimate for moment-map potentials

If the gradient of a convex Lipschitz potential `u` with `∫ e^{-u} = 1` pushes `e^{-u} dx` forward
to a law with density
`e^{-V}` on a compact convex body, with `V` κ-strongly convex, then `∇u` is `16/κ`-Lipschitz
(maximum principle for penalized second differences). The exact centered-difference
coefficient `4/κ` is exported for the actual weak Hessian regularity consumer. The gradient
interface uses `16/κ` with the stated source hypotheses.
The `_on_range` variants assume `V − (κ/2)‖·‖²` convex only on a set containing every gradient value
(for instance the interior of the body); the maximum-principle argument evaluates it nowhere else.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma exists_moment_bumps (n : ℕ) :
    ∃ φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)),
      Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun k =>
    ContDiffBump.mk
      (1 / (2 * ((k : ℝ) + 1)))
      (1 / ((k : ℝ) + 1))
      (by positivity)
      (by
        have hk : 0 < (k : ℝ) + 1 := by positivity
        apply (div_lt_div_iff₀ (by positivity) hk).2
        nlinarith)
  refine ⟨φ, ?_⟩
  have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro a
    obtain ⟨j, hj⟩ := exists_nat_gt a
    filter_upwards [eventually_ge_atTop j] with k hk
    have hk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  change Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hnat

private lemma moment_mollification_contDiff_and_close
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ 2
        (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧
      ∀ x, |convolution (φ.normed volume) u
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u x| ≤ (L : ℝ) * φ.rOut := by
  constructor
  · exact HasCompactSupport.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      φ.hasCompactSupport_normed φ.contDiff_normed hu.continuous.locallyIntegrable
  · intro x
    rw [← Real.dist_eq]
    apply ContDiffBump.dist_normed_convolution_le hu.continuous.aestronglyMeasurable
    intro y hy
    exact (hu.dist_le_mul y x).trans
      (mul_le_mul_of_nonneg_left (le_of_lt hy) L.coe_nonneg)

private lemma moment_mollification_tendstoLocallyUniformly
    {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Continuous F)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    TendstoLocallyUniformly
      (fun k => convolution ((φ k).normed volume) F
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) F atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have hc :
      Tendsto
        (fun i : ℕ × EuclideanSpace ℝ (Fin n) =>
          convolution ((φ i.1).normed volume) F
            (ContinuousLinearMap.lsmul ℝ ℝ) volume i.2)
        (atTop ×ˢ 𝓝 x) (𝓝 (F x)) :=
    ContDiffBump.convolution_tendsto_right
      (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hF.aestronglyMeasurable)
      ((hF.tendsto x).comp tendsto_snd)
      tendsto_snd
  exact (((hF.tendsto x).comp tendsto_snd).prodMk_nhds hc).mono_right
    (nhds_le_uniformity (F x))

/-- The moment-map centered-difference estimate with its exact `4/κ` coefficient, when
`V − (κ/2)‖·‖²` is convex only on a set `Ω` containing every gradient value `∇u x` (for instance
`Ω = interior K`). -/
theorem secondDifference_le_of_map_gradient_on_range {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hstrong : ConvexOn ℝ Ω (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hΩ : ∀ x, gradient u x ∈ Ω)
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    ∀ x h : EuclideanSpace ℝ (Fin n),
      u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 := by
  classical
  let F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => -u x + V (gradient u x)
  have hgrad : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hC1.continuous_fderiv (by norm_num))
  have hF : Continuous F := hu.continuous.neg.add (hV.continuous.comp hgrad)
  have hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
        volume (subgradientImage u G) =
          ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)) := by
    intro G hG
    exact volume_subgradientImage_eq_lintegral_of_isOpen
      hu hconv hnorm hK.isClosed hKc hV.continuous.measurable hmap hG
  obtain ⟨φ, hφ⟩ := exists_moment_bumps n
  let uk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
    convolution ((φ k).normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
    convolution ((φ k).normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let δ : ℕ → ℝ := fun k => (L : ℝ) * (φ k).rOut
  have huk : ∀ k, ContDiff ℝ 2 (uk k) := fun k =>
    (moment_mollification_contDiff_and_close hu (φ k)).1
  have hclose : ∀ k x, |uk k x - u x| ≤ δ k := fun k =>
    (moment_mollification_contDiff_and_close hu (φ k)).2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using hφ.const_mul (L : ℝ)
  have hFk : TendstoLocallyUniformly Fk F atTop :=
    moment_mollification_tendstoLocallyUniformly hF φ hφ
  have hposlog : ∀ k x,
      (hessianMatrix (uk k) x).PosDef ∧
        Fk k x ≤ Real.log (hessianMatrix (uk k) x).det := by
    intro k x
    apply posDef_and_convolution_le_log_det_hessianMatrix hconv hF
    filter_upwards
      [ae_exists_posDef_det_eq hconv (Real.continuous_exp.comp hF)
        (fun y => Real.exp_pos (F y)) hMA] with y hy
    rcases hy with ⟨B, hB, hPD, hdet, hexp⟩
    refine ⟨B, hB, hPD, ?_, hexp⟩
    rw [hdet, Function.comp_apply, Real.log_exp]
  have hint : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  obtain ⟨⟨xm, hm⟩, hcoer⟩ :=
    exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      volume hconv hint
  have hgrad_bound (x : EuclideanSpace ℝ (Fin n)) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hu)
  obtain ⟨C, hCball⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ))
      ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_id).continuousOn
  have hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C := by
    intro x
    have hx : gradient u x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ) :=
      mem_closedBall_zero_iff.mpr (hgrad_bound x)
    simpa only [id_eq, Real.norm_eq_abs] using hCball (gradient u x) hx
  have hsd : ∀ x h : EuclideanSpace ℝ (Fin n),
      u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 := by
    intro x h
    have hmax : ∀ η > 0, ∃ x₀,
        (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
          u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
        V (gradient u (x₀ + h)) - u (x₀ + h) +
          (V (gradient u (x₀ - h)) - u (x₀ - h)) -
          2 * (V (gradient u x₀) - u x₀) ≤ η * (n : ℝ) := by
      intro η hη
      simpa only [F, neg_add_eq_sub] using
        exists_penalized_maximum_with_comparison hconv hu hcoer hF hMA huk hδ
          hclose hFk (fun k y => (hposlog k y).1) (fun k y => (hposlog k y).2) h hη
    simpa only [div_mul_eq_mul_div] using
      secondDifference_le_of_penalized_maxima_on_range hconv
        (hC1.differentiable (by norm_num)) (hV.differentiable (by norm_num))
        hκ hstrong hΩ hC hm n h hmax x
  exact hsd

/--
Export the existing moment-map centered-difference estimate with its exact 4/kappa coefficient. -/
theorem secondDifference_le_of_map_gradient {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hmap :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    ∀ x h : EuclideanSpace ℝ (Fin n), u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 :=
  secondDifference_le_of_map_gradient_on_range hu hconv hnorm hK hKc hV hκ hstrong
    (fun x => mem_univ (gradient u x)) hmap hC1

/-- **`C^{1,1}` regularity of the moment potential, convexity on the gradient range**: as
`lipschitzWith_gradient_of_map_gradient`, with `V − (κ/2)‖·‖²` convex only on a set `Ω` containing
every gradient value `∇u x` (for instance `Ω = interior K`). Then `∇u` is `16/κ`-Lipschitz. -/
theorem lipschitzWith_gradient_of_map_gradient_on_range {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hstrong : ConvexOn ℝ Ω (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hΩ : ∀ x, gradient u x ∈ Ω)
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) := by
  have hsd := secondDifference_le_of_map_gradient_on_range hu hconv hnorm hK hKc hV hκ
    hstrong hΩ hmap hC1
  have hLip :=
    lipschitzWith_gradient_of_second_difference_le hconv
      (hC1.differentiable (by norm_num)) (show 0 ≤ 4 / κ by positivity) hsd
  have hconstant : 4 * (4 / κ) = 16 / κ := by ring
  rw [hconstant] at hLip
  exact hLip

/-- **`C^{1,1}` regularity of the moment potential**: if the `C¹` convex Lipschitz `u` with
`∫ e^{-u} = 1` pushes `e^{-u} dx` forward by `∇u` to `1_K e^{-V} dx` with `K` compact convex and `V
∈ C¹` such
that `V − (κ/2)‖·‖²` is convex, then `∇u` is `16/κ`-Lipschitz. -/
theorem lipschitzWith_gradient_of_map_gradient {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hmap :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) : LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) :=
  lipschitzWith_gradient_of_map_gradient_on_range hu hconv hnorm hK hKc hV hκ hstrong
    (fun x => mem_univ (gradient u x)) hmap hC1

end FunctionalInequalities.Analysis
