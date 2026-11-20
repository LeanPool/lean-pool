/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianEndpoint.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianNoise
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryEndpointApproximation
public import LeanPool.GinibrePoincare.Analysis.EntropyLimitStability
/-!
# Alternative Bakry Emery Brownian endpoint

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryBrownianEndpointLaw_probability`,
`bakryEmeryBrownianEndpointLaw_square_lsi`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- The time-`T` endpoint of the Langevin dynamics for `W` started at `z` and driven by `√2`
times the Brownian noise path built from `B` at the sample `ω`. -/
def bakryEmeryBrownianEndpoint
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (B : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) : EuclideanSpace ℝ ι :=
  bakryEmeryLangevinEndpoint W κ hκ hW hc z T hT (Real.sqrt 2 • bakryEmeryBrownianNoisePath T B ω)

/-- The endpoint of the `n + 1`-step discretised Langevin scheme for `W` started at `z` with
step `T / (n + 1)`, driven by the normalised increments of the Brownian noise `B` at `ω`. -/
def bakryEmeryBrownianFiniteEndpoint
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 < T)
    (B : ι → ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ ι :=
  bakryEmeryFiniteEndpoint W κ hκ hW hc z (n+1) (T/(n+1 : ℝ)) (by positivity)
    (WithLp.toLp 2 (fun p : Fin (n+1) × ι =>
      (bakryEmeryBrownianNoiseReal B ω (((p.1.val+1 : ℕ) : ℝ)*(T/(n+1 : ℝ))) p.2-
       bakryEmeryBrownianNoiseReal B ω ((p.1.val : ℝ)*(T/(n+1 : ℝ))) p.2)/Real.sqrt (T/(n+1 : ℝ))))

omit [DecidableEq ι] in
theorem bakryEmeryBrownianEndpoint_measurable
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (bakryEmeryBrownianEndpoint W κ hκ hW hc z T hT B) := by
  classical
  let : MeasurableSpace C(Icc 0 T, EuclideanSpace ℝ ι) := borel _
  let : BorelSpace C(Icc 0 T, EuclideanSpace ℝ ι) := ⟨rfl⟩
  have hg : Continuous (fun N : C(Icc 0 T, EuclideanSpace ℝ ι) => (z, Real.sqrt 2 • N)) :=
    continuous_const.prodMk (continuous_id.const_smul (Real.sqrt 2))
  have he := (bakryEmeryLangevinEndpoint_continuous W κ hκ hW hc T hT).comp hg
  change Measurable (fun ω => bakryEmeryLangevinEndpoint W κ hκ hW hc z T hT
    (Real.sqrt 2 • bakryEmeryBrownianNoisePath T B ω))
  exact he.measurable.comp (bakryEmeryBrownianNoisePath_measurable T hT B P hB)

omit [DecidableEq ι] in
theorem bakryEmeryBrownianFiniteEndpoint_tendsto
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 < T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => bakryEmeryBrownianFiniteEndpoint W κ hκ hW hc z T hT B n ω)
      atTop (nhds (bakryEmeryBrownianEndpoint W κ hκ hW hc z T hT.le B ω)) := by
  classical
  filter_upwards [bakryEmeryBrownianNoiseReal_actual B P hB,
    bakryEmeryBrownianNoisePath_actual T B P hB] with ω hω hpath
  have hp : bakryEmeryBrownianNoisePath T B ω =
      (⟨fun t : Icc 0 T => bakryEmeryBrownianNoiseReal B ω t.val,
        hω.1.comp continuous_subtype_val⟩ : C(Icc 0 T, EuclideanSpace ℝ ι)) :=
    ContinuousMap.ext hpath
  unfold bakryEmeryBrownianEndpoint
  rw [hp]
  exact bakryEmeryFiniteEndpoint_sampled_tendsto W κ hκ hW hc z T hT
    (bakryEmeryBrownianNoiseReal B ω) hω.1.continuousOn hω.2

omit [DecidableEq ι] in
/-- The sampled actual Brownian-driven state has exactly the concrete finite
Gaussian endpoint law whose LSI was proved above. -/
theorem bakryEmeryBrownianFiniteEndpoint_hasLaw
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 < T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (n : ℕ) :
    HasLaw (bakryEmeryBrownianFiniteEndpoint W κ hκ hW hc z T hT B n)
      (bakryEmeryFiniteEndpointLaw W κ hκ hW hc z (n+1) (T/(n+1 : ℝ)) (by positivity)) P := by
  classical
  let h : ℝ≥0 := ⟨T/(n+1 : ℝ), by positivity⟩
  have hh : h ≠ 0 := by
    apply ne_of_gt
    change 0 < T/(n+1 : ℝ)
    positivity
  have htime (j : ℕ) : ((j : ℝ)*(h : ℝ)).toNNReal=(j : ℝ≥0)*h := by
    apply Subtype.ext
    change max ((j : ℝ)*(h : ℝ)) 0 = (j : ℝ)*(h : ℝ)
    exact max_eq_left (by positivity)
  have hraw := bakryEmeryBrownianGrid_coordinates_hasLaw B P
    (fun i => (hB i).toIsPreBrownianReal) hind h hh (n+1)
  let X := fun ω (p : Fin (n+1) × ι) =>
    (bakryEmeryBrownianNoiseReal B ω (((p.1.val+1 : ℕ) : ℝ)*(h : ℝ)) p.2-
     bakryEmeryBrownianNoiseReal B ω ((p.1.val : ℝ)*(h : ℝ)) p.2)/Real.sqrt (h : ℝ)
  have hX : HasLaw X (Measure.pi (fun _ : Fin (n+1) × ι => gaussianReal 0 1)) P := by
    convert hraw using 1
    funext ω p
    simp only [X, bakryEmeryBrownianNoiseReal, htime]
  let F := fun x : (Fin (n+1) × ι) → ℝ =>
    bakryEmeryFiniteEndpoint W κ hκ hW hc z (n+1) (h : ℝ) (by positivity) (WithLp.toLp 2 x)
  have hF : Measurable F :=
    ((bakryEmeryFiniteEndpoint_lipschitz W κ hκ hW hc z (n+1) (h : ℝ) (by
        positivity)).continuous.comp
      (PiLp.continuous_toLp 2 _)).measurable
  have hdet : HasLaw F (bakryEmeryFiniteEndpointLaw W κ hκ hW hc z (n+1) (h : ℝ) (by positivity))
      (Measure.pi (fun _ : Fin (n+1) × ι => gaussianReal 0 1)) := ⟨hF.aemeasurable, rfl⟩
  have hout := HasLaw.comp hdet hX
  exact hout

omit [DecidableEq ι] in
/-- The actual Brownian Langevin endpoint satisfies the uniform sharp entropy
bound, obtained from proved finite Gaussian laws and actual solution convergence. -/
theorem bakryEmeryBrownianEndpoint_square_lsi [Nonempty ι]
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 < T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hfL : LipschitzWith L f) (C : ℝ) (hfC : ∀ y, |f y| ≤ C) :
    squareEntropy P (fun ω => f (bakryEmeryBrownianEndpoint W κ hκ hW hc z T hT.le B ω)) ≤
      (2/κ)*∫ ω, ‖gradient f (bakryEmeryBrownianEndpoint W κ hκ hW hc z T hT.le B ω)‖^2 ∂P := by
  classical
  let X := bakryEmeryBrownianFiniteEndpoint W κ hκ hW hc z T hT B
  let Y := bakryEmeryBrownianEndpoint W κ hκ hW hc z T hT.le B
  have hLaw (n : ℕ) := bakryEmeryBrownianFiniteEndpoint_hasLaw W κ hκ hW hc z T hT B P hB hind n
  have hXm (n : ℕ) : Measurable (X n) := aemeasurable_iff_measurable.mp (hLaw n).aemeasurable
  have hYm : Measurable Y := bakryEmeryBrownianEndpoint_measurable W κ hκ hW hc z T hT.le B P hB
  have hXY := bakryEmeryBrownianFiniteEndpoint_tendsto W κ hκ hW hc z T hT B P hB
  have hgrad : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgn (x : EuclideanSpace ℝ ι) : ‖gradient f x‖ ≤ (L : ℝ) := by
    have hn : ‖gradient f x‖=‖fderiv ℝ f x‖ := by simp only [gradient, LinearIsometryEquiv.norm_map]
    rw [hn]
    exact norm_fderiv_le_of_lipschitz ℝ hfL
  have hsq (x : EuclideanSpace ℝ ι) : f x^2 ∈ Icc 0 (C^2) := by
    refine ⟨sq_nonneg _,?_⟩
    nlinarith [hfC x, abs_nonneg (f x), sq_abs (f x)]
  have hmass : Tendsto (fun n => ∫ ω, f (X n ω)^2 ∂P) atTop (nhds (∫ ω, f (Y ω)^2 ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C^2)
      (Eventually.of_forall (fun n => ((hf.continuous.measurable.comp (hXm n)).pow_const
          2).aestronglyMeasurable))
      (Eventually.of_forall (fun n => ae_of_all _ (fun ω => ?_))) (integrable_const _) ?_
    · filter_upwards [hXY] with ω hω
      exact (hf.continuous.continuousAt.tendsto.comp hω).pow 2
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (hsq _).2
  have henergy : Tendsto (fun n => ∫ ω, ‖gradient f (X n ω)‖^2 ∂P) atTop
      (nhds (∫ ω, ‖gradient f (Y ω)‖^2 ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (L : ℝ)^2)
      (Eventually.of_forall (fun n =>
        ((hgrad.norm.pow 2).measurable.comp (hXm n)).aestronglyMeasurable))
      (Eventually.of_forall (fun n => ae_of_all _ (fun ω => ?_))) (integrable_const _) ?_
    · filter_upwards [hXY] with ω hω
      exact (hgrad.continuousAt.tendsto.comp hω).norm.pow 2
    · change ‖‖gradient f (X n ω)‖^2‖ ≤ (L : ℝ)^2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hgn (X n ω), norm_nonneg (gradient f (X n ω)), L.coe_nonneg]
  have hineq (n : ℕ) : squareEntropy P (fun ω => f (X n ω)) ≤
      (2/κ)*∫ ω, ‖gradient f (X n ω)‖^2 ∂P := by
    have hsqmom := (hLaw n).integral_comp (hf.continuous.pow 2).aestronglyMeasurable
    have hlogmom := (hLaw n).integral_comp (continuous_square_mul_log
        hf.continuous).aestronglyMeasurable
    have hgmom := (hLaw n).integral_comp (hgrad.norm.pow 2).aestronglyMeasurable
    have hEnt := squareEntropy_eq_of_moments P
      (bakryEmeryFiniteEndpointLaw W κ hκ hW hc z (n+1) (T/(n+1 : ℝ)) (by positivity))
      (fun ω => f (X n ω)) f (by simpa only [Function.comp_def, Pi.pow_apply] using hsqmom)
      (by simpa only [Function.comp_def, Pi.pow_apply] using hlogmom)
    rw [hEnt]
    have hmom : (∫ ω, ‖gradient f (X n ω)‖^2 ∂P)=
      ∫ y, ‖gradient f y‖^2 ∂bakryEmeryFiniteEndpointLaw W κ hκ hW hc z (n+1) (T/(n+1 : ℝ)) (by
          positivity) := by
      simpa only [Function.comp_def, Pi.pow_apply] using hgmom
    rw [hmom]
    exact bakryEmeryFiniteEndpointLaw_uniform_square_lsi W κ hκ hW hc z (n+1) (by omega)
      (T/(n+1 : ℝ)) (by positivity) f hf hfL C hfC
  exact (squareEntropy_le_of_ae_tendsto P (fun n ω => f (X n ω)) (fun ω => f (Y ω))
    (fun n => (2/κ)*∫ ω, ‖gradient f (X n ω)‖^2 ∂P)
    ((2/κ)*∫ ω, ‖gradient f (Y ω)‖^2 ∂P)
    (fun n => (hf.continuous.measurable.comp (hXm n)).aestronglyMeasurable)
    (hf.continuous.measurable.comp hYm).aestronglyMeasurable
    (fun n => integrable_mul_log_of_bounded_nonneg P _
      ((hf.continuous.measurable.comp (hXm n)).pow_const 2) (C^2) (fun ω => hsq _))
    (by filter_upwards [hXY] with ω hω; exact hf.continuous.continuousAt.tendsto.comp hω)
    hmass (henergy.const_mul (2/κ)) hineq).2

/-- Actual law of the constructed Brownian Langevin state. -/
def bakryEmeryBrownianEndpointLaw
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Measure (EuclideanSpace ℝ ι) :=
  P.map (bakryEmeryBrownianEndpoint W κ hκ hW hc z T hT B)

omit [DecidableEq ι] in
theorem bakryEmeryBrownianEndpointLaw_probability
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (bakryEmeryBrownianEndpointLaw W κ hκ hW hc z T hT B P) := by
  classical
  unfold bakryEmeryBrownianEndpointLaw
  infer_instance

omit [DecidableEq ι] in
/-- The actual Brownian endpoint probability law satisfies the sharp uniform
Bakry–Émery square LSI, with the actual Euclidean gradient in its energy. -/
theorem bakryEmeryBrownianEndpointLaw_square_lsi [Nonempty ι]
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 < T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hfL : LipschitzWith L f) (C : ℝ) (hfC : ∀ y, |f y| ≤ C) :
    squareEntropy (bakryEmeryBrownianEndpointLaw W κ hκ hW hc z T hT.le B P) f ≤
      (2/κ)*∫ x, ‖gradient f x‖^2 ∂bakryEmeryBrownianEndpointLaw W κ hκ hW hc z T hT.le B P := by
  classical
  have hm := bakryEmeryBrownianEndpoint_measurable W κ hκ hW hc z T hT.le B P hB
  have hgrad : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  unfold bakryEmeryBrownianEndpointLaw
  rw [squareEntropy_map _ _ hm.aemeasurable f
    (hf.continuous.pow 2).aestronglyMeasurable
    (continuous_square_mul_log hf.continuous).aestronglyMeasurable,
    integral_map hm.aemeasurable
      (show AEStronglyMeasurable (fun x => ‖gradient f x‖^2) _ from (hgrad.norm.pow
          2).aestronglyMeasurable)]
  exact bakryEmeryBrownianEndpoint_square_lsi W κ hκ hW hc z T hT B P hB hind f hf hfL C hfC

end
end GinibrePoincare
