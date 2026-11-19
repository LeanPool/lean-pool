/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinGlobalContinuity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinGlobal
/-!
# Alternative Bakry Emery Langevin global continuity

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryLangevinPath_initial`, `bakryEmeryLangevinEndpoint_continuous`,
`bakryEmeryLangevinPath_measurable`, `bakryEmeryLangevinCorrectionOn_noise_congr`.
-/

@[expose] public section
open MeasureTheory Set Metric
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The Langevin state on the horizon `T` driven by the noise path `N`: the corrected trajectory
`bakryEmeryLangevinCorrectionOn` for the extended noise plus the extended noise itself. -/
def bakryEmeryLangevinStateOn (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : E) (T : ℝ) (hT : 0 ≤ T) (N : C(Icc 0 T, E)) (t : ℝ) : E :=
  bakryEmeryLangevinCorrectionOn W κ hκ hW hc
    (bkWeightedExtension T hT N) (bkWeightedExtension_continuous T hT N) z T hT t +
    bkWeightedExtension T hT N t

/-- The time-`T` endpoint of the Langevin state `bakryEmeryLangevinStateOn` started at `z` and
driven by `N`. -/
def bakryEmeryLangevinEndpoint (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : E) (T : ℝ) (hT : 0 ≤ T) (N : C(Icc 0 T, E)) : E :=
  bakryEmeryLangevinStateOn W κ hκ hW hc z T hT N T

lemma bakryEmeryLangevinStateOn_spec (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : E) (T : ℝ) (hT : 0 ≤ T) (N : C(Icc 0 T, E)) :
    Continuous (bakryEmeryLangevinStateOn W κ hκ hW hc z T hT N) ∧
    ∀ t ∈ Icc 0 T, bakryEmeryLangevinStateOn W κ hκ hW hc z T hT N t =
      z + bkWeightedExtension T hT N t + ∫ s in (0 : ℝ)..t,
        bakryEmeryLangevinDrift W (bakryEmeryLangevinStateOn W κ hκ hW hc z T hT N s) := by
  obtain ⟨hY, _, hI, _⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc
    (bkWeightedExtension T hT N) (bkWeightedExtension_continuous T hT N) z T hT
  refine ⟨hY.add (bkWeightedExtension_continuous T hT N), ?_⟩
  intro t ht
  change _ + bkWeightedExtension T hT N t = _
  rw [hI t ht]
  dsimp only [bakryEmeryLangevinStateOn]
  abel

lemma bakryEmeryLangevinStateOn_uniform_bound (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T) (M : ℝ) (hM : 0 ≤ M) :
    ∃ R : ℝ, ∀ (z : E) (N : C(Icc 0 T, E)), ‖z‖ ≤ M → ‖N‖ ≤ M →
      ∀ t ∈ Icc 0 T, bakryEmeryLangevinStateOn W κ hκ hW hc z T hT N t ∈ closedBall 0 R := by
  have hb : Continuous (bakryEmeryLangevinDrift W) := continuous_iff_continuousAt.mpr
    (fun x => (bakryEmeryLangevinDrift_contDiffAt W x hW.contDiffAt).continuousAt)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hb.continuousOn
  let A : ℝ := M^2 + (C^2/κ)*T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1+M, ?_⟩
  intro z N hz hN t ht
  let NN := bkWeightedExtension T hT N
  let Y := bakryEmeryLangevinCorrectionOn W κ hκ hW hc NN
    (bkWeightedExtension_continuous T hT N) z T hT
  have hnoise (s : ℝ) : ‖NN s‖ ≤ M := (N.norm_coe_le_norm _).trans hN
  obtain ⟨hY, hY0, _, hD⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc NN
    (bkWeightedExtension_continuous T hT N) z T hT
  have he := bakryEmeryLangevin_driven_energy_bound_uniform W κ hκ hW hc NN Y T hT
    hY.continuousOn hD C (fun s _ => hC (NN s) (by
      simpa only [mem_closedBall, dist_zero_right] using hnoise s)) t ht
  change Y 0 = z at hY0
  rw [hY0] at he
  have hzsq : ‖z‖^2 ≤ M^2 := by nlinarith [norm_nonneg z]
  have hea : ‖Y t‖^2 ≤ A := he.trans (by
    dsimp [A]
    exact add_le_add hzsq (mul_le_mul_of_nonneg_left ht.2 (div_nonneg (sq_nonneg C) hκ.le)))
  have hybound : ‖Y t‖ ≤ A+1 := by nlinarith [norm_nonneg (Y t), sq_nonneg A]
  change Y t+NN t ∈ closedBall 0 (A+1+M)
  simpa only [mem_closedBall, dist_zero_right] using
    (norm_add_le (Y t) (NN t)).trans (add_le_add hybound (hnoise t))

/-- The Langevin state on `[0, T]` started at `p.1` and driven by the noise path `p.2`, as a
continuous path. -/
def bakryEmeryLangevinPath (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T) (p : E × C(Icc 0 T, E)) : C(Icc 0 T, E) where
  toFun t := bakryEmeryLangevinStateOn W κ hκ hW hc p.1 T hT p.2 t
  continuous_toFun := (bakryEmeryLangevinStateOn_spec W κ hκ hW hc p.1 T hT p.2).1.comp
    continuous_subtype_val

/-- The selected measurable path solves the original state Volterra equation. -/
theorem bakryEmeryLangevinPath_equation (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T) (p : E × C(Icc 0 T, E)) (t : Icc 0 T) :
    bakryEmeryLangevinPath W κ hκ hW hc T hT p t =
      p.1 + p.2 t + ∫ s in (0 : ℝ)..(t : ℝ), bakryEmeryLangevinDrift W
        (bakryEmeryLangevinStateOn W κ hκ hW hc p.1 T hT p.2 s) := by
  have hh := (bakryEmeryLangevinStateOn_spec W κ hκ hW hc p.1 T hT p.2).2 t t.property
  simpa only [bakryEmeryLangevinPath, ContinuousMap.coe_mk, bkWeightedExtension,
    projIcc_of_mem hT t.property] using hh

theorem bakryEmeryLangevinPath_initial (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T) (p : E × C(Icc 0 T, E)) :
    bakryEmeryLangevinPath W κ hκ hW hc T hT p ⟨0, ⟨le_rfl, hT⟩⟩ =
      p.1 + p.2 ⟨0, ⟨le_rfl, hT⟩⟩ := by
  simpa using bakryEmeryLangevinPath_equation W κ hκ hW hc T hT p ⟨0, ⟨le_rfl, hT⟩⟩

lemma bakryEmeryLangevinPath_lipschitzOn_bounded (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T) (M : ℝ) (hM : 0 ≤ M) :
    ∃ L : ℝ≥0, LipschitzOnWith L (bakryEmeryLangevinPath W κ hκ hW hc T hT)
      {p : E × C(Icc 0 T, E) | ‖p.1‖ ≤ M ∧ ‖p.2‖ ≤ M} := by
  obtain ⟨R, hR⟩ := bakryEmeryLangevinStateOn_uniform_bound W κ hκ hW hc T hT M hM
  obtain ⟨K, hK⟩ := bakryEmeryLangevin_noise_stability_on_ball W hW R
  let L : ℝ≥0 := ⟨2*Real.exp ((K : ℝ)*T), by positivity⟩
  refine ⟨L, LipschitzOnWith.of_dist_le_mul (fun p hp q hq => ?_)⟩
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro t
  have hps := bakryEmeryLangevinStateOn_spec W κ hκ hW hc p.1 T hT p.2
  have hqs := bakryEmeryLangevinStateOn_spec W κ hκ hW hc q.1 T hT q.2
  have hest := hK 0
    (fun s => p.1+bkWeightedExtension T hT p.2 s)
    (fun s => q.1+bkWeightedExtension T hT q.2 s)
    (bakryEmeryLangevinStateOn W κ hκ hW hc p.1 T hT p.2)
    (bakryEmeryLangevinStateOn W κ hκ hW hc q.1 T hT q.2)
    T (dist p.1 q.1+dist p.2 q.2) hT (by positivity)
    hps.1.continuousOn hqs.1.continuousOn
    (hR p.1 p.2 hp.1 hp.2) (hR q.1 q.2 hq.1 hq.2)
    (by intro s hs; simpa using hps.2 s hs)
    (by intro s hs; simpa using hqs.2 s hs)
    (by
      intro s hs
      have hn := (p.2-q.2).norm_coe_le_norm (projIcc 0 T hT s)
      simp only [ContinuousMap.sub_apply] at hn
      have hh := norm_add_le (p.1-q.1)
        (bkWeightedExtension T hT p.2 s-bkWeightedExtension T hT q.2 s)
      rw [show p.1+bkWeightedExtension T hT p.2 s-(q.1+bkWeightedExtension T hT q.2 s) =
        (p.1-q.1)+(bkWeightedExtension T hT p.2 s-bkWeightedExtension T hT q.2 s) by abel]
      exact hh.trans (add_le_add (by rw [dist_eq_norm]) (by simpa [bkWeightedExtension,
                                                              dist_eq_norm] using hn)))
    t t.property
  change ‖bakryEmeryLangevinStateOn W κ hκ hW hc p.1 T hT p.2 t -
    bakryEmeryLangevinStateOn W κ hκ hW hc q.1 T hT q.2 t‖ ≤ _
  apply hest.trans
  have hpq : dist p.1 q.1+dist p.2 q.2 ≤ 2*dist p q := by
    rw [Prod.dist_eq]
    nlinarith [le_max_left (dist p.1 q.1) (dist p.2 q.2),
      le_max_right (dist p.1 q.1) (dist p.2 q.2)]
  change (dist p.1 q.1+dist p.2 q.2)*Real.exp ((K : ℝ)*T) ≤
    (2*Real.exp ((K : ℝ)*T))*dist p q
  nlinarith [mul_le_mul_of_nonneg_right hpq (Real.exp_nonneg ((K : ℝ)*T))]

theorem bakryEmeryLangevinPath_continuous (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T) :
    Continuous (bakryEmeryLangevinPath W κ hκ hW hc T hT) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let M : ℝ := max ‖p.1‖ ‖p.2‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨L, hL⟩ := bakryEmeryLangevinPath_lipschitzOn_bounded W κ hκ hW hc T hT M hM
  apply hL.continuousOn.continuousAt
  have hopen : IsOpen {q : E × C(Icc 0 T, E) | ‖q.1‖ < M ∧ ‖q.2‖ < M} :=
    (isOpen_lt continuous_fst.norm continuous_const).inter
      (isOpen_lt continuous_snd.norm continuous_const)
  have hp : p ∈ {q : E × C(Icc 0 T, E) | ‖q.1‖ < M ∧ ‖q.2‖ < M} := by
    dsimp [M]
    constructor <;> linarith [le_max_left ‖p.1‖ ‖p.2‖, le_max_right ‖p.1‖ ‖p.2‖]
  exact Filter.mem_of_superset (hopen.mem_nhds hp) (fun q hq => ⟨hq.1.le, hq.2.le⟩)

theorem bakryEmeryLangevinEndpoint_continuous (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun p : E × C(Icc 0 T, E) =>
      bakryEmeryLangevinEndpoint W κ hκ hW hc p.1 T hT p.2) := by
  have he : Continuous (fun f : C(Icc 0 T, E) => f ⟨T, ⟨hT, le_rfl⟩⟩) :=
    continuous_eval_const _
  simpa only [Function.comp_def, bakryEmeryLangevinPath, bakryEmeryLangevinEndpoint,
    ContinuousMap.coe_mk] using he.comp (bakryEmeryLangevinPath_continuous W κ hκ hW hc T hT)

theorem bakryEmeryLangevinPath_measurable [MeasurableSpace E] [BorelSpace E]
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (T : ℝ) (hT : 0 ≤ T)
    [MeasurableSpace C(Icc 0 T, E)] [BorelSpace C(Icc 0 T, E)] :
    Measurable (bakryEmeryLangevinPath W κ hκ hW hc T hT) :=
  (bakryEmeryLangevinPath_continuous W κ hκ hW hc T hT).measurable

/-- The chosen corrected flow depends only on its driving path on the chosen
finite horizon, including its endpoints. -/
theorem bakryEmeryLangevinCorrectionOn_noise_congr (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N M : ℝ → E) (hN : Continuous N) (hM : Continuous M)
    (z : E) (T : ℝ) (hT : 0 ≤ T) (hNM : EqOn N M (Icc 0 T)) :
    EqOn (bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z T hT)
      (bakryEmeryLangevinCorrectionOn W κ hκ hW hc M hM z T hT) (Icc 0 T) := by
  obtain ⟨hX, hX0, _, hXD⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc N hN z T hT
  obtain ⟨hY, hY0, _, hYD⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc M hM z T hT
  apply bakryEmeryLangevin_pathwise_unique W κ (hW.differentiable (by norm_num)) hc M
    _ _ T hT hX.continuousOn hY.continuousOn
  · intro t ht
    rw [← hNM ⟨ht.1.le, ht.2.le⟩]
    exact hXD t ht
  · exact hYD
  · rw [hX0, hY0]

end
end GinibrePoincare
