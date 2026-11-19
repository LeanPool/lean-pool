/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinGlobal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryVolterraContraction
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinContraction
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinNoiseStability
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinEnergyUniform

/-! # Global strongly convex Langevin flow
The finite-horizon construction uses a weighted Volterra contraction. A ball
Lipschitz extension is then removed by a first-exit argument using the actual
strong-convexity energy estimate. Pathwise uniqueness glues the finite horizons
into one trajectory on all nonnegative times. -/

@[expose] public section

open MeasureTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The extension of a path `X` on `[0, T]` to all of `ℝ`, constant outside `[0, T]`, via the
projection `projIcc 0 T`. -/
def bkWeightedExtension (T : ℝ) (hT : 0 ≤ T) (X : C(Icc 0 T, E)) (s : ℝ) : E :=
  X (projIcc 0 T hT s)

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma bkWeightedExtension_continuous (T : ℝ) (hT : 0 ≤ T) (X : C(Icc 0 T, E)) :
    Continuous (bkWeightedExtension T hT X) :=
  X.continuous.comp continuous_projIcc

/-- The exponentially weighted Volterra map
`X ↦ (t ↦ e^(-L t) • (z + ∫₀ᵗ g (e^(L s) • X̂ s + N s) ds))` on paths over `[0, T]`, where `X̂`
is `bkWeightedExtension` of `X`. -/
def bkWeightedVolterra (g : E → E) (hg : Continuous g) (N : ℝ → E)
    (hN : Continuous N) (z : E) (T : ℝ) (hT : 0 ≤ T) (L : ℝ)
    (X : C(Icc 0 T, E)) : C(Icc 0 T, E) where
  toFun t := Real.exp (-L * t) • (z + ∫ s in (0 : ℝ)..(t : ℝ),
    g (Real.exp (L*s) • bkWeightedExtension T hT X s + N s))
  continuous_toFun := by
    have hi : Continuous (fun s => g (Real.exp (L*s) • bkWeightedExtension T hT X s + N s)) :=
      hg.comp (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        (bkWeightedExtension_continuous T hT X)).add hN)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
      (continuous_const.add ((intervalIntegral.differentiable_integral_of_continuous
          hi).continuous.comp
        continuous_subtype_val))

lemma bkWeightedVolterra_lipschitz (g : E → E) {K : ℝ≥0} (hg : LipschitzWith K g)
    (N : ℝ → E) (hN : Continuous N) (z : E) (T : ℝ) (hT : 0 ≤ T)
    (L : ℝ) (hL : 0 < L) :
    LipschitzWith (⟨(K : ℝ)/L, div_nonneg K.coe_nonneg hL.le⟩ : ℝ≥0)
      (bkWeightedVolterra g hg.continuous N hN z T hT L) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg (div_nonneg K.coe_nonneg hL.le)
    (dist_nonneg))).mpr
  intro t
  change ‖Real.exp (-L*(t : ℝ)) • (z + ∫ s in (0 : ℝ)..(t : ℝ),
      g (Real.exp (L*s) • bkWeightedExtension T hT X s + N s)) -
    Real.exp (-L*(t : ℝ)) • (z + ∫ s in (0 : ℝ)..(t : ℝ),
      g (Real.exp (L*s) • bkWeightedExtension T hT Y s + N s))‖ ≤ _
  rw [← smul_sub, add_sub_add_left_eq_sub]
  have hc (Z : C(Icc 0 T, E)) : Continuous (fun s =>
      g (Real.exp (L*s) • bkWeightedExtension T hT Z s + N s)) :=
    hg.continuous.comp (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (bkWeightedExtension_continuous T hT Z)).add hN)
  rw [← intervalIntegral.integral_sub ((hc X).intervalIntegrable _ _)
    ((hc Y).intervalIntegrable _ _)]
  apply bakryEmeryVolterra_weighted_contraction g hg L hL t t.property.1
    N (bkWeightedExtension T hT X) (bkWeightedExtension T hT Y) (dist X Y) dist_nonneg
  intro s hs
  simpa [bkWeightedExtension, dist_eq_norm] using
    (X-Y).norm_coe_le_norm (projIcc 0 T hT s)

/-- Genuine finite-horizon existence for arbitrary globally Lipschitz drift and
continuous additive driving path, constructed by a weighted Banach fixed point. -/
theorem bakryEmeryVolterra_globalLip_exists (g : E → E) {K : ℝ≥0}
    (hg : LipschitzWith K g) (N : ℝ → E) (hN : Continuous N)
    (z : E) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → E, Continuous Y ∧ Y 0 = z ∧
      (∀ t ∈ Icc 0 T, Y t = z + ∫ s in (0 : ℝ)..t, g (Y s + N s)) ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt Y (g (Y t + N t)) t) := by
  let L : ℝ := (K : ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  let q : ℝ≥0 := ⟨(K : ℝ)/L, div_nonneg K.coe_nonneg hL.le⟩
  let F := bkWeightedVolterra g hg.continuous N hN z T hT L
  have hF : ContractingWith q F := by
    constructor
    · change (K : ℝ)/L < 1
      rw [div_lt_one hL]
      dsimp [L]; linarith
    · exact bkWeightedVolterra_lipschitz g hg N hN z T hT L hL
  let X : C(Icc 0 T, E) := hF.fixedPoint F
  have hx : F X = X := hF.fixedPoint_isFixedPt
  let v : ℝ → E := fun s => g (Real.exp (L*s) • bkWeightedExtension T hT X s + N s)
  have hv : Continuous v := hg.continuous.comp
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (bkWeightedExtension_continuous T hT X)).add hN)
  let Y : ℝ → E := fun t => z + ∫ s in (0 : ℝ)..t, v s
  have hy : Continuous Y := continuous_const.add
    (intervalIntegral.differentiable_integral_of_continuous hv).continuous
  have hrel (s : ℝ) (hs : s ∈ Icc 0 T) :
      Real.exp (L*s) • bkWeightedExtension T hT X s = Y s := by
    have he := congrArg (fun A : C(Icc 0 T, E) => A ⟨s, hs⟩) hx
    change Real.exp (-L*s) • Y s = X ⟨s, hs⟩ at he
    rw [bkWeightedExtension, projIcc_of_mem hT hs, ← he, smul_smul]
    have hc : Real.exp (L*s)*Real.exp (-L*s) = 1 := by
      rw [← Real.exp_add]; convert Real.exp_zero using 1; ring_nf
    rw [hc, one_smul]
  refine ⟨Y, hy, ?_, ?_, ?_⟩
  · simp [Y]
  · intro t ht
    change z + (∫ s in (0 : ℝ)..t, v s) = _
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change g (Real.exp (L*s) • bkWeightedExtension T hT X s + N s) = _
    rw [hrel s ⟨hs.1, hs.2.trans ht.2⟩]
  · intro t ht
    have hd := intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
    have hd' := hd.const_add z
    change HasDerivAt Y (v t) t at hd'
    simpa only [v, hrel t ⟨ht.1.le, ht.2.le⟩] using hd'

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The first exit of a continuous path from a ball, without differentiability assumptions. -/
lemma bkContinuous_first_exit (X : ℝ → E) (hX : Continuous X)
    (T R : ℝ) (_ : 0 ≤ T) (h0 : ‖X 0‖ < R)
    (hout : ∃ t ∈ Icc 0 T, R ≤ ‖X t‖) :
    ∃ a ∈ Icc 0 T, 0 < a ∧ R ≤ ‖X a‖ ∧
      ∀ s ∈ Ico 0 a, ‖X s‖ < R := by
  let S : Set ℝ := Icc 0 T ∩ {t | R ≤ ‖X t‖}
  have hclosed : IsClosed {t : ℝ | R ≤ ‖X t‖} :=
    isClosed_le continuous_const hX.norm
  have hcomp : IsCompact S := isCompact_Icc.inter_right hclosed
  have hne : S.Nonempty := by
    obtain ⟨t, ht, h⟩ := hout
    exact ⟨t, ht, h⟩
  obtain ⟨a, ha⟩ := hcomp.exists_isLeast hne
  have ha0 : 0 < a := by
    have hn : a ≠ 0 := by intro he; have := ha.1.2; rw [he] at this; exact (not_le_of_gt h0) this
    exact lt_of_le_of_ne ha.1.1.1 (Ne.symm hn)
  refine ⟨a, ha.1.1, ha0, ha.1.2, ?_⟩
  intro s hs
  by_contra hh
  have hmem : s ∈ S := ⟨⟨hs.1, hs.2.le.trans ha.1.1.2⟩, le_of_not_gt hh⟩
  exact (not_le_of_gt hs.2) (ha.2 hmem)

end Banach
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
/-- Actual finite-horizon Langevin construction for a C² strongly convex
potential and arbitrary continuous additive noise. No solution is assumed. -/
theorem bakryEmeryLangevin_global_exists_on (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N : ℝ → E) (hN : Continuous N) (z : E) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → E, Continuous Y ∧ Y 0 = z ∧
      (∀ t ∈ Icc 0 T, Y t = z + ∫ s in (0 : ℝ)..t,
        bakryEmeryLangevinDrift W (Y s + N s)) ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt Y (bakryEmeryLangevinDrift W (Y t + N t)) t) := by
  have hb : Continuous (bakryEmeryLangevinDrift W) := continuous_iff_continuousAt.mpr
    (fun x => (bakryEmeryLangevinDrift_contDiffAt W x hW.contDiffAt).continuousAt)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hN.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    (hb.comp hN).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT⟩)
  let A : ℝ := ‖z‖^2 + (C^2/κ)*T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let R : ℝ := ‖z‖ + A + B + 2
  obtain ⟨K, hK⟩ := bakryEmeryLangevinDrift_closedBall_lipschitz W hW R
  obtain ⟨g, hg, heq⟩ := hK.extend_finite_dimension
  obtain ⟨Y, hY, hY0, hI, hD⟩ := bakryEmeryVolterra_globalLip_exists g hg N hN z T hT
  have hinside : ∀ t ∈ Icc 0 T, ‖Y t+N t‖ < R := by
    by_contra hh
    have hout : ∃ t ∈ Icc 0 T, R ≤ ‖Y t + N t‖ := by
      push Not at hh
      exact hh
    have hz : ‖Y 0+N 0‖ < R := by
      rw [hY0]
      have hn := (norm_add_le z (N 0)).trans (add_le_add le_rfl (hB 0 ⟨le_rfl, hT⟩))
      dsimp [R]; linarith
    obtain ⟨a, ha, ha0, haR, hbefore⟩ := bkContinuous_first_exit (fun t => Y t+N t)
      (hY.add hN) T R hT hz hout
    have hd : ∀ s ∈ Ioo 0 a,
        HasDerivAt Y (bakryEmeryLangevinDrift W (Y s+N s)) s := by
      intro s hs
      have hm : Y s+N s ∈ Metric.closedBall 0 R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (hbefore s ⟨hs.1.le, hs.2⟩).le
      rw [heq hm]
      exact hD s ⟨hs.1, hs.2.trans_le ha.2⟩
    have he := bakryEmeryLangevin_driven_energy_bound_uniform W κ hκ hW hc N Y a ha.1
      hY.continuousOn hd C (fun s hs => hC s ⟨hs.1, hs.2.trans ha.2⟩) a ⟨ha.1, le_rfl⟩
    rw [hY0] at he
    have hea : ‖Y a‖^2 ≤ A := he.trans (by
      dsimp [A]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ha.2 (div_nonneg (sq_nonneg C) hκ.le)))
    have hybound : ‖Y a‖ < A+1 := by nlinarith [norm_nonneg (Y a), sq_nonneg A]
    have hxbound := (norm_add_le (Y a) (N a)).trans_lt
      (add_lt_add_of_lt_of_le hybound (hB a ha))
    dsimp [R] at haR
    linarith [norm_nonneg z]
  have hequal (s : ℝ) (hs : s ∈ Icc 0 T) :
      g (Y s+N s) = bakryEmeryLangevinDrift W (Y s+N s) := by
    exact (heq (by simpa only [Metric.mem_closedBall, dist_zero_right] using (hinside s
                     hs).le)).symm
  refine ⟨Y, hY, hY0,?_,?_⟩
  · intro t ht
    rw [hI t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hequal s ⟨hs.1, hs.2.trans ht.2⟩
  · intro t ht
    rw [← hequal t ⟨ht.1.le, ht.2.le⟩]
    exact hD t ht
/-- A chosen actual finite-horizon corrected trajectory. All existence inputs
are discharged by the preceding construction. -/
noncomputable def bakryEmeryLangevinCorrectionOn (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N : ℝ → E) (hN : Continuous N) (z : E) (T : ℝ) (hT : 0 ≤ T) : ℝ → E :=
  Classical.choose (bakryEmeryLangevin_global_exists_on W κ hκ hW hc N hN z T hT)

theorem bakryEmeryLangevinCorrectionOn_spec (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N : ℝ → E) (hN : Continuous N) (z : E) (T : ℝ) (hT : 0 ≤ T) :
    let Y := bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z T hT
    Continuous Y ∧ Y 0 = z ∧
      (∀ t ∈ Icc 0 T, Y t = z + ∫ s in (0 : ℝ)..t,
        bakryEmeryLangevinDrift W (Y s + N s)) ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt Y (bakryEmeryLangevinDrift W (Y t + N t)) t) :=
  Classical.choose_spec (bakryEmeryLangevin_global_exists_on W κ hκ hW hc N hN z T hT)
theorem bakryEmeryLangevinCorrectionOn_consistent (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N : ℝ → E) (hN : Continuous N) (z : E)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    EqOn (bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z S hS)
      (bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z T hT) (Icc 0 (min S T)) := by
  obtain ⟨hXS, hX0, _, hXD⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc N hN z S hS
  obtain ⟨hYS, hY0, _, hYD⟩ := bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc N hN z T hT
  apply bakryEmeryLangevin_pathwise_unique W κ (hW.differentiable (by norm_num)) hc N
    _ _ (min S T) (le_min hS hT) hXS.continuousOn hYS.continuousOn
  · intro t ht; exact hXD t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  · intro t ht; exact hYD t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  · rw [hX0, hY0]
/-- The global corrected Langevin trajectory: at time `t`, the chosen finite-horizon corrected
trajectory `bakryEmeryLangevinCorrectionOn` with horizon `|t| + 1`, evaluated at `t`. -/
noncomputable def bakryEmeryLangevinCorrection (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N : ℝ → E) (hN : Continuous N) (z : E) (t : ℝ) : E :=
  bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z (|t|+1)
    (by positivity) t

lemma bakryEmeryLangevinCorrection_eq_on (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N : ℝ → E) (hN : Continuous N) (z : E) (T : ℝ) (hT : 0 ≤ T) :
    EqOn (bakryEmeryLangevinCorrection W κ hκ hW hc N hN z)
      (bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z T hT) (Icc 0 T) := by
  intro t ht
  exact bakryEmeryLangevinCorrectionOn_consistent W κ hκ hW hc N hN z
    (|t|+1) T (by positivity) hT
    ⟨ht.1, le_min (by rw [abs_of_nonneg ht.1]; linarith) ht.2⟩

/-- One actual corrected trajectory exists for all nonnegative times. -/
theorem bakryEmeryLangevinCorrection_global_spec (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (N : ℝ → E) (hN : Continuous N) (z : E) :
    let Y := bakryEmeryLangevinCorrection W κ hκ hW hc N hN z
    ContinuousOn Y (Ici 0) ∧ Y 0 = z ∧
      (∀ t, 0 ≤ t → Y t = z + ∫ s in (0 : ℝ)..t,
        bakryEmeryLangevinDrift W (Y s + N s)) ∧
      (∀ t, 0 < t → HasDerivAt Y (bakryEmeryLangevinDrift W (Y t+N t)) t) := by
  let Y := bakryEmeryLangevinCorrection W κ hκ hW hc N hN z
  have heq (T : ℝ) (hT : 0 ≤ T) :=
    bakryEmeryLangevinCorrection_eq_on W κ hκ hW hc N hN z T hT
  have hspec (T : ℝ) (hT : 0 ≤ T) :=
    bakryEmeryLangevinCorrectionOn_spec W κ hκ hW hc N hN z T hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht0 : 0 ≤ t := ht
    have hn : Icc 0 (t+1) ∈ 𝓝[Ici 0] t := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : t < t+1)),
        self_mem_nhdsWithin] with s hs hs0
      exact ⟨hs0, hs.le⟩
    have hh : Y =ᶠ[𝓝[Ici 0] t]
        bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z (t+1) (by positivity) :=
      Filter.eventually_of_mem hn (fun s hs => heq (t+1) (by positivity) hs)
    exact ((hspec (t+1) (by positivity)).1.continuousAt.continuousWithinAt).congr_of_eventuallyEq hh
      (heq (t+1) (by positivity) ⟨ht0, by linarith⟩)
  · exact (heq 0 le_rfl ⟨le_rfl, le_rfl⟩).trans (hspec 0 le_rfl).2.1
  · intro t ht
    rw [heq t ht ⟨ht, le_rfl⟩, (hspec t ht).2.2.1 t ⟨ht, le_rfl⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    dsimp only
    rw [heq t ht hs]
  · intro t ht
    have hT : 0 ≤ t+1 := by linarith
    have hd := (hspec (t+1) hT).2.2.2 t ⟨ht, by linarith⟩
    have hh : Y =ᶠ[𝓝 t] bakryEmeryLangevinCorrectionOn W κ hκ hW hc N hN z (t+1) hT := by
      filter_upwards [Ioo_mem_nhds ht (by linarith : t < t+1)] with s hs
      exact heq (t+1) hT ⟨hs.1.le, hs.2.le⟩
    have hd' := hd.congr_of_eventuallyEq hh
    simpa only [heq (t+1) hT ⟨ht.le, by linarith⟩] using hd'
end Hilbert

end
end GinibrePoincare
