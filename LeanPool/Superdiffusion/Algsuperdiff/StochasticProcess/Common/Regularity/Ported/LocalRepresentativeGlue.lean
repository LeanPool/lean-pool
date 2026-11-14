/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderSchauderBall
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.Average

/-!
# LocalRepresentativeGlue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From local continuous representatives to a global one

An interior estimate produces, on each small ball inside an open set `W`, a
continuous function agreeing almost everywhere with a given `u`.  This file
glues those local representatives into a single function continuous on all of
`W` and still agreeing almost everywhere with `u`.

No choice over a cover is used.  The glued function is the canonical
shrinking-average candidate

`shrinkingAverageLimit u x = limUnder atTop (fun n ↦ ⨍_{euclideanBall x (n+1)⁻¹} u)`,

which reproduces the value of *any* local continuous representative at the
centre of the ball, hence is automatically consistent on overlaps.

The uniqueness companion `eqOn_of_continuousOn_of_ae_eq` upgrades an almost
everywhere identity between two functions continuous on an open set to an
identity at every point of that set.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport Filter Topology
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Two functions continuous on an open set that agree almost everywhere there
agree at every point of the set. -/
theorem eqOn_of_continuousOn_of_ae_eq {W : Set (Vec d)} (hW : IsOpen W)
    {f g : Vec d → ℝ} (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (hfg : f =ᵐ[volume.restrict W] g) : Set.EqOn f g W :=
  Measure.eqOn_open_of_ae_eq (μ := volume) hfg hW hf hg

/-! ## The shrinking-average candidate -/

/-- The average of `u` over the Euclidean ball of radius `(n+1)⁻¹` about `x`. -/
def shrinkingBallAverage (u : Vec d → ℝ) (x : Vec d) (n : ℕ) : ℝ :=
  ⨍ y in euclideanBall x ((n : ℝ) + 1)⁻¹, u y ∂volume

/-- The canonical candidate representative: the limit of the shrinking ball
averages of `u`. -/
def shrinkingAverageLimit (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  limUnder atTop (shrinkingBallAverage u x)

/-- Where `u` agrees almost everywhere with a function continuous on a ball
about `x`, the shrinking ball averages of `u` converge to the value of that
function at `x`. -/
theorem tendsto_shrinkingBallAverage {x : Vec d} {r : ℝ} (hr : 0 < r)
    {u v : Vec d → ℝ} (hv : ContinuousOn v (euclideanBall x r))
    (huv : v =ᵐ[volume.restrict (euclideanBall x r)] u) :
    Tendsto (shrinkingBallAverage u x) atTop (nhds (v x)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hxmem : x ∈ euclideanBall x r := center_mem_euclideanBall x hr
  have hcont : ContinuousAt v x :=
    hv.continuousAt ((isOpen_euclideanBall x r).mem_nhds hxmem)
  have hnear : ∀ᶠ y in nhds x, |v y - v x| ≤ eps / 2 := by
    have := hcont.tendsto
    have hball : Set.Ioo (v x - eps / 2) (v x + eps / 2) ∈ nhds (v x) :=
      Ioo_mem_nhds (by linarith only [heps]) (by linarith only [heps])
    filter_upwards [this hball] with y hy
    rw [abs_le]
    constructor <;> [linarith only [hy.1]; linarith only [hy.2]]
  obtain ⟨eta, heta, hetaball⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨N, hN⟩ := exists_nat_gt (min eta r)⁻¹
  have hmin : 0 < min eta r := lt_min heta hr
  refine ⟨N, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : (min eta r)⁻¹ < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    linarith only [hN, this]
  set rho : ℝ := ((n : ℝ) + 1)⁻¹ with hrho
  have hrhopos : 0 < rho := by positivity
  have hrhomin : rho < min eta r := by
    rw [hrho]
    rw [inv_lt_comm₀ hnpos hmin]
    exact hlt
  have hrhoeta : rho < eta := lt_of_lt_of_le hrhomin (min_le_left _ _)
  have hrhor : rho < r := lt_of_lt_of_le hrhomin (min_le_right _ _)
  set B : Set (Vec d) := euclideanBall x rho with hB
  have hBopen : IsOpen B := isOpen_euclideanBall x rho
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hBsub : B ⊆ euclideanBall x r :=
    euclideanBall_subset_euclideanBall hrhopos.le hrhor
  have hBmetric : B ⊆ Metric.ball x eta := fun y hy =>
    Metric.ball_subset_ball hrhoeta.le (euclideanBall_subset_metricBall hrhopos hy)
  have hBne : B.Nonempty := ⟨x, center_mem_euclideanBall x hrhopos⟩
  have hBfin : IsFiniteMeasure (volume.restrict B) :=
    HCPolySupport.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall x rho
  have hBpos : volume.restrict B ≠ 0 := by
    intro hzero
    have hval : (volume.restrict B) B = 0 := by rw [hzero]; rfl
    rw [Measure.restrict_apply_self] at hval
    exact (hBopen.measure_pos volume hBne).ne' hval
  have hbound : ∀ y ∈ B, |v y - v x| ≤ eps / 2 := fun y hy =>
    hetaball (Metric.mem_ball.mp (hBmetric hy))
  have hvB : ContinuousOn v B := hv.mono hBsub
  have hvmeas : AEStronglyMeasurable v (volume.restrict B) :=
    hvB.aestronglyMeasurable hBmeas
  have hvint : Integrable v (volume.restrict B) := by
    refine Integrable.mono' (integrable_const (|v x| + eps / 2)) hvmeas ?_
    filter_upwards [ae_restrict_mem hBmeas] with y hy
    have := hbound y hy
    rw [Real.norm_eq_abs]
    calc |v y| = |(v y - v x) + v x| := by ring_nf
      _ ≤ |v y - v x| + |v x| := abs_add_le _ _
      _ ≤ eps / 2 + |v x| := by linarith only [this]
      _ = |v x| + eps / 2 := by ring
  have huvB : v =ᵐ[volume.restrict B] u := by
    refine ae_restrict_of_ae_restrict_of_subset hBsub huv
  have hcongr : shrinkingBallAverage u x n = ⨍ y in B, v y ∂volume := by
    rw [shrinkingBallAverage, ← hrho, ← hB]
    exact (average_congr huvB).symm
  have hae : ∀ᵐ y ∂volume.restrict B, |v y - v x| ≤ eps / 2 := by
    filter_upwards [ae_restrict_mem hBmeas] with y hy
    exact hbound y hy
  have hfinal := Algsuperdiff.Probability.abs_average_sub_const_le_of_ae hBpos hvint hae
  rw [Real.dist_eq, hcongr]
  calc |(⨍ y in B, v y ∂volume) - v x| ≤ eps / 2 := hfinal
    _ < eps := by linarith only [heps]

/-- The candidate reproduces the value of any local continuous representative. -/
theorem shrinkingAverageLimit_eq_of_local {x : Vec d} {r : ℝ} (hr : 0 < r)
    {u v : Vec d → ℝ} (hv : ContinuousOn v (euclideanBall x r))
    (huv : v =ᵐ[volume.restrict (euclideanBall x r)] u) :
    shrinkingAverageLimit u x = v x :=
  (tendsto_shrinkingBallAverage hr hv huv).limUnder_eq

/-- The candidate agrees with a local continuous representative on the whole
ball on which the latter is defined. -/
theorem eqOn_shrinkingAverageLimit {x : Vec d} {r : ℝ}
    {u v : Vec d → ℝ} (hv : ContinuousOn v (euclideanBall x r))
    (huv : v =ᵐ[volume.restrict (euclideanBall x r)] u) :
    Set.EqOn (shrinkingAverageLimit u) v (euclideanBall x r) := by
  intro z hz
  obtain ⟨s, hs, hsub⟩ :=
    Metric.isOpen_iff.mp (isOpen_euclideanBall x r) z hz
  have hsubEuclid : euclideanBall z s ⊆ euclideanBall x r := fun y hy =>
    hsub (euclideanBall_subset_metricBall hs hy)
  exact shrinkingAverageLimit_eq_of_local hs (hv.mono hsubEuclid)
    (ae_restrict_of_ae_restrict_of_subset hsubEuclid huv)

/-- Local continuous representatives on Euclidean balls glue to a single
representative continuous on the whole open set. -/
theorem exists_continuousOn_representative_of_local
    {W : Set (Vec d)} (hW : IsOpen W) (u : Vec d → ℝ)
    (hloc : ∀ x ∈ W, ∃ r > 0, euclideanBall x r ⊆ W ∧
      ∃ v : Vec d → ℝ, ContinuousOn v (euclideanBall x r) ∧
        v =ᵐ[volume.restrict (euclideanBall x r)] u) :
    ∃ w : Vec d → ℝ, ContinuousOn w W ∧ w =ᵐ[volume.restrict W] u := by
  refine ⟨shrinkingAverageLimit u, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, -, v, hv, huv⟩ := hloc x hx
    have hEq : Set.EqOn (shrinkingAverageLimit u) v (euclideanBall x r) :=
      eqOn_shrinkingAverageLimit hv huv
    have hcontBall : ContinuousOn (shrinkingAverageLimit u) (euclideanBall x r) :=
      (hv.mono (le_refl _)).congr hEq
    exact ((hcontBall.continuousAt
      ((isOpen_euclideanBall x r).mem_nhds
        (center_mem_euclideanBall x hr))).continuousWithinAt)
  · have hnull : volume ({y : Vec d | shrinkingAverageLimit u y ≠ u y} ∩ W) = 0 := by
      refine measure_null_of_locally_null _ ?_
      rintro x ⟨-, hxW⟩
      obtain ⟨r, hr, -, v, hv, huv⟩ := hloc x hxW
      refine ⟨({y : Vec d | shrinkingAverageLimit u y ≠ u y} ∩ W) ∩
        euclideanBall x r, ?_, ?_⟩
      · exact inter_mem_nhdsWithin _
          ((isOpen_euclideanBall x r).mem_nhds (center_mem_euclideanBall x hr))
      · have hEq : Set.EqOn (shrinkingAverageLimit u) v (euclideanBall x r) :=
          eqOn_shrinkingAverageLimit hv huv
        have hball : shrinkingAverageLimit u =ᵐ[volume.restrict (euclideanBall x r)] u := by
          filter_upwards [huv, ae_restrict_mem (isOpen_euclideanBall x r).measurableSet]
            with y hy hyB
          rw [hEq hyB, hy]
        rw [Filter.EventuallyEq, ae_iff,
          Measure.restrict_apply' (isOpen_euclideanBall x r).measurableSet] at hball
        refine measure_mono_null ?_ hball
        rintro y ⟨⟨hy, -⟩, hyB⟩
        exact ⟨hy, hyB⟩
    rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' hW.measurableSet]
    exact hnull

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
