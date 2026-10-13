/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.FreezingRadius
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CoefficientMeasurable

/-!
# Measurable stream coefficients

Coefficient-field evaluations depend measurably on the environment.
Ported from the Apache-2.0 Superdiffusion source at
`7f20476385d4af418f110303085ad0740c9eba46`.
-/

@[expose] public section

namespace Algsuperdiff.Section5.Measurability

open Algsuperdiff.Section3
open Algsuperdiff.Section5
open Algsuperdiff.Frozen.Assumptions
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ} {gamma nu : ℝ}

theorem measurable_streamField_apply (x : Vec d) :
    Measurable fun omega : Field.FullSample d gamma => Field.streamField omega x := by
  refine measurable_matrix_of_entries fun i j => ?_
  apply Measurable.tsum
  intro n
  have hcont (z : Vec d) : Continuous fun j : ShellField d => j z :=
    (continuous_eval_const z).comp
      (continuous_fst.comp continuous_subtype_val)
  have hvalue (z : Vec d) : Measurable fun j : ShellField d => j z :=
    (hcont z).measurable
  have hshell (z : Vec d) : Measurable fun omega : Field.FullSample d gamma =>
      omega.1.1 n z :=
    (hvalue z).comp
      ((measurable_pi_apply n).comp (measurable_subtype_coe.comp measurable_subtype_coe))
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hshell x))).sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hshell 0)))

theorem measurable_streamCoefficient_apply (x : Vec d) :
    Measurable fun omega : Field.FullSample d gamma => Field.streamCoefficient nu omega x := by
  exact measurable_const.add (measurable_streamField_apply x)

theorem measurable_streamCoefficient_joint :
    Measurable fun p : Field.FullSample d gamma × Vec d =>
      Field.streamCoefficient nu p.1 p.2 := by
  have hswap : Measurable
      (Function.uncurry fun x : Vec d => fun omega : Field.FullSample d gamma =>
        Field.streamCoefficient nu omega x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => Field.continuous_streamCoefficient nu omega)
      (fun x => measurable_streamCoefficient_apply x)
  exact hswap.comp measurable_swap

/-- The full stream coefficient restricted to a compact spatial carrier. -/
def streamCoefficientRestrict (nu : ℝ) (K : Set (Vec d))
    (omega : Field.FullSample d gamma) : C(K, Mat d) :=
  ⟨fun x => Field.streamCoefficient nu omega x,
    (Field.continuous_streamCoefficient nu omega).comp continuous_subtype_val⟩

@[simp] theorem streamCoefficientRestrict_apply (nu : ℝ) (K : Set (Vec d))
    (omega : Field.FullSample d gamma) (x : K) :
    streamCoefficientRestrict nu K omega x = Field.streamCoefficient nu omega x := rfl

private theorem measurableSet_preimage_open_of_closedBall {Omega X : Type*}
    (mOmega : MeasurableSpace Omega) [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] {F : Omega → X}
    (hF : ∀ (c : X) (r : ℝ), MeasurableSet[mOmega] (F ⁻¹' Metric.closedBall c r))
    {V : Set X} (hV : IsOpen V) : MeasurableSet[mOmega] (F ⁻¹' V) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have := hDc.to_subtype
  have hEq : F ⁻¹' V =
      ⋃ (c : ↥D) (q : ℚ) (_ : Metric.closedBall (c : X) (q : ℝ) ⊆ V),
        F ⁻¹' Metric.closedBall (c : X) (q : ℝ) := by
    refine Set.Subset.antisymm (fun w hw => ?_) ?_
    · obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.1 hV (F w) hw
      obtain ⟨c, hcD, hc⟩ :=
        Metric.mem_closure_iff.1 (hDd (F w)) (eps / 4) (by linarith)
      obtain ⟨q, hq1, _hq2⟩ := exists_rat_btwn (show eps / 4 < eps / 3 by linarith)
      refine Set.mem_iUnion.2 ⟨⟨c, hcD⟩, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩⟩
      · intro z hz
        refine hball (Metric.mem_ball.2 ?_)
        have h1 : dist z c ≤ (q : ℝ) := Metric.mem_closedBall.1 hz
        have h2 : dist c (F w) < eps / 4 := by rwa [dist_comm] at hc
        calc dist z (F w) ≤ dist z c + dist c (F w) := dist_triangle _ _ _
          _ < (q : ℝ) + eps / 4 := by linarith
          _ < eps := by linarith
      · exact Metric.mem_closedBall.2 (le_of_lt (hc.trans hq1))
    · refine Set.iUnion_subset fun c => Set.iUnion_subset fun q =>
        Set.iUnion_subset fun hsub => Set.preimage_mono hsub
  rw [hEq]
  exact MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun q =>
    MeasurableSet.iUnion fun _ => hF _ _

private theorem measurable_of_preimage_closedBall {Omega X : Type*}
    (mOmega : MeasurableSpace Omega) [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] {F : Omega → X}
    (hF : ∀ (c : X) (r : ℝ), MeasurableSet[mOmega] (F ⁻¹' Metric.closedBall c r)) :
    Measurable[mOmega] F := by
  have key : @Measurable Omega X mOmega
      (MeasurableSpace.generateFrom {s : Set X | IsOpen s}) F :=
    measurable_generateFrom fun _t ht =>
      measurableSet_preimage_open_of_closedBall mOmega hF ht
  intro s hs
  rw [BorelSpace.measurable_eq (α := X)] at hs
  exact key hs

private theorem measurable_continuousMap_of_eval {Omega : Type*}
    (mOmega : MeasurableSpace Omega) {K : Set (Vec d)} [CompactSpace K]
    {F : Omega → C(K, Mat d)} (hF : ∀ z : K, Measurable[mOmega] fun w => F w z) :
    Measurable[mOmega] F := by
  have : SecondCountableTopology C(K, Mat d) := inferInstance
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  have : Countable D := hDc.to_subtype
  refine measurable_of_preimage_closedBall mOmega fun g r => ?_
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.2 hr, Set.preimage_empty]
    exact MeasurableSet.empty
  · have hEqset : F ⁻¹' Metric.closedBall g r =
        ⋂ z : ↥D, {w | dist (F w z) (g z) ≤ r} := by
      ext w
      simp only [Set.mem_preimage, Metric.mem_closedBall, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h z
        exact (ContinuousMap.dist_le hr).1 h z
      · intro h
        refine (ContinuousMap.dist_le hr).2 fun z => ?_
        have hclosed : IsClosed {z : K | dist (F w z) (g z) ≤ r} :=
          isClosed_le ((F w).continuous.dist g.continuous) continuous_const
        exact hclosed.closure_subset_iff.2 (fun z hz => h ⟨z, hz⟩) (hDd z)
    rw [hEqset]
    refine MeasurableSet.iInter fun z => ?_
    have hdist : Measurable[mOmega] fun w => dist (F w z) (g z) :=
      (continuous_id.dist continuous_const).measurable.comp (hF z)
    exact measurableSet_le hdist measurable_const

/-- The full stream coefficient, restricted to any compact set, is a Borel
measurable continuous matrix field. -/
theorem measurable_streamCoefficientRestrict (nu : ℝ) (K : Set (Vec d))
    [CompactSpace K] :
    Measurable (streamCoefficientRestrict (d := d) (gamma := gamma) nu K) := by
  refine measurable_continuousMap_of_eval _ fun z => ?_
  exact measurable_streamCoefficient_apply (nu := nu) (x := (z : Vec d))


end

end Algsuperdiff.Section5.Measurability
