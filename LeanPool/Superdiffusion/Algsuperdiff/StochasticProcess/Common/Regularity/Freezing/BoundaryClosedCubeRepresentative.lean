/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryLocalRepresentative

/-!
# BoundaryClosedCubeRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Gluing the local representatives on the closed cube

Every point of the closed cube carries a ball on which the solution has a
continuous representative vanishing on the part of the cube boundary the ball
meets.  Averaging over shrinking balls glues the interior data into one
function on the open cube; extending it by zero produces a single
representative continuous on the closed cube and vanishing on its whole
boundary, corners included.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-- **A representative continuous on the closed cube and vanishing on its
boundary.**  The coefficient is continuous on the closed cube with symmetric
part `nu • 1` and skew part of arbitrary size; there is no contrast
hypothesis. -/
theorem exists_closedCube_representative_continuousCoeff [NeZero d] (hd : 2 ≤ d)
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d} (hameas : Measurable a)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d))
      {x | MemAxisCubeClosure z L x})
    {u : H10Function (axisCube z L)} {g : Vec d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : MemScalarLInfOn (axisCube z L) g)
    (hgM : ∀ᵐ y ∂volume.restrict (axisCube z L), |g y| ≤ M)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (axisCube z L)
      u.toH1Function g 0) :
    ∃ V : Vec d → ℝ,
      ContinuousOn V {x | MemAxisCubeClosure z L x} ∧
      V =ᵐ[volume.restrict (axisCube z L)] u.toH1Function.toFun ∧
      ∀ x : Vec d, MemAxisCubeClosure z L x → x ∉ axisCube z L → V x = 0 := by
  classical
  set K : Set (Vec d) := {x | MemAxisCubeClosure z L x} with hKdef
  have hlocalAll : ∀ x : Vec d, MemAxisCubeClosure z L x →
      ∃ rho > 0, ∃ V : Vec d → ℝ,
        ContinuousOn V (euclideanBall x rho) ∧
        V =ᵐ[volume.restrict (euclideanBall x rho ∩ axisCube z L)]
          u.toH1Function.toFun ∧
        ∀ y ∈ euclideanBall x rho, MemAxisCubeClosure z L y →
          y ∉ axisCube z L → V y = 0 := fun x hx =>
    exists_boundary_local_representative hd z hL hnu hameas hsymm hcont hM hg hgM
      hu hx
  -- glue the interior data
  have hlocalInterior : ∀ x ∈ axisCube z L, ∃ r > 0,
      euclideanBall x r ⊆ axisCube z L ∧
      ∃ V : Vec d → ℝ, ContinuousOn V (euclideanBall x r) ∧
        V =ᵐ[volume.restrict (euclideanBall x r)] u.toH1Function.toFun := by
    intro x hx
    obtain ⟨rho, hrho, V, hVcont, hVae, -⟩ :=
      hlocalAll x (axisCube_subset_closureSet z L hx)
    obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.mp (isOpen_axisCube z L) x hx
    have hmin : 0 < min rho s := lt_min hrho hs
    have hballrho : euclideanBall x (min rho s) ⊆ euclideanBall x rho := by
      intro y hy
      rcases eq_or_lt_of_le (min_le_left rho s) with heq | hlt
      · rw [← heq]
        exact hy
      · exact euclideanBall_subset_euclideanBall hmin.le hlt hy
    have hballQ : euclideanBall x (min rho s) ⊆ axisCube z L := by
      intro y hy
      have hd1 : dist y x < min rho s :=
        HCPolySupport.euclideanBall_subset_metricBall hmin hy
      exact hsub (show y ∈ Metric.ball x s from
        lt_of_lt_of_le hd1 (min_le_right rho s))
    refine ⟨min rho s, hmin, hballQ, V, hVcont.mono hballrho, ?_⟩
    refine ae_restrict_of_ae_restrict_of_subset ?_ hVae
    intro y hy
    exact ⟨hballrho hy, hballQ hy⟩
  obtain ⟨Vint, hVintCont, hVintAE⟩ :=
    exists_continuousOn_representative_of_local (isOpen_axisCube z L)
      u.toH1Function.toFun hlocalInterior
  set Vfull : Vec d → ℝ := fun x => if x ∈ axisCube z L then Vint x else 0 with hVfull
  have hVfullQ : ∀ x ∈ axisCube z L, Vfull x = Vint x := by
    intro x hx
    rw [hVfull]
    simp only [hx, ite_true]
  have hVfullZero : ∀ x : Vec d, x ∉ axisCube z L → Vfull x = 0 := by
    intro x hx
    rw [hVfull]
    simp only [hx, ite_false]
  -- the local representatives compute `Vfull` on the closed cube
  have hEqLocal : ∀ x : Vec d, MemAxisCubeClosure z L x → ∀ rho : ℝ, 0 < rho →
      ∀ V : Vec d → ℝ, ContinuousOn V (euclideanBall x rho) →
      V =ᵐ[volume.restrict (euclideanBall x rho ∩ axisCube z L)]
        u.toH1Function.toFun →
      (∀ y ∈ euclideanBall x rho, MemAxisCubeClosure z L y →
        y ∉ axisCube z L → V y = 0) →
      Set.EqOn Vfull V (K ∩ euclideanBall x rho) := by
    intro x _hx rho _hrho V hVcont hVae hVzero y hy
    by_cases hyQ : y ∈ axisCube z L
    · have hOopen : IsOpen (euclideanBall x rho ∩ axisCube z L) :=
        (isOpen_euclideanBall x rho).inter (isOpen_axisCube z L)
      have hae : Vint =ᵐ[volume.restrict (euclideanBall x rho ∩ axisCube z L)] V := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
            (Set.inter_subset_right : euclideanBall x rho ∩ axisCube z L ⊆
              axisCube z L) hVintAE, hVae] with q hq1 hq2
        rw [hq1, hq2]
      have hEq := eqOn_of_continuousOn_of_ae_eq hOopen
        (hVintCont.mono Set.inter_subset_right)
        (hVcont.mono Set.inter_subset_left) hae
      rw [hVfullQ y hyQ]
      exact hEq ⟨hy.2, hyQ⟩
    · rw [hVfullZero y hyQ, hVzero y hy.2 hy.1 hyQ]
  refine ⟨Vfull, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨rho, hrho, V, hVcont, hVae, hVzero⟩ := hlocalAll x hx
    have hEqOn := hEqLocal x hx rho hrho V hVcont hVae hVzero
    have hVat : ContinuousWithinAt V K x :=
      (hVcont.continuousAt ((isOpen_euclideanBall x rho).mem_nhds
        (center_mem_euclideanBall x hrho))).continuousWithinAt
    refine hVat.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds ((isOpen_euclideanBall x rho).mem_nhds
        (center_mem_euclideanBall x hrho)), self_mem_nhdsWithin] with y hy hyK
      exact hEqOn ⟨hyK, hy⟩
    · exact hEqOn ⟨hx, center_mem_euclideanBall x hrho⟩
  · filter_upwards [hVintAE, ae_restrict_mem (isOpen_axisCube z L).measurableSet]
      with y hy hyQ
    rw [hVfullQ y hyQ]
    exact hy
  · intro x _hx hxQ
    exact hVfullZero x hxQ

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
