/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildInitialTrace

/-!
# Local mild solution for regularized Leray evolution

The contraction on the lifespan of `eq:reg-lifespan` gives the solution of
`lem:reg-local-mild`, including its initial value and uniqueness among all
continuous spatial `L²` mild trajectories.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Local existence and unrestricted mild uniqueness in `lem:reg-local-mild`.
The trajectory takes values in the divergence-free closed subspace. -/
theorem regularizedMildLocalSolution
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) :
    ∃ u : C(RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b),
        RealVectorL2),
      IsRegularizedMildTrajectory ρ ε hε b
        (regularizedMildLocalLifespan ρ ε b) u ∧
      (∀ t, RegularizedMildJData (u t)) ∧
      u ⟨0, le_refl _, (regularizedMildLocalLifespan_pos ρ ε hε b).le⟩ = b ∧
      ∀ v : C(RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b),
          RealVectorL2),
        IsRegularizedMildTrajectory ρ ε hε b
          (regularizedMildLocalLifespan ρ ε b) v → v = u := by
  obtain ⟨u, hu, hball⟩ := regularizedMildLocalFixedPoint ρ ε hε b hb
  refine ⟨u, hu, (fun t => (hball t).1), ?_, ?_⟩
  · have h := hu ⟨0, le_refl _, (regularizedMildLocalLifespan_pos ρ ε hε b).le⟩
    rw [regularizedMildRightHandSide] at h
    have hzero : regularizedMildStokesIntegral
        (fun s => if hs : s ∈
          RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b) then
            regularizedMildTensor ρ ε hε (u ⟨s, hs⟩) else 0) 0 = 0 := by
      simp [regularizedMildStokesIntegral]
    rw [hzero, sub_zero, realHeatOperator_zero] at h
    exact h
  · intro v hv
    exact (regularizedMildTrajectory_unique_local ρ ε hε b v u hv hu)

end CKN.Leray

end
