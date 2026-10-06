/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierHeatJRange
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildVelocityDefinition
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLipschitz
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildStokesLinear
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Local solutions of the regularized mild equation

The solution is constructed as a continuous trajectory on the closed lifespan
interval in `lem:reg-local-mild`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The compact time interval for a local mild trajectory. -/
abbrev RegularizedMildTimeInterval (T : ℝ) := Set.Icc (0 : ℝ) T

/-- A continuous trajectory satisfies the regularized mild equation on its
time interval. -/
@[expose]
def IsRegularizedMildTrajectory (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (b : RealVectorL2) (T : ℝ)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2)) : Prop :=
  ∀ t : RegularizedMildTimeInterval T,
    u t = regularizedMildRightHandSide b
      (fun s => if hs : s ∈ RegularizedMildTimeInterval T then
        regularizedMildTensor ρ ε hε (u ⟨s, hs⟩) else 0)
      t.1 t.2.1

/-- The continuous time space on the closed interval has the supremum norm
used in the contraction argument. -/
theorem regularizedMildTrajectory_norm_le_iff
    (T : ℝ)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2)) (R : ℝ)
    (hR : 0 ≤ R) : ‖u‖ ≤ R ↔ ∀ t, ‖u t‖ ≤ R := by
  exact u.norm_le hR

end CKN.Leray

end
