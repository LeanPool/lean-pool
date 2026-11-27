/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.WeakOperatorUnitBall
public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Actual von Neumann algebras are WOT closed with WOT-compact unit balls

The algebra is its original double commutant. Separate multiplication is
continuous in the actual weak operator topology, so its commutant is closed.
No normal-functional continuity or GNS image theorem is assumed or concluded.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal membership in the original VNA under the WOT type copy. -/
theorem vna_wot_eq_centralizer (M : VonNeumannAlgebra H) :
    {T : H →WOT[ℂ] H | T.toCLM ∈ M} =
      Set.centralizer (ofCLM '' (M.commutant : Set (H →L[ℂ] H))) := by
  ext T
  have hmem : T.toCLM ∈ M ↔
      ∀ Y ∈ M.commutant, Y * T.toCLM = T.toCLM * Y := by
    simpa only [VonNeumannAlgebra.commutant_commutant] using
      (VonNeumannAlgebra.mem_commutant_iff (S := M.commutant) (z := T.toCLM))
  change T.toCLM ∈ M ↔ ∀ X ∈ ofCLM '' (M.commutant : Set (H →L[ℂ] H)),
    X * T = T * X
  rw [hmem]
  constructor
  · intro h X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    apply ContinuousLinearMapWOT.toCLM_injective
    exact h Y hY
  · intro h Y hY
    exact congrArg ContinuousLinearMapWOT.toCLM (h (ofCLM Y) ⟨Y, hY, rfl⟩)

theorem isClosed_vna_wot (M : VonNeumannAlgebra H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ M} := by
  rw [vna_wot_eq_centralizer]
  exact Set.isClosed_centralizer _

/-- This is the original VNA's full unit ball, not a finite-rank compression
or the ball of a generated replacement algebra. -/
theorem isCompact_vna_unitBall_wot (M : VonNeumannAlgebra H) :
    IsCompact {T : H →WOT[ℂ] H | T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ 1} := by
  have h := (isCompact_operator_unitBall_wot (H := H)).inter_left (isClosed_vna_wot M)
  exact h

end VacuumBellSeparation.Bipartite
