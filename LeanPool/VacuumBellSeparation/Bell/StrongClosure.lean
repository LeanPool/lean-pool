/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Defs

/-!
# Strong limits in the actual von Neumann algebra

The double-commutant definition implies closure under pointwise convergence of
bounded operators. No operator-norm convergence or bound on the family is
required: the limiting operator is already an actual continuous linear map.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_vonNeumannAlgebra_of_strong_tendsto (A : VonNeumannAlgebra H)
    {α : Type*} {l : Filter α} [l.NeBot]
    {Ts : α → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hmem : ∀ᶠ i in l, Ts i ∈ A)
    (hlim : ∀ x, Tendsto (fun i => Ts i x) l (𝓝 (T x))) : T ∈ A := by
  rw [← A.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro B hB
  apply ContinuousLinearMap.ext
  intro x
  have hleft := B.continuous.continuousAt.tendsto.comp (hlim x)
  have hright := hlim (B x)
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  filter_upwards [hmem] with i hi
  exact (DFunLike.congr_fun (VonNeumannAlgebra.mem_commutant_iff.mp hB (Ts i) hi) x).symm

end VacuumBellSeparation
