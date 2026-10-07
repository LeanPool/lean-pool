/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionLerayHopf
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatStrongContinuity

/-!
# The short-time Leray–Hopf solution from an `L³` trace

`prop:pv-local-solution`: every divergence-free datum `a ∈ L² ∩ L³` has a
short-time Leray–Hopf solution in `L⁵ ∩ L⁴` of the slab, with `U(t) → a`
strongly in `L³` as `t ↓ 0`, whose associated pressure `P[U ⊗ U]` lies in
`L² ∩ L^{5/2}` of the slab and satisfies the momentum equation with `U`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `prop:pv-local-solution`. -/
theorem pvLocalSolution_lerayHopf {a : Vec3 → Vec3} (ha : IsInJ a)
    (ha3 : MemLp a (ENNReal.ofReal 3) volume) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ U : ParabolicPoint → Vec3, ∃ DU : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution τ a U DU ∧
      MemLp U (ENNReal.ofReal 5) (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      MemLp U (ENNReal.ofReal 4) (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      Tendsto (fun t => eLpNorm (fun x : Vec3 => U (x, t) - a x) (ENNReal.ofReal 3) volume)
        (𝓝[>] 0) (𝓝 0) ∧
      IsSerrinWeakSolution τ a U DU (pvSlabPressure τ U) ∧
      MemLp (pvSlabPressure τ U) (ENNReal.ofReal 2)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
      MemLp (pvSlabPressure τ U) (ENNReal.ofReal (5 / 2))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) :=
  pvLocalSolution_lerayHopf_of_strongContinuity forcedHeat_strong_continuity ha ha3

end ESS

end
