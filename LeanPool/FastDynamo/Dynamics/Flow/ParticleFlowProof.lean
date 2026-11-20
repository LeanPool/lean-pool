/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Flow.TorusFlow

/-!
# The explicit map `Φ_t` is the particle flow of the velocity

`FastDynamo/Dynamics/Flow/TorusFlow.lean` builds the map

```
  literalFlow h P angularSpeed axialSpeed tau t : Torus 3 → Torus 3
```

of `eq:explicit-particle-flow` together with its
periodic lift `literalFlowLift … t : ℝ³ → ℝ³`, and proves the group laws, `Φ_0 = id`,
`Φ_{−t} ∘ Φ_t = id` and the Lipschitz bound `flowLipschitzBound … t`.  This module closes the
dynamical statement those pieces were built for: the paper's

```
  d/dt Φ_t(x) = u(Φ_t(x)),        Φ_0(x) = x
```

(the display at the start of §4), **verified** on the explicit formula rather than obtained from
ODE theory.  This is a deviation in the argument: the paper takes existence and uniqueness of
`Φ_t` from the global Lipschitz bound of `lem:global-velocity` (Cauchy–Lipschitz) and, in the
proof of `prop:particle-flow`, derives `eq:explicit-particle-flow` by following a trajectory
(`r` is invariant, angle and axial coordinate move at constant speeds).  Here the formula is the
definition of `Φ_t`, this module checks that it solves the ODE, and uniqueness is proved
separately by a Grönwall argument in `FastDynamo/Dynamics/Flow/ParticleFlowUniqueness.lean`.

## Contents

* `parameterizedFullGlobalPeriodizedRealSource_eq_of_localTranslationIndex_eq_zero`,
  `parameterizedFullGlobalPeriodizedRealSource_add_chartTranslation`,
  `literalVelocity_literalTorusPoint` — the velocity read on the universal cover: the value of
  `literalVelocity (parameterizedFullGlobalRealTorusSource …)` at a lifted point is the
  periodised chart-side field at the transverse coordinates of the lift, and the periodised field
  is the chart-side field itself wherever the active integer translate is trivial.
* `hasDerivAt_planePeriodizedFlowTriple`, `hasDerivAt_literalFlowLift` — **the ODE**: the velocity
  along the lift of a trajectory is the velocity of the field at the current point.  Inside a
  buffer disc this is `hasDerivAt_cellTransverseFlow` / `hasDerivAt_cellAxialDisplacement`
  (`Flow/CellFlowMap.lean`) read through the single-cell reduction
  `planeTransverseFlow_eq_cell_of_mem_bufferDisk` (`Flow/PlaneFlow.lean`) and the cell-velocity
  formula `parameterizedFullEuclideanCellRealSource_eq_cellProfiles` (`Flow/CellProfiles.lean`,
  first display of the proof of `prop:particle-flow`); off the discs both sides vanish.
* `isParticleFlow_literalFlow` — `IsParticleFlow (literalVelocity …) (literalFlow …)`.
* `forall_literalFlow_neg_literalFlow`, `exists_lipschitzWith_literalFlow` — the two clauses of
  `MainLagrangianClauses` (`FastDynamo/Dynamics/ParticleFlow.lean`) that the flow alone discharges
  besides the particle-flow property: the inverse clause (`Φ_t^{-1} = Φ_{-t}`, proof of
  `prop:particle-flow`) and the Lipschitz clause `eq:linear-flow-lipschitz` with the constant
  `flowCL` of `FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`.

## Two facts that make the ODE a computation

1. **The chart-side flow is not `ℤ²`-equivariant, the periodised one is**.  So the lift of
   `Φ_t` runs on `planePeriodizedTransverseFlow` / `planePeriodizedAxialShift`, and every
   statement about the velocity has to be moved to the chart through
   `planePeriodizedTransverseFlow_eq`: the periodised flow at `x` is the chart-side flow at the
   recentred point `x − chartTranslation x`, translated back by the same integer vector.  The
   recentred point has trivial translation index, and so does its whole forward orbit
   (`localTranslationIndex_planeTransverseFlow`), which is what lets the *velocity* be read on
   the chart at every time.
2. **Radius invariance**: `ω_n` and `g_n` are constant along a trajectory
   (`cellAngularSpeed_cellTransverseFlow`, `Flow/CellFlowMap.lean`), so the right-hand side of the
   ODE may be read either at the initial point — the form `hasDerivAt_cellTransverseFlow` proves —
   or at the current point (the form `IsParticleFlow` asks for).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete
open UnitBoxPeriodization

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The velocity read on the universal cover -/

/-- Where the active integer translate is the trivial one, the periodised velocity is the
chart-side velocity itself.  This is the `UnitBoxPeriodization` lemma
`eventuallyEq_self_of_localTranslationIndex_eq_zero`, read at the centre of the neighbourhood on
which it is stated. -/
theorem parameterizedFullGlobalPeriodizedRealSource_eq_of_localTranslationIndex_eq_zero
    {x : ℝ × ℝ} (hx : localTranslationIndex x = 0) :
    parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau x =
      parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau x :=
  (eventuallyEq_self_of_localTranslationIndex_eq_zero
    (supportedInPlacementChart_parameterizedFullGlobalEuclideanRealSource
      h P angularSpeed axialSpeed tau) hx).eq_of_nhds

/-- The periodised velocity does not see the integer vector `chartTranslation z`: that is the
whole point of the periodisation. -/
theorem parameterizedFullGlobalPeriodizedRealSource_add_chartTranslation (y z : ℝ × ℝ) :
    parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
        (y + chartTranslation z) =
      parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau y :=
  isLatticePeriodic_parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
    y (localTranslationIndex z).1 (localTranslationIndex z).2

/-- **The velocity of the main theorem, read at a lifted point.**  The axially independent
extension of the torus-side velocity, evaluated at `literalTorusPoint a`, is the periodised
chart-side velocity evaluated at the transverse coordinates `(a 0, a 1)` of the lift.  This is
`parameterizedFullGlobalRealTorusSource_transverseTorusPoint`
(`FastDynamo/Global/TorusGlobalVelocityLipschitz.lean`) in the three-dimensional coordinates. -/
theorem literalVelocity_literalTorusPoint (a : R3) :
    literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
        (literalTorusPoint a) =
      parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau (a 0, a 1) := by
  change parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau
      (fun j : Fin 2 ↦ literalTorusPoint a j.castSucc) = _
  rw [literalTorusPoint_castSucc a, parameterizedFullGlobalRealTorusSource_transverseTorusPoint]

/-! ## The ODE -/

/-- **The ODE, on the universal cover** (cf. the first paragraph of the proof of
`prop:particle-flow`).  The curve
built from the periodised plane flow and the periodised axial shift — which is exactly the lift
`literalFlowLift … t a` at `x = (a 0, a 1)`, `axialBase = a 2` — has, at every time, derivative
equal to the periodised velocity at the current transverse position.

The proof is a two-case computation.  Both cases are read at the recentred point
`x − chartTranslation x`, where the bridge `planePeriodizedTransverseFlow_eq` puts the periodised
flow, and whose forward orbit keeps a trivial translation index, so that the periodised velocity
along the orbit is the chart-side velocity.  Inside a buffer disc the plane flow is the single
cell flow, its time derivative is `ω_n(x) (Φ_t x − p_n)^⊥` and `g_n(x)`
(`hasDerivAt_cellTransverseFlow`, `hasDerivAt_cellAxialDisplacement`), the profiles are constant
along the orbit (`cellAngularSpeed_cellTransverseFlow`), and the cell-velocity formula
`u = (ω_n(r)(y−p_n)^⊥, g_n(r))` (first display of the proof of `prop:particle-flow`) identifies that
with the velocity at the current point.  Off every buffer disc the flow is the identity and the
velocity is zero. -/
theorem hasDerivAt_planePeriodizedFlowTriple (t : ℝ) (axialBase : ℝ) (x : ℝ × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![(planePeriodizedTransverseFlow h P angularSpeed s x).1,
          (planePeriodizedTransverseFlow h P angularSpeed s x).2,
          axialBase + planePeriodizedAxialShift h P axialSpeed tau s x])
      (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
        (planePeriodizedTransverseFlow h P angularSpeed t x)) t := by
  have hzero : localTranslationIndex (x - chartTranslation x) = 0 :=
    localTranslationIndex_sub_chartTranslation x
  have hvel : parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
      (planePeriodizedTransverseFlow h P angularSpeed t x) =
      parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau
        (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)) := by
    rw [planePeriodizedTransverseFlow_eq,
      parameterizedFullGlobalPeriodizedRealSource_add_chartTranslation,
      parameterizedFullGlobalPeriodizedRealSource_eq_of_localTranslationIndex_eq_zero
        h P angularSpeed axialSpeed tau
        (localTranslationIndex_planeTransverseFlow h P angularSpeed hzero t)]
  rw [hvel]
  by_cases hbuf : ∃ n : ℕ, (x - chartTranslation x) ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuf
    have hcell : planeTransverseFlow h P angularSpeed t (x - chartTranslation x) =
        cellTransverseFlow h P angularSpeed n t (x - chartTranslation x) :=
      planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hn
    have hmem : planeTransverseFlow h P angularSpeed t (x - chartTranslation x) ∈
        P.scaleFamily.bufferDisk n := by
      rw [hcell]
      exact cellTransverseFlow_mem_bufferDisk h P angularSpeed n t hn
    have hw : parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau
        (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)) =
        parameterizedFullEuclideanCellRealSource h P angularSpeed axialSpeed tau n
          (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)) :=
      parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
        h P angularSpeed axialSpeed tau hmem
    refine hasDerivAt_r3
      (u := cellAngularSpeed h P angularSpeed n (x - chartTranslation x) •
        perp (cellTransverseFlow h P angularSpeed n t (x - chartTranslation x) -
          P.scaleFamily.cellCenter n))
      (d := cellAxialSpeed h P axialSpeed tau n (x - chartTranslation x)) ?_ ?_ ?_ ?_ ?_
    · have hfun : (fun s : ℝ ↦ planePeriodizedTransverseFlow h P angularSpeed s x) =
          fun s : ℝ ↦ cellTransverseFlow h P angularSpeed n s (x - chartTranslation x) +
            chartTranslation x := by
        funext s
        rw [planePeriodizedTransverseFlow_eq,
          planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed s hn]
      rw [hfun]
      exact (hasDerivAt_cellTransverseFlow h P angularSpeed n t
        (x - chartTranslation x)).add_const _
    · have hfun : (fun s : ℝ ↦ axialBase + planePeriodizedAxialShift h P axialSpeed tau s x) =
          fun s : ℝ ↦ axialBase +
            cellAxialDisplacement h P axialSpeed tau n s (x - chartTranslation x) := by
        funext s
        rw [planePeriodizedAxialShift_eq,
          planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau s hn]
      rw [hfun]
      exact (hasDerivAt_cellAxialDisplacement h P axialSpeed tau n t
        (x - chartTranslation x)).const_add _
    · rw [hw, parameterizedFullEuclideanCellRealSource_apply_zero, hcell,
        cellAngularSpeed_cellTransverseFlow]
      simp [perp]
      ring
    · rw [hw, parameterizedFullEuclideanCellRealSource_apply_one, hcell,
        cellAngularSpeed_cellTransverseFlow]
      simp [perp]
    · rw [hw, parameterizedFullEuclideanCellRealSource_apply_two, hcell,
        cellAxialSpeed_cellTransverseFlow]
  · push Not at hbuf
    have hfix : planeTransverseFlow h P angularSpeed t (x - chartTranslation x) =
        x - chartTranslation x :=
      planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed t hbuf
    have hw : parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau
        (planeTransverseFlow h P angularSpeed t (x - chartTranslation x)) = 0 := by
      rw [hfix]
      exact parameterizedFullGlobalEuclideanRealSource_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed tau hbuf
    refine hasDerivAt_r3 (u := (0 : ℝ × ℝ)) (d := (0 : ℝ)) ?_ ?_ ?_ ?_ ?_
    · have hfun : (fun s : ℝ ↦ planePeriodizedTransverseFlow h P angularSpeed s x) =
          fun _ : ℝ ↦ (x - chartTranslation x) + chartTranslation x := by
        funext s
        rw [planePeriodizedTransverseFlow_eq,
          planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed s hbuf]
      rw [hfun]
      exact hasDerivAt_const t _
    · have hfun : (fun s : ℝ ↦ axialBase + planePeriodizedAxialShift h P axialSpeed tau s x) =
          fun _ : ℝ ↦ axialBase + (0 : ℝ) := by
        funext s
        rw [planePeriodizedAxialShift_eq,
          planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau s hbuf]
      rw [hfun]
      exact hasDerivAt_const t _
    · rw [hw]; rfl
    · rw [hw]; rfl
    · rw [hw]; rfl

/-- **The ODE along the lift** (the flow equation at the start of §4):
the lift `t ↦ literalFlowLift … t a` of the trajectory through `literalTorusPoint a` has, at every
time, derivative equal to the velocity of the field at the current point of the trajectory.  This
is the clause `IsParticleFlow.ode` asks for, at the lift `literalFlowLift`
(`Flow/TorusFlow.lean`). -/
theorem hasDerivAt_literalFlowLift (t : ℝ) (a : R3) :
    HasDerivAt (fun s : ℝ ↦ literalFlowLift h P angularSpeed axialSpeed tau s a)
      (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
        (literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau t a))) t := by
  have hvel :
      literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
          (literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau t a)) =
        parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
          (planePeriodizedTransverseFlow h P angularSpeed t (a 0, a 1)) := by
    rw [literalVelocity_literalTorusPoint, literalFlowLift_pair]
  rw [hvel]
  exact hasDerivAt_planePeriodizedFlowTriple h P angularSpeed axialSpeed tau t (a 2) (a 0, a 1)

/-- **`Φ` is the particle flow of the velocity** (the flow equation at the start of §4, for the
map of `eq:explicit-particle-flow`): `Φ_0 = id` and `d/dt Φ_t(x) = u(Φ_t(x))`, the derivative read
along the periodic lift `literalFlowLift` of the trajectory, as the paper does in the proof of
`cor:ideal-growth` ("the periodic lift of `u` and the corresponding equivariant lift of `Φ_t`").

No sign condition on `tau` is needed: the ODE is an identity between explicit formulas, and only
the *size* of the velocity — never its verification — uses `0 ≤ tau`. -/
theorem isParticleFlow_literalFlow :
    IsParticleFlow
      (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
      (literalFlow h P angularSpeed axialSpeed tau) where
  initial := literalFlow_zero h P angularSpeed axialSpeed tau
  ode := by
    intro y
    obtain ⟨a, rfl⟩ := literalTorusPoint_surjective y
    refine ⟨fun s : ℝ ↦ literalFlowLift h P angularSpeed axialSpeed tau s a, fun s ↦ ?_,
      fun s ↦ ?_⟩
    · exact (literalTorusPoint_literalFlowLift h P angularSpeed axialSpeed tau s a).symm
    · have hflow := literalTorusPoint_literalFlowLift h P angularSpeed axialSpeed tau s a
      rw [← hflow]
      exact hasDerivAt_literalFlowLift h P angularSpeed axialSpeed tau s a

/-! ## The clauses of `MainLagrangianClauses` carried by the flow -/

/-- **`Φ_t⁻¹ = Φ_{−t}`** (proof of `prop:particle-flow`), in the shape the clause of
`MainLagrangianClauses` asks for.  This is `literalFlow_neg_literalFlow`
(`Flow/TorusFlow.lean`), re-exported. -/
theorem forall_literalFlow_neg_literalFlow :
    ∀ (t : ℝ) (x : Torus 3),
      literalFlow h P angularSpeed axialSpeed tau (-t)
        (literalFlow h P angularSpeed axialSpeed tau t x) = x :=
  literalFlow_neg_literalFlow h P angularSpeed axialSpeed tau

/-- **The Lipschitz clause** `eq:linear-flow-lipschitz` (statement of `prop:particle-flow`), in
the shape the clause of `MainLagrangianClauses` asks for:

```
  Lip(Φ_t) + Lip(Φ_{−t}) ≤ C_L (1 + |t|),        C_L = flowCL h P Ω U tau.
```

Both admissible constants are `flowLipschitzBound … t` (`lipschitzWith_literalFlow`), and the
sum estimate is `flowLipschitzBound_add_neg_le`; `1 ≤ flowCL` is `one_le_flowCL`
(both in `Flow/PlaneFlowLipschitz.lean`). -/
theorem exists_lipschitzWith_literalFlow (htau : 0 ≤ tau) :
    ∀ t : ℝ, ∃ L₁ L₂ : NNReal,
      LipschitzWith L₁ (literalFlow h P angularSpeed axialSpeed tau t) ∧
        LipschitzWith L₂ (literalFlow h P angularSpeed axialSpeed tau (-t)) ∧
          (L₁ : ℝ) + (L₂ : ℝ) ≤ flowCL h P angularSpeed axialSpeed tau * (1 + |t|) := by
  intro t
  refine ⟨flowLipschitzBoundNN h P angularSpeed axialSpeed tau t,
    flowLipschitzBoundNN h P angularSpeed axialSpeed tau (-t),
    lipschitzWith_literalFlow h P angularSpeed axialSpeed tau htau t,
    lipschitzWith_literalFlow h P angularSpeed axialSpeed tau htau (-t), ?_⟩
  rw [coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau,
    coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau]
  exact flowLipschitzBound_add_neg_le h P angularSpeed axialSpeed tau htau t

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
