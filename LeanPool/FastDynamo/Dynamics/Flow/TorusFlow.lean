/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Flow.PlaneFlowLipschitz
public import LeanPool.FastDynamo.Dynamics.Flow.PeriodizedFlowData

/-!
# The explicit particle flow on the literal three-torus

`FastDynamo/Dynamics/Flow/PlaneFlowRegularity.lean` builds the `ℤ²`-equivariant plane flow
`planePeriodizedTransverseFlow` together with the `ℤ²`-periodic axial shift
`planePeriodizedAxialShift` of `prop:particle-flow` (`eq:explicit-particle-flow`), and
`FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean` supplies their uniform Lipschitz constants.
This module packages the two as a `PeriodizedPlaneFlowData`
(`FastDynamo/Dynamics/Flow/PeriodizedFlowData.lean`) and reads off the flow `Φ_t : T³ → T³`
defined at the start of §4,

```
  Φ_t(y, x₃) = (transverse flow of y, x₃ + axial shift of y),
```

together with its periodic lift `literalFlowLift : ℝ³ → ℝ³`, which is the device the paper uses to
differentiate maps of the torus ("the periodic lift of `u` and the corresponding equivariant lift of
`Φ_t`", proof of `cor:ideal-growth`).

## Contents

* The two plane-level facts the datum needs and no other module states: the unit Jacobian
  `det_fderiv_planePeriodizedTransverseFlow` (`det DΦ_t = 1`, which the proof of
  `cor:ideal-growth` obtains almost everywhere from Liouville's formula and `div u = 0`; here it
  is computed pointwise from the closed rank-one derivative formula of
  `FastDynamo/Dynamics/Flow/CellFlowMap.lean`, and Liouville's formula is not used) and the
  invariance `planePeriodizedTransverseFlow_mem_pairUnitIocBox` of the fundamental box.
* `fullFlowData` — the datum itself, and with it `torusTransverseFlow`, `torusAxialShift`,
  `literalFlow` and `literalFlowLift` as the instantiations of `torusFlow`, `torusShift`,
  `PeriodizedPlaneFlowData.literalFlow` and `PeriodizedPlaneFlowData.literalFlowLift`.  The
  descent identities, the time origin, the inverse (`literalFlow_neg_literalFlow`,
  `Φ_t⁻¹ = Φ_{-t}`, proof of `prop:particle-flow`), the iterate law, continuity and
  `isLiteralTorusLift_literalFlow` (`IsLiteralTorusLift` of
  `FastDynamo/Dynamics/ParticleFlow.lean`) are the generic lemmas specialised.
* `literalFlow_eq_cell_of_mem_bufferDisk`, `literalFlow_eq_self_of_forall_not_mem_bufferDisk` and
  `literalFlow_eq_self_of_accumulationPoint` — `eq:explicit-particle-flow` and the fixed points of
  `prop:particle-flow` read at torus level (the statement of `prop:particle-flow`: "Every point
  outside the cells, on their boundaries, and of the accumulation circle `{p_∞} × T` is fixed", the
  cells being the buffer discs `D(p_n, R_n)`).  The development *defines* the flow cell by cell, so
  the display is proved rather than assumed; since the flow is *the* particle flow of the velocity
  (`Flow/ParticleFlowUniqueness.lean`), these are statements about the paper's `Φ_t`.  The paper
  states the cell formula for `y ∈ D(p_n, R_n)` in its coordinate chart; the Lean statement takes
  `y` to be the representative of the horizontal block in the fundamental box `(0,1]²` (where all
  buffer discs lie).  The fixed-point hypothesis is that every integer translate of the chosen
  horizontal representative misses every buffer disc, which is what "outside the discs" means on the
  torus; boundary points are covered because `bufferDisk` is the open disc.
* `lipschitzWith_literalFlow` — the descent of the plane constant, the one part of the torus
  tower that is *not* generic: the truncated tower carries no Lipschitz constant.  The
  transverse coordinates inherit `flowLipschitzBound … t` unchanged, because
  `transverseTorusPoint` is `1`-Lipschitz and
  `lipschitzWith_of_factorsThrough_transverseTorusPoint` transfers the constant with no loss; the
  axial coordinate costs `1 + |t| · flowLipschitzSlope …`, translation on `UnitAddCircle` being
  an isometry and the coercion `ℝ → UnitAddCircle` being `1`-Lipschitz.  Since
  `flowLipschitzBound … t = 2 (1 + |t| · flowLipschitzSlope …)`, the `max` of `dist_pi_le_iff` is
  the transverse constant and **no extra factor is paid**.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

/-- The placement chart `Ioo 0 (1/4) ×ˢ Ioo (1/4) (3/4)` is a proper subbox of the fundamental
box, so the whole displacement of the flow takes place inside a single fundamental cell.

The chart is the one the paper's own placement argument in §3.3 produces — "The first
coordinate of every point in `D(p_n,R_n)` lies between `4∑_{m≥n}R_m − R_n > 0` and
`4∑_{m≥0}R_m + R_0 < 1/4` … Its second coordinate lies in `(1/4,3/4)`" — which is the sharper
*half*-square of the paper's declared coordinate square `(−1/4,1/4) × (1/4,3/4)` (§3.3, right
after `eq:chart-packing`); the packing inequality is `eq:chart-packing`,
`4∑R_n + R_0 < 1/4`. -/
theorem placementChart_subset_pairUnitIocBox : ScaleFamily.placementChart ⊆ pairUnitIocBox := by
  rintro x ⟨hx1, hx2⟩
  simp only [Set.mem_Ioo] at hx1 hx2
  exact ⟨⟨hx1.1, by linarith [hx1.2]⟩, ⟨by linarith [hx2.1], by linarith [hx2.2]⟩⟩

namespace ScaleFamily.TorusCellPlacement

open UnitBoxPeriodization

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The unit Jacobian and the invariant fundamental box -/

/-- **`det DΦ_t = 1` on the plane** (cf. the proof of `cor:ideal-growth`, which obtains it almost
everywhere from Liouville's formula).  Inside a buffer disc the
derivative is `FastDynamo/Dynamics/Flow/CellFlowMap.lean`'s
`R_{tω} ∘ (id + (t ∇ω) ⊗ J(x - p_n))`, whose determinant is `1` because `∇ω (J(x - p_n)) = 0`;
outside every buffer disc the flow is the identity. -/
theorem det_fderiv_planeTransverseFlow (t : ℝ) (x : ℝ × ℝ) :
    LinearMap.det ((fderiv ℝ (planeTransverseFlow h P angularSpeed t) x :
      (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  by_cases hbuf : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuf
    rw [fderiv_planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hn]
    exact det_fderiv_cellTransverseFlow h P angularSpeed n t x
  · push Not at hbuf
    rw [fderiv_planeTransverseFlow_eq_id_of_outside_buffers h P angularSpeed t hbuf]
    simp

/-- **`det DΦ_t = 1` for the `ℤ²`-equivariant plane flow.**  The periodisation has, near every
point, the differential of a single integer translate of the chart-side flow
(`fderiv_planePeriodizedTransverseFlow`), so its Jacobian determinant is again `1`. -/
theorem det_fderiv_planePeriodizedTransverseFlow (t : ℝ) (x : ℝ × ℝ) :
    LinearMap.det ((fderiv ℝ (planePeriodizedTransverseFlow h P angularSpeed t) x :
      (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
  rw [fderiv_planePeriodizedTransverseFlow h P angularSpeed t x]
  exact det_fderiv_planeTransverseFlow h P angularSpeed _ _

/-- On the fundamental box the periodisation is a single translate — the trivial one — so the
`ℤ²`-equivariant flow agrees there with the chart-side flow. -/
theorem planePeriodizedTransverseFlow_eq_of_mem_pairUnitIocBox (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ pairUnitIocBox) :
    planePeriodizedTransverseFlow h P angularSpeed t x =
      planeTransverseFlow h P angularSpeed t x := by
  have hdisp : planePeriodizedTransverseDisplacement h P angularSpeed t x =
      planeTransverseDisplacement h P angularSpeed t x :=
    periodization_eq_self_of_mem_Ioc
      (supportedInPlacementChart_planeTransverseDisplacement h P angularSpeed
        t).supportedInOpenUnitBox hx.1 hx.2
  rw [planePeriodizedTransverseFlow, hdisp, planeTransverseFlow_eq_add_displacement]

/-- **The fundamental box is invariant.**  A point of `(0,1]²` either lies in a buffer disc, which
the flow maps onto itself and which is contained in the placement chart, or lies outside every
buffer disc, where the flow is the identity. -/
theorem planePeriodizedTransverseFlow_mem_pairUnitIocBox (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ pairUnitIocBox) :
    planePeriodizedTransverseFlow h P angularSpeed t x ∈ pairUnitIocBox := by
  rw [planePeriodizedTransverseFlow_eq_of_mem_pairUnitIocBox h P angularSpeed t hx]
  by_cases hbuf : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuf
    exact placementChart_subset_pairUnitIocBox
      (P.bufferDisk_subset_chart n (planeTransverseFlow_mem_bufferDisk h P angularSpeed t hn))
  · push Not at hbuf
    rw [planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed t hbuf]
    exact hx

/-! ## The periodised plane-flow datum of the full flow -/

/-- **The periodised plane-flow datum of the paper's particle flow**: the `ℤ²`-equivariant
transverse flow `planePeriodizedTransverseFlow` together with the `ℤ²`-periodic axial shift
`planePeriodizedAxialShift`.  Every torus-level construction of the development —
`literalFlow`, its lift, measure preservation, `flowFDeriv`, `idealSymbol`, `idealTransport` —
is the corresponding generic construction of
`FastDynamo/Dynamics/Flow/PeriodizedFlowData.lean` at this datum.  The truncated tower of
`FastDynamo/Dynamics/Ideal/TruncatedFlow.lean` is the same constructions at `truncatedFlowData`. -/
def fullFlowData : PeriodizedPlaneFlowData where
  flow := planePeriodizedTransverseFlow h P angularSpeed
  shift := planePeriodizedAxialShift h P axialSpeed tau
  flow_add_int := planePeriodizedTransverseFlow_add_int h P angularSpeed
  isPeriodic_shift := isPeriodic_planePeriodizedAxialShift h P axialSpeed tau
  flow_zero := planePeriodizedTransverseFlow_zero h P angularSpeed
  shift_zero := planePeriodizedAxialShift_zero h P axialSpeed tau
  flow_comp := planePeriodizedTransverseFlow_planePeriodizedTransverseFlow h P angularSpeed
  shift_comp :=
    planePeriodizedAxialShift_planePeriodizedTransverseFlow_add h P angularSpeed axialSpeed tau
  differentiable_flow := differentiable_planePeriodizedTransverseFlow h P angularSpeed
  differentiable_shift := differentiable_planePeriodizedAxialShift h P axialSpeed tau
  det_fderiv_flow := det_fderiv_planePeriodizedTransverseFlow h P angularSpeed
  flow_mem_pairUnitIocBox := fun t _ hx ↦
    planePeriodizedTransverseFlow_mem_pairUnitIocBox h P angularSpeed t hx

/-! ## The transverse flow and the axial shift of the two-torus -/

/-- **The transverse flow of the two-torus**: the descent of the `ℤ²`-equivariant plane flow
along `transverseTorusPoint`.  It is the periodised flow that descends — the chart-side
`planeTransverseFlow` is supported in `placementChart` and is *not* `ℤ²`-equivariant.

It is written out rather than read off `fullFlowData` only so that it keeps the axial parameters
out of its signature; the two agree by definition. -/
def torusTransverseFlow (t : ℝ) : TransverseTorus → TransverseTorus :=
  transverseDescent fun x ↦
    transverseTorusPoint (planePeriodizedTransverseFlow h P angularSpeed t x)

/-- **The axial shift of the two-torus**: the descent of the `ℤ²`-periodic plane axial shift,
the second component of `eq:explicit-particle-flow`. -/
def torusAxialShift (t : ℝ) : TransverseTorus → ℝ :=
  transverseDescent (planePeriodizedAxialShift h P axialSpeed tau t)

/-- **Descent identity for the transverse flow**: the descent reproduces the periodised plane flow
on every representative. -/
theorem torusTransverseFlow_transverseTorusPoint (t : ℝ) (x : ℝ × ℝ) :
    torusTransverseFlow h P angularSpeed t (transverseTorusPoint x) =
      transverseTorusPoint (planePeriodizedTransverseFlow h P angularSpeed t x) :=
  transverseDescent_transverseTorusPoint
    (isPeriodic_transverseTorusPoint_planePeriodizedTransverseFlow h P angularSpeed t) x

/-- **Descent identity for the axial shift**. -/
theorem torusAxialShift_transverseTorusPoint (t : ℝ) (x : ℝ × ℝ) :
    torusAxialShift h P axialSpeed tau t (transverseTorusPoint x) =
      planePeriodizedAxialShift h P axialSpeed tau t x :=
  transverseDescent_transverseTorusPoint
    (isPeriodic_planePeriodizedAxialShift h P axialSpeed tau t) x

/-! ## The flow of the literal three-torus and its periodic lift -/

/-- **The particle flow of the literal three-torus** (`eq:explicit-particle-flow`, read as the
flow `Φ_t` defined at the start of §4): the transverse block flows by `torusTransverseFlow` and the
axial coordinate is translated by `torusAxialShift`, the translation being taken modulo one. -/
abbrev literalFlow (t : ℝ) (x : Torus 3) : Torus 3 :=
  (fullFlowData h P angularSpeed axialSpeed tau).literalFlow t x

/-- **The periodic lift of the flow** (proof of `cor:ideal-growth`): the plane flow in the first two
coordinates, the plane axial shift added to the third. -/
abbrev literalFlowLift (t : ℝ) (a : R3) : R3 :=
  (fullFlowData h P angularSpeed axialSpeed tau).literalFlowLift t a

/-- Transverse coordinates of the flow. -/
theorem literalFlow_apply_castSucc (t : ℝ) (x : Torus 3) (j : Fin 2) :
    literalFlow h P angularSpeed axialSpeed tau t x j.castSucc =
      torusTransverseFlow h P angularSpeed t (fun i : Fin 2 ↦ x i.castSucc) j :=
  (fullFlowData h P angularSpeed axialSpeed tau).literalFlow_apply_castSucc t x j

/-- Axial coordinate of the flow. -/
theorem literalFlow_apply_last (t : ℝ) (x : Torus 3) :
    literalFlow h P angularSpeed axialSpeed tau t x (Fin.last 2) =
      x (Fin.last 2) +
        ((torusAxialShift h P axialSpeed tau t
          (fun i : Fin 2 ↦ x i.castSucc) : ℝ) : UnitAddCircle) := rfl

/-- The transverse pair of the lift is the periodised plane flow of the transverse pair. -/
theorem literalFlowLift_pair (t : ℝ) (a : R3) :
    (literalFlowLift h P angularSpeed axialSpeed tau t a 0,
        literalFlowLift h P angularSpeed axialSpeed tau t a 1) =
      planePeriodizedTransverseFlow h P angularSpeed t (a 0, a 1) := rfl

/-- `literalFlowLift … t` is a periodic lift of `literalFlow … t`
(`IsLiteralTorusLift`, `FastDynamo/Dynamics/ParticleFlow.lean`).  Consumed by
`isIdealInductionGroup_idealGroup` (`FastDynamo/Dynamics/Ideal/IdealGroup.lean`). -/
theorem isLiteralTorusLift_literalFlow (t : ℝ) :
    IsLiteralTorusLift (literalFlow h P angularSpeed axialSpeed tau t)
      (literalFlowLift h P angularSpeed axialSpeed tau t) :=
  (fullFlowData h P angularSpeed axialSpeed tau).isLiteralTorusLift_literalFlow t

/-- The lift read through the quotient is the flow, in the direction the chain rule uses. -/
theorem literalTorusPoint_literalFlowLift (t : ℝ) (a : R3) :
    literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau t a) =
      literalFlow h P angularSpeed axialSpeed tau t (literalTorusPoint a) :=
  (fullFlowData h P angularSpeed axialSpeed tau).literalTorusPoint_literalFlowLift t a

/-! ## The group laws of the flow -/

/-- `Φ_0 = id` (the initial condition of the flow equation at the start of §4). -/
theorem literalFlow_zero (x : Torus 3) :
    literalFlow h P angularSpeed axialSpeed tau 0 x = x :=
  (fullFlowData h P angularSpeed axialSpeed tau).literalFlow_zero x

/-- **`Φ_t⁻¹ = Φ_{-t}`** (proof of `prop:particle-flow`), the clause `MainLagrangianClauses` asks
for. -/
theorem literalFlow_neg_literalFlow (t : ℝ) (x : Torus 3) :
    literalFlow h P angularSpeed axialSpeed tau (-t)
        (literalFlow h P angularSpeed axialSpeed tau t x) = x :=
  (fullFlowData h P angularSpeed axialSpeed tau).literalFlow_neg t x

/-- The iterate law `(Φ_t)^[m] = Φ_{m t}`, the form `lipschitzWith_literalFlow_iterate`
(`FastDynamo/Dynamics/Flow/Entropy.lean`) feeds to the entropy criterion. -/
theorem literalFlow_iterate (t : ℝ) (m : ℕ) :
    (literalFlow h P angularSpeed axialSpeed tau t)^[m] =
      literalFlow h P angularSpeed axialSpeed tau (m * t) :=
  (fullFlowData h P angularSpeed axialSpeed tau).literalFlow_iterate t m

/-- The flow is continuous at every time. -/
theorem continuous_literalFlow (t : ℝ) :
    Continuous (literalFlow h P angularSpeed axialSpeed tau t) :=
  (fullFlowData h P angularSpeed axialSpeed tau).continuous_literalFlow t

/-! ## `eq:explicit-particle-flow` and the fixed points, at torus level -/

/-- On the fundamental box the periodised axial shift is the chart-side one, the axial shift
being supported in the placement chart.  Axial companion of
`planePeriodizedTransverseFlow_eq_of_mem_pairUnitIocBox`. -/
theorem planePeriodizedAxialShift_eq_of_mem_pairUnitIocBox (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ pairUnitIocBox) :
    planePeriodizedAxialShift h P axialSpeed tau t x =
      planeAxialShift h P axialSpeed tau t x :=
  periodization_eq_self_of_mem_Ioc
    (supportedInPlacementChart_planeAxialShift h P axialSpeed tau t).supportedInOpenUnitBox
    hx.1 hx.2

/-- **`eq:explicit-particle-flow` for the flow of the literal three-torus**:

```
  Φ_t(y, x₃) = (p_n + R_{t ω_n(r)}(y - p_n),  x₃ + t g_n(r))        (y ∈ D(p_n, R_n)),
```

the second component modulo one.  The hypotheses say that `y` is a representative of the
horizontal block of `x` inside the fundamental box `(0,1]²` and that it lies in the `n`-th
buffer disc (the paper states the formula for `y ∈ D(p_n, R_n)` in its coordinate chart; every
buffer disc lies in the fundamental box, so this is the same set of points); the profiles `ω_n`,
`g_n` are `cellAngularSpeed`, `cellAxialSpeed`, which are `eq:particle-cell-profiles`.

The development *defines* the flow cell by cell, so this is a chain of the four reductions:
the descent identities of `torusTransverseFlow`/`torusAxialShift`, the agreement of the
periodisation with the chart-side maps on the fundamental box, the single-cell reductions
`planeTransverseFlow_eq_cell_of_mem_bufferDisk`/`planeAxialShift_eq_cell_of_mem_bufferDisk`,
and the closed form `cellTransverseFlow_eq`.  Since the flow is *the* particle flow of the
velocity (`ParticleFlowUniqueness.lean`), the display is a theorem about the paper's
`Φ_t` and not only about a named function. -/
theorem literalFlow_eq_cell_of_mem_bufferDisk (t : ℝ) {n : ℕ} {x : Torus 3} {y : ℝ × ℝ}
    (hbox : y ∈ pairUnitIocBox)
    (hy : transverseTorusPoint y = fun j : Fin 2 ↦ x j.castSucc)
    (hn : y ∈ P.scaleFamily.bufferDisk n) :
    (∀ j : Fin 2,
        literalFlow h P angularSpeed axialSpeed tau t x j.castSucc =
          transverseTorusPoint
            (P.scaleFamily.cellCenter n +
              planeRotate (t * cellAngularSpeed h P angularSpeed n y)
                (y - P.scaleFamily.cellCenter n)) j) ∧
      literalFlow h P angularSpeed axialSpeed tau t x (Fin.last 2) =
        x (Fin.last 2) +
          ((t * cellAxialSpeed h P axialSpeed tau n y : ℝ) : UnitAddCircle) := by
  constructor
  · intro j
    rw [literalFlow_apply_castSucc, ← hy, torusTransverseFlow_transverseTorusPoint,
      planePeriodizedTransverseFlow_eq_of_mem_pairUnitIocBox h P angularSpeed t hbox,
      planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hn,
      cellTransverseFlow_eq]
  · rw [literalFlow_apply_last, ← hy, torusAxialShift_transverseTorusPoint,
      planePeriodizedAxialShift_eq_of_mem_pairUnitIocBox h P axialSpeed tau t hbox,
      planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hn,
      cellAxialDisplacement]

/-- **The fixed points of the flow on the literal three-torus** (statement of
`prop:particle-flow`: "Every point outside the cells, on their boundaries, and of the
accumulation circle `{p_∞} × T` is fixed"; the cells are the buffer discs `D(p_n, R_n)`).

The hypothesis is that *every* integer translate of the chosen horizontal representative `y`
misses every buffer disc — which is what "outside the cells" means on the torus, the
discs being drawn in the chart and the flow being the `ℤ²`-periodisation.  Boundary points are
covered: `bufferDisk` is the *open* disc, so `dist y (p_n) = R_n` already puts `y` outside it.

This is the paper's own route (proof of `prop:particle-flow`: "The velocity vanishes outside of
the cells. Hence, the flow is the identity there"). -/
theorem literalFlow_eq_self_of_forall_not_mem_bufferDisk (t : ℝ) {x : Torus 3} {y : ℝ × ℝ}
    (hy : transverseTorusPoint y = fun j : Fin 2 ↦ x j.castSucc)
    (hout : ∀ (k : ℤ × ℤ) (n : ℕ),
      (y - ((k.1 : ℝ), (k.2 : ℝ))) ∉ P.scaleFamily.bufferDisk n) :
    literalFlow h P angularSpeed axialSpeed tau t x = x := by
  refine (fullFlowData h P angularSpeed axialSpeed tau).literalFlow_eq_self ?_ ?_
  · change torusTransverseFlow h P angularSpeed t (fun j : Fin 2 ↦ x j.castSucc) =
      fun j : Fin 2 ↦ x j.castSucc
    rw [← hy, torusTransverseFlow_transverseTorusPoint]
    have hzero : planePeriodizedTransverseDisplacement h P angularSpeed t y = 0 :=
      periodization_eq_zero fun k ↦
        planeTransverseDisplacement_eq_zero_of_outside_buffers h P angularSpeed t (hout k)
    rw [planePeriodizedTransverseFlow, hzero, add_zero]
  · change torusAxialShift h P axialSpeed tau t (fun j : Fin 2 ↦ x j.castSucc) = 0
    rw [← hy, torusAxialShift_transverseTorusPoint]
    exact periodization_eq_zero fun k ↦
      planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t (hout k)

/-- No integer translate of the accumulation point `p_∞ = (0, 1/2)` lies in a buffer disc: every
buffer disc is contained in the placement chart `(0, 1/4) × (1/4, 3/4)`, whose first factor
contains no integer, while the first coordinate of every translate of `p_∞` is an integer. -/
theorem forall_not_mem_bufferDisk_accumulationPoint_sub_intCast (k : ℤ × ℤ) (n : ℕ) :
    (FullVelocityConcrete.accumulationPoint - ((k.1 : ℝ), (k.2 : ℝ))) ∉
      P.scaleFamily.bufferDisk n := by
  intro hmem
  have hchart := P.bufferDisk_subset_chart n hmem
  rw [ScaleFamily.placementChart, Set.mem_prod] at hchart
  have h1 : (0 : ℝ) < -(k.1 : ℝ) ∧ -(k.1 : ℝ) < 1 / 4 := by
    simpa [FullVelocityConcrete.accumulationPoint] using hchart.1
  have hgt : (0 : ℤ) < -k.1 := by exact_mod_cast h1.1
  have hone : (1 : ℤ) ≤ -k.1 := by omega
  have hcast : (1 : ℝ) ≤ ((-k.1 : ℤ) : ℝ) := by exact_mod_cast hone
  push_cast at hcast
  linarith [h1.2]

/-- **The accumulation circle `{p_∞} × T` is fixed** (statement of `prop:particle-flow`), at
torus level: every point of `Torus 3` whose
horizontal block is the class of the accumulation point is a fixed point of every time map. -/
theorem literalFlow_eq_self_of_accumulationPoint (t : ℝ) {x : Torus 3}
    (hx : transverseTorusPoint FullVelocityConcrete.accumulationPoint =
      fun j : Fin 2 ↦ x j.castSucc) :
    literalFlow h P angularSpeed axialSpeed tau t x = x :=
  literalFlow_eq_self_of_forall_not_mem_bufferDisk h P angularSpeed axialSpeed tau t hx
    (forall_not_mem_bufferDisk_accumulationPoint_sub_intCast h P)

/-! ## The Lipschitz constant of the flow -/

/-- The transverse flow of the two-torus inherits the plane constant **unchanged**: the quotient
map is `1`-Lipschitz and `lipschitzWith_of_factorsThrough_transverseTorusPoint` loses nothing. -/
theorem lipschitzWith_torusTransverseFlow (htau : 0 ≤ tau) (t : ℝ) :
    LipschitzWith (flowLipschitzBoundNN h P angularSpeed axialSpeed tau t)
      (torusTransverseFlow h P angularSpeed t) := by
  have hcomp : LipschitzWith
      (flowLipschitzBoundNN h P angularSpeed axialSpeed tau t)
      (fun x : ℝ × ℝ ↦
        transverseTorusPoint (planePeriodizedTransverseFlow h P angularSpeed t x)) := by
    have hc := lipschitzWith_transverseTorusPoint.comp
      (lipschitzWith_planePeriodizedTransverseFlow h P angularSpeed axialSpeed tau htau t)
    rwa [one_mul] at hc
  exact lipschitzWith_of_factorsThrough_transverseTorusPoint hcomp
    (torusTransverseFlow_transverseTorusPoint h P angularSpeed t)

/-- The axial shift of the two-torus inherits the plane constant `|t| · flowLipschitzSlope`. -/
theorem lipschitzWith_torusAxialShift (htau : 0 ≤ tau) (t : ℝ) :
    LipschitzWith (‖t‖₊ * flowLipschitzSlopeNN h P angularSpeed axialSpeed tau)
      (torusAxialShift h P axialSpeed tau t) :=
  lipschitzWith_of_factorsThrough_transverseTorusPoint
    (lipschitzWith_planePeriodizedAxialShift h P angularSpeed axialSpeed tau htau t)
    (torusAxialShift_transverseTorusPoint h P axialSpeed tau t)

/-- The axial coordinate's constant `1 + |t| · flowLipschitzSlope` is dominated by the transverse
one: `flowLipschitzBound … t` is twice `1 + |t| · flowLipschitzSlope …`, so the `max` of
`dist_pi_le_iff` costs no extra factor. -/
theorem one_add_mul_flowLipschitzSlope_le_flowLipschitzBound (htau : 0 ≤ tau) (t : ℝ) :
    1 + |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  have hnn : 0 ≤ |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau :=
    mul_nonneg (abs_nonneg t)
      (flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau)
  rw [flowLipschitzBound]
  linarith

/-- `Lip(Φ_t) ≤ flowLipschitzBound … t`, the first half of
`eq:linear-flow-lipschitz` read on `Torus 3`.  The three coordinates are glued by
`dist_pi_le_iff`: the transverse ones carry the plane constant unchanged, and the axial one costs
`1 + |t| · flowLipschitzSlope`, translation on `UnitAddCircle` being an isometry and the coercion
`ℝ → UnitAddCircle` being `1`-Lipschitz. -/
theorem lipschitzWith_literalFlow (htau : 0 ≤ tau) (t : ℝ) :
    LipschitzWith (flowLipschitzBoundNN h P angularSpeed axialSpeed tau t)
      (literalFlow h P angularSpeed axialSpeed tau t) := by
  have hCnn : 0 ≤ flowLipschitzBound h P angularSpeed axialSpeed tau t :=
    flowLipschitzBound_nonneg h P angularSpeed axialSpeed tau htau t
  have hBnn : 0 ≤ |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau :=
    mul_nonneg (abs_nonneg t)
      (flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau)
  have hBC := one_add_mul_flowLipschitzSlope_le_flowLipschitzBound h P angularSpeed axialSpeed
    tau htau t
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau]
  have hdrop : dist (fun j : Fin 2 ↦ x j.castSucc) (fun j : Fin 2 ↦ y j.castSucc) ≤ dist x y := by
    simpa using lipschitzWith_dropAxial.dist_le_mul x y
  refine (dist_pi_le_iff (by positivity)).2 fun j ↦ ?_
  refine Fin.lastCases ?_ ?_ j
  · rw [literalFlow_apply_last, literalFlow_apply_last]
    have haxial : dist
        ((torusAxialShift h P axialSpeed tau t
          (fun i : Fin 2 ↦ x i.castSucc) : ℝ) : UnitAddCircle)
        ((torusAxialShift h P axialSpeed tau t
          (fun i : Fin 2 ↦ y i.castSucc) : ℝ) : UnitAddCircle) ≤
        (|t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) * dist x y := by
      refine le_trans (by
        simpa using lipschitzWith_unitAddCircle_coe.dist_le_mul
          (torusAxialShift h P axialSpeed tau t (fun i : Fin 2 ↦ x i.castSucc))
          (torusAxialShift h P axialSpeed tau t
            (fun i : Fin 2 ↦ y i.castSucc))) ?_
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hdrop hBnn)
      have hlip := (lipschitzWith_torusAxialShift h P angularSpeed axialSpeed tau htau
        t).dist_le_mul (fun i : Fin 2 ↦ x i.castSucc) (fun i : Fin 2 ↦ y i.castSucc)
      rwa [coe_nnnorm_mul_flowLipschitzSlopeNN h P angularSpeed axialSpeed tau htau] at hlip
    calc dist (x (Fin.last 2) + _) (y (Fin.last 2) + _)
        ≤ dist (x (Fin.last 2) +
              ((torusAxialShift h P axialSpeed tau t
                (fun i : Fin 2 ↦ x i.castSucc) : ℝ) : UnitAddCircle))
            (y (Fin.last 2) +
              ((torusAxialShift h P axialSpeed tau t
                (fun i : Fin 2 ↦ x i.castSucc) : ℝ) : UnitAddCircle)) +
          dist (y (Fin.last 2) +
              ((torusAxialShift h P axialSpeed tau t
                (fun i : Fin 2 ↦ x i.castSucc) : ℝ) : UnitAddCircle))
            (y (Fin.last 2) +
              ((torusAxialShift h P axialSpeed tau t
                (fun i : Fin 2 ↦ y i.castSucc) : ℝ) : UnitAddCircle)) := dist_triangle _ _ _
      _ = dist (x (Fin.last 2)) (y (Fin.last 2)) +
            dist ((torusAxialShift h P axialSpeed tau t
                (fun i : Fin 2 ↦ x i.castSucc) : ℝ) : UnitAddCircle)
              ((torusAxialShift h P axialSpeed tau t
                (fun i : Fin 2 ↦ y i.castSucc) : ℝ) : UnitAddCircle) := by
            rw [dist_add_right, dist_add_left]
      _ ≤ dist x y +
            (|t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) * dist x y :=
            add_le_add (dist_le_pi_dist x y _) haxial
      _ = (1 + |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) * dist x y := by ring
      _ ≤ flowLipschitzBound h P angularSpeed axialSpeed tau t * dist x y :=
            mul_le_mul_of_nonneg_right hBC dist_nonneg
  · intro i
    rw [literalFlow_apply_castSucc, literalFlow_apply_castSucc]
    refine le_trans (dist_le_pi_dist _ _ i) ?_
    have hlip := (lipschitzWith_torusTransverseFlow h P angularSpeed axialSpeed tau htau
      t).dist_le_mul (fun i : Fin 2 ↦ x i.castSucc) (fun i : Fin 2 ↦ y i.castSucc)
    rw [coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau] at hlip
    exact le_trans hlip (mul_le_mul_of_nonneg_left hdrop hCnn)

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
