/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.ParticleFlow
public import LeanPool.FastDynamo.Global.TransverseFundamentalBox
public import LeanPool.FastDynamo.Analysis.PlaneJacobian

/-!
# The periodised plane-flow datum, and the torus tower it generates

The paper's particle flow `Φ_t : T³ → T³` (the flow defined at the start of §4, given in closed
form by `eq:explicit-particle-flow`) is assembled from two maps of the plane: a
`ℤ²`-equivariant transverse flow and a `ℤ²`-periodic axial shift.  The development needs the flow
**twice**: once for the full displacement `∑' n, d_n` and once for the truncation
`∑ n ∈ Finset.range N, d_n` that `FastDynamo/Dynamics/Ideal/TruncatedPlaneFlow.lean` builds, and
the two plane-level families differ only in the index set.  Everything above the periodisation —
the descent to `TransverseTorus`, the skew product on `Torus 3`, the periodic lift, measure
preservation, the block differential, the complexified symbol and the Cauchy transport — uses
nothing about the index set.

This module isolates what those constructions consume: a `PeriodizedPlaneFlowData`, the
bundle of the two plane maps together with the twelve facts the tower is built from.  The tower
itself is developed once, generically in `D : PeriodizedPlaneFlowData`, and the two towers of the
development are specialisations:

* `fullFlowData` (`FastDynamo/Dynamics/Flow/TorusFlow.lean`), at `planePeriodizedTransverseFlow`
  and `planePeriodizedAxialShift`;
* `truncatedFlowData` (`FastDynamo/Dynamics/Ideal/TruncatedFlow.lean`), at
  `planePeriodizedTruncatedFlow` and `planePeriodizedTruncatedShift`.

## Contents

* `PeriodizedPlaneFlowData` and the plane-level consequences of its fields (the inverse, the
  continuity of both maps, the descent hypothesis `isPeriodic_transverseTorusPoint_flow`).
* `torusFlow`, `torusShift` — the descents along `transverseTorusPoint`, with the descent
  identities, the time origin, the group law, the axial cocycle, the inverse and continuity.
* `literalFlow`, `literalFlowLift` — the flow of `Torus 3` and its periodic lift, with
  `isLiteralTorusLift_literalFlow` (`IsLiteralTorusLift` of
  `FastDynamo/Dynamics/ParticleFlow.lean`), `literalFlow_zero`, `literalFlow_comp`,
  `literalFlow_neg` (`Φ_t⁻¹ = Φ_{-t}`, proof of `prop:particle-flow`), `literalFlow_iterate`,
  continuity, the group law of the lift itself, and the two comparison lemmas `literalFlow_eq_of`,
  `literalFlow_eq_self` that a consumer comparing two towers needs.
* `measurePreserving_literalFlow` (measure preservation, proof of `cor:ideal-growth`) by the
  three-step route: unit Jacobian on the plane, invariance of the fundamental box
  `pairUnitIocBox`, and `MeasureTheory.MeasurePreserving.skew_product` for the axial shear; then the
  transport corollaries `literalFlowMeasurableEquiv`, `measurableEmbedding_literalFlow` and
  `quasiMeasurePreserving_literalFlow`.

The differential `DΦ_t`, its complexification and the Cauchy transport are the second half of the
generic tower and live in `FastDynamo/Dynamics/Flow/PeriodizedFlowSymbol.lean`.

Liouville's formula is *not* proved anywhere: the datum carries `det_fderiv_flow` as a field, and
each instance discharges it pointwise from the closed rank-one derivative formula of
`FastDynamo/Dynamics/Flow/CellFlowMap.lean`.  (The proof of `cor:ideal-growth` obtains
`det DΦ_t = 1` almost everywhere from Liouville's formula and `div u = 0`, and measure
preservation from the area formula for the bi-Lipschitz map `Φ_t`.)
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- **A periodised plane-flow datum**: the pair of plane maps the particle flow of the literal
three-torus is assembled from, together with the facts the assembly consumes.

`flow t` is the `ℤ²`-equivariant transverse flow of the plane and `shift t` the `ℤ²`-periodic
axial shift, so that the flow of `Torus 3` is the skew product

```
  Φ_t(y, x₃) = (descent of flow t at y, x₃ + descent of shift t at y).
```

The fields are exactly what the torus tower uses: equivariance and periodicity (for the descent),
the group law and the axial cocycle (for `Φ_s ∘ Φ_t = Φ_{s+t}`), differentiability of both maps
(for the block differential and, through it, for continuity), the unit Jacobian and the
invariance of the fundamental box `pairUnitIocBox` (for measure preservation).  No bound on the
differentials is a field: the two towers carry different hypotheses on their parameters, so the
uniform bounds are generic *lemmas* with the constant as a variable
(`FastDynamo/Dynamics/Flow/PeriodizedFlowSymbol.lean`). -/
structure PeriodizedPlaneFlowData where
  /-- The `ℤ²`-equivariant transverse flow of the plane. -/
  flow : ℝ → (ℝ × ℝ) → ℝ × ℝ
  /-- The `ℤ²`-periodic axial shift of the plane. -/
  shift : ℝ → (ℝ × ℝ) → ℝ
  /-- **`ℤ²`-equivariance of the flow**: `flow t (x + m) = flow t x + m`. -/
  flow_add_int : ∀ (t : ℝ) (x : ℝ × ℝ) (m n : ℤ),
    flow t (x.1 + m, x.2 + n) = ((flow t x).1 + m, (flow t x).2 + n)
  /-- **`ℤ²`-periodicity of the axial shift.** -/
  isPeriodic_shift : ∀ t : ℝ, LatticePeriodic.IsPeriodic (shift t)
  /-- At time zero the flow is the identity. -/
  flow_zero : ∀ x : ℝ × ℝ, flow 0 x = x
  /-- At time zero the axial shift vanishes. -/
  shift_zero : ∀ x : ℝ × ℝ, shift 0 x = 0
  /-- **The group law of the plane flow.** -/
  flow_comp : ∀ (s t : ℝ) (x : ℝ × ℝ), flow s (flow t x) = flow (s + t) x
  /-- **The axial cocycle**: the shifts compose along the flow. -/
  shift_comp : ∀ (s t : ℝ) (x : ℝ × ℝ), shift s (flow t x) + shift t x = shift (s + t) x
  /-- The flow is differentiable everywhere. -/
  differentiable_flow : ∀ t : ℝ, Differentiable ℝ (flow t)
  /-- The axial shift is differentiable everywhere. -/
  differentiable_shift : ∀ t : ℝ, Differentiable ℝ (shift t)
  /-- **`det Dflow_t = 1`**, the pointwise replacement of Liouville's formula. -/
  det_fderiv_flow : ∀ (t : ℝ) (x : ℝ × ℝ),
    LinearMap.det ((fderiv ℝ (flow t) x : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1
  /-- **The fundamental box `(0,1]²` is invariant.** -/
  flow_mem_pairUnitIocBox : ∀ (t : ℝ) {x : ℝ × ℝ},
    x ∈ pairUnitIocBox → flow t x ∈ pairUnitIocBox

namespace PeriodizedPlaneFlowData

variable (D : PeriodizedPlaneFlowData)

/-! ## The plane level -/

/-- The flow at `-t` undoes the flow at `t`. -/
@[simp] theorem flow_neg (t : ℝ) (x : ℝ × ℝ) : D.flow (-t) (D.flow t x) = x := by
  rw [D.flow_comp, neg_add_cancel, D.flow_zero]

/-- The flow at `t` undoes the flow at `-t`. -/
theorem flow_neg' (t : ℝ) (x : ℝ × ℝ) : D.flow t (D.flow (-t) x) = x := by
  rw [D.flow_comp, add_neg_cancel, D.flow_zero]

/-- The plane flow is continuous at every time. -/
theorem continuous_flow (t : ℝ) : Continuous (D.flow t) :=
  (D.differentiable_flow t).continuous

/-- The axial shift is continuous at every time. -/
theorem continuous_shift (t : ℝ) : Continuous (D.shift t) :=
  (D.differentiable_shift t).continuous

/-- **The flow descends to the transverse two-torus**: the composite with the quotient map is
`ℤ²`-periodic, which is the hypothesis of `transverseDescent`. -/
theorem isPeriodic_transverseTorusPoint_flow (t : ℝ) :
    LatticePeriodic.IsPeriodic fun x : ℝ × ℝ ↦ transverseTorusPoint (D.flow t x) := by
  intro x m n
  change transverseTorusPoint (D.flow t ((x.1 + m, x.2 + n))) = _
  rw [D.flow_add_int]
  exact transverseTorusPoint_add_int _ m n

/-! ## The transverse flow and the axial shift of the two-torus -/

/-- **The transverse flow of the two-torus**: the descent of the `ℤ²`-equivariant plane flow
along `transverseTorusPoint`. -/
def torusFlow (t : ℝ) : TransverseTorus → TransverseTorus :=
  transverseDescent fun x ↦ transverseTorusPoint (D.flow t x)

/-- **The axial shift of the two-torus**: the descent of the `ℤ²`-periodic plane axial shift,
the second component of `eq:explicit-particle-flow`. -/
def torusShift (t : ℝ) : TransverseTorus → ℝ :=
  transverseDescent (D.shift t)

/-- **Descent identity for the transverse flow**: the descent reproduces the plane flow on every
representative. -/
theorem torusFlow_transverseTorusPoint (t : ℝ) (x : ℝ × ℝ) :
    D.torusFlow t (transverseTorusPoint x) = transverseTorusPoint (D.flow t x) :=
  transverseDescent_transverseTorusPoint (D.isPeriodic_transverseTorusPoint_flow t) x

/-- **Descent identity for the axial shift.** -/
theorem torusShift_transverseTorusPoint (t : ℝ) (x : ℝ × ℝ) :
    D.torusShift t (transverseTorusPoint x) = D.shift t x :=
  transverseDescent_transverseTorusPoint (D.isPeriodic_shift t) x

/-- At time zero the transverse flow of the two-torus is the identity. -/
@[simp] theorem torusFlow_zero (y : TransverseTorus) : D.torusFlow 0 y = y := by
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [D.torusFlow_transverseTorusPoint, D.flow_zero]

/-- At time zero the axial shift of the two-torus vanishes. -/
@[simp] theorem torusShift_zero (y : TransverseTorus) : D.torusShift 0 y = 0 := by
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [D.torusShift_transverseTorusPoint, D.shift_zero]

/-- **The group law of the transverse flow of the two-torus.** -/
theorem torusFlow_comp (s t : ℝ) (y : TransverseTorus) :
    D.torusFlow s (D.torusFlow t y) = D.torusFlow (s + t) y := by
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [D.torusFlow_transverseTorusPoint, D.torusFlow_transverseTorusPoint,
    D.torusFlow_transverseTorusPoint, D.flow_comp]

/-- **The axial cocycle on the two-torus**: the axial shifts compose along the transverse flow. -/
theorem torusShift_comp (s t : ℝ) (y : TransverseTorus) :
    D.torusShift s (D.torusFlow t y) + D.torusShift t y = D.torusShift (s + t) y := by
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [D.torusFlow_transverseTorusPoint, D.torusShift_transverseTorusPoint,
    D.torusShift_transverseTorusPoint, D.torusShift_transverseTorusPoint, D.shift_comp]

/-- The transverse flow of the two-torus is continuous at every time. -/
theorem continuous_torusFlow (t : ℝ) : Continuous (D.torusFlow t) :=
  continuous_transverseDescent
    (lipschitzWith_transverseTorusPoint.continuous.comp (D.continuous_flow t))
    (D.isPeriodic_transverseTorusPoint_flow t)

/-- The axial shift of the two-torus is continuous at every time. -/
theorem continuous_torusShift (t : ℝ) : Continuous (D.torusShift t) :=
  continuous_transverseDescent (D.continuous_shift t) (D.isPeriodic_shift t)

/-! ## The flow of the literal three-torus and its periodic lift -/

/-- **The particle flow of the literal three-torus** (`eq:explicit-particle-flow`, read as the
flow `Φ_t` defined at the start of §4): the transverse block flows by `torusFlow` and the axial
coordinate is translated by `torusShift`, the translation being taken modulo one. -/
def literalFlow (t : ℝ) (x : Torus 3) : Torus 3 :=
  Fin.snoc (D.torusFlow t fun j : Fin 2 ↦ x j.castSucc)
    (x (Fin.last 2) + ((D.torusShift t (fun j : Fin 2 ↦ x j.castSucc) : ℝ) : UnitAddCircle))

/-- **The periodic lift of the flow** (proof of `cor:ideal-growth`): the plane flow in the first two
coordinates, the plane axial shift added to the third. -/
def literalFlowLift (t : ℝ) (a : R3) : R3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![(D.flow t (a 0, a 1)).1, (D.flow t (a 0, a 1)).2, a 2 + D.shift t (a 0, a 1)]

/-- Transverse coordinates of the flow. -/
@[simp] theorem literalFlow_apply_castSucc (t : ℝ) (x : Torus 3) (j : Fin 2) :
    D.literalFlow t x j.castSucc = D.torusFlow t (fun i : Fin 2 ↦ x i.castSucc) j := by
  simp [literalFlow]

/-- Axial coordinate of the flow. -/
@[simp] theorem literalFlow_apply_last (t : ℝ) (x : Torus 3) :
    D.literalFlow t x (Fin.last 2) =
      x (Fin.last 2) +
        ((D.torusShift t (fun i : Fin 2 ↦ x i.castSucc) : ℝ) : UnitAddCircle) := rfl

/-- The transverse block of the flow is the transverse flow of the transverse block. -/
theorem literalFlow_castSucc_eq (t : ℝ) (x : Torus 3) :
    (fun j : Fin 2 ↦ D.literalFlow t x j.castSucc) =
      D.torusFlow t (fun i : Fin 2 ↦ x i.castSucc) :=
  funext fun j ↦ D.literalFlow_apply_castSucc t x j

/-- **The flow in the product coordinates** of `productToLiteral`: it is the skew product of the
transverse flow of the two-torus with the axial translation by `torusShift`, which is the shape
`MeasureTheory.MeasurePreserving.skew_product` consumes in `measurePreserving_literalFlow`. -/
theorem literalFlow_productToLiteral (t : ℝ) (y : TransverseTorus) (s : AxialCircle) :
    D.literalFlow t (productToLiteral (y, s)) =
      productToLiteral (D.torusFlow t y, s + ((D.torusShift t y : ℝ) : UnitAddCircle)) := by
  have hinit : (fun j : Fin 2 ↦ (productToLiteral (y, s)) j.castSucc) = y := by
    funext j
    simp
  have hlast : (productToLiteral (y, s)) (Fin.last 2) = s := by
    rw [productToLiteral_apply]
    rfl
  rw [literalFlow, hinit, hlast, productToLiteral_apply]

/-- First coordinate of the lift. -/
@[simp] theorem literalFlowLift_apply_zero (t : ℝ) (a : R3) :
    D.literalFlowLift t a 0 = (D.flow t (a 0, a 1)).1 := rfl

/-- Second coordinate of the lift. -/
@[simp] theorem literalFlowLift_apply_one (t : ℝ) (a : R3) :
    D.literalFlowLift t a 1 = (D.flow t (a 0, a 1)).2 := rfl

/-- Third coordinate of the lift. -/
@[simp] theorem literalFlowLift_apply_two (t : ℝ) (a : R3) :
    D.literalFlowLift t a 2 = a 2 + D.shift t (a 0, a 1) := rfl

/-- The transverse pair of the lift is the plane flow of the transverse pair. -/
theorem literalFlowLift_pair (t : ℝ) (a : R3) :
    (D.literalFlowLift t a 0, D.literalFlowLift t a 1) = D.flow t (a 0, a 1) := rfl

/-- **The group law of the lift**, the form the chain rule for `DΦ` consumes. -/
theorem literalFlowLift_comp (s t : ℝ) (a : R3) :
    D.literalFlowLift s (D.literalFlowLift t a) = D.literalFlowLift (s + t) a := by
  have hpair := D.literalFlowLift_pair t a
  have hco := D.shift_comp s t (a 0, a 1)
  refine r3_ext ?_ ?_ ?_
  · rw [D.literalFlowLift_apply_zero, hpair, D.flow_comp, D.literalFlowLift_apply_zero]
  · rw [D.literalFlowLift_apply_one, hpair, D.flow_comp, D.literalFlowLift_apply_one]
  · rw [D.literalFlowLift_apply_two, hpair, D.literalFlowLift_apply_two,
      D.literalFlowLift_apply_two, add_assoc, ← hco]
    ring

/-- `literalFlowLift D t` is a periodic lift of `literalFlow D t` (`IsLiteralTorusLift`,
`FastDynamo/Dynamics/ParticleFlow.lean`). -/
theorem isLiteralTorusLift_literalFlow (t : ℝ) :
    IsLiteralTorusLift (D.literalFlow t) (D.literalFlowLift t) := by
  intro a
  have htr : (fun j : Fin 2 ↦ literalTorusPoint a j.castSucc)
      = transverseTorusPoint (a 0, a 1) := literalTorusPoint_castSucc a
  refine funext fun j ↦ ?_
  refine Fin.lastCases ?_ ?_ j
  · rw [D.literalFlow_apply_last, htr, D.torusShift_transverseTorusPoint]
    change ((a 2 : ℝ) : UnitAddCircle) + _ = _
    rw [← AddCircle.coe_add]
    rfl
  · intro i
    rw [D.literalFlow_apply_castSucc, htr, D.torusFlow_transverseTorusPoint]
    fin_cases i <;> rfl

/-- The lift read through the quotient is the flow, in the direction the chain rule uses. -/
theorem literalTorusPoint_literalFlowLift (t : ℝ) (a : R3) :
    literalTorusPoint (D.literalFlowLift t a) = D.literalFlow t (literalTorusPoint a) :=
  (D.isLiteralTorusLift_literalFlow t a).symm

/-! ## The group laws of the flow -/

/-- `Φ_0 = id` (the initial condition of the flow equation at the start of §4). -/
@[simp] theorem literalFlow_zero (x : Torus 3) : D.literalFlow 0 x = x := by
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := by simp
  rw [literalFlow, D.torusFlow_zero, D.torusShift_zero, h0, add_zero]
  exact Fin.snoc_init_self x

/-- **Two data with the same transverse action at a point agree there.**  The flow of `Torus 3`
sees the datum only through the two descents at the transverse block of `x`, so this is what a
consumer comparing two towers — the full one and a truncation — needs. -/
theorem literalFlow_eq_of (D' : PeriodizedPlaneFlowData) {s t : ℝ} {x : Torus 3}
    (hflow : D.torusFlow t (fun j : Fin 2 ↦ x j.castSucc) =
      D'.torusFlow s (fun j : Fin 2 ↦ x j.castSucc))
    (hshift : D.torusShift t (fun j : Fin 2 ↦ x j.castSucc) =
      D'.torusShift s (fun j : Fin 2 ↦ x j.castSucc)) :
    D.literalFlow t x = D'.literalFlow s x := by
  rw [literalFlow, literalFlow, hflow, hshift]

/-- **The flow fixes a point whose transverse block is fixed and carries no axial shift.** -/
theorem literalFlow_eq_self {t : ℝ} {x : Torus 3}
    (hflow : D.torusFlow t (fun j : Fin 2 ↦ x j.castSucc) = fun j : Fin 2 ↦ x j.castSucc)
    (hshift : D.torusShift t (fun j : Fin 2 ↦ x j.castSucc) = 0) :
    D.literalFlow t x = x := by
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := by simp
  rw [literalFlow, hflow, hshift, h0, add_zero]
  exact Fin.snoc_init_self x

/-- The group law `Φ_s ∘ Φ_t = Φ_{s+t}`. -/
theorem literalFlow_comp (s t : ℝ) (x : Torus 3) :
    D.literalFlow s (D.literalFlow t x) = D.literalFlow (s + t) x := by
  have hco := D.torusShift_comp s t (fun i : Fin 2 ↦ x i.castSucc)
  refine funext fun j ↦ ?_
  refine Fin.lastCases ?_ ?_ j
  · rw [D.literalFlow_apply_last, D.literalFlow_apply_last, D.literalFlow_castSucc_eq,
      D.literalFlow_apply_last, add_assoc]
    congr 1
    rw [← AddCircle.coe_add, ← hco, add_comm]
  · intro i
    rw [D.literalFlow_apply_castSucc, D.literalFlow_castSucc_eq, D.literalFlow_apply_castSucc,
      D.torusFlow_comp]

/-- **`Φ_t⁻¹ = Φ_{-t}`** (proof of `prop:particle-flow`), the clause `MainLagrangianClauses` asks
for. -/
@[simp] theorem literalFlow_neg (t : ℝ) (x : Torus 3) :
    D.literalFlow (-t) (D.literalFlow t x) = x := by
  rw [D.literalFlow_comp, neg_add_cancel, D.literalFlow_zero]

/-- The flow at `t` undoes the flow at `-t`. -/
theorem literalFlow_neg' (t : ℝ) (x : Torus 3) :
    D.literalFlow t (D.literalFlow (-t) x) = x := by
  rw [D.literalFlow_comp, add_neg_cancel, D.literalFlow_zero]

/-- The iterate law `(Φ_t)^[m] = Φ_{m t}`, the form the entropy criterion consumes. -/
theorem literalFlow_iterate (t : ℝ) (m : ℕ) :
    (D.literalFlow t)^[m] = D.literalFlow (m * t) := by
  induction m with
  | zero => funext x; simp
  | succ m ih =>
      funext x
      have hcast : t + (m : ℝ) * t = ((m + 1 : ℕ) : ℝ) * t := by push_cast; ring
      rw [Function.iterate_succ_apply', ih, D.literalFlow_comp, hcast]

/-- The flow is continuous at every time. -/
theorem continuous_literalFlow (t : ℝ) : Continuous (D.literalFlow t) := by
  have hdrop : Continuous fun x : Torus 3 ↦ (fun j : Fin 2 ↦ x j.castSucc) :=
    lipschitzWith_dropAxial.continuous
  refine continuous_pi fun j ↦ ?_
  refine Fin.lastCases ?_ ?_ j
  · simp only [literalFlow_apply_last]
    exact (continuous_apply (Fin.last 2)).add
      (lipschitzWith_unitAddCircle_coe.continuous.comp ((D.continuous_torusShift t).comp hdrop))
  · intro i
    simp only [literalFlow_apply_castSucc]
    exact (continuous_apply i).comp ((D.continuous_torusFlow t).comp hdrop)

/-! ## Step 1 of measure preservation: the plane -/

/-- **The plane flow preserves Lebesgue measure**: its inverse is the flow at `-t`, which is
differentiable with unit Jacobian (cf. the proof of `cor:ideal-growth`). -/
theorem measurePreserving_flow (t : ℝ) :
    MeasurePreserving (D.flow t) (volume : Measure (ℝ × ℝ)) volume :=
  planeMeasurePreserving_of_det_fderiv_eq_one (D.continuous_flow t).measurable
    (D.differentiable_flow (-t)) (D.flow_neg t) (D.flow_neg' t) (D.det_fderiv_flow (-t))

/-- The fundamental box is its own preimage: the flow maps it *bijectively* onto itself, the
backward inclusion coming from the flow at `-t`. -/
theorem preimage_pairUnitIocBox_flow (t : ℝ) :
    D.flow t ⁻¹' pairUnitIocBox = pairUnitIocBox := by
  ext x
  constructor
  · intro hx
    have hback := D.flow_mem_pairUnitIocBox (-t) hx
    rwa [D.flow_neg] at hback
  · intro hx
    exact D.flow_mem_pairUnitIocBox t hx

/-- The plane flow preserves Lebesgue measure *restricted to the fundamental box*, because the
box is its own preimage. -/
theorem measurePreserving_flow_pairUnitIocBox (t : ℝ) :
    MeasurePreserving (D.flow t) (volume.restrict pairUnitIocBox)
      (volume.restrict pairUnitIocBox) := by
  have hmp := (D.measurePreserving_flow t).restrict_preimage measurableSet_pairUnitIocBox
  rwa [D.preimage_pairUnitIocBox_flow] at hmp

/-! ## Step 2: descent to the transverse two-torus -/

/-- The descended transverse flow of the two-torus is measurable, being continuous. -/
theorem measurable_torusFlow (t : ℝ) : Measurable (D.torusFlow t) :=
  (D.continuous_torusFlow t).measurable

/-- **The transverse flow of the two-torus preserves the transverse volume.**  Conjugate step 1
through the measure-preserving quotient map `transverseTorusPoint` of the invariant fundamental
box (cf. the proof of `cor:ideal-growth`). -/
theorem measurePreserving_torusFlow (t : ℝ) :
    MeasurePreserving (D.torusFlow t) transverseMeasure transverseMeasure := by
  have hcomp := measurePreserving_transverseTorusPoint.comp
    (D.measurePreserving_flow_pairUnitIocBox t)
  have hfun : transverseTorusPoint ∘ D.flow t = D.torusFlow t ∘ transverseTorusPoint :=
    funext fun x ↦ (D.torusFlow_transverseTorusPoint t x).symm
  rw [hfun] at hcomp
  refine ⟨D.measurable_torusFlow t, ?_⟩
  calc Measure.map (D.torusFlow t) transverseMeasure
      = Measure.map (D.torusFlow t)
          (Measure.map transverseTorusPoint (volume.restrict pairUnitIocBox)) := by
        rw [measurePreserving_transverseTorusPoint.map_eq]
    _ = Measure.map (D.torusFlow t ∘ transverseTorusPoint)
          (volume.restrict pairUnitIocBox) :=
        Measure.map_map (D.measurable_torusFlow t)
          measurePreserving_transverseTorusPoint.measurable
    _ = transverseMeasure := hcomp.map_eq

/-! ## Step 3: the axial shear, and the flow on the literal three-torus -/

/-- The descended axial shift of the two-torus is measurable, being continuous. -/
theorem measurable_torusShift (t : ℝ) : Measurable (D.torusShift t) :=
  (D.continuous_torusShift t).measurable

/-- **The skew product preserves the product volume.**  The base map is the transverse flow of
step 2 and each fibre map is a translation of the axial circle, which preserves the axial Haar
measure; `MeasureTheory.MeasurePreserving.skew_product` assembles the two. -/
theorem measurePreserving_torusSkewFlow (t : ℝ) :
    MeasurePreserving
      (fun q : ProductTorus3 =>
        (D.torusFlow t q.1, q.2 + ((D.torusShift t q.1 : ℝ) : AxialCircle)))
      productMeasure productMeasure := by
  refine (D.measurePreserving_torusFlow t).skew_product
    (g := fun y s => s + ((D.torusShift t y : ℝ) : AxialCircle)) ?_ ?_
  · exact measurable_snd.add
      ((AddCircle.measurable_mk'.comp (D.measurable_torusShift t)).comp measurable_fst)
  · filter_upwards with y
    exact (measurePreserving_add_right axialMeasure
      ((D.torusShift t y : ℝ) : AxialCircle)).map_eq

/-- **The particle flow preserves the volume of the literal three-torus.**  The flow is the skew
product of step 3 read through the measure-preserving identification `productToLiteral` of the
product model with `Torus 3`.  This is the `measurePreserving` field of `IsIdealInductionGroup`
(proof of `cor:ideal-growth`). -/
theorem measurePreserving_literalFlow (t : ℝ) :
    MeasurePreserving (D.literalFlow t) (volume : Measure (Torus 3)) volume := by
  have hcomp := measurePreserving_productToLiteral.comp (D.measurePreserving_torusSkewFlow t)
  have hfun : (⇑productToLiteral ∘ fun q : ProductTorus3 =>
      (D.torusFlow t q.1, q.2 + ((D.torusShift t q.1 : ℝ) : AxialCircle))) =
      D.literalFlow t ∘ ⇑productToLiteral :=
    funext fun q ↦ (D.literalFlow_productToLiteral t q.1 q.2).symm
  rw [hfun] at hcomp
  have hback := hcomp.comp (measurePreserving_productToLiteral.symm productToLiteral)
  have hid : (D.literalFlow t ∘ ⇑productToLiteral) ∘ ⇑productToLiteral.symm =
      D.literalFlow t := by
    funext x
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  rwa [hid] at hback

/-! ## Transport corollaries -/

/-- The particle flow is measurable, being continuous. -/
theorem measurable_literalFlow (t : ℝ) : Measurable (D.literalFlow t) :=
  (D.continuous_literalFlow t).measurable

/-- **The particle flow as a measurable equivalence of `Torus 3`.**  Its inverse is the flow at
`-t` (`Φ_t^{-1} = Φ_{-t}`, proof of `prop:particle-flow`). -/
def literalFlowMeasurableEquiv (t : ℝ) : Torus 3 ≃ᵐ Torus 3 where
  toFun := D.literalFlow t
  invFun := D.literalFlow (-t)
  left_inv := D.literalFlow_neg t
  right_inv := D.literalFlow_neg' t
  measurable_toFun := D.measurable_literalFlow t
  measurable_invFun := D.measurable_literalFlow (-t)

/-- The particle flow is a measurable embedding: it is a measurable bijection with measurable
inverse. -/
theorem measurableEmbedding_literalFlow (t : ℝ) :
    MeasurableEmbedding (D.literalFlow t) :=
  (D.literalFlowMeasurableEquiv t).measurableEmbedding

/-- The particle flow is quasi measure preserving.  This is the form in which almost-everywhere
statements are pulled back along `Φ_t` in the Cauchy formula `eq:ideal-cauchy-formula`. -/
theorem quasiMeasurePreserving_literalFlow (t : ℝ) :
    QuasiMeasurePreserving (D.literalFlow t) (volume : Measure (Torus 3)) volume :=
  (D.measurePreserving_literalFlow t).quasiMeasurePreserving

end PeriodizedPlaneFlowData

end

end FastDynamo
