/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Flow.TorusFlow
public import LeanPool.FastDynamo.Dynamics.Flow.PeriodizedFlowSymbol

/-!
# The derivative flow `DΦ_t` of the explicit particle flow

The paper reads the derivative of the flow on a periodic lift ("the periodic lift of `u` and the
corresponding equivariant lift of `Φ_t`", proof of `cor:ideal-growth`): `DΦ_t(a)` is the Fréchet
derivative at `a ∈ ℝ³` of the lift `literalFlowLift … t` of
`FastDynamo/Dynamics/Flow/TorusFlow.lean`.  The lift is the *skew product*

```
  a ↦ (planePeriodizedTransverseFlow t (a₁, a₂), a₃ + planePeriodizedAxialShift t (a₁, a₂)),
```

so its differential is the block matrix

```
  DΦ_t(a) = [[ D(planePeriodizedTransverseFlow t)(y) , 0 ],
             [ D(planePeriodizedAxialShift t)(y)    , 1 ]],        y = (a₁, a₂)
```

`FastDynamo/Dynamics/Flow/PeriodizedFlowSymbol.lean` builds that block matrix, its descent to the
torus and its complexification generically over a `PeriodizedPlaneFlowData`; `flowFDeriv`,
`flowFDerivC` and their properties are those constructions at `fullFlowData`.

What this module adds on top of the generic tower:

* the explicit constants `flowDerivativeBound … t = 2 · flowLipschitzBound … t
  = 4 (1 + |t| · flowLipschitzSlope …)` and `flowComplexDerivativeBound … t
  = 6 · flowDerivativeBound … t`, with the arithmetic the per-datum bounds of
  `cor:ideal-growth` need,
  and the uniform bound `norm_flowFDerivC_le` of the complexified derivative flow;
* the continuity of the differential **in the time variable**, which the truncated tower does not
  need and which is therefore not generic: inside a buffer disc the transverse block is the
  closed rank-one formula of `FastDynamo/Dynamics/Flow/CellFlowMap.lean` and the axial block is
  linear in `t`, outside every buffer disc they are the identity and zero.  This is the input of
  `strongly_continuous_idealTransport` (`FastDynamo/Dynamics/Ideal/StrongContinuity.lean`).

**The constant is not `flowLipschitzBound`.**  `flowLipschitzBound … t` bounds the differential of
the plane flow for the *sup* norm of `ℝ × ℝ`; the block matrix acts on the *Euclidean* `ℝ³`, and
assembling three sup-normed coordinates into a Euclidean vector costs the factor `√3 ≤ 2`.  So
the derivative flow is bounded by `flowDerivativeBound … t = 2 · flowLipschitzBound … t` rather
than by `flowLipschitzBound … t` itself; it is the same explicit `C (1 + |t|)` shape, and
`IdealGroup.lean` absorbs the factor into `dynamicalCL`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped NNReal Topology

open ScaleFamily.TorusCellPlacement

/-! ## The derivative flow -/

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete
open UnitBoxPeriodization

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- **The derivative flow read at a point of the plane**: the block matrix of the module
docstring at the transverse coordinates `y`: the derivative `DΦ_t` of
`eq:flow-variational-equation`, in closed form. -/
abbrev flowFDerivPlane (t : ℝ) (y : ℝ × ℝ) : R3 →L[ℝ] R3 :=
  (fullFlowData h P angularSpeed axialSpeed tau).flowFDerivPlane t y

/-- **The derivative flow `DΦ_t`** (proof of `cor:ideal-growth`): the block matrix of the
periodised plane differentials, read at the canonical `(0,1]³` representative of the torus
point.  By `flowFDeriv_literalTorusPoint` the representative is immaterial, and by
`hasFDerivAt_literalFlowLift` this is the Fréchet derivative of the periodic lift at every
point. -/
abbrev flowFDeriv (t : ℝ) (x : Torus 3) : R3 →L[ℝ] R3 :=
  (fullFlowData h P angularSpeed axialSpeed tau).flowFDeriv t x

/-- The derivative flow in closed block form. -/
theorem flowFDerivPlane_eq (t : ℝ) (y : ℝ × ℝ) :
    flowFDerivPlane h P angularSpeed axialSpeed tau t y =
      flowBlockCLM (fderiv ℝ (planePeriodizedTransverseFlow h P angularSpeed t) y)
        (fderiv ℝ (planePeriodizedAxialShift h P axialSpeed tau t) y) := rfl

/-- The derivative flow of the torus is the plane one at the canonical representative. -/
theorem flowFDeriv_eq (t : ℝ) (x : Torus 3) :
    flowFDeriv h P angularSpeed axialSpeed tau t x =
      flowFDerivPlane h P angularSpeed axialSpeed tau t (literalIocPair x) := rfl

/-- `flowFDeriv … t (π a)` is the Fréchet derivative at `a` of the periodic lift
`literalFlowLift … t` of `Φ_t`, at *every* point of `ℝ³`.  The proof of `cor:ideal-growth`
obtains `DΦ_t` almost everywhere from the Cauchy–Lipschitz theorem, Rademacher's theorem and the
chain rule; here the closed formula gives it everywhere, with no appeal to Rademacher's
theorem. -/
theorem hasFDerivAt_literalFlowLift (t : ℝ) (a : R3) :
    HasFDerivAt (literalFlowLift h P angularSpeed axialSpeed tau t)
      (flowFDeriv h P angularSpeed axialSpeed tau t (literalTorusPoint a)) a :=
  (fullFlowData h P angularSpeed axialSpeed tau).hasFDerivAt_literalFlowLift t a

/-! ### The uniform bound -/

/-- **The uniform bound on the derivative flow**: `flowDerivativeBound … t = 4 (1 + |t| · slope)`,
twice the plane bound `flowLipschitzBound … t` of `Flow/PlaneFlowLipschitz.lean`.  The extra
factor `2` is the cost of assembling three
sup-normed coordinates of the chart plane into one Euclidean vector of `ℝ³`; it is the same loss
as the `2` of `globalVelocityLipschitzBound`. -/
def flowDerivativeBound (t : ℝ) : ℝ :=
  2 * flowLipschitzBound h P angularSpeed axialSpeed tau t

/-- The derivative bound in closed form. -/
theorem flowDerivativeBound_eq (t : ℝ) :
    flowDerivativeBound h P angularSpeed axialSpeed tau t =
      4 * (1 + |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) := by
  rw [flowDerivativeBound, flowLipschitzBound]
  ring

/-- The derivative bound only sees `|t|`, so it is even in the time. -/
theorem flowDerivativeBound_neg (t : ℝ) :
    flowDerivativeBound h P angularSpeed axialSpeed tau (-t) =
      flowDerivativeBound h P angularSpeed axialSpeed tau t := by
  rw [flowDerivativeBound_eq, flowDerivativeBound_eq, abs_neg]

/-- The derivative bound is at least `4`, in particular at least `1`. -/
theorem four_le_flowDerivativeBound (htau : 0 ≤ tau) (t : ℝ) :
    4 ≤ flowDerivativeBound h P angularSpeed axialSpeed tau t := by
  have := two_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau t
  rw [flowDerivativeBound]
  linarith

/-- The derivative bound is at least `1`. -/
theorem one_le_flowDerivativeBound (htau : 0 ≤ tau) (t : ℝ) :
    1 ≤ flowDerivativeBound h P angularSpeed axialSpeed tau t :=
  le_trans (by norm_num) (four_le_flowDerivativeBound h P angularSpeed axialSpeed tau htau t)

/-- The derivative bound is nonnegative. -/
theorem flowDerivativeBound_nonneg (htau : 0 ≤ tau) (t : ℝ) :
    0 ≤ flowDerivativeBound h P angularSpeed axialSpeed tau t :=
  le_trans (by norm_num) (one_le_flowDerivativeBound h P angularSpeed axialSpeed tau htau t)

/-- The axial block's bound, in the `‖·‖ + 1 ≤ C` shape the block estimate of
`FastDynamo/Analysis/R3BlockComplexify.lean` consumes. -/
theorem norm_fderiv_planePeriodizedAxialShift_add_one_le (htau : 0 ≤ tau) (t : ℝ) (y : ℝ × ℝ) :
    ‖fderiv ℝ (planePeriodizedAxialShift h P axialSpeed tau t) y‖ + 1 ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  have hphi := norm_fderiv_planePeriodizedAxialShift_le h P angularSpeed axialSpeed tau htau t y
  have hslope := one_add_mul_flowLipschitzSlope_le_flowLipschitzBound h P angularSpeed axialSpeed
    tau htau t
  linarith

/-! ### Continuity in the time variable -/

/-- The chart-side transverse differential is continuous in the time: inside a buffer disc it is
the closed rank-one formula of `Flow/CellFlowMap.lean`, outside every buffer disc it is the
identity. -/
theorem continuous_fderiv_planeTransverseFlow_time (x : ℝ × ℝ) :
    Continuous fun t : ℝ ↦ fderiv ℝ (planeTransverseFlow h P angularSpeed t) x := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    have hEq : ∀ t : ℝ, fderiv ℝ (planeTransverseFlow h P angularSpeed t) x =
        (planeRotateCLM (t * cellAngularSpeed h P angularSpeed n x)).comp
          (ContinuousLinearMap.id ℝ (ℝ × ℝ) +
            t • (fderiv ℝ (cellAngularSpeed h P angularSpeed n) x).smulRight
              (perp (x - P.scaleFamily.cellCenter n))) := by
      intro t
      rw [fderiv_planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hn,
        fderiv_cellTransverseFlow]
      congr 1
      congr 1
      refine ContinuousLinearMap.ext fun z ↦ ?_
      simp [smul_smul]
    simp only [hEq]
    have h1 : Continuous fun t : ℝ ↦
        planeRotateCLM (t * cellAngularSpeed h P angularSpeed n x) :=
      continuous_planeRotateCLM.comp (continuous_id.mul continuous_const)
    have h2 : Continuous fun t : ℝ ↦ (ContinuousLinearMap.id ℝ (ℝ × ℝ) +
        t • (fderiv ℝ (cellAngularSpeed h P angularSpeed n) x).smulRight
          (perp (x - P.scaleFamily.cellCenter n))) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ)).continuous₂.comp (h1.prodMk h2)
  · have hout := not_exists.1 hbuffer
    have hEq : ∀ t : ℝ, fderiv ℝ (planeTransverseFlow h P angularSpeed t) x =
        ContinuousLinearMap.id ℝ (ℝ × ℝ) := fun t ↦
      fderiv_planeTransverseFlow_eq_id_of_outside_buffers h P angularSpeed t hout
    simp only [hEq]
    exact continuous_const

/-- The chart-side axial differential is continuous in the time: it is linear in `t` inside a
buffer disc and zero outside every buffer disc. -/
theorem continuous_fderiv_planeAxialShift_time (x : ℝ × ℝ) :
    Continuous fun t : ℝ ↦ fderiv ℝ (planeAxialShift h P axialSpeed tau t) x := by
  by_cases hbuffer : ∃ n : ℕ, x ∈ P.scaleFamily.bufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    have hEq : ∀ t : ℝ, fderiv ℝ (planeAxialShift h P axialSpeed tau t) x =
        t • fderiv ℝ (cellAxialSpeed h P axialSpeed tau n) x := by
      intro t
      rw [fderiv_planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hn,
        fderiv_cellAxialDisplacement]
    simp only [hEq]
    exact continuous_id.smul continuous_const
  · have hout := not_exists.1 hbuffer
    have hEq : ∀ t : ℝ, fderiv ℝ (planeAxialShift h P axialSpeed tau t) x = 0 := fun t ↦
      fderiv_planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t hout
    simp only [hEq]
    exact continuous_const

/-- The periodised transverse differential is continuous in the time. -/
theorem continuous_fderiv_planePeriodizedTransverseFlow_time (x : ℝ × ℝ) :
    Continuous fun t : ℝ ↦
      fderiv ℝ (planePeriodizedTransverseFlow h P angularSpeed t) x := by
  simp only [fderiv_planePeriodizedTransverseFlow]
  exact continuous_fderiv_planeTransverseFlow_time h P angularSpeed (x - chartTranslation x)

/-- The periodised axial differential is continuous in the time. -/
theorem continuous_fderiv_planePeriodizedAxialShift_time (x : ℝ × ℝ) :
    Continuous fun t : ℝ ↦ fderiv ℝ (planePeriodizedAxialShift h P axialSpeed tau t) x := by
  simp only [fderiv_planePeriodizedAxialShift]
  exact continuous_fderiv_planeAxialShift_time h P axialSpeed tau (x - chartTranslation x)

/-- The derivative flow at a fixed plane point is continuous in the time. -/
theorem continuous_flowFDerivPlane_time (y : ℝ × ℝ) :
    Continuous fun t : ℝ ↦ flowFDerivPlane h P angularSpeed axialSpeed tau t y := by
  have hfun : (fun t : ℝ ↦ flowFDerivPlane h P angularSpeed axialSpeed tau t y) =
      fun t : ℝ ↦ flowBlockCLM (fderiv ℝ (planePeriodizedTransverseFlow h P angularSpeed t) y)
        (fderiv ℝ (planePeriodizedAxialShift h P axialSpeed tau t) y) := rfl
  rw [hfun]
  exact continuous_flowBlockCLM_comp
    (continuous_fderiv_planePeriodizedTransverseFlow_time h P angularSpeed y)
    (continuous_fderiv_planePeriodizedAxialShift_time h P axialSpeed tau y)

/-- **The derivative flow at a fixed torus point is continuous in the time.**  This is the input
of `strongly_continuous_idealTransport` (`FastDynamo/Dynamics/Ideal/StrongContinuity.lean`). -/
theorem continuous_flowFDeriv_time (x : Torus 3) :
    Continuous fun t : ℝ ↦ flowFDeriv h P angularSpeed axialSpeed tau t x :=
  continuous_flowFDerivPlane_time h P angularSpeed axialSpeed tau _

/-! ### The complexified derivative flow -/

/-- **The complexified derivative flow** `DΦ_t ⊗ ℂ`, the symbol of the Cauchy transport operator
`eq:ideal-cauchy-formula`: the `ℂ`-linear endomorphism of `ℂ³` with the real
matrix entries of `flowFDeriv … t x`. -/
abbrev flowFDerivC (t : ℝ) (x : Torus 3) : C3 →L[ℂ] C3 :=
  (fullFlowData h P angularSpeed axialSpeed tau).flowFDerivC t x

/-- The complexified derivative flow is the complexification of the real one. -/
theorem flowFDerivC_eq (t : ℝ) (x : Torus 3) :
    flowFDerivC h P angularSpeed axialSpeed tau t x =
      r3Complexify (flowFDeriv h P angularSpeed axialSpeed tau t x) := rfl

/-- **The uniform bound on the complexified derivative flow**: the `L^∞` symbol bound consumed by
`norm_idealSymbol_le` (`FastDynamo/Dynamics/Ideal/CauchyOperator.lean`).  The factor `6` is the
coordinate count of a matrix row times the Euclidean assembly factor `2`. -/
def flowComplexDerivativeBound (t : ℝ) : ℝ :=
  6 * flowDerivativeBound h P angularSpeed axialSpeed tau t

/-- The complex derivative bound in closed form. -/
theorem flowComplexDerivativeBound_eq (t : ℝ) :
    flowComplexDerivativeBound h P angularSpeed axialSpeed tau t =
      24 * (1 + |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau) := by
  rw [flowComplexDerivativeBound, flowDerivativeBound_eq]
  ring

/-- The complex derivative bound is nonnegative. -/
theorem flowComplexDerivativeBound_nonneg (htau : 0 ≤ tau) (t : ℝ) :
    0 ≤ flowComplexDerivativeBound h P angularSpeed axialSpeed tau t := by
  have := flowDerivativeBound_nonneg h P angularSpeed axialSpeed tau htau t
  rw [flowComplexDerivativeBound]
  linarith

/-- **The uniform bound on the complexified derivative flow.** -/
theorem norm_flowFDerivC_le (htau : 0 ≤ tau) (t : ℝ) (x : Torus 3) :
    ‖flowFDerivC h P angularSpeed axialSpeed tau t x‖ ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau t :=
  (fullFlowData h P angularSpeed axialSpeed tau).norm_flowFDerivC_le
    (norm_fderiv_planePeriodizedTransverseFlow_le h P angularSpeed axialSpeed tau htau t)
    (norm_fderiv_planePeriodizedAxialShift_add_one_le h P angularSpeed axialSpeed tau htau t) x

/-- The complexified derivative flow is measurable. -/
theorem measurable_flowFDerivC (t : ℝ) :
    Measurable (flowFDerivC h P angularSpeed axialSpeed tau t) :=
  (fullFlowData h P angularSpeed axialSpeed tau).measurable_flowFDerivC t

/-- The complexified derivative flow at a fixed torus point is continuous in the time. -/
theorem continuous_flowFDerivC_time (x : Torus 3) :
    Continuous fun t : ℝ ↦ flowFDerivC h P angularSpeed axialSpeed tau t x :=
  continuous_r3Complexify.comp
    (continuous_flowFDeriv_time h P angularSpeed axialSpeed tau x)

/-- `DΦ_0 ⊗ ℂ = id`. -/
theorem flowFDerivC_zero :
    flowFDerivC h P angularSpeed axialSpeed tau 0 =
      fun _ ↦ ContinuousLinearMap.id ℂ C3 :=
  (fullFlowData h P angularSpeed axialSpeed tau).flowFDerivC_zero

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
