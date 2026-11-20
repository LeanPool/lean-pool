/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedPlaneFlow
public import LeanPool.FastDynamo.Dynamics.Flow.MeasurePreserving
public import LeanPool.FastDynamo.Dynamics.Flow.FlowDerivative

/-!
# The truncated particle flow of the three-torus, its measure preservation and its differential

`FastDynamo/Dynamics/Ideal/TruncatedPlaneFlow.lean` builds the truncated plane flow
`planePeriodizedTruncatedFlow … N t` and its axial shift, the `ℤ²`-equivariant maps obtained by
keeping only the first `N` cells of `eq:explicit-particle-flow`.  They are a
`PeriodizedPlaneFlowData` (`FastDynamo/Dynamics/Flow/PeriodizedFlowData.lean`) exactly as the
full plane flow is, so the whole torus tower — the descent, the skew product on `Torus 3`, the
periodic lift, measure preservation, the block differential and its complexification — is the
generic one at `truncatedFlowData`, and this module only names the specialisations:

* `literalTruncatedFlow … N t : Torus 3 → Torus 3` with its periodic lift
  `literalTruncatedFlowLift … N t : R3 → R3` (`isLiteralTorusLift_literalTruncatedFlow`);
* `measurePreserving_literalTruncatedFlow` and `measurableEmbedding_literalTruncatedFlow`, which
  the truncated Cauchy transport consumes (the proof of `cor:ideal-growth`);
* `truncatedFlowFDeriv`, `truncatedFlowFDerivC` and the uniform symbol bound
  `norm_truncatedFlowFDerivC_le`, *with the untruncated constant*
  `flowComplexDerivativeBound` of `FastDynamo/Dynamics/Flow/FlowDerivative.lean` — the bound is
  uniform in `N`.

What is **not** generic, and is proved here, is everything that sees the truncation:

* `contDiff_literalTruncatedFlowLift`, the second of the two hypotheses the lemma
  `inner_gradient_mFourier_comp_eq_zero_of_mem_literalSolenoidalSubspace` of
  `FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean` imposes on a test flow — this is the
  hypothesis the truncation is introduced to satisfy (the paper instead extends the divergence
  identity to `ψ ∘ Φ_t ∈ H¹` by density, in the proof of `cor:ideal-growth`).  A *finite* sum of
  compactly supported smooth cell displacements has no accumulation point, so nothing obstructs
  smoothness;
  the untruncated lift is only differentiable at `accumulationPoint`;
* the two plane-level facts the datum needs — the invariance of the fundamental box
  `pairUnitIocBox` and the differentiability of the periodised truncated shift;
* the plane-level bounds on the truncated differentials, which go through the retained buffer
  discs one at a time.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory

open scoped Topology

namespace ScaleFamily.TorusCellPlacement

open UnitBoxPeriodization

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The plane-level facts the datum needs -/

/-- On the fundamental box the periodisation is the trivial translate. -/
theorem planePeriodizedTruncatedFlow_eq_of_mem_pairUnitIocBox (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ pairUnitIocBox) :
    planePeriodizedTruncatedFlow h P angularSpeed N t x =
      planeTruncatedTransverseFlow h P angularSpeed N t x := by
  have hdisp : planePeriodizedTruncatedDisplacement h P angularSpeed N t x =
      planeTruncatedTransverseDisplacement h P angularSpeed N t x :=
    periodization_eq_self_of_mem_Ioc
      (supportedInPlacementChart_planeTruncatedTransverseDisplacement h P angularSpeed N
        t).supportedInOpenUnitBox hx.1 hx.2
  rw [planePeriodizedTruncatedFlow, hdisp, planeTruncatedTransverseFlow_eq_add_displacement]

/-- **The fundamental box is invariant under the truncated flow.** -/
theorem planePeriodizedTruncatedFlow_mem_pairUnitIocBox (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ pairUnitIocBox) :
    planePeriodizedTruncatedFlow h P angularSpeed N t x ∈ pairUnitIocBox := by
  rw [planePeriodizedTruncatedFlow_eq_of_mem_pairUnitIocBox h P angularSpeed N t hx]
  by_cases hbuf : ∃ k : ℕ, x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuf
    exact placementChart_subset_pairUnitIocBox
      (P.bufferDisk_subset_chart k
        (planeTruncatedTransverseFlow_mem_bufferDisk h P angularSpeed N t hk))
  · rw [planeTruncatedTransverseFlow_eq_self h P angularSpeed N t
      fun n _ hmem ↦ hbuf ⟨n, hmem⟩]
    exact hx

/-- The periodised truncated axial shift is differentiable everywhere. -/
theorem differentiable_planePeriodizedTruncatedShift (N : ℕ) (t : ℝ) :
    Differentiable ℝ (planePeriodizedTruncatedShift h P axialSpeed tau N t) :=
  (contDiff_planePeriodizedTruncatedShift h P axialSpeed tau N t).differentiable (by simp)

/-! ## The periodised plane-flow datum of the truncated flow -/

/-- **The periodised plane-flow datum of the truncated particle flow**: the same bundle as
`fullFlowData` (`FastDynamo/Dynamics/Flow/TorusFlow.lean`) at the truncated plane maps.  The two
differ only in the index set of the displacement sum — `Finset.range N` instead of all of `ℕ` —
and every fact the torus tower consumes holds for both, which is why the tower is proved once. -/
def truncatedFlowData (N : ℕ) : PeriodizedPlaneFlowData where
  flow := planePeriodizedTruncatedFlow h P angularSpeed N
  shift := planePeriodizedTruncatedShift h P axialSpeed tau N
  flow_add_int := planePeriodizedTruncatedFlow_add_int h P angularSpeed N
  isPeriodic_shift := isPeriodic_planePeriodizedTruncatedShift h P axialSpeed tau N
  flow_zero := planePeriodizedTruncatedFlow_zero h P angularSpeed N
  shift_zero := planePeriodizedTruncatedShift_zero h P axialSpeed tau N
  flow_comp := planePeriodizedTruncatedFlow_comp h P angularSpeed N
  shift_comp := planePeriodizedTruncatedShift_comp h P angularSpeed axialSpeed tau N
  differentiable_flow := differentiable_planePeriodizedTruncatedFlow h P angularSpeed N
  differentiable_shift := differentiable_planePeriodizedTruncatedShift h P axialSpeed tau N
  det_fderiv_flow := det_fderiv_planePeriodizedTruncatedFlow h P angularSpeed N
  flow_mem_pairUnitIocBox := fun t _ hx ↦
    planePeriodizedTruncatedFlow_mem_pairUnitIocBox h P angularSpeed N t hx

/-! ## The truncated flow of the tori -/

/-- **The truncated transverse flow of the two-torus**: the descent of the `ℤ²`-equivariant
truncated plane flow.  It is written out rather than read off `truncatedFlowData` only so that it
keeps the axial parameters out of its signature; the two agree by definition. -/
def torusTruncatedFlow (N : ℕ) (t : ℝ) : TransverseTorus → TransverseTorus :=
  transverseDescent fun x ↦
    transverseTorusPoint (planePeriodizedTruncatedFlow h P angularSpeed N t x)

/-- **The truncated axial shift of the two-torus.** -/
def torusTruncatedShift (N : ℕ) (t : ℝ) : TransverseTorus → ℝ :=
  transverseDescent (planePeriodizedTruncatedShift h P axialSpeed tau N t)

/-- Descent identity for the truncated transverse flow. -/
theorem torusTruncatedFlow_transverseTorusPoint (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    torusTruncatedFlow h P angularSpeed N t (transverseTorusPoint x) =
      transverseTorusPoint (planePeriodizedTruncatedFlow h P angularSpeed N t x) :=
  transverseDescent_transverseTorusPoint
    (isPeriodic_transverseTorusPoint_planePeriodizedTruncatedFlow h P angularSpeed N t) x

/-- Descent identity for the truncated axial shift. -/
theorem torusTruncatedShift_transverseTorusPoint (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    torusTruncatedShift h P axialSpeed tau N t (transverseTorusPoint x) =
      planePeriodizedTruncatedShift h P axialSpeed tau N t x :=
  transverseDescent_transverseTorusPoint
    (isPeriodic_planePeriodizedTruncatedShift h P axialSpeed tau N t) x

/-- **The truncated particle flow of the literal three-torus** `Φ^{(N)}_t`. -/
abbrev literalTruncatedFlow (N : ℕ) (t : ℝ) (x : Torus 3) : Torus 3 :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).literalFlow t x

/-- **The periodic lift of the truncated flow** (periodic lifts as in the proof of
`cor:ideal-growth`). -/
abbrev literalTruncatedFlowLift (N : ℕ) (t : ℝ) (a : R3) : R3 :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).literalFlowLift t a

/-- **`literalTruncatedFlowLift … N t` is a periodic lift of `literalTruncatedFlow … N t`.**  This
is the first of the two hypotheses the orthogonality lemma (S1) of `GradientOrthogonality`
imposes on a test flow. -/
theorem isLiteralTorusLift_literalTruncatedFlow (N : ℕ) (t : ℝ) :
    IsLiteralTorusLift (literalTruncatedFlow h P angularSpeed axialSpeed tau N t)
      (literalTruncatedFlowLift h P angularSpeed axialSpeed tau N t) :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).isLiteralTorusLift_literalFlow t

/-- **The truncated lift is `C^∞`.**  This is the second hypothesis the orthogonality
lemma (S1) of `GradientOrthogonality` imposes: a *finite* sum of compactly supported smooth cell
displacements has no accumulation point, so nothing obstructs smoothness (contrast the untruncated
lift, which is only differentiable at `accumulationPoint`). -/
theorem contDiff_literalTruncatedFlowLift (N : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (literalTruncatedFlowLift h P angularSpeed axialSpeed tau N t) := by
  have hfun : literalTruncatedFlowLift h P angularSpeed axialSpeed tau N t = fun a : R3 ↦
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![(planePeriodizedTruncatedFlow h P angularSpeed N t (a 0, a 1)).1,
          (planePeriodizedTruncatedFlow h P angularSpeed N t (a 0, a 1)).2,
          a 2 + planePeriodizedTruncatedShift h P axialSpeed tau N t (a 0, a 1)] := rfl
  rw [hfun]
  have hflow := (contDiff_planePeriodizedTruncatedFlow h P angularSpeed N t).comp
    (contDiff_r3Pair (n := (⊤ : ℕ∞)))
  exact contDiff_r3_of_contDiff_coords (contDiff_fst.comp hflow) (contDiff_snd.comp hflow)
    (contDiff_r3Axial.add ((contDiff_planePeriodizedTruncatedShift h P axialSpeed tau N t).comp
      (contDiff_r3Pair (n := (⊤ : ℕ∞)))))

/-! ## Measure preservation -/

/-- **The truncated particle flow preserves the volume of the literal three-torus** — the
measure-preservation clause for `Φ^{(N)}`, proved exactly as `measurePreserving_literalFlow`
(the proof of `cor:ideal-growth`). -/
theorem measurePreserving_literalTruncatedFlow (N : ℕ) (t : ℝ) :
    MeasurePreserving (literalTruncatedFlow h P angularSpeed axialSpeed tau N t)
      (volume : Measure (Torus 3)) volume :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).measurePreserving_literalFlow t

/-- The truncated particle flow is a measurable embedding. -/
theorem measurableEmbedding_literalTruncatedFlow (N : ℕ) (t : ℝ) :
    MeasurableEmbedding (literalTruncatedFlow h P angularSpeed axialSpeed tau N t) :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).measurableEmbedding_literalFlow t

/-! ## The plane-level bounds on the truncated differentials -/

/-- On a retained buffer disc the differential of the truncated axial shift is the cell one. -/
theorem fderiv_planeTruncatedAxialShift_eq_cell (N : ℕ) (t : ℝ) {k : ℕ} (hk : k < N)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk k) :
    fderiv ℝ (planeTruncatedAxialShift h P axialSpeed tau N t) x =
      fderiv ℝ (cellAxialDisplacement h P axialSpeed tau k t) x :=
  (planeTruncatedAxialShift_eventuallyEq_cell h P axialSpeed tau N t hk hx).fderiv_eq

/-- Off every retained buffer disc the differential of the truncated axial shift vanishes.  Unlike
the transverse displacement, the axial plateau does not vanish on a *neighbourhood* of a boundary
point, so the argument goes through the finite sum of differentials instead. -/
theorem fderiv_planeTruncatedAxialShift_eq_zero (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, n < N → x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeTruncatedAxialShift h P axialSpeed tau N t) x = 0 := by
  have hfun : planeTruncatedAxialShift h P axialSpeed tau N t =
      ∑ m ∈ Finset.range N, cellAxialDisplacement h P axialSpeed tau m t := by
    funext y
    rw [Finset.sum_apply]
    rfl
  have hsum : HasFDerivAt (planeTruncatedAxialShift h P axialSpeed tau N t)
      (∑ m ∈ Finset.range N, t • fderiv ℝ (cellAxialSpeed h P axialSpeed tau m) x) x := by
    rw [hfun]
    exact HasFDerivAt.sum fun m _ ↦ hasFDerivAt_cellAxialDisplacement h P axialSpeed tau m t x
  rw [hsum.fderiv]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [fderiv_cellAxialSpeed_eq_zero_of_not_mem_bufferDisk h P axialSpeed tau m
    (hx m (Finset.mem_range.1 hm)), smul_zero]

/-- **The uniform bound on the truncated transverse differential**, with the untruncated constant
`flowLipschitzBound` of `FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`: on a retained disc it
is the cell differential of `FastDynamo/Dynamics/Flow/CellFlowMap.lean`, off the retained discs
it is the identity. -/
theorem norm_fderiv_planeTruncatedTransverseFlow_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ)
    (x : ℝ × ℝ) :
    ‖fderiv ℝ (planeTruncatedTransverseFlow h P angularSpeed N t) x‖ ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  by_cases hbuf : ∃ k : ℕ, k < N ∧ x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk, hx⟩ := hbuf
    rw [fderiv_planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hk hx,
      flowLipschitzBound]
    refine (norm_fderiv_cellTransverseFlow_le h P angularSpeed k t x).trans ?_
    have hstep := mul_le_mul_of_nonneg_left
      (two_mul_abs_mul_radialShearBound_le_flowLipschitzSlope h P angularSpeed axialSpeed tau htau)
      (abs_nonneg t)
    linarith
  · rw [fderiv_planeTruncatedTransverseFlow_eq_id h P angularSpeed N t
      fun n hn hmem ↦ hbuf ⟨n, hn, hmem⟩]
    exact ContinuousLinearMap.norm_id_le.trans
      (one_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau t)

/-- **The uniform bound on the truncated axial differential**, with the untruncated constant
`|t| * flowLipschitzSlope`. -/
theorem norm_fderiv_planeTruncatedAxialShift_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    ‖fderiv ℝ (planeTruncatedAxialShift h P axialSpeed tau N t) x‖ ≤
      |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  by_cases hbuf : ∃ k : ℕ, k < N ∧ x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk, hx⟩ := hbuf
    rw [fderiv_planeTruncatedAxialShift_eq_cell h P axialSpeed tau N t hk hx]
    refine (norm_fderiv_cellAxialDisplacement_le h P angularSpeed axialSpeed tau htau k t
      x).trans ?_
    exact mul_le_mul_of_nonneg_left
      (globalVelocityCoordinateDerivativeBound_le_flowLipschitzSlope h P angularSpeed axialSpeed
        tau) (abs_nonneg t)
  · rw [fderiv_planeTruncatedAxialShift_eq_zero h P axialSpeed tau N t
      fun n hn hmem ↦ hbuf ⟨n, hn, hmem⟩, norm_zero]
    exact mul_nonneg (abs_nonneg t)
      (flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau)

/-- The differential of the periodised truncated axial shift is the chart-side one at the
recentred point. -/
theorem fderiv_planePeriodizedTruncatedShift (N : ℕ) (t : ℝ) (x : ℝ × ℝ) :
    fderiv ℝ (planePeriodizedTruncatedShift h P axialSpeed tau N t) x =
      fderiv ℝ (planeTruncatedAxialShift h P axialSpeed tau N t) (x - chartTranslation x) := by
  have hsub : HasFDerivAt (fun y : ℝ × ℝ ↦ y - chartTranslation x)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := (hasFDerivAt_id x).sub_const _
  have hcomp := ((differentiable_planeTruncatedAxialShift h P axialSpeed tau N t
    (x - chartTranslation x)).hasFDerivAt).comp x hsub
  rw [ContinuousLinearMap.comp_id] at hcomp
  exact ((planePeriodizedTruncatedShift_eventuallyEq h P axialSpeed tau N t x).hasFDerivAt_iff.2
    hcomp).fderiv

/-- The periodised truncated transverse differential obeys the chart-side bound. -/
theorem norm_fderiv_planePeriodizedTruncatedFlow_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ)
    (x : ℝ × ℝ) :
    ‖fderiv ℝ (planePeriodizedTruncatedFlow h P angularSpeed N t) x‖ ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  rw [fderiv_planePeriodizedTruncatedFlow]
  exact norm_fderiv_planeTruncatedTransverseFlow_le h P angularSpeed axialSpeed tau htau N t _

/-- The periodised truncated axial differential obeys the chart-side bound. -/
theorem norm_fderiv_planePeriodizedTruncatedShift_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ)
    (x : ℝ × ℝ) :
    ‖fderiv ℝ (planePeriodizedTruncatedShift h P axialSpeed tau N t) x‖ ≤
      |t| * flowLipschitzSlope h P angularSpeed axialSpeed tau := by
  rw [fderiv_planePeriodizedTruncatedShift]
  exact norm_fderiv_planeTruncatedAxialShift_le h P angularSpeed axialSpeed tau htau N t _

/-- The truncated axial block's bound, in the `‖·‖ + 1 ≤ C` shape the block estimate of
`FastDynamo/Analysis/R3BlockComplexify.lean` consumes. -/
theorem norm_fderiv_planePeriodizedTruncatedShift_add_one_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ)
    (y : ℝ × ℝ) :
    ‖fderiv ℝ (planePeriodizedTruncatedShift h P axialSpeed tau N t) y‖ + 1 ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  have hphi := norm_fderiv_planePeriodizedTruncatedShift_le h P angularSpeed axialSpeed tau htau
    N t y
  have hslope := one_add_mul_flowLipschitzSlope_le_flowLipschitzBound h P angularSpeed axialSpeed
    tau htau t
  linarith

/-! ## The differential of the truncated flow -/

/-- **The truncated derivative flow on the plane**: the block matrix
`[[D(planePeriodizedTruncatedFlow), 0], [D(planePeriodizedTruncatedShift), 1]]` of
`FastDynamo/Analysis/R3BlockComplexify.lean`, with the truncated blocks. -/
abbrev truncatedFlowFDerivPlane (N : ℕ) (t : ℝ) (y : ℝ × ℝ) : R3 →L[ℝ] R3 :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).flowFDerivPlane t y

/-- **The truncated derivative flow `DΦ^{(N)}_t`** (cf. `eq:flow-variational-equation`), read at
the canonical `(0,1]³` representative of the torus point. -/
abbrev truncatedFlowFDeriv (N : ℕ) (t : ℝ) (x : Torus 3) : R3 →L[ℝ] R3 :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).flowFDeriv t x

/-- The truncated derivative flow in closed block form. -/
theorem truncatedFlowFDerivPlane_eq (N : ℕ) (t : ℝ) (y : ℝ × ℝ) :
    truncatedFlowFDerivPlane h P angularSpeed axialSpeed tau N t y =
      flowBlockCLM (fderiv ℝ (planePeriodizedTruncatedFlow h P angularSpeed N t) y)
        (fderiv ℝ (planePeriodizedTruncatedShift h P axialSpeed tau N t) y) := rfl

/-- The truncated derivative flow of the torus is the plane one at the canonical
representative. -/
theorem truncatedFlowFDeriv_eq (N : ℕ) (t : ℝ) (x : Torus 3) :
    truncatedFlowFDeriv h P angularSpeed axialSpeed tau N t x =
      truncatedFlowFDerivPlane h P angularSpeed axialSpeed tau N t (literalIocPair x) := rfl

/-- `truncatedFlowFDeriv … N t (π a)` is the Fréchet derivative at `a` of the periodic lift
`literalTruncatedFlowLift … N t`, at *every* point of `ℝ³`. -/
theorem hasFDerivAt_literalTruncatedFlowLift (N : ℕ) (t : ℝ) (a : R3) :
    HasFDerivAt (literalTruncatedFlowLift h P angularSpeed axialSpeed tau N t)
      (truncatedFlowFDeriv h P angularSpeed axialSpeed tau N t (literalTorusPoint a)) a :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).hasFDerivAt_literalFlowLift t a

/-- **The complexified truncated derivative flow**, the symbol of the truncated Cauchy transport
`eq:ideal-cauchy-formula`. -/
abbrev truncatedFlowFDerivC (N : ℕ) (t : ℝ) (x : Torus 3) : C3 →L[ℂ] C3 :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).flowFDerivC t x

/-- The complexified truncated derivative flow is the complexification of the real one. -/
theorem truncatedFlowFDerivC_eq (N : ℕ) (t : ℝ) (x : Torus 3) :
    truncatedFlowFDerivC h P angularSpeed axialSpeed tau N t x =
      r3Complexify (truncatedFlowFDeriv h P angularSpeed axialSpeed tau N t x) := rfl

/-- **The uniform `L^∞` bound on the complexified truncated symbol**, uniformly in `N`. -/
theorem norm_truncatedFlowFDerivC_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ) (x : Torus 3) :
    ‖truncatedFlowFDerivC h P angularSpeed axialSpeed tau N t x‖ ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau t :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).norm_flowFDerivC_le
    (norm_fderiv_planePeriodizedTruncatedFlow_le h P angularSpeed axialSpeed tau htau N t)
    (norm_fderiv_planePeriodizedTruncatedShift_add_one_le h P angularSpeed axialSpeed tau htau
      N t) x

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
