/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Flow.PeriodizedFlowData
public import LeanPool.FastDynamo.Analysis.R3BlockComplexify
public import LeanPool.FastDynamo.Analysis.LpCompMeasurePreserving

/-!
# The derivative flow, the symbol and the Cauchy transport of a periodised plane-flow datum

`FastDynamo/Dynamics/Flow/PeriodizedFlowData.lean` builds, over a `PeriodizedPlaneFlowData`, the
particle flow `Φ_t` of `Torus 3`, its periodic lift and its measure preservation.  This module
completes the generic tower with everything the ideal induction equation needs:

* `flowFDerivPlane`, `flowFDeriv` — the block matrix
  `[[D(flow t)(y), 0], [D(shift t)(y), 1]]` of `FastDynamo/Analysis/R3BlockComplexify.lean`, read
  at the canonical `(0,1]³` representative of the torus point
  (`FastDynamo/Analysis/LiteralTorusRepresentative.lean`), with
  `hasFDerivAt_literalFlowLift`, which makes it the Fréchet derivative of the periodic lift at
  *every* point of `ℝ³` (no Rademacher), the chain rule `flowFDeriv_add` (proof of
  `cor:ideal-growth`), and the measurability the `L^∞` symbol needs;
* `flowFDerivC` — the coordinatewise complexification `DΦ_t ⊗ ℂ`, the symbol of
  `eq:ideal-cauchy-formula`;
* `symbol`, `symbolLInf` — that complexification read at the pre-image `Φ_{-t}(x)` and its class
  in `L^∞(T³; ℂ³ →L[ℂ] ℂ³)`;
* `transport` — the Cauchy transport operator on `LiteralC3L2 = L²(T³; ℂ³)`, its almost
  everywhere representative, its per-datum bound, the group law `𝒯₀(s + t) = 𝒯₀(s) 𝒯₀(t)`
  (proof of `cor:ideal-growth`) and the Cauchy identity in the coordinatewise shape
  `IsIdealInductionGroup` (`FastDynamo/Dynamics/ParticleFlow.lean`) uses.

**No uniform bound is a field of the datum.**  The two instances of the development bound their
differentials under a hypothesis on the parameters (`0 ≤ tau`), which the convention of
`FastDynamo/Conventions.lean` forbids on a `def`.  So every bound here is a *lemma* with the
constant `C` as a variable and the pointwise bound as a hypothesis, and the essential
boundedness of the symbol enters as a `MemLp … ∞` hypothesis; `symbolLInf` itself branches on
that membership.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Two lifts of the same point of the literal three-torus differ by an integer in every
coordinate. -/
theorem exists_intCast_add_of_literalTorusPoint_eq {a b : R3}
    (hab : literalTorusPoint a = literalTorusPoint b) (j : Fin 3) : ∃ k : ℤ, a j = b j + k := by
  have hj : ((a j : ℝ) : UnitAddCircle) = ((b j : ℝ) : UnitAddCircle) := congrFun hab j
  exact LatticePeriodic.unitAddCircle_coe_eq_iff.1 hj

namespace PeriodizedPlaneFlowData

variable (D : PeriodizedPlaneFlowData)

/-! ## `ℤ²`-invariance of the two differentials -/

/-- The differential of the plane flow is `ℤ²`-periodic. -/
theorem fderiv_flow_add_int (t : ℝ) (x : ℝ × ℝ) (m n : ℤ) :
    fderiv ℝ (D.flow t) (x.1 + m, x.2 + n) = fderiv ℝ (D.flow t) x := by
  have hxv : ((x.1 + (m : ℝ), x.2 + (n : ℝ)) : ℝ × ℝ) = x + ((m : ℝ), (n : ℝ)) := rfl
  have hfun : (fun z : ℝ × ℝ ↦ D.flow t (z + ((m : ℝ), (n : ℝ)))) =
      fun z : ℝ × ℝ ↦ D.flow t z + ((m : ℝ), (n : ℝ)) :=
    funext fun z ↦ D.flow_add_int t z m n
  rw [hxv, ← fderiv_comp_add_right, hfun, fderiv_add_const]

/-- The differential of the axial shift is `ℤ²`-periodic. -/
theorem fderiv_shift_add_int (t : ℝ) (x : ℝ × ℝ) (m n : ℤ) :
    fderiv ℝ (D.shift t) (x.1 + m, x.2 + n) = fderiv ℝ (D.shift t) x := by
  have hxv : ((x.1 + (m : ℝ), x.2 + (n : ℝ)) : ℝ × ℝ) = x + ((m : ℝ), (n : ℝ)) := rfl
  have hfun : (fun z : ℝ × ℝ ↦ D.shift t (z + ((m : ℝ), (n : ℝ)))) = D.shift t :=
    funext fun z ↦ D.isPeriodic_shift t z m n
  rw [hxv, ← fderiv_comp_add_right, hfun]

/-! ## The derivative flow -/

/-- **The derivative flow read at a point of the plane**: the block matrix
`[[D(flow t)(y), 0], [D(shift t)(y), 1]]`: the derivative `DΦ_t` of
`eq:flow-variational-equation`, in closed form. -/
def flowFDerivPlane (t : ℝ) (y : ℝ × ℝ) : R3 →L[ℝ] R3 :=
  flowBlockCLM (fderiv ℝ (D.flow t) y) (fderiv ℝ (D.shift t) y)

/-- **The derivative flow `DΦ_t`** (proof of `cor:ideal-growth`): the block matrix of the plane
differentials, read at the canonical `(0,1]³` representative of the torus point.  By
`flowFDeriv_literalTorusPoint` the representative is immaterial, and by
`hasFDerivAt_literalFlowLift` this is the Fréchet derivative of the periodic lift at every
point. -/
def flowFDeriv (t : ℝ) (x : Torus 3) : R3 →L[ℝ] R3 :=
  D.flowFDerivPlane t (literalIocPair x)

/-- **The derivative flow is `ℤ²`-invariant on the plane**, so it descends to the torus. -/
theorem flowFDerivPlane_add_int (t : ℝ) (x : ℝ × ℝ) (m n : ℤ) :
    D.flowFDerivPlane t (x.1 + m, x.2 + n) = D.flowFDerivPlane t x := by
  rw [flowFDerivPlane, flowFDerivPlane, D.fderiv_flow_add_int t x m n,
    D.fderiv_shift_add_int t x m n]

/-- **The derivative flow at the class of `a` is the block matrix at `a`**: the defining choice of
representative is immaterial.  This is the identity a consumer uses to compute `flowFDeriv` from
an explicit lift. -/
theorem flowFDeriv_literalTorusPoint (t : ℝ) (a : R3) :
    D.flowFDeriv t (literalTorusPoint a) = D.flowFDerivPlane t (a 0, a 1) := by
  obtain ⟨k0, hk0⟩ := exists_intCast_add_of_literalTorusPoint_eq
    (literalTorusPoint_literalIocRepresentative (literalTorusPoint a)) 0
  obtain ⟨k1, hk1⟩ := exists_intCast_add_of_literalTorusPoint_eq
    (literalTorusPoint_literalIocRepresentative (literalTorusPoint a)) 1
  rw [flowFDeriv, literalIocPair, hk0, hk1]
  exact D.flowFDerivPlane_add_int t (a 0, a 1) k0 k1

/-- `flowFDeriv D t (π a)` is the Fréchet derivative at `a` of the periodic lift
`literalFlowLift D t` of `Φ_t`, at *every* point of `ℝ³`, with no appeal to Rademacher's
theorem (which the proof of `cor:ideal-growth` uses to define `DΦ_t` almost everywhere). -/
theorem hasFDerivAt_literalFlowLift (t : ℝ) (a : R3) :
    HasFDerivAt (D.literalFlowLift t) (D.flowFDeriv t (literalTorusPoint a)) a := by
  have hpair : HasFDerivAt (fun x : R3 ↦ ((x 0, x 1) : ℝ × ℝ)) flowPairProjection a :=
    flowPairProjection.hasFDerivAt
  have hF := (D.differentiable_flow t ((a 0, a 1) : ℝ × ℝ)).hasFDerivAt
  have hG := (D.differentiable_shift t ((a 0, a 1) : ℝ × ℝ)).hasFDerivAt
  have hFc := hF.comp a hpair
  have hGc := hG.comp a hpair
  have hthird := ((EuclideanSpace.proj (2 : Fin 3) : R3 →L[ℝ] ℝ).hasFDerivAt (x := a)).add hGc
  have hg : HasFDerivAt
      (fun x : R3 ↦ (![(D.flow t (x 0, x 1)).1, (D.flow t (x 0, x 1)).2,
        x 2 + D.shift t (x 0, x 1)] : Fin 3 → ℝ))
      (ContinuousLinearMap.pi
        ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp
            ((fderiv ℝ (D.flow t) ((a 0, a 1) : ℝ × ℝ)).comp flowPairProjection),
          (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
            ((fderiv ℝ (D.flow t) ((a 0, a 1) : ℝ × ℝ)).comp flowPairProjection),
          (EuclideanSpace.proj 2 : R3 →L[ℝ] ℝ) +
            (fderiv ℝ (D.shift t) ((a 0, a 1) : ℝ × ℝ)).comp flowPairProjection]) a := by
    rw [hasFDerivAt_pi']
    intro i
    rw [ContinuousLinearMap.proj_pi]
    fin_cases i
    · exact hFc.fst
    · exact hFc.snd
    · exact hthird
  have hfinal := ((EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt (x := _)).comp a hg
  rw [D.flowFDeriv_literalTorusPoint, flowFDerivPlane, flowBlockCLM]
  exact hfinal

/-! ## The uniform bound -/

/-- **The block bound at every point of the plane.**  The constant is a variable: each instance of
the development supplies its own pointwise bounds on the two blocks, under its own hypotheses. -/
theorem norm_flowFDerivPlane_le {C t : ℝ}
    (hA : ∀ y : ℝ × ℝ, ‖fderiv ℝ (D.flow t) y‖ ≤ C)
    (hphi : ∀ y : ℝ × ℝ, ‖fderiv ℝ (D.shift t) y‖ + 1 ≤ C) (y : ℝ × ℝ) :
    ‖D.flowFDerivPlane t y‖ ≤ 2 * C :=
  norm_flowBlockCLM_le (hA y) (hphi y)

/-- **The uniform bound on the derivative flow** at every point of the torus. -/
theorem norm_flowFDeriv_le {C t : ℝ}
    (hA : ∀ y : ℝ × ℝ, ‖fderiv ℝ (D.flow t) y‖ ≤ C)
    (hphi : ∀ y : ℝ × ℝ, ‖fderiv ℝ (D.shift t) y‖ + 1 ≤ C) (x : Torus 3) :
    ‖D.flowFDeriv t x‖ ≤ 2 * C :=
  D.norm_flowFDerivPlane_le hA hphi _

/-! ## The group law -/

/-- `DΦ_0 = id`. -/
theorem flowFDeriv_zero : D.flowFDeriv 0 = fun _ ↦ ContinuousLinearMap.id ℝ R3 := by
  funext x
  have hF : D.flow 0 = fun z : ℝ × ℝ ↦ z := funext D.flow_zero
  have hG : D.shift 0 = fun _ : ℝ × ℝ ↦ (0 : ℝ) := funext D.shift_zero
  rw [flowFDeriv, flowFDerivPlane, hF, hG, fderiv_fun_id, fderiv_fun_const]
  exact flowBlockCLM_id

/-- **The chain rule** `DΦ_{s+t}(a) = DΦ_s(Φ_t a) DΦ_t(a)` (proof of `cor:ideal-growth`, where it
holds almost everywhere; here everywhere): both sides are the
derivative at a lift of the composite lift, and the derivative is unique. -/
theorem flowFDeriv_add (s t : ℝ) (x : Torus 3) :
    D.flowFDeriv (s + t) x = (D.flowFDeriv s (D.literalFlow t x)).comp (D.flowFDeriv t x) := by
  obtain ⟨a, rfl⟩ := literalTorusPoint_surjective x
  have hinner := D.hasFDerivAt_literalFlowLift t a
  have houter := D.hasFDerivAt_literalFlowLift s (D.literalFlowLift t a)
  rw [D.literalTorusPoint_literalFlowLift t a] at houter
  have hcomp := houter.comp a hinner
  have hsum : HasFDerivAt (D.literalFlowLift (s + t))
      (D.flowFDeriv (s + t) (literalTorusPoint a)) a :=
    D.hasFDerivAt_literalFlowLift (s + t) a
  have hfun : (D.literalFlowLift s ∘ D.literalFlowLift t) = D.literalFlowLift (s + t) :=
    funext fun b ↦ D.literalFlowLift_comp s t b
  rw [hfun] at hcomp
  exact hsum.unique hcomp

/-! ## Measurability in the space variable -/

/-- The derivative flow is a measurable function of the plane point: both blocks are measurable
differentials of everywhere-differentiable maps, and the block matrix is continuous in them. -/
theorem measurable_flowFDerivPlane (t : ℝ) : Measurable (D.flowFDerivPlane t) := by
  have hfun : D.flowFDerivPlane t = fun y : ℝ × ℝ ↦
      flowBlockCLM (fderiv ℝ (D.flow t) y) (fderiv ℝ (D.shift t) y) := rfl
  rw [hfun]
  exact measurable_flowBlockCLM_comp (measurable_fderiv ℝ (D.flow t))
    (measurable_fderiv ℝ (D.shift t))

/-- **The derivative flow is measurable on the torus.**  It is the measurable block matrix read at
the measurable canonical section of the quotient. -/
theorem measurable_flowFDeriv (t : ℝ) : Measurable (D.flowFDeriv t) :=
  (D.measurable_flowFDerivPlane t).comp measurable_literalIocPair

/-! ## The complexified derivative flow -/

/-- **The complexified derivative flow** `DΦ_t ⊗ ℂ`, the symbol of the Cauchy transport operator
`eq:ideal-cauchy-formula`: the `ℂ`-linear endomorphism of `ℂ³` with the real
matrix entries of `flowFDeriv D t x`. -/
def flowFDerivC (t : ℝ) (x : Torus 3) : C3 →L[ℂ] C3 :=
  r3Complexify (D.flowFDeriv t x)

/-- The complexified derivative flow acts by the real matrix entries of `DΦ_t`, which is the
coordinatewise form the `cauchy` clause of `IsIdealInductionGroup` uses. -/
theorem flowFDerivC_apply (t : ℝ) (x : Torus 3) (v : C3) (i : Fin 3) :
    D.flowFDerivC t x v i =
      ∑ j : Fin 3, ((D.flowFDeriv t x (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * v j :=
  r3Complexify_apply _ v i

/-- **The uniform bound on the complexified derivative flow**, the `L^∞` symbol bound.  The factor
`6` is the coordinate count of a matrix row times the Euclidean assembly factor `2`. -/
theorem norm_flowFDerivC_le {C t : ℝ}
    (hA : ∀ y : ℝ × ℝ, ‖fderiv ℝ (D.flow t) y‖ ≤ C)
    (hphi : ∀ y : ℝ × ℝ, ‖fderiv ℝ (D.shift t) y‖ + 1 ≤ C) (x : Torus 3) :
    ‖D.flowFDerivC t x‖ ≤ 6 * (2 * C) := by
  have hbase := D.norm_flowFDeriv_le hA hphi x
  have hc := norm_r3Complexify_le (D.flowFDeriv t x)
  rw [flowFDerivC]
  linarith

/-- The complexified derivative flow is measurable. -/
theorem measurable_flowFDerivC (t : ℝ) : Measurable (D.flowFDerivC t) :=
  continuous_r3Complexify.measurable.comp (D.measurable_flowFDeriv t)

/-- `DΦ_0 ⊗ ℂ = id`. -/
theorem flowFDerivC_zero : D.flowFDerivC 0 = fun _ ↦ ContinuousLinearMap.id ℂ C3 := by
  funext x
  rw [flowFDerivC, D.flowFDeriv_zero, r3Complexify_id]

/-- **The chain rule for the complexified derivative flow**, the identity behind the group law of
the Cauchy transport operator. -/
theorem flowFDerivC_add (s t : ℝ) (x : Torus 3) :
    D.flowFDerivC (s + t) x = (D.flowFDerivC s (D.literalFlow t x)).comp (D.flowFDerivC t x) := by
  rw [flowFDerivC, flowFDerivC, flowFDerivC, D.flowFDeriv_add s t x, r3Complexify_comp]

/-! ## The symbol of the Cauchy transport -/

/-- **The symbol of the Cauchy transport** (`eq:ideal-cauchy-formula`): the
complexified derivative flow `DΦ_t ⊗ ℂ` read at the pre-image `Φ_{-t}(x)`, so that the Cauchy
formula `(𝒯₀(t)B)(Φ_t a) = DΦ_t(a) B(a)` becomes the pointwise multiplier
`(𝒯₀(t)B)(x) = symbol D t x (B (Φ_{-t} x))`. -/
def symbol (t : ℝ) (x : Torus 3) : C3 →L[ℂ] C3 :=
  D.flowFDerivC t (D.literalFlow (-t) x)

/-- The symbol is measurable: the complexified derivative flow is measurable (it need not be
continuous) and the flow is measurable. -/
theorem measurable_symbol (t : ℝ) : Measurable (D.symbol t) :=
  (D.measurable_flowFDerivC t).comp (D.measurable_literalFlow (-t))

/-- The symbol is almost everywhere strongly measurable, the first half of `MemLp … ∞`. -/
theorem aestronglyMeasurable_symbol (t : ℝ) :
    AEStronglyMeasurable (D.symbol t) (volume : Measure (Torus 3)) :=
  (D.measurable_symbol t).aestronglyMeasurable

/-- At time `0` the symbol is the identity of `ℂ³`. -/
theorem symbol_zero : D.symbol 0 = fun _ ↦ ContinuousLinearMap.id ℂ C3 := by
  funext x
  rw [symbol, D.flowFDerivC_zero]

/-- **The cocycle identity of the symbol**, the chain rule `DΦ_{s+t} = DΦ_s(Φ_t ·) DΦ_t` read at
the pre-image (proof of `cor:ideal-growth`).  It is the identity behind the group law of the
transport. -/
theorem symbol_add (s t : ℝ) (x : Torus 3) :
    D.symbol (s + t) x =
      (D.symbol s x).comp (D.symbol t (D.literalFlow (-s) x)) := by
  have hforward : D.literalFlow t (D.literalFlow (-(s + t)) x) = D.literalFlow (-s) x := by
    rw [D.literalFlow_comp]
    have hts : t + -(s + t) = -s := by ring
    rw [hts]
  have hback : D.literalFlow (-t) (D.literalFlow (-s) x) = D.literalFlow (-(s + t)) x := by
    rw [D.literalFlow_comp]
    have hts : -t + -s = -(s + t) := by ring
    rw [hts]
  rw [symbol, symbol, symbol, hback, D.flowFDerivC_add s t (D.literalFlow (-(s + t)) x),
    hforward]

/-- A uniform bound makes the symbol essentially bounded, hence a class in
`L^∞(T³; ℂ³ →L[ℂ] ℂ³)`. -/
theorem memLp_symbol_of_bound {C t : ℝ} (h : ∀ x : Torus 3, ‖D.symbol t x‖ ≤ C) :
    MemLp (D.symbol t) ∞ (volume : Measure (Torus 3)) :=
  memLp_top_of_bound (D.aestronglyMeasurable_symbol t) C (ae_of_all _ h)

/-- At time `0` the symbol is essentially bounded with no hypothesis at all: it is the identity.
This is why `transport_zero` has no hypothesis. -/
theorem memLp_symbol_zero : MemLp (D.symbol 0) ∞ (volume : Measure (Torus 3)) := by
  rw [D.symbol_zero]
  refine memLp_top_of_bound aestronglyMeasurable_const 1 (ae_of_all _ fun _ ↦ ?_)
  exact ContinuousLinearMap.norm_id_le

/-! ## The symbol as an element of `L^∞` -/

/-- **The symbol as an `L^∞` class**.  The case distinction is on the essential boundedness of the
symbol, which each instance proves only under a hypothesis on its parameters; under that
hypothesis `symbolLInf_eq_toLp` identifies this with `MemLp.toLp` of the symbol.  This is the
positivity-hypothesis convention of `FastDynamo/Conventions.lean`. -/
def symbolLInf (t : ℝ) : Lp (C3 →L[ℂ] C3) ∞ (volume : Measure (Torus 3)) :=
  @dite _ (MemLp (D.symbol t) ∞ (volume : Measure (Torus 3))) (Classical.propDecidable _)
    (fun hmem ↦ hmem.toLp _) fun _ ↦ 0

/-- Whenever the symbol is essentially bounded, the `L^∞` class is its `MemLp.toLp`. -/
theorem symbolLInf_eq_toLp {t : ℝ}
    (hmem : MemLp (D.symbol t) ∞ (volume : Measure (Torus 3))) :
    D.symbolLInf t = hmem.toLp _ :=
  dite_eq_left _

/-- **The almost everywhere representative of the `L^∞` symbol** is the symbol. -/
theorem symbolLInf_coe_ae {t : ℝ}
    (hmem : MemLp (D.symbol t) ∞ (volume : Measure (Torus 3))) :
    (D.symbolLInf t : Torus 3 → (C3 →L[ℂ] C3)) =ᵐ[volume] D.symbol t := by
  rw [D.symbolLInf_eq_toLp hmem]
  exact MemLp.coeFn_toLp _

/-- At time `0` the `L^∞` symbol is the identity, with no hypothesis. -/
theorem symbolLInf_zero_coe_ae :
    (D.symbolLInf 0 : Torus 3 → (C3 →L[ℂ] C3)) =ᵐ[volume]
      fun _ ↦ ContinuousLinearMap.id ℂ C3 := by
  filter_upwards [D.symbolLInf_coe_ae D.memLp_symbol_zero] with x hx
  rw [hx, D.symbol_zero]

/-- **The `L^∞` norm of the symbol** is bounded by any pointwise bound on it. -/
theorem norm_symbolLInf_le {C t : ℝ} (hC : 0 ≤ C) (h : ∀ x : Torus 3, ‖D.symbol t x‖ ≤ C) :
    ‖D.symbolLInf t‖ ≤ C := by
  rw [D.symbolLInf_eq_toLp (D.memLp_symbol_of_bound h), Lp.norm_toLp]
  rw [eLpNorm_exponent_top (D.aestronglyMeasurable_symbol t)]
  have htop : eLpNormEssSup (D.symbol t) (volume : Measure (Torus 3)) ≤ ENNReal.ofReal C :=
    eLpNormEssSup_le_of_ae_bound (ae_of_all _ h)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htop).trans_eq (ENNReal.toReal_ofReal hC)

/-! ## The transport operator -/

/-- **The Cauchy transport operator `𝒯₀(t)` on `L²(T³; ℂ³)`** (`eq:ideal-cauchy-formula`):
pointwise multiplication by the `L^∞` symbol `DΦ_t(Φ_{-t} ·)`, composed with the
measure-preserving substitution `B ↦ B ∘ Φ_{-t}`. -/
def transport (t : ℝ) : LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  (operatorMulL2 (volume : Measure (Torus 3)) (D.symbolLInf t)).comp
    ((Lp.compMeasurePreservingₗᵢ ℂ (D.literalFlow (-t))
        (D.measurePreserving_literalFlow (-t))).toContinuousLinearMap)

/-- The almost everywhere representative of the transport, for **any** almost everywhere
representative `M` of the `L^∞` symbol.  Both `transport_coe_ae` and `transport_zero` are
instances of this. -/
theorem transport_coe_ae_of_symbol (t : ℝ) (B : LiteralC3L2) {M : Torus 3 → (C3 →L[ℂ] C3)}
    (hM : (D.symbolLInf t : Torus 3 → (C3 →L[ℂ] C3)) =ᵐ[volume] M) :
    (D.transport t B : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ M x ((B : Torus 3 → C3) (D.literalFlow (-t) x)) := by
  have hcomp := coeFn_compMeasurePreservingCLM (D.measurePreserving_literalFlow (-t)) B
  have hmul := operatorMulL2_coe_ae (volume : Measure (Torus 3)) (D.symbolLInf t)
    ((Lp.compMeasurePreservingₗᵢ ℂ (D.literalFlow (-t))
      (D.measurePreserving_literalFlow (-t))).toContinuousLinearMap B)
  filter_upwards [hmul, hcomp, hM] with x hx hcx hsx
  rw [transport, ContinuousLinearMap.comp_apply, hx, hcx, hsx]

/-- **The almost everywhere representative of the Cauchy transport**:
`(𝒯₀(t)B)(x) = DΦ_t(Φ_{-t} x) B(Φ_{-t} x)` for almost every `x`. -/
theorem transport_coe_ae {t : ℝ} (hmem : MemLp (D.symbol t) ∞ (volume : Measure (Torus 3)))
    (B : LiteralC3L2) :
    (D.transport t B : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ D.symbol t x ((B : Torus 3 → C3) (D.literalFlow (-t) x)) :=
  D.transport_coe_ae_of_symbol t B (D.symbolLInf_coe_ae hmem)

/-- **The per-datum upper bound** `‖𝒯₀(t)B‖₂ ≤ C ‖B‖₂` (the bound after `eq:ideal-cauchy-formula`):
Hölder's estimate for the `L^∞` symbol, together with the isometry of the substitution. -/
theorem norm_transport_apply_le {C t : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : Torus 3, ‖D.symbol t x‖ ≤ C) (B : LiteralC3L2) :
    ‖D.transport t B‖ ≤ C * ‖B‖ := by
  have hholder := norm_operatorMulL2_apply_apply_le (volume : Measure (Torus 3))
    (D.symbolLInf t)
    ((Lp.compMeasurePreservingₗᵢ ℂ (D.literalFlow (-t))
      (D.measurePreserving_literalFlow (-t))).toContinuousLinearMap B)
  rw [norm_compMeasurePreservingCLM (D.measurePreserving_literalFlow (-t)) B] at hholder
  refine hholder.trans ?_
  gcongr
  exact D.norm_symbolLInf_le hC h

/-- **The identity at time zero**: `𝒯₀(0) = id`.  No hypothesis is needed. -/
theorem transport_zero : D.transport 0 = ContinuousLinearMap.id ℂ LiteralC3L2 := by
  refine ContinuousLinearMap.ext fun B ↦ ?_
  refine Lp.ext ?_
  have hrep := D.transport_coe_ae_of_symbol 0 B D.symbolLInf_zero_coe_ae
  filter_upwards [hrep] with x hx
  rw [hx]
  have hflow : D.literalFlow (-0) x = x := by
    rw [neg_zero]
    exact D.literalFlow_zero x
  rw [hflow]
  rfl

/-- The backward flow composes into the backward flow of the sum time. -/
theorem literalFlow_neg_add (s t : ℝ) (x : Torus 3) :
    D.literalFlow (-t) (D.literalFlow (-s) x) = D.literalFlow (-(s + t)) x := by
  rw [D.literalFlow_comp]
  have hts : -t + -s = -(s + t) := by ring
  rw [hts]

/-- **The group law** `𝒯₀(s + t) = 𝒯₀(s) 𝒯₀(t)` (proof of `cor:ideal-growth`), from the cocycle
identity `symbol_add` of the symbol and the flow law. -/
theorem transport_add {s t : ℝ} (hs : MemLp (D.symbol s) ∞ (volume : Measure (Torus 3)))
    (ht : MemLp (D.symbol t) ∞ (volume : Measure (Torus 3)))
    (hst : MemLp (D.symbol (s + t)) ∞ (volume : Measure (Torus 3))) :
    D.transport (s + t) = (D.transport s).comp (D.transport t) := by
  refine ContinuousLinearMap.ext fun B ↦ ?_
  refine Lp.ext ?_
  have hsum := D.transport_coe_ae hst B
  have houter := D.transport_coe_ae hs (D.transport t B)
  have hinner := (D.quasiMeasurePreserving_literalFlow (-s)).ae (D.transport_coe_ae ht B)
  filter_upwards [hsum, houter, hinner] with x hx hox hix
  rw [ContinuousLinearMap.comp_apply, hox, hix, hx, D.symbol_add s t x,
    D.literalFlow_neg_add s t x]
  rfl

/-- **The Cauchy formula in the shape of the `cauchy` clause of `IsIdealInductionGroup`**
(`FastDynamo/Dynamics/ParticleFlow.lean`, `eq:ideal-cauchy-formula`): for almost
every `a` and every coordinate `i`,

```
  (𝒯₀(t)B)(Φ_t a)ᵢ = ∑ⱼ (DΦ_t(a) e_j)ᵢ B(a)ⱼ .
```

The proof reads the almost everywhere representative at `Φ_t a`, which is legitimate because the
flow is quasi-measure-preserving. -/
theorem transport_cauchy {t : ℝ} (hmem : MemLp (D.symbol t) ∞ (volume : Measure (Torus 3)))
    (B : LiteralC3L2) :
    ∀ᵐ a : Torus 3, ∀ i : Fin 3,
      (D.transport t B : Torus 3 → C3) (D.literalFlow t a) i =
        ∑ j : Fin 3, ((D.flowFDeriv t a (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) *
          (B : Torus 3 → C3) a j := by
  have hae := (D.quasiMeasurePreserving_literalFlow t).ae (D.transport_coe_ae hmem B)
  filter_upwards [hae] with a ha
  intro i
  rw [ha, symbol, D.literalFlow_neg]
  exact D.flowFDerivC_apply t a _ i

/-- `𝒯₀(-t)` inverts `𝒯₀(t)` (proof of `cor:ideal-growth`), the per-datum form. -/
theorem transport_neg_transport {t : ℝ}
    (ht : MemLp (D.symbol t) ∞ (volume : Measure (Torus 3)))
    (hneg : MemLp (D.symbol (-t)) ∞ (volume : Measure (Torus 3))) (B : LiteralC3L2) :
    D.transport (-t) (D.transport t B) = B := by
  have hzero : -t + t = 0 := by ring
  have hgroup := D.transport_add hneg ht (by rw [hzero]; exact D.memLp_symbol_zero)
  rw [hzero, D.transport_zero] at hgroup
  have happ := congrArg (fun f : LiteralC3L2 →L[ℂ] LiteralC3L2 ↦ f B) hgroup
  exact happ.symm

/-- **The per-datum lower bound**: `‖B‖₂ = ‖𝒯₀(-t)𝒯₀(t)B‖₂ ≤ C ‖𝒯₀(t)B‖₂`. -/
theorem norm_le_mul_norm_transport {C t : ℝ} (hC : 0 ≤ C)
    (ht : MemLp (D.symbol t) ∞ (volume : Measure (Torus 3)))
    (hneg : MemLp (D.symbol (-t)) ∞ (volume : Measure (Torus 3)))
    (h : ∀ x : Torus 3, ‖D.symbol (-t) x‖ ≤ C) (B : LiteralC3L2) :
    ‖B‖ ≤ C * ‖D.transport t B‖ := by
  calc ‖B‖ = ‖D.transport (-t) (D.transport t B)‖ := by
        rw [D.transport_neg_transport ht hneg B]
    _ ≤ C * ‖D.transport t B‖ := D.norm_transport_apply_le hC h _

end PeriodizedPlaneFlowData

end

end FastDynamo
