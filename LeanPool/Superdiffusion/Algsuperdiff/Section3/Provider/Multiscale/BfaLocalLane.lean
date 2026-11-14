/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BfaPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# BfaLocalLane

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The local-descendant lane for `p.bfA.multiscalebound`

ABK26 applies `p.bfA.multiscalebound` separately on every translated cube `R =
z + cu_n` before invoking `e.maxy.bound` over the finite grid (especially).
Consequently the random separation scale at `R` is not the root observable
`hsep M m E b omega`: it is the origin observable at scale `R.scale`, read at
the translated sample

```
hsep M R.scale E b
  (Cutoff.translateCutoffSample (triadicCubeShift R) omega).
```

This file records exactly that local lane.  Stationarity transports the
proved local `Gamma_(bfaTau sigma gam b)` bound from `BfaPerCube` without changing its
amplitude.  The subsequent finite-grid maximum is deliberately priced by the
existing `BlockPayload.isBigOWith_gammaSigma_blockGridSup`; thus the
`e.maxy.bound` cost `gridBlockAmp ... k` remains visible and is not replaced by
an unsupported same-sample domination by the root `hsep`.

## Scope of the payoff interface

`ConclusionRoot.abs_blockVecDot_coarseBlockMatrix_originCube_le_payload_ae` is
almost-everywhere and retains, as antecedents, nonemptiness of `hsepSet`, the
wave envelope, and the potential/solenoidal competitor clauses.  The final
theorem here therefore only converts an *already supplied a.e. conditional*
local Step-3 payoff into the constant-plus-lane form, preserving an explicit
gate unchanged on both sides.  It does not assert that the gate or payoff is
satisfied, and it does not turn an a.e. conclusion into a pointwise one.

A producer from `ConclusionRoot` still requires the analytic competitor
clauses, a uniform envelope, the quadratic-form-to-operator-norm bridge, and a
simultaneous a.e. argument over the loadings (the cutoff indices are countable,
but the unit sphere is not).  None of those obligations is moved into a
hypothesis of an unconditional theorem here.

## Source

* Source: ABK26, `p.bfA.multiscalebound`; the translated-grid maximum in the
  proof of `p.cg.ellipticity.bounds`.
* No theorem in this file closes `p.bfA.multiscalebound`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-! ## The local lane and its deterministic hygiene -/

/-- The `p.bfA.multiscalebound` random lane at a triadic cube `R`: the origin
lane at scale `R.scale`, evaluated on the sample translated by the base point
of `R`. -/
def bfaLocalLane (M : ABKModel d) (R : TriadicCube d) (E b gam Cpre eps : ℝ)
    (omega : CutoffSample d) : ℝ :=
  bfaLane M R.scale E b gam Cpre eps
    (translateCutoffSample (triadicCubeShift R) omega)


theorem bfaLocalLane_nonneg (M : ABKModel d) (R : TriadicCube d)
    {E b gam Cpre eps : ℝ} (hCpre : 0 ≤ Cpre) (heps : 0 ≤ eps)
    (omega : CutoffSample d) :
    0 ≤ bfaLocalLane M R E b gam Cpre eps omega :=
  bfaLane_nonneg M R.scale hCpre heps
    (translateCutoffSample (triadicCubeShift R) omega)

theorem measurable_bfaLocalLane (M : ABKModel d) (R : TriadicCube d)
    (E b gam Cpre eps : ℝ) :
    Measurable (bfaLocalLane M R E b gam Cpre eps) :=
  (measurable_bfaLane M R.scale E b gam Cpre eps).comp
    (measurable_translateCutoffSample (triadicCubeShift R))

/-! ## Stationarity transport of the proved local `BfaPerCube` bound -/

/-- Restrict the induction state to an earlier terminal scale.  This is only
the monotonicity already present in the frozen definition's two `forall
m <= m0` clauses. -/
theorem inductionState_restrict {M : ABKModel d} {m0 m1 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hm : m1 ≤ m0)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) :
    Algsuperdiff.Frozen.Section3.inductionState M m1 E :=
  ⟨fun j hj => hS.1 j (hj.trans hm), fun j hj => hS.2 j (hj.trans hm)⟩


/-- The same stationarity transport from the raw bad-event gates. -/
theorem isBigOWith_gammaSigma_bfaLocalLane_of_localInduction_of_gates
    (M : ABKModel d) (R : TriadicCube d) {E sigma b gam Cpre eps : ℝ}
    (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (R.scale - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam)
    (hgammab : gam ≤ b) (hCpre : 0 < Cpre) (heps : 0 < eps) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (bfaTau sigma gam b))
      (bfaLocalLane M R E b gam Cpre eps)
      (bfaLaneScale sigma b gam Cpre eps) := by
  exact Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample M
    (triadicCubeShift R) (measurable_bfaLane M R.scale E b gam Cpre eps)
    (isBigOWith_gammaSigma_bfaLane_of_gates M hd hE hS hsigma0 hsigma hb0 hb1 hEexp
      hE4 hunit hgamma20 hinvSq hEb hgammaE hgam hgammab hCpre heps)


/-- The descendant-grid local bound from the raw bad-event gates. -/
theorem isBigOWith_gammaSigma_bfaLocalLane_of_mem_descendantsAtScale_of_gates
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E sigma b gam Cpre eps : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam)
    (hgammab : gam ≤ b) (hCpre : 0 < Cpre) (heps : 0 < eps) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (bfaTau sigma gam b))
      (bfaLocalLane M R E b gam Cpre eps)
      (bfaLaneScale sigma b gam Cpre eps) := by
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hle : R.scale - 1 ≤ m - 1 := by
    rw [hscale]
    omega
  exact isBigOWith_gammaSigma_bfaLocalLane_of_localInduction_of_gates M R hd hE
    (inductionState_restrict hle hS) hsigma0 hsigma hb0 hb1 hEexp hE4 hunit hgamma20
    hinvSq hEb hgammaE hgam hgammab hCpre heps

/-! ## The honest `e.maxy.bound` lift -/

/-- The finite descendant-grid maximum of the local lane. -/
def bfaLocalGridSup (M : ABKModel d) (m : ℤ) (k : ℕ)
    (E b gam Cpre eps : ℝ) (omega : CutoffSample d) : ℝ :=
  blockGridSup d m k (fun R => bfaLocalLane M R E b gam Cpre eps) omega

theorem bfaLocalGridSup_nonneg (M : ABKModel d) (m : ℤ) (k : ℕ)
    (E b gam Cpre eps : ℝ) (omega : CutoffSample d) :
    0 ≤ bfaLocalGridSup M m k E b gam Cpre eps omega :=
  blockGridSup_nonneg d m k (fun R => bfaLocalLane M R E b gam Cpre eps) omega


/-- The finite-grid maximum priced from the raw bad-event gates. -/
theorem isBigOWith_gammaSigma_bfaLocalGridSup_of_gates (M : ABKModel d) {m : ℤ}
    (k : ℕ) {E sigma b gam Cpre eps : ℝ} (hd : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) (hgam : 0 < gam)
    (hgammab : gam ≤ b) (hCpre : 0 < Cpre) (heps : 0 < eps) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (bfaTau sigma gam b))
      (bfaLocalGridSup M m k E b gam Cpre eps)
      (gridBlockAmp d (bfaTau sigma gam b)
        (bfaLaneScale sigma b gam Cpre eps) k) := by
  have hsigma1 : sigma < 1 := by linarith
  have htau : 0 < bfaTau sigma gam b := bfaTau_pos hsigma1 hgam hb0
  refine isBigOWith_gammaSigma_blockGridSup (mu := (cutoffSampleLaw M).toMeasure)
    (by omega) m k htau (bfaLaneScale_pos hCpre heps).le ?_ ?_
  · exact fun R omega => bfaLocalLane_nonneg M R hCpre.le heps.le omega
  · intro R hR
    exact isBigOWith_gammaSigma_bfaLocalLane_of_mem_descendantsAtScale_of_gates M hR hd hE
      hS hsigma0 hsigma hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgammaE hgam
      hgammab hCpre heps

/-! ## A.e. conditional conversion of a local Step-3 payoff -/


end

end Algsuperdiff.Section3.Provider.Multiscale
