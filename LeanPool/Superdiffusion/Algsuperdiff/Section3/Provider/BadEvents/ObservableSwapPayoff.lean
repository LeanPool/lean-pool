/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.LowerFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LambdaGridBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# ObservableSwapPayoff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# What the observable body swap buys: the two pointwise payoffs

Two obstructions that were recorded as *structural* in the tree were
obstructions of that representative choice only, and both dissolve.  This
module proves the two consequences.

## The lower leg's grid domination, now pointwise in the sample

Its module docstring recorded the resulting quantifier gap as the lower leg's
open `hgrid` conjunct, and named the fix — "a pointwise-valid representative
for `Observable.cutoffLowerEllipticityInv` (i.e. a change in the observable
layer)".  That change has now been made, so the equality descends at **every**
sample point: `cutoffLowerEllipticityInv_eq_top_add_gridSum`, and with it the
`for all omega, for all L` form
`cutoffLowerEllipticityInv_forall_le_top_add_gridSum`.  The quantifier order
the pointwise `dominates` clause of
`Probability.IsLowerIntegerFamilyOrliczWithWitness` demands is available.

## (b) The off-centre transport of the lower family relation

The *centered-cube* transport of the `hcg` anchoring is definitional after the
observable body swap: both observables reduce to the same clamped literal.
Earlier scope notes, including the corresponding note in
`Provider/Tail/TailSqrt.lean`, said the off-centre half admitted "no defeq
escape", because the only proved translate identity
(`LambdaCovariance.lambdaSq_cutoff_translateCutoffSample`) is a pathwise
equality read at a *different sample*, while the exported observables carried
no pointwise information at all.

They do now.  The exported observables *are* the literals on the source range,
so the pathwise covariance applies to them directly:

```
cubeLowerEllipticityInv M Q L s hs q omega
  = Observable.cutoffLowerEllipticityInv M Q.scale L s hs q
      (translateCutoffSample (triadicCubeShift Q) omega)  ,
```

at every sample point and every cutoff index, with one shift vector
`triadicCubeShift Q` independent of `L`.  Composing with the law invariance
`Cutoff.map_translateCutoffSample_cutoffSampleLaw` (through
`Provider.Stream.isBigOWith_comp_translateCutoffSample`) transports the whole
`IsLowerIntegerFamilyOrliczWithWitness` package from the centered cube to an
arbitrary triadic cube of the same scale, with the witness `Y` replaced by
`Y ∘ translateCutoffSample (triadicCubeShift Q)` and with `b`, `A`, `L0` and the
tail profile unchanged.  This is the per-translate producer of the `hcg` binder
of `EllipticityBranchLow.lean`.

**Scope.**  The local result transports the *statement* from the centered cube
to a translate.  The frozen
`Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` is now proved, but it
is not applied in this transport module; the `hcg` binder of
`EllipticityBranchLow.lean` remains a conditional A binder.  A downstream
assembly can now discharge it at the centered cube and use this result at every
translate of that scale, which is exactly the manuscript's own stationarity
reduction (applied).  The upper (`Lambda`) leg is not transported here: only
the lower covariance `lambdaSq_cutoff_translateCutoffSample` is proved, and the
`Lambda` twin would need the `upperLeft` analogue of
`coarseSigmaStarInvMatrixNorm_cutoff_translateCutoffSample`, which is not.

## Main results

* `cubeLowerEllipticityInvLiteral_translateCutoffSample`,
  `cubeLowerEllipticityInv_translateCutoffSample`: the pathwise off-centre
  identification, at the literal and at the exported observable.
* `isLowerIntegerFamilyOrliczWithWitness_cubeLowerEllipticityInv_translate`,
  `isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_translate`: the off-centre
  transport of the lower family relation, and its existential form.
* `isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_forall_descendant`: the
  per-translate `hcg` producer, in the `∀ R ∈ descendantsAtScale Q n` shape the
  branch consumes.

## References

* ABK26, `l.bad.event.lemma`; the case `n < m`; the per-translate application;
  the stationarity reduction.
* ABK26, `p.cg.ellipticity.bounds`.
* ABK26, coarse-grained ellipticity constants.
* `Provider/BadEvents/CubeEllipticity.lean` (the centered literal identities),
  `Provider/CoarseEllipticity/LambdaGridBridge.lean` (seam (ii)),
  `Provider/Tail/TailSqrt.lean` (the scope note this module updates).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
private theorem neZero_of_model_payoff (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-! ## (b) The off-centre identification -/

/-- **The pathwise off-centre identification, at the literal.**  The literal
inverse lower ellipticity on an arbitrary triadic cube `Q` is the centered
literal at the same scale, read at the sample translated by the base point of
`Q`.  This is `LambdaCovariance.lambdaSq_cutoff_translateCutoffSample` written
at the Section 3 observable layer. -/
theorem cubeLowerEllipticityInvLiteral_translateCutoffSample (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega =
      Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInvLiteral M Q.scale
        cutoffScale s q (translateCutoffSample (triadicCubeShift Q) omega) := by
  let : NeZero d := neZero_of_model_payoff M
  rw [← cubeLowerEllipticityInvLiteral_originCube]
  rw [show cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega =
      (Ch02.lambdaSq Q s q.1
        (coefficientCutoffTriadicCoeffFamily M cutoffScale omega))⁻¹ by
    rw [← cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, inv_inv]]
  rw [show cubeLowerEllipticityInvLiteral M (originCube d Q.scale) cutoffScale s q
      (translateCutoffSample (triadicCubeShift Q) omega) =
      (Ch02.lambdaSq (originCube d Q.scale) s q.1
        (coefficientCutoffTriadicCoeffFamily M cutoffScale
          (translateCutoffSample (triadicCubeShift Q) omega)))⁻¹ by
    rw [← cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, inv_inv]]
  rw [lambdaSq_cutoff_translateCutoffSample M cutoffScale Q s q.1 omega]

/-- **The pathwise off-centre identification, at the exported observable.**  On the
source range `0 < s` the clamp is inert on both sides, so the covariance of the
literals is inherited verbatim.  Before the  body swap no such statement was
available at the exported observables: they were `Classical.choose`-selected
representatives, and no pointwise identity of an off-centre representative with
anything was proved. -/
theorem cubeLowerEllipticityInv_translateCutoffSample (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    cubeLowerEllipticityInv M Q cutoffScale s hs q omega =
      Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M Q.scale
        cutoffScale s hs q (translateCutoffSample (triadicCubeShift Q) omega) := by
  rw [congrFun (cubeLowerEllipticityInv_eq_literal M Q cutoffScale s hs q) omega,
    congrFun (Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv_eq_literal M
      Q.scale cutoffScale s hs q) (translateCutoffSample (triadicCubeShift Q) omega),
    cubeLowerEllipticityInvLiteral_translateCutoffSample]

/-! ## (b) The transport of the lower family relation to a translate -/

/-- **The off-centre witness-level transport.**  A lower-integer-family
weak-Orlicz relation for the *centered* observable at scale `Q.scale`, with
witness `Y`, gives the same relation for the general-cube observable at `Q`,
with the translated witness `Y ∘ translateCutoffSample (triadicCubeShift Q)`,
the same deterministic shift `b`, the same amplitude `A`, the same lower index
`L0` and the same tail profile. -/
theorem isLowerIntegerFamilyOrliczWithWitness_cubeLowerEllipticityInv_translate
    (M : ABKModel d) (Ψ : ℝ → ℝ) (Q : TriadicCube d) (L0 : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (scaling b A : ℝ) (Y : CutoffSample d → ℝ)
    (hY : Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrliczWithWitness
      (Cutoff.cutoffSampleLaw M).toMeasure Ψ
      (fun L : ℤ => fun omega =>
        Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M Q.scale L s hs q
          omega * scaling)
      L0 b Y A) :
    Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrliczWithWitness
      (Cutoff.cutoffSampleLaw M).toMeasure Ψ
      (fun L : ℤ => fun omega =>
        cubeLowerEllipticityInv M Q L s hs q omega * scaling)
      L0 b (fun omega => Y (translateCutoffSample (triadicCubeShift Q) omega)) A where
  admissible := hY.admissible
  scale_pos := hY.scale_pos
  measurable_observable := fun L _ =>
    (measurable_cubeLowerEllipticityInv M Q L s hs q).mul_const scaling
  measurable_witness :=
    hY.measurable_witness.comp (measurable_translateCutoffSample (triadicCubeShift Q))
  dominates := by
    intro omega L hL
    rw [cubeLowerEllipticityInv_translateCutoffSample M Q L s hs q omega]
    exact hY.dominates (translateCutoffSample (triadicCubeShift Q) omega) L hL
  tail :=
    Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample M
      (triadicCubeShift Q) hY.measurable_witness
      hY.tail

/-- **The off-centre transport, in the shape the `hcg` binder is stated in.** The
conclusion of `p.cg.ellipticity.bounds` at the centered cube of scale `Q.scale`
implies the same conclusion at `Q`.  This is the manuscript's own stationarity
reduction at the observable layer. -/
theorem isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_translate
    (M : ABKModel d) (Ψ : ℝ → ℝ) (Q : TriadicCube d) (L0 : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) (scaling b A : ℝ)
    (hcen : Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure Ψ
      (fun L : ℤ => fun omega =>
        Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M Q.scale L s hs q
          omega * scaling)
      L0 b A) :
    Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure Ψ
      (fun L : ℤ => fun omega =>
        cubeLowerEllipticityInv M Q L s hs q omega * scaling)
      L0 b A := by
  obtain ⟨Y, hY⟩ := hcen
  exact ⟨_, isLowerIntegerFamilyOrliczWithWitness_cubeLowerEllipticityInv_translate
    M Ψ Q L0 s hs q scaling b A Y hY⟩

/-- **The per-translate `hcg` producer.**  One centered instance of
`p.cg.ellipticity.bounds` at scale `n` yields the binder of
`EllipticityBranchLow.lean` at *every* scale-`n` descendant of `Q`, which is
exactly what ABK26 applies and justifies. -/
theorem isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_forall_descendant
    (M : ABKModel d) (Ψ : ℝ → ℝ) (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (L0 : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) (scaling b A : ℝ)
    (hcen : Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure Ψ
      (fun L : ℤ => fun omega =>
        Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n L s hs q
          omega * scaling)
      L0 b A) :
    ∀ R ∈ descendantsAtScale Q n,
      Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure Ψ
        (fun L : ℤ => fun omega =>
          cubeLowerEllipticityInv M R L s hs q omega * scaling)
        L0 b A := by
  intro R hR
  have hscale : R.scale = n := by
    have h := scale_eq_sub_of_mem_descendantsAtScale hn hR
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ Q.scale - n)] at h
    omega
  refine isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_translate M Ψ R L0 s hs q
    scaling b A ?_
  rw [hscale]
  exact hcen

end

end Algsuperdiff.Section3.Provider.BadEvents
