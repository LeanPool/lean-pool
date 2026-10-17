/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLp
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLaw
public import LeanPool.HighContrastHomogenization.Support.Besov.Localization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.PartitionAverageFluctuations

/-!
# IncrementConcentration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The deterministic partition identity for the stream-increment `L^p` mass

ABK26 proves `e.kl.bounds.large` by writing the cube average `⨍_{cu_l} |k_m -
k_n|^p` as the average of the *subcube* averages over the scale-`m` partition
of `cu_l`, and then applying `p.concentration` to that partition average.  This
module proves the deterministic half of that step — the exact identity —
together with the law-carrier form of the cube observable that the
concentration step consumes.

## What is proved

* `regFieldLpMass p U a` — the volume-normalized `L^p` mass of a *regular
  coefficient field* on an observation set.  This is the CoarseGraining-shaped
  cube observable `X : Set (Vec d) → RegCoeffField d → ℝ`; read at the
  increment field on a half-open triadic cube it is the cube average of the
  increment density (`cubeAverage_streamIncrementLpDensity`), i.e. the proved
  `streamIncrementLpMass`.
* `regFieldLpMass_translateSet` — translating the observation set is the same
  as translating the field.  This is the raw form of the covariance that
  CoarseGraining's restriction lane asks for
  (`Ch04.IsRestrictionTranslationCovariant`), one of the three structural
  hypotheses of
  `isBigO_gammaSigma_restrictionCenteredDescendantAverage_of_restrictionUnitRangeDependentLaw`;
  the lane-shaped statement is carried by the measurable representative
  `regFieldLpMassRep` of `IncrementMassRepresentative.lean`, together with the
  restriction locality (`Ch04.IsRestrictionLocalRandomVariable`) that the same
  module supplies.  What that representative costs is exactly the measurability
  obstruction described in the gap note below.
* `integrableOn_cubeSet_streamIncrementLpDensity` — the `x`-side integrability
  of the density on a half-open triadic cube (the proved `IncrementLp`
  integrability suite is in `omega`, and its `x`-side lemma is stated on the
  *open* cube; CoarseGraining's partition identity needs the half-open one).
* `streamIncrementLpMass_eq_descendantsAverage`,
  `streamIncrementLpMass_eq_descendantAverage_of_scale` — **the deterministic
  descendant identity**, CoarseGraining's
  `cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn` instantiated
  at the increment density, in both the depth-indexed and the scale-indexed
  form.
  The *head + centered tail* rewriting of that identity is not performed here.
  The raw centered tail is signed, so it does NOT satisfy the concentration
  interface's `hT_nonneg` directly; a consumer must pass `T := |mass − H|`, to
  which the `Γ` bound transfers since `IsBigOWith` is stated through the
  absolute tail event, and the proved
  `IncrementLpGain.streamIncrementLpMass_head_tail` does exactly that.

## The remaining gap for `e.kl.bounds.large`

The concentration application itself is *not* proved, and needs exactly one
more input, recorded here so the follow-up is bounded:

* `Measurable (regFieldLpMass p U)` on the canonical carrier σ-algebra of
  `RegCoeffField d` (equivalently, an a.e. representative of it in the sense of
  Ch04's restriction-lane centered-descendant-average theorem for an a.e.-equal
  local representative).
  Pointwise evaluation `a ↦ a x i j` is measurable, but the carrier σ-algebra
  is a join containing an uncountable-product part, so the *integral* over `U`
  of a nonlinear function of the values is not measurable for free.  The
  canonical route is a countable local representative: on the (full-measure,
  because every increment field is continuous) set of continuous fields,
  `⨍_U |a|^p` is the limit of the triadic Riemann sums
  `descendantsAverage U j (fun R => |cubeAverageMat R a|^p)`, and each
  `cubeAverageMat R a` is a fixed multiple of `entryTestR i j (1_{cubeSet R})`,
  hence `LocalSigmaR`- and `RestrictionSigmaR`-measurable.

: no rescaling achieves this for the manuscript's scale-`m` subcubes (unit
range and nonnegative subcube scale are incompatible); the local partition runs
at the coarser scale-`(m+c)` subcubes via `Provider/Stream/IncrementLaw.lean`'s
`scaledStreamIncrementLaw` at `3^{m+c}`, `3^c > 2 sqrt d`, costing the
dimension-only `3^{(d/2)c}`.

## References

* ABK26, `e.kl.bounds.large`; `p.concentration`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The `L^p` mass as an observable of the coefficient field -/

/-- The volume-normalized `L^p` mass of a regular coefficient field on an
observation set, measured in the exact Euclidean matrix operator norm.  This is
the cube observable `X : Set (Vec d) → RegCoeffField d → ℝ` of the
`p.concentration` step. -/
def regFieldLpMass (p : ℝ) (U : Set (Vec d)) (a : RegCoeffField d) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, Book.Ch02.matrixOperatorNorm (a x) ^ p

/-- The cube average of the increment density is the cube observable at the
increment field, on the half-open cube used by CoarseGraining's partition
identity. -/
theorem cubeAverage_streamIncrementLpDensity (p : ℝ) (Q : TriadicCube d)
    (n m : ℤ) (omega : ShellSeq d) :
    cubeAverage Q (streamIncrementLpDensity p n m omega) =
      regFieldLpMass p (cubeSet Q) (finiteShellIncrement omega n m) := by
  rw [cubeAverage, regFieldLpMass, volume_cubeSet_toReal]
  rfl

/-! ## Translation covariance of the observable -/

/-- The `L^p` mass observable commutes with spatial translation: translating
the observation set is the same as translating the field. -/
theorem regFieldLpMass_translateSet (p : ℝ) (U : Set (Vec d)) (z : Vec d)
    (a : RegCoeffField d) :
    regFieldLpMass p (translateSet z U) a =
      regFieldLpMass p U (translateReg z a) := by
  rw [regFieldLpMass, regFieldLpMass, volume_translateSet_eq]
  refine congrArg (fun t : ℝ => (volume U).toReal⁻¹ * t) ?_
  rw [← setIntegral_comp_addRight_translateSet z U
    (fun y : Vec d => Book.Ch02.matrixOperatorNorm (a y) ^ p)]
  rfl

/-! ## The `x`-side integrability of the increment density -/

/-- The `L^p` density of a stream increment is integrable on every half-open
triadic cube: it is continuous and the cube is bounded.  The proved
`IncrementLp` integrability suite is in the sample `omega`; this is the
`x`-side statement, on the half-open cube used by CoarseGraining's partition
identity. -/
theorem integrableOn_cubeSet_streamIncrementLpDensity {p : ℝ} (hp : 0 < p)
    (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) :
    IntegrableOn (streamIncrementLpDensity p n m omega) (cubeSet Q) volume := by
  have hcont := continuous_streamIncrementLpDensity hp n m omega
  have hcompact : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    isCompact_closedBall _ _
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set
    (cubeSet_subset_closedBall Q)

/-! ## The deterministic descendant identity -/

/-- **The deterministic descendant identity at the increment** (depth form).
CoarseGraining's
`cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn`, instantiated
at the increment `L^p` density: the cube mass on `cu_l` is the average of the
subcube masses over the depth-`j` descendants of `cu_l`. -/
theorem streamIncrementLpMass_eq_descendantsAverage {p : ℝ} (hp : 0 < p)
    (l n m : ℤ) (j : ℕ) (omega : ShellSeq d) :
    streamIncrementLpMass p l n m omega =
      descendantsAverage (originCube d l) j
        (fun R => cubeAverage R (streamIncrementLpDensity p n m omega)) := by
  have hmass : streamIncrementLpMass p l n m omega =
      cubeAverage (originCube d l) (streamIncrementLpDensity p n m omega) := by
    rw [streamIncrementLpMass, Book.Ch02.average, Book.Ch02.cubeDomain_coe,
      cubeAverage, volume_openCubeSet_toReal,
      setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  rw [hmass]
  exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (originCube d l) j (streamIncrementLpDensity p n m omega)
    (integrableOn_cubeSet_streamIncrementLpDensity hp (originCube d l) n m omega)

/-- **The deterministic descendant identity at the increment** (scale form).
This is the partition of `cu_l` into its scale-`k` subcubes, which for `k = m`
is exactly the partition used by `e.kl.bounds.large`. -/
theorem streamIncrementLpMass_eq_descendantAverage_of_scale {p : ℝ} (hp : 0 < p)
    {l k : ℤ} (hkl : k ≤ l) (n m : ℤ) (omega : ShellSeq d) :
    streamIncrementLpMass p l n m omega =
      ((descendantsAtScale (originCube d l) k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d l) k,
          cubeAverage R (streamIncrementLpDensity p n m omega) := by
  have hscale : descendantsAtScale (originCube d l) k =
      descendantsAtDepth (originCube d l) (Int.toNat (l - k)) :=
    descendantsAtScale_eq_descendantsAtDepth (originCube d l) hkl
  rw [hscale]
  exact streamIncrementLpMass_eq_descendantsAverage hp l n m (Int.toNat (l - k)) omega

end

end Algsuperdiff.Section3.Provider.Stream
