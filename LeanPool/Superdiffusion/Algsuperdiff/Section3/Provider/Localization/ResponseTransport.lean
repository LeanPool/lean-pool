/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.Breakdown
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffResponseJ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.TriadicCubeTranslation
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeOpenBridge
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Adapters

/-!
# ResponseTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the response transport of the localization breakdown

`Provider/Localization/Breakdown.lean` produces, for the Section 3 carrier, the
display `e.mathcal.E.breakdown` with its two legs `breakdownLegA` /
`breakdownLegB` sitting at the *arbitrary descendant* `R = z + □_l` of `□_m`.
Its consumption interface `breakdownLegA_le_of_paired_bound` /
`breakdownLegB_le_of_paired_bound` demands a bound on

```
J(z + □_l, σ^{-1/2} v, σ^{1/2} v; a)      for every v with |v|^2 ≤ 2,
```

written as `Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (a.coeffOn R)` — the
bundled Chapter 2 functional on the **open** cube realisation `openCubeSet R`.

The Section 3 response *observable* `Observable.cutoffResponseJ M l L e` is, on
one probability-one event and simultaneously in every direction
(`Observable.ae_forall_cutoffResponseJ_eq_literal`), the raw functional

```
ResponseJ (cubeSet (originCube d l)) (σ_L^{-1/2} e) (σ_L^{1/2} e)
  (Cutoff.coefficientCutoff M.nu L ω).toFun
```

on the **half-open** realisation of the **origin** cube only — there is no
translate parameter anywhere in the observable.

This module is the bridge between those two spellings.  It is a proved local
provider: it closes no source node and asserts no estimate.  Every statement
below is an *identity* (or, in the consumption lemmas, a transport of a
hypothesis), so no constant is created or lost anywhere in this file.

## The three components

** Translate transport.**  `responseJ_cutoffFamily_eq_originCube_translate`
moves the response at `R` under the sample `ω` to the response at `originCube d
R.scale` under the translated sample `Cutoff.translateCutoffSample
(triadicCubeShift R) ω`.  No *rescaling* is performed here and none is needed:
`breakdownLeg{A,B}` and the observable both live at the same scale `l`.  The
scale normalisation `□_l → □_0` is a separate, already proved identity
(`Provider/Multiscale/JCarrierRescale.responseJ_originCube_dilate`).

*There is no printed transport, and none is claimed.*  Every display in ABK26
carries `z + □_l` identically on both sides of the estimate; the manuscript
never moves a response of this proof onto the origin cube.  Its mathematical
content is the pathwise change of variables the manuscript does perform
elsewhere ("rescale and translate so that `z + □_n` appears in place of `□_0`"),
and it is an *identity for every sample*: the only probabilistic ingredient, J1
stationarity, moves the almost-sure **event** and nothing else, so no constant,
no estimate and no printed step is created, transported or consumed by it.

**(b) The `openCubeSet` / `cubeSet` response identity.**
`responseJ_cubeDomain_eq_ResponseJ_cubeSet` is an **equality**, in both
directions, at every triadic cube: the bundled Chapter 2 response on
`cubeDomain Q` (carrier `openCubeSet Q`) equals the raw `ResponseJ` on the
half-open `cubeSet Q`.  It is CoarseGraining's
`Internal.Ch02.book_responseJ_eq_ResponseJ` composed with CoarseGraining's
`responseJ_cubeSet_eq_openCubeSet_of_triadicCube`
(`CoarseGraining/OriginCubeOpenBridge.lean`), whose proof reduces the two
`AHarmonicFunction` value sets to one another through the two CoarseGraining
functors `AHarmonicFunction.toCubeSetOriginCube` / `toOpenCubeSetOriginCube`
(`PDE/HarmonicCube.lean`, built on `Sobolev/H1/OriginCubeBridge` together with
`Sobolev/PotentialSolenoidalOriginCubeBridge`), and observes that the two
volume averages agree because the boundary faces are Lebesgue-null.  (The
transfer is *not* `Sobolev/PotentialSolenoidalCubeBridge`, which is only an
ambient import of that CoarseGraining module.)  Since a genuine equality is
available, no inequality direction has to be selected and the transport
composes in both directions.

**(c) The coefficient bridge.**
`coefficientCutoffTriadicCoeffFamily_coeffOn_toCoeffField` holds at **every**
scale `L` and **every** cube `Q`, by `rfl`:

```
((Cutoff.coefficientCutoffTriadicCoeffFamily M L ω).coeffOn Q).toCoeffField
  = (Cutoff.coefficientCutoff M.nu L ω).toFun .
```

The family's per-cube `CoeffOn` object carries the *same* pointwise
representative for every cube — only its locally derived upper-ellipticity
witness varies (`Cutoff/CoefficientFamily.lean`, the `coefficientCutoffCoeffOn`
field `toCoeffField := coefficientCutoff M.nu m ω`) — so no cube-dependence and
no a.e. modification enters.  The `Filter.EventuallyEq.rfl` shape of the proved
`Cutoff.coefficientCutoffTriadicCoeffFamily_coeffOn_aeeq` is a consequence of
this, not a restriction to `L = m`: the family's *scale* argument is a free
parameter, and the observable's `coefficientScale` argument is free as well.
There is therefore no carrier obstruction at `L ≠ m`, and none is claimed to be
bridged: `Cutoff.coefficientCutoff M.nu m ω` and `Cutoff.coefficientCutoff M.nu
L ω` are genuinely *different coefficient fields* for `L ≠ m`, and passing
between them is the manuscript's `l.J.sensitivity` step (
`e.J.sensitivity.apppp`), i.e. mathematics, not a spelling change.

## What is deliberately *not* here

* The comparator change `σ_m → σ_{l-h}` (`e.shaking.lambda` at `λ = σ_m
  σ_{l-h}^{-1}`) is the comparator normalization of
  `Localization/SwitchNormalization.lean`.  Every deterministic statement in
  this module leaves the comparator `sigma: Observable.PositiveScalar` free,
  so that the transport itself commits to nothing.  The almost-sure
  statements that mention `Observable.cutoffResponseJ` specialise to `sigma
  = Annealed.sigmaBar M L` because the observable pins its loads to `σ_L`.
* The coefficient change `a_m → a_{l-h}` (`e.J.sensitivity.apppp`).
* Any bound whatsoever.  The consumption lemmas take the per-cube bound as a
  *hypothesis of a universally quantified statement*, never as a binder of the
  theorem.

## Main results

* `responseJ_cubeDomain_eq_ResponseJ_cubeSet` — component (b), an equality.
* `coefficientCutoffTriadicCoeffFamily_coeffOn_toCoeffField` and its adjoint
  twin — component (c), at every scale.
* `responseJ_cutoffFamily_eq_originCube_translate` and its adjoint twin —
  component, pathwise, at a free comparator and a free coefficient scale.
* `responseJ_cutoffFamily_eq_ResponseJ_originCube_translate` — the same
  transport proved in the observable's own raw `ResponseJ`/`cubeSet` spelling.
* `ae_forall_responseJ_cutoffFamily_eq_cutoffResponseJ_translate` — the a.e.
  endpoint: on **one** event, for **every** triadic cube `R`, **every**
  coefficient-cutoff scale `L` and **every** loading `v`, the demanded
  `Book.Ch02.responseJ` at `R` is the observable
  `Observable.cutoffResponseJ M R.scale L v` read at the translated sample.  The
  coefficient scale is *inside* the event, at zero import cost, so one and the
  same event serves the coefficient before and after the `J`-sensitivity step.
  `ae_forall_descendant_responseJ_cutoffFamily_eq_cutoffResponseJ_translate` is
  its restriction to `descendantsAtScale (originCube d m) l`.
* `breakdownLegA_le_of_originCube_translate_bound` /
  `breakdownLegB_le_of_originCube_translate_bound` — the
  composition with `Breakdown`'s consumption interface, pathwise and at a free
  comparator.

## A.e. structure

The single null set is the one produced by the **all-`L`** literal
identification
`Observable.ae_forall_coefficientScale_cutoffResponseJ_eq_literal`
(`Section3/Observable/CutoffResponseJ.lean`), intersected over the *countable*
type `TriadicCube d` after each member has been pulled back along the
measure-preserving translation `Cutoff.translateCutoffSample`
(`Cutoff.map_translateCutoffSample_cutoffSampleLaw`, the J1 stationarity
descent).  Using the all-`L` variant rather than its fixed-`L` companion
`Observable.ae_forall_cutoffResponseJ_eq_literal` costs nothing: the two live
in the same module, and the all-`L` one is itself only `ae_all_iff` over the
countable index `ℤ`.  So the coefficient scale is quantified *inside* the event
here as well, and both countable intersections (over cubes and over scales) are
already paid for.  The uncountable direction quantifier stays inside each
fixed-cube, fixed-scale event, where the verified common full-block
representative already placed it.  Every deterministic statement in this module
is universally quantified with no null set at all.

## References

* ABK26 (`e.mathcal.E.breakdown`, the legs at `z + □_l`).
* ABK26, the comparator change; the switch acts pointwise inside the response.
* ABK26 (`e.J.sensitivity.apppp`, the coefficient change).
* ABK26 (the proof in full: every display carries `z + □_l` identically on both
  sides, so no transport is printed anywhere in it).
* ABK26 (the manuscript's own "rescale and translate so that `z + □_n` appears
  in place of `□_0`" — the pathwise change of variables whose character the
  translation performed here matches).
* ABK26, (2.4), the definition of `J(U, p, q; a)`.
-/

namespace Algsuperdiff.Section3.Provider.Localization

-- `_root_` is load-bearing: `Algsuperdiff.Section3.Provider.Homogenization` is a live
-- sibling namespace, so a bare `open Homogenization` resolves to it once any
-- `Provider.Homogenization` module enters this file's import closure.  The closure
-- currently contains none; the counterfactual probe shadows every root-`Homogenization`
-- identifier this file uses (rc=1, 40+ unknown identifiers).
open _root_.MeasureTheory
open _root_.HCPolySupport
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Component (b): the `openCubeSet` / `cubeSet` response identity -/

/-- **The bundled Chapter 2 response on a triadic cube is the raw response on
its half-open realisation.**  `Book.Ch02.cubeDomain Q` carries `openCubeSet Q`,
while the Section 3 observable is written on `cubeSet Q`; the two responses are
*equal*, so the transport below composes in both directions and no inequality
direction has to be selected.

This is CoarseGraining's internal adapter
`Internal.Ch02.book_responseJ_eq_ResponseJ` followed by CoarseGraining's
`responseJ_cubeSet_eq_openCubeSet_of_triadicCube`, which matches the two
`AHarmonicFunction` value sets and uses that the boundary faces of a triadic
cube are Lebesgue-null. -/
theorem responseJ_cubeDomain_eq_ResponseJ_cubeSet [NeZero d] (Q : TriadicCube d)
    (b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (p q : Vec d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) b p q =
      ResponseJ (cubeSet Q) p q b.toCoeffField := by
  rw [HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ,
    responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
  rfl

/-! ## Component (c): the coefficient carrier bridge, at every scale -/

/-- **The cutoff family's per-cube representative is the cutoff field itself, at
every scale and every cube.**  `Cutoff.coefficientCutoffTriadicCoeffFamily`
assigns the *same* pointwise coefficient field to every triadic cube; only the
locally derived upper-ellipticity witness depends on the cube.  In particular the
family's scale argument `L` is free: nothing in this identity restricts it to the
scale of the enclosing cube. -/
theorem coefficientCutoffTriadicCoeffFamily_coeffOn_toCoeffField (M : ABKModel d)
    (L : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) :
    ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn Q).toCoeffField =
      (coefficientCutoff M.nu L omega).toFun :=
  rfl

/-- The adjoint twin of
`coefficientCutoffTriadicCoeffFamily_coeffOn_toCoeffField`: the transposed
per-cube representative is the pointwise transpose of the cutoff field. -/
theorem coefficientCutoffTriadicCoeffFamily_coeffOn_transpose_toCoeffField
    (M : ABKModel d) (L : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) :
    ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn Q).transpose.toCoeffField =
      fun x => matTranspose ((coefficientCutoff M.nu L omega).toFun x) :=
  rfl

/-! ## Component: the translate transport -/

/-- **Translation to the origin cube, at the raw carrier.**  Every triadic cube is
the translate of the origin cube at its own scale by CoarseGraining's canonical
base point `triadicCubeShift`, and `ResponseJ` is covariant under translations
of the domain. -/
theorem ResponseJ_cubeSet_eq_originCube_translateCoeffField (Q : TriadicCube d)
    (p q : Vec d) (a : CoeffField d) :
    ResponseJ (cubeSet Q) p q a =
      ResponseJ (cubeSet (originCube d Q.scale)) p q
        (translateCoeffField (triadicCubeShift Q) a) := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q,
    ResponseJ_translateSet_eq_translateCoeffField]

/-- **Translating the coefficient field is translating the sample.**  This is
`Cutoff.coefficientCutoff_translateCutoffSample` read in the raw `CoeffField`
spelling used by `ResponseJ`. -/
theorem translateCoeffField_coefficientCutoff (nu : ℝ) (L : ℤ) (z : Vec d)
    (omega : CutoffSample d) :
    translateCoeffField z (coefficientCutoff nu L omega).toFun =
      (coefficientCutoff nu L (translateCutoffSample z omega)).toFun := by
  rw [coefficientCutoff_translateCutoffSample]
  rfl

/-- **The response transport, in the observable's own spelling.**  The demanded
bundled response of the cutoff family at an arbitrary triadic cube `R` is the raw
response, on the half-open origin cube of the same scale, of the cutoff field at
the translated sample.  The comparator does not appear: the identity holds at
every pair of loads `p`, `q`, hence at every comparator the switch step may
choose. -/
theorem responseJ_cutoffFamily_eq_ResponseJ_originCube_translate [NeZero d]
    (M : ABKModel d) (L : ℤ) (R : TriadicCube d) (p q : Vec d)
    (omega : CutoffSample d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) p q =
      ResponseJ (cubeSet (originCube d R.scale)) p q
        (coefficientCutoff M.nu L
          (translateCutoffSample (triadicCubeShift R) omega)).toFun := by
  rw [responseJ_cubeDomain_eq_ResponseJ_cubeSet,
    coefficientCutoffTriadicCoeffFamily_coeffOn_toCoeffField,
    ResponseJ_cubeSet_eq_originCube_translateCoeffField,
    translateCoeffField_coefficientCutoff]

/-- The adjoint twin of
`responseJ_cutoffFamily_eq_ResponseJ_originCube_translate`. -/
theorem responseJ_cutoffFamily_transpose_eq_ResponseJ_originCube_translate [NeZero d]
    (M : ABKModel d) (L : ℤ) (R : TriadicCube d) (p q : Vec d)
    (omega : CutoffSample d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R).transpose p q =
      ResponseJ (cubeSet (originCube d R.scale)) p q
        (fun x => matTranspose ((coefficientCutoff M.nu L
          (translateCutoffSample (triadicCubeShift R) omega)).toFun x)) := by
  rw [responseJ_cubeDomain_eq_ResponseJ_cubeSet,
    coefficientCutoffTriadicCoeffFamily_coeffOn_transpose_toCoeffField,
    ResponseJ_cubeSet_eq_originCube_translateCoeffField]
  change ResponseJ (cubeSet (originCube d R.scale)) p q
      (fun x => matTranspose (translateCoeffField (triadicCubeShift R)
        (coefficientCutoff M.nu L omega).toFun x)) = _
  rw [translateCoeffField_coefficientCutoff]

/-- **The response transport, in the bundled Chapter 2 spelling.**  The demanded
response at `R` under `ω` is the response at the origin cube of the same scale
under the translated sample, both read through the cutoff family at the same
coefficient scale `L`.  This is the form in which the comparator normalization
consumes the transport, since that step is stated at the manuscript's own `J(·;
a_m)`. -/
theorem responseJ_cutoffFamily_eq_originCube_translate [NeZero d] (M : ABKModel d)
    (L : ℤ) (R : TriadicCube d) (p q : Vec d) (omega : CutoffSample d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) p q =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
        ((coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
            (originCube d R.scale)) p q := by
  rw [responseJ_cutoffFamily_eq_ResponseJ_originCube_translate,
    responseJ_cubeDomain_eq_ResponseJ_cubeSet,
    coefficientCutoffTriadicCoeffFamily_coeffOn_toCoeffField]

/-- The adjoint twin of `responseJ_cutoffFamily_eq_originCube_translate`. -/
theorem responseJ_cutoffFamily_transpose_eq_originCube_translate [NeZero d]
    (M : ABKModel d) (L : ℤ) (R : TriadicCube d) (p q : Vec d)
    (omega : CutoffSample d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R).transpose p q =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
        ((coefficientCutoffTriadicCoeffFamily M L
          (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
            (originCube d R.scale)).transpose p q := by
  rw [responseJ_cutoffFamily_transpose_eq_ResponseJ_originCube_translate,
    responseJ_cubeDomain_eq_ResponseJ_cubeSet,
    coefficientCutoffTriadicCoeffFamily_coeffOn_transpose_toCoeffField]

/-! ## The almost-sure endpoint through the Section 3 observable -/

/-- The cutoff-sample law is invariant under a real translation of the shell
field, in the `MeasurePreserving` spelling.

Kept private: it duplicates the proved public
`measurePreserving_translateCutoffSample` of
`Provider/Diffusivity/ApproximateRecurrence/Closure/GammaTenCloserMoments.lean`
verbatim, and is re-derived here only so that this carrier-only module does not
acquire that module's frozen-anchor import closure. -/
private theorem measurePreserving_translate (M : ABKModel d) (z : Vec d) :
    MeasurePreserving (translateCutoffSample (d := d) z)
      (cutoffSampleLaw M).toMeasure (cutoffSampleLaw M).toMeasure :=
  ⟨measurable_translateCutoffSample z, map_translateCutoffSample_cutoffSampleLaw M z⟩

/-- **The unit-D endpoint.**  On *one* probability-one event, simultaneously for
every triadic cube `R`, every coefficient-cutoff scale `L` and every loading
vector `v`, the response demanded by `Breakdown`'s consumption interface at `R`
is the Section 3 observable `Observable.cutoffResponseJ M R.scale L v` read at
the translated sample `translateCutoffSample (triadicCubeShift R) ω`.

The coefficient scale is *inside* the event: the all-`L` identification
`Observable.ae_forall_coefficientScale_cutoffResponseJ_eq_literal` is available at
zero import cost (same module as the fixed-`L` one), so no null set is spent on
`L` beyond the one intersection over the countable index `ℤ` that lemma already
performs.  This is what the `J`-sensitivity step needs, since it moves the
coefficient scale from `m` to `l - h` on the same event.

The loads are the observable's own `σ_L`-pair, which is the comparator the
observable pins; the free-comparator form of the transport is the deterministic
`responseJ_cutoffFamily_eq_originCube_translate` above.

The null set is the one of
`Observable.ae_forall_coefficientScale_cutoffResponseJ_eq_literal`, pulled back
along the measure-preserving translation and intersected over the countable type
`TriadicCube d`; the uncountable direction quantifier stays inside each
fixed-cube event. -/
theorem ae_forall_responseJ_cutoffFamily_eq_cutoffResponseJ_translate [NeZero d]
    (M : ABKModel d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (R : TriadicCube d) (L : ℤ) (v : Vec d),
        Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
            ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) v)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) v) =
          Observable.cutoffResponseJ M R.scale L v
            (translateCutoffSample (triadicCubeShift R) omega) := by
  rw [MeasureTheory.ae_all_iff]
  intro R
  filter_upwards [(measurePreserving_translate M (triadicCubeShift R)).quasiMeasurePreserving.ae
    (Observable.ae_forall_coefficientScale_cutoffResponseJ_eq_literal M R.scale)]
    with omega homega
  intro L v
  rw [homega L v, responseJ_cutoffFamily_eq_ResponseJ_originCube_translate]

/-- The descendant restriction of
`ae_forall_responseJ_cutoffFamily_eq_cutoffResponseJ_translate`: on the same
event, and still simultaneously in the coefficient scale `L`, every descendant
`R = z + □_l` of `□_m` is read at the observable's cube scale `l`. -/
theorem ae_forall_descendant_responseJ_cutoffFamily_eq_cutoffResponseJ_translate
    [NeZero d] (M : ABKModel d) {m l : ℤ} (hlm : l ≤ m) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ R ∈ descendantsAtScale (originCube d m) l, ∀ (L : ℤ) (v : Vec d),
        Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
            ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) v)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) v) =
          Observable.cutoffResponseJ M l L v
            (translateCutoffSample (triadicCubeShift R) omega) := by
  filter_upwards [ae_forall_responseJ_cutoffFamily_eq_cutoffResponseJ_translate M]
    with omega homega
  intro R hR L v
  have hscale : R.scale = l :=
    Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube hlm hR
  rw [homega R L v, hscale]

/-! ## Composition with the breakdown legs -/

/-- **The primal leg from a bound at the translated origin cube.**  A per-cube
bound on the response at `□_{R.scale}` for the translated sample, uniform over
loading vectors of squared length at most `2`, bounds `breakdownLegA` at `R`.

Pathwise, and at a free comparator `sigma`.  The comparator is left free so
that the caller may choose it, but the instantiation that serves the carrier
endpoint is `sigma := Annealed.sigmaBar M m`: that is the comparator matrix
`Breakdown.cutoffHomogenizationError_sq_ae_le_breakdown` reads its legs at, and
a leg produced at `sigma := σ_{l-h}` is simply not the leg that endpoint
accepts.  The comparator normalization is not a re-instantiation of `sigma`: it
acts *pointwise inside* the response (→ 9313 replaces the loads `σ_m^{∓1/2} e`
by `σ_{l-h}^{∓1/2} e` on the same cube `z + □_l` and the same coefficient
`a_m`, at the price of an additive `σ_{m,*}^{-1}` remainder), so it is
discharged **inside the hypothesis `h`**, with `sigma` still `σ_m`.

The per-cube bound is a hypothesis of the statement, not a premise of the module:
nothing here asserts that such a bound holds. -/
theorem breakdownLegA_le_of_originCube_translate_bound [NeZero d] (M : ABKModel d)
    (L : ℤ) (R : TriadicCube d) (omega : CutoffSample d)
    (sigma : Observable.PositiveScalar) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M L
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale))
          (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤ c) :
    breakdownLegA R (coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma) ≤ c := by
  refine breakdownLegA_le_of_paired_bound R _ sigma hc ?_
  intro v hv
  rw [responseJ_cutoffFamily_eq_originCube_translate]
  exact h v hv

/-- **The adjoint leg from a bound at the translated origin cube.**  The adjoint
twin of `breakdownLegA_le_of_originCube_translate_bound`; the transported
coefficient object is the transpose, exactly as in
`breakdownLegB_le_of_paired_bound`.

The comparator reading is the same as for the primal leg: the instantiation
that serves `Breakdown.cutoffHomogenizationError_sq_ae_le_breakdown` is
`sigma:= Annealed.sigmaBar M m`, with the comparator change discharged
pointwise inside the hypothesis `h`, not by instantiating `sigma :=
σ_{l-h}`. -/
theorem breakdownLegB_le_of_originCube_translate_bound [NeZero d] (M : ABKModel d)
    (L : ℤ) (R : TriadicCube d) (omega : CutoffSample d)
    (sigma : Observable.PositiveScalar) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d R.scale))
          ((coefficientCutoffTriadicCoeffFamily M L
            (translateCutoffSample (triadicCubeShift R) omega)).coeffOn
              (originCube d R.scale)).transpose
          (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤ c) :
    breakdownLegB R (coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix sigma) ≤ c := by
  refine breakdownLegB_le_of_paired_bound R _ sigma hc ?_
  intro v hv
  rw [responseJ_cutoffFamily_transpose_eq_originCube_translate]
  exact h v hv

end

end Algsuperdiff.Section3.Provider.Localization
