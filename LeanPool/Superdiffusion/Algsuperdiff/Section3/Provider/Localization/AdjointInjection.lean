/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.LambdaGateChain

/-!
# AdjointInjection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the `(J3)` adjoint leg of the localization `J`-injection

ABK26: the `lambda`-gate chain, and the injection display
`e.J.sensitivity.apppp`, read at the **transposed** representative `a^t`.

## What is delivered, and why it is not a rearrangement

The manuscript prints the localization `J`-injection only at the primal
coefficient, while the buckle's deep `J`-sum `T2` needs it at `a^t`.

The transpose statement is not obtained by a deterministic rearrangement of the
primal one.  This is a precise claim and not a claim that no deterministic
transpose-response identity exists: one does, it is proved, it is in this
file's closure, and it is disclosed below
(`responseJ_transpose_neg_right` in
`Section24/Sensitivity/Provider/DhBound/Discharge/AdjointResponse.lean`, `J(U,
a^t, p, -q) = J(U, a, p, q) + 2 p . q`). What that identity cannot do is close
the injection, because it is off-diagonal: at the manuscript's own loadings `p =
shom^{-1/2} v`, `q = shom^{1/2} v` it relates the transposed value at `v` to the
primal value at the loading `(p(v), q(-v))`, which is `(p(w), q(w))` for no `w`
at all -- that would force `w = v` and `w = -v` simultaneously -- while the
primal injection endpoint prices only the diagonal pair. So the deterministic
route is genuinely unavailable and the law-level route is genuinely required.
That route is a symmetry of the law, and exactly the one `(J3)` supplies; it is
the route taken here:

* negating every layer, `j_n |-> -j_n`, transposes the lower-infinite field,
  because each layer is antisymmetric and `a_m = nu Id + k_m` with `k_m` skew:
  this is the proved pointwise identity
  `Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint`;
* the joint law is negation invariant: this is the proved
  `Cutoff.map_negateCutoffSample_cutoffSampleLaw`, which descends from the
  frozen `M.J3.negation` (`a.j.iso`);
* hence the adjoint site at `omega` is almost surely the primal site at the
  negated sample, and every quantity the primal endpoint prices -- the
  `W-underline^{2,infinity}` gauge, the good local event, the `lambda`
  observable -- is negation invariant, so the price is carried at the SAME
  level.

Nothing here re-derives the sensitivity engine at a negated perturbation field:
the primal endpoint is consumed verbatim and evaluated at the negated sample.

## 1. The `(J3)` invariance layer (section 1 below)

The layer the composition needs, in the order it is built:

* the three exact `L-infinity` shell gauges are negation invariant
  (`unitCubeDerivNorm_negate`, `unitCubeSecondDerivNorm_negate`, and the proved
  `Cutoff.localCubeControl_negate` for the zeroth order), hence so are
  `underlineW2Gauge` and `BadEvents.cubeOscGauge`, hence so is the good event's
  own gauge `incrementOscGauge₂`;
* the cutoff triadic family at the negated sample is a.e. the adjoint family
  (`coefficientCutoffTriadicCoeffFamily_negateCutoffSample_aeEq`), so
  `lambdaSq` is negation invariant (`lambdaSq_negateCutoffSample`, through the
  proved `CoarseEllipticity.lambdaSq_adjointFamily`);
* therefore the good local event `Q(l,n,z)` is negation invariant almost surely
  (`mem_goodLocalEvent_negateCutoffSample_ae`): its sensitivity clause exactly,
  its ellipticity clause through the measurable representative's own a.e.
  identification `BadEvents.cubeLowerEllipticity_ae_eq_literal`.  The
  representative `cubeLowerEllipticity` is an `A.mk` choice, so this clause is
  genuinely only almost sure -- which is all the consumer needs, since the
  endpoint is itself an almost-sure statement.

## 3. The transposed priced endpoint (section 3 below)

`responseJ_transpose_injection_priced_forall_loads_of_primal` carries the primal
per-`(l,z)` priced injection display to the transposed representative, at the
same loadings `p = shom_{l-h}^{-1/2} v`, `q = shom_{l-h}^{1/2} v`, the same
leading constant `3` and the same remainder

```
324 C_resp (16 Ccg + 8 Ccg^2) cstar^{-1} cgamma 3^{4l - 2 cgamma l}
  ||k_m - k_{l-h}||^2_{W-underline^{2,infinity}(z+cu_l)} ,
```

## The scale gate on `m0`

The landmark premise carried by every statement below is `mStarStar M < m0`,
**not** the printed `m0 in (mstar, infty) cap Z`.  Nothing else moved: the
premise is forwarded verbatim to the proved statements consumed here, no proof
step here consumes it, and no frozen statement changes --
`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics` keeps the printed `mStar
M < m0` and reaches the weaker-gated chain a fortiori through
`Provider.Scales.mStarStar_le_mStar`.

## Related statements elsewhere

The `c >= 0` amplitude-scaling twins
`Stream.unitCubeDerivNorm_scale_of_nonneg` and
`Stream.unitCubeSecondDerivNorm_scale_of_nonneg` are *not* usable here:
`ShellField.negate = ShellField.scale (-1)`, and the sign hypothesis `0 <= c`
fails at `c = -1`.  The route taken instead is the sharp characterization pair
`Stream.unitCubeDerivNorm_le_iff` / `Stream.unitCubeSecondDerivNorm_le_iff'`
composed with `ShellField.matrixDerivativeNorm_neg`, which is exact.  Its
second-derivative companion `matrixSecondDerivativeNorm_neg` is proved below,
from `ShellField.matrixSecondDerivativeNorm_le_iff` in both directions.

## References

* ABK26, `l.localization.mathcalE` and its `lambda`-gate,
  `e.J.sensitivity.apppp`, the adjoint deep `J`-sum, `(J3)`, `a.j.iso`,
  `e.good.local.events`.
* ABK26: the manuscript makes the same inference explicitly there, deducing
  `khom_m(U) = 0` from `e.adjoint.redundant` and the assumption `a.j.iso` that
  `a_m` has the same law as `a_m^t`.  The step this file performs at the
  localization display --- `a_m` and `a_m^t` are equidistributed by `(J3)`,
  hence a priced primal statement transfers to the transpose at the same level
  --- is that same move at a different functional; nothing in the route
  depends on it.
* `negateCutoffSample` is exactly the whole-sequence action.
-/

namespace Algsuperdiff.Section3.Provider.Localization

open _root_.MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book _root_.HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.MultiscaleEstimate
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## 1. The `(J3)` invariance layer

In ABK26, negation acts on the whole shell sequence and preserves the joint law.
This section proves that every quantity the injection prices is invariant under
that action. -/

/-! ### 1.1 The exact shell gauges -/

/-- The exact twice-induced norm is even.  (Its first-order companion is the proved
simp lemma `ShellField.matrixDerivativeNorm_neg`; the repository carries no
second-order version.) -/
theorem matrixSecondDerivativeNorm_neg (H : ShellField.MatrixSecondDerivative d) :
    ShellField.matrixSecondDerivativeNorm (-H) =
      ShellField.matrixSecondDerivativeNorm H := by
  have hpt : ∀ u : Vec d,
      ShellField.matrixDerivativeNorm ((-H) u) =
        ShellField.matrixDerivativeNorm (H u) := by
    intro u
    have hval : (-H) u = -(H u) := rfl
    rw [hval, ShellField.matrixDerivativeNorm_neg]
  refine le_antisymm ?_ ?_
  · rw [ShellField.matrixSecondDerivativeNorm_le_iff]
    refine ⟨ShellField.matrixSecondDerivativeNorm_nonneg H, fun u hu => ?_⟩
    rw [hpt u]
    exact ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H u hu
  · rw [ShellField.matrixSecondDerivativeNorm_le_iff]
    refine ⟨ShellField.matrixSecondDerivativeNorm_nonneg (-H), fun u hu => ?_⟩
    rw [← hpt u]
    exact ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm (-H) u hu

/-- The exact open-unit-cube first-derivative `L-infinity` norm is even. -/
theorem unitCubeDerivNorm_negate (j : ShellField d) :
    ShellField.unitCubeDerivNorm (ShellField.negate j) =
      ShellField.unitCubeDerivNorm j := by
  have hpt : ∀ y : Vec d,
      ShellField.matrixDerivativeNorm (ShellField.deriv (ShellField.negate j) y) =
        ShellField.matrixDerivativeNorm (ShellField.deriv j y) := by
    intro y
    rw [ShellField.negate_deriv, ShellField.matrixDerivativeNorm_neg]
  refine le_antisymm ?_ ?_
  · rw [unitCubeDerivNorm_le_iff]
    refine ⟨ShellField.unitCubeDerivNorm_nonneg j, fun y hy => ?_⟩
    rw [hpt y]
    exact matrixDerivativeNorm_deriv_le_unitCubeDerivNorm j hy
  · rw [unitCubeDerivNorm_le_iff]
    refine ⟨ShellField.unitCubeDerivNorm_nonneg _, fun y hy => ?_⟩
    rw [← hpt y]
    exact matrixDerivativeNorm_deriv_le_unitCubeDerivNorm (ShellField.negate j) hy

/-- The exact open-unit-cube second-derivative `L-infinity` norm is even. -/
theorem unitCubeSecondDerivNorm_negate (j : ShellField d) :
    ShellField.unitCubeSecondDerivNorm (ShellField.negate j) =
      ShellField.unitCubeSecondDerivNorm j := by
  have hpt : ∀ y : Vec d,
      ShellField.matrixSecondDerivativeNorm
          (ShellField.secondDeriv (ShellField.negate j) y) =
        ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j y) := by
    intro y
    rw [ShellField.negate_secondDeriv, matrixSecondDerivativeNorm_neg]
  refine le_antisymm ?_ ?_
  · rw [unitCubeSecondDerivNorm_le_iff']
    refine ⟨ShellField.unitCubeSecondDerivNorm_nonneg j, fun y hy => ?_⟩
    rw [hpt y]
    exact matrixSecondDerivativeNorm_secondDeriv_le_unitCubeSecondDerivNorm j hy
  · rw [unitCubeSecondDerivNorm_le_iff']
    refine ⟨ShellField.unitCubeSecondDerivNorm_nonneg _, fun y hy => ?_⟩
    rw [← hpt y]
    exact matrixSecondDerivativeNorm_secondDeriv_le_unitCubeSecondDerivNorm
      (ShellField.negate j) hy

/-- Spatial rescaling commutes with negation.  (A `private` twin of the same
statement sits in `Section3/Cutoff/Symmetry.lean`; see the header.) -/
theorem spatialScale_negate (r : ℝ) (j : ShellField d) :
    ShellField.spatialScale r (ShellField.negate j) =
      ShellField.negate (ShellField.spatialScale r j) := by
  apply ShellField.ext
  intro x
  simp only [ShellField.spatialScale_apply, ShellField.negate_apply]

/-- Translation commutes with negation. -/
theorem translate_negate (z : Vec d) (j : ShellField d) :
    ShellField.translate z (ShellField.negate j) =
      ShellField.negate (ShellField.translate z j) := by
  apply ShellField.ext
  intro x
  simp only [ShellField.translate_apply, ShellField.negate_apply]

/-- The exact local first-derivative gauge is even. -/
theorem localCubeDerivNorm_negate (ell : ℤ) (j : ShellField d) :
    localCubeDerivNorm ell (ShellField.negate j) = localCubeDerivNorm ell j := by
  rw [localCubeDerivNorm, localCubeDerivNorm, spatialScale_negate,
    unitCubeDerivNorm_negate]

/-- The exact local second-derivative gauge is even. -/
theorem localCubeSecondDerivNorm_negate (ell : ℤ) (j : ShellField d) :
    localCubeSecondDerivNorm ell (ShellField.negate j) =
      localCubeSecondDerivNorm ell j := by
  rw [localCubeSecondDerivNorm, localCubeSecondDerivNorm, spatialScale_negate,
    unitCubeSecondDerivNorm_negate]

/-- **The manuscript's `W-underline^{2,infinity}` gauge is even.**  All three
`max`-entries are: the second-order and first-order legs by the two lemmas
above, the zeroth-order leg by the proved `Cutoff.localCubeControl_negate`. -/
theorem underlineW2Gauge_negate (Q : TriadicCube d) (h : ShellField d) :
    underlineW2Gauge Q (ShellField.negate h) = underlineW2Gauge Q h := by
  rw [underlineW2Gauge, underlineW2Gauge, translate_negate,
    localCubeSecondDerivNorm_negate, localCubeDerivNorm_negate,
    localCubeControl_negate]

/-- The good event's own oscillation gauge is even. -/
theorem cubeOscGauge_negate (Q : TriadicCube d) (h : ShellField d) :
    cubeOscGauge Q (ShellField.negate h) = cubeOscGauge Q h := by
  rw [cubeOscGauge, cubeOscGauge, translate_negate, localCubeDerivNorm_negate,
    localCubeSecondDerivNorm_negate]

/-- Negating the whole shell sequence negates the finite increment `k_L - k_n`. -/
theorem shellIncrement_negateSequence (omega : ShellSeq d) (n L : ℤ) :
    shellIncrement (ShellField.negateSequence omega) n L =
      ShellField.negate (shellIncrement omega n L) := by
  apply ShellField.ext
  intro x
  simp only [shellIncrement, ShellField.sum_apply, ShellField.negate_apply,
    ShellField.negateSequence_apply]
  rw [← Finset.sum_neg_distrib]

/-- The two-index gauge of `e.good.local.events` is invariant under the `(J3)`
negation action on the cutoff carrier. -/
theorem incrementOscGauge₂_negateCutoffSample (Q : TriadicCube d) (n L : ℤ)
    (omega : CutoffSample d) :
    incrementOscGauge₂ Q n L (negateCutoffSample omega) =
      incrementOscGauge₂ Q n L omega := by
  rw [incrementOscGauge₂, incrementOscGauge₂, negateCutoffSample_val,
    shellIncrement_negateSequence, cubeOscGauge_negate]

/-- The `W-underline^{2,infinity}` gauge of the increment is invariant under the
`(J3)` negation action on the cutoff carrier. -/
theorem underlineW2Gauge_shellIncrement_negateCutoffSample (Q : TriadicCube d)
    (n L : ℤ) (omega : CutoffSample d) :
    underlineW2Gauge Q (shellIncrement (negateCutoffSample omega).1 n L) =
      underlineW2Gauge Q (shellIncrement omega.1 n L) := by
  rw [negateCutoffSample_val, shellIncrement_negateSequence,
    underlineW2Gauge_negate]

/-! ### 1.2 The coefficient carrier and the multiscale observable -/

/-- **The `(J3)` carrier identity, at the triadic family level.**  The cutoff
family of the negated sample is, a.e. on every cube, the adjoint family of the
cutoff family of the sample.  This is the proved pointwise identity
`Cutoff.coefficientCutoff_negateCutoffSample_eq_adjoint` (`a_m(-omega) =
a_m(omega)^t`, itself a consequence of the proved skewness of the genuine
lower-infinite cutoff) read through the family's own representative. -/
theorem coefficientCutoffTriadicCoeffFamily_negateCutoffSample_aeEq
    (M : ABKModel d) (n : ℤ) (omega : CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq
      (coefficientCutoffTriadicCoeffFamily M n (negateCutoffSample omega))
      (adjointFamily (coefficientCutoffTriadicCoeffFamily M n omega)) := by
  intro Q
  refine Filter.Eventually.of_forall fun x => ?_
  have hx := congrArg (fun a : RegCoeffField d => a x)
    (coefficientCutoff_negateCutoffSample_eq_adjoint (d := d) M.nu n omega)
  change coefficientCutoff M.nu n (negateCutoffSample omega) x =
    matTranspose (coefficientCutoff M.nu n omega x)
  change coefficientCutoff M.nu n (negateCutoffSample omega) x =
    adjointReg (coefficientCutoff M.nu n omega) x at hx
  rw [hx, adjointReg_apply]
  rfl

/-- **The multiscale lower ellipticity is `(J3)`-invariant.**  Composing the
carrier identity above with the proved
`CoarseEllipticity.lambdaSq_adjointFamily` (`lambda_{s,q}(Q; a^t) =
lambda_{s,q}(Q; a)`). -/
theorem lambdaSq_negateCutoffSample (M : ABKModel d) (n : ℤ)
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (omega : CutoffSample d) :
    Ch02.lambdaSq Q s q
        (coefficientCutoffTriadicCoeffFamily M n (negateCutoffSample omega)) =
      Ch02.lambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M n omega) := by
  rw [Ch02.lambdaSq_eq_ofAEEq
    (coefficientCutoffTriadicCoeffFamily_negateCutoffSample_aeEq M n omega) Q s q,
    lambdaSq_adjointFamily]

/-! ### 1.3 Almost-sure transport along the two carrier actions -/

/-- Almost-sure statements travel along the `(J3)` sample negation, because the
genuine cutoff sample law is invariant under it
(`Cutoff.map_negateCutoffSample_cutoffSampleLaw`, which descends from the frozen
`M.J3.negation`). -/
theorem ae_comp_negateCutoffSample (M : ABKModel d)
    {P : CutoffSample d → Prop}
    (h : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, P omega) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, P (negateCutoffSample omega) := by
  have hmap : ∀ᵐ omega ∂Measure.map (negateCutoffSample (d := d))
      (cutoffSampleLaw M).toMeasure, P omega := by
    rw [map_negateCutoffSample_cutoffSampleLaw]
    exact h
  exact ae_of_ae_map measurable_negateCutoffSample.aemeasurable hmap

/-! ### 1.4 The good local event -/

/-- **The good local event `Q(l,n,z)` is `(J3)`-invariant, almost surely.**

Its sensitivity clause is invariant (`incrementOscGauge₂_negateCutoffSample`);
its ellipticity clause is invariant only almost surely, because
`BadEvents.cubeLowerEllipticity` is an `A.mk` representative of
`lambda_{1/8,2}(z+cu_l; a_n)` and a choice of representative need not commute
with the negation pointwise.  Both readings of the representative are pinned to
the literal observable by the proved
`BadEvents.cubeLowerEllipticity_ae_eq_literal`, and the literal one is
invariant by `lambdaSq_negateCutoffSample`.

This is the file's only genuinely new a.e. ingredient beyond those already
carried; it is stated as an implication, which is the direction the composition
of section 3 consumes. -/
theorem mem_goodLocalEvent_negateCutoffSample_ae (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n : ℤ) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        negateCutoffSample omega ∈ goodLocalEvent M Ccg Q n := by
  have hlit : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega =
        Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2)
          (coefficientCutoffTriadicCoeffFamily M n omega) := by
    filter_upwards [cubeLowerEllipticity_ae_eq_literal M Q n (1 / 8) (by norm_num)
      exponentTwo] with omega homega
    rw [homega, cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, exponentTwo_val]
  filter_upwards [hlit, ae_comp_negateCutoffSample M hlit] with omega hone hneg homega
  obtain ⟨hsens, hell⟩ := (mem_goodLocalEvent_iff M Ccg Q n omega).1 homega
  refine (mem_goodLocalEvent_iff M Ccg Q n (negateCutoffSample omega)).2 ⟨?_, ?_⟩
  · intro L hL
    rw [incrementOscGauge₂_negateCutoffSample]
    exact hsens L hL
  · rw [hneg, lambdaSq_negateCutoffSample, ← hone]
    exact hell

/-! ## 3. The transposed priced injection endpoint
 The gate at the transposed representative, by the `(J3)` law-level negation
 symmetry. -/

/-- The `(J3)` transport of the demanded response: the response of the cutoff
family at the negated sample is the response of the T representative at the
sample. -/
theorem responseJ_cutoffFamily_negateCutoffSample (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) (p q : Vec d) (omega : CutoffSample d) :
    Ch02.responseJ (Ch02.cubeDomain Q)
        ((coefficientCutoffTriadicCoeffFamily M L
          (negateCutoffSample omega)).coeffOn Q) p q =
      Ch02.responseJ (Ch02.cubeDomain Q)
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn Q).transpose p q := by
  rw [Ch02.responseJ_eq_ofAEEq
    (coefficientCutoffTriadicCoeffFamily_negateCutoffSample_aeEq M L omega Q) p q,
    adjointFamily_coeffOn]

/-- **The `(J3)` transfer, uniformly in the loading.**

The negation symmetry does not care where the loading quantifier sits: given the
primal display on ONE probability-one event, simultaneously for every loading
direction, the transposed display holds on ONE probability-one event,
simultaneously for every loading direction, at the same constants.  The proof is
the `(J3)` carrier and gauge rewrites of this section, performed under the
`∀ v` binder.

This is the only conditional statement in this file, and its hypothesis has a
named producer: `hprimal` is exactly the conclusion of
`GoodEventAggregation.responseJ_injection_priced_ae_forall_loads` after its
`∃ C` and its regime premises are instantiated.  That module is not imported
here, so this file's import list stays at the single `LambdaGateChain`.

No further premise is added: the only binder beyond the hypothesis is
`hnL : Q.scale - hgap <= L`, which is the producer's own `n <= L`. -/
theorem responseJ_transpose_injection_priced_forall_loads_of_primal
    (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (hgap : ℕ) (L : ℤ)
    (hnL : Q.scale - (hgap : ℤ) ≤ L)
    (hprimal : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q (Q.scale - (hgap : ℤ)) →
        ∀ v : Vec d, vecNormSq v ≤ 2 →
          Ch02.responseJ (Ch02.cubeDomain (originCube d 0))
              (perturbCoeffOn (Ch02.cubeDomain (originCube d 0))
                (unitRescaledCutoffCoeff M Q (Q.scale - (hgap : ℤ)) omega)
                (incrementUnitCube₂ Q (Q.scale - (hgap : ℤ)) L
                  omega).toLInfSkewMatrixFieldOn 1)
              (Observable.inverseSqrtLoad
                (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
              (Observable.sqrtLoad
                (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) ≤
            3 * Ch02.responseJ (Ch02.cubeDomain Q)
                ((coefficientCutoffTriadicCoeffFamily M
                  (Q.scale - (hgap : ℤ)) omega).coeffOn Q)
                (Observable.inverseSqrtLoad
                  (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                (Observable.sqrtLoad
                  (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) +
              324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
                ((Disorder.cstar M)⁻¹ * M.gamma *
                  (3 : ℝ) ^ (4 * (Q.scale : ℝ) - 2 * M.gamma * (Q.scale : ℝ))) *
                underlineW2Gauge Q
                  (shellIncrement omega.1 (Q.scale - (hgap : ℤ)) L) ^ 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q (Q.scale - (hgap : ℤ)) →
        ∀ v : Vec d, vecNormSq v ≤ 2 →
          Ch02.responseJ (Ch02.cubeDomain Q)
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn Q).transpose
              (Observable.inverseSqrtLoad
                (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
              (Observable.sqrtLoad
                (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) ≤
            3 * Ch02.responseJ (Ch02.cubeDomain Q)
                ((coefficientCutoffTriadicCoeffFamily M
                  (Q.scale - (hgap : ℤ)) omega).coeffOn Q).transpose
                (Observable.inverseSqrtLoad
                  (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v)
                (Observable.sqrtLoad
                  (Annealed.sigmaBar M (Q.scale - (hgap : ℤ))) v) +
              324 * responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
                ((Disorder.cstar M)⁻¹ * M.gamma *
                  (3 : ℝ) ^ (4 * (Q.scale : ℝ) - 2 * M.gamma * (Q.scale : ℝ))) *
                underlineW2Gauge Q
                  (shellIncrement omega.1 (Q.scale - (hgap : ℤ)) L) ^ 2 := by
  filter_upwards [ae_comp_negateCutoffSample M hprimal,
    mem_goodLocalEvent_negateCutoffSample_ae M Ccg Q (Q.scale - (hgap : ℤ))]
    with omega hstep hgood homega v hv
  have hmain := hstep (hgood homega) v hv
  rw [responseJ_perturbCoeffOn_unitRescaledCutoffCoeff M Q hnL
      (negateCutoffSample omega),
    ← responseJ_cutoffFamily_eq_unitRescaledCutoffCoeff M L Q _ _
      (negateCutoffSample omega),
    responseJ_cutoffFamily_negateCutoffSample,
    responseJ_cutoffFamily_negateCutoffSample,
    underlineW2Gauge_shellIncrement_negateCutoffSample] at hmain
  exact hmain

end

end Algsuperdiff.Section3.Provider.Localization
