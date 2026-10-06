/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ResponseWeakEstimateBasics
public import LeanPool.HighContrastHomogenization.Provider.Response.ResponseCongruence

/-!
# High-contrast homogenization: Entry.Response.Kernel.OptimizerEnergyIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The optimizer-energy identity and the energy split on `{M > 1}`

For a response maximizer of a load `(p, q)`, the squared pathwise optimizer energy equals twice
the response value, `ℰ² = x · A(U) x - 2(p · q) = 2J`, and this file proves that identity - via
a first-variation (Euler-Lagrange) argument for `IsResponseMaximizer`, since no available
identity reaches the Dirichlet energy directly - together with its instances at the recentred
and adjoint coefficients. It also proves the resulting energy-split bound on the event `{M > 1}`
of the all-scale maximum, `p.response.transfer`.
-/

section
open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter blockScale blockSub coarseBlock
  matSqrt matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The energy split on `{M > 1}` (`p.response.transfer`) -/

/-! ### The energy identity, the depth-0 extraction, congruence and un-normalization

The statement is dealt with in four steps.

(i) ENERGY IDENTITY.  By definition
    `ℰ_t(a)² = volumeAverage U_t (x ↦ ∇v_a(x) ⬝ b_a(x) ∇v_a(x))`.
  For a response maximizer `u` of the load `(p, q)` for `b` on `U` the identity needed is
      `volumeAverage U (∇v ⬝ b ∇v) = x ⬝ (coarseBlockMatrix U b) x - 2 (p ⬝ q)`,  `x = (-p, q)`,
  i.e. `ℰ² = 2 J = x ⬝ A(U;b) x - 2 (p ⬝ q)` with `J = ResponseJ U p q b`.  What is available
  is
    * the MEAN identity `cellAverage_optimizerField_eq_blockResponseMean`
     : the cell average of `(∇v, b∇v)` is `x + 𝐑 A(U) x`; and
    * the RESPONSE-VALUE identity `ResponseJ U p q b = ½ x ⬝ A(U) x - p⬝q`, used inside that
  proof and exported as
      `Annealed.responseJ_eq_coarseBlock_adapted`.
  Neither says anything about the maximizer's Dirichlet ENERGY.  `CoarseGraining`'s
    `ResponseIdentities/AverageFormulas/CoarseFormulas.lean` is the only candidate and it is
    (a) only the `p = 0` case, (b) only under `IsSigmaStarCoarse`, and (c) only an inequality.
  The identity is therefore supplied below by a first-variation lemma (the Euler-Lagrange
  identity for `IsResponseMaximizer`), not by reassembling the identities above.

(ii) DEPTH-0 EXTRACTION.  The bound
    `A_t(a) ≤ (1 + M(a)) E_t` comes from `M(a) ≥ 3^{-ρ·0}·blockSpecBound(normalizedBlock (A_t(a))
  E_t - I)`, i.e. from `le_csSup` applied to the `n = 0`, `z = 0` member of the defining set of
    `respAllScaleMax` (`ResponseBlockObjects.lean`; `triadicIndexBox d 0 = {0}` and
    `adaptedCellAtCenter q (t-0) 0 = adaptedCell q t` are routine).  `le_csSup` needs `BddAbove`
    of that
  set.  Without it the `sSup` is the junk value `0` and the inequality is FALSE (take any `a`
  whose coarse blocks blow up along `n`: `M(a) = 0` while `A_t(a)` is not `≤ E_t`).  This is why
  the statement carries the qualification `∀ᵐ a ∂P`.  That `BddAbove` is derivable pathwise from
    `RawOutput` alone and with no new binder; it is proved below as `pathwise_envelope` and
  consumed by `coarseBlock_le_one_add_respAllScaleMax`.  The bound comes from
    `Source.bounded_source_envelope` (`HCPoly/Entry/Source/BoundedWindowFiniteness.lean`,
    sorry-free),
  whose only hypotheses are `IsStationaryLaw P` and `CoarseEllipticityDagger P γ E Ψ K Src` --
    `raw.stat` and `raw.ell`.  See the block below for the full argument.

(iii) CONGRUENCE.  `coarseBlockMatrix U_t (respCoeffMinus F a) = blockCongr (respG F) (coarseBlock
U_t a)`
  is `coarseBlockMatrix_sub_skew_eq_blockCongr`.  It consumes
    `HasQuadraticMu U_t (a.1 : CoeffField d)`, which `RawOutput` does not state: the congruence
    lemmas take it
  as the explicit hypothesis `hquad`.  That datum is a theorem on
  every adapted cell, `hasQuadraticMu_adaptedCell` below, whose only hypothesis
    `IsUnit (respGrid jStar F)` is itself discharged from `RawOutput` by
    `isUnit_respGrid_of_rawOutput` below, so no binder is added to the statement.

(iv) UN-NORMALIZATION.  `A_t(a) ≤ (1+M) E_t` gives, by congruence with `respG F`,
    `x ⬝ A^{b^-}_t(a) x ≤ (1+M) · x ⬝ Ehat_t^- x = (1+M) (L^-)²`
    (`le_smul_of_normalizedBlock_le_of_posDef`,
    `HCPoly/Entry/Response/Core/AnnealedMeanDrift.lean`, and `Analysis.matrix_congr_le`). -/

/-! ### The first-variation lemma and the sign of the `p·q` term

Step (i) is proved below and step (iii) is not a missing premise.

The identity is supplied by the first-variation lemma `responseJ_energy_of_isResponseMaximizer`
(`CoarseGraining/ResponseIdentities/Foundations/Ellipticity.lean`), proved there from
`basic_cg_identities_first_variation_of_isResponseMaximizer` (the Euler-Lagrange identity,
same file) and `volumeAverage_scalarResponseIntegrand_eq_firstVariation_self_add_half_energy`.
Its integrability premises are discharged by
`ResponseLinearIntegrabilityData.of_isEllipticFieldOn`
(`ResponseIdentities/Foundations/Maximizer.lean`).  This tree's `weakOptimizerEnergy`
is already the scalar energy `⨍ ∇v·b∇v`, and
`vecDot_matVecMul_symmPart` (`Ambient/CoefficientField.lean`) identifies it with
`scalarVariationEnergyIntegrand`.  The block form below is the identity
`responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain`.

SIGN RESOLUTION (the `−2p·q` vs `+2p·q` discrepancy in the block above).  Writing both sides with
this tree's actual definitions:
* `ResponseJ U p q b = ½ (−p,q)·A(U;b)(−p,q) − vecDot p q`
  (`Annealed.responseJ_eq_coarseBlock_adapted`, `HCPoly/Entry/Annealed/AdaptedDomainLocality.lean`);
* `weakOptimizerEnergy U b u ^ 2 = 2 · ResponseJ U p q b` (step (i), below).
Eliminating `ResponseJ` gives `ℰ² = x·A(U;b)x − 2 (p·q)`, `x = (−p,q)`: exactly the identity
displayed in the block above.  The block's own gloss
"`ℰ² = 2 J + 2 p⬝q` with `J = ResponseJ U p q b`" is internally inconsistent with its own display
two lines earlier (it would force `ℰ² = x·A x`); so is the docstring's
"`ℰ_t^2 = 2J_t = x^-·A^b_t(a)x^-`".  No sign was adjusted to make a proof close: the four
theorems below are proved from the identities as stated, and the `−2 (p·q)` is what comes out.
The residual `−2 (p·q)` is harmless for the statement, whose conclusion is an upper bound: on the
selected
loads `vecDot p q^∓ = 1` (`vecDot_respP_respqMinus_eq_one` and `vecDot_respP_respqPlus_eq_one`,
`HCPoly/Entry/Response/Core/ResponseCalibrationBundles.lean`, from `p·q = e·e = 1`
and the skewness of `g − h_t`), so the term is `−2 ≤ 0`.

STEP (iii) IS NOT A MISSING PREMISE.  The statement is not "under-hypothesised" by
`HasQuadraticMu U_t (a.1 : CoeffField d)`: that datum is a THEOREM on every adapted
cell, `hasQuadraticMu_adaptedCell` below (re-proved from the sorry-free
`hasQuadraticMu_adaptedCellTranslate`, `HCPoly/Entry/Response/Core/SourceLoadBound.lean`), and its
only hypothesis
`IsUnit (respGrid jStar F)` is itself discharged from `RawOutput` by
`isUnit_respGrid_of_rawOutput` below (`raw.hj`, `raw.symm`, `raw.pos`).  So no binder is added to
the statement.

STEP (ii).  `le_csSup` on the defining set of
`respAllScaleMax` (`ResponseBlockObjects.lean`) needs a.e. `BddAbove` of
`{3^{−ρn} · blockSpecBound (normalizedBlock (coarseBlock (adaptedCellAtCenter q (t−n) z) a) E_t −
I)}`
over all `n : ℕ` and `z ∈ triadicIndexBox d n`.  This is proved below. -/

/-! ### The pathwise envelope behind the a.e. `BddAbove`

Step (ii) is derivable with no new hypothesis.

WHERE THE BOUNDEDNESS COMES FROM.  Every cited declaration is sorry-free.

(1) `HCPoly/Entry/Source/BoundedWindowFiniteness.lean Source.bounded_source_envelope`.  For any
  BOUNDED region `W` it produces an auxiliary scale `J` and a measurable envelope `X ≥ 0` with
      `∀ᵐ a ∂P, ∀ q, InverseNormLE q 2 → ∀ j y, adaptedCellTranslate q j y ⊆ W →`
      ` coarseBlock (adaptedCellTranslate q j y) a ≤ (Cd · X a · 3^{γ·max(J−j,0)}) E`.
  Its ONLY hypotheses are `IsStationaryLaw P` and `CoarseEllipticityDagger P γ E Ψ K Src`,
  which `RawOutput` carries verbatim as `raw.stat` and `raw.ell` (`ResponseBlockObjects.lean`).
  It carries **no source threshold**, which is why this estimate is available here
  while the threshold estimate described below is not.
(2) The bounded region is `U_t` itself: `adaptedCell_isOpenBoundedConvexDomain`
   , and every cell of the family lies in it --
    `adaptedCellAtCenter_subset_adaptedCell`
  (`HCPoly/Entry/Response/Core/ScalarMaximizerExistence.lean`).  So the ellipticity constants are
  fixed BEFORE the
  scale index `n` is quantified.  `InverseNormLE (respGrid jStar F) 2` is
    `Geometry.inverseNormLE_roundedGrid` (`RoundedGridBasic.lean`) from `raw.hj` and
    `raw.symm`/`raw.pos`.
(3) The normalizer `E_t` is positive definite -- `Annealed.adaptedMean_posDef`
    (`HCPoly/Entry/Annealed/AdaptedCellFoundations.lean`) -- so `E ≤ κ E_t` for SOME `κ ≥ 0` by pure
  linear algebra (`exists_scale_le` below, `κ = ‖E_t^{-1/2} E E_t^{-1/2}‖`).  Only the
  EXISTENCE of `κ` is needed, never its size; that is what lets this argument avoid
    `Annealed.adaptedMean_refBlock_normalization`, whose source threshold the statement cannot
    discharge.
(4) The decay `3^{-ρn}` IS used: the envelope's own factor `3^{γ·max(J−j,0)}` GROWS in
  the depth `n = t − j`, and it is `ρ = (1+γ)/2 ≥ γ` (for `γ < 1`) that makes the weighted
  family bounded -- in fact bounded by its `n = 0` value.  See `pathwise_envelope`.

THE THRESHOLD ESTIMATE IS NOT USED.
`pathwise_bound_max` (`HCPoly/Entry/Response/Core/PathwiseFluctuationBound.lean`) feeds
`respAllScaleMax_le_of_forall` a hypothesis that IS a
`BddAbove` witness, and it is already elaborated.  But it consumes `hpath` from
`Source.source_multiplier_and_adapted_bound` and `hnormt` from
`Annealed.adaptedMean_refBlock_normalization`, BOTH of which require the source threshold
`⌈Csrc_i · logb 3 (2K)⌉ ≤ j_*` for constants `Csrc_i` they themselves produce.  The all-scale
maximum bound can supply it because it *produces* `Csrc`
The statement quantifies `Csrc`
universally, so `raw.hsrc` cannot be specialised and that estimate is unavailable here WITHOUT a
statement change.  The envelope estimate needs no threshold at all.

The helpers below are `private` in
`HCPoly/Entry/Response/Core/AnnealedMeanDrift.lean` and
`HCPoly/Entry/Response/Core/PathwiseFluctuationBound.lean`, and are re-proved here on
this tree's carriers.  Those modules are already in this
file's import closure (via `LoadMeanIdentity`), but their helpers are `private`, so importing would
not have helped; **no import was added**. -/

/-! ### step (i): the maximizer energy identity.

`ℰ² = 2 J = x·A(U;b)x − 2 (p·q)`, `x = (−p, q)`.  This is the first-variation lemma; the sign
of the `p·q` term is that of the block above. -/

/-- **Step (i)**, the maximizer energy identity in the form `ℰ² = 2 J`, for a pointwise elliptic
coefficient field.  The Euler-Lagrange identity is
`responseJ_energy_of_isResponseMaximizer` (`ResponseIdentities/Foundations/Ellipticity.lean`)
on this tree's set-level carriers; the passage from
`weakOptimizerEnergy`'s integrand `∇v·b∇v` to `scalarVariationEnergyIntegrand`'s `∇v·symm(b)∇v`
is `vecDot_matVecMul_symmPart`. -/
theorem weakOptimizerEnergy_sq_eq_two_responseJ {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ} {b : CoeffField d}
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U b) (p q : Vec d)
    (u : AHarmonicFunction b U) (hu : IsResponseMaximizer U p q b u) :
    weakOptimizerEnergy U b u ^ 2 = 2 * ResponseJ U p q b := by
  have hInt : ResponseLinearIntegrabilityData U b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hJ : ResponseJ U p q b =
      (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand b u) :=
    responseJ_energy_of_isResponseMaximizer U b p q u hu (hInt.weakFlux u)
      (hInt.response p q u) (hInt.firstVariation p q u u) (hInt.energy u)
  have hpt : (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      = scalarVariationEnergyIntegrand b u := by
    funext x
    simp [optimizerField, scalarVariationEnergyIntegrand, vecDot_matVecMul_symmPart]
  have hnn : 0 ≤ volumeAverage U (scalarVariationEnergyIntegrand b u) :=
    volumeAverage_nonneg_of_nonneg_on hU
      (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U b hEll u)
  rw [weakOptimizerEnergy, hpt, Real.sq_sqrt hnn, hJ]
  ring

/-- **Step (i)**, transported to the qualitative coefficient carrier: the identity holds for a
field `b` that is only a.e. equal to a pointwise elliptic representative, which is the only form
the carrier `CoeffSpace d` supports (same transport pattern as
`bddAbove_respWeakEnergySet`). -/
theorem weakOptimizerEnergy_sq_eq_two_responseJ_of_aeEq {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ} {b f : CoeffField d}
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn lam Lam U f)
    (hae : b =ᵐ[volumeMeasureOn U] f) (p q : Vec d)
    (u : AHarmonicFunction b U) (hu : IsResponseMaximizer U p q b u) :
    weakOptimizerEnergy U b u ^ 2 = 2 * ResponseJ U p q b := by
  have huT : IsResponseMaximizer U p q f (Response.aHarmonicOfAEEq hae u) := by
    intro z
    have key := hu (Response.aHarmonicOfAEEq hae.symm z)
    have h1 : volumeAverage U (scalarResponseIntegrand U f p q z) =
        volumeAverage U (scalarResponseIntegrand U b p q
          (Response.aHarmonicOfAEEq hae.symm z)) :=
      volumeAverage_scalarResponseIntegrand_congr hae.symm p q z _ (fun _ => rfl)
    have h2 : volumeAverage U (scalarResponseIntegrand U b p q u) =
        volumeAverage U (scalarResponseIntegrand U f p q
          (Response.aHarmonicOfAEEq hae u)) :=
      volumeAverage_scalarResponseIntegrand_congr hae p q u _ (fun _ => rfl)
    rw [h1, ← h2]
    exact key
  have hE : weakOptimizerEnergy U b u
      = weakOptimizerEnergy U f (Response.aHarmonicOfAEEq hae u) := by
    unfold weakOptimizerEnergy volumeAverage
    congr 2
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp [optimizerField, Response.aHarmonicOfAEEq, hx]
  rw [hE, weakOptimizerEnergy_sq_eq_two_responseJ hU hEll p q _ huT,
    responseJ_congr_of_ae_eq hae p q]

/-- **Step (i)**, in block form on an adapted cell: `ℰ² = x·A(U;b)x − 2 (p·q)`, `x = (−p, q)`.
This is the identity displayed above; note the sign of the `p·q` term. -/
theorem weakOptimizerEnergy_sq_eq_blockQuadratic_of_aeEq [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f) (p r : Vec d)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r b u) :
    weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2 =
      blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q t) b) (-p, r))
        - 2 * vecDot p r := by
  have hset : HighContrast.adaptedCell q t =
      translateSet 0 ((matVecMul q) '' (openCubeSet (originCube d t))) := by
    rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
    simp [HighContrast.adaptedCellTranslate]
  have hconv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) := by
    rw [hset]; exact isOpenBoundedConvexDomain_affine_openCube q hq t 0
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [hset]; exact volume_affine_openCube_toReal_pos q hq t 0
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  have hJ : ResponseJ (HighContrast.adaptedCell q t) p r b =
      (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q t) b) (-p, r))
        - vecDot p r := by
    rw [responseJ_congr_of_ae_eq hae p r, coarseBlockMatrix_congr_of_ae_eq hae]
    exact responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hconv hEll hvol p r
  rw [weakOptimizerEnergy_sq_eq_two_responseJ_of_aeEq hconv.isOpen.measurableSet hEll hae p r u hu,
    hJ]
  ring

/-- **Step (i)** for the recentred sample `a_- = a − g` (`p.response.transfer`), on the carrier. -/
theorem weakOptimizerEnergy_sq_eq_blockQuadratic_respCoeffMinus [NeZero d] (q : Mat d)
    (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    weakOptimizerEnergy (HighContrast.adaptedCell q t) (respCoeffMinus F a) u ^ 2 =
      blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r))
        - 2 * vecDot p r := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae0⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine weakOptimizerEnergy_sq_eq_blockQuadratic_of_aeEq q hq t
    (isEllipticFieldOn_sub_skew hEll (respg F) (respg_isSkew F)) ?_ p r u hu
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae0] with x hx
  simp [respCoeffMinus, hx]

/-- **Step (i)** for the adjoint sample `a_+ = a^t + g` (`p.response.transfer`), on the carrier. -/
theorem weakOptimizerEnergy_sq_eq_blockQuadratic_respCoeffPlus [NeZero d] (q : Mat d)
    (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    weakOptimizerEnergy (HighContrast.adaptedCell q t) (respCoeffPlus F a) u ^ 2 =
      blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r))
        - 2 * vecDot p r := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae0⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine weakOptimizerEnergy_sq_eq_blockQuadratic_of_aeEq q hq t
    (isEllipticFieldOn_transpose_add_skew hEll (respg F) (respg_isSkew F)) ?_ p r u hu
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae0] with x hx
  simp [respCoeffPlus, hx]

/-! ### step (iii): the congruence hypotheses

Neither datum becomes a binder of the statement: both are theorems, provable from `RawOutput`
alone. -/

/-- **Step (iii.a)**.  `IsUnit (respGrid jStar F)` is a consequence of `RawOutput`: `raw.hj` is
`2d ≤ 3^jStar` and `raw.symm`/`raw.pos` give `(explicitCanonicalMetric F).PosDef`. -/
theorem isUnit_respGrid_of_rawOutput [NeZero d] {γ : ℝ} {S : SelectionData}
    {ε σ Cglob Cprof Csrc Bresp : ℝ} {H : ℕ} {P : Measure (CoeffSpace d)} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {Kg : ℝ} {Src : CoeffSpace d → ℝ} {B : ℝ} {jStar : ℕ} {F : BlockMat d}
    {s t : ℤ}
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t) :
    IsUnit (respGrid jStar F) :=
  Geometry.isUnit_roundedGrid raw.hj (Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos)

/-- **Step (iii.b)**.  `HasQuadraticMu` holds on every adapted cell for the qualitative
coefficient carrier, so it is not a missing premise of the statement.  This specializes the
sorry-free
`private` `hasQuadraticMu_adaptedCellTranslate`
 to `y = 0`. -/
theorem hasQuadraticMu_adaptedCell [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ)
    (a : CoeffSpace d) :
    HasQuadraticMu (HighContrast.adaptedCell q j) (⇑a.1 : CoeffField d) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hConv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q j) :=
    adaptedCell_isOpenBoundedConvexDomain q hq j
  let : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q j)) :=
    hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (HighContrast.adaptedCell q j)).toReal :=
    ENNReal.toReal_pos (hConv.isOpen.measure_ne_zero volume (Recurrence.adaptedCell_nonempty q j))
      hConv.volume_lt_top.ne
  obtain ⟨R, ⟨compat⟩⟩ :=
    exists_recovery_compatibility_of_isOpenBoundedConvexDomain hConv hEll hvol
  obtain ⟨Q, hQ⟩ := R.hasQuadraticMuOfIsEllipticFieldOn hEll hvol compat
  exact ⟨Q, fun Pv => by rw [Mu_congr_of_ae_eq (ae_restrict_of_ae hae) Pv]; exact hQ Pv⟩

/-! Block A: the Loewner / `blockSpecBound` layer. -/

private theorem toFullBlockMat_blockIdentity :
    toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, Matrix.one_apply]

private theorem blockScale_mono (A R : BlockMat d) (c k : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE A (blockScale k R)) :
    BlockMatLoewnerLE (blockScale c A) (blockScale (c * k) R) := by
  intro X
  have hX := h X
  rw [qform_blockScale_smul] at hX
  rw [qform_blockScale_smul, qform_blockScale_smul, mul_assoc]
  nlinarith only [hX, hc]

theorem dotProduct_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) :
    (0 : ℝ) ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem toFullBlockMat_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext (i | i) (j | j) <;> rfl

/-- The quadratic form of `blockIdentity`. -/
theorem qform_identity (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X) =
      toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_blockIdentity, Matrix.one_mulVec]

private theorem blockSpecBound_attained (N : BlockMat d) (c : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    BlockMatLoewnerLE N (blockScale (blockSpecBound N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have hid := qform_identity X
  set q : ℝ := toFullBlockVec X ⬝ᵥ toFullBlockVec X with hqdef
  have hq0 : (0 : ℝ) ≤ q := dotProduct_self_nonneg _
  set p : ℝ := blockVecDot X (blockMatVecMul N X) with hpdef
  have hmem : ∀ b ∈ {c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}, p ≤ b * q := by
    intro b hb
    have hbX := hb.2 X
    rw [qform_blockScale_smul, hid] at hbX
    linarith only [hbX, hpdef, hqdef]
  have hne : ({c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}).Nonempty := ⟨c, hc, h⟩
  have hkey : p ≤ blockSpecBound N * q := by
    rcases eq_or_lt_of_le hq0 with h0 | hpos
    · have hc0 := hmem c ⟨hc, h⟩
      rw [← h0] at hc0 ⊢
      simpa using hc0
    · have hdiv : p / q ≤ blockSpecBound N := by
        refine le_csInf hne fun b hb => ?_
        exact (div_le_iff₀ hpos).2 (hmem b hb)
      exact (div_le_iff₀ hpos).1 hdiv
  rw [qform_blockScale_smul, hid]
  linarith only [hkey, hpdef, hqdef]

private theorem specBound_sub_identity_le (A : BlockMat d) (c : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE A (blockScale c (Book.Ch02.blockIdentity d))) :
    blockSpecBound (blockSub A (Book.Ch02.blockIdentity d)) ≤ c := by
  refine blockSpecBound_le_of_loewner _ _ hc ?_
  intro X
  have hfull : toFullBlockMat A =
      toFullBlockMat (blockSub A (Book.Ch02.blockIdentity d)) +
        toFullBlockMat (Book.Ch02.blockIdentity d) := by
    rw [toFullBlockMat_blockSub, sub_add_cancel]
  have hsplit := qform_add_of_full A (blockSub A (Book.Ch02.blockIdentity d))
    (Book.Ch02.blockIdentity d) hfull X
  have hid := qform_identity X
  have hq0 : (0 : ℝ) ≤ toFullBlockVec X ⬝ᵥ toFullBlockVec X := dotProduct_self_nonneg _
  have hA := h X
  rw [qform_blockScale_smul, hid] at hA
  rw [qform_blockScale_smul, hid]
  rw [hid] at hsplit
  linarith only [hA, hsplit, hq0]

/-- The converse of `specBound_sub_identity_le`: from a spectral bound on `A - I` back to
`A ≤ (1 + c) I`, given any witness making the defining infimum attained. -/
theorem le_one_add_specBound (A : BlockMat d) (c M : ℝ) (hc : 0 ≤ c)
    (hwit : BlockMatLoewnerLE (blockSub A (Book.Ch02.blockIdentity d))
      (blockScale c (Book.Ch02.blockIdentity d)))
    (hM : blockSpecBound (blockSub A (Book.Ch02.blockIdentity d)) ≤ M) :
    BlockMatLoewnerLE A (blockScale (1 + M) (Book.Ch02.blockIdentity d)) := by
  have hatt := blockSpecBound_attained _ c hc hwit
  intro X
  have hid := qform_identity X
  have hq0 : (0 : ℝ) ≤ toFullBlockVec X ⬝ᵥ toFullBlockVec X := dotProduct_self_nonneg _
  have hfull : toFullBlockMat A =
      toFullBlockMat (blockSub A (Book.Ch02.blockIdentity d)) +
        toFullBlockMat (Book.Ch02.blockIdentity d) := by
    rw [toFullBlockMat_blockSub, sub_add_cancel]
  have hsplit := qform_add_of_full A (blockSub A (Book.Ch02.blockIdentity d))
    (Book.Ch02.blockIdentity d) hfull X
  have hA := hatt X
  rw [qform_blockScale_smul, hid] at hA
  rw [qform_blockScale_smul, hid]
  rw [hid] at hsplit
  have hsq : blockSpecBound (blockSub A (Book.Ch02.blockIdentity d)) *
      (toFullBlockVec X ⬝ᵥ toFullBlockVec X) ≤
      M * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) :=
    mul_le_mul_of_nonneg_right hM hq0
  linarith only [hA, hsplit, hsq]

/-! Block B: un-normalization, the converse of `normalizedBlock_le_scale`
(`HCPoly/Entry/Response/Core/PathwiseFluctuationBound.lean`, public).  The matrix algebra follows
the `private`
`le_smul_of_normalizedBlock_le_of_posDef` (`HCPoly/Entry/Response/Core/AnnealedMeanDrift.lean`),
rewritten in the
`BlockMatLoewnerLE` language so that no `Matrix`-order bridge is needed. -/

private theorem qform_conj {n : Type*} [Fintype n] [DecidableEq n]
    (Sm M : Matrix n n ℝ) (hS : Smᵀ = Sm) (v : n → ℝ) :
    v ⬝ᵥ ((Sm * M * Sm) *ᵥ v) = (Sm *ᵥ v) ⬝ᵥ (M *ᵥ (Sm *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hS]

/-- **Undoing the normalization in block language**: `R^{-1/2} A R^{-1/2} ≤ c I` gives
`A ≤ c R`. -/
theorem le_scale_of_normalizedBlock_le {A R : BlockMat d} {c : ℝ}
    (hR : (toFullBlockMat R).PosDef)
    (h : BlockMatLoewnerLE (normalizedBlock A R) (blockScale c (Book.Ch02.blockIdentity d))) :
    BlockMatLoewnerLE A (blockScale c R) := by
  set Rf := toFullBlockMat R with hRf
  set S := matSqrt Rf⁻¹ with hSdef
  have hSpd : S.PosDef := matSqrt_inv_posDef_full hR
  have hSt : Sᵀ = S := transpose_eq_of_psd hSpd.posSemidef
  have hSS : S * S = Rf⁻¹ := (matSqrt_spec hR.inv.posSemidef).2
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).mp hSpd.isUnit
  have hRu : IsUnit Rf.det := (Matrix.isUnit_iff_isUnit_det Rf).mp hR.isUnit
  have hiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hSu
  have hii : S⁻¹ * S⁻¹ = Rf := by
    rw [← Matrix.mul_inv_rev, hSS, Matrix.nonsing_inv_nonsing_inv Rf hRu]
  have hSit : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSt]
  have key : ∀ (M : BlockMat d) (Y : BlockVec d), blockVecDot Y (blockMatVecMul M Y) =
      toFullBlockVec Y ⬝ᵥ (toFullBlockMat M *ᵥ toFullBlockVec Y) := by
    intro M Y
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hN : toFullBlockMat (normalizedBlock A R) = S * toFullBlockMat A * S := by
    simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hRf, hSdef]
  intro X
  have hY := h (ofFullBlockVec (S⁻¹ *ᵥ toFullBlockVec X))
  rw [key, key] at hY
  simp only [toFullBlockVec_ofFullBlockVec, toFullBlockMat_blockScale, hN,
    toFullBlockMat_blockIdentity] at hY
  -- left-hand side collapses to the quadratic form of `A`
  have hL : (S⁻¹ *ᵥ toFullBlockVec X) ⬝ᵥ
      ((S * toFullBlockMat A * S) *ᵥ (S⁻¹ *ᵥ toFullBlockVec X))
      = toFullBlockVec X ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec X) := by
    have hm : S⁻¹ * (S * toFullBlockMat A * S) * S⁻¹ = toFullBlockMat A := by
      calc S⁻¹ * (S * toFullBlockMat A * S) * S⁻¹
          = (S⁻¹ * S) * toFullBlockMat A * (S * S⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = toFullBlockMat A := by rw [hiS, hSi, Matrix.one_mul, Matrix.mul_one]
    rw [← qform_conj (S⁻¹) (S * toFullBlockMat A * S) hSit, hm]
  -- right-hand side collapses to the quadratic form of `R`
  have hRq : (S⁻¹ *ᵥ toFullBlockVec X) ⬝ᵥ
      ((c • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)) *ᵥ (S⁻¹ *ᵥ toFullBlockVec X))
      = toFullBlockVec X ⬝ᵥ ((c • Rf) *ᵥ toFullBlockVec X) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Matrix.one_mulVec]
    congr 1
    have hq := qform_conj (S⁻¹) (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ) hSit
      (toFullBlockVec X)
    rw [Matrix.mul_one, Matrix.one_mulVec] at hq
    rw [← hii]
    exact hq.symm
  rw [hL, hRq] at hY
  rw [key, key, toFullBlockMat_blockScale, ← hRf]
  exact hY

/-! Block C: **the soft comparison of two fixed blocks**.  This is what replaces the
quantitative `Annealed.adaptedMean_refBlock_normalization`, whose threshold hypothesis the statement
cannot discharge.  Only *existence* of a
constant is needed for `BddAbove`, and existence is pure linear algebra. -/

private theorem dot_mulVec_le_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (v : n → ℝ) : v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ * (v ⬝ᵥ v) := by
  have hsq := vecSq_mulVec_le N v
  have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := dotProduct_self_nonneg v
  rcases eq_or_lt_of_le (norm_nonneg N) with h0 | hpos
  · have hN : N = 0 := norm_eq_zero.mp h0.symm
    subst hN
    simp
  · have hexp : (0 : ℝ) ≤ (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) :=
      dotProduct_self_nonneg _
    have hexpand : (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) =
        ‖N‖ * ‖N‖ * (v ⬝ᵥ v) - 2 * ‖N‖ * (v ⬝ᵥ (N *ᵥ v)) + (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (N *ᵥ v) v]
      ring
    rw [hexpand] at hexp
    nlinarith only [hexp, hsq, hpos]

private theorem loewner_le_blockOpNorm (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockOpNorm N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := dot_mulVec_le_opNorm (toFullBlockMat N) (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hR : blockVecDot X (blockMatVecMul (blockScale (blockOpNorm N)
      (Book.Ch02.blockIdentity d)) X) =
      blockOpNorm N * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, toFullBlockMat_blockScale,
      toFullBlockMat_blockIdentity]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [hL, hR]
  unfold blockOpNorm at h ⊢
  linarith only [h]

/-- **Every fixed block is Loewner-dominated by a multiple of any fixed positive definite
block.**  `κ = ‖R^{-1/2} A R^{-1/2}‖` works; no quantitative control of `κ` is claimed, and
none is needed for `BddAbove`. -/
private theorem exists_scale_le {A R : BlockMat d} (hR : (toFullBlockMat R).PosDef) :
    ∃ κ : ℝ, 0 ≤ κ ∧ BlockMatLoewnerLE A (blockScale κ R) :=
  ⟨blockOpNorm (normalizedBlock A R), norm_nonneg _,
    le_scale_of_normalizedBlock_le hR (loewner_le_blockOpNorm _)⟩

/-! Block D: **the envelope estimate** -- the pathwise, a.e. bound on every weighted term of the
defining set of `respAllScaleMax` (`ResponseBlockObjects.lean`), hence its `BddAbove`.

The producer is `Source.bounded_source_envelope`
(`HCPoly/Entry/Source/BoundedWindowFiniteness.lean`, sorry-free), whose ONLY hypotheses are
`IsStationaryLaw P` and `CoarseEllipticityDagger P γ E Ψ K Src` -- both carried by `RawOutput`
as `raw.stat` and `raw.ell`.  It carries **no source threshold**, which is what lets this estimate
avoid the threshold required by the estimate discussed above. -/

-- of the private `HCPoly/Entry/Response/Core/AnnealedMeanDrift.lean`
-- `adaptedCellAtCenter_zero_eq_adaptedCell`)
theorem adaptedCellAtCenter_zero (q : Mat d) (j : ℤ) :
    adaptedCellAtCenter q j 0 = HighContrast.adaptedCell q j := by
  have hc : adaptedCellCenter q j (0 : Fin d → ℤ) = 0 := by
    have h0 : (fun i => (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = (0 : Vec d) := by
      funext i; simp
    rw [adaptedCellCenter, h0]
    show (3 : ℝ) ^ j • Matrix.mulVec q (0 : Vec d) = 0
    simp
  rw [adaptedCellAtCenter, hc]
  ext x
  simp [HighContrast.adaptedCellTranslate, HighContrast.adaptedCell]

/-- `0 ∈ triadicIndexBox d n` for every depth. -/
theorem zero_mem_triadicIndexBox (n : ℕ) :
    (0 : Fin d → ℤ) ∈ triadicIndexBox d n := by
  rw [mem_triadicIndexBox_iff]
  intro i
  simpa using Int.natCast_nonneg (((3 ^ n - 1) / 2 : ℕ))

/-- **The pathwise all-scale envelope.**  For `P`-a.e. sample `a` there is
one constant `C(a)` that simultaneously (1) Loewner-dominates the depth-`0` coarse block by
`C · E_t` and (2) bounds every weighted term of the defining set of `respAllScaleMax`.

The decay `3^{-ρ n}` IS used: the window envelope's own factor `3^{γ·max(J-j,0)}` grows in the
depth `n = t - j`, and it is `ρ = (1+γ)/2 ≥ γ` (for `γ < 1`) that makes the product summable --
in fact bounded by its `n = 0` value. -/
theorem pathwise_envelope (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∃ C : ℝ, 0 ≤ C ∧
      BlockMatLoewnerLE (coarseBlock (respCell jStar F t) a)
        (blockScale C (respMean P jStar F t)) ∧
      ∀ (n : ℕ), ∀ z ∈ triadicIndexBox d n,
        (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
          blockSpecBound (blockSub (normalizedBlock (coarseBlock
            (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a) (respMean P jStar F t))
            (Book.Ch02.blockIdentity d)) ≤ C := by
  have hγ := hdag.g_mem
  classical
  let : NeZero d := ⟨by omega⟩
  -- the fixed bounded window: the generation-`t` adapted cell itself
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hqinv : Geometry.InverseNormLE (respGrid jStar F) 2 :=
    Geometry.inverseNormLE_roundedGrid hj hm
  obtain ⟨R, hR0, hRb⟩ :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isBoundedDomain
  have hWb : Bornology.IsBounded (respCell jStar F t) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨R, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hR0.le).mpr fun i => by
      simpa [Real.norm_eq_abs] using hRb x hx i
  obtain ⟨J, X, _hXm, hX0, _hXmom, henv⟩ :=
    Source.bounded_source_envelope P γ E Ψ Kg Src hstat hdag (respCell jStar F t) hWb
  -- the deterministic constants
  set Cd : ℝ := 12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ))) with hCd
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 - γ)) := by
    have h1 : (3 : ℝ) ^ (-(1 - γ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ.2])
    linarith only [h1]
  have hCd0 : (0 : ℝ) ≤ Cd := by rw [hCd]; positivity
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric
      F) hm t
  obtain ⟨κ, hκ0, hκ⟩ :=
    exists_scale_le (A := E) (R := respMean P jStar F t) hEt
  filter_upwards [henv] with a ha
  set C : ℝ := Cd * X a * (3 : ℝ) ^ (γ * max ((J : ℝ) - (t : ℝ)) 0) * κ with hC
  have hC0 : (0 : ℝ) ≤ C := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hCd0 (hX0 a)) ?_) hκ0
    exact Real.rpow_nonneg (by norm_num) _
  -- the uniform Loewner bound on every cell of the family, against `E_t`
  have hgen : ∀ (n : ℕ), ∀ z ∈ triadicIndexBox d n,
      BlockMatLoewnerLE
        (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
        (blockScale (Cd * X a *
          (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) * κ)
          (respMean P jStar F t)) := by
    intro n z hz
    have hsub : HighContrast.adaptedCellTranslate (respGrid jStar F) (t - (n : ℤ))
        (adaptedCellCenter (respGrid jStar F) (t - (n : ℤ)) z) ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hz
    have hb := ha (respGrid jStar F) hqinv (t - (n : ℤ))
      (adaptedCellCenter (respGrid jStar F) (t - (n : ℤ)) z) hsub
    -- `E ≤ κ E_t` dilates the envelope's reference block into `E_t`
    have hdil : BlockMatLoewnerLE
        (blockScale (Cd * X a *
          (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0)) E)
        (blockScale (Cd * X a *
          (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) * κ)
          (respMean P jStar F t)) :=
      blockScale_mono E (respMean P jStar F t) _ κ
        (mul_nonneg (mul_nonneg hCd0 (hX0 a)) (Real.rpow_nonneg (by norm_num) _)) hκ
    exact hb.trans hdil
  refine ⟨C, hC0, ?_, ?_⟩
  · -- (1) the depth-`0` Loewner bound is the `n = 0`, `z = 0` member
    have h0 := hgen 0 0 (zero_mem_triadicIndexBox 0)
    rw [Nat.cast_zero, sub_zero, adaptedCellAtCenter_zero] at h0
    simpa only [hC, respCell, Nat.cast_zero, sub_zero] using h0
  · -- (2) every weighted term
    intro n z hz
    have hb := hgen n z hz
    have hc1 : (0 : ℝ) ≤ Cd * X a *
        (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) * κ := by
      refine mul_nonneg (mul_nonneg (mul_nonneg hCd0 (hX0 a)) ?_) hκ0
      exact Real.rpow_nonneg (by norm_num) _
    have hspec : blockSpecBound (blockSub (normalizedBlock (coarseBlock
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a) (respMean P jStar F t))
        (Book.Ch02.blockIdentity d)) ≤
        Cd * X a * (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) * κ :=
      specBound_sub_identity_le _ _ hc1
        (normalizedBlock_le_scale _ _ hEt _ hb)
    have hwnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    refine le_trans (mul_le_mul_of_nonneg_left hspec hwnn) ?_
    -- the exponent arithmetic: `ρ ≥ γ` for `γ < 1` absorbs the window growth
    have hcast : ((t - (n : ℤ) : ℤ) : ℝ) = (t : ℝ) - (n : ℝ) := by push_cast; ring
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmax : max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0 ≤
        max ((J : ℝ) - (t : ℝ)) 0 + (n : ℝ) := by
      rw [hcast]
      rcases le_or_gt ((J : ℝ) - ((t : ℝ) - (n : ℝ))) 0 with h | h
      · rw [max_eq_right h]
        have := le_max_right ((J : ℝ) - (t : ℝ)) 0
        linarith only [this, hn0]
      · rw [max_eq_left h.le]
        have := le_max_left ((J : ℝ) - (t : ℝ)) 0
        linarith only [this, hn0]
    have hexp : -(Quenched.contrastRho γ * (n : ℝ)) +
        γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0 ≤ γ * max ((J : ℝ) - (t : ℝ)) 0 := by
      have hρ : γ ≤ Quenched.contrastRho γ := by
        rw [Quenched.contrastRho]; linarith only [hγ.2]
      have h1 : γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0 ≤
          γ * (max ((J : ℝ) - (t : ℝ)) 0 + (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hmax hγ.1
      have h2 : -(Quenched.contrastRho γ * (n : ℝ)) +
          γ * (max ((J : ℝ) - (t : ℝ)) 0 + (n : ℝ)) ≤
          γ * max ((J : ℝ) - (t : ℝ)) 0 := by
        have h3 : (0 : ℝ) ≤ (Quenched.contrastRho γ - γ) * (n : ℝ) :=
          mul_nonneg (by linarith only [hρ]) hn0
        linarith only [h3]
      linarith only [h1, h2]
    have hpow : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) ≤
        (3 : ℝ) ^ (γ * max ((J : ℝ) - (t : ℝ)) 0) := by
      rw [← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hBase : (0 : ℝ) ≤ Cd * X a * κ := mul_nonneg (mul_nonneg hCd0 (hX0 a)) hκ0
    rw [hC]
    have hstep : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        (Cd * X a * (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) * κ) ≤
        Cd * X a * (3 : ℝ) ^ (γ * max ((J : ℝ) - (t : ℝ)) 0) * κ := by
      calc (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
            (Cd * X a *
              (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) * κ)
          = (Cd * X a * κ) *
              ((3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
                (3 : ℝ) ^ (γ * max ((J : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0)) := by
            ring
        _ ≤ (Cd * X a * κ) * (3 : ℝ) ^ (γ * max ((J : ℝ) - (t : ℝ)) 0) :=
            mul_le_mul_of_nonneg_left hpow hBase
        _ = Cd * X a * (3 : ℝ) ^ (γ * max ((J : ℝ) - (t : ℝ)) 0) * κ := by
            ring
    exact hstep

end

end HCPolySupport.HighContrast.Multiscale
end
