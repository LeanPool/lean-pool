/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCell
public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCellTransport
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ScalarMaximizerExistence
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalReadoutMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseCutoffExistence
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Setup.AdaptedGridCells
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# High-contrast homogenization: Entry.Response.Cutoff.ResponseTransferFromCutoffBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Response-Transfer Estimate and Its Companion Facts

This file transports the reference-cube cutoff bound to the adapted cell through the change of
variables `x = q y`, giving the response-transfer estimate `p.response.transfer` of AK.HC Lemma
A.1, (3.45)-(3.54) together with the integrability premises it needs on the squared scale-average
seminorm, the pathwise response and the cutoff pairing. It records the Lipschitz oscillation
bound a response cutoff inherits from its pullback derivative scale across a descendant cell, the
nonnegativity of the pathwise and annealed response energies for both recentred coefficients, the
subcell means of the cutoff fluctuation used as the weights of the cutoff-mean row, and the
elliptic-representative bridge carrying the optimizer, the response and its volume averages
across an almost-everywhere equal, pointwise elliptic representative of a coefficient of the
carrier.
-/

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! **GAP 1 of the integrability premise: PROVED, and the generic form REFUTED.**

The bound needed here is the squared scale-average seminorm bound for the doubled optimizer
state.  It holds, for the two recentred response coefficients, by chaining the linearity of the
cell average, the Jensen/partition bound and the square integrability of the
doubled state on the cell.

It is NOT available for an arbitrary coefficient family `c : CoeffSpace d → CoeffField d`, and
the generic statement is false: if the flux slot `c a ⋅ ∇v` fails to be square integrable on the
cell, the right-hand side is the Bochner junk value `0`
(`cellMeanSq_eq_zero_of_not_integrable`) while the left-hand side, whose gradient slot is an
honest average of an `L²` field, need not vanish; the resulting collapse is
`eq_zero_of_sq_le_cellMeanSq_of_not_integrable`.  The proof below therefore splits on the
hypothesis that the coefficient family is one of the two recentrings. -/

/-! **The `L¹(P)` envelope of the weak quantity: PROVED, and the `cellMeanSq` route ABANDONED.**

The bound needed here -- `P`-integrability of the pathwise `M_0`-energy
`cellMeanSq U_t (M_0^{1/2}(X_t - Y))` of the doubled optimizer state -- is NOT available, and not
for want of a proof: the `M_0`-energy of the state is the `L²(U_t)` norm of the GRADIENT and of the
FLUX separately, and in the high-contrast class those are not controlled by the coarse block.  A
one-dimensional sample with conductivity `δ` on a set of measure `δ` has `⟨a⁻¹⟩ = 2` -- so its
coarse block, and every moment of it, is bounded uniformly in `δ` -- while the gradient energy of
its response maximizer is of order `δ⁻¹`; a law with a heavy tail in `δ⁻¹` therefore satisfies
`e.coarse.ellipticity` with a non-integrable `M_0`-energy.

The scale-average seminorm, however, never sees the pointwise state: it sees only the cell averages
of the state over the triadic subcells, and those ARE controlled, by the Fenchel inequality dual to
AK.HC (2.15) on each subcell together with the all-scale coarse-block bound of
`p.response.transfer`.  That is the route taken below: it dominates the seminorm square
by `C ((1 + ℳ) J + 1)` with `ℳ` the all-scale maximum and `J` the pathwise response, both of which
the standing assumptions make square integrable.  The private helper is therefore gone, and with it
the `cellMeanSq` detour; see `WeakIntegrandDomination.lean` and the modules it names. -/

/-! **The measurability of the weak-quantity integrand: PROVED.**

A response maximizer is unique up to a null set in its gradient, so the cell averages entering the
scale-average seminorm are those of the canonical Chapter-2 maximizer, which depends measurably on
the sample; and the seminorm is a sum of measurable terms.  This is
`aestronglyMeasurable_besovSeminorm_sq_of_maximizer` (`DualityBoundHypotheses.lean`), which
consumes the maximizer hypothesis and the identification of the coefficient family — both of which
the caller below already carries, and neither of which the deleted generic form had.  For an
arbitrary family of `AHarmonicFunction`s, with no maximizer hypothesis, measurability is not
available and the generic statement is false. -/

/-- **The integrability premise of `e.response.weak.estimate`, PROVED.**

`respWeakEnergy` is the supremum of the numbers `3^{-t} E[[M_0^{1/2}(X_t - Y)]^2]`, and Bochner
integration returns `0` on a non-integrable integrand, so the cutoff estimate is only informative
once the squared scale-average seminorm of the doubled optimizer state is `P`-integrable.  That is
what this theorem supplies, from the standing assumptions on the law alone.

The two measurability premises are the all-scale maximum `ℳ` of `p.response.transfer`
in `L^Q(P)`; they are produced once and for all by
`respAllScaleMax_aestronglyMeasurable_integrable` and discharged at the sole call site.  The
dimension premise `2 ≤ d` is the one the coarse-ellipticity source chain carries; it too is
discharged at the call site, which already assumes it.

The proof is the almost sure envelope of `WeakIntegrandDomination.lean` -- the subcell Fenchel
inequality dual to AK.HC (2.15), the all-scale coarse-block bound, exact partition averaging and
the geometric summation of the scale-average seminorm -- integrated against the law by
`WeakIntegrandDomination.lean`; the majorant `(1 + ℳ) J + 1` is integrable by Cauchy-Schwarz,
since `ℳ` has all moments up to `Q` and the recentred pathwise response is square integrable. -/
theorem integrable_besovSeminorm_sq_respCell (d : ℕ) [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (c : CoeffSpace d → CoeffField d)
    (_hc : c = respCoeffMinus F ∨ c = respCoeffPlus F) (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (_hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  have := _raw.prob
  -- The selected grid is invertible (`RawOutput.hj/symm/pos`).
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    _raw.symm _raw.pos
  rcases _hc with rfl | rfl
  · exact integrable_besovSeminorm_sq_of_raw_minus hd γ _raw.ell.g_mem P E Ψ Kg Src _raw.stat
      _raw.ell jStar _raw.hj F hm t p q' Y hMint hMmeas
      (integrable_respJ_sq_respCoeffMinus_of_dagger P γ E Ψ Kg Src _raw.stat _raw.ell jStar
        _raw.hj F hm t p q') u _hu
  · exact integrable_besovSeminorm_sq_of_raw_plus hd γ _raw.ell.g_mem P E Ψ Kg Src _raw.stat
      _raw.ell jStar _raw.hj F hm t p q' Y hMint hMmeas
      (integrable_respJ_sq_respCoeffPlus_of_dagger P γ E Ψ Kg Src _raw.stat _raw.ell jStar
        _raw.hj F hm t p q') u _hu

/-! ### The metric dichotomy that makes the pullback estimates applicable under the hypotheses of
`p.response.transfer`.

The pullback estimates all carry `hm : m.PosDef` for `m = explicitCanonicalMetric F`, while the
response-transfer estimate quantifies over a
BARE `F : BlockMat d` (the `PosDef` fact is `Geometry.explicitCanonicalMetric_posDef`, which
consumes
`raw.symm`/`raw.pos` of `RawOutput`, available to the CALLER `ResponseCutoffEstimate.lean` but not
inside that estimate).  This is NOT a hypothesis deficiency: the missing case
is empty on the left-hand side.  Indeed `explicitCanonicalMetric F` is `X⁻¹` for
`X = (ofFullBlockMat (matSqrt · * matSqrt · * matSqrt ·)).lowerRight`, and `matSqrt` is
positive semidefinite on EVERY input (on non-`PosSemidef` data it
takes its junk value `1`), so `X` is positive semidefinite and `explicitCanonicalMetric F` is either
positive definite (when `X` is invertible) or singular.  In the singular case
`(explicitCanonicalMetric F)⁻¹ = 0`, so the selected grid `respGrid jStar F = explicitRoundedGrid
jStar
(explicitCanonicalMetric F)` -- whose every entry carries the factor `sqrt ‖m⁻¹‖` -- is the ZERO
matrix,
its determinant vanishes, the adapted cell is
Lebesgue-null and the left-hand side of the response-transfer estimate is `0`.

Positive semidefiniteness of `explicitCanonicalMetric F` itself, i.e. preservation of `PosSemidef`
by
`A * B * A`, by the lower-right principal block and by `Matrix.inv`, is NOT
formalized here. -/

/-! ### The change of variables `x = q y` of `p.response.transfer`.

`cutoffPairingOnCellAux` lives on the adapted cell `U_t = q ⋄_t`; the reference-cube product-term
bound and the two pullback seminorm bounds live on the reference cube `originCube d t`.  The bridge
is the pullback `x = q y`, which is exact on volume
averages (`cubeAverage_comp_matVecMul`, `ScaleAverageSeminorm.lean`) and which distributes the
grid between the two slots of the pairing through the adjoint identity `⟨qᵀ v, q⁻¹ w⟩ = ⟨v, w⟩`:
the two pulled-back slots are then LITERALLY the fields `fun y => qᵀ (X (q y)).1` and
`fun y => q⁻¹ (X (q y)).2` whose partial Besov seminorms are bounded by the pullback lemmas
(`partialSeminorm_pullback_fst_le` / `partialSeminorm_pullback_snd_le`, with `X` the centred
field `fun x => optimizerField b u x - Y`).  No estimate is used here; this step is an identity. -/

/-! ### The two steps that do NOT depend on the AK.HC (A.4) transport.

The two private lemmas below are the outer shell of the response-transfer estimate
(`p.response.transfer`): the
degenerate branch and the integration in `a`.  Together they reduce the response-transfer estimate
to the SINGLE pathwise
estimate

`|(φ (X_a - Y) · (X_a - Y))_{U_t}| ≤ C₀ * (3 ^ (-t) * ‖M₀^{1/2}((X_a)_· - Y)‖_{B,t} ^ 2)` (P1)

for each sample `a` on a NONSINGULAR grid, which is the remaining analytic content (the change
of variables `x = q y` of `p.response.transfer` composed with the pullback estimates and AK.HC
Lemma A.1 (A.4)).
Nothing below assumes (P1); the reduction is unconditional. -/

/-- **The response-transfer estimate** (`p.response.transfer`).  Integration by parts, the cutoff
functional
estimate, and the direct full-dual pairing of AK.HC Lemma A.1 (A.4) give
`E[|(φ (∇v_t^± - P^±) · (a_± ∇v_t^± - Q^±))_{U_t}|] ≤ C W^±`,
with a constant `C` that is independent of the eccentricity of the grid: the comparison of the
rounded and unrounded metrics costs only the dimensional factor
`|m^{-1/2}q| |q^{-1}m^{1/2}| ≤ 3` of `p.response.transfer`, and the pullback `x = q y` preserves
normalized cell averages and their Besov sums.

`W^±` is `respWMinus`/`respWPlus` (`ResponseBlockObjects.lean`); `(P^±, Q^±) = Y^±` is
`respYMinus`/`respYPlus`; the cutoff class is `IsResponseCutoff`.

The cutoff-product estimate consumes
`ContDiff R (top : N-infty) phi`, `HasCompactSupport phi`, `tsupport phi subseteq openCubeSet Q`
and a bound `B` on the derivative of `scalarCutoffGradientField phi` -- i.e. SMOOTHNESS and a
SECOND-derivative scale -- while a cutoff class recording only nonnegativity, the bound `2`, the
support, the mean and a FIRST-order Lipschitz constant, with a piecewise linear witness, does not
suffice.  `IsResponseCutoff` (`ResponseBlockObjects.lean`) therefore carries exactly the four
additional
conjuncts (`ContDiff`, `HasCompactSupport`, `tsupport phi subseteq adaptedCell qq t`, and the
pullback second-derivative bound `1024 * d ^ 4 * Theta ^ 2 * 3 ^ (-2 * t)`), and
`exists_isResponseCutoff` above constructs a genuinely SMOOTH member of that class out of
`QuantitativeCubeCutoff.canonicalFun` and `smoothTransitionProfile` of the pinned CoarseGraining
package.  See the `IsResponseCutoff` docstring: the two coefficients carry the universal profile
factor `Theta >= 1`, which no choice of the recorded numerals avoids, since
`derivBound = secondDerivBound = 1` is satisfied by no smooth profile and bounded by nothing in the
pinned package.

The hypothesis is not deficient, so the reference-cube product-term bound applies; the remaining
analytic transport is the change
of variables `x = q y` of `p.response.transfer` carrying `cutoffPairingOnCellAux` on `U_t` to
`cutoffProductTermOnCube` on the reference cube, composed with the pullback estimates
(`partialSeminorm_pullback_fst_le`, `partialSeminorm_pullback_snd_le`,
`explicitRoundedGrid_metricFrobenius_product_le`, all in `ScaleAverageSeminorm.lean`) and the
integration in
`a`.

The statement carries, once per sign, the integrability of the Besov square of the family whose
cutoff pairing it bounds -- the integrand of `respWeakEnergySet`
itself, which is the weakest form the proof can use and the form the caller can state.  The
hypothesis is necessary: without it the statement is false, since on a family whose Besov square
is not `P`-integrable Bochner returns `0`, `respWeakEnergySet` is a subsingleton, `W^± = 0`, and
the left-hand side can still be positive.  The caller (`ResponseCutoffEstimate.lean`) discharges
both from
`integrable_besovSeminorm_sq_respCell` above.

The statement carries `2 * d ≤ 3 ^ jStar`.  Without it the selected grid `q = respGrid jStar F`
need not be invertible -- the only route to `IsUnit (explicitRoundedGrid jStar m)` in the tree is
`Geometry.isUnit_roundedGrid` (`HCPoly/Entry/Geometry/RoundedGridBasic.lean`), which consumes
exactly this
premise -- so the change of variables `x = q y` of `p.response.transfer`, and with it the pullback
of the
potential, are unavailable at ANY constant, whatever one is willing to pay.  The premise is
discharged at the sole caller (`ResponseCutoffEstimate.lean`) by `raw.hj`, the very hypothesis
that already
supplies the grid's invertibility there, so nothing downstream pays for it.  It is needed only on
the `PosDef` branch; the `¬PosDef` branch is killed by the vanishing of the grid for a singular
metric.

A separate ellipticity hypothesis `IsEllipticFieldOn lam Lam (adaptedCell q t) b` is NOT needed.
Although the coefficient of the response-transfer estimate is the bare `respCoeffMinus F a` and
carries no ellipticity, that
hypothesis is DERIVABLE, for both signs, from the sample's own qualitative local uniform
ellipticity together with the invertibility that the new premise above already provides: see
`exists_elliptic_representative_respCoeffMinus` / `…Plus` and
`memLp_two_normalizedCubeMeasure_pullback_flux` in
`HCPoly/Entry/Response/Kernel/EllipticRepresentativeInputs.lean`, which close the `hflux` slot of
the generic
CG product bridge outright.  The response-transfer estimate therefore takes no ellipticity binder.
-/
theorem integral_abs_cutoffPairingOnCell_le_respWeak (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
        (t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
        -- Without this the selected grid `q = respGrid jStar F` need not be
        -- invertible, so the change of variables `x = q y` of `p.response.transfer` is
        -- unavailable at
        -- ANY constant; see the paragraph in the docstring above.
        2 * d ≤ 3 ^ jStar →
        IsResponseCutoff (respGrid jStar F) t φ →
        ∀ uM : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) →
          -- The Besov square of this family must be `P`-integrable, otherwise the
          -- Bochner integral defining `W^-` collapses to `0` while the left-hand side stays
          -- positive; see `integrable_besovSeminorm_sq_respCell` above.
          Integrable (fun a => besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                  (optimizerField (respCoeffMinus F a) (uM a)) -
                respYMinus P jStar F t e)) ^ 2) P →
        ∀ uP : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) →
          Integrable (fun a => besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                  (optimizerField (respCoeffPlus F a) (uP a)) -
                respYPlus P jStar F t e)) ^ 2) P →
        (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
              (respCoeffMinus F a) (uM a)| ∂P) ≤ C * respWMinus P jStar F t e ∧
          (∫ a, |cutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
              (respCoeffPlus F a) (uP a)| ∂P) ≤ C * respWPlus P jStar F t e := by
  obtain ⟨C₀, hC₀, hpath⟩ := exists_pathwise_cutoff_pairing_bound d
  exact exists_pos_const_integral_abs_pairing_le_respWeak d C₀ hC₀ hpath

/-! ### Collapse diagnostics for the cutoff estimate.

`respEJMinus/Plus` (`ResponseBlockObjects.lean`) and both scale integrals inside
`respTauMinus/Plus` are Bochner integrals of `a ↦ respJ … (respCoeffMinus F a)`,
and the fourth summand of the cutoff estimate is a Bochner integral of `a ↦
|cutoffPairingOnCellAux …|`.
Nothing in the cutoff estimate's premises forces any of them to be `Integrable`: a point of
`CoeffSpace d` is only QUALITATIVELY locally uniformly elliptic
(`HCPoly/Setup/CoefficientSpace.lean`
-- the ellipticity constants are quantified INSIDE the predicate, per sample), so on a general `P`
the map `a ↦ respJ …` is unbounded and need not even be a.e.-strongly measurable.  On such a `P`
all of these integrals take the Bochner junk value `0` (`MeasureTheory.integral_undef`), the entire
right-hand side of the cutoff estimate collapses to `0`, and the estimate then FORCES
`Jtilde^-(e) = 0`.  But `respCenteredJMinus` (`ResponseBlockObjects.lean`) is a purely algebraic
function of `adaptedMean P (respGrid jStar F) t`, i.e. of the four ENTRYWISE integrals of the
coarse block (`HCPoly/Setup/Response.lean`), which do not collapse together with the response
integrals: a law with uniformly bounded upper ellipticity and degenerating lower ellipticity keeps
`(adaptedMean P q t).upperLeft` finite while `respJ` blows up.  The lemmas below are half of that
argument; the construction of the law itself is not carried out here.
This is the same integrability obstruction as the one for the response-transfer estimate. -/

/-! ### The integrability premises of the cutoff estimate.

Both statements below consume `raw` and are the cutoff-estimate analogues of
`integrable_besovSeminorm_sq_respCell` above (the integrability hypothesis of the response-transfer
estimate).  They record
the premises the cutoff estimate now carries as explicit obligations on the law, rather than
folding them into the estimate itself (which would make it false -- see the collapse diagnostics
above) or leaving them unstated inside `response_cutoff_estimate`.

Why they cannot be discharged here from the available hypotheses.
`Annealed.responseJ_eq_coarseBlock_adapted` (`HCPoly/Entry/Annealed/AdaptedDomainLocality.lean`)
turns
`ResponseJ (adaptedCellTranslate q j y) p r (a.1)` into the fixed quadratic
`(1/2) (-p, r). A(U; a) (-p, r) - p. r` in the coarse block, and the coarse block IS entrywise
`P`-integrable under `raw` (`Annealed.hasIntegrableCoarseBlock_adapted`, from `raw.stat`,
`raw.ell`, `raw.hj`).  That would settle integrability immediately -- but the cutoff estimate's
integrands are `respJ... (respCoeffMinus F a)` and `respJ... (respCoeffPlus F a)`, i.e. the
RECENTRED fields `a - g` and `a^t + g` of `p.response.transfer`, and
`responseJ_eq_coarseBlock_adapted` is available only for members of the coefficient carrier: its
proof goes through `exists_elliptic_representative_adapted`, and a recentred field need not be
elliptic at all.  Supplying the recentred avatar of that identity (equivalently, the ellipticity of
`a_±` that the self-dual recentring of Step 4 is supposed to provide) is the content of these two
statements. -/

/-- **The pathwise-response integrability premise of the cutoff estimate.**
`respEJMinus/Plus` (`ResponseBlockObjects.lean`) and both scale integrals inside
`respTauMinus/Plus` are Bochner integrals of `a => respJ... (respCoeffMinus F a)`;
without integrability they take the junk value `0`, the entire right-hand side of the cutoff
estimate collapses and the estimate forces `Jtilde^±(e) = 0`.  The cutoff estimate therefore
carries the four instances `u ∈ {s, t}` × `sign ∈ {-, +}` of this statement, and the caller
discharges them from here. -/
theorem integrable_respJ_respCell (d : ℕ) [NeZero d] (γ : ℝ) (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (c : CoeffSpace d → CoeffField d)
    (_hc : c = respCoeffMinus F ∨ c = respCoeffPlus F) (u : ℤ)
    (_hlo : (jStar : ℤ) ≤ u) (_hhi : u ≤ t) (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (c a)) P := by
  have := _raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    _raw.symm _raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid _raw.hj hm
  have hint : HasIntegrableCoarseBlock P (respCell jStar F u) :=
    hasIntegrableCoarseBlock_respCell P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj F hm u
  rcases _hc with rfl | rfl
  · exact integrable_respJ_respCoeffMinus P jStar F u hq hint p q'
  · exact integrable_respJ_respCoeffPlus P jStar F u hq hint p q'

/-- **The cutoff-pairing integrability premise of the cutoff rows, PROVED.**
The fourth summand of each row of the cutoff estimate is `∫ |cutoffPairingOnCellAux...| ∂P`, which
is `0` on a non-integrable integrand; that is the `E4 = 0` input of the collapse lemma, and the
weak-quantity bound does not supply it,
being itself true, vacuously, with both sides `0` in the bad case.

The two ingredients are now available.  The pathwise cutoff estimate dominates the absolute pairing
by a fixed multiple of the squared scale-average seminorm, whose integrability is
`integrable_besovSeminorm_sq_respCell` above; and the pairing is almost everywhere strongly
measurable in the sample, because a response maximizer is determined almost everywhere by the
canonical Chapter-2 one, whose cutoff-weighted readouts -- the three linear ones and the quadratic
one -- are measurable through the Galerkin selection.  The two measurability premises on the
all-scale maximum and the dimension premise are those of `integrable_besovSeminorm_sq_respCell`,
and are discharged at the same call site. -/
theorem integrable_abs_cutoffPairingOnCell (d : ℕ) [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (c : CoeffSpace d → CoeffField d)
    (_hc : c = respCoeffMinus F ∨ c = respCoeffPlus F) (φ : Vec d → ℝ)
    (_hφ : IsResponseCutoff (respGrid jStar F) t φ) (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (_hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a)) :
    Integrable (fun a =>
      |cutoffPairingOnCellAux (respCell jStar F t) φ Y (c a) (u a)|) P := by
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    _raw.symm _raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid _raw.hj hm
  have hbesov := integrable_besovSeminorm_sq_respCell d hd γ S ε σ Cglob Cprof Csrc Bresp H P E Ψ
    Kg Src B jStar F s t _raw hMmeas hMint c _hc p q' Y u _hu
  have hmeas := aestronglyMeasurable_abs_pairing_of_maximizer P jStar F t _raw.hj hm c _hc
    p q' Y _hφ u _hu
    ((measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffMinus_full
      (respGrid jStar F) (Geometry.isUnit_roundedGrid _raw.hj hm) t F p q'
        _hφ).aestronglyMeasurable)
    ((measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffPlus_full
      (respGrid jStar F) (Geometry.isUnit_roundedGrid _raw.hj hm) t F p q'
        _hφ).aestronglyMeasurable)
  have hrep : ∀ a : CoeffSpace d, ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        c a =ᵐ[volumeMeasureOn (respCell jStar F t)] f := by
    rcases _hc with rfl | rfl
    · exact fun a => exists_elliptic_representative_respCell_respCoeffMinus _raw.hj hm t a
    · exact fun a => exists_elliptic_representative_respCell_respCoeffPlus _raw.hj hm t a
  have _ := hq
  simpa only [cutoffPairingOnCellAux] using
    integrable_abs_pairing_of_measurable_of_integrable_besov P jStar F t φ _raw.hj _hφ hm c hrep
      Y u hmeas hbesov

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Nonnegativity of the pathwise and annealed response energies

The pathwise response `J(U; p, q'; b)` of AK.HC (2.9) is the supremum of the A-harmonic
variational functional over the admissible class, and the zero field is admissible for every
coefficient field `b`; hence the supremum dominates `0` without any ellipticity hypothesis.  The
two recentred coefficients `a_- = a - g` and `a_+ = aᵗ + g` are special cases.  Integrating a
pointwise nonnegative function yields a nonnegative Bochner integral for every measure, so the
annealed responses `E[J_t^-]` and `E[J_t^+]` are nonnegative as well, with no integrability
hypothesis.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise response `J(U_u; p, r; a_-)` of the recentred coefficient `a_- = a - g` is
nonnegative.  It is the response supremum of AK.HC (2.9), whose admissible class contains the
zero field, so the value at the zero competitor already witnesses nonnegativity. -/
theorem zero_le_respJ_respCoeffMinus {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ respJ q u p r (respCoeffMinus F a) := by
  have _ := hq
  exact responseJ_nonneg (HighContrast.adaptedCell q u) p r (respCoeffMinus F a)

/-- The pathwise response `J(U_u; p, r; a_+)` of the recentred coefficient `a_+ = aᵗ + g` is
nonnegative.  It is the response supremum of AK.HC (2.9), whose admissible class contains the
zero field, so the value at the zero competitor already witnesses nonnegativity. -/
theorem zero_le_respJ_respCoeffPlus {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ respJ q u p r (respCoeffPlus F a) := by
  have _ := hq
  exact responseJ_nonneg (HighContrast.adaptedCell q u) p r (respCoeffPlus F a)

/-- The annealed response `E[J_t^-] = E[J(U_t; p, q^-; a_-)]` is nonnegative.  Its integrand is
pointwise nonnegative by the pathwise nonnegativity of the response, and the Bochner integral of
a pointwise nonnegative function is nonnegative for every measure, so no integrability hypothesis
is required.  This is the sign `0 ≤ E[J_t^-]` of the printed display
`e.response.energy.and.defect`. -/
theorem zero_le_respEJMinus {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F)) :
    0 ≤ respEJMinus P jStar F t e := by
  unfold respEJMinus
  exact integral_nonneg fun a =>
    zero_le_respJ_respCoeffMinus (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)

/-- The annealed response `E[J_t^+] = E[J(U_t; p, q^+; a_+)]` is nonnegative.  Its integrand is
pointwise nonnegative by the pathwise nonnegativity of the response, and the Bochner integral of
a pointwise nonnegative function is nonnegative for every measure, so no integrability hypothesis
is required.  This is the sign `0 ≤ E[J_t^+]` of the printed display
`e.response.energy.and.defect`. -/
theorem zero_le_respEJPlus {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F)) :
    0 ≤ respEJPlus P jStar F t e := by
  unfold respEJPlus
  exact integral_nonneg fun a =>
    zero_le_respJ_respCoeffPlus (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The oscillation of a response cutoff across a descendant adapted cell

The scale gain `3^-H` of the cutoff estimate `p.response.transfer` comes from the derivative
scale carried by the cutoff class `IsResponseCutoff`: the pullback `y ↦ φ (qq y)` is Lipschitz
with constant `32 d^2 Θ 3^(-t)`, so across a cell of generation `t - n` of `q`-diameter
`3^(t-n)` a cutoff can vary by at most that constant times `3^(t-n)`, i.e. by at most
`32 d^2 Θ 3^(-n)`.  This is proved here uniformly in the generation `t`, the aligned index `w`
and the grid `qq`, together with its `n = 0` specialization to a single adapted cell.
-/

open HCPolySupport.HighContrast (adaptedCellCenter)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Across two points of a descendant adapted cell `adaptedCellAtCenter qq (t - n) w`, a
cutoff `φ` of the response class `IsResponseCutoff qq t φ` oscillates by at most
`32 d^2 responseCutoffProfileConst 3^(-n)`: the Lipschitz scale `3^(-t)` of the cutoff class,
applied on the cell of generation `t - n`, loses exactly the `n` generations of the descent. -/
theorem abs_sub_le_of_mem_adaptedCellAtCenter {d : ℕ} {qq : Mat d} (hq : IsUnit qq) {t : ℤ}
    {φ : Vec d → ℝ} (h : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ)
    {x y : Vec d} (hx : x ∈ adaptedCellAtCenter qq (t - (n : ℤ)) w)
    (hy : y ∈ adaptedCellAtCenter qq (t - (n : ℤ)) w) :
    |φ x - φ y| ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by
  obtain ⟨v, hv, hxv⟩ :=
    Geometry.mem_adaptedCellTranslate_iff.mp
      (show x ∈ HighContrast.adaptedCellTranslate qq (t - (n : ℤ))
          (adaptedCellCenter qq (t - (n : ℤ)) w) from hx)
  obtain ⟨u, hu, hyu⟩ :=
    Geometry.mem_adaptedCellTranslate_iff.mp
      (show y ∈ HighContrast.adaptedCellTranslate qq (t - (n : ℤ))
          (adaptedCellCenter qq (t - (n : ℤ)) w) from hy)
  set z : Vec d := adaptedCellCenter qq (t - (n : ℤ)) w with hzdef
  set z' : Vec d := matVecMul qq⁻¹ z with hz'def
  have hz : matVecMul qq z' = z := by
    have hdet : IsUnit qq.det := (Matrix.isUnit_iff_isUnit_det qq).mp hq
    rw [hz'def, Geometry.matVecMul_eq_mulVec, Geometry.matVecMul_eq_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv qq hdet, Matrix.one_mulVec]
  have hxv' : x = matVecMul qq (z' + v) := by
    rw [← hxv, ← hz, matVecMul_add]
  have hyu' : y = matVecMul qq (z' + u) := by
    rw [← hyu, ← hz, matVecMul_add]
  have hdist : dist (z' + v) (z' + u) = ‖v - u‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  have hvu : ‖v - u‖ ≤ (3 : ℝ) ^ (t - (n : ℤ)) := by
    rw [pi_norm_le_iff_of_nonneg (zpow_nonneg (by norm_num) _)]
    intro i
    rw [Real.norm_eq_abs]
    have hv1 : -((1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ))) < v i := by
      have h := (Recurrence.mem_centeredCube_iff.mp hv i).1
      linarith only [h]
    have hv2 : v i < (1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ)) :=
      (Recurrence.mem_centeredCube_iff.mp hv i).2
    have hu1 : -((1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ))) < u i := by
      have h := (Recurrence.mem_centeredCube_iff.mp hu i).1
      linarith only [h]
    have hu2 : u i < (1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ)) :=
      (Recurrence.mem_centeredCube_iff.mp hu i).2
    have hlt : |v i - u i| < (3 : ℝ) ^ (t - (n : ℤ)) := by
      rw [abs_lt]
      constructor
      · linarith only [hv1, hu2]
      · linarith only [hv2, hu1]
    exact hlt.le
  have hL : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) := by
    have hd : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have hΘ : (0 : ℝ) ≤ responseCutoffProfileConst := responseCutoffProfileConst_pos.le
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-t) := zpow_nonneg (by norm_num) (-t)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) hΘ) h3
  have harith : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) *
      (3 : ℝ) ^ (t - (n : ℤ)) =
      32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have hrn : (3 : ℝ) ^ (-(n : ℤ)) = (3 : ℝ) ^ (-(n : ℝ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ))]
      congr 1
      push_cast
      ring
    calc
      (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) *
          (3 : ℝ) ^ (t - (n : ℤ))
          = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst *
              ((3 : ℝ) ^ (-t) * (3 : ℝ) ^ (t - (n : ℤ))) := by ring
      _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst *
              (3 : ℝ) ^ (-t + (t - (n : ℤ))) := by rw [← zpow_add₀ h3]
      _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℤ)) := by
            rw [show -t + (t - (n : ℤ)) = -(n : ℤ) by ring]
      _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by rw [hrn]
  calc
    |φ x - φ y| = dist (φ x) (φ y) := (Real.dist_eq _ _).symm
    _ = dist (φ (matVecMul qq (z' + v))) (φ (matVecMul qq (z' + u))) := by rw [hxv', hyu']
    _ ≤ (Real.toNNReal
            (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) : ℝ) *
          dist (z' + v) (z' + u) := h.lipschitz.dist_le_mul _ _
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) * ‖v - u‖ := by
          rw [Real.coe_toNNReal _ hL, hdist]
    _ ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) *
          (3 : ℝ) ^ (t - (n : ℤ)) := mul_le_mul_of_nonneg_left hvu hL
    _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := harith

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The subcell means of the cutoff fluctuation

In the terminal-optimizer replacement of `p.response.transfer` the cutoff fluctuation `φ - 1` is
replaced, on each aligned subcell of the coarse scale, by its mean there.  Those means are the
weights of the row.  This module records the two elementary analytic facts the row assembly
consumes alongside the already-recorded mean-zero identity: the cutoff and its fluctuation are
integrable on every aligned adapted cell, and each subcell mean of the fluctuation is at most one
in absolute value.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A cutoff `φ` of the response class `IsResponseCutoff qq t φ` is integrable on every aligned
adapted cell `adaptedCellAtCenter qq j w`.  The class makes `φ` continuous with compact support,
so `φ`
is integrable on the whole space and hence on any set.  This is the integrability of the cutoff on
the subcells of the row assembly of `p.response.transfer`. -/
theorem integrableOn_isResponseCutoff {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq) {t : ℤ}
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (j : ℤ) (w : Fin d → ℤ) :
    MeasureTheory.IntegrableOn φ (adaptedCellAtCenter qq j w) := by
  have hcont : Continuous φ := hφ.contDiff.continuous
  have hint : Integrable φ := hcont.integrable_of_hasCompactSupport hφ.hasCompactSupport
  have hVopen : IsOpen (adaptedCellAtCenter qq j w) :=
    Geometry.isOpen_adaptedCellTranslate hq j _
  exact hint.integrableOn.congr_fun (fun x _ => rfl) hVopen.measurableSet

/-- The cutoff fluctuation `φ - 1` of the response class `IsResponseCutoff qq t φ` is integrable on
every aligned adapted cell `adaptedCellAtCenter qq j w`.  The cutoff is integrable there and so is
the
constant `1`, because the aligned cell has finite volume.  This is the integrability of the subcell
weights of the centred cutoff decomposition of `p.response.transfer`. -/
theorem integrableOn_sub_one_isResponseCutoff {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq)
    {t : ℤ} {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (j : ℤ) (w : Fin d → ℤ) :
    MeasureTheory.IntegrableOn (fun x => φ x - 1) (adaptedCellAtCenter qq j w) := by
  have hVfin : volume (adaptedCellAtCenter qq j w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top qq j w
  exact (integrableOn_isResponseCutoff hq hφ j w).sub (integrableOn_const hVfin)

/-- Every subcell mean of the cutoff fluctuation `φ - 1` is at most one in absolute value.  The
response class confines `φ` to `[0, 2]`, so the fluctuation `φ - 1` lies in `[-1, 1]`; its volume
average over an aligned adapted cell therefore inherits the bound, because the cell has finite
nonzero volume.  These are the weights of the row assembly of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_isResponseCutoff_le_one {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (j : ℤ)
    (w : Fin d → ℤ) :
    |volumeAverage (adaptedCellAtCenter qq j w) (fun x => φ x - 1)| ≤ 1 := by
  have hVfin : volume (adaptedCellAtCenter qq j w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top qq j w
  have hVpos : 0 < (volume (adaptedCellAtCenter qq j w)).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ j)]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det qq).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ j) d)
  have hbound : |∫ x in adaptedCellAtCenter qq j w, (φ x - 1) ∂volume|
      ≤ (volume (adaptedCellAtCenter qq j w)).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := adaptedCellAtCenter qq j w) (f := fun x => φ x - 1) (C := 1)
      (lt_top_iff_ne_top.mpr hVfin) (fun x _ => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by have h0 := hφ.nonneg x; linarith only [h0],
          by have h2 := hφ.le_two x; linarith only [h2]⟩)
    rw [Real.norm_eq_abs, one_mul, MeasureTheory.measureReal_def] at h
    exact h
  unfold volumeAverage
  rw [abs_mul, abs_of_pos (inv_pos.mpr hVpos)]
  calc (volume (adaptedCellAtCenter qq j w)).toReal⁻¹
        * |∫ x in adaptedCellAtCenter qq j w, (φ x - 1) ∂volume|
      ≤ (volume (adaptedCellAtCenter qq j w)).toReal⁻¹ * (volume (adaptedCellAtCenter qq j
        w)).toReal :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hVpos)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The elliptic representative of a coefficient of the carrier

A point of the coefficient carrier is elliptic only almost everywhere, while the variational
identities of the response are stated for a pointwise elliptic coefficient.  The bridge is the
elliptic representative `Response.aHarmonicOfAEEq`: replacing a coefficient by an almost
everywhere equal one carries a harmonic function along and leaves unchanged every quantity the
cutoff estimate of `p.response.transfer` mentions.  This module records that invariance for the
maximizer property, for the averaged variation energy on any measurable subset, and for the
cutoff half-energy.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The response-maximizer property is invariant under an almost-everywhere replacement of the
coefficient: if `u` maximizes the response functional for `a` on `U`, then the field carried
along `a =ᵐ b` maximizes it for `b`.  Both response averages are rewritten by
`volumeAverage_scalarResponseIntegrand_congr`; this is the transport behind the terminal-optimizer
replacement row of `p.response.transfer`. -/
theorem isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d)
    {u : AHarmonicFunction a U} (hmax : IsResponseMaximizer U p r a u) :
    IsResponseMaximizer U p r b (Response.aHarmonicOfAEEq h u) := by
  intro w
  have key := hmax (Response.aHarmonicOfAEEq h.symm w)
  have h1 : volumeAverage U (scalarResponseIntegrand U b p r w) =
      volumeAverage U (scalarResponseIntegrand U a p r
        (Response.aHarmonicOfAEEq h.symm w)) :=
    volumeAverage_scalarResponseIntegrand_congr h.symm p r w _ (fun _ => rfl)
  have h2 : volumeAverage U (scalarResponseIntegrand U a p r u) =
      volumeAverage U (scalarResponseIntegrand U b p r (Response.aHarmonicOfAEEq h u)) :=
    volumeAverage_scalarResponseIntegrand_congr h p r u _ (fun _ => rfl)
  rw [h1, ← h2]
  exact key

/-- The averaged variation energy on a smaller measurable set is invariant under an
almost-everywhere replacement of the coefficient: `a` and `b` agree almost everywhere on `U`,
hence on any `V ⊆ U`, and the two energy integrands differ only through the coefficient matrix
there. -/
theorem volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff {d : ℕ}
    {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b)
    (u : AHarmonicFunction a U) :
    volumeAverage V (scalarVariationEnergyIntegrand b (Response.aHarmonicOfAEEq h u))
      = volumeAverage V (scalarVariationEnergyIntegrand a u) := by
  have hV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hV] with x hx
  simp only [scalarVariationEnergyIntegrand, Response.aHarmonicOfAEEq_grad, ← hx]

/-- The cutoff half-energy is invariant under an almost-everywhere replacement of the
coefficient: the doubled optimizer state `X = (∇u, b ∇u)` agrees wherever `a = b`, so its
cutoff-weighted half-energy is unchanged. -/
theorem cutoffHalfEnergyAux_aHarmonicFunctionOfAEEqCoeff {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b) (φ : Vec d → ℝ)
    (u : AHarmonicFunction a U) :
    cutoffHalfEnergyAux U φ b (Response.aHarmonicOfAEEq h u) = cutoffHalfEnergyAux U φ a u := by
  unfold cutoffHalfEnergyAux volumeAverage
  congr 1
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp only [optimizerField, Response.aHarmonicOfAEEq_grad, ← hx]

end

end HCPolySupport.HighContrast.Multiscale
end
