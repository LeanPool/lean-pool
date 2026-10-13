/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationInterior
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorContinuity

/-!
# ShiftedResolventRegularity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
The interior regularity witness that indexes the analytic resolvent on bounded
data, and the two hypotheses that supply it.
-/

/-!
# Interior regularity witnesses for the shifted resolvents

The interior estimates the divergence-form layer consumes are packaged here as
predicates on the coefficient field: `HasContinuousShiftedResolvents` for a
continuous representative on the open set, and `HasLocalHolderShiftedResolvents`
and `HasLocalHolderPenalizedResolvents` for the local Hölder form.

Stating the layer against a witness rather than against a smallness hypothesis
keeps the analytic input in one place: a caller supplies the witness once and
every downstream statement is indexed by it.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- **The interior regularity witness.**  For every positive shift and every
`L²` datum with an essential bound, the shifted resolvent has a representative
continuous on the open domain.  No boundary value is asserted, and no bound on
the representative is asserted: the statement mentions only the `L²` class. -/
def HasContinuousShiftedResolvents (a : CoeffField d) {lam Lam : ℝ}
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a) : Prop :=
  ∀ {mu : ℝ} (hmu : 0 < mu) (f : ScalarL2 U) {M : ℝ}, 0 ≤ M →
    (∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ M) →
    ∃ v : Vec d → ℝ, ContinuousOn v U ∧
      v =ᵐ[volumeMeasureOn U] alphaShiftedResolvent a hmu hlam hEll f

open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing in
/-- **The freezing route to the witness.**  A coefficient whose symmetric part
is the scalar field `nu • 1` and whose skew part is continuous on the domain has
continuous interior representatives, with no restriction on the size of the
skew part. -/
theorem hasContinuousShiftedResolvents_continuousCoeff [NeZero d] (hd : 2 ≤ d)
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {nu : ℝ} (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) U)
    {lam Lam : ℝ} (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a) :
    HasContinuousShiftedResolvents a hlam hEll := by
  intro mu hmu f M hM hfM
  obtain ⟨v, hv, hvae, -⟩ :=
    continuousOn_alphaShiftedResolvent_continuousCoeff hd hU a hnu hsymm hcont
      hmu hlam hEll f hM hfM
  exact ⟨v, hv, hvae⟩


/-- **Restriction of the freezing route to a subdomain.**  The witness itself
does not restrict along `V ⊆ U`, because the resolvent of `V` is a different
operator; the hypotheses of the freezing route do, so the witness for the
subdomain is available whenever the coefficient is continuous on `U`. -/
theorem hasContinuousShiftedResolvents_mono_continuousCoeff [NeZero d]
    (hd : 2 ≤ d) (a : CoeffField d) {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {nu : ℝ} (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) U)
    {lam Lam : ℝ} (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a) :
    HasContinuousShiftedResolvents a hlam
      (hEll.mono hV.isOpen.measurableSet hVU) :=
  hasContinuousShiftedResolvents_continuousCoeff hd a hV hnu hsymm
    (hcont.mono hVU) hlam (hEll.mono hV.isOpen.measurableSet hVU)

variable [NeZero d]

/-- **The quantitative interior regularity witness.**  It adds one clause to
`HasContinuousShiftedResolvents`: at every point of the domain there is a
radius, depending on the point but not on the datum, on which every
representative of the shifted resolvent of a datum with essential bound `M`
that is continuous there obeys the explicit interior Hölder bound of the
small-contrast Schauder estimate, with gradient budget `(min mu lam)⁻¹ ‖f‖` and
forcing budget `B * M`.  The radius does not see the datum at all, and the
constant sees it only through `‖f‖` and `M`.  On a bounded domain the first of
these is controlled by the second, since `‖f‖ ≤ M * |U| ^ (1 / 2)`, and the
constant is increasing in its gradient budget; so the bound is uniform over
every family of data with a common essential bound. -/
def HasLocalHolderShiftedResolvents (a : CoeffField d) {lam Lam : ℝ}
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a) (alpha B : ℝ) :
    Prop :=
  HasContinuousShiftedResolvents a hlam hEll ∧
    ∀ {mu : ℝ} (hmu : 0 < mu), ∀ x ∈ U, ∀ {M : ℝ}, 0 ≤ M →
      ∃ r > 0, euclideanBall x r ⊆ U ∧
        ∀ f : ScalarL2 U, (∀ᵐ y ∂volumeMeasureOn U, |f y| ≤ M) →
          ∀ v : Vec d → ℝ, ContinuousOn v (euclideanBall x r) →
            v =ᵐ[volume.restrict (euclideanBall x r)]
              alphaShiftedResolvent a hmu hlam hEll f →
            EuclideanHolderBoundOn (euclideanBall x r) alpha
              (penalizationInteriorHolderConstant d alpha r
                ((min mu lam)⁻¹ * ‖f‖) (B * M)) v

/-- **The quantitative witness for the penalized family.**  One radius and one
constant, both free of the penalization index, serve the whole penalized
sequence of a fixed datum at each point of the part domain. -/
def HasLocalHolderPenalizedResolvents (a : CoeffField d)
    (hU : IsOpenBoundedConvexDomain U) {V : Set (Vec d)} (hV : IsOpen V)
    {lam Lam : ℝ} (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a)
    (alpha B : ℝ) : Prop :=
  ∀ {mu : ℝ} (hmu : 0 < mu) (f : ScalarL2 U) {M : ℝ}, 0 ≤ M →
    (∀ᵐ y ∂volumeMeasureOn U, |f y| ≤ M) →
    ∀ x ∈ V, ∃ r > 0, euclideanBall x r ⊆ V ∧ ∀ n : ℕ,
      ∃ v : Vec d → ℝ, ContinuousOn v (euclideanBall x r) ∧
        v =ᵐ[volume.restrict (euclideanBall x r)]
          penalizedResolvent a hU.isOpen hV hmu hlam hEll n f ∧
        EuclideanHolderBoundOn (euclideanBall x r) alpha
          (penalizationInteriorHolderConstant d alpha r
            ((min mu lam)⁻¹ * ‖f‖) (B * M)) v

end

end DivergenceFormProcess.Form
