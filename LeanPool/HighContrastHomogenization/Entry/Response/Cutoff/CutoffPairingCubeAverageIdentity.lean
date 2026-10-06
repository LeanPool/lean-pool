/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AffineSobolevPullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.DualityBoundHypotheses
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Support.Multiscale.NormalizedNorms
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidal
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# High-contrast homogenization: Entry.Response.Cutoff.CutoffPairingCubeAverageIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff pairing as a centred cube average, and its duality-bound hypotheses

For a cutoff `φ` in the response cutoff class `IsResponseCutoff`, this file derives from the
class's defining bounds that the pulled-back weight field `ξ = scalarCutoffGradientField (φ ∘ qq)`
is smooth, uniformly bounded to second order, measurable, and hence essentially bounded for the
normalized cube measure - the hypotheses the negative-Besov duality bound of
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)) needs. Testing the weak solenoidal condition
`HCPolySupport.IsSolenoidalOn` moves a cutoff off the gradient of an `H¹` test function at the
cost of a sign and makes a solenoidal field pair to zero against a compactly supported cutoff's
gradient. Combining this integration-by-parts step with the centering identity for a normalized
cube average and the pathwise estimate's integrability side conditions identifies the
cutoff-weighted pairing on a cell with minus the pairing of the centred potential against the
flux defect contracted with the cutoff's gradient, and, after the adapted cell's change of
variables, the same identity on the reference cube.
-/

section
/-!
## The weight-field hypotheses of the duality bound, from the cutoff class

For a cutoff `φ` in the response cutoff class `IsResponseCutoff` and a matrix `qq`, put
`ξ = scalarCutoffGradientField (fun z => φ (matVecMul qq z))`.  The negative-Besov duality bound
(`e.response.cutoff.estimate`) needs three facts about this weight field: it is smooth
coordinatewise, each coordinate field has derivative bounded by the second-order scale `3^{-2t}`,
and `ξ` itself is bounded by the first-order scale `3^{-t}`, both bounds carrying only the
dimensional prefactors recorded in the cutoff class.  The declarations below discharge those three
hypotheses directly from membership in `IsResponseCutoff`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A cutoff in the response class has a coordinatewise smooth gradient field
(`e.response.cutoff.estimate`). -/
theorem contDiff_xi_of_isResponseCutoff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec d => scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y i) :=
  contDiff_scalarCutoffGradientField_comp qq h.2.2.2.2.2.1 i

/-- For a cutoff in the response class, the derivative of each coordinate of the gradient field of
the pulled-back cutoff is bounded by the second-order scale recorded in the class
(`e.response.cutoff.estimate`). -/
theorem norm_fderiv_xi_le_of_isResponseCutoff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (i : Fin d) (z : Vec d) :
    ‖fderiv ℝ
        (fun y : Vec d => scalarCutoffGradientField (fun w : Vec d => φ (matVecMul qq w)) y i)
        z‖ ≤ 1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t) :=
  norm_fderiv_scalarCutoffGradientField_comp_le qq h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 i z

/-- For a cutoff in the response class, the gradient field of the pulled-back cutoff is bounded by
the first-order scale recorded in the class (`e.response.cutoff.estimate`). -/
theorem norm_xi_le_of_isResponseCutoff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (y : Vec d) :
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖ ≤
      32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) := by
  have hΘ : (0 : ℝ) < responseCutoffProfileConst := responseCutoffProfileConst_pos
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-t) := zpow_pos (by norm_num) (-t)
  have hd : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hr : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) hΘ.le) h3.le
  calc
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖
        ≤ (Real.toNNReal
            (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) : ℝ) :=
          norm_scalarCutoffGradientField_comp_le qq h.2.2.2.2.2.1 h.2.2.2.2.1 y
    _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) :=
          Real.coe_toNNReal _ hr

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integration by parts against a divergence-free field

Testing the weak solenoidal condition `HCPolySupport.IsSolenoidalOn` on the product of a smooth
cutoff `φ` with an `H¹(U)` function `w` moves the cutoff off the gradient of `w` and onto `w`
itself, at the cost of a sign.  This is the integration-by-parts step in the derivation of the
cutoff estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)); it turns the
cutoff-weighted pairing of the response estimate into a pairing of a centred potential against a
flux.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Integration by parts against a weakly solenoidal field `g` on an open bounded convex domain
`U`: for an `H¹(U)` function `w` and a smooth compactly supported cutoff `φ` whose support lies
in `U`, the cutoff-weighted pairing `∫_U φ (g · ∇w)` equals the negative of the pairing
`∫_U w (g · ∇φ)` in which the cutoff has been differentiated.  Both pairings are assumed
integrable on `U`.  This is the integration-by-parts step in the derivation of the cutoff
estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem integral_cutoff_vecDot_grad_eq_neg_integral_vecDot_gradCutoff {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {g : Vec d → Vec d}
    (hsol : IsSolenoidalOn U g) (w : H1Function U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U)
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x * vecDot (g x) (w.grad x)) U)
    (hint2 : MeasureTheory.IntegrableOn
      (fun x => w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) U) :
    (∫ x in U, φ x * vecDot (g x) (w.grad x))
      = -∫ x in U, w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j)) := by
  have hgrad :=
    WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae w hU hφ hφ_compact hφ_sub
  have hsolψ :
      (∫ x in U, vecDot (g x)
        ((w.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub).toH1Function.grad x))
        = 0 :=
    hsol (w.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub)
  have hF : ∀ x,
      vecDot (g x) (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))
        = φ x * vecDot (g x) (w.grad x)
          + w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j)) := by
    intro x
    simp only [vecDot, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  have hzero :
      (∫ x in U,
        vecDot (g x) (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))) = 0 := by
    have hpt : (fun x => vecDot (g x)
          ((w.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub).toH1Function.grad x))
        =ᵐ[volume.restrict U]
        (fun x => vecDot (g x)
          (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))) := by
      filter_upwards [hgrad] with x hx
      rw [hx]
    rw [← MeasureTheory.integral_congr_ae hpt, hsolψ]
  have hsplit :
      (∫ x in U, (φ x * vecDot (g x) (w.grad x)
          + w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))))
        = (∫ x in U, φ x * vecDot (g x) (w.grad x))
          + (∫ x in U, w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) :=
    MeasureTheory.integral_add hint1 hint2
  have hFsame :
      (∫ x in U, (φ x * vecDot (g x) (w.grad x)
          + w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))))
        = (∫ x in U,
          vecDot (g x) (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => (hF x).symm
  have hsum :
      (∫ x in U, φ x * vecDot (g x) (w.grad x))
        + (∫ x in U, w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) = 0 := by
    rw [← hsplit, hFsame]
    exact hzero
  exact eq_neg_of_add_eq_zero_left hsum

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Vanishing of a solenoidal field against a cutoff gradient

Testing the weak solenoidal condition `HCPolySupport.IsSolenoidalOn` on a smooth compactly
supported function `φ` whose support lies in the open bounded convex domain `U` shows that the
pairing of the field with the gradient of `φ` integrates to zero.  A smooth compactly supported
function supported in `U` is an `H¹₀(U)` test function, so the weak divergence-free condition
applies to it directly, and its gradient is the Fréchet derivative.

Consequently the normalized volume average of the same pairing vanishes as well.  This is the
observation that lets the cutoff argument behind `e.response.cutoff.estimate` replace a potential
by its centred version at no cost: the difference produced by centring is a constant multiple of
this average.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A weakly divergence-free field pairs to zero against the gradient of a smooth compactly
supported cutoff whose support lies in the domain.  For an open bounded convex domain `U`, a field
`g` satisfying `IsSolenoidalOn U g`, and a smooth `φ` with compact support contained in `U`, the
integral over `U` of the pairing of `g` with the gradient `fun j => (fderiv ℝ φ x) (basisVec j)`
is zero.  This is the vanishing used in the cutoff argument `e.response.cutoff.estimate`. -/
theorem integral_vecDot_solenoidal_gradCutoff_eq_zero {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {g : Vec d → Vec d} (hsol : IsSolenoidalOn U g)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U) :
    (∫ x in U, vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) = 0 :=
  hsol.test_of_contDiff hU.isOpen hφ hφ_compact hφ_sub

/-- The normalized volume average of a weakly divergence-free field against the gradient of a
smooth compactly supported cutoff vanishes.  For an open bounded convex domain `U`, a field `g`
satisfying `IsSolenoidalOn U g`, and a smooth `φ` with compact support contained in `U`, the
volume average over `U` of the pairing of `g` with `fun j => (fderiv ℝ φ x) (basisVec j)` is zero.
This is the vanishing used in the cutoff argument `e.response.cutoff.estimate`. -/
theorem volumeAverage_vecDot_solenoidal_gradCutoff_eq_zero {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {g : Vec d → Vec d} (hsol : IsSolenoidalOn U g)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U) :
    volumeAverage U (fun x => vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) = 0 :=
  volumeAverage_eq_zero_of_integral_eq_zero
    (integral_vecDot_solenoidal_gradCutoff_eq_zero hU hsol hφ hφ_compact hφ_sub)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The integrability hypotheses of the pathwise cutoff estimate

The pathwise cutoff pairing bound of `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4)) is
assembled in `abs_volumeAverage_cutoff_pairing_le_of_inputs` with several analytic inputs exposed as
hypotheses: the integrability of the cutoff-weighted pairing and of the centred-potential pairing on
the adapted cell, the integrability on the reference cube of the pulled-back flux defect against the
pulled-back cutoff gradient and of that pairing multiplied by the centred potential, and the
vanishing of the cube average of the flux defect against the cutoff gradient.

The hypotheses only assert what the caller already has: `IsResponseCutoff (respGrid jStar F) t φ`,
positive definiteness of the canonical metric with the grid-depth inequality `2 * d ≤ 3 ^ jStar`,
and
an almost-everywhere uniformly elliptic representative of the coefficient on the cell.  This file
discharges each hypothesis from that data.  The fields occurring in the pairings are square
integrable on the cell (`e.response.cutoff.estimate`): the optimizer flux by ellipticity, its
gradient because the optimizer is `H¹`, the pulled-back flux on the cube by the change of variables,
and the cutoff and its gradient are bounded there.

Paper: `e.response.cutoff.estimate` and the negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)).
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- **The cut-off-weighted pairing is integrable on the adapted cell.**  If the coefficient `b`
agrees almost everywhere on `respCell jStar F t` with a field uniformly elliptic there and `u` is
`b`-harmonic on the cell, then the cutoff `φ` of the response class times the Euclidean pairing of
the flux defect `b ∇u − Y.2` with the centred gradient `∇u − Y.1` is integrable on the cell.  This
is
the `hint1` input of the pathwise cutoff estimate `e.response.cutoff.estimate`: the flux defect and
the gradient defect are both coordinatewise square integrable on the cell, and the cutoff is bounded
and measurable. -/
theorem cutoffPairingIntegrability_of_inputs {d : ℕ} [NeZero d] {jStar : ℕ} {F : BlockMat d} {t : ℤ}
    {φ : Vec d → ℝ} {b : CoeffField d}
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d) :
    MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (respCell jStar F t) := by
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hbf⟩ := hb
  have hcoords :=
    memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u Y
  have hfin : IsFiniteMeasure (volume.restrict (respCell jStar F t)) := by
    simpa only [respCell] using
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  refine integrableOn_cutoff_pairing_of_coords (V := respCell jStar F t)
    (A := fun x => matVecMul (b x) (u.toH1.grad x) - Y.2)
    (B := fun x => u.toH1.grad x - Y.1) ?_ ?_ ?_ ?_
  · intro i
    simpa only [optimizerField, Prod.snd_sub, respCell] using hcoords.2 i
  · intro i
    simpa only [optimizerField, Prod.fst_sub, respCell] using hcoords.1 i
  · refine ⟨2, fun x => ?_⟩
    rw [abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  · exact hφ.contDiff.continuous.aestronglyMeasurable

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Bounded weight fields are `L^∞` for the normalized cube measure

The negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)) pairs the cutoff weight field `ξ`
against
a centred potential in the normalized pairing on a cube.  Its hypothesis on `ξ` is uniform
boundedness, `‖ξ y‖ ≤ K` for every `y`.  The two declarations below show that such a field is
`L^∞` for `normalizedCubeMeasure Q`, with `L^∞` norm at most `K`, so that the duality bound can
consume the weight field directly.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- A vector field bounded uniformly by `K` is essentially bounded, hence `L^∞`, for the
normalized cube measure (`AK.HC` Lemma A.1, (A.4)). -/
theorem memLp_top_normalizedCubeMeasure_of_norm_le {d : ℕ} (Q : TriadicCube d)
    {ξ : Vec d → Vec d} (hξm : MeasureTheory.AEStronglyMeasurable ξ (normalizedCubeMeasure Q))
    {K : ℝ} (hK : ∀ y, ‖ξ y‖ ≤ K) :
    MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q) :=
  MeasureTheory.memLp_top_of_bound hξm K (Filter.Eventually.of_forall hK)

/-- The normalized `L^∞` norm of a vector field bounded uniformly by `K` is at most `K`
(`AK.HC` Lemma A.1, (A.4)). -/
theorem cubeLpNorm_top_le_of_norm_le {d : ℕ} (Q : TriadicCube d)
    {ξ : Vec d → Vec d} {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ y, ‖ξ y‖ ≤ K) :
    cubeLpNorm Q ∞ ξ ≤ K := by
  unfold cubeLpNorm
  by_cases hξm : MeasureTheory.AEStronglyMeasurable ξ (normalizedCubeMeasure Q)
  swap
  · rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hξm, ENNReal.toReal_top]
    exact hK0
  rw [MeasureTheory.eLpNorm_exponent_top hξm]
  exact ENNReal.toReal_le_of_le_ofReal hK0
    (MeasureTheory.eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hK))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The bundled weight-field and Hessian hypotheses of the cutoff pairing bound

For a cutoff `φ` in the response cutoff class `IsResponseCutoff` and a matrix `qq`, the
negative-Besov duality bound behind `e.response.cutoff.estimate` consumes the weight field
`ξ = scalarCutoffGradientField (fun y => φ (qq y))` through its measurability, its uniform
first-order bound, and its resulting `L^∞` membership for the normalized reference-cube
measure; the same estimate consumes the nonnegativity of the second-order Hessian coefficient
carried by the cutoff class.  The declarations below discharge those four requirements directly
from membership in `IsResponseCutoff`, so that the hypotheses `hB`, `hξLp`, `hξ`, `hderiv` and
`hflux` of the pathwise cutoff pairing bound can be fed from the class instead of being carried
separately.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- The gradient field of the pulled-back cutoff of the response class is a.e. strongly measurable
for every measure on `Vec d` (`e.response.cutoff.estimate`). -/
theorem aestronglyMeasurable_xi {d : ℕ} (qq : Mat d) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (μ : MeasureTheory.Measure (Vec d)) :
    MeasureTheory.AEStronglyMeasurable
      (scalarCutoffGradientField (fun y => φ (matVecMul qq y))) μ := by
  have hcont : Continuous
      (scalarCutoffGradientField (fun y : Vec d => φ (matVecMul qq y))) := by
    refine continuous_pi ?_
    intro i
    exact (contDiff_xi_of_isResponseCutoff hφ i).continuous
  exact hcont.aestronglyMeasurable

/-- The gradient field of a cutoff of the response class is essentially bounded, hence `L^∞`, for
the normalized measure of the reference cube (`e.response.cutoff.estimate`). -/
theorem memLp_top_xi_of_isResponseCutoff {d : ℕ} [NeZero d] (qq : Mat d) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) :
    MeasureTheory.MemLp (scalarCutoffGradientField (fun y => φ (matVecMul qq y))) ∞
      (normalizedCubeMeasure (originCube d t)) := by
  have _ : NeZero d := inferInstance
  exact memLp_top_normalizedCubeMeasure_of_norm_le (originCube d t)
    (aestronglyMeasurable_xi qq hφ (normalizedCubeMeasure (originCube d t)))
    (norm_xi_le_of_isResponseCutoff hφ)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Centring one factor in a normalized cube average

`cubeAverage Q f` is the average of `f` over the cube `Q`, normalized by the volume of `Q`.
Subtracting a constant from one factor of a product changes the average of the product by that
constant times the average of the other factor.  Consequently, if the other factor has zero
average, the centred and uncentred products have the same average.

This is the algebraic step used in the cutoff argument `e.response.cutoff.estimate`, where the
negative-Besov duality bound is stated for a centred potential while the integration by parts
produces the uncentred one; the difference is a constant multiple of the average of the pairing,
which vanishes because the field paired against is divergence free.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Centring one factor of a normalized cube average.  For a cube `Q` and a constant `c`, the
average of `(f - c) * g` over `Q` equals the average of `f * g` minus `c` times the average of
`g`, whenever `f * g` and `g` are integrable on `cubeSet Q`. -/
theorem cubeAverage_sub_const_mul {d : ℕ} (Q : TriadicCube d) (c : ℝ) {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun y => f y * g y) (cubeSet Q))
    (hg : MeasureTheory.IntegrableOn g (cubeSet Q)) :
    cubeAverage Q (fun y => (f y - c) * g y)
      = cubeAverage Q (fun y => f y * g y) - c * cubeAverage Q g := by
  have hcg : MeasureTheory.IntegrableOn (fun y => c * g y) (cubeSet Q) := hg.const_mul c
  have hdiff : (fun y => (f y - c) * g y) = fun y => f y * g y - c * g y := by
    funext y
    ring
  rw [hdiff, cubeAverage, cubeAverage, cubeAverage]
  rw [MeasureTheory.integral_sub hf hcg, MeasureTheory.integral_const_mul]
  ring

/-- The centred and uncentred pairings agree when the paired field has zero average.  If
`cubeAverage Q g = 0`, then the average over `Q` of `(f - cubeAverage Q f) * g` equals the
average of `f * g`, whenever `f * g` and `g` are integrable on `cubeSet Q`. -/
theorem cubeAverage_centered_mul_of_average_eq_zero {d : ℕ} (Q : TriadicCube d)
    {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun y => f y * g y) (cubeSet Q))
    (hg : MeasureTheory.IntegrableOn g (cubeSet Q))
    (hzero : cubeAverage Q g = 0) :
    cubeAverage Q (fun y => (f y - cubeAverage Q f) * g y)
      = cubeAverage Q (fun y => f y * g y) := by
  rw [cubeAverage_sub_const_mul Q (cubeAverage Q f) hf hg, hzero]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff pairing on a cell, after integration by parts

On a cell `U`, the cutoff-weighted pairing of the gradient defect of an `A`-harmonic function
against its flux defect equals minus the pairing of the centred potential against the flux defect
contracted with the gradient of the cutoff.  This is the normalization by the cell volume of the
integration-by-parts identity `integral_cutoff_vecDot_grad_eq_neg_integral_vecDot_gradCutoff`
applied to the flux defect and to the affine defect of the potential; it is the step that opens
the cutoff argument of the response estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1,
(A.4)) by moving one derivative off the optimizer and onto the cutoff.

The centring constant `c` is arbitrary; it is chosen later to centre the potential.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- On a cell `U`, the volume average of the cutoff-weighted pairing of the gradient defect
`∇v - Y.1` against the flux defect `b ∇v - Y.2` of an `A`-harmonic function `v` equals the
negative of the volume average of the pairing of the centred potential `v - Y.1 · x - c` against
the flux defect contracted with the gradient of the cutoff.  Both pairings are assumed
integrable on `U`.  This is the normalized form of the integration-by-parts step in the
derivation of the cutoff estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem volumeAverage_cutoff_pairing_eq_neg {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {b : CoeffField d}
    (u : AHarmonicFunction b U)
    (hflux : MemVectorL2 U (fun x => matVecMul (b x) (u.toH1.grad x)))
    (Y : BlockVec d) (c : ℝ)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U)
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1)) U)
    (hint2 : MeasureTheory.IntegrableOn (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j))) U) :
    volumeAverage U (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -volumeAverage U (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
          vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
            (fun j => (fderiv ℝ φ x) (basisVec j))) := by
  have hsol : IsSolenoidalOn U (fun x => matVecMul (b x) (u.toH1.grad x) - Y.2) :=
    isSolenoidalOn_fluxDefect_of_finiteMeasure u hflux Y.2
  have hkey :
      (∫ x in U, φ x * vecDot (u.toH1.grad x - Y.1)
          (matVecMul (b x) (u.toH1.grad x) - Y.2))
        = -∫ x in U, (u.toH1.toFun x - vecDot Y.1 x - c) *
            vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
              (fun j => (fderiv ℝ φ x) (basisVec j)) := by
    have hswap :
        (∫ x in U, φ x * vecDot (u.toH1.grad x - Y.1)
            (matVecMul (b x) (u.toH1.grad x) - Y.2))
          = ∫ x in U, φ x * vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
              (u.toH1.grad x - Y.1) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [vecDot_comm]
    rw [hswap]
    have hibp := integral_cutoff_vecDot_grad_eq_neg_integral_vecDot_gradCutoff (U := U) hU
      (g := fun x => matVecMul (b x) (u.toH1.grad x) - Y.2) hsol
      (affineDefectH1 hU u.toH1 Y.1 c) hφ hφ_compact hφ_sub
      (by simpa only [affineDefectH1_grad] using hint1)
      (by simpa only [affineDefectH1_toFun] using hint2)
    simpa only [affineDefectH1_grad, affineDefectH1_toFun] using hibp
  change volumeAverage U (fun x => φ x * vecDot (u.toH1.grad x - Y.1)
      (matVecMul (b x) (u.toH1.grad x) - Y.2))
    = -volumeAverage U (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
        vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
          (fun j => (fderiv ℝ φ x) (basisVec j)))
  simp only [volumeAverage]
  rw [hkey, mul_neg]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff pairing after integration by parts, written on the reference cube

On the adapted cell `HighContrast.adaptedCell q t`, the integration-by-parts form of the
cutoff pairing is the negative of the volume average of the centred potential against the
flux defect contracted with the gradient of the cutoff.  Composing that identity with the
change of variables `x = q y` that identifies the normalized average on the adapted cell
with the normalized average on the reference cube `originCube d t` gives the form of the
cutoff argument in which the negative-Besov duality of the response estimate
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)) applies.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The integration-by-parts identity for the cutoff pairing on the adapted cell
`HighContrast.adaptedCell q t`, transported to the reference cube.  The volume average on the
adapted cell of the cutoff-weighted pairing of the gradient defect `∇v - Y.1` against the
flux defect `b ∇v - Y.2` equals the negative of the cube average on `originCube d t` of the
centred potential `v (q y) - Y.1 · (q y) - c` against the flux defect evaluated at `q y`,
contracted with the gradient of the cutoff at `q y`.  Both pairings are assumed integrable
on the adapted cell.  This is the form of the cutoff estimate `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) in which the negative-Besov duality is applied. -/
theorem cubeAverage_cutoff_pairing_eq_neg {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    (hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t))
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t))]
    {b : CoeffField d} (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hflux : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (b x) (u.toH1.grad x)))
    (Y : BlockVec d) (c : ℝ)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ HighContrast.adaptedCell q t)
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (HighContrast.adaptedCell q t))
    (hint2 : MeasureTheory.IntegrableOn (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j))) (HighContrast.adaptedCell q t)) :
    volumeAverage (HighContrast.adaptedCell q t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -cubeAverage (originCube d t) (fun y =>
          (u.toH1.toFun (matVecMul q y) - vecDot Y.1 (matVecMul q y) - c) *
            vecDot (matVecMul (b (matVecMul q y)) (u.toH1.grad (matVecMul q y)) - Y.2)
              (fun j => (fderiv ℝ φ (matVecMul q y)) (basisVec j))) := by
  have h := volumeAverage_cutoff_pairing_eq_neg (U := HighContrast.adaptedCell q t) hU u hflux Y c
    hφ hφ_compact hφ_sub hint1 hint2
  have hcv := volumeAverage_adaptedCell_eq_cubeAverage_comp (q := q) hq t
    (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j)))
  calc volumeAverage (HighContrast.adaptedCell q t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -volumeAverage (HighContrast.adaptedCell q t) (fun x =>
          (u.toH1.toFun x - vecDot Y.1 x - c) *
            vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
              (fun j => (fderiv ℝ φ x) (basisVec j))) := h
    _ = -cubeAverage (originCube d t) (fun y =>
          (u.toH1.toFun (matVecMul q y) - vecDot Y.1 (matVecMul q y) - c) *
            vecDot (matVecMul (b (matVecMul q y)) (u.toH1.grad (matVecMul q y)) - Y.2)
              (fun j => (fderiv ℝ φ (matVecMul q y)) (basisVec j))) := by
        rw [hcv]

end

end HCPolySupport.HighContrast.Multiscale
end
