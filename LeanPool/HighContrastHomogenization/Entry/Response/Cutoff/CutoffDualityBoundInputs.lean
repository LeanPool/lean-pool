/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AffineSobolevPullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CutoffPairingCubeAverageIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.DualityBoundHypotheses
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Product.Bridge
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# High-contrast homogenization: Entry.Response.Cutoff.CutoffDualityBoundInputs

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The negative-Besov duality bound, assembled on the reference cube

This file serves the cutoff estimate `e.response.cutoff.estimate`. On the adapted cell
`U_t = q ⋄_t`, it identifies the cutoff-weighted pairing of a harmonic optimizer's gradient and
flux defects, after integration by parts and the change of variables `x = q y`, with minus the
centred cube average of the potential against the flux defect contracted with the cutoff's
gradient (AK.HC Lemma A.1, (A.4)). It reads the generic negative-Besov duality bound of the
cutoff-product estimate on the reference cube, records the Besov scale weight of that cube at
every scale, and shows that coordinatewise square-integrability of a doubled field on the
adapted cell supplies the measurability and the two slotwise pullback bounds the duality
estimate needs. Instantiating these at the centred doubled optimizer field, it assembles the
resulting coefficient and seminorm bounds into the shape the final inequality consumes: a
dimension-only constant times the scale weight `3^{-t}` times the square of the scale-average
seminorm.
-/

section
/-!
## The cutoff pairing as a centred cube average

On the adapted cell `U_t = q ⋄_t` the cutoff-weighted pairing of the gradient defect of a harmonic
optimizer against its flux defect is, after integration by parts, the negative of the normalized
average of the centred potential against the flux defect contracted with the gradient of the
cutoff.  Composing that identity with the change of variables `x = q y` and with the adjointness of
the pulled-back pairing rewrites it on the reference cube `originCube d t`, where the first slot of
the pairing is the pulled-back flux defect `q⁻¹ (b ∇v - q₀)` and the second is the gradient of the
pulled-back cutoff.

Because the flux defect is weakly divergence free, the pairing against the cutoff gradient has zero
average, so centring the potential changes nothing.  The resulting identity is the exact shape in
which the negative-Besov duality bound `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)) is
stated, and it is the identity half of the pathwise cutoff bound: no inequality is involved.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff-weighted pairing of the gradient defect of a harmonic optimizer against its flux
defect, normalized over the adapted cell `U_t = q ⋄_t`, equals the negative of the normalized
average over the reference cube `originCube d t` of the Euclidean pairing of the pulled-back flux
defect `q⁻¹ (b ∇v - q₀)` against the centred pulled-back potential multiplied into the gradient of
the pulled-back cutoff.  With `q` the selected grid and the potential centred at its cube average,
this is the identity form of the cutoff estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1,
(A.4)) on which the negative-Besov duality bound is applied. -/
theorem volumeAverage_cutoff_pairing_eq_neg_cubeAverage_centered
    {d : ℕ} {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {b : CoeffField d} (u : AHarmonicFunction b (HighContrast.adaptedCell (respGrid jStar F) t))
    (Y : BlockVec d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ HighContrast.adaptedCell (respGrid jStar F) t)
    (hflux : MemVectorL2 (HighContrast.adaptedCell (respGrid jStar F) t)
      (fun x => matVecMul (b x) (u.toH1.grad x)))
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (HighContrast.adaptedCell (respGrid jStar F) t))
    (hint2 : MeasureTheory.IntegrableOn (fun x => (u.toH1.toFun x - vecDot Y.1 x) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j))) (HighContrast.adaptedCell (respGrid jStar F) t))
    (hcube : MeasureTheory.IntegrableOn
      (fun y => vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (scalarCutoffGradientField
          (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y))
      (cubeSet (originCube d t)))
    (hcubeProd : MeasureTheory.IntegrableOn
      (fun y => respCenteredPullbackH1 hjStar hm t b u Y y * vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (scalarCutoffGradientField
          (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y))
      (cubeSet (originCube d t))) :
    volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -cubeAverage (originCube d t) (fun y =>
          vecDot
            (matVecMul (respGrid jStar F)⁻¹
              ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
            (((respCenteredPullbackH1 hjStar hm t b u Y y -
                cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
              scalarCutoffGradientField
                (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y : Vec d))) := by
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell (respGrid jStar F) t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F)
      (isUnit_respGrid hjStar hm) t).isFiniteMeasure_restrict_volume
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell (respGrid jStar F) t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
  have hint2' : MeasureTheory.IntegrableOn
      (fun x => (u.toH1.toFun x - vecDot Y.1 x - 0) *
        vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
          (fun j => (fderiv ℝ φ x) (basisVec j)))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    simpa only [sub_zero] using hint2
  have hIBP := cubeAverage_cutoff_pairing_eq_neg (q := respGrid jStar F) hq t hU u hflux Y 0
    hφ hφ_compact hφ_sub hint1 hint2'
  have hsol : IsSolenoidalOn (HighContrast.adaptedCell (respGrid jStar F) t)
      (fun x => matVecMul (b x) (u.toH1.grad x) - Y.2) :=
    isSolenoidalOn_fluxDefect_of_finiteMeasure u hflux Y.2
  have hzero : cubeAverage (originCube d t)
      (fun y => vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (scalarCutoffGradientField
          (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) = 0 := by
    let f : Vec d → ℝ := fun x => vecDot
      (matVecMul (b x) (u.toH1.grad x) - Y.2)
      (fun j => (fderiv ℝ φ x) (basisVec j))
    have hz : volumeAverage (HighContrast.adaptedCell (respGrid jStar F) t) f = 0 :=
      volumeAverage_vecDot_solenoidal_gradCutoff_eq_zero hU hsol hφ hφ_compact hφ_sub
    have hcov := volumeAverage_adaptedCell_eq_cubeAverage_comp (q := respGrid jStar F) hq t f
    have hcomp : cubeAverage (originCube d t)
        (fun y => f (matVecMul (respGrid jStar F) y)) = 0 := hcov.symm.trans hz
    refine Eq.trans ?_ hcomp
    apply congrArg (cubeAverage (originCube d t))
    funext y
    exact vecDot_pullback_slots hq hφ
      ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2) y
  have hcent := cubeAverage_centered_mul_of_average_eq_zero (originCube d t)
    (f := fun y => respCenteredPullbackH1 hjStar hm t b u Y y)
    (g := fun y => vecDot
      (matVecMul (respGrid jStar F)⁻¹
        ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
      (scalarCutoffGradientField
        (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y))
    hcubeProd hcube hzero
  have hpt : ∀ y : Vec d,
      (u.toH1.toFun (matVecMul (respGrid jStar F) y)
          - vecDot Y.1 (matVecMul (respGrid jStar F) y) - 0) *
        vecDot
          (matVecMul (b (matVecMul (respGrid jStar F) y))
            (u.toH1.grad (matVecMul (respGrid jStar F) y)) - Y.2)
          (fun j => (fderiv ℝ φ (matVecMul (respGrid jStar F) y)) (basisVec j))
      = (respCenteredPullbackH1 hjStar hm t b u Y).toFun y *
        vecDot
          (matVecMul (respGrid jStar F)⁻¹
            ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
          (scalarCutoffGradientField
            (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y) := by
    intro y
    simp only [optimizerField, Prod.snd_sub]
    rw [respCenteredPullbackH1_toFun, sub_zero]
    refine congrArg (fun t : ℝ =>
      (u.toH1.toFun (matVecMul (respGrid jStar F) y)
        - vecDot Y.1 (matVecMul (respGrid jStar F) y)) * t) ?_
    rw [vecDot_pullback_slots hq hφ
      (matVecMul (b (matVecMul (respGrid jStar F) y))
        (u.toH1.grad (matVecMul (respGrid jStar F) y)) - Y.2) y]
    congr 1
  have hmain : volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -cubeAverage (originCube d t) (fun y =>
          respCenteredPullbackH1 hjStar hm t b u Y y *
            vecDot
              (matVecMul (respGrid jStar F)⁻¹
                ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
              (scalarCutoffGradientField
                (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) := by
    unfold respCell
    rw [hIBP]
    apply congrArg (fun z : ℝ => -z)
    apply congrArg (cubeAverage (originCube d t))
    funext y
    exact hpt y
  calc
    volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
        = -cubeAverage (originCube d t) (fun y =>
            respCenteredPullbackH1 hjStar hm t b u Y y *
              vecDot
                (matVecMul (respGrid jStar F)⁻¹
                  ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
                (scalarCutoffGradientField
                  (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) := hmain
    _ = -cubeAverage (originCube d t) (fun y =>
            (respCenteredPullbackH1 hjStar hm t b u Y y
              - cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) *
              vecDot
                (matVecMul (respGrid jStar F)⁻¹
                  ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
                (scalarCutoffGradientField
                  (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) :=
          congrArg (fun z : ℝ => -z) hcent.symm
    _ = -cubeAverage (originCube d t) (fun y =>
            vecDot
              (matVecMul (respGrid jStar F)⁻¹
                ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
              (((respCenteredPullbackH1 hjStar hm t b u Y y
                  - cubeAverage (originCube d t)
                      (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
                scalarCutoffGradientField
                  (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y : Vec d))) := by
          apply congrArg (fun z : ℝ => -z)
          apply congrArg (cubeAverage (originCube d t))
          funext y
          exact (vecDot_smul_right
            (matVecMul (respGrid jStar F)⁻¹
              ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
            (scalarCutoffGradientField
              (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)
            (respCenteredPullbackH1 hjStar hm t b u Y y
              - cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z))).symm

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The negative-Besov duality bound at the pulled-back cutoff data

The generic cutoff-product duality bound
`abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct` in namespace
`Book.Ch05.Section53.JUpperBoundWeakNorms`
is the direct full-dual pairing form of `AK.HC` Lemma A.1, (A.4).  This file reads it on the
reference cube after the linear change of variables of the cutoff argument: with `q = respGrid
jStar F`
the centred potential is the pulled-back response `respCenteredPullbackH1`, the flux is the
pulled-back flux defect `q⁻¹ (b ∇v - q0)`, and the weight field is the gradient of the pulled-back
cutoff `scalarCutoffGradientField (φ ∘ q)`.  Every analytic hypothesis of the generic bound — the
membrane and smoothness data of the weight field, the derivative bound, the square integrability of
the flux, and the two negative-Besov seminorm bounds — is carried through unchanged at the
pulled-back data.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal

noncomputable section

/-- The negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)) evaluated on the reference cube
`openCubeSet (originCube d t)` at the pulled-back cutoff data.  With `q = respGrid jStar F`, the
potential is the centred pulled-back response `respCenteredPullbackH1`, the flux is the pulled-back
flux defect `q⁻¹ (b ∇v - q0)`, and the weight field is the gradient of the pulled-back cutoff
`φ ∘ q`; the two exponents take the symmetric value `s = t = 1/2`.

The conclusion is the generic bound with its four coefficient `let`s expanded: the scaled gradient
and flux seminorms, the cutoff-product coefficient built from the derivative bound `B` and the
cutoff gradient, and the flux coefficient carrying the scale weights. -/
theorem abs_cubeAverage_pullback_pairing_le
    {d : ℕ} {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (b : CoeffField d) (u : AHarmonicFunction b (HighContrast.adaptedCell (respGrid jStar F) t))
    (Y : BlockVec d) {φ : Vec d → ℝ} {B gradWeak fluxWeak : ℝ}
    (hB : 0 ≤ B)
    (hξLp :
      MemLp (scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y))) ∞
        (normalizedCubeMeasure (originCube d t)))
    (hξ :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) x i))
    (hderiv :
      ∀ i : Fin d, ∀ z ∈ cubeSet (originCube d t),
        ‖fderiv ℝ (fun x =>
          scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) x i) z‖ ≤ B)
    (hflux :
      MemLp (fun y => matVecMul (respGrid jStar F)⁻¹
        ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d t)))
    (hgradWeak :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
        (respCenteredPullbackH1 hjStar hm t b u Y).grad ≤ gradWeak)
    (hfluxWeak :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
        (fun y => matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) ≤ fluxWeak) :
    |cubeAverage (originCube d t)
        (fun x => vecDot
          (matVecMul (respGrid jStar F)⁻¹
            ((optimizerField b u (matVecMul (respGrid jStar F) x) - Y).2))
          (((respCenteredPullbackH1 hjStar hm t b u Y x
              - cubeAverage (originCube d t)
                  (fun y => respCenteredPullbackH1 hjStar hm t b u Y y)) •
            scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) x :
              Vec d)))| ≤
      (((2 * cubeScaleFactor (originCube d t) * B +
            3 * cubeLpNorm (originCube d t) ∞
              (scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)))) *
            ((Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) *
                (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (Fintype.card (Fin d) : ℝ))) *
          ((Fintype.card (Fin d) : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + (1 - 1 / 2)) *
              cubeBesovScaleWeight (-(1 - 1 / 2 - 1 / 2)) (originCube d t)))) *
        ((cubeBesovScaleWeight (-(1 / 2)) (originCube d t) * gradWeak) *
          (cubeBesovScaleWeight (-(1 / 2)) (originCube d t) * fluxWeak)) := by
  exact abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct
    (Q := originCube d t) (s := 1 / 2) (t := 1 / 2)
    (hs_pos := by norm_num) (hs_lt_one := by norm_num) (hst := by norm_num)
    (flux := fun y => matVecMul (respGrid jStar F)⁻¹
      ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
    (u := respCenteredPullbackH1 hjStar hm t b u Y)
    (ξ := scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)))
    (B := B) (gradWeak := gradWeak) (fluxWeak := fluxWeak)
    (hB := hB) (hξLp := hξLp) (hξ := hξ) (hderiv := hderiv) (hflux := hflux)
    (hgradWeak := hgradWeak) (hfluxWeak := hfluxWeak)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Constant arithmetic of the pathwise cutoff bound

The negative-Besov duality bound of the cutoff argument yields, on a reference cube, the product
of two coefficient bounds and two pulled-back seminorm bounds.  This file assembles those factors
into the single shape consumed by the annealed estimate: a dimensional constant times the scale
weight `3 ^ (-t)` times the square of the scale-average seminorm.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- The product of the two coefficient bounds and the two pulled-back seminorm bounds of the
pathwise cutoff estimate is bounded by the dimensional constant `K * L * 3 * d ^ 2` times the
scale weight `3 ^ (-t)` and the squared scale-average seminorm `A ^ 2`.  The coefficient bounds
are `gradCoeff ≤ K * 3 ^ (-t)` and `fluxCoeff ≤ L`, the seminorm bounds are `scaledGrad ≤ G * A`
and `scaledFlux ≤ f * A`, and the two Frobenius factors satisfy `G * f ≤ 3 * d ^ 2`; all
quantities are nonnegative.  This is the form in which the pathwise cutoff bound
`e.response.cutoff.estimate` feeds the annealed one. -/
theorem mul_le_const_mul_rpow_mul_sq {d : ℕ} (t : ℤ) {gradCoeff fluxCoeff scaledGrad scaledFlux
    G f A K L : ℝ}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hf : 0 ≤ f) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hgc : 0 ≤ gradCoeff) (hfc : 0 ≤ fluxCoeff)
    (hsg : 0 ≤ scaledGrad) (hsf : 0 ≤ scaledFlux)
    (hgradCoeff : gradCoeff ≤ K * (3 : ℝ) ^ (-(t : ℝ)))
    (hfluxCoeff : fluxCoeff ≤ L)
    (hscaledGrad : scaledGrad ≤ G * A) (hscaledFlux : scaledFlux ≤ f * A)
    (hGf : G * f ≤ 3 * (d : ℝ) ^ 2) :
    (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) ≤
      (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) := by
  have _ := hgc
  have _ := hf
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-(t : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(t : ℝ)) := le_of_lt hr
  have hKr : 0 ≤ K * (3 : ℝ) ^ (-(t : ℝ)) := mul_nonneg hK hr0
  have hGA : 0 ≤ G * A := mul_nonneg hG hA
  have h1 : gradCoeff * fluxCoeff ≤ (K * (3 : ℝ) ^ (-(t : ℝ))) * L :=
    mul_le_mul hgradCoeff hfluxCoeff hfc hKr
  have h2 : scaledGrad * scaledFlux ≤ (G * A) * (f * A) :=
    mul_le_mul hscaledGrad hscaledFlux hsf hGA
  have h3 : ((K * (3 : ℝ) ^ (-(t : ℝ))) * L) * ((G * A) * (f * A)) ≤
      (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) := by
    calc
      ((K * (3 : ℝ) ^ (-(t : ℝ))) * L) * ((G * A) * (f * A))
          = (K * L) * ((3 : ℝ) ^ (-(t : ℝ)) * ((G * f) * A ^ 2)) := by
            ring
      _ ≤ (K * L) * ((3 : ℝ) ^ (-(t : ℝ)) * ((3 * (d : ℝ) ^ 2) * A ^ 2)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hGf (sq_nonneg A)) hr0
            · exact mul_nonneg hK hL
      _ = (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) := by
            ring
  exact le_trans (mul_le_mul h1 h2 (mul_nonneg hsg hsf) (mul_nonneg hKr hL)) h3

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The Besov scale weight of the reference cube

The Besov scale weight `cubeBesovScaleWeight s Q = (cubeScaleFactor Q) ^ (-s)` assigns to a
triadic cube `Q` the geometric weight `3^{-s · scale Q}`, and the scale factor is
`cubeScaleFactor Q = 3 ^ (scale Q)`.  On the reference cube `originCube d t`, whose scale is `t`,
both collapse to elementary powers of `3`: the scale factor is `3 ^ t` and the weight is
`3^{-s t}`.  In particular the exponent `-1/2` weight is `3^{t/2}` and the exponent `0` weight is
`1`.  These are the weight evaluations used when the cutoff support of the response is expanded in
the cube Besov scale.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The scale factor of the reference cube `originCube d t` is `3 ^ t`, the integer power being
read as a real power: `cubeScaleFactor (originCube d t) = 3 ^ (t : ℝ)`. -/
theorem cubeScaleFactor_originCube {d : ℕ} (t : ℤ) :
    cubeScaleFactor (originCube d t) = (3 : ℝ) ^ (t : ℝ) :=
  (HCPolySupport.cubeScaleFactor_originCube t).trans (Real.rpow_intCast 3 t).symm

/-- The Besov scale weight of exponent `s` on the reference cube `originCube d t` equals
`3^{-s t}`: `cubeBesovScaleWeight s (originCube d t) = 3 ^ (-s * (t : ℝ))`. -/
theorem cubeBesovScaleWeight_originCube {d : ℕ} (s : ℝ) (t : ℤ) :
    cubeBesovScaleWeight s (originCube d t) = (3 : ℝ) ^ (-s * (t : ℝ)) := by
  unfold cubeBesovScaleWeight
  rw [cubeScaleFactor_originCube, mul_comm (-s) (t : ℝ),
    Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The exponent `-1/2` Besov scale weight of the reference cube `originCube d t` is the positive
power `3^{t/2}`: `cubeBesovScaleWeight (-(1/2)) (originCube d t) = 3 ^ ((t : ℝ) / 2)`. -/
theorem cubeBesovScaleWeight_neg_half_originCube {d : ℕ} (t : ℤ) :
    cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) = (3 : ℝ) ^ ((t : ℝ) / 2) := by
  rw [cubeBesovScaleWeight_originCube,
    show -(-(1 / 2 : ℝ)) * (t : ℝ) = (t : ℝ) / 2 by ring]

/-- The exponent `0` Besov scale weight of the reference cube `originCube d t` is `1`:
`cubeBesovScaleWeight 0 (originCube d t) = 1`. -/
theorem cubeBesovScaleWeight_zero_originCube {d : ℕ} (t : ℤ) :
    cubeBesovScaleWeight 0 (originCube d t) = 1 := by
  rw [cubeBesovScaleWeight_originCube,
    show -(0 : ℝ) * (t : ℝ) = 0 by ring, Real.rpow_zero]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The pulled-back cube seminorms of a square-integrable doubled field

The slotwise pullback bounds of the cutoff argument, `partialSeminorm_pullback_fst_le` and
`partialSeminorm_pullback_snd_le`, take as side conditions the integrability of the squared
Euclidean length of the metric-scaled doubled field together with its a.e. strong measurability.
This file supplies both from the single hypothesis that all `2d` coordinates of the field are
square integrable on the adapted cell.

Paper: the cutoff estimate `e.response.cutoff.estimate` and its pullback to the reference cube.
-/

open HCPolySupport.HighContrast (matSqrt)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The metric scaling of a doubled field, by `m^{1/2}` in the first slot and `m^{-1/2}` in the
second, carries square integrable coordinates to square integrable coordinates. -/
theorem memLp_two_coords_metricScaled {d : ℕ} {V : Set (Vec d)} (m : Mat d)
    {X : Vec d → BlockVec d}
    (h1 : ∀ i, MemLp (fun x => (X x).1 i) 2 (volume.restrict V))
    (h2 : ∀ i, MemLp (fun x => (X x).2 i) 2 (volume.restrict V)) :
    (∀ i, MemLp (fun x => (matVecMul (matSqrt m) (X x).1) i) 2 (volume.restrict V)) ∧
      ∀ i, MemLp (fun x => (matVecMul (matSqrt m)⁻¹ (X x).2) i) 2 (volume.restrict V) := by
  have h := memLp_two_coords_blockMatVecMul
    (⟨matSqrt m, 0, 0, (matSqrt m)⁻¹⟩ : BlockMat d) h1 h2
  constructor
  · intro i
    have hfun : (fun x => (matVecMul (matSqrt m) (X x).1) i)
        = fun x =>
          (blockMatVecMul (⟨matSqrt m, 0, 0, (matSqrt m)⁻¹⟩ : BlockMat d) (X x)).1 i := by
      funext x
      simp [blockMatVecMul, matVecMul]
    rw [hfun]
    exact h.1 i
  · intro i
    have hfun : (fun x => (matVecMul (matSqrt m)⁻¹ (X x).2) i)
        = fun x =>
          (blockMatVecMul (⟨matSqrt m, 0, 0, (matSqrt m)⁻¹⟩ : BlockMat d) (X x)).2 i := by
      funext x
      simp [blockMatVecMul, matVecMul]
    rw [hfun]
    exact h.2 i

/-- The slotwise pullback bound for the gradient slot, with the square-integrability side
conditions supplied coordinatewise. -/
theorem partialSeminorm_pullback_fst_le_of_coords {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (m : Mat d) (hm : m.PosDef) (t : ℤ) (N : ℕ)
    (X : Vec d → BlockVec d)
    (h1 : ∀ i, MemLp (fun x => (X x).1 i) 2 (volume.restrict (HighContrast.adaptedCell q t)))
    (h2 : ∀ i, MemLp (fun x => (X x).2 i) 2 (volume.restrict (HighContrast.adaptedCell q t))) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul (matTranspose q) (X (matVecMul q y)).1) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq (matTranspose q * (matSqrt m)⁻¹)) *
        besovSeminorm t (cellAverageFamily q t fun x =>
          (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) := by
  obtain ⟨k1, k2⟩ := memLp_two_coords_metricScaled (V := HighContrast.adaptedCell q t) m h1 h2
  have hX : MemLp (fun x => blockVecDot
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) 1
      (volume.restrict (HighContrast.adaptedCell q t)) :=
    memLp_one_blockVecDot_self_of_coords (W := fun x =>
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) k1 k2
  have hXm : AEStronglyMeasurable
      (fun x => ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
      (volume.restrict (HighContrast.adaptedCell q t)) := by
    have hW1 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m) (X x).1)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k1 i).aestronglyMeasurable.aemeasurable
    have hW2 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m)⁻¹ (X x).2)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k2 i).aestronglyMeasurable.aemeasurable
    exact hW1.prodMk hW2
  exact partialSeminorm_pullback_fst_le q hq m hm t N X hX hXm

/-- The slotwise pullback bound for the flux slot, with the square-integrability side conditions
supplied coordinatewise. -/
theorem partialSeminorm_pullback_snd_le_of_coords {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (m : Mat d) (hm : m.PosDef) (t : ℤ) (N : ℕ)
    (X : Vec d → BlockVec d)
    (h1 : ∀ i, MemLp (fun x => (X x).1 i) 2 (volume.restrict (HighContrast.adaptedCell q t)))
    (h2 : ∀ i, MemLp (fun x => (X x).2 i) 2 (volume.restrict (HighContrast.adaptedCell q t))) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul q⁻¹ (X (matVecMul q y)).2) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq (q⁻¹ * matSqrt m)) *
        besovSeminorm t (cellAverageFamily q t fun x =>
          (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) := by
  obtain ⟨k1, k2⟩ := memLp_two_coords_metricScaled (V := HighContrast.adaptedCell q t) m h1 h2
  have hX : MemLp (fun x => blockVecDot
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) 1
      (volume.restrict (HighContrast.adaptedCell q t)) :=
    memLp_one_blockVecDot_self_of_coords (W := fun x =>
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) k1 k2
  have hXm : AEStronglyMeasurable
      (fun x => ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
      (volume.restrict (HighContrast.adaptedCell q t)) := by
    have hW1 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m) (X x).1)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k1 i).aestronglyMeasurable.aemeasurable
    have hW2 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m)⁻¹ (X x).2)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k2 i).aestronglyMeasurable.aemeasurable
    exact hW1.prodMk hW2
  exact partialSeminorm_pullback_snd_le q hq m hm t N X hX hXm

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The two negative-Besov inputs of the duality bound

The slotwise pullback bounds `partialSeminorm_pullback_fst_le_of_coords` and
`partialSeminorm_pullback_snd_le_of_coords` hold for an arbitrary doubled field `X`, subject to
coordinatewise square integrability on the adapted cell.  This file instantiates them at the
centred doubled optimizer field `X = (∇v, b∇v) − Y`.  The first slot is then the gradient of the
centred pulled-back potential, and the second the pulled-back flux defect, while the
square-integrability hypotheses are supplied by the elliptic representative of the coefficient.

Paper: the cutoff estimate `e.response.cutoff.estimate` and the scale-average seminorm bound of
`e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (matSqrt)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The negative-Besov seminorm on the reference cube of the gradient of the centred pulled-back
potential is bounded by the scale-average seminorm of the metric-scaled doubled optimizer state,
with the metric factor `qᵀ m^{-1/2}`.  This is the gradient slot of the duality bound, obtained by
applying `partialSeminorm_pullback_fst_le_of_coords` to the centred doubled optimizer field and
rewriting its first slot through the gradient of the pulled-back centred potential. -/
theorem cubeBesov_respCenteredPullbackH1_grad_le {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (respCell jStar F t) f)
    (hbf : b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (respCenteredPullbackH1 hjStar hm t b u Y).grad ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
          (matTranspose (respGrid jStar F) * (matSqrt (explicitCanonicalMetric F))⁻¹)) *
        besovSeminorm t (cellAverageFamily (respGrid jStar F) t fun x =>
          (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
            matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2)) := by
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  obtain ⟨h1, h2⟩ :=
    memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u Y
  have hmain := partialSeminorm_pullback_fst_le_of_coords (q := respGrid jStar F) hq
    (explicitCanonicalMetric F) hm t N (fun x => optimizerField b u x - Y) h1 h2
  rw [respCenteredPullbackH1_grad hjStar hm t b u Y]
  exact hmain

/-- The negative-Besov seminorm on the reference cube of the pulled-back flux defect is bounded by
the scale-average seminorm of the metric-scaled doubled optimizer state, with the metric factor
`q⁻¹ m^{1/2}`.  This is the flux slot of the duality bound, obtained by applying
`partialSeminorm_pullback_snd_le_of_coords` to the centred doubled optimizer field. -/
theorem cubeBesov_pullback_fluxDefect_le {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (respCell jStar F t) f)
    (hbf : b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
          ((respGrid jStar F)⁻¹ * matSqrt (explicitCanonicalMetric F))) *
        besovSeminorm t (cellAverageFamily (respGrid jStar F) t fun x =>
          (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
            matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2)) := by
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  obtain ⟨h1, h2⟩ :=
    memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u Y
  have hmain := partialSeminorm_pullback_snd_le_of_coords (q := respGrid jStar F) hq
    (explicitCanonicalMetric F) hm t N (fun x => optimizerField b u x - Y) h1 h2
  exact hmain

end

end HCPolySupport.HighContrast.Multiscale
end
