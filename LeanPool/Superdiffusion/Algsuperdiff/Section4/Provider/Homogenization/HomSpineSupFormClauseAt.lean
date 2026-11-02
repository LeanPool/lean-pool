/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormClause

/-!
# HomSpineSupFormClauseAt

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The sup-form clause producer with its constant DISPLAYED

## Why the constant has to come out of the `∃`

`HomSpineSupFormClause`'s single-depth clause production
hides its constant `√d · CA · C(p,d)` inside an existential.  That is harmless
when `CA` is model-free, and USELESS when it is not: the frozen budget
(`K_abs ≤ C_abs·|log γ|`) is a QUANTITATIVE statement about the constant, and
the Step-3 realization at the fixed exponent `p = 4d` has
`CA ≍ |log γ|^{1-1/(4d)}`.

This file re-states the same theorem with the `C(p,d)` factor hoisted OUT of the
existential and `CA` universally quantified INSIDE it, so that the produced
constant is the displayed term `(ofReal √d · CA · C).toReal` and its
`CA`-dependence is visible to the budget.

The proof is unchanged; the ONLY change is the order of the two
binders `C` (hoisted) and `CA` (pushed in).  `C(p,d)` never depended on `CA`:
it comes from `exists_printedCoarseGrainingFiniteP_smoothDual`, which is fixed
before the cube, the orders, the coefficient field, the forcing and the
solutions.

`exists_coarseGrainingSupMultiscale_of_depthConverseOn_of_at` is the REGRESSION
certificate: the statement follows from this one immediately.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

/-! ## 1. The producer, with `C(p,d)` hoisted -/

/-- **THE SUP-FORM CLAUSE, AT A DISPLAYED CONSTANT.**

`HomSpineSupFormClause`'s single-depth clause production
with `C(p,d)` hoisted out of the existential and `CA` quantified inside: the
produced clause constant is the DISPLAYED term
`(ofReal √d · CA · C).toReal`, so a consumer can bound it. -/
theorem exists_coarseGrainingSupMultiscale_of_depthConverseOn_at (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ CA : ℝ≥0∞, CA ≠ ⊤ → ∀ Pred : FractionalOrder → Prop,
        (∀ (m : ℤ) (j : ℕ) (s : FractionalOrder), Pred s →
          NegativeBesovGridSmoothDualConverseAtDepth (originCube d m) s p j CA) →
      ∀ (m : ℤ) (jn : ℕ), 0 < jn →
      ∀ (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 → Pred s →
      ∀ (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
        (u v : H1Function (openCubeSet (originCube d m))),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
      ∀ (E1 E2 Dg : ℝ) (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d),
        0 ≤ E1 → 0 ≤ E2 → 0 ≤ Dg →
        (∀ R, 0 ≤ Gen R) →
        (∀ R, printedLocalEnergy a u R ≤ Gen R) →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0 s1 ≤
          ENNReal.ofReal E1 →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) (by omega) a sigma0 hsigma0
            (fractionalOrderHalf s1) ≤ ENNReal.ofReal E2 →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg →
        Fgrad = (centeredCubeGradientDifferenceL2Field m u v).toField →
        Fflux = (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField →
          CoarseGrainingSupMultiscale (originCube d m) jn
            ((ENNReal.ofReal (Real.sqrt d) * CA * C).toReal) s.1 s1.1 s2.1
            p.exponent.toReal sigma0 E1 E2 Dg Gen Fgrad Fflux := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hsd⟩ := exists_printedCoarseGrainingFiniteP_smoothDual d hd p hp
  refine ⟨C, hCtop.ne, ?_⟩
  intro CA hCA Pred hconv
  set Kd : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt d) * CA with hKd
  have hKdne : Kd ≠ ⊤ := by
    rw [hKd]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCA
  have hKdC : Kd * C ≠ ⊤ := ENNReal.mul_ne_top hKdne hCtop.ne
  intro m jn hjn s1 s s2 hs1s hss2 hband a sigma0 hsigma0 g u v hg hu hv hzero
    E1 E2 Dg Gen Fgrad Fflux hE10 hE20 hDg0 hGen0 hGen hE1 hE2 hDg hFg hFf S hS N
  have hms : (originCube d m).scale = m := rfl
  have hn : (originCube d m).scale - (jn : ℤ) ≤ (originCube d m).scale := by omega
  have hnm : (originCube d m).scale - (jn : ℤ) < m := by rw [hms]; omega
  /- the energy slot, from the clause's own hypothes -/
  have hS0 : (0 : ℝ) ≤ S := by
    have hge := hS 0
    have h0 : (0 : ℝ) ≤ coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal
        (s.1 - s1.1) jn 0 Gen := by
      rw [coarseGrainingEnergyPartial_def]
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (descendantsAverage_nonneg _ _ _ fun R _ => Real.rpow_nonneg (hGen0 R) _)) _
    linarith only [hge, h0]
  have hSlot : weightedLocalSymmetricEnergyLp (originCube d m)
      ((originCube d m).scale - (jn : ℤ)) hn a u s1 s p ≤ ENNReal.ofReal S :=
    weightedLocalSymmetricEnergyLp_le_ofReal hn a u s1 s p (wgap := s.1 - s1.1) le_rfl
      (by omega) hGen0 hGen hS0 hS
  /- the smooth-dual composition, already assembl -/
  have hdisplay := hsd m ((originCube d m).scale - (jn : ℤ)) hnm s1 s s2 hs1s hss2 a
    sigma0 hsigma0 g hg u v hu hv hzero
  set Ggrad := centeredCubeGradientDifferenceL2Field m u v with hGgrad
  set Gflux := centeredCubeFluxDifferenceL2Field m a sigma0 u v with hGflux
  set W : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) with hW
  have hsplit : ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) =
      ENNReal.ofReal (Real.sqrt d) * W := by
    rw [gridScaleGauge, hms, ENNReal.ofReal_mul (Real.sqrt_nonneg _), hW, real_rpow_three_eq]
  /- the ONE input, one depth at a ti -/
  have hSgrad := ofReal_negBesovSupPartialNorm_le_of_depthConverse (originCube d m) s p N
    (fun j => hconv m j s hband) Ggrad
  have hSflux := ofReal_negBesovSupPartialNorm_le_of_depthConverse (originCube d m) s p N
    (fun j => hconv m j s hband) Gflux
  have hchain : ENNReal.ofReal
      (sigma0 * negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Fgrad +
        negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Fflux) ≤
      ENNReal.ofReal (coarseGrainingFinitePRHS (Kd * C).toReal s.1 s2.1 sigma0 E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ))) := by
    rw [hFg, hFf,
      ENNReal.ofReal_add (mul_nonneg hsigma0.le (negBesovSupPartialNorm_nonneg _ _ _ _ _))
        (negBesovSupPartialNorm_nonneg _ _ _ _ _),
      ENNReal.ofReal_mul hsigma0.le]
    calc ENNReal.ofReal sigma0 *
          ENNReal.ofReal
            (negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Ggrad.toField) +
          ENNReal.ofReal
            (negBesovSupPartialNorm (originCube d m) s.1 p.exponent.toReal N Gflux.toField)
        ≤ ENNReal.ofReal sigma0 *
            (ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Ggrad)) +
            ENNReal.ofReal (gridScaleGauge d s.1 (originCube d m).scale) *
              (CA * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p Gflux) :=
          add_le_add (mul_le_mul' le_rfl hSgrad) hSflux
      _ = Kd * (W * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p) := by
          rw [hKd, hsplit]
          simp only [centeredCubeFluxComparisonSmoothDualLHS, ← hGgrad, ← hGflux]
          ring
      _ ≤ Kd * localCoarseGrainingLpRHS C (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p :=
          mul_le_mul' le_rfl hdisplay
      _ = localCoarseGrainingLpRHS (Kd * C) (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p :=
          localCoarseGrainingLpRHS_const_mul Kd C (originCube d m)
            ((originCube d m).scale - (jn : ℤ)) hn a sigma0 hsigma0 g u s1 s s2 p
      _ ≤ ENNReal.ofReal (coarseGrainingFinitePRHS (Kd * C).toReal s.1 s2.1 sigma0 E1 E2 Dg S
            ((originCube d m).scale - (jn : ℤ))) :=
          localCoarseGrainingLpRHS_le_ofReal hn a hsigma0 g u s1 s s2 p hss2
            ENNReal.toReal_nonneg hE10 hE20 hDg0 hS0
            (le_of_eq (ENNReal.ofReal_toReal hKdC).symm) hE1 hE2 hDg hSlot
  exact (ENNReal.ofReal_le_ofReal_iff
    (coarseGrainingFinitePRHS_nonneg ENNReal.toReal_nonneg s.2.1 hss2 hE10 hE20 hDg0
      hS0)).mp hchain

end

end Algsuperdiff.Section4.Provider.Homogenization
