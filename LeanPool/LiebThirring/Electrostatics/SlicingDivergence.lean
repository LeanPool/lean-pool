/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingCellIntegral
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFluxField

/-!
# Compact Voronoi cell and exterior divergence formulas

Cell divergence theorem proved by coordinate line slicing.

Equation, with precisely the directed bisector measures used in the energy deficit.
-/

public section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace LiebThirring

theorem integrable_compact_directional_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Position → E) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Position) :
    Integrable (fun x => fderiv ℝ g x v) :=
  ((hg.continuous_fderiv (by decide)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hgc.fderiv_apply ℝ v)

theorem integral_compact_directional_derivative_eq_zero (g : Position → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (a : Fin 3) :
    (∫ x, fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ a)) = 0 := by
  rw [integral_coordinateLines a _ (integrable_compact_directional_derivative g hg hgc _)]
  have he (q : Planar) :
      (∫ t, fderiv ℝ g (coordinateLine a q t) (EuclideanSpace.basisFun (Fin 3) ℝ a)) = 0 := by
    let G := fun t => g (coordinateLine a q t)
    have hG : ContDiff ℝ 1 G := hg.comp (contDiff_coordinateLine a q 1)
    have hGc : HasCompactSupport G := hgc.comp_isClosedEmbedding
      (isClosedEmbedding_coordinateLine a q)
    have hi := integral_derivative_finite_halfspaces (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (fun _ i => Fin.elim0 i) G (deriv G)
      (fun t => (hG.differentiable (by decide) t).hasDerivAt)
      hG.continuous_deriv_one hGc hGc.deriv
    have hd (t : ℝ) : deriv G t =
        fderiv ℝ g (coordinateLine a q t) (EuclideanSpace.basisFun (Fin 3) ℝ a) :=
      (hasDerivAt_comp_coordinateLine g hg a q t).deriv
    simpa only [Fin.forall_fin_zero, ofPred_true, Measure.restrict_univ,
      Finset.univ_eq_empty, Finset.sum_empty, sub_zero, hd] using hi
  simp only [he, integral_zero]

theorem fderiv_position_component (V : Position → Position) (hV : ContDiff ℝ 1 V)
    (a : Fin 3) (x v : Position) :
    fderiv ℝ (fun y => V y a) x v = (fderiv ℝ V x v) a := by
  have hd := (EuclideanSpace.proj a : Position →L[ℝ] ℝ).hasFDerivAt.comp x
    ((hV.differentiable (by decide)).differentiableAt.hasFDerivAt)
  have hd' : HasFDerivAt (fun y => V y a)
      ((EuclideanSpace.proj a : Position →L[ℝ] ℝ).comp (fderiv ℝ V x)) x := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using hd
  rw [hd'.fderiv, ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj]

theorem integrable_positionDivergence (V : Position → Position)
    (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V) :
    Integrable (positionDivergence V) := by
  apply integrable_finsetSum
  intro a _
  simpa only [EuclideanSpace.coe_proj] using
    (EuclideanSpace.proj a : Position →L[ℝ] ℝ).integrable_comp
      (integrable_compact_directional_derivative V hV hVc (EuclideanSpace.basisFun (Fin 3) ℝ a))

theorem integral_positionDivergence_eq_zero (V : Position → Position)
    (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V) :
    (∫ x, positionDivergence V x) = 0 := by
  unfold positionDivergence
  rw [integral_finsetSum _ (fun a _ => (by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj a : Position →L[ℝ] ℝ).integrable_comp
        (integrable_compact_directional_derivative V hV hVc (EuclideanSpace.basisFun (Fin 3) ℝ
          a))))]
  apply Finset.sum_eq_zero
  intro a _
  have hg : ContDiff ℝ 1 (fun x => V x a) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj a : Position →L[ℝ] ℝ).contDiff.comp hV
  have hgc : HasCompactSupport (fun x => V x a) := hVc.comp_left (map_zero (EuclideanSpace.proj a :
    Position →L[ℝ] ℝ))
  simpa only [fderiv_position_component V hV a] using
    integral_compact_directional_derivative_eq_zero (fun x => V x a) hg hgc a

/-- Cell divergence theorem proved by coordinate line slicing. -/
theorem voronoiCell_compact_flux {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    (V : Position → Position) (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V) :
    (∫ x in voronoiCell R k, positionDivergence V x) =
      ∑ l : {l : Fin M // l ≠ k},
        ∫ y in voronoiFace R k l.val, inner ℝ (bisectorNormal R k l.val) (V y)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  classical
  have hg (a : Fin 3) : ContDiff ℝ 1 (fun x => V x a) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj a : Position →L[ℝ] ℝ).contDiff.comp hV
  have hgc (a : Fin 3) : HasCompactSupport (fun x => V x a) :=
    hVc.comp_left (map_zero (EuclideanSpace.proj a : Position →L[ℝ] ℝ))
  have hi (a : Fin 3) : Integrable (fun x => (fderiv ℝ V x
      (EuclideanSpace.basisFun (Fin 3) ℝ a)) a)  := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj a : Position →L[ℝ] ℝ).integrable_comp
        (integrable_compact_directional_derivative V hV hVc (EuclideanSpace.basisFun (Fin 3) ℝ a))
  have hb (a : Fin 3) (l : {l : Fin M // l ≠ k}) :
      IntegrableOn (fun x => bisectorNormal R k l.val a * V x a) (voronoiFace R k l.val)
        (bisectorSurfaceMeasure R hR k l.val l.property.symm) :=
    ((integrable_compact_bisectorSurfaceMeasure R hR k l.val l.property.symm
      (fun x => V x a) (hg a).continuous (hgc a)).const_mul _).integrableOn
  unfold positionDivergence
  rw [integral_finsetSum _ (fun a _ => (hi a).integrableOn)]
  have he (a : Fin 3) :
      (∫ x in voronoiCell R k, (fderiv ℝ V x (EuclideanSpace.basisFun (Fin 3) ℝ a)) a) =
      ∑ l : {l : Fin M // l ≠ k}, bisectorNormal R k l.val a *
        ∫ x in voronoiFace R k l.val, V x a
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
    simpa only [fderiv_position_component V hV a] using
      voronoiCell_compact_directional_integral R hR k a (fun x => V x a) (hg a) (hgc a)
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun a _ => hb a l)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Equation, with precisely the directed bisector measures used in the energy deficit. -/
theorem voronoiExterior_compact_flux {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    (V : Position → Position) (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V) :
    (∫ x in (voronoiCell R k)ᶜ, positionDivergence V x) =
      -(∑ l : {l : Fin M // l ≠ k},
        ∫ y in voronoiFace R k l.val, inner ℝ (bisectorNormal R k l.val) (V y)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) := by
  have he := integral_add_compl (isOpen_voronoiCell R k).measurableSet
    (integrable_positionDivergence V hV hVc)
  rw [integral_positionDivergence_eq_zero V hV hVc,
    voronoiCell_compact_flux R hR k V hV hVc] at he
  exact eq_neg_of_add_eq_zero_right he

end LiebThirring

end
