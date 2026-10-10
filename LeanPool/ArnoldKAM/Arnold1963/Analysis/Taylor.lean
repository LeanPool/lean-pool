/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Taylor remainder estimates obtained by integration along a contained segment, with explicit
operator and coordinate Hessian bounds.
-/

@[expose] public section

noncomputable section
open MeasureTheory
namespace KamProject.Arnold1963

theorem norm_taylor_remainder_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    [CompleteSpace F] {f : E → F} {U : Set E} {a b : E} {C : ℝ}
    (hab : segment ℝ a b ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    (hC : NormBoundOn (fderiv ℂ (fderiv ℂ f)) U C) :
    ‖f b - f a - fderiv ℂ f a (b - a)‖ ≤ C / 2 * ‖b - a‖ ^ 2 := by
  let l : ℝ → E := AffineMap.lineMap a b
  let d : E := b - a
  let g : ℝ → F := fun t => f (l t) - f a - t • (fderiv ℂ f a d)
  let g' : ℝ → F := fun t => (fderiv ℂ f (l t) - fderiv ℂ f a) d
  have hl : Set.MapsTo l (Set.Icc 0 1) (segment ℝ a b) :=
    (convex_segment a b).mapsTo_lineMap (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  have hlU : Set.MapsTo l (Set.Icc 0 1) U := fun t ht => hab (hl ht)
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    have hpath : HasDerivAt l d t := AffineMap.hasDerivAt_lineMap
    have hfR := (hf _ (hlU ht)).differentiableAt.hasFDerivAt.restrictScalars ℝ
    have hcomp := hfR.comp_hasDerivAt t hpath
    have hlin : HasDerivAt (fun s : ℝ => s • fderiv ℂ f a d) (fderiv ℂ f a d) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℂ f a d)
    simpa [g, g', Function.comp_def, sub_apply] using (hcomp.sub_const (f a)).fun_sub hlin
  have hc : ContinuousOn g' (Set.Icc (0 : ℝ) 1) := by
    have hdf : ContinuousOn (fun t => fderiv ℂ f (l t)) (Set.Icc (0 : ℝ) 1) :=
      hf.fderiv.continuousOn.comp (by fun_prop) hlU
    exact (hdf.sub continuousOn_const).clm_apply continuousOn_const
  have hFTC : (∫ t in (0 : ℝ)..1, g' t) = f b - f a - fderiv ℂ f a d := by
    have hc' : ContinuousOn g' (Set.uIcc (0 : ℝ) 1) := by simpa using hc
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := g)
      (fun t ht => hd t (by simpa using ht)) hc'.intervalIntegrable
    simpa [g, l] using h
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g' t‖ ≤ C * t * ‖d‖ ^ 2 := by
    intro t ht
    have hseg : segment ℝ a (l t) ⊆ U :=
      ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) (hl ht)).trans hab
    have hv := norm_sub_le_of_analytic_segment_bound hseg hf.fderiv hC
    have hdist : ‖l t - a‖ = t * ‖d‖ := by
      simp [l, d, AffineMap.lineMap_apply_module', norm_smul, abs_of_nonneg ht.1]
    calc
      ‖g' t‖ ≤ ‖fderiv ℂ f (l t) - fderiv ℂ f a‖ * ‖d‖ :=
        (fderiv ℂ f (l t) - fderiv ℂ f a).le_opNorm d
      _ ≤ (C * ‖l t - a‖) * ‖d‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ = C * t * ‖d‖ ^ 2 := by rw [hdist]; ring
  rw [← hFTC]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, C * t * ‖d‖ ^ 2 :=
      intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Filter.Eventually.of_forall fun t ht => hb t ⟨ht.1.le, ht.2⟩)
        (by apply Continuous.intervalIntegrable; fun_prop)
    _ = C / 2 * ‖b - a‖ ^ 2 := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_id]
      norm_num
      dsimp [d]
      ring

theorem norm_taylor_remainder_le_of_coordinate_bound {n : ℕ}
    {f : ComplexSpace n → ℂ} {U : Set (ComplexSpace n)} {a b : ComplexSpace n} {Θ : ℝ}
    (hab : segment ℝ a b ⊆ U) (hf : AnalyticOnNhd ℂ f U) (hΘ : 0 ≤ Θ)
    (hbound : ∀ x ∈ U, ∀ i j,
      ‖fderiv ℂ (fderiv ℂ f) x (Pi.single i 1) (Pi.single j 1)‖ ≤ Θ) :
    ‖f b - f a - fderiv ℂ f a (b - a)‖ ≤
      (1 / 2 : ℝ) * n ^ 2 * Θ * ‖b - a‖ ^ 2 := by
  have hC : NormBoundOn (fderiv ℂ (fderiv ℂ f)) U ((n : ℝ) * ((n : ℝ) * Θ)) := by
    refine ⟨by positivity, fun x hx => ?_⟩
    apply norm_linearMap_le_of_coordinate_bound _ (by positivity)
    intro i
    exact norm_linearMap_le_of_coordinate_bound _ hΘ (hbound x hx i)
  convert norm_taylor_remainder_le hab hf hC using 1
  ring

end KamProject.Arnold1963
