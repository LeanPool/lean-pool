/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevGlobalL6
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMollified
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Sobolev control of the regularized transport field

The H¹ Sobolev estimate is stated for a vector field and its specified
gradient. It will be applied to the mollified transport field in the regularized
H¹ energy estimate.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The `L⁶` norm of an `H¹(ℝ³)` function is bounded by the Gagliardo–Nirenberg–Sobolev constant
times the `L²` norm of its gradient (`lem:lps-H1-estimate`). -/
theorem lps_h1_component_six
    (g : H1Function (Set.univ : Set Vec3)) :
    eLpNorm g.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant *
        eLpNorm (fun x => vec3EuclideanNorm (g.grad x)) 2 volume := by
  have hgradFun (j : Fin 3) : MemLp (fun x => g.grad x j) 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn] using g.gradMemL2 j
  have hgrad : MemLp g.grad 2 volume := (memLp_pi_iff).2 hgradFun
  have hgradLe : eLpNorm g.grad 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (g.grad x)) 2 volume := by
    rw [← eLpNorm_norm g.grad hgrad.aestronglyMeasurable]
    apply eLpNorm_mono_ae_real (hgrad.aestronglyMeasurable.norm)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm (g.grad x)
  have hglobal := (Classical.choose_spec CKN.sobolev_L6_global).2 g
  have hglobal' : eLpNorm g.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant * eLpNorm g.grad 2 volume := by
    simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
      CKN.weakGradientLpNormOn, Measure.restrict_univ] using hglobal
  exact hglobal'.trans (mul_le_mul_of_nonneg_left hgradLe (by positivity))

/-- Componentwise whole-space Sobolev control for a vector field whose
components are represented by the supplied `H¹` functions. -/
theorem lps_regularised_h1_vector_six_bound
    {w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3}
    (hw2 : MemLp w 2 volume) (hDw2 : MemLp Dw 2 volume)
    (hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x => w x i) ∧
      h.grad = (fun x j => Dw x i j)) :
    eLpNorm w 6 volume ≤
      (6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
  let Wsum : Vec3 → ℝ := fun x => ∑ i : Fin 3, |w x i|
  have hWsumNonneg (x : Vec3) : 0 ≤ Wsum x := by
    dsimp [Wsum]
    positivity
  have hpoint (x : Vec3) : ‖w x‖ ≤ Wsum x := by
    apply (pi_norm_le_iff_of_nonneg (hWsumNonneg x)).2
    intro i
    dsimp [Wsum]
    calc
      ‖w x i‖ = |w x i| := Real.norm_eq_abs _
      _ ≤ ∑ j : Fin 3, |w x j| :=
        Finset.single_le_sum (f := fun j : Fin 3 => |w x j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hvector : eLpNorm w 6 volume ≤ eLpNorm Wsum 6 volume :=
    eLpNorm_mono_ae_real hw2.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hsumEq : Wsum = ∑ i : Fin 3, (fun x : Vec3 => |w x i|) := by
    funext x
    rfl
  have hsum : eLpNorm Wsum 6 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => |w x i|) 6 volume := by
    rw [hsumEq]
    exact eLpNorm_sum_le (p := (6 : ℝ≥0∞)) (s := Finset.univ)
      (f := fun i => fun x : Vec3 => |w x i|) (by norm_num)
  have hcomp (i : Fin 3) :
      eLpNorm (fun x => |w x i|) 6 volume ≤
        2 * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
    rcases hH1 i with ⟨g, hFun, hGrad⟩
    have hcoord : AEStronglyMeasurable (fun x => w x i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        hw2.aestronglyMeasurable
    have habs : eLpNorm (fun x => |w x i|) 6 volume =
        eLpNorm (fun x => w x i) 6 volume := by
      rw [← eLpNorm_norm (fun x => w x i) hcoord]
      exact eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs])
    rw [habs, ← hFun]
    calc
      eLpNorm g.toFun 6 volume ≤
          gagliardoNirenbergSobolevConstant *
            eLpNorm (fun x => vec3EuclideanNorm (g.grad x)) 2 volume :=
        lps_h1_component_six g
      _ ≤ 2 * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
        have hrowMem : MemLp (fun x => g.grad x) 2 volume := by
          apply memLp_pi_iff.mpr
          intro j
          simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
            Measure.restrict_univ] using g.gradMemL2 j
        have hrowPoint (x : Vec3) :
            vec3EuclideanNorm (g.grad x) ≤ 2 * ‖Dw x‖ := by
          rw [hGrad]
          have hrow : ‖(fun j => Dw x i j : Vec3)‖ ≤ ‖Dw x‖ :=
            norm_le_pi_norm (Dw x) i
          have hsqrt : Real.sqrt 3 ≤ 2 := by
            nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
              Real.sqrt_nonneg 3]
          calc
            vec3EuclideanNorm (fun j => Dw x i j) ≤
                Real.sqrt 3 * ‖(fun j => Dw x i j : Vec3)‖ :=
              vec3EuclideanNorm_le_sqrt_three_mul_norm _
            _ ≤ Real.sqrt 3 * ‖Dw x‖ :=
              mul_le_mul_of_nonneg_left hrow (Real.sqrt_nonneg 3)
            _ ≤ 2 * ‖Dw x‖ :=
              mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
        have hrowMeas : AEStronglyMeasurable
            (fun x => vec3EuclideanNorm (g.grad x)) volume :=
          continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
            hrowMem.aestronglyMeasurable
        have hrowPoint' (x : Vec3) :
            ‖vec3EuclideanNorm (g.grad x)‖ ≤ 2 * ‖‖Dw x‖‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
            Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hrowPoint x
        have hscaled := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hrowMeas
          (Filter.Eventually.of_forall hrowPoint') (2 : ℝ≥0∞)
        have hrowLe : eLpNorm (fun x => vec3EuclideanNorm (g.grad x)) 2 volume ≤
            2 * eLpNorm Dw 2 volume := by
          have hDwNorm : eLpNorm (fun x => ‖Dw x‖) 2 volume =
              eLpNorm Dw 2 volume := eLpNorm_norm Dw hDw2.aestronglyMeasurable
          rw [hDwNorm] at hscaled
          norm_num at hscaled ⊢
          exact hscaled
        calc
          gagliardoNirenbergSobolevConstant *
              eLpNorm (fun x => vec3EuclideanNorm (g.grad x)) 2 volume ≤
            gagliardoNirenbergSobolevConstant * (2 * eLpNorm Dw 2 volume) :=
              mul_le_mul_of_nonneg_left hrowLe (by positivity)
          _ = 2 * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
              ring
  calc
    eLpNorm w 6 volume ≤ eLpNorm Wsum 6 volume := hvector
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => |w x i|) 6 volume := hsum
    _ ≤ ∑ _i : Fin 3,
        2 * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume :=
      Finset.sum_le_sum fun i _ => hcomp i
    _ = (6 : ℝ≥0∞) * gagliardoNirenbergSobolevConstant * eLpNorm Dw 2 volume := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- Convolution does not increase the vector `L⁶` norm beyond a fixed
coordinate factor. The factor is independent of the regularization scale. -/
theorem lps_regMollified_velocity_l6_bound
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {u : Vec3 → Vec3} (hu2 : MemLp u 2 volume)
    (hu6 : MemLp u 6 volume) :
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm
      (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x)) 6 volume ≤
      9 * eLpNorm u 6 volume := by
  have hcomponent (i : Fin 3) :
      eLpNorm (fun x : Vec3 =>
        (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i) 6 volume ≤
        ∑ j : Fin 3, eLpNorm (fun x : Vec3 => u x j) 6 volume := by
    change eLpNorm (fun x : Vec3 =>
        (WithLp.ofLp (CKN.Leray.regMollifyVector ρ ε hε
          (CKN.Leray.regUniformSpatialField u) (WithLp.toLp 2 x))) i)
        6 volume ≤ _
    exact CKN.Leray.regMollifyVector_component_eLpNorm_le_sum
      ρ ε hε (by norm_num) (by norm_num) hu2
      (fun j => hu6.eval j) i
  have hcoord (i : Fin 3) :
      eLpNorm (fun x : Vec3 => u x i) 6 volume ≤ eLpNorm u 6 volume := by
    have hmeas : AEStronglyMeasurable (fun x : Vec3 => u x i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        hu6.aestronglyMeasurable
    rw [← eLpNorm_norm (fun x : Vec3 => u x i) hmeas,
      ← eLpNorm_norm u hu6.aestronglyMeasurable]
    apply eLpNorm_mono_ae_real hmeas.norm
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_abs] using
      (norm_le_pi_norm (u x) i)
  have hcomponentBound (i : Fin 3) :
      eLpNorm (fun x : Vec3 =>
        (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i) 6 volume ≤
        3 * eLpNorm u 6 volume := by
    calc
      _ ≤ ∑ j : Fin 3, eLpNorm (fun x : Vec3 => u x j) 6 volume :=
        hcomponent i
      _ ≤ ∑ _j : Fin 3, eLpNorm u 6 volume :=
        Finset.sum_le_sum fun j _ => hcoord j
      _ = 3 * eLpNorm u 6 volume := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have houtComp : ∀ i : Fin 3,
      MemLp (fun x : Vec3 =>
        (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i) 6 volume := by
    intro i
    rw [memLp_iff]
    have h6Top : eLpNorm u 6 volume < ⊤ :=
      lt_top_iff_ne_top.mpr hu6.eLpNorm_ne_top
    have hfinite : (3 : ℝ≥0∞) * eLpNorm u 6 volume < ⊤ :=
      ENNReal.mul_lt_top (by norm_num) h6Top
    exact lt_of_le_of_lt (hcomponentBound i) hfinite
  have hout : MemLp (CKN.Leray.regUniformMollifiedInitial ρ ε hε u) 6 volume :=
    memLp_pi_iff.mpr houtComp
  have hsumNorm (x : Vec3) :
      vec3EuclideanNorm (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) ≤
        ∑ i : Fin 3, |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i| :=
    vec3EuclideanNorm_le_sum_abs _
  have hsum : eLpNorm
      (fun x : Vec3 => ∑ i : Fin 3,
        |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i|) 6 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x : Vec3 =>
        |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i|) 6 volume :=
    eLpNorm_sum_le (p := (6 : ℝ≥0∞)) (s := Finset.univ)
      (f := fun i => fun x : Vec3 =>
        |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i|) (by norm_num)
  have habs (i : Fin 3) : eLpNorm (fun x : Vec3 =>
      |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i|) 6 volume =
      eLpNorm (fun x : Vec3 =>
        (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i) 6 volume := by
    rw [← eLpNorm_norm _ (houtComp i).aestronglyMeasurable]
    exact eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [Real.norm_eq_abs])
  have hvec : eLpNorm (fun x : Vec3 =>
      vec3EuclideanNorm (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x))
      6 volume ≤ eLpNorm
        (fun x : Vec3 => ∑ i : Fin 3,
          |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i|) 6 volume := by
    have hmeas := continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hout.aestronglyMeasurable
    apply eLpNorm_mono_ae_real hmeas
    filter_upwards [] with x
    have hsumNonneg : 0 ≤ ∑ i : Fin 3,
        |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      abs_of_nonneg hsumNonneg] using hsumNorm x
  calc
    _ ≤ eLpNorm (fun x : Vec3 => ∑ i : Fin 3,
        |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i|) 6 volume := hvec
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x : Vec3 =>
        |(CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i|) 6 volume := hsum
    _ = ∑ i : Fin 3, eLpNorm (fun x : Vec3 =>
        (CKN.Leray.regUniformMollifiedInitial ρ ε hε u x) i) 6 volume := by
        exact Finset.sum_congr rfl fun i _ => habs i
    _ ≤ ∑ _i : Fin 3, 3 * eLpNorm u 6 volume :=
        Finset.sum_le_sum fun i _ => hcomponentBound i
    _ = 9 * eLpNorm u 6 volume := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end ESS.LPS

end
