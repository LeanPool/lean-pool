/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorDerivative
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Support and derivative facts for compactly supported tests. -/

public section
open MeasureTheory
open CKN.Foundation.Parabolic
namespace CKN

theorem setIntegral_eq_integral_of_tsupport_subset
    {X : Type} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace X]
    {s : Set X} {f : X → ℝ} (hs : MeasurableSet s)
    (hsub : tsupport f ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  rw [← MeasureTheory.integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · simp [hx]
  · have hfx : f x = 0 := by
      by_contra hne
      have hts : x ∈ tsupport f :=
        subset_tsupport (f := f) (Function.mem_support.mpr hne)
      exact hx (hsub hts)
    simp [hx, hfx]

theorem component_contDiff {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z i) := by
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun v : Vec3 => v i) := by fun_prop
  exact hproj.comp hφ

theorem timePartial_contDiff {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from g) z) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Vec3 × ℝ) × (Vec3 × ℝ) => fderiv ℝ g p.1 p.2) :=
    hg.contDiff_fderiv_apply (by simp)
  have hcurve : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (z, ((0 : Vec3), (1 : ℝ)))) := by fun_prop
  have hc := hD.comp hcurve
  have heq : (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from g) z) =
      fun z => fderiv ℝ g z ((0 : Vec3), (1 : ℝ)) := by
    funext z
    exact timePartial_eq_joint_fderiv hg z
  rw [heq]
  exact hc

theorem spatialPartial_mul {g h : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (show ParabolicPoint → ℝ from fun w => g w * h w) i z =
      g z * spatialPartial (show ParabolicPoint → ℝ from h) i z +
        h z * spatialPartial (show ParabolicPoint → ℝ from g) i z := by
  let G : Vec3 → ℝ := fun x => g (x, z.2)
  let H : Vec3 → ℝ := fun x => h (x, z.2)
  have hEmbed : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => (x, z.2)) := by fun_prop
  have hGcont : ContDiff ℝ (⊤ : ℕ∞) G := by
    exact hg.comp hEmbed
  have hHcont : ContDiff ℝ (⊤ : ℕ∞) H := by
    exact hh.comp hEmbed
  have hGdiff : DifferentiableAt ℝ G z.1 :=
    (hGcont.differentiable (by simp)).differentiableAt
  have hHdiff : DifferentiableAt ℝ H z.1 :=
    (hHcont.differentiable (by simp)).differentiableAt
  change fderiv ℝ (G * H) z.1 (basisVec i) = _
  rw [fderiv_mul hGdiff hHdiff]
  simp only [add_apply, smul_apply]
  rfl

theorem component_hasCompactSupport {φ : Vec3 × ℝ → Vec3}
    (hφ : HasCompactSupport φ) (i : Fin 3) :
    HasCompactSupport (fun z => φ z i) := by
  apply hφ.mono'
  intro z hz
  have hts := subset_tsupport (f := fun z => φ z i) hz
  exact (tsupport_comp_subset (g := fun v : Vec3 => v i) (by simp) φ) hts

theorem spatialPartial_hasCompactSupport {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (i : Fin 3) :
    HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from g) i z) := by
  have heq : (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from g) i z) =
      fun z => fderiv ℝ g z (basisVec i, 0) := by
    funext z
    exact spatialPartial_eq_joint_fderiv hg z i
  rw [heq]
  apply hgc.mono'
  exact (subset_tsupport (f := fun z : Vec3 × ℝ =>
      fderiv ℝ g z (basisVec i, (0 : ℝ)))).trans
    (tsupport_fderiv_apply_subset ℝ (basisVec i, (0 : ℝ)))

theorem timePartial_hasCompactSupport {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from g) z) := by
  have heq : (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from g) z) =
      fun z => fderiv ℝ g z (0, 1) := by
    funext z
    exact timePartial_eq_joint_fderiv hg z
  rw [heq]
  apply hgc.mono'
  exact (subset_tsupport (f := fun z : Vec3 × ℝ =>
      fderiv ℝ g z ((0 : Vec3), (1 : ℝ)))).trans
    (tsupport_fderiv_apply_subset ℝ ((0 : Vec3), (1 : ℝ)))

end CKN
