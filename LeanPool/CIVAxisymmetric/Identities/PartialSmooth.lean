/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Barrier
public import LeanPool.CIVAxisymmetric.Comparison.MollifySlice
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! ### The unit cylinder is open -/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- A `C^{n+1}` scalar has `C^n` spatial partial derivatives on the unit cylinder. -/
theorem contDiffOn_spatialPartial_of_contDiffOn {n : ℕ} {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (n + 1) (fun z : Vec3 × ℝ => g z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ n (fun z : Vec3 × ℝ => spatialPartial g i z) unitCylinder := by
  set G := fun z : Vec3 × ℝ => g z with hG
  have h_fderiv_G : ContDiffOn ℝ n (fderiv ℝ G) unitCylinder :=
    hg.fderiv_of_isOpen isOpen_unitCylinder_prod (le_refl _)
  have hG_diffOn : DifferentiableOn ℝ G unitCylinder :=
    hg.differentiableOn (by simp)
  have h_spatial_eq : ∀ z ∈ unitCylinder,
      spatialPartial g i z = (fderiv ℝ G z) (basisVec i, (0 : ℝ)) := by
    intro z hz
    dsimp [spatialPartial, G]
    have hG_diff : DifferentiableAt ℝ (fun z' : Vec3 × ℝ => g z') z :=
      hG_diffOn.differentiableAt (isOpen_unitCylinder_prod.mem_nhds hz)
    have h_affine_diff : DifferentiableAt ℝ (fun x : Vec3 => (x, z.2)) z.1 :=
      ((hasFDerivAt_id z.1).differentiableAt).prodMk ((hasFDerivAt_const z.2 z.1).differentiableAt)
    have h_comp := fderiv_comp z.1 hG_diff h_affine_diff
    have h_affine_fderiv : fderiv ℝ (fun x : Vec3 => (x, z.2)) z.1 = ContinuousLinearMap.inl ℝ
      Vec3 ℝ := by
      have h_hasFDeriv : HasFDerivAt (fun x : Vec3 => (x, z.2))
          (ContinuousLinearMap.inl ℝ Vec3 ℝ) z.1 :=
        hasFDerivAt_prodMk_left z.1 z.2
      exact h_hasFDeriv.fderiv
    calc
      (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)
          = (fderiv ℝ ((fun z' : Vec3 × ℝ => g z') ∘ (fun x : Vec3 => (x, z.2))) z.1) (basisVec
            i) := rfl
      _ = ((fderiv ℝ G (z.1, z.2)).comp (fderiv ℝ (fun x : Vec3 => (x, z.2)) z.1)) (basisVec i)
        := by
        rw [h_comp]
      _ = (fderiv ℝ G z) ((fderiv ℝ (fun x : Vec3 => (x, z.2)) z.1) (basisVec i)) := rfl
      _ = (fderiv ℝ G z) ((ContinuousLinearMap.inl ℝ Vec3 ℝ) (basisVec i)) := by rw
        [h_affine_fderiv]
      _ = (fderiv ℝ G z) (basisVec i, (0 : ℝ)) := by simp
  have h_target : ContDiffOn ℝ n (fun z : Vec3 × ℝ => (fderiv ℝ G z) (basisVec i, (0 : ℝ)))
      unitCylinder :=
    h_fderiv_G.clm_apply contDiffOn_const
  exact h_target.congr h_spatial_eq

/-- A smooth scalar has smooth spatial partial derivatives on the unit cylinder. -/
theorem contDiffOn_spatialPartial_of_smooth {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial g i z) unitCylinder := by
  set G := fun z : Vec3 × ℝ => g z with hG
  have h_fderiv_G : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ G) unitCylinder :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_unitCylinder_prod).mp hg).2
  have hG_diffOn : DifferentiableOn ℝ G unitCylinder :=
    hg.differentiableOn (by simp)
  have h_spatial_eq : ∀ z ∈ unitCylinder,
      spatialPartial g i z = (fderiv ℝ G z) (basisVec i, (0 : ℝ)) := by
    intro z hz
    dsimp [spatialPartial, G]
    have hG_diff : DifferentiableAt ℝ (fun z' : Vec3 × ℝ => g z') z :=
      hG_diffOn.differentiableAt (isOpen_unitCylinder_prod.mem_nhds hz)
    have h_affine_diff : DifferentiableAt ℝ (fun x : Vec3 => (x, z.2)) z.1 :=
      ((hasFDerivAt_id z.1).differentiableAt).prodMk ((hasFDerivAt_const z.2 z.1).differentiableAt)
    have h_comp := fderiv_comp z.1 hG_diff h_affine_diff
    have h_affine_fderiv : fderiv ℝ (fun x : Vec3 => (x, z.2)) z.1 = ContinuousLinearMap.inl ℝ
      Vec3 ℝ := by
      have h_hasFDeriv : HasFDerivAt (fun x : Vec3 => (x, z.2))
          (ContinuousLinearMap.inl ℝ Vec3 ℝ) z.1 :=
        hasFDerivAt_prodMk_left z.1 z.2
      exact h_hasFDeriv.fderiv
    calc
      (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)
          = (fderiv ℝ ((fun z' : Vec3 × ℝ => g z') ∘ (fun x : Vec3 => (x, z.2))) z.1) (basisVec
            i) := rfl
      _ = ((fderiv ℝ G (z.1, z.2)).comp (fderiv ℝ (fun x : Vec3 => (x, z.2)) z.1)) (basisVec i)
        := by
        rw [h_comp]
      _ = (fderiv ℝ G z) ((fderiv ℝ (fun x : Vec3 => (x, z.2)) z.1) (basisVec i)) := rfl
      _ = (fderiv ℝ G z) ((ContinuousLinearMap.inl ℝ Vec3 ℝ) (basisVec i)) := by rw
        [h_affine_fderiv]
      _ = (fderiv ℝ G z) (basisVec i, (0 : ℝ)) := by simp
  have h_target : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (fderiv ℝ G z) (basisVec i, (0 : ℝ))) unitCylinder :=
    h_fderiv_G.clm_apply contDiffOn_const
  exact h_target.congr h_spatial_eq

/-! ### Smoothness of the time partial derivative -/

/-- A `C^{n+1}` scalar has `C^n` time partial derivative on the unit cylinder. -/
theorem contDiffOn_timePartial_of_contDiffOn {n : ℕ} {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (n + 1) (fun z : Vec3 × ℝ => g z) unitCylinder) :
    ContDiffOn ℝ n (fun z : Vec3 × ℝ => timePartial g z) unitCylinder := by
  set G := fun z : Vec3 × ℝ => g z with hG
  have h_fderiv_G : ContDiffOn ℝ n (fderiv ℝ G) unitCylinder :=
    hg.fderiv_of_isOpen isOpen_unitCylinder_prod (le_refl _)
  have hG_diffOn : DifferentiableOn ℝ G unitCylinder :=
    hg.differentiableOn (by simp)
  have h_time_eq : ∀ z ∈ unitCylinder,
      timePartial g z = (fderiv ℝ G z) ((0 : Vec3), (1 : ℝ)) := by
    intro z hz
    dsimp [timePartial, G]
    have hG_diff : DifferentiableAt ℝ (fun z' : Vec3 × ℝ => g z') z :=
      hG_diffOn.differentiableAt (isOpen_unitCylinder_prod.mem_nhds hz)
    have h_affine_diff : DifferentiableAt ℝ (fun s : ℝ => (z.1, s)) z.2 :=
      ((hasFDerivAt_const z.1 z.2).differentiableAt).prodMk ((hasFDerivAt_id z.2).differentiableAt)
    have h_comp := fderiv_comp z.2 hG_diff h_affine_diff
    have h_affine_fderiv : fderiv ℝ (fun s : ℝ => (z.1, s)) z.2 = ContinuousLinearMap.inr ℝ Vec3
      ℝ := by
      have h_hasFDeriv : HasFDerivAt (fun s : ℝ => (z.1, s))
          (ContinuousLinearMap.inr ℝ Vec3 ℝ) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      exact h_hasFDeriv.fderiv
    calc
      (fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2) 1
          = (fderiv ℝ ((fun z' : Vec3 × ℝ => g z') ∘ (fun s : ℝ => (z.1, s))) z.2) 1 := rfl
      _ = ((fderiv ℝ G (z.1, z.2)).comp (fderiv ℝ (fun s : ℝ => (z.1, s)) z.2)) 1 := by rw [h_comp]
      _ = (fderiv ℝ G z) ((fderiv ℝ (fun s : ℝ => (z.1, s)) z.2) 1) := rfl
      _ = (fderiv ℝ G z) ((ContinuousLinearMap.inr ℝ Vec3 ℝ) 1) := by rw [h_affine_fderiv]
      _ = (fderiv ℝ G z) ((0 : Vec3), (1 : ℝ)) := by simp
  have h_target : ContDiffOn ℝ n (fun z : Vec3 × ℝ => (fderiv ℝ G z) ((0 : Vec3), (1 : ℝ)))
      unitCylinder :=
    h_fderiv_G.clm_apply contDiffOn_const
  exact h_target.congr h_time_eq

/-! ### Smoothness of components of a vector field -/

/-- A `C^n` vector field has `C^n` component functions on the unit cylinder. -/
theorem contDiffOn_componentFun {n : ℕ∞} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ n (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ n (fun z : Vec3 × ℝ => u z i) unitCylinder := by
  have h_proj : ContDiffOn ℝ n (fun v : Vec3 => v i) Set.univ :=
    (contDiff_apply ℝ ℝ i).contDiffOn
  exact h_proj.comp hu (by intro y hy; simp)

end CIV
