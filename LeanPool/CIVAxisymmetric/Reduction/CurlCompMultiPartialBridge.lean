/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.CartesianVorticityEquation
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialOrderShift

/-!
# Bridge from `curlComp` to `multiPartial` language

extends `CIV.curlComp`'s definition (built from CKN's `spatialPartial`) with the smoothness
transfer, time-slice restriction, and one-derivative `multiPartial`-language translation that every
consumer of the genuine vorticity field `ω := CIV.curlComp u` needs, the missing static
(non-PDE) half of the bridge from the Cartesian curl to the `multiPartial` language used
throughout the induction on derivative order behind `thm:analytic:interior` (Kahane 1969,
Theorem 1.2).
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem contDiffOn_curlComp_public {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => curlComp u i z) unitCylinder := by
  unfold curlComp
  exact (contDiffOn_spatialPartial (contDiffOn_component hu (i + 2)) (i + 1)).sub
    (contDiffOn_spatialPartial (contDiffOn_component hu (i + 1)) (i + 2))

theorem contDiffOn_curlComp_slice_public {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3) (s : ℝ)
    (hs : s ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => curlComp u i (x, s)) (vec3Ball 0 1) :=
  contDiffOn_spatialSlice (contDiffOn_curlComp_public hu i) hs

theorem axisDeriv_curlComp_eq_multiPartial {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) (i k : Fin 3) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) {x : Vec3} (hx : x ∈ vec3Ball 0 1) :
    axisDeriv k (fun y : Vec3 => curlComp u i (y, t)) x
      = multiPartial (fun w => u w (i + 2)) (Pi.single (i + 1) 1 + Pi.single k 1) (x, t)
        - multiPartial (fun w => u w (i + 1)) (Pi.single (i + 2) 1 + Pi.single k 1) (x, t) := by
  have hUo : IsOpen (vec3Ball (0 : Vec3) 1) := isOpen_vec3Ball 0 1
  unfold curlComp
  have h_diff1 : DifferentiableAt ℝ
      (fun y : Vec3 => spatialPartial (fun w => u w (i + 2)) (i + 1) (y, t)) x := by
    have h_spatial : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => spatialPartial (fun w => u w (i + 2)) (i + 1) z) unitCylinder :=
      contDiffOn_spatialPartial (contDiffOn_component hu (i + 2)) (i + 1)
    have h_slice : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => spatialPartial (fun w => u w (i + 2)) (i + 1) (y, t))
        (vec3Ball (0 : Vec3) 1) :=
      contDiffOn_spatialSlice h_spatial ht
    exact (h_slice.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hx)
  have h_diff2 : DifferentiableAt ℝ
      (fun y : Vec3 => spatialPartial (fun w => u w (i + 1)) (i + 2) (y, t)) x := by
    have h_spatial : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => spatialPartial (fun w => u w (i + 1)) (i + 2) z) unitCylinder :=
      contDiffOn_spatialPartial (contDiffOn_component hu (i + 1)) (i + 2)
    have h_slice : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => spatialPartial (fun w => u w (i + 1)) (i + 2) (y, t))
        (vec3Ball (0 : Vec3) 1) :=
      contDiffOn_spatialSlice h_spatial ht
    exact (h_slice.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hx)
  have h_sub : axisDeriv k (fun y : Vec3 =>
      spatialPartial (fun w => u w (i + 2)) (i + 1) (y, t)
      - spatialPartial (fun w => u w (i + 1)) (i + 2) (y, t)) x
      = axisDeriv k (fun y : Vec3 => spatialPartial (fun w => u w (i + 2)) (i + 1) (y, t)) x
        - axisDeriv k (fun y : Vec3 => spatialPartial (fun w => u w (i + 1)) (i + 2) (y, t)) x := by
    unfold axisDeriv
    rw [fderiv_fun_sub h_diff1 h_diff2]
    simp
  rw [h_sub]
  have h_rewrite1 : axisDeriv k (fun y : Vec3 => spatialPartial (fun w => u w (i + 2)) (i + 1)
    (y, t)) x
      = axisDeriv k (fun y : Vec3 =>
          multiPartial (fun w => u w (i + 2)) (Pi.single (i + 1) 1) (y, t)) x := by
    refine congrArg (fun f => axisDeriv k f x) (funext fun y => ?_)
    set G : Vec3 → ℝ := fun y' => (fun w => u w (i + 2)) (y', t)
    have h_spatial : spatialPartial (fun w => u w (i + 2)) (i + 1) (y, t) = axisDeriv (i + 1) G
      y := by
      have h_iter := slice_spatialPartial_iterate (fun w => u w (i + 2)) (i + 1) 1 t
      rw [Function.iterate_one] at h_iter
      exact congr_fun h_iter y
    have h_multi : multiPartial (fun w => u w (i + 2)) (Pi.single (i + 1) 1) (y, t) = axisDeriv
      (i + 1) G y := by
      have h_slice := multiPartial_slice (fun w => u w (i + 2)) (Pi.single (i + 1) 1) t
      have h_eq := congr_fun h_slice y
      fin_cases i <;> simpa [G] using h_eq
    rw [h_multi, h_spatial]
  have h_rewrite2 : axisDeriv k (fun y : Vec3 => spatialPartial (fun w => u w (i + 1)) (i + 2)
    (y, t)) x
      = axisDeriv k (fun y : Vec3 =>
          multiPartial (fun w => u w (i + 1)) (Pi.single (i + 2) 1) (y, t)) x := by
    refine congrArg (fun f => axisDeriv k f x) (funext fun y => ?_)
    set G : Vec3 → ℝ := fun y' => (fun w => u w (i + 1)) (y', t)
    have h_spatial : spatialPartial (fun w => u w (i + 1)) (i + 2) (y, t) = axisDeriv (i + 2) G
      y := by
      have h_iter := slice_spatialPartial_iterate (fun w => u w (i + 1)) (i + 2) 1 t
      rw [Function.iterate_one] at h_iter
      exact congr_fun h_iter y
    have h_multi : multiPartial (fun w => u w (i + 1)) (Pi.single (i + 2) 1) (y, t) = axisDeriv
      (i + 2) G y := by
      have h_slice := multiPartial_slice (fun w => u w (i + 1)) (Pi.single (i + 2) 1) t
      have h_eq := congr_fun h_slice y
      fin_cases i <;> simpa [G] using h_eq
    rw [h_multi, h_spatial]
  rw [h_rewrite1, h_rewrite2]
  have hG1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x' : Vec3 => (fun w => u w (i + 2)) (x', t))
      (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_pi.1 (contDiffOn_spatialSlice hu ht) (i + 2)
  have hG2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x' : Vec3 => (fun w => u w (i + 1)) (x', t))
      (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_pi.1 (contDiffOn_spatialSlice hu ht) (i + 1)
  rw [axisDeriv_multiPartial_slice_eq hUo t hG1 (Pi.single (i + 1) 1) k hx,
    axisDeriv_multiPartial_slice_eq hUo t hG2 (Pi.single (i + 2) 1) k hx]

end CIV
