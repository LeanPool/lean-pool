/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEq
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed

/-!
# Calculus of vorticity test fields

The curl of a smooth compact test field commutes with time differentiation.
-/

public section

open CKN


open CKN.Foundation.Parabolic

namespace ESS

theorem vorticityTestPartial_timePartial_commute
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.timePartial
        (fun w : ParabolicPoint => vorticityTestPartial f i w) z =
      vorticityTestPartial
        (fun w : ParabolicPoint => CKN.timePartial f w) i z := by
  change CKN.timePartial
      (fun w : ParabolicPoint => CKN.spatialPartial f i w) z =
    CKN.spatialPartial (fun w : ParabolicPoint => CKN.timePartial f w) i z
  exact timePartial_spatialPartial_comm hf z i

/-- The CKN time derivative of a scalar test in product coordinates. -/
@[expose] noncomputable def vorticityTestTimePartial (f : Vec3 × ℝ → ℝ) :
    ParabolicPoint → ℝ :=
  fun z => CKN.timePartial (fun w : ParabolicPoint => f (show Vec3 × ℝ from w)) z

private theorem vorticityTestTimePartial_sub
    {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : ParabolicPoint) :
    vorticityTestTimePartial (fun w => f w - g w) z =
      vorticityTestTimePartial f z - vorticityTestTimePartial g z := by
  let F : ℝ → ℝ := fun t => f (z.1, t)
  let G : ℝ → ℝ := fun t => g (z.1, t)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hf.comp (contDiff_const.prodMk contDiff_id)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := hg.comp (contDiff_const.prodMk contDiff_id)
  have hFd : DifferentiableAt ℝ F z.2 := (hF.differentiable (by simp)) z.2
  have hGd : DifferentiableAt ℝ G z.2 := (hG.differentiable (by simp)) z.2
  have hsub := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (fderiv_fun_sub hFd hGd)
  simpa only [vorticityTestTimePartial, CKN.timePartial, F, G, sub_apply] using hsub

/-- The time derivative of the test curl is the curl of the time derivative,
using CKN's factor-wise derivatives (manuscript `lem:vorticity-weak-eq`). -/
theorem vorticityTestCurl_timePartial
    {ψ : Vec3 × ℝ → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (z : ParabolicPoint) :
    vorticityTestTimePartial (fun w => vorticityTestCurl ψ w i) z =
      vorticityTestCurl
        (fun w => fun k => vorticityTestTimePartial (fun y => ψ y k) w) z i := by
  have hcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => ψ w k) :=
    (contDiff_apply ℝ ℝ k).comp hψ
  have hpartial (k l : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => vorticityTestPartial (fun y => ψ y k) l w) := by
    have h := CKN.spatialPartial_contDiff (hcomp k) l
    convert h using 1
    funext w
    exact vorticityTestPartial_eq_spatialPartial (fun y => ψ y k) l w
  have hderiv (k l : Fin 3) (w : ParabolicPoint) :
      vorticityTestTimePartial
        (fun y => vorticityTestPartial (fun x => ψ x k) l y) w =
      vorticityTestPartial
        (fun x => vorticityTestTimePartial (fun y => ψ y k) x) l w := by
    change CKN.timePartial
        (fun y : ParabolicPoint => vorticityTestPartial (fun x => ψ x k) l y) w =
      vorticityTestPartial
        (fun x => CKN.timePartial (fun y : ParabolicPoint => ψ y k) x) l w
    exact vorticityTestPartial_timePartial_commute (hcomp k) l w
  fin_cases i
  · change vorticityTestTimePartial
        (fun y => vorticityTestPartial (fun x => ψ x 2) 1 y -
          vorticityTestPartial (fun x => ψ x 1) 2 y) z =
      vorticityTestPartial (fun x => vorticityTestTimePartial (fun y => ψ y 2) x) 1 z -
        vorticityTestPartial (fun x => vorticityTestTimePartial (fun y => ψ y 1) x) 2 z
    rw [vorticityTestTimePartial_sub (hpartial 2 1) (hpartial 1 2), hderiv 2 1, hderiv 1 2]
  · change vorticityTestTimePartial
        (fun y => vorticityTestPartial (fun x => ψ x 0) 2 y -
          vorticityTestPartial (fun x => ψ x 2) 0 y) z =
      vorticityTestPartial (fun x => vorticityTestTimePartial (fun y => ψ y 0) x) 2 z -
        vorticityTestPartial (fun x => vorticityTestTimePartial (fun y => ψ y 2) x) 0 z
    rw [vorticityTestTimePartial_sub (hpartial 0 2) (hpartial 2 0), hderiv 0 2, hderiv 2 0]
  · change vorticityTestTimePartial
        (fun y => vorticityTestPartial (fun x => ψ x 1) 0 y -
          vorticityTestPartial (fun x => ψ x 0) 1 y) z =
      vorticityTestPartial (fun x => vorticityTestTimePartial (fun y => ψ y 1) x) 0 z -
        vorticityTestPartial (fun x => vorticityTestTimePartial (fun y => ψ y 0) x) 1 z
    rw [vorticityTestTimePartial_sub (hpartial 1 0) (hpartial 0 1), hderiv 1 0, hderiv 0 1]

end ESS
