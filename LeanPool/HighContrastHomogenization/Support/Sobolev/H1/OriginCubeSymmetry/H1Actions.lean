/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.OriginCubeSymmetry.Geometry

/-!
# Coordinate symmetry of centered-cube H¹ functions

Constructor transport from the Apache-2.0 CoarseGraining development, pinned at
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
The original namespaces, definitions, theorem statements, and proofs are retained.
-/

public section

namespace HCPolySupport

open scoped Topology

noncomputable section

namespace H1Function

/--
Precompose an `H¹` witness on the open centered cube with a coordinate sign
flip, transporting the weak gradient by the same sign flip.
-/
@[expose]
noncomputable def signFlipOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) (i : Fin d) :
    H1Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := signFlipVecContinuousLinearEquiv i
  let hμ := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i n
  refine
    { toFun := fun x => u (T x)
      grad := fun x => signFlipVecContinuousLinearEquiv i (u.grad (T x))
      memL2 := by
        change MemL2On U (u.toFun ∘ signFlipVecContinuousLinearEquiv i)
        simpa [MemL2On, U, Function.comp] using u.memL2.comp_measurePreserving hμ
      gradMemL2 := by
        intro k
        have hcomp :
            MemL2On U ((fun x => u.grad x k) ∘ signFlipVecContinuousLinearEquiv i) := by
          simpa [MemL2On, U, Function.comp] using
            (u.gradMemL2 k).comp_measurePreserving hμ
        by_cases hki : k = i
        · simpa [U, T, signFlipVecContinuousLinearEquiv_apply,
            matVecMul_signFlipMatrix_apply, hki] using hcomp.const_mul (-1 : ℝ)
        · simpa [U, T, signFlipVecContinuousLinearEquiv_apply,
            matVecMul_signFlipMatrix_apply, hki] using hcomp.const_mul (1 : ℝ)
      hasWeakGradient := ?_ }
  intro k φ hφ hφ_supp hφ_sub
  let ψ : Vec d → ℝ := fun x => φ (T x)
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec k)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    change ContDiff ℝ (⊤ : ℕ∞) (φ ∘ signFlipVecContinuousLinearEquiv i)
    simpa [ψ, T, Function.comp] using
      (ContDiff.comp_continuousLinearMap
        (g := (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap) hφ)
  have hψ_supp : HasCompactSupport ψ := by
    change HasCompactSupport (φ ∘ signFlipVecContinuousLinearEquiv i)
    simpa [ψ, T, Function.comp] using
      hφ_supp.comp_homeomorph (signFlipVecContinuousLinearEquiv i).toHomeomorph
  have hψ_sub : tsupport ψ ⊆ U := by
    simpa [U, ψ, T] using
      tsupport_comp_signFlip_subset_openCubeSet_originCube (f := φ) i n hφ_sub
  have hweak := u.hasWeakGradient k ψ hψ_smooth hψ_supp hψ_sub
  have hleft :
      ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume =
        (if k = i then (-1 : ℝ) else 1) *
          ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ ψ x) (basisVec k)) =
          fun x => (if k = i then (-1 : ℝ) else 1) * (u x * dφ (T x)) := by
      funext x
      have hx : DifferentiableAt ℝ φ (T x) := (hφ.differentiable (by simp)) (T x)
      rw [show ψ = fun y => φ (signFlipVecContinuousLinearEquiv i y) by
        funext y
        simp [ψ, T]]
      rw [fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec (i := i) (k := k) (x := x) hx]
      simp [dφ, T]
    rw [hfun, MeasureTheory.integral_const_mul]
  have hchange_left :
      ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u (T y) * dφ y
    change ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
    simpa only [U, T, dφ, f, signFlipVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube i n f
  have hchange_right :
      ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u.grad (T y) k * φ y
    change ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume
    simpa only [U, T, f, signFlipVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube i n f
  have hmain :
      (if k = i then (-1 : ℝ) else 1) *
          ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume =
        -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    calc
      (if k = i then (-1 : ℝ) else 1) *
          ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
        = (if k = i then (-1 : ℝ) else 1) *
            ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by rw [hchange_left]
      _ = ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume := by
            symm
            exact hleft
      _ = -∫ x in U, u.grad x k * ψ x ∂MeasureTheory.volume := hweak
      _ = -∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume := by rfl
      _ = -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by rw [hchange_right]
  by_cases hki : k = i
  · simpa [U, T, dφ, signFlipVecContinuousLinearEquiv_apply,
      matVecMul_signFlipMatrix_apply, hki, MeasureTheory.integral_neg] using hmain
  · simpa [U, T, dφ, signFlipVecContinuousLinearEquiv_apply,
      matVecMul_signFlipMatrix_apply, hki] using hmain

/--
Precompose an `H¹` witness on the open centered cube with a coordinate swap,
transporting the weak gradient by the same swap.
-/
@[expose]
noncomputable def swapOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) (i j : Fin d) :
    H1Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  let hμ := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n
  refine
    { toFun := fun x => u (matVecMul (Matrix.swap ℝ i j) x)
      grad := fun x => matVecMul (Matrix.swap ℝ i j) (u.grad (matVecMul (Matrix.swap ℝ i j) x))
      memL2 := by
        change MeasureTheory.MemLp
          (fun x => u.toFun (matVecMul (Matrix.swap ℝ i j) x)) 2
          (MeasureTheory.volume.restrict U)
        convert (u.memL2.comp_measurePreserving hμ) using 1
        ext x
        simp [Function.comp, swapVecContinuousLinearEquiv_apply]
      gradMemL2 := by
        intro l
        let k : Fin d := Equiv.swap i j l
        change MeasureTheory.MemLp
          (fun x => matVecMul (Matrix.swap ℝ i j) (u.grad (matVecMul (Matrix.swap ℝ i j) x)) l) 2
          (MeasureTheory.volume.restrict U)
        convert ((u.gradMemL2 k).comp_measurePreserving hμ) using 1
        ext x
        simp [k, Function.comp, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp]
      hasWeakGradient := ?_ }
  intro l φ hφ hφ_supp hφ_sub
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  let ψ : Vec d → ℝ := fun x => φ (T x)
  let k : Fin d := Equiv.swap i j l
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec l)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    change ContDiff ℝ (⊤ : ℕ∞) (φ ∘ swapVecContinuousLinearEquiv i j)
    simpa [ψ, T, Function.comp] using
      (ContDiff.comp_continuousLinearMap
        (g := (swapVecContinuousLinearEquiv i j).toContinuousLinearMap) hφ)
  have hψ_supp : HasCompactSupport ψ := by
    change HasCompactSupport (φ ∘ swapVecContinuousLinearEquiv i j)
    simpa [ψ, T, Function.comp] using
      hφ_supp.comp_homeomorph (swapVecContinuousLinearEquiv i j).toHomeomorph
  have hψ_sub : tsupport ψ ⊆ U := by
    simpa [U, ψ, T] using
      tsupport_comp_swap_subset_openCubeSet_originCube (f := φ) i j n hφ_sub
  have hweak := u.hasWeakGradient k ψ hψ_smooth hψ_supp hψ_sub
  have hleft :
      ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume =
        ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ ψ x) (basisVec k)) =
          fun x => u x * dφ (T x) := by
      funext x
      have hx : DifferentiableAt ℝ φ (T x) := (hφ.differentiable (by simp)) (T x)
      have hderiv :=
        fderiv_comp_swapVecContinuousLinearEquiv_apply_basisVec
          (i := i) (j := j) (k := l) (x := x) hx
      simpa [ψ, T, dφ, k] using congrArg (fun r => u x * r) hderiv
    rw [hfun]
  have hchange_left :
      ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u (T y) * dφ y
    change ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
    simpa only [U, T, dφ, f, swapVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube i j n f
  have hchange_right :
      ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u.grad (T y) k * φ y
    change ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume
    simpa only [U, T, k, f, swapVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube i j n f
  have hmain :
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume =
        -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    calc
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
        = ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by rw [hchange_left]
      _ = ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume := by
            symm
            exact hleft
      _ = -∫ x in U, u.grad x k * ψ x ∂MeasureTheory.volume := hweak
      _ = -∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume := by rfl
      _ = -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by rw [hchange_right]
  simpa [U, T, dφ, k, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp] using hmain

end H1Function

end

end HCPolySupport
