/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.OriginCubeSymmetry.H1Actions

/-!
# Coordinate symmetry of centered-cube H¹₀ functions

Constructor transport from the Apache-2.0 CoarseGraining development, pinned at
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
The original namespaces, definitions, theorem statements, and proofs are retained.
-/

public section

namespace HCPolySupport

open scoped Topology

noncomputable section

namespace H10Function

/--
Precompose an `H¹₀` witness on the open centered cube with a coordinate sign
flip.
-/
@[expose]
noncomputable def signFlipOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i : Fin d) :
    H10Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := signFlipVecContinuousLinearEquiv i
  let hμ := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i n
  refine
    { toH1Function := u.toH1Function.signFlipOnOpenCubeSetOriginCube i
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        change ContDiff ℝ (⊤ : ℕ∞) (u.approx m ∘ signFlipVecContinuousLinearEquiv i)
        simpa [T, Function.comp] using
          (ContDiff.comp_continuousLinearMap
            (g := (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap)
            (u.approx_smooth m))
      approx_hasCompactSupport := by
        intro m
        change HasCompactSupport (u.approx m ∘ signFlipVecContinuousLinearEquiv i)
        simpa [T, Function.comp] using
          (u.approx_hasCompactSupport m).comp_homeomorph
            (signFlipVecContinuousLinearEquiv i).toHomeomorph
      approx_support_subset := by
        intro m
        simpa [U, T] using
          tsupport_comp_signFlip_subset_openCubeSet_originCube
            (f := u.approx m) i n (u.approx_support_subset m)
      tendsto_approx := by
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  u.approx m (T x) -
                    (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).toFun x)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => u.approx m x - u.toH1Function.toFun x)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x => u.approx m x - u.toH1Function.toFun x
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact (u.approx_smooth m).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable
          have hfun :
              (fun x =>
                u.approx m (T x) -
                  (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).toFun x) =
                g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.signFlipOnOpenCubeSetOriginCube,
              signFlipVecContinuousLinearEquiv_apply]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx
      tendsto_approx_grad := by
        intro k
        by_cases hki : k = i
        · have hEq :
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                      (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k)
                  2 (MeasureTheory.volume.restrict U)) =
                (fun m =>
                  MeasureTheory.eLpNorm
                    (fun x =>
                      -((fderiv ℝ (u.approx m) x) (basisVec k) -
                        u.toH1Function.grad x k))
                    2 (MeasureTheory.volume.restrict U)) := by
            funext m
            let g : Vec d → ℝ := fun x =>
              -((fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
            have hg :
                MeasureTheory.AEStronglyMeasurable g
                  (MeasureTheory.volume.restrict U) := by
              exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
                continuous_const |>.aestronglyMeasurable.sub
                  (u.toH1Function.gradMemL2 k).aestronglyMeasurable |>.neg
            have hfun :
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                    (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k) =
                g ∘ T := by
              funext x
              have hx : DifferentiableAt ℝ (u.approx m) (T x) :=
                (u.approx_smooth m).differentiable (by simp) (T x)
              rw [fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec
                (i := i) (k := k) (x := x) hx]
              simp [g, T, hki, H1Function.signFlipOnOpenCubeSetOriginCube,
                signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply]
              ring
            rw [hfun]
            simpa [g, T, Function.comp] using
              (MeasureTheory.eLpNorm_comp_measurePreserving
                (g := g) (p := (2 : ENNReal)) hg hμ)
          rw [hEq]
          have hEqNeg :
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    -((fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k))
                  2 (MeasureTheory.volume.restrict U)) =
                (fun m =>
                  MeasureTheory.eLpNorm
                    (fun x =>
                      (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                    2 (MeasureTheory.volume.restrict U)) := by
            funext m
            have hfun :
                (fun x =>
                  -((fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)) =
                (-1 : ℝ) •
                  (fun x =>
                    (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k) := by
              funext x
              simp
            rw [hfun, MeasureTheory.eLpNorm_const_smul]
            norm_num
          rw [hEqNeg]
          exact u.tendsto_approx_grad k
        · have hEq :
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                      (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k)
                  2 (MeasureTheory.volume.restrict U)) =
                (fun m =>
                  MeasureTheory.eLpNorm
                    (fun x =>
                      (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                    2 (MeasureTheory.volume.restrict U)) := by
            funext m
            let g : Vec d → ℝ := fun x =>
              (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k
            have hg :
                MeasureTheory.AEStronglyMeasurable g
                  (MeasureTheory.volume.restrict U) := by
              exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
                continuous_const |>.aestronglyMeasurable.sub
                  (u.toH1Function.gradMemL2 k).aestronglyMeasurable
            have hfun :
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                    (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k) =
                g ∘ T := by
              funext x
              have hx : DifferentiableAt ℝ (u.approx m) (T x) :=
                (u.approx_smooth m).differentiable (by simp) (T x)
              rw [fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec
                (i := i) (k := k) (x := x) hx]
              simp [g, T, hki, H1Function.signFlipOnOpenCubeSetOriginCube,
                signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply]
            rw [hfun]
            simpa [g, T, Function.comp] using
              (MeasureTheory.eLpNorm_comp_measurePreserving
                (g := g) (p := (2 : ENNReal)) hg hμ)
          rw [hEq]
          exact u.tendsto_approx_grad k }

@[simp] theorem signFlipOnOpenCubeSetOriginCube_toH1Function {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i : Fin d) :
    (u.signFlipOnOpenCubeSetOriginCube i).toH1Function =
      u.toH1Function.signFlipOnOpenCubeSetOriginCube i :=
  rfl

/--
Precompose an `H¹₀` witness on the open centered cube with a coordinate swap.
-/
@[expose]
noncomputable def swapOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i j : Fin d) :
    H10Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  let hμ := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n
  refine
    { toH1Function := u.toH1Function.swapOnOpenCubeSetOriginCube i j
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        change ContDiff ℝ (⊤ : ℕ∞) (u.approx m ∘ swapVecContinuousLinearEquiv i j)
        simpa [T, Function.comp] using
          (ContDiff.comp_continuousLinearMap
            (g := (swapVecContinuousLinearEquiv i j).toContinuousLinearMap)
            (u.approx_smooth m))
      approx_hasCompactSupport := by
        intro m
        change HasCompactSupport (u.approx m ∘ swapVecContinuousLinearEquiv i j)
        simpa [T, Function.comp] using
          (u.approx_hasCompactSupport m).comp_homeomorph
            (swapVecContinuousLinearEquiv i j).toHomeomorph
      approx_support_subset := by
        intro m
        simpa [U, T] using
          tsupport_comp_swap_subset_openCubeSet_originCube
            (f := u.approx m) i j n (u.approx_support_subset m)
      tendsto_approx := by
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  u.approx m (T x) -
                    (u.toH1Function.swapOnOpenCubeSetOriginCube i j).toFun x)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => u.approx m x - u.toH1Function.toFun x)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x => u.approx m x - u.toH1Function.toFun x
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact (u.approx_smooth m).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable
          have hfun :
              (fun x =>
                u.approx m (T x) -
                  (u.toH1Function.swapOnOpenCubeSetOriginCube i j).toFun x) =
                g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.swapOnOpenCubeSetOriginCube,
              swapVecContinuousLinearEquiv_apply]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx
      tendsto_approx_grad := by
        intro l
        let k : Fin d := Equiv.swap i j l
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec l) -
                    (u.toH1Function.swapOnOpenCubeSetOriginCube i j).grad x l)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x =>
            (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.aestronglyMeasurable.sub
                (u.toH1Function.gradMemL2 k).aestronglyMeasurable
          have hfun :
              (fun x =>
                (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec l) -
                  (u.toH1Function.swapOnOpenCubeSetOriginCube i j).grad x l) =
              g ∘ T := by
            funext x
            have hx : DifferentiableAt ℝ (u.approx m) (T x) :=
              (u.approx_smooth m).differentiable (by simp) (T x)
            rw [show basisVec l = basisVec (Equiv.swap i j k) by
              simp [k]]
            rw [fderiv_comp_swapVecContinuousLinearEquiv_apply_basisVec
              (i := i) (j := j) (k := k) (x := x) hx]
            simp [g, T, k, H1Function.swapOnOpenCubeSetOriginCube,
              swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        simpa [k] using u.tendsto_approx_grad k }

@[simp] theorem swapOnOpenCubeSetOriginCube_toH1Function {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i j : Fin d) :
    (u.swapOnOpenCubeSetOriginCube i j).toH1Function =
      u.toH1Function.swapOnOpenCubeSetOriginCube i j :=
  rfl

end H10Function

end

end HCPolySupport
