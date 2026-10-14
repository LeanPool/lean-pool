/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry
public import LeanPool.Superdiffusion.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Theory

/-!
# Constant cube data

The constant `H¹` cube object and its value, gradient and subtraction laws are shared
by the interior Caccioppoli and zero-trace corrector routes.
-/

@[expose] public section

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant datum -/

/-- The constant function as an `H¹` function of a cube. -/
def constantDatumH1 (Q : TriadicCube d) (c : ℝ) :
    H1Function (Ch02.cubeDomain Q : Set (Vec d)) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (by
      rw [Ch02.cubeDomain_coe]
      exact isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_const : ContDiff ℝ 1 fun _ : Vec d => c)

theorem constantDatumH1_toFun (Q : TriadicCube d) (c : ℝ) :
    (constantDatumH1 Q c).toFun = fun _ => c := rfl

theorem constantDatumH1_grad (Q : TriadicCube d) (c : ℝ) :
    (constantDatumH1 Q c).grad = fun _ => (0 : Vec d) := by
  funext y
  funext i
  change (fderiv ℝ (fun _ : Vec d => c) y) (basisVec i) = 0
  rw [fderiv_fun_const]
  rfl

/-- The gradient of a constant-shifted `H¹` function. -/
theorem sub_constantDatumH1_grad (Q : TriadicCube d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ) :
    (u - constantDatumH1 Q c).grad = u.grad := by
  rw [H1Function.sub_grad, constantDatumH1_grad]
  funext y
  exact sub_zero (u.grad y)

/-- The values of a constant-shifted `H¹` function. -/
theorem sub_constantDatumH1_toFun (Q : TriadicCube d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ) :
    (u - constantDatumH1 Q c).toFun = fun y => u.toFun y - c := by
  funext y
  rw [H1Function.sub_toFun, constantDatumH1_toFun]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
