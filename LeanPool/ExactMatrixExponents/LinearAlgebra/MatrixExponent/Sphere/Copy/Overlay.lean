/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Ballot
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Weight

/-! # Navigation is preserved by a local copying path -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local

variable {e k : ℕ} (a : Design)

open scoped Classical in
theorem path_nav (r : (a.port e).obj) (i : ℕ) (x : Fin i → (a.selectors k).obj) (j : B a.m) :
    (a.path r i x j).1 = (r j).1 := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih (Fin.init x)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Copy
end
