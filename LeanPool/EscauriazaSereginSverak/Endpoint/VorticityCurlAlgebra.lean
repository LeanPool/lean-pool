/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityDefinitions

/-!
# Vorticity components from a gradient field

The weak vorticity of a gradient field and its antisymmetric matrix. The antisymmetric part
`∂ᵢ uₖ - ∂ₖ uᵢ` of the gradient is a signed vorticity component; this is the curl input of the
div–curl recovery in `thm:vorticity-regularity`.
-/

public section

open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The vorticity of a space-time gradient field `G i j = ∂ⱼ uᵢ`. -/
@[expose] def vorticityCurl (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (l : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  weakVorticity (fun z i j => G i j z) z l

/-- The antisymmetric matrix of a vector: `vorticityAntisym v i k = ∑ₗ εᵢₖₗ vₗ`. -/
@[expose] def vorticityAntisym (v : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, v 2, -v 1], ![-v 2, 0, v 0], ![v 1, -v 0, 0]]

/-- The coefficients of the antisymmetric matrix. -/
@[expose] def vorticityEps (i k l : Fin 3) : ℝ :=
  vorticityAntisym (fun m => if m = l then 1 else 0) i k

/-- The antisymmetric matrix of the vorticity is the antisymmetric part of the gradient. -/
theorem vorticityAntisym_curl (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (z : Vec3 × ℝ)
    (i k : Fin 3) :
    vorticityAntisym (fun l => vorticityCurl G l z) i k = G k i z - G i k z := by
  have h0 : vorticityCurl G 0 z = G 2 1 z - G 1 2 z := rfl
  have h1 : vorticityCurl G 1 z = G 0 2 z - G 2 0 z := rfl
  have h2 : vorticityCurl G 2 z = G 1 0 z - G 0 1 z := rfl
  fin_cases i <;> fin_cases k <;> simp [vorticityAntisym, h0, h1, h2]

/-- The antisymmetric matrix is linear in the vector. -/
theorem vorticityAntisym_eq_sum (v : Fin 3 → ℝ) (i k : Fin 3) :
    vorticityAntisym v i k = ∑ l : Fin 3, vorticityEps i k l * v l := by
  fin_cases i <;> fin_cases k <;>
    simp [vorticityAntisym, vorticityEps]

/-- The squared entries of the antisymmetric matrix are bounded by twice the squared norm. -/
theorem vorticityAntisym_sq_sum_le (v : Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ k : Fin 3, vorticityAntisym v i k ^ 2 ≤ 2 * ∑ l : Fin 3, v l ^ 2 := by
  simp only [vorticityAntisym, Fin.sum_univ_three]
  simp
  nlinarith only [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

/-- The squared vorticity is bounded by four times the squared gradient. -/
theorem vorticityCurl_sq_le (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) (l : Fin 3) :
    vorticityCurl G l z ^ 2 ≤ 2 * ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 := by
  have h0 : vorticityCurl G 0 z = G 2 1 z - G 1 2 z := rfl
  have h1 : vorticityCurl G 1 z = G 0 2 z - G 2 0 z := rfl
  have h2 : vorticityCurl G 2 z = G 1 0 z - G 0 1 z := rfl
  fin_cases l <;> simp [h0, h1, h2, Fin.sum_univ_three] <;>
    nlinarith only [sq_nonneg (G 0 0 z), sq_nonneg (G 0 1 z), sq_nonneg (G 0 2 z),
      sq_nonneg (G 1 0 z), sq_nonneg (G 1 1 z), sq_nonneg (G 1 2 z),
      sq_nonneg (G 2 0 z), sq_nonneg (G 2 1 z), sq_nonneg (G 2 2 z),
      sq_nonneg (G 2 1 z + G 1 2 z), sq_nonneg (G 0 2 z + G 2 0 z),
      sq_nonneg (G 1 0 z + G 0 1 z)]

end ESS
