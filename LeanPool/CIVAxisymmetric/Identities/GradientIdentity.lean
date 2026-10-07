/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import LeanPool.CIVAxisymmetric.Identities.Divergence

/-!
# The gradient-squared identity for axisymmetric fields on the meridional plane

On the meridional plane `{x₂ = 0}` away from the axis, the full Cartesian
gradient-squared `∑ᵢ ∑ⱼ (∂ⱼ vᵢ)²` splits into the meridional part `∑ᵢ ((∂₁ vᵢ)² + (∂₃ vᵢ)²)`
plus the angular contribution `(v₀² + v₁²) / r²`. This is `eq:aniso:closure:gradient`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- For an axisymmetric field on the meridional plane, off the axis, the full Cartesian
gradient-squared equals the meridional gradient-squared plus the `1/r²` angular
contribution. -/
theorem gradient_sq_meridional {v : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn v unitCylinder)
    (hv : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => v z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => v w i) j z) ^ 2 =
      ∑ i : Fin 3, ((spatialPartial (fun w => v w i) 0 z) ^ 2
          + (spatialPartial (fun w => v w i) 2 z) ^ 2)
        + ((v z 0) ^ 2 + (v z 1) ^ 2) / (z.1 0) ^ 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  -- Left-hand side: 9 terms. Split into j=0,2 (six terms, matching RHS first sum)
  -- and j=1 (three terms, rewritten via the θ-relations).
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  -- Now LHS = sum_i sum_j (∂_j v_i)² = (∂₀v₀)²+(∂₀v₁)²+(∂₀v₂)² + (∂₁v₀)²+(∂₁v₁)²+(∂₁v₂)² +
  -- (∂₂v₀)²+(∂₂v₁)²+(∂₂v₂)²
  -- RHS = sum_i ((∂₀v_i)² + (∂₂v_i)²) + (v₀²+v₁²)/r²
  -- The six terms with j=0 or j=2 cancel between LHS and RHS first sum.
  -- The three j=1 terms: apply the θ-relations.
  have h0 := spatialPartial_one_zero_meridional haxi hv hz hplane hr
  have h1 := spatialPartial_one_one_meridional haxi hv hz hplane hr
  have h2 := spatialPartial_one_two_meridional haxi hv hz hplane hr
  rw [h0, h1, h2]
  -- Now the three j=1 terms are: (-v₁/r)² + (v₀/r)² + 0² = (v₀²+v₁²)/r²
  ring

end CIV
