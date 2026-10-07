/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSpaceTimeProduct
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingProductFamilyMixed

/-!
# Mixed-order products of space-time Sobolev families

A field in `L²(I; H²(ℝ³))` whose `H²` slices are uniformly bounded in time
multiplies `L²(I; H¹(ℝ³))` into itself, and the space-time Leibniz family is
the family of weak derivatives of the product. The slice estimate is the
mixed-order whole-space product estimate `H² × H¹ → H¹`; it integrates in time
as in the equal-order case. This is the product estimate for the nonlinear
term at the base level of `prop:lps-smoothing`.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The mixed-order space-time product estimate (`prop:lps-smoothing`): a
field `f` in `L²(I; H²(ℝ³))` whose `H²` slices have squared norm at most `K`
multiplies `g ∈ L²(I; H¹(ℝ³))` into `L²(I; H¹(ℝ³))`; the product has the
space-time Leibniz family and `‖fg‖²_{L²H¹} ≤ C K ‖g‖²_{L²H¹}`. -/
theorem lps_spaceTime_mul_family_mixed :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ} {f g : Vec3 × ℝ → ℝ}
      {Df Dg : List (Fin 3) → Vec3 × ℝ → ℝ} {K : ℝ},
      IsL2SobolevFamilyOn 2 (Set.univ : Set Vec3) (Ioo a b) f Df →
      IsL2SobolevFamilyOn 1 (Set.univ : Set Vec3) (Ioo a b) g Dg →
      (∀ᵐ t ∂(volume.restrict (Ioo a b)),
        ∑ α ∈ sobolevWords 2, ∫ x : Vec3, (Df α (x, t)) ^ 2 ≤ K) →
      IsL2SobolevFamilyOn 1 (Set.univ : Set Vec3) (Ioo a b) (fun z => f z * g z)
          (fun α => stLeibniz α Df Dg) ∧
        l2SobolevNormSqOn 1 (Set.univ : Set Vec3) (Ioo a b) (fun α => stLeibniz α Df Dg) ≤
          C * K * l2SobolevNormSqOn 1 (Set.univ : Set Vec3) (Ioo a b) Dg := by
  obtain ⟨C, hC, hslice⟩ := lps_sobolevFamily_mul_mixed
  exact ⟨C, hC, fun hf hg hK =>
    lps_spaceTime_mul_family_of_slice (by norm_num) hC hslice hf hg hK⟩

end ESS
