/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Extension.C1Test
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


/-!
# Shear of a `C¹` boundary chart

A bounded domain with `C¹` boundary is, near a boundary point and after relabelling the
coordinates, the region above the graph of a `C¹` function `γ` of the remaining coordinates.
The map that flattens the boundary is the shear `y ↦ y + γ(y) • eⱼ`, whose inverse is the shear
by `-γ`, and whose derivative is the identity plus a rank-one map that annihilates its own
direction. Its determinant is therefore `1`, so it preserves Lebesgue measure and the change of
variables leaves every integral unchanged.

## Main declarations

* `EllipticPdes.Extension.shear`: the map.
* `EllipticPdes.Extension.shear_shear_neg`: the shear by `-γ` inverts it.
* `EllipticPdes.Extension.det_shearDeriv`: the derivative has determinant `1`.
* `EllipticPdes.Extension.integral_comp_shear`: the change of variables.
* `EllipticPdes.Extension.shearHomeomorph`: the shear as a homeomorphism of the whole space.
* `EllipticPdes.Extension.measurePreserving_shear`: the shear preserves Lebesgue measure.
* `EllipticPdes.Extension.partialD_comp_shear`: the chain rule through a shear.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4, and §C.1 for the boundary chart.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Shear of a boundary chart.** The point `y` moves along the `j`-th axis by `γ y`. -/
def shear (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  y + γ y • EuclideanSpace.single j (1 : ℝ)

/-- `γ` does not depend on the `j`-th coordinate, which is what makes the shear invertible by a
shear and its derivative nilpotent. -/
def IndepCoord (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), γ (y + t • EuclideanSpace.single j (1 : ℝ)) = γ y

/-- **Inversion of the shear by `γ`.** -/
theorem shear_shear_neg {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j (fun z => -γ z) (shear j γ y) = y := by
  simp only [shear, hind y (γ y)]
  module

/-- **Inversion of the shear by `-γ`.** -/
theorem shear_neg_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ)
    (y : EuclideanSpace ℝ (Fin d)) : shear j γ (shear j (fun z => -γ z) y) = y := by
  simp only [shear]
  rw [hind y (-γ y)]
  module

/-- The shear is a bijection of the whole space. -/
theorem bijective_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ) :
    Function.Bijective (shear j γ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shear j (fun z => -γ z), shear_shear_neg hind, shear_neg_shear hind⟩

/-- **Vanishing `j`-th partial of a function independent of that coordinate.** -/
theorem partialD_eq_zero_of_indepCoord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ γ y (EuclideanSpace.single j (1 : ℝ)) = 0 := by
  have h1 : HasLineDerivAt ℝ γ (fderiv ℝ γ y (EuclideanSpace.single j (1 : ℝ))) y
      (EuclideanSpace.single j (1 : ℝ)) :=
    (hγ y).hasFDerivAt.hasLineDerivAt _
  have h0 : HasLineDerivAt ℝ γ 0 y (EuclideanSpace.single j (1 : ℝ)) := by
    change HasDerivAt (fun t : ℝ => γ (y + t • EuclideanSpace.single j (1 : ℝ))) 0 0
    have hconst : (fun t : ℝ => γ (y + t • EuclideanSpace.single j (1 : ℝ))) = fun _ => γ y :=
      funext (hind y)
    rw [hconst]
    exact hasDerivAt_const 0 (γ y)
  exact h1.unique h0

/-- The derivative of the shear: the identity plus a rank-one map in the direction `eⱼ`. -/
def shearDeriv (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
    + (fderiv ℝ γ y).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- **Derivative of the shear.** -/
theorem hasFDerivAt_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (shear j γ) (shearDeriv j γ y) y := by
  exact (hasFDerivAt_id y).add (((hγ y).hasFDerivAt).smul_const
    (EuclideanSpace.single j (1 : ℝ)))

/-- **Determinant `1` of the shear derivative.** In the standard basis the matrix is the
identity with row `j` replaced by `eⱼ + ∇γ`. Multilinearity in that row splits the determinant
into `det 1` and the determinant of the identity with row `j` replaced by `∇γ`, and the latter
reads off as the `j`-th component of `∇γ`, which vanishes. -/
theorem det_shearDeriv {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) :
    (shearDeriv j γ y).det = 1 := by
  classical
  set b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis with hb
  set c : Fin d → ℝ := fun k => fderiv ℝ γ y (b k) with hc
  have hbk : ∀ k, b k = EuclideanSpace.single k (1 : ℝ) := by
    intro k; rw [hb]; simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have hcj : c j = 0 := by
    rw [hc]
    simp only
    rw [hbk j]
    exact partialD_eq_zero_of_indepCoord hγ hind y
  have hmat : LinearMap.toMatrix b b (shearDeriv j γ y : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _)
      = Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
          ((1 : Matrix (Fin d) (Fin d) ℝ) j + c) := by
    ext i k
    rw [LinearMap.toMatrix_apply]
    simp only [hb, shearDeriv]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.updateRow_apply, Matrix.one_apply, hc, hbk]
    · rw [Matrix.updateRow_ne hij]
      simp [Matrix.one_apply, hij]
  have hdet : (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
      ((1 : Matrix (Fin d) (Fin d) ℝ) j + c)).det = 1 := by
    rw [Matrix.det_updateRow_add]
    have h1 : (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
        ((1 : Matrix (Fin d) (Fin d) ℝ) j)).det = 1 := by
      rw [Matrix.updateRow_eq_self, Matrix.det_one]
    have h2 : (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j c).det = 0 := by
      have hrow : c = ∑ k, c k • (1 : Matrix (Fin d) (Fin d) ℝ) k := by
        funext m
        simp [Matrix.one_apply, Finset.sum_apply]
      rw [hrow, Matrix.det_updateRow_sum, Matrix.det_one]
      simp [hcj]
    rw [h1, h2, add_zero]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, hmat, hdet]

/-- **Change of variables through a shear.** The Jacobian determinant is `1`, so the shear
leaves every integral unchanged. -/
theorem integral_comp_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ y, g (shear j γ y) = ∫ x, g x := by
  have hinj : Set.InjOn (shear j γ) Set.univ := (bijective_shear hind).injective.injOn
  have hfd : ∀ y ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))),
      HasFDerivWithinAt (shear j γ) (shearDeriv j γ y) Set.univ y :=
    fun y _ => (hasFDerivAt_shear hγ y).hasFDerivWithinAt
  have himg : (shear j γ) '' Set.univ = Set.univ := by
    rw [Set.image_univ, (bijective_shear hind).surjective.range_eq]
  have h := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) MeasurableSet.univ hfd
    hinj g
  rw [himg, Measure.restrict_univ] at h
  simp only [det_shearDeriv hγ hind, abs_one, one_smul] at h
  exact h.symm

/-! ### The shear as a homeomorphism, and its measure -/

/-- The shear is continuous when the chart is. -/
theorem continuous_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ) :
    Continuous (shear j γ) :=
  continuous_id.add (hγ.smul continuous_const)

/-- The shear is `C^n` when the chart is. -/
theorem contDiff_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} {n : ℕ∞}
    (hγ : ContDiff ℝ n γ) : ContDiff ℝ n (shear j γ) :=
  contDiff_id.add (hγ.smul contDiff_const)

/-- Negating a chart preserves independence of the `j`-th coordinate. -/
theorem IndepCoord.neg {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j γ) :
    IndepCoord j fun z => -γ z := by
  intro y t
  change -γ (y + t • EuclideanSpace.single j (1 : ℝ)) = -γ y
  rw [hind y t]

/-- **Shear as a homeomorphism of the whole space**, inverted by the shear by `-γ`. -/
def shearHomeomorph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : Continuous γ)
    (hind : IndepCoord j γ) : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) where
  toFun := shear j γ
  invFun := shear j fun z => -γ z
  left_inv := shear_shear_neg hind
  right_inv := shear_neg_shear hind
  continuous_toFun := continuous_shear hγ
  continuous_invFun := continuous_shear hγ.neg

/-- The shear is a measurable embedding, being a homeomorphism. -/
theorem measurableEmbedding_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Continuous γ) (hind : IndepCoord j γ) : MeasurableEmbedding (shear j γ) :=
  (shearHomeomorph hγ hind).measurableEmbedding

/-- **Preservation of Lebesgue measure by a shear.** Its inverse is the shear by `-γ`, whose
derivative has determinant `1`, so the image of a measurable set has the measure of the set. -/
theorem measurePreserving_shear {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) :
    MeasurePreserving (shear j γ) volume volume := by
  have hcont : Continuous (shear j γ) := continuous_shear hγ.continuous
  have hnegd : Differentiable ℝ fun z => -γ z := hγ.neg
  refine ⟨hcont.measurable, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hcont.measurable hs]
  have hpre : shear j γ ⁻¹' s = shear j (fun z => -γ z) '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨shear j γ x, hx, shear_shear_neg hind x⟩
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_preimage, shear_neg_shear hind y]
      exact hy
  have hfd : ∀ x ∈ s, HasFDerivWithinAt (shear j fun z => -γ z)
      (shearDeriv j (fun z => -γ z) x) s x :=
    fun x _ => (hasFDerivAt_shear hnegd x).hasFDerivWithinAt
  have hinj : Set.InjOn (shear j fun z => -γ z) s :=
    (bijective_shear hind.neg).injective.injOn
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hs hfd hinj
    (fun _ => 1)
  have hdet1 : ∀ x : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal |(shearDeriv j (fun z => -γ z) x).det| * 1 = 1 := by
    intro x
    rw [det_shearDeriv hnegd hind.neg x, abs_one, ENNReal.ofReal_one, mul_one]
  rw [hpre]
  calc volume (shear j (fun z => -γ z) '' s)
      = ∫⁻ _ in shear j (fun z => -γ z) '' s, (1 : ℝ≥0∞) := (setLIntegral_one _).symm
    _ = ∫⁻ x in s, ENNReal.ofReal |(shearDeriv j (fun z => -γ z) x).det| * 1 := h
    _ = ∫⁻ _ in s, (1 : ℝ≥0∞) := by
        simp only [hdet1]
    _ = volume s := setLIntegral_one _

/-! ### The chain rule through a shear -/

/-- **Partial derivatives through a shear.** The derivative of the shear is the identity plus a
rank-one map in the direction `eⱼ`, so a partial derivative of a composition adds to the
corresponding partial of the outer function the `j`-th one times the partial of the chart. -/
theorem partialD_comp_shear {j : Fin d} {γ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hφ : Differentiable ℝ φ) (k : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun z => φ (shear j γ z)) y
      = partialD k φ (shear j γ y) + partialD j φ (shear j γ y) * partialD k γ y := by
  have hcomp : HasFDerivAt (fun z => φ (shear j γ z))
      ((fderiv ℝ φ (shear j γ y)).comp (shearDeriv j γ y)) y :=
    (hφ (shear j γ y)).hasFDerivAt.comp y (hasFDerivAt_shear hγ y)
  rw [partialD, hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, shearDeriv,
    _root_.add_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul, partialD]
  ring

end EllipticPdes.Extension
