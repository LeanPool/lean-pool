/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.MeasurableCover
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Analysis.Hausdorff.Volume
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The codimension-one area formula for `C¹` graphs

General geometric analysis, independent of the KLS objects: the `(n-1)`-dimensional Hausdorff
measure of the graph of a `C¹` function.  Every statement here is proved and uses only the
standard axioms; the module contains no hole.

## Setting

`H` and `V` are finite-dimensional real inner-product spaces, `ι : H →ₗᵢ[ℝ] V` a linear isometry
and `e : V` a unit vector orthogonal to the range of `ι` (in the application `V` is the ambient
space, `e` a normal direction and `H` the tangent hyperplane).  For `g : H → ℝ` the *graph map* is
`graphMap ι e g y = ι y + g y • e`, and the *graph Jacobian* is
`graphJacobian a = √(1 + ‖a‖²)` evaluated at `a = ∇g y`.

## Contents

* `graphLinear ι e a : H →L[ℝ] V`, `v ↦ ι v + ⟪a, v⟫ • e`, the derivative of a graph map.
* `hausdorffMeasure_image_graphLinear`: the linear case, `ℋ^k (graphLinear ι e a '' s)
  = √(1 + ‖a‖²) · ℋ^k s`.  Proved by factoring `graphLinear ι e (r • u) = shearCLM ∘ dilate`
  into a linear isometry `H → V` and a dilation of `H` by `√(1 + r²)` along `u`, so that the
  isometry invariance of Hausdorff measure and the Haar behaviour of a linear map give the
  constant; no polar decomposition or general area formula is needed.

The linear statement is the exact codimension-one analogue of `Measure.addHaar_image_linearMap`
and is the input for the `C¹` case.  Dimension zero is included: then `H` is trivial, `a = 0` and
both sides are the unit mass at the single point.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace FunctionalInequalities.Analysis

universe u v

section Jacobian

variable {H : Type u} [NormedAddCommGroup H]

/-- The graph Jacobian `√(1 + ‖a‖²)`: the factor by which the linear graph map with slope `a`
expands `k`-dimensional measure. -/
def graphJacobian (a : H) : ℝ := Real.sqrt (1 + ‖a‖ ^ 2)

theorem graphJacobian_pos (a : H) : 0 < graphJacobian a := by
  unfold graphJacobian; positivity

theorem graphJacobian_nonneg (a : H) : 0 ≤ graphJacobian a := (graphJacobian_pos a).le

theorem one_le_graphJacobian (a : H) : 1 ≤ graphJacobian a := by
  have hle : (1 : ℝ) ≤ 1 + ‖a‖ ^ 2 := by nlinarith [sq_nonneg ‖a‖]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖a‖ ^ 2) := Real.sqrt_le_sqrt hle

@[simp] theorem graphJacobian_zero : graphJacobian (0 : H) = 1 := by
  simp [graphJacobian]

/-- `√(1 + ‖·‖²)` is `1`-Lipschitz: the Jacobian of a graph map is controlled by its slope. -/
theorem abs_graphJacobian_sub_le (a b : H) : |graphJacobian a - graphJacobian b| ≤ ‖a - b‖ := by
  have key : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      Real.sqrt (1 + x ^ 2) - Real.sqrt (1 + y ^ 2) ≤ x - y ∨ x ≤ y := by
    intro x y hx hy
    rcases le_or_gt x y with h | h
    · exact Or.inr h
    · refine Or.inl ?_
      have h1 : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
      have h2 : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
      have hx' : x ≤ Real.sqrt (1 + x ^ 2) := by nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
      have hy' : y ≤ Real.sqrt (1 + y ^ 2) := by nlinarith [Real.sqrt_nonneg (1 + y ^ 2)]
      nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + y ^ 2)]
  have hmono : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ y →
      Real.sqrt (1 + x ^ 2) ≤ Real.sqrt (1 + y ^ 2) := by
    intro x y hx hy hxy
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [abs_le]
  constructor
  · rcases key ‖b‖ ‖a‖ (norm_nonneg _) (norm_nonneg _) with h | h
    · have : ‖b‖ - ‖a‖ ≤ ‖a - b‖ := by
        rw [← norm_neg (a - b), neg_sub]
        exact norm_sub_norm_le b a
      simp only [graphJacobian]; linarith
    · have := hmono ‖b‖ ‖a‖ (norm_nonneg _) (norm_nonneg _) h
      simp only [graphJacobian]
      have : (0:ℝ) ≤ ‖a - b‖ := norm_nonneg _
      linarith [hmono ‖b‖ ‖a‖ (norm_nonneg _) (norm_nonneg _) h]
  · rcases key ‖a‖ ‖b‖ (norm_nonneg _) (norm_nonneg _) with h | h
    · have : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := norm_sub_norm_le a b
      simp only [graphJacobian]; linarith
    · have := hmono ‖a‖ ‖b‖ (norm_nonneg _) (norm_nonneg _) h
      simp only [graphJacobian]
      have : (0:ℝ) ≤ ‖a - b‖ := norm_nonneg _
      linarith

end Jacobian

section GraphLinear

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The linear graph map with slope `a`: `v ↦ ι v + ⟪a, v⟫ • e`.  It is the Fréchet derivative of
`graphMap ι e g` at a point where `∇g = a`. -/
def graphLinear (ι : H →ₗᵢ[ℝ] V) (e : V) (a : H) : H →L[ℝ] V :=
  ι.toContinuousLinearMap + (innerSL ℝ a).smulRight e

@[simp] theorem graphLinear_apply (ι : H →ₗᵢ[ℝ] V) (e : V) (a : H) (v : H) :
    graphLinear ι e a v = ι v + ⟪a, v⟫ • e := rfl

/-- Auxiliary vector of the shear isometry. -/
private def shearVec (ι : H →ₗᵢ[ℝ] V) (e : V) (u : H) (r : ℝ) : V :=
  (1 / Real.sqrt (1 + r ^ 2) - 1) • ι u + (r / Real.sqrt (1 + r ^ 2)) • e

/-- The shear map `v ↦ ι v + ⟪u, v⟫ • z`.  For a unit `u` and a unit `e` orthogonal to the range
of `ι` it is a linear isometry (`isometry_shearCLM`) taking the dilated hyperplane onto the graph
hyperplane. -/
private def shearCLM (ι : H →ₗᵢ[ℝ] V) (e : V) (u : H) (r : ℝ) : H →L[ℝ] V :=
  ι.toContinuousLinearMap + (innerSL ℝ u).smulRight (shearVec ι e u r)

@[simp] private theorem shearCLM_apply (ι : H →ₗᵢ[ℝ] V) (e : V) (u : H) (r : ℝ) (v : H) :
    shearCLM ι e u r v = ι v + ⟪u, v⟫ • shearVec ι e u r := rfl

private theorem inner_shearCLM (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {u : H} (hu : ‖u‖ = 1) (r : ℝ) (v w : H) :
    ⟪shearCLM ι e u r v, shearCLM ι e u r w⟫ = ⟪v, w⟫ := by
  have hcpos : 0 < Real.sqrt (1 + r ^ 2) := by positivity
  have hc2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
  have huu : ⟪u, u⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hue : ⟪ι u, e⟫ = (0 : ℝ) := hperp u
  have heu : ⟪e, ι u⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hue
  have hee : ⟪e, e⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hiue : ∀ x : H, ⟪e, ι x⟫ = (0 : ℝ) := by
    intro x; rw [real_inner_comm]; exact hperp x
  have key : 2 * (1 / Real.sqrt (1 + r ^ 2) - 1) + ((1 / Real.sqrt (1 + r ^ 2) - 1) ^ 2
      + (r / Real.sqrt (1 + r ^ 2)) ^ 2) = 0 := by
    field_simp
    nlinarith [hc2, hcpos]
  simp only [shearCLM_apply, shearVec, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ι.inner_map_map, hue, heu, hee, huu, hiue, hperp]
  have hvu : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm u v
  rw [hvu]
  linear_combination (⟪u, v⟫ * ⟪u, w⟫) * key

private theorem isometry_shearCLM (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {u : H} (hu : ‖u‖ = 1) (r : ℝ) :
    Isometry (shearCLM ι e u r) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x => ?_
  have hx := inner_shearCLM ι he hperp hu r x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hx
  nlinarith [norm_nonneg (shearCLM ι e u r x), norm_nonneg x]

/-- The dilation of `H` by `c` along the unit vector `u`: `v ↦ v + (c - 1) ⟪u, v⟫ u`. -/
private def dilate (u : H) (c : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H + (c - 1) • ((innerSL ℝ u).smulRight u)

@[simp] private theorem dilate_apply (u : H) (c : ℝ) (v : H) :
    dilate u c v = v + ((c - 1) * ⟪u, v⟫) • u := by
  simp [dilate, smul_smul]

/-- The graph map with slope `r • u` factors as a dilation of `H` followed by a linear isometry. -/
private theorem shearCLM_dilate (ι : H →ₗᵢ[ℝ] V) (e : V) {u : H} (hu : ‖u‖ = 1) (r : ℝ) (v : H) :
    shearCLM ι e u r (dilate u (Real.sqrt (1 + r ^ 2)) v) = graphLinear ι e (r • u) v := by
  have hcpos : 0 < Real.sqrt (1 + r ^ 2) := by positivity
  have huu : ⟪u, u⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  set c : ℝ := Real.sqrt (1 + r ^ 2) with hc
  simp only [shearCLM_apply, dilate_apply, graphLinear_apply, shearVec, ← hc, map_add,
    LinearIsometry.map_smul, real_inner_smul_right, huu, real_inner_smul_left]
  have h1 : (c - 1) * ⟪u, v⟫ + (⟪u, v⟫ + (c - 1) * ⟪u, v⟫ * 1) * (1 / c - 1) = 0 := by
    field_simp; ring
  have h2 : (⟪u, v⟫ + (c - 1) * ⟪u, v⟫ * 1) * (r / c) = r * ⟪u, v⟫ := by
    field_simp; ring
  match_scalars
  · ring
  · linear_combination h1
  · linear_combination h2

end GraphLinear

section Measure

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] [MeasurableSpace H] [BorelSpace H] in
private theorem det_dilate {u : H} (hu : ‖u‖ = 1) (c : ℝ) :
    LinearMap.det ((dilate u c : H →ₗ[ℝ] H)) = c := by
  classical
  set k := Module.finrank ℝ H with hk
  have hune : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hpos : 0 < k := by
    rw [hk, Module.finrank_pos_iff (R := ℝ) (M := H)]
    exact ⟨⟨u, 0, hune⟩⟩
  have hcard : Module.finrank ℝ H = Fintype.card (Fin k) := by simp [hk]
  have horth :
    Orthonormal ℝ (Set.domRestrict ({⟨0, hpos⟩} : Set (Fin k)) (fun _ : Fin k => u)) := by
    constructor
    · rintro ⟨i, hi⟩; simpa using hu
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [Set.mem_singleton_iff] at hi hj
      exact absurd (Subtype.ext (hi.trans hj.symm)) hij
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb0 : b ⟨0, hpos⟩ = u := hb _ rfl
  have hmat :
    LinearMap.toMatrix b.toBasis b.toBasis (dilate u c : H →ₗ[ℝ] H) =
      Matrix.diagonal (fun j => if j = (⟨0, hpos⟩ : Fin k) then c else 1) := by
    ext i j
    have hbj :
      (dilate u c : H →ₗ[ℝ] H) (b.toBasis j) =
        (if j = (⟨0, hpos⟩ : Fin k) then c else 1) • b.toBasis j := by
      by_cases hj : j = (⟨0, hpos⟩ : Fin k)
      · rw [ite_eq_left hj]
        simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, dilate_apply, hj,
          hb0]
        rw [real_inner_self_eq_norm_sq, hu]
        module
      · rw [ite_eq_right hj]
        have hinner : ⟪u, b j⟫ = (0 : ℝ) := by
          rw [← hb0];
          exact b.orthonormal.2 (fun h => hj h.symm)
        simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, dilate_apply,
          hinner]
        simp
    rw [LinearMap.toMatrix_apply, hbj, map_smul, Matrix.diagonal_apply]
    simp only [Finsupp.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬(j = i) := fun h => hij h.symm
      simp [hij, hji]
  rw [← LinearMap.det_toMatrix b.toBasis, hmat, Matrix.det_diagonal]
  rw [Finset.prod_ite_eq' Finset.univ (⟨0, hpos⟩ : Fin k) (fun _ => c)]
  simp

omit [MeasurableSpace V] [BorelSpace V] in
private theorem hausdorffMeasure_image_dilate {u : H} (hu : ‖u‖ = 1) {c : ℝ} (hc : 0 ≤ c)
    (s : Set H) :
    μH[(Module.finrank ℝ H : ℝ)] (dilate u c '' s)
      = ENNReal.ofReal c * μH[(Module.finrank ℝ H : ℝ)] s := by
  have hH := hausdorffMeasure_finrank_eq_smul_volume H
  have himg : (dilate u c) '' s = (dilate u c : H →ₗ[ℝ] H) '' s := rfl
  rw [himg, hH]
  simp only [smul_apply, smul_eq_mul]
  rw [Measure.addHaar_image_linearMap (volume : Measure H) (dilate u c : H →ₗ[ℝ] H) s,
    det_dilate hu c, abs_of_nonneg hc]
  ring

/-- **Linear codimension-one area formula.**  A linear graph map with slope `a` expands
`k`-dimensional Hausdorff measure by exactly `√(1 + ‖a‖²)`, where `k = finrank ℝ H`.  The ambient
space is arbitrary: `ι` is any linear isometry and `e` any unit vector orthogonal to its range.
Dimension zero is included. -/
theorem hausdorffMeasure_image_graphLinear (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (a : H) (s : Set H) :
    μH[(Module.finrank ℝ H : ℝ)] (graphLinear ι e a '' s)
      = ENNReal.ofReal (graphJacobian a) * μH[(Module.finrank ℝ H : ℝ)] s := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ H : ℝ) := by positivity
  rcases eq_or_ne a 0 with rfl | ha
  · have hfun : ⇑(graphLinear ι e (0 : H)) = (ι : H → V) := by
      funext v; simp
    rw [hfun, ι.isometry.hausdorffMeasure_image (Or.inl hd) s, graphJacobian_zero,
      ENNReal.ofReal_one, one_mul]
  · have hrpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set r : ℝ := ‖a‖ with hr
    set u : H := r⁻¹ • a with hudef
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hrpos, ← hr,
        inv_mul_cancel₀ hrpos.ne']
    have hau : r • u = a := by
      rw [hudef, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
    have hJ : graphJacobian a = Real.sqrt (1 + r ^ 2) := by rw [graphJacobian, hr]
    have hcomp : ⇑(graphLinear ι e a)
        = (shearCLM ι e u r) ∘ (dilate u (Real.sqrt (1 + r ^ 2))) := by
      funext v
      rw [Function.comp_apply, shearCLM_dilate ι e hu r v, hau]
    rw [hcomp, Set.image_comp,
      (isometry_shearCLM ι he hperp hu r).hausdorffMeasure_image (Or.inl hd) _,
      hausdorffMeasure_image_dilate hu (by positivity) s, hJ]

end Measure

/-! ### The `C¹` graph map -/

section GraphMap

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The graph map `y ↦ ι y + g y • e`. -/
def graphMap (ι : H →ₗᵢ[ℝ] V) (e : V) (g : H → ℝ) : H → V := fun y => ι y + g y • e

/-- The retraction `P` of `V` onto `H` along `e`. -/
def graphProj (ι : H →ₗᵢ[ℝ] V) : V →L[ℝ] H := ContinuousLinearMap.adjoint ι.toContinuousLinearMap

theorem graphProj_ι (ι : H →ₗᵢ[ℝ] V) (y : H) : graphProj ι (ι y) = y := by
  refine ext_inner_right ℝ fun w => ?_
  rw [graphProj, ContinuousLinearMap.adjoint_inner_left]
  exact ι.inner_map_map y w

theorem graphProj_eq_zero (ι : H →ₗᵢ[ℝ] V) {e : V} (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) :
    graphProj ι e = 0 := by
  refine ext_inner_right ℝ fun w => ?_
  rw [graphProj, ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
  rw [real_inner_comm]
  exact hperp w

theorem graphProj_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ))
    (g : H → ℝ) (y : H) : graphProj ι (graphMap ι e g y) = y := by
  rw [graphMap, map_add, graphProj_ι, ContinuousLinearMap.map_smul,
    graphProj_eq_zero ι hperp, smul_zero, add_zero]

section GraphDistances

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ V]
/-- The graph map separates points at least as much as the identity. -/
theorem norm_sub_graphMap_sq (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (g : H → ℝ) (y y' : H) :
    ‖graphMap ι e g y - graphMap ι e g y'‖ ^ 2 = ‖y - y'‖ ^ 2 + (g y - g y') ^ 2 := by
  have hsub : graphMap ι e g y - graphMap ι e g y' = ι (y - y') + (g y - g y') • e := by
    simp only [graphMap, map_sub, sub_smul]; abel
  rw [hsub, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have hie : ⟪ι (y - y'), e⟫ = (0 : ℝ) := hperp _
  have hei : ⟪e, ι (y - y')⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hie
  have hee : ⟪e, e⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ι.inner_map_map, hie, hei, hee]
  ring

theorem norm_sub_le_norm_sub_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (g : H → ℝ) (y y' : H) :
    ‖y - y'‖ ≤ ‖graphMap ι e g y - graphMap ι e g y'‖ := by
  have h := norm_sub_graphMap_sq ι he hperp g y y'
  nlinarith [norm_nonneg (graphMap ι e g y - graphMap ι e g y'), norm_nonneg (y - y'),
    sq_nonneg (g y - g y')]

end GraphDistances

theorem graphMap_injective (ι : H →ₗᵢ[ℝ] V) {e : V} (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ))
    (g : H → ℝ) : Function.Injective (graphMap ι e g) := by
  intro y y' h
  have := graphProj_graphMap ι hperp g y
  rw [h, graphProj_graphMap ι hperp g y'] at this
  exact this.symm

theorem image_graphMap_eq (ι : H →ₗᵢ[ℝ] V) {e : V} (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ))
    {g : H → ℝ} (E : Set H) :
    graphMap ι e g '' E
      = {x : V | graphMap ι e g (graphProj ι x) = x} ∩ (graphProj ι) ⁻¹' E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · change graphMap ι e g (graphProj ι (graphMap ι e g y)) = graphMap ι e g y
      rw [graphProj_graphMap ι hperp g y]
    · simp only [Set.mem_preimage, graphProj_graphMap ι hperp g y]; exact hy
  · rintro ⟨hx1, hx2⟩
    exact ⟨graphProj ι x, hx2, hx1⟩

theorem measurableSet_image_graphMap [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V]
    [BorelSpace V] (ι : H →ₗᵢ[ℝ] V) {e : V} (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ))
    {g : H → ℝ} (hg : Continuous g) {E : Set H} (hE : MeasurableSet E) :
    MeasurableSet (graphMap ι e g '' E) := by
  rw [image_graphMap_eq ι hperp E]
  have hcont : Continuous (graphMap ι e g) :=
    ι.continuous.add (hg.smul continuous_const)
  refine MeasurableSet.inter ?_ (hE.preimage (graphProj ι).continuous.measurable)
  exact (isClosed_eq (hcont.comp (graphProj ι).continuous) continuous_id).measurableSet

omit [FiniteDimensional ℝ V] in
/-- The derivative of the graph map is the linear graph map with slope the gradient. -/
theorem hasFDerivAt_graphMap (ι : H →ₗᵢ[ℝ] V) (e : V) {g : H → ℝ} {y : H}
    (hg : DifferentiableAt ℝ g y) :
    HasFDerivAt (graphMap ι e g) (graphLinear ι e (gradient g y)) y := by
  have h1 : HasFDerivAt (fun y : H => ι y) ι.toContinuousLinearMap y :=
    ι.toContinuousLinearMap.hasFDerivAt
  have h2 : HasFDerivAt (fun y : H => g y • e) ((innerSL ℝ (gradient g y)).smulRight e) y := by
    have heq : (innerSL ℝ (gradient g y) : H →L[ℝ] ℝ) = fderiv ℝ g y := by
      rw [← toDual_gradient (𝕜 := ℝ) (f := g) (x := y)]
      refine ContinuousLinearMap.ext fun v => ?_
      rw [InnerProductSpace.toDual_apply_apply]
      rfl
    have hgd : HasFDerivAt g (innerSL ℝ (gradient g y)) y := by
      rw [heq]; exact hg.hasFDerivAt
    exact hgd.smul_const e
  exact h1.add h2

end GraphMap

/-! ### Approximation of a `C¹` graph map by linear graph maps -/

section Approximation

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem fderiv_eq_innerSL_gradient (g : H → ℝ) (y : H) :
    (innerSL ℝ (gradient g y) : H →L[ℝ] ℝ) = fderiv ℝ g y := by
  rw [← toDual_gradient (𝕜 := ℝ) (f := g) (x := y)]
  refine ContinuousLinearMap.ext fun v => ?_
  rw [InnerProductSpace.toDual_apply_apply]
  rfl

omit [FiniteDimensional ℝ V] in
/-- On a ball where the gradient stays `ε`-close to `a`, the graph map is `ε`-approximated by the
linear graph map with slope `a`. -/
theorem approximatesLinearOn_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    {g : H → ℝ} (hg : ContDiff ℝ 1 g) {y₀ : H} {r : ℝ} {ε : ℝ≥0}
    (hball : ∀ z ∈ Metric.ball y₀ r, ‖gradient g z - gradient g y₀‖ ≤ (ε : ℝ))
    {t : Set H} (hts : t ⊆ Metric.ball y₀ r) :
    ApproximatesLinearOn (graphMap ι e g) (graphLinear ι e (gradient g y₀)) t ε := by
  set a : H := gradient g y₀ with ha
  set h : H → ℝ := fun z => g z - ⟪a, z⟫ with hh
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hhd : ∀ x : H, DifferentiableAt ℝ h x := by
    intro x
    exact (hgd x).sub ((innerSL ℝ a).differentiableAt)
  have hfd : ∀ x : H, fderiv ℝ h x = innerSL ℝ (gradient g x - a) := by
    intro x
    have h1 : HasFDerivAt g (innerSL ℝ (gradient g x)) x := by
      rw [fderiv_eq_innerSL_gradient]; exact (hgd x).hasFDerivAt
    have h2 : HasFDerivAt (fun z : H => ⟪a, z⟫) (innerSL ℝ a) x :=
      (innerSL ℝ a).hasFDerivAt
    have h3 : HasFDerivAt h (innerSL ℝ (gradient g x) - innerSL ℝ a) x := h1.sub h2
    rw [h3.fderiv, ← map_sub]
  have hbound : ∀ x ∈ Metric.ball y₀ r, ‖fderiv ℝ h x‖ ≤ (ε : ℝ) := by
    intro x hx
    rw [hfd x, innerSL_apply_norm]
    exact hball x hx
  intro y hy y' hy'
  have hsub : graphMap ι e g y - graphMap ι e g y' - graphLinear ι e a (y - y')
      = (h y - h y') • e := by
    simp only [graphMap, graphLinear_apply, hh, map_sub, sub_smul]
    module
  rw [hsub, norm_smul, he, mul_one, Real.norm_eq_abs, ← Real.norm_eq_abs]
  have := (convex_ball y₀ r).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hhd x) hbound (hts hy') (hts hy)
  calc ‖h y - h y'‖ ≤ (ε : ℝ) * ‖y - y'‖ := this
    _ = (ε : ℝ) * ‖y - y'‖ := rfl

end Approximation

section Sandwich

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
theorem continuous_graphJacobian : Continuous (graphJacobian : H → ℝ) := by
  unfold graphJacobian
  fun_prop

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- A countable measurable partition of `H` on which the graph map is `ε`-approximated by linear
graph maps and the gradient stays `ε`-close to the corresponding slope. -/
theorem exists_approximating_partition (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    {g : H → ℝ} (hg : ContDiff ℝ 1 g) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (t : ℕ → Set H) (a : ℕ → H),
      (∀ n, MeasurableSet (t n)) ∧ Pairwise (Function.onFun Disjoint t) ∧
      (⋃ n, t n) = Set.univ ∧
      (∀ n, ApproximatesLinearOn (graphMap ι e g) (graphLinear ι e (a n)) (t n) ε) ∧
      (∀ n, ∀ z ∈ t n, ‖gradient g z - a n‖ ≤ (ε : ℝ)) := by
  classical
  have hgc : Continuous (gradient g) := BakryEmery.continuous_gradient hg
  have hrad : ∀ y₀ : H, ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ Metric.ball y₀ r, ‖gradient g z - gradient g y₀‖ ≤ (ε : ℝ) := by
    intro y₀
    have hpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hgc.continuousAt (ε : ℝ) hpos
    refine ⟨r, hr, fun z hz => ?_⟩
    have := hball (Metric.mem_ball.mp hz)
    rw [dist_eq_norm] at this
    exact this.le
  choose r hrpos hrball using hrad
  obtain ⟨σ, T, hTm, hTd, hTu, hTsub⟩ :=
    exists_measurable_partition_subordinate MeasurableSet.univ (subset_refl _)
      ⟨(0 : H), Set.mem_univ _⟩
      (fun z : (Set.univ : Set H) => Metric.ball (z : H) (r z))
      (fun _ => Metric.isOpen_ball)
      (fun z => Metric.mem_ball_self (hrpos z)) (fun _ => Set.subset_univ _)
  let w : ℕ → H := fun n => σ n
  refine ⟨T, fun n => gradient g (w n), hTm, hTd, hTu, ?_, ?_⟩
  · intro n
    exact approximatesLinearOn_graphMap ι he hg (hrball (w n)) (hTsub n)
  · intro n z hz
    exact hrball (w n) z (hTsub n hz)
omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Comparison of Hausdorff measures of two images from a pointwise Lipschitz comparison. -/
theorem hausdorffMeasure_image_le_of_norm_le {f₁ f₂ : H → V} {s : Set H} {K : ℝ≥0}
    (hinj : Set.InjOn f₂ s)
    (hle : ∀ y ∈ s, ∀ y' ∈ s, ‖f₁ y - f₁ y'‖ ≤ (K : ℝ) * ‖f₂ y - f₂ y'‖)
    {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (f₁ '' s) ≤ (K : ℝ≥0∞) ^ d * μH[d] (f₂ '' s) := by
  classical
  have himg : (f₁ ∘ Function.invFunOn f₂ s) '' (f₂ '' s) = f₁ '' s := by
    rw [← Set.image_comp]
    refine Set.image_congr fun y hy => ?_
    simp only [Function.comp_apply, hinj.leftInvOn_invFunOn hy]
  rw [← himg]
  refine LipschitzOnWith.hausdorffMeasure_image_le ?_ hd
  refine LipschitzOnWith.of_dist_le_mul ?_
  rintro x ⟨y, hy, rfl⟩ x' ⟨y', hy', rfl⟩
  simp only [Function.comp_apply, hinj.leftInvOn_invFunOn hy, hinj.leftInvOn_invFunOn hy']
  rw [dist_eq_norm, dist_eq_norm]
  exact hle y hy y' hy'

omit [FiniteDimensional ℝ V] in
/-- Both sandwich estimates for a graph map that is `ε`-close to a linear graph map. -/
theorem hausdorffMeasure_image_graphMap_le (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (g : H → ℝ) (a : H) {t : Set H} {ε : ℝ≥0}
    (happ : ApproximatesLinearOn (graphMap ι e g) (graphLinear ι e a) t ε) :
    μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' t) ≤
      ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ) * ENNReal.ofReal (graphJacobian a) *
        μH[(Module.finrank ℝ H : ℝ)] t := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ H : ℝ) := by positivity
  have hAnorm : ∀ v : H, ‖v‖ ≤ ‖graphLinear ι e a v‖ := by
    intro v
    have hsub :
      graphLinear ι e a v =
        graphMap ι e (fun y => ⟪a, y⟫) v - graphMap ι e (fun _ => (0 : ℝ)) 0 := by
      simp [graphMap, graphLinear_apply]
    have := norm_sub_le_norm_sub_graphMap ι he hperp (fun y => ⟪a, y⟫) v 0
    simpa [graphMap, graphLinear_apply] using this
  have hAinj : Set.InjOn (graphLinear ι e a) t := by
    intro y hy y' hy' hh
    have := hAnorm (y - y')
    rw [map_sub, hh, sub_self, norm_zero] at this
    simpa [sub_eq_zero] using le_antisymm this (norm_nonneg _)
  have hcmp :
    ∀ y ∈ t,
      ∀ y' ∈ t,
        ‖graphMap ι e g y - graphMap ι e g y'‖ ≤
          ((1 + ε : ℝ≥0) : ℝ) * ‖graphLinear ι e a y - graphLinear ι e a y'‖ := by
    intro y hy y' hy'
    have h1 := happ y hy y' hy'
    have h2 : ‖y - y'‖ ≤ ‖graphLinear ι e a (y - y')‖ := hAnorm _
    have h3 : graphLinear ι e a (y - y') = graphLinear ι e a y - graphLinear ι e a y' :=
      map_sub _ _ _
    have h4 :
      ‖graphMap ι e g y - graphMap ι e g y'‖ ≤
        ‖graphMap ι e g y - graphMap ι e g y' - graphLinear ι e a (y - y')‖ +
          ‖graphLinear ι e a (y - y')‖ := by
      have :=
        norm_add_le (graphMap ι e g y - graphMap ι e g y' - graphLinear ι e a (y - y'))
          (graphLinear ι e a (y - y'))
      simpa using this
    rw [h3] at h1 h2 h4
    have h5 : (ε : ℝ) * ‖y - y'‖ ≤ (ε : ℝ) * ‖graphLinear ι e a y - graphLinear ι e a y'‖ :=
      mul_le_mul_of_nonneg_left h2 ε.coe_nonneg
    push_cast
    linarith
  calc
    μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' t) ≤
        ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ) *
          μH[(Module.finrank ℝ H : ℝ)] (graphLinear ι e a '' t) :=
      hausdorffMeasure_image_le_of_norm_le hAinj hcmp hd
    _ =
        ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ) * ENNReal.ofReal (graphJacobian a) *
          μH[(Module.finrank ℝ H : ℝ)] t := by
      rw [hausdorffMeasure_image_graphLinear ι he hperp a t, mul_assoc]

/-- Reverse sandwich estimate. -/
theorem le_hausdorffMeasure_image_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (g : H → ℝ) (a : H) {t : Set H} {ε : ℝ≥0}
    (happ : ApproximatesLinearOn (graphMap ι e g) (graphLinear ι e a) t ε) :
    ENNReal.ofReal (graphJacobian a) * μH[(Module.finrank ℝ H : ℝ)] t
      ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
        * μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' t) := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ H : ℝ) := by positivity
  have hΨinj : Set.InjOn (graphMap ι e g) t :=
    (graphMap_injective ι hperp g).injOn
  have hcmp : ∀ y ∈ t, ∀ y' ∈ t,
      ‖graphLinear ι e a y - graphLinear ι e a y'‖
        ≤ ((1 + ε : ℝ≥0) : ℝ) * ‖graphMap ι e g y - graphMap ι e g y'‖ := by
    intro y hy y' hy'
    have h1 := happ y hy y' hy'
    have h2 : ‖y - y'‖ ≤ ‖graphMap ι e g y - graphMap ι e g y'‖ :=
      norm_sub_le_norm_sub_graphMap ι he hperp g y y'
    have h3 : graphLinear ι e a (y - y') = graphLinear ι e a y - graphLinear ι e a y' :=
      map_sub _ _ _
    have h4 : ‖graphLinear ι e a (y - y')‖
        ≤ ‖graphMap ι e g y - graphMap ι e g y' - graphLinear ι e a (y - y')‖
          + ‖graphMap ι e g y - graphMap ι e g y'‖ := by
      have := norm_add_le (graphLinear ι e a (y - y')
          - (graphMap ι e g y - graphMap ι e g y')) (graphMap ι e g y - graphMap ι e g y')
      have hnn : ‖graphLinear ι e a (y - y') - (graphMap ι e g y - graphMap ι e g y')‖
          = ‖graphMap ι e g y - graphMap ι e g y' - graphLinear ι e a (y - y')‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [hnn] at this
      simpa using this
    rw [h3] at h1 h4
    have h5 : (ε : ℝ) * ‖y - y'‖
        ≤ (ε : ℝ) * ‖graphMap ι e g y - graphMap ι e g y'‖ :=
      mul_le_mul_of_nonneg_left h2 ε.coe_nonneg
    push_cast
    linarith
  calc ENNReal.ofReal (graphJacobian a) * μH[(Module.finrank ℝ H : ℝ)] t
      = μH[(Module.finrank ℝ H : ℝ)] (graphLinear ι e a '' t) :=
        (hausdorffMeasure_image_graphLinear ι he hperp a t).symm
    _ ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
          * μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' t) :=
        hausdorffMeasure_image_le_of_norm_le hΨinj hcmp hd

end Sandwich

/-! ### Two-sided estimate and the limit -/

section Limits

/-- `ε ↦ (1+ε)^n * (X + ε * M)` tends to `X` as `ε ↓ 0`, when `X` and `M` are finite. -/
theorem tendsto_aux (n : ℕ) {X M : ℝ≥0∞} (hM : M ≠ ⊤) :
    Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n * (X + (ε : ℝ≥0∞) * M))
      (𝓝[>] 0) (𝓝 X) := by
  have hc : Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞)) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun ε : ℝ≥0 => (1 + ε : ℝ≥0)) (𝓝[>] 0) (𝓝 1) := by
      have : Continuous fun ε : ℝ≥0 => (1 + ε : ℝ≥0) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (ENNReal.continuous_coe.tendsto 1).comp h0
  have h1 : Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n) (𝓝[>] 0) (𝓝 1) := by
    have := (ENNReal.continuous_pow n).tendsto (1 : ℝ≥0∞)
    simpa [Function.comp_def] using this.comp hc
  have hcoe : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ≥0 => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [Function.comp_def] using (ENNReal.continuous_coe.tendsto 0).comp h0
  have h2 : Tendsto (fun ε : ℝ≥0 => X + (ε : ℝ≥0∞) * M) (𝓝[>] 0) (𝓝 X) := by
    have hm : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * M) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.mul hcoe (Or.inr hM) tendsto_const_nhds (Or.inr (by simp))
      simpa using this
    simpa using tendsto_const_nhds.add hm
  have := ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero) h2 (Or.inr (by simp))
  simpa using this

/-- `ε ↦ (1+ε)^n * X + ε * M` tends to `X` as `ε ↓ 0`, when `X` and `M` are finite. -/
theorem tendsto_aux' (n : ℕ) {X M : ℝ≥0∞} (_hX : X ≠ ⊤) (hM : M ≠ ⊤) :
    Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n * X + (ε : ℝ≥0∞) * M)
      (𝓝[>] 0) (𝓝 X) := by
  have hc : Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞)) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun ε : ℝ≥0 => (1 + ε : ℝ≥0)) (𝓝[>] 0) (𝓝 1) := by
      have : Continuous fun ε : ℝ≥0 => (1 + ε : ℝ≥0) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (ENNReal.continuous_coe.tendsto 1).comp h0
  have h1 : Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n) (𝓝[>] 0) (𝓝 1) := by
    have := (ENNReal.continuous_pow n).tendsto (1 : ℝ≥0∞)
    simpa [Function.comp_def] using this.comp hc
  have hcoe : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ≥0 => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [Function.comp_def] using (ENNReal.continuous_coe.tendsto 0).comp h0
  have hm : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * M) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.mul hcoe (Or.inr hM) tendsto_const_nhds (Or.inr (by simp))
    simpa using this
  have hl : Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n * X) (𝓝[>] 0) (𝓝 X) := by
    have := ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero)
      (tendsto_const_nhds (x := X) (f := (𝓝[>] (0:ℝ≥0)))) (Or.inr (by simp))
    simpa using this
  simpa using hl.add hm

end Limits

section Estimates

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem measurable_graphJacobian_gradient {g : H → ℝ} (hg : ContDiff ℝ 1 g) :
    Measurable fun y : H => ENNReal.ofReal (graphJacobian (gradient g y)) :=
  (ENNReal.measurable_ofReal.comp
    (continuous_graphJacobian.comp (BakryEmery.continuous_gradient hg)).measurable)

/-- Two-sided estimate at scale `ε`. -/
theorem graphMap_estimates (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) {ε : ℝ≥0} (hε : 0 < ε) :
    μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' s)
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
          * (∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y))
              ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H)
            + ε * μH[(Module.finrank ℝ H : ℝ)] s)
      ∧ ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y))
              ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H)
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
            * μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' s)
          + ε * μH[(Module.finrank ℝ H : ℝ)] s := by
  classical
  set k : ℝ := (Module.finrank ℝ H : ℝ) with hk
  set μ : Measure H := (μH[k] : Measure H) with hμ
  set Ψ : H → V := graphMap ι e g with hΨ
  set J : H → ℝ≥0∞ := fun y => ENNReal.ofReal (graphJacobian (gradient g y)) with hJ
  have hJmeas : Measurable J := measurable_graphJacobian_gradient hg
  have hgcont : Continuous g := hg.continuous
  obtain ⟨t, a, hmeas, hdisj, hcover, happ, hgrad⟩ := exists_approximating_partition ι he hg hε
  set u : ℕ → Set H := fun n => s ∩ t n with hu
  have humeas : ∀ n, MeasurableSet (u n) := fun n => hs.inter (hmeas n)
  have hudisj : Pairwise (Function.onFun Disjoint u) := fun i j hij =>
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hij)
  have huunion : (⋃ n, u n) = s := by
    rw [hu, ← Set.inter_iUnion, hcover, Set.inter_univ]
  have hsub : ∀ n, u n ⊆ t n := fun n => Set.inter_subset_right
  have himgdisj : Pairwise (Function.onFun Disjoint (fun n => Ψ '' (u n))) := fun i j hij =>
    Set.disjoint_image_of_injective (graphMap_injective ι hperp g) (hudisj hij)
  have himgmeas : ∀ n, MeasurableSet (Ψ '' (u n)) := fun n =>
    measurableSet_image_graphMap ι hperp hgcont (humeas n)
  have himg : Ψ '' s = ⋃ n, Ψ '' (u n) := by rw [← Set.image_iUnion, huunion]
  have hsplitμ : μH[k] (Ψ '' s) = ∑' n, μH[k] (Ψ '' (u n)) := by
    rw [himg, measure_iUnion himgdisj himgmeas]
  have hsplitint : ∫⁻ y in s, J y ∂μ = ∑' n, ∫⁻ y in u n, J y ∂μ := by
    rw [← huunion, lintegral_iUnion humeas hudisj]
  have hsplitmeas : μ s = ∑' n, μ (u n) := by
    rw [← huunion, measure_iUnion hudisj humeas]
  -- pointwise Jacobian comparison on each piece
  have hJcmp : ∀ n, ∀ y ∈ u n,
      ENNReal.ofReal (graphJacobian (a n)) ≤ J y + ENNReal.ofReal (ε : ℝ) := by
    intro n y hy
    have h1 : ‖gradient g y - a n‖ ≤ (ε : ℝ) := hgrad n y (hsub n hy)
    have h2 : |graphJacobian (a n) - graphJacobian (gradient g y)| ≤ ‖a n - gradient g y‖ :=
      abs_graphJacobian_sub_le _ _
    have h3 : ‖a n - gradient g y‖ = ‖gradient g y - a n‖ := by rw [← norm_neg]; congr 1; abel
    have h4 : graphJacobian (a n) ≤ graphJacobian (gradient g y) + (ε : ℝ) := by
      rw [h3] at h2
      cases abs_le.mp h2 with
      | intro hlo hhi => linarith
    calc ENNReal.ofReal (graphJacobian (a n))
        ≤ ENNReal.ofReal (graphJacobian (gradient g y) + (ε : ℝ)) := ENNReal.ofReal_le_ofReal h4
      _ = J y + ENNReal.ofReal (ε : ℝ) := by
          rw [hJ, ENNReal.ofReal_add (graphJacobian_nonneg _) (NNReal.coe_nonneg ε)]
  have hJcmp' : ∀ n, ∀ y ∈ u n,
      J y ≤ ENNReal.ofReal (graphJacobian (a n)) + ENNReal.ofReal (ε : ℝ) := by
    intro n y hy
    have h1 : ‖gradient g y - a n‖ ≤ (ε : ℝ) := hgrad n y (hsub n hy)
    have h2 : |graphJacobian (gradient g y) - graphJacobian (a n)| ≤ ‖gradient g y - a n‖ :=
      abs_graphJacobian_sub_le _ _
    have h4 : graphJacobian (gradient g y) ≤ graphJacobian (a n) + (ε : ℝ) := by
      cases abs_le.mp h2 with
      | intro hlo hhi => linarith
    calc J y ≤ ENNReal.ofReal (graphJacobian (a n) + (ε : ℝ)) := ENNReal.ofReal_le_ofReal h4
      _ = ENNReal.ofReal (graphJacobian (a n)) + ENNReal.ofReal (ε : ℝ) := by
          rw [ENNReal.ofReal_add (graphJacobian_nonneg _) (NNReal.coe_nonneg ε)]
  constructor
  · rw [hsplitμ]
    have hterm : ∀ n, μH[k] (Ψ '' (u n))
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * (∫⁻ y in u n, J y ∂μ + ε * μ (u n)) := by
      intro n
      have h1 := hausdorffMeasure_image_graphMap_le ι he hperp g (a n)
        ((happ n).mono_set (hsub n))
      have h2 : ENNReal.ofReal (graphJacobian (a n)) * μ (u n)
          ≤ ∫⁻ y in u n, J y ∂μ + ε * μ (u n) := by
        have hconst : ENNReal.ofReal (graphJacobian (a n)) * μ (u n)
            = ∫⁻ y in u n, ENNReal.ofReal (graphJacobian (a n)) ∂μ := by
          rw [setLIntegral_const]
        rw [hconst]
        calc ∫⁻ y in u n, ENNReal.ofReal (graphJacobian (a n)) ∂μ
            ≤ ∫⁻ y in u n, (J y + ENNReal.ofReal (ε : ℝ)) ∂μ :=
              setLIntegral_mono' (humeas n) (hJcmp n)
          _ = ∫⁻ y in u n, J y ∂μ + ENNReal.ofReal (ε : ℝ) * μ (u n) := by
              rw [lintegral_add_right _ measurable_const, setLIntegral_const]
          _ = ∫⁻ y in u n, J y ∂μ + ε * μ (u n) := by
              rw [ENNReal.ofReal_coe_nnreal]
      calc μH[k] (Ψ '' (u n))
          ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * ENNReal.ofReal (graphJacobian (a n)) * μH[k] (u n) := h1
        _ = ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * (ENNReal.ofReal (graphJacobian (a n)) * μ (u n)) := by
            rw [mul_assoc]
        _ ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * (∫⁻ y in u n, J y ∂μ + ε * μ (u n)) := by gcongr
    simpa only [ENNReal.tsum_mul_left, tsum_add, ← hsplitint, ← hsplitmeas]
      using tsum_le_tsum hterm
  · rw [hsplitint]
    have hterm : ∀ n, ∫⁻ y in u n, J y ∂μ
        ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' (u n)) + ε * μ (u n) := by
      intro n
      have h1 := le_hausdorffMeasure_image_graphMap ι he hperp g (a n)
        ((happ n).mono_set (hsub n))
      calc ∫⁻ y in u n, J y ∂μ
          ≤ ∫⁻ y in u n, (ENNReal.ofReal (graphJacobian (a n)) + ENNReal.ofReal (ε : ℝ)) ∂μ :=
            setLIntegral_mono' (humeas n) (hJcmp' n)
        _ = ENNReal.ofReal (graphJacobian (a n)) * μ (u n) + ε * μ (u n) := by
            rw [setLIntegral_const, add_mul, ENNReal.ofReal_coe_nnreal]
        _ ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' (u n)) + ε * μ (u n) := by gcongr
    calc ∑' n, ∫⁻ y in u n, J y ∂μ
        ≤ ∑' n, (((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' (u n)) + ε * μ (u n)) :=
          tsum_le_tsum hterm
      _ = ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * (∑' n, μH[k] (Ψ '' (u n))) + ε * ∑' n, μ (u n) := by
          rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ = ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ k * μH[k] (Ψ '' s) + ε * μ s := by
          rw [← hsplitμ, ← hsplitmeas]

end Estimates

/-! ### The area formula -/

section AreaFormula

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem hausdorffMeasure_image_graphMap_of_finite (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s)
    (hsfin : (μH[(Module.finrank ℝ H : ℝ)] : Measure H) s ≠ ⊤) :
    μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' s)
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y))
          ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H) := by
  set n : ℕ := Module.finrank ℝ H with hn
  set μ : Measure H := (μH[(n : ℝ)] : Measure H) with hμ
  set A : ℝ≥0∞ := μH[(n : ℝ)] (graphMap ι e g '' s) with hA
  set I : ℝ≥0∞ := ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y)) ∂μ with hI
  set M : ℝ≥0∞ := μ s with hM
  have hrw : ∀ x : ℝ≥0∞, x ^ ((n : ℕ) : ℝ) = x ^ n := fun x => ENNReal.rpow_natCast x n
  have hest : ∀ ε : ℝ≥0, 0 < ε →
      A ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n * (I + (ε : ℝ≥0∞) * M) ∧
      I ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ n * A + (ε : ℝ≥0∞) * M := by
    intro ε hε
    obtain ⟨h1, h2⟩ := graphMap_estimates ι he hperp hg hs hε
    rw [hrw] at h1 h2
    exact ⟨h1, h2⟩
  rcases eq_or_ne I ⊤ with hItop | hItop
  · have h2 := (hest 1 one_pos).2
    rw [hItop] at h2
    have hAtop : A = ⊤ := by
      by_contra hAne
      have hfin : ((1 + (1 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ^ n * A + ((1 : ℝ≥0) : ℝ≥0∞) * M ≠ ⊤ := by
        refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hAne, ?_⟩
        exact ENNReal.mul_ne_top (by simp) hsfin
      exact hfin (top_le_iff.mp h2)
    rw [hAtop, hItop]
  · have hAle : A ≤ I := by
      refine ge_of_tendsto (tendsto_aux n hsfin (X := I)) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hest ε hε).1
    have hAne : A ≠ ⊤ := by
      have h1 := (hest 1 one_pos).1
      refine ne_top_of_le_ne_top ?_ h1
      exact ENNReal.mul_ne_top (by simp)
        (ENNReal.add_ne_top.mpr ⟨hItop, ENNReal.mul_ne_top (by simp) hsfin⟩)
    have hIle : I ≤ A := by
      refine ge_of_tendsto (tendsto_aux' n hAne hsfin) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hest ε hε).2
    exact le_antisymm hAle hIle

/-- **Codimension-one area formula for `C¹` graphs.** -/
theorem hausdorffMeasure_image_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) :
    μH[(Module.finrank ℝ H : ℝ)] (graphMap ι e g '' s)
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y))
          ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H) := by
  set n : ℕ := Module.finrank ℝ H with hn
  set μ : Measure H := (μH[(n : ℝ)] : Measure H) with hμ
  set J : H → ℝ≥0∞ := fun y => ENNReal.ofReal (graphJacobian (gradient g y)) with hJ
  have hJmeas : Measurable J := measurable_graphJacobian_gradient hg
  set sm : ℕ → Set H := fun m => s ∩ Metric.ball (0 : H) (m + 1) with hsm
  have hsmmeas : ∀ m, MeasurableSet (sm m) := fun m => hs.inter Metric.isOpen_ball.measurableSet
  have hsmmono : Monotone sm := by
    intro i j hij
    refine Set.inter_subset_inter_right _ (Metric.ball_subset_ball ?_)
    have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  have hsmunion : (⋃ m, sm m) = s := by
    simp only [sm, ← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]
  have hsmfin : ∀ m, μ (sm m) ≠ ⊤ := by
    intro m
    exact ((Metric.isBounded_ball (x := (0 : H)) (r := (m : ℝ) + 1)).subset
      Set.inter_subset_right).measure_lt_top.ne
  -- both sides are limits of the truncated versions
  have hLim : Tendsto (fun m => μH[(n : ℝ)] (graphMap ι e g '' sm m)) atTop
      (𝓝 (μH[(n : ℝ)] (graphMap ι e g '' s))) := by
    have himg : (⋃ m, graphMap ι e g '' sm m) = graphMap ι e g '' s := by
      rw [← Set.image_iUnion, hsmunion]
    rw [← himg]
    exact tendsto_measure_iUnion_atTop (fun i j hij => Set.image_mono (hsmmono hij))
  have hRlim : Tendsto (fun m => ∫⁻ y in sm m, J y ∂μ) atTop (𝓝 (∫⁻ y in s, J y ∂μ)) := by
    have hd : Directed (· ⊆ ·) sm := fun i j =>
      ⟨max i j, hsmmono (le_max_left _ _), hsmmono (le_max_right _ _)⟩
    rw [← hsmunion, setLIntegral_iUnion_of_directed J hd]
    exact tendsto_atTop_iSup fun i j hij => lintegral_mono_set (hsmmono hij)
  refine tendsto_nhds_unique hLim ?_
  have heq : ∀ m, μH[(n : ℝ)] (graphMap ι e g '' sm m) = ∫⁻ y in sm m, J y ∂μ :=
    fun m => hausdorffMeasure_image_graphMap_of_finite ι he hperp hg (hsmmeas m) (hsmfin m)
  simpa only [heq] using hRlim

/-- **Codimension-one area formula, normalized convention.**  With `hausdorffNormalized`, the
`k`-dimensional measure of the graph of a `C¹` function over a measurable set `s` is the integral
of `√(1 + ‖∇g‖²)` against Lebesgue measure on `H`.  This is the form used by the relative-perimeter
chain, where `H` is a tangent hyperplane of the ambient space `V` and `k = finrank V - 1`. -/
theorem hausdorffNormalized_image_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) :
    KLS.hausdorffNormalized V (Module.finrank ℝ H) (graphMap ι e g '' s)
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y)) ∂(volume : Measure H) := by
  set k : ℕ := Module.finrank ℝ H with hk
  have hωpos : 0 < KLS.unitBallVolume k := by unfold KLS.unitBallVolume; positivity
  have hcancel : ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k)
      * ENNReal.ofReal (2 ^ k / KLS.unitBallVolume k) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show KLS.unitBallVolume k / 2 ^ k * (2 ^ k / KLS.unitBallVolume k) = 1 by field_simp]
    exact ENNReal.ofReal_one
  rw [KLS.hausdorffNormalized, smul_apply, smul_eq_mul,
    hausdorffMeasure_image_graphMap ι he hperp hg hs]
  rw [hausdorffMeasure_finrank_eq_smul_volume H]
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← hk, ← mul_assoc, hcancel,
    one_mul]

end AreaFormula




end FunctionalInequalities.Analysis
