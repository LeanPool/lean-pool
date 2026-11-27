/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphParametrization
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.LinearAlgebra.Transvection.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Flattening a graph domain

For a Lipschitz graph domain `Ω = {x : φ(x) < ⟪x, e⟫}` the **flattening**
`F(x) = x - φ(x) e` (`Rd.LipschitzGraph.flatten`) maps `Ω` onto the half-space `{⟪y, e⟫ > 0}`
(`Rd.LipschitzGraph.inner_flatten`): it is a bijection of `V` with inverse `y ↦ y + φ(y) e`
(`Rd.LipschitzGraph.unflatten`), because `φ` is constant along `e`. Both maps are
`(1 + M)`-Lipschitz (`Rd.LipschitzGraph.lipschitzWith_flatten`,
`Rd.LipschitzGraph.lipschitzWith_unflatten`), and the image of the hyperplane
`e^⊥` under it contains the graph (`Rd.LipschitzGraph.graph_subset_image_unflatten`). For smooth
`φ` both maps are smooth, and the derivative `id - e ⊗ Dφ(x)` of the flattening is a
transvection, since `Dφ(x) e = 0`, so its determinant is `1`
(`Rd.LipschitzGraph.det_fderiv_flatten`, Mathlib's `LinearMap.transvection.det`).

Over `H = e^⊥` the **product coordinates** `(x', t) ↦ x' + t e` and the **graph coordinates**
`(x', t) ↦ γ(x') + t e` with `γ(x') = x' + φ(x') e` (`Rd.LipschitzGraph.prodEquiv`,
`Rd.LipschitzGraph.graphEquiv`) preserve the Lebesgue measure, and the inverse flattening is the
graph coordinates after the inverse of the product coordinates (`Rd.LipschitzGraph.unflatten_eq`).
So both maps preserve the Lebesgue measure for every Lipschitz graph
(`Rd.LipschitzGraph.measurePreserving_flatten`,
`Rd.LipschitzGraph.measurePreserving_unflatten`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace Rd

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-- The **flattening** `x ↦ x - φ(x) e`. -/
def flatten (x : V) : V := x - Ω.phi x • Ω.e

/-- The inverse of the flattening, `y ↦ y + φ(y) e`. -/
def unflatten (y : V) : V := y + Ω.phi y • Ω.e

/-- `φ` is constant along `e`, also backwards: `φ(x - t e) = φ(x)`. -/
theorem phi_sub_smul (x : V) (t : ℝ) : Ω.phi (x - t • Ω.e) = Ω.phi x := by
  rw [sub_eq_add_neg, ← neg_smul, Ω.const]

/-- The inverse undoes the flattening. -/
theorem unflatten_flatten (x : V) : Ω.unflatten (Ω.flatten x) = x := by
  rw [unflatten, flatten, Ω.phi_sub_smul, sub_add_cancel]

/-- The flattening undoes the inverse. -/
theorem flatten_unflatten (y : V) : Ω.flatten (Ω.unflatten y) = y := by
  rw [flatten, unflatten, Ω.const, add_sub_cancel_right]

/-- **The flattening lowers the height by the graph**: `⟪F(x), e⟫ = ⟪x, e⟫ - φ(x)`. -/
theorem inner_flatten (x : V) : inner ℝ (Ω.flatten x) Ω.e = inner ℝ x Ω.e - Ω.phi x := by
  rw [flatten, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, Ω.norm_e]
  ring

/-- The flattening is a bijection of `V`. -/
noncomputable def flattenEquiv : V ≃ V where
  toFun := Ω.flatten
  invFun := Ω.unflatten
  left_inv := Ω.unflatten_flatten
  right_inv := Ω.flatten_unflatten

/-- The flattening is continuous. -/
theorem continuous_flatten : Continuous Ω.flatten :=
  continuous_id.sub (Ω.continuous_phi.smul continuous_const)

/-- The inverse of the flattening is continuous. -/
theorem continuous_unflatten : Continuous Ω.unflatten :=
  continuous_id.add (Ω.continuous_phi.smul continuous_const)

/-- **The inverse flattening is Lipschitz**: `y ↦ y + φ(y) e` is `(1 + M)`-Lipschitz, since `φ`
is `M`-Lipschitz and `‖e‖ = 1`. On the hyperplane `e^⊥` this is
`Rd.LipschitzGraph.norm_graphMap_sub_le`. -/
theorem lipschitzWith_unflatten :
    LipschitzWith ⟨1 + Ω.M, add_nonneg zero_le_one Ω.M_nonneg⟩ Ω.unflatten := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  change _ ≤ (1 + Ω.M) * _
  calc ‖Ω.unflatten x - Ω.unflatten y‖ = ‖(x - y) + (Ω.phi x - Ω.phi y) • Ω.e‖ := by
        rw [unflatten, unflatten, sub_smul]
        congr 1
        abel
    _ ≤ ‖x - y‖ + |Ω.phi x - Ω.phi y| := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs]
    _ ≤ (1 + Ω.M) * ‖x - y‖ := by linarith [Ω.lipschitz x y]

/-- **The flattening is Lipschitz**: `x ↦ x - φ(x) e` is `(1 + M)`-Lipschitz, since `φ` is
`M`-Lipschitz and `‖e‖ = 1`. -/
theorem lipschitzWith_flatten :
    LipschitzWith ⟨1 + Ω.M, add_nonneg zero_le_one Ω.M_nonneg⟩ Ω.flatten := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  change _ ≤ (1 + Ω.M) * _
  calc ‖Ω.flatten x - Ω.flatten y‖ = ‖(x - y) - (Ω.phi x - Ω.phi y) • Ω.e‖ := by
        rw [flatten, flatten, sub_smul]
        congr 1
        abel
    _ ≤ ‖x - y‖ + |Ω.phi x - Ω.phi y| := by
        refine (norm_sub_le _ _).trans_eq ?_
        rw [norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs]
    _ ≤ (1 + Ω.M) * ‖x - y‖ := by linarith [Ω.lipschitz x y]

/-- **The graph lies in the image of the hyperplane** `e^⊥` under `y ↦ y + φ(y) e`: a point `x`
of the graph is the image of its flattening `x - φ(x) e`, which lies in `e^⊥`
(`Rd.LipschitzGraph.inner_flatten`). -/
theorem graph_subset_image_unflatten :
    {x | Ω.phi x = inner ℝ x Ω.e} ⊆ Ω.unflatten '' ((ℝ ∙ Ω.e)ᗮ : Set V) := by
  intro x (hx : Ω.phi x = inner ℝ x Ω.e)
  refine ⟨Ω.flatten x, ?_, Ω.unflatten_flatten x⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm,
    Ω.inner_flatten, hx, sub_self]

/-- For smooth `φ`, the flattening is smooth. -/
theorem contDiff_flatten {n : WithTop ℕ∞} (hφ : ContDiff ℝ n Ω.phi) : ContDiff ℝ n Ω.flatten :=
  contDiff_id.sub (hφ.smul contDiff_const)

/-- For smooth `φ`, the inverse of the flattening is smooth. -/
theorem contDiff_unflatten {n : WithTop ℕ∞} (hφ : ContDiff ℝ n Ω.phi) :
    ContDiff ℝ n Ω.unflatten :=
  contDiff_id.add (hφ.smul contDiff_const)

/-- **`φ` does not change along `e`**: `Dφ(x) e = 0`. -/
theorem fderiv_phi_e {x : V} (hφ : DifferentiableAt ℝ Ω.phi x) : fderiv ℝ Ω.phi x Ω.e = 0 := by
  rw [← hφ.lineDeriv_eq_fderiv, lineDeriv]
  simp only [Ω.const, deriv_const]

/-- The derivative of the flattening, `id - e ⊗ Dφ(x)`. -/
theorem hasFDerivAt_flatten {x : V} (hφ : DifferentiableAt ℝ Ω.phi x) :
    HasFDerivAt Ω.flatten (ContinuousLinearMap.id ℝ V - (fderiv ℝ Ω.phi x).smulRight Ω.e) x :=
  (hasFDerivAt_id x).sub (hφ.hasFDerivAt.smul_const Ω.e)

/-- **The derivative of the flattening has determinant `1`**: it is the transvection
`y ↦ y + (-Dφ(x) y) e` with `Dφ(x) e = 0`. -/
theorem det_fderiv_flatten [FiniteDimensional ℝ V] {x : V} (hφ : DifferentiableAt ℝ Ω.phi x) :
    (ContinuousLinearMap.id ℝ V - (fderiv ℝ Ω.phi x).smulRight Ω.e).det = 1 := by
  have h : ((ContinuousLinearMap.id ℝ V - (fderiv ℝ Ω.phi x).smulRight Ω.e : V →L[ℝ] V) :
      V →ₗ[ℝ] V) = LinearMap.transvection (-(fderiv ℝ Ω.phi x : V →ₗ[ℝ] ℝ)) Ω.e := by
    ext y
    simp [LinearMap.transvection, sub_eq_add_neg]
  rw [ContinuousLinearMap.det, h, LinearMap.transvection.det]
  simp [Ω.fderiv_phi_e hφ]

/-! ### Product and graph coordinates -/

section Coordinates

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The isometry `t ↦ t e` of `ℝ` onto the orthogonal complement `H^⊥ = ℝ e` of the hyperplane
(Mathlib's `LinearIsometryEquiv.toSpanUnitSingleton`). -/
noncomputable def lineEquiv : ℝ ≃ₗᵢ[ℝ] Ω.hyperplaneᗮ :=
  (LinearIsometryEquiv.toSpanUnitSingleton Ω.e Ω.norm_e).trans
    (LinearIsometryEquiv.ofEq _ _ Ω.orthogonal_hyperplane.symm)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `lineEquiv t = t e`. -/
theorem coe_lineEquiv (t : ℝ) : (Ω.lineEquiv t : V) = t • Ω.e := rfl

/-- The **product coordinates** `(x', t) ↦ x' + t e` of `V = H ⊕ ℝ e`, as a measurable
equivalence (Mathlib's `Submodule.measurableEquivProd`). -/
noncomputable def prodEquiv : Ω.hyperplane × ℝ ≃ᵐ V :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    Ω.lineEquiv.toHomeomorph.toMeasurableEquiv).trans
    (Ω.hyperplane.measurableEquivProd (0 : V)).symm

/-- `prodEquiv (x', t) = x' + t e`. -/
theorem prodEquiv_apply (p : Ω.hyperplane × ℝ) : Ω.prodEquiv p = (p.1 : V) + p.2 • Ω.e := by
  simp [prodEquiv]
  rfl

/-- **The product coordinates preserve the Lebesgue measure**: `(x', t) ↦ x' + t e` carries the
product of the Lebesgue measures of `H` and `ℝ` to the Lebesgue measure of `V` (Mathlib's
`Submodule.measurePreserving_measurableEquivProd`,
`InnerProductSpace.euclideanHausdorffMeasure_eq_volume` and
`LinearIsometryEquiv.measurePreserving`). -/
theorem measurePreserving_prodEquiv :
    MeasurePreserving Ω.prodEquiv (volume.prod volume) volume := by
  have h1 := (Ω.hyperplane.measurePreserving_measurableEquivProd (0 : V)).symm
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h1
  exact h1.comp ((MeasurePreserving.id volume).prod Ω.lineEquiv.measurePreserving)

/-- The **shear** `(x', t) ↦ (x', t + φ(x'))` of `H × ℝ`, as a measurable equivalence. -/
noncomputable def graphShear : Ω.hyperplane × ℝ ≃ᵐ Ω.hyperplane × ℝ where
  toFun p := (p.1, p.2 + Ω.phiH p.1)
  invFun p := (p.1, p.2 - Ω.phiH p.1)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun :=
    measurable_fst.prodMk (measurable_snd.add (Ω.continuous_phiH.measurable.comp measurable_fst))
  measurable_invFun :=
    measurable_fst.prodMk (measurable_snd.sub (Ω.continuous_phiH.measurable.comp measurable_fst))

/-- The shear preserves the Lebesgue measure of `H × ℝ`: it translates each vertical line
(Mathlib's `MeasurePreserving.skew_product`). -/
theorem measurePreserving_graphShear :
    MeasurePreserving Ω.graphShear (volume.prod volume) (volume.prod volume) :=
  (MeasurePreserving.id volume).skew_product (g := fun x' t => t + Ω.phiH x')
    (measurable_snd.add (Ω.continuous_phiH.measurable.comp measurable_fst))
    (ae_of_all _ fun _ => map_add_right_eq_self volume _)

/-- The **graph coordinates** `(x', t) ↦ γ(x') + t e`, the product coordinates after the shear. -/
noncomputable def graphEquiv : Ω.hyperplane × ℝ ≃ᵐ V := Ω.graphShear.trans Ω.prodEquiv

/-- `graphEquiv (x', t) = γ(x') + t e`. -/
theorem graphEquiv_apply (p : Ω.hyperplane × ℝ) :
    Ω.graphEquiv p = Ω.graphMap p.1 + p.2 • Ω.e := by
  simp only [graphEquiv, MeasurableEquiv.trans_apply, prodEquiv_apply]
  change (p.1 : V) + (p.2 + Ω.phi p.1) • Ω.e = (p.1 : V) + Ω.phi p.1 • Ω.e + p.2 • Ω.e
  rw [add_smul]
  abel

/-- The graph coordinates preserve the Lebesgue measure. -/
theorem measurePreserving_graphEquiv :
    MeasurePreserving Ω.graphEquiv (volume.prod volume) volume :=
  Ω.measurePreserving_prodEquiv.comp Ω.measurePreserving_graphShear

/-! ### The flattening preserves the Lebesgue measure -/

/-- **The inverse flattening in coordinates**: `y ↦ y + φ(y) e` is the graph coordinates
`(x', t) ↦ γ(x') + t e` after the inverse of the product coordinates `(x', t) ↦ x' + t e`, since
`φ` is constant along `e`. -/
theorem unflatten_eq : Ω.unflatten = Ω.graphEquiv ∘ Ω.prodEquiv.symm := by
  funext y
  have hy : y = ((Ω.prodEquiv.symm y).1 : V) + (Ω.prodEquiv.symm y).2 • Ω.e := by
    rw [← prodEquiv_apply, MeasurableEquiv.apply_symm_apply]
  rw [Function.comp_apply, graphEquiv_apply, graphMap, unflatten]
  conv_lhs => rw [hy, Ω.const]
  abel

/-- **The flattening in coordinates**: `x ↦ x - φ(x) e` is the product coordinates after the
inverse of the graph coordinates (`Rd.LipschitzGraph.unflatten_eq`). -/
theorem flatten_eq : Ω.flatten = Ω.prodEquiv ∘ Ω.graphEquiv.symm := by
  funext x
  have h : Ω.unflatten (Ω.prodEquiv (Ω.graphEquiv.symm x)) = x := by
    rw [unflatten_eq, Function.comp_apply, MeasurableEquiv.symm_apply_apply,
      MeasurableEquiv.apply_symm_apply]
  conv_lhs => rw [← h]
  rw [Function.comp_apply, flatten_unflatten]

/-- **The inverse flattening preserves the Lebesgue measure** for every Lipschitz graph
(`Rd.LipschitzGraph.measurePreserving_graphEquiv`, `Rd.LipschitzGraph.measurePreserving_prodEquiv`):
it is a shear along `e` in the product coordinates. -/
theorem measurePreserving_unflatten : MeasurePreserving Ω.unflatten volume volume := by
  rw [unflatten_eq]
  exact Ω.measurePreserving_graphEquiv.comp Ω.measurePreserving_prodEquiv.symm

/-- **The flattening preserves the Lebesgue measure** for every Lipschitz graph, the inverse of
`Rd.LipschitzGraph.measurePreserving_unflatten`: it is the product coordinates after the inverse of
the graph coordinates (`Rd.LipschitzGraph.flatten_eq`). -/
theorem measurePreserving_flatten : MeasurePreserving Ω.flatten volume volume := by
  rw [flatten_eq]
  exact Ω.measurePreserving_prodEquiv.comp Ω.measurePreserving_graphEquiv.symm

end Coordinates

end LipschitzGraph

end Rd
