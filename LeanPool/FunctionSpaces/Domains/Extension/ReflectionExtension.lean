/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Extension.HalfSpaceReflection
public import LeanPool.FunctionSpaces.Domains.Extension.SobolevExtension
public import LeanPool.FunctionSpaces.Domains.Sobolev.LipschitzGraphGreen
public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphStraightening

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Extension by reflection

Let `Ω = {x : φ(x) < ⟪x, e⟫}` be a Lipschitz graph domain (`Rd.LipschitzGraph`) with the
flattening `F(x) = x - φ(x) e` and its inverse `F⁻¹(y) = y + φ(y) e`.

* **Flattening** (`Rd.LipschitzGraph.mapsTo_flatten`,
  `Rd.LipschitzGraph.mapsTo_unflatten_inter_ball`): `F` maps `Ω` into the half-space
  `H₊ = {⟪y, e⟫ > 0}` and `F⁻¹` maps `H₊ ∩ B(0, R)` into `Ω ∩ B(0, R')`. Both preserve Lebesgue
  measure (`Rd.LipschitzGraph.measurePreserving_flatten`,
  `Rd.LipschitzGraph.measurePreserving_unflatten`).
* **The extension by reflection** (`Rd.LipschitzGraph.reflectionExtension`): the even reflection
  (`Rd.evenReflection`) of `f ∘ F⁻¹` across `e^⊥`, composed with `F`. It is `f` on `Ω` and
  `f ∘ R` below the graph, for the graph reflection `R = F⁻¹ ∘ σ ∘ F`
  (`Rd.LipschitzGraph.reflect_eq`). It is linear (`Rd.LipschitzGraph.reflectionExtensionLinearMap`)
  and sees only the values on `Ω` (`Rd.LipschitzGraph.reflectionExtension_congr_ae`). If `f` and
  its weak derivatives on `Ω` are integrable on the bounded parts of `Ω`, it is weakly
  differentiable on `V` (`Rd.LipschitzGraph.hasWeakLineDeriv_reflectionExtension_of_integrableOn`,
  by the chain rule `Rd.HasWeakLineDeriv.comp_lipschitzWith` for `F⁻¹` and for `F`); for
  `1 ≤ p ≤ ∞` and `f ∈ W^1_p(Ω)`, with `‖E f‖_{L_p(V)} ≤ 2 ‖f‖_{L_p(Ω)}` and
  `‖∂_v E f‖_{L_p(V)} ≤ 2 (1 + M)² ‖v‖ ∑_i ‖∂_{e_i} f‖_{L_p(Ω)}`.
* **Bounded Lipschitz domains**: a boundary patch extends by a cutoff
  (`Rd.BoundedLipschitzDomain.hasWeakLineDeriv_mul_graph`) and the reflection in its graph domain
  with the constant `Rd.reflectionConst`
  (`Rd.BoundedLipschitzDomain.exists_hasWeakLineDeriv_reflectionExtension_mul`), the inner patch
  by a cutoff (`Rd.BoundedLipschitzDomain.exists_hasWeakLineDeriv_mul_interior`). These bounds
  give the extension operator by reflection and with it the extension theorem for every
  `1 ≤ p ≤ ∞` (Evans–Gariepy, Section 4.4), in
  `FunctionSpaces.Domains.Extension.ReflectionExtensionOperator`.
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Module Set Metric
open scoped ENNReal NNReal LineDeriv

namespace Rd

namespace LipschitzGraph

/-! ### Flattening a Lipschitz graph domain -/

section Flattening

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-- **The flattening maps the domain into the half-space** `H₊ = {⟪y, e⟫ > 0}`
(`Rd.LipschitzGraph.inner_flatten`). -/
theorem mapsTo_flatten : MapsTo Ω.flatten Ω.domain (openHalfSpace Ω.e) := fun x hx => by
  have hx' : Ω.phi x < inner ℝ x Ω.e := hx
  change 0 < inner ℝ (Ω.flatten x) Ω.e
  rw [Ω.inner_flatten]
  linarith

/-- **The inverse flattening maps the half-space into the domain**: `⟪y, e⟫ > 0` gives
`y + φ(y) e ∈ Ω`, since its flattening is `y`. -/
theorem mapsTo_unflatten : MapsTo Ω.unflatten (openHalfSpace Ω.e) Ω.domain := fun y hy => by
  have h := Ω.inner_flatten (Ω.unflatten y)
  rw [Ω.flatten_unflatten] at h
  have hy' : 0 < inner ℝ y Ω.e := hy
  change Ω.phi (Ω.unflatten y) < inner ℝ (Ω.unflatten y) Ω.e
  linarith

/-- **The inverse flattening on bounded parts**: `F⁻¹` maps `H₊ ∩ B(0, R)` into
`Ω ∩ B(0, ‖F⁻¹ 0‖ + (1 + M) R)`, since it is `(1 + M)`-Lipschitz (Mathlib's
`LipschitzWith.mapsTo_ball`). -/
theorem mapsTo_unflatten_inter_ball (R : ℝ) :
    MapsTo Ω.unflatten ((openHalfSpace Ω.e : Set V) ∩ ball 0 R)
      (Ω.domain ∩ ball 0 (‖Ω.unflatten 0‖ + (1 + Ω.M) * R)) := fun y hy => by
  have hK : (⟨1 + Ω.M, add_nonneg zero_le_one Ω.M_nonneg⟩ : ℝ≥0) ≠ 0 := fun h => by
    have h' : (1 + Ω.M : ℝ) = ((0 : ℝ≥0) : ℝ) := congrArg NNReal.toReal h
    rw [NNReal.coe_zero] at h'
    linarith [Ω.M_nonneg]
  refine ⟨Ω.mapsTo_unflatten hy.1, ball_subset_ball' ?_
    (Ω.lipschitzWith_unflatten.mapsTo_ball hK 0 R hy.2)⟩
  change (1 + Ω.M) * R + dist (Ω.unflatten 0) 0 ≤ ‖Ω.unflatten 0‖ + (1 + Ω.M) * R
  rw [dist_zero_right, add_comm]

end Flattening

/-! ### The reflection across the graph -/

section Reflection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-- The **reflection across the graph** `x ↦ x + 2(φ(x) - ⟪x, e⟫) e`: it moves `x` along `e` to the
point at the same distance on the other side of the graph. -/
def reflect (x : V) : V := x + (2 * (Ω.phi x - inner ℝ x Ω.e)) • Ω.e

/-- **The graph reflection in flat coordinates**: it is the reflection `σ` across the hyperplane
`e^⊥` after the flattening, followed by the inverse flattening. -/
theorem reflect_eq : Ω.reflect = Ω.unflatten ∘ halfSpaceReflection Ω.e ∘ Ω.flatten := by
  funext x
  simp only [Function.comp_apply, reflect, unflatten]
  rw [halfSpaceReflection_apply Ω.norm_e, Ω.inner_flatten]
  have hφ : Ω.phi (Ω.flatten x - (2 * (inner ℝ x Ω.e - Ω.phi x)) • Ω.e) = Ω.phi x := by
    rw [Ω.phi_sub_smul, flatten, Ω.phi_sub_smul]
  rw [hφ, flatten]
  module

/-- The graph reflection is an involution. -/
theorem reflect_reflect (x : V) : Ω.reflect (Ω.reflect x) = x := by
  simp only [reflect_eq, Function.comp_apply, flatten_unflatten,
    halfSpaceReflection_halfSpaceReflection, unflatten_flatten]

/-- The **extension by reflection** of a function `u` on the graph domain `Ω`: the even reflection
(`Rd.evenReflection`) of `u ∘ F⁻¹` across `e^⊥` in the flat coordinates `F(x) = x - φ(x) e`, that
is `u` on `Ω` (`Rd.LipschitzGraph.reflectionExtension_of_mem`) and `u` after the graph reflection
below the graph (`Rd.LipschitzGraph.reflectionExtension_of_lt`). -/
noncomputable def reflectionExtension (u : V → ℂ) : V → ℂ :=
  evenReflection Ω.e (u ∘ Ω.unflatten) ∘ Ω.flatten

/-- On the graph domain the extension by reflection of `u` is `u`. -/
theorem reflectionExtension_of_mem (u : V → ℂ) {x : V} (hx : x ∈ Ω.domain) :
    Ω.reflectionExtension u x = u x := by
  rw [reflectionExtension, Function.comp_apply,
    evenReflection_of_mem Ω.norm_e _ (Ω.mapsTo_flatten hx), Function.comp_apply,
    unflatten_flatten]

/-- Below the graph, `⟪x, e⟫ < φ(x)`, the extension by reflection of `u` is `u` at the reflected
point. -/
theorem reflectionExtension_of_lt (u : V → ℂ) {x : V} (hx : inner ℝ x Ω.e < Ω.phi x) :
    Ω.reflectionExtension u x = u (Ω.reflect x) := by
  have h : halfSpaceReflection Ω.e (Ω.flatten x) ∈ openHalfSpace Ω.e := by
    change 0 < inner ℝ (halfSpaceReflection Ω.e (Ω.flatten x)) Ω.e
    rw [inner_halfSpaceReflection Ω.norm_e, Ω.inner_flatten]
    linarith
  rw [reflectionExtension, Function.comp_apply, evenReflection_of_reflection_mem Ω.norm_e _ h,
    reflect_eq]
  rfl

/-- The extension by reflection is additive (`Rd.evenReflection_add`). -/
theorem reflectionExtension_add (u u' : V → ℂ) :
    Ω.reflectionExtension (u + u') = Ω.reflectionExtension u + Ω.reflectionExtension u' := by
  simp only [reflectionExtension]
  rw [show (u + u') ∘ Ω.unflatten = u ∘ Ω.unflatten + u' ∘ Ω.unflatten from rfl,
    evenReflection_add]
  rfl

/-- The extension by reflection is homogeneous (`Rd.evenReflection_smul`). -/
theorem reflectionExtension_smul (c : ℂ) (u : V → ℂ) :
    Ω.reflectionExtension (c • u) = c • Ω.reflectionExtension u := by
  simp only [reflectionExtension]
  rw [show (c • u) ∘ Ω.unflatten = c • (u ∘ Ω.unflatten) from rfl, evenReflection_smul]
  rfl

/-- **The extension by reflection as a linear map** on functions `V → ℂ`. -/
noncomputable def reflectionExtensionLinearMap : (V → ℂ) →ₗ[ℂ] V → ℂ where
  toFun := Ω.reflectionExtension
  map_add' := Ω.reflectionExtension_add
  map_smul' := Ω.reflectionExtension_smul

/-- The linear map of the extension by reflection is the extension by reflection. -/
theorem reflectionExtensionLinearMap_apply (u : V → ℂ) :
    Ω.reflectionExtensionLinearMap u = Ω.reflectionExtension u :=
  rfl

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The graph reflection preserves the Lebesgue measure (`Rd.LipschitzGraph.reflect_eq`). -/
theorem measurePreserving_reflect : MeasurePreserving Ω.reflect volume volume := by
  rw [reflect_eq]
  exact Ω.measurePreserving_unflatten.comp
    ((measurePreserving_halfSpaceReflection Ω.e).comp Ω.measurePreserving_flatten)

/-- **The extension by reflection sees only the values on the graph domain**: if `u = u'` almost
everywhere on the graph domain, then their extensions by reflection agree almost everywhere on
`V`, since the inverse flattening maps `H₊` into the graph domain and the flattening, its inverse
and `σ` preserve Lebesgue measure (Mathlib's
`MeasureTheory.QuasiMeasurePreserving.ae_eq_comp`). -/
theorem reflectionExtension_congr_ae {u u' : V → ℂ} (h : u =ᵐ[volume.restrict Ω.domain] u') :
    Ω.reflectionExtension u =ᵐ[volume] Ω.reflectionExtension u' := by
  have hH := (openHalfSpace Ω.e).isOpen.measurableSet
  have h1 : u ∘ Ω.unflatten =ᵐ[volume.restrict (openHalfSpace Ω.e)] u' ∘ Ω.unflatten := by
    refine (ae_restrict_iff' hH).2 ?_
    filter_upwards [Ω.measurePreserving_unflatten.quasiMeasurePreserving.ae
      ((ae_restrict_iff' Ω.measurableSet_domain).1 h)] with y hy hyH
    exact hy (Ω.mapsTo_unflatten hyH)
  have h2 := (ae_eq_restrict_iff_indicator_ae_eq hH).1 h1
  have h3 : evenReflection Ω.e (u ∘ Ω.unflatten) =ᵐ[volume]
      evenReflection Ω.e (u' ∘ Ω.unflatten) :=
    h2.add ((measurePreserving_halfSpaceReflection Ω.e).quasiMeasurePreserving.ae_eq_comp h2)
  exact Ω.measurePreserving_flatten.quasiMeasurePreserving.ae_eq_comp h3

end Reflection

/-! ### The weak derivatives of the extension by reflection -/

section Derivatives

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (Ω : LipschitzGraph V)

/-- The **derivative in flat coordinates**: for the derivatives `g_i = ∂_{e_i} f` on `Ω`, the
function `y ↦ ∑_i ⟪DF⁻¹(y) w, e_i⟫ g_i(F⁻¹ y)` with the inverse flattening `F⁻¹(y) = y + φ(y) e`;
it is the weak derivative `∂_w (f ∘ F⁻¹)` on `H₊`
(`Rd.LipschitzGraph.hasWeakLineDeriv_comp_unflatten`). -/
noncomputable def flatDeriv (g : Fin (finrank ℝ V) → V → ℂ) (w y : V) : ℂ :=
  ∑ i, (inner ℝ (fderiv ℝ Ω.unflatten y w) (gridBasis V i) : ℂ) * g i (Ω.unflatten y)

variable {g : Fin (finrank ℝ V) → V → ℂ}

/-- The derivative in flat coordinates is linear in the direction:
`D_{∑ c_k w_k} = ∑_k c_k D_{w_k}`. -/
theorem flatDeriv_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → V) (y : V) :
    Ω.flatDeriv g (∑ k ∈ s, c k • w k) y = ∑ k ∈ s, (c k : ℂ) * Ω.flatDeriv g (w k) y := by
  simp only [flatDeriv, map_sum, map_smul, sum_inner, real_inner_smul_left, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- **The derivative in flat coordinates through the basis**: for a linear map `T`,
`∑_k ⟪a, e_k⟫ D_{T e_k} = D_{T a}`, since `a = ∑_k ⟪a, e_k⟫ e_k` (Mathlib's
`OrthonormalBasis.sum_repr'`). -/
theorem sum_inner_mul_flatDeriv (T : V →ₗ[ℝ] V) (a y : V) :
    ∑ k, (inner ℝ a (gridBasis V k) : ℂ) * Ω.flatDeriv g (T (gridBasis V k)) y =
      Ω.flatDeriv g (T a) y := by
  conv_rhs => rw [← (gridBasis V).sum_repr' a]
  rw [map_sum]
  simp_rw [map_smul]
  rw [flatDeriv_sum_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm]

/-- **The pointwise bound of the derivative in flat coordinates**:
`|D_w(y)| ≤ (1 + M) ‖w‖ ∑_i |g_i(F⁻¹ y)|`, since `F⁻¹` is `(1 + M)`-Lipschitz (Mathlib's
`norm_fderiv_le_of_lipschitz`) and `‖e_i‖ = 1`. -/
theorem norm_flatDeriv_le (w y : V) :
    ‖Ω.flatDeriv g w y‖ ≤ (1 + Ω.M) * ‖w‖ * ∑ i, ‖g i (Ω.unflatten y)‖ := by
  rw [flatDeriv, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real]
  gcongr
  calc ‖inner ℝ (fderiv ℝ Ω.unflatten y w) (gridBasis V i)‖
      ≤ ‖fderiv ℝ Ω.unflatten y w‖ * ‖gridBasis V i‖ := norm_inner_le_norm _ _
    _ = ‖fderiv ℝ Ω.unflatten y w‖ := by rw [(gridBasis V).orthonormal.1 i, mul_one]
    _ ≤ ‖fderiv ℝ Ω.unflatten y‖ * ‖w‖ := (fderiv ℝ Ω.unflatten y).le_opNorm w
    _ ≤ (1 + Ω.M) * ‖w‖ := by
        gcongr
        exact norm_fderiv_le_of_lipschitz ℝ Ω.lipschitzWith_unflatten

/-- The **derivative of the extension by reflection** along `v`: with `a = DF(x) v` for the
flattening `F`, `x ↦ 1_{H₊}(D_a)(F x) + 1_{H₊}(D_{σ a})(σ F x)`, where `D_w` is the derivative in
flat coordinates (`Rd.LipschitzGraph.flatDeriv`) and `σ` the reflection across `e^⊥`. It is the
weak derivative `∂_v` of the extension by reflection on `V`
(`Rd.LipschitzGraph.hasWeakLineDeriv_reflectionExtension`). -/
noncomputable def reflectionDeriv (g : Fin (finrank ℝ V) → V → ℂ) (v x : V) : ℂ :=
  (openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g (fderiv ℝ Ω.flatten x v)) (Ω.flatten x) +
    (openHalfSpace Ω.e : Set V).indicator
      (Ω.flatDeriv g (halfSpaceReflection Ω.e (fderiv ℝ Ω.flatten x v)))
      (halfSpaceReflection Ω.e (Ω.flatten x))

/-- **The chain rule collapses the basis sum**: for every `a` and `y`,
`∑_k ⟪a, e_k⟫ (1_{H₊}(D_{e_k})(y) + 1_{H₊}(D_{σ e_k})(σ y)) = 1_{H₊}(D_a)(y) + 1_{H₊}(D_{σ a})(σ y)`
(`Rd.LipschitzGraph.sum_inner_mul_flatDeriv` for the identity and for `σ`). -/
theorem sum_inner_mul_indicator_flatDeriv (a y : V) :
    ∑ k, (inner ℝ a (gridBasis V k) : ℂ) *
        ((openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g (gridBasis V k)) y +
          (openHalfSpace Ω.e : Set V).indicator
            (Ω.flatDeriv g (halfSpaceReflection Ω.e (gridBasis V k))) (halfSpaceReflection Ω.e y)) =
      (openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g a) y +
        (openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g (halfSpaceReflection Ω.e a))
          (halfSpaceReflection Ω.e y) := by
  have hind : ∀ (T : V →ₗ[ℝ] V) (z : V), ∑ k, (inner ℝ a (gridBasis V k) : ℂ) *
      (openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g (T (gridBasis V k))) z =
      (openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g (T a)) z := fun T z => by
    by_cases hz : z ∈ (openHalfSpace Ω.e : Set V)
    · simp only [indicator_of_mem hz]
      exact Ω.sum_inner_mul_flatDeriv T a z
    · simp only [indicator_of_notMem hz, mul_zero, Finset.sum_const_zero]
  have h1 := hind LinearMap.id y
  have h2 := hind (halfSpaceReflection Ω.e).toLinearEquiv.toLinearMap (halfSpaceReflection Ω.e y)
  simp only [LinearMap.id_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    at h1 h2
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h1, h2]

/-- **The pointwise bound of the reflection derivative**: with `S(y) = ∑_i |g_i(F⁻¹ y)|`,
`|∂_v E(x)| ≤ (1 + M)² ‖v‖ (1_{H₊}(S)(F x) + 1_{H₊}(S)(σ F x))`, since `‖DF(x) v‖ ≤ (1 + M) ‖v‖`,
`σ` preserves norms and `Rd.LipschitzGraph.norm_flatDeriv_le`. -/
theorem norm_reflectionDeriv_le (v x : V) :
    ‖Ω.reflectionDeriv g v x‖ ≤ (1 + Ω.M) ^ 2 * ‖v‖ *
      ((openHalfSpace Ω.e : Set V).indicator (fun y => ∑ i, ‖g i (Ω.unflatten y)‖) (Ω.flatten x) +
        (openHalfSpace Ω.e : Set V).indicator (fun y => ∑ i, ‖g i (Ω.unflatten y)‖)
          (halfSpaceReflection Ω.e (Ω.flatten x))) := by
  have hM : 0 ≤ 1 + Ω.M := add_nonneg zero_le_one Ω.M_nonneg
  have hA : ‖fderiv ℝ Ω.flatten x v‖ ≤ (1 + Ω.M) * ‖v‖ :=
    ((fderiv ℝ Ω.flatten x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ Ω.lipschitzWith_flatten)
        (norm_nonneg v))
  have hb : ∀ w y : V, ‖w‖ ≤ (1 + Ω.M) * ‖v‖ →
      ‖(openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g w) y‖ ≤ (1 + Ω.M) ^ 2 * ‖v‖ *
        (openHalfSpace Ω.e : Set V).indicator (fun y => ∑ i, ‖g i (Ω.unflatten y)‖) y := by
    intro w y hw
    by_cases hy : y ∈ (openHalfSpace Ω.e : Set V)
    · rw [indicator_of_mem hy, indicator_of_mem hy]
      calc _ ≤ (1 + Ω.M) * ‖w‖ * ∑ i, ‖g i (Ω.unflatten y)‖ := Ω.norm_flatDeriv_le w y
        _ ≤ (1 + Ω.M) * ((1 + Ω.M) * ‖v‖) * ∑ i, ‖g i (Ω.unflatten y)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hM)
              (Finset.sum_nonneg fun i _ => norm_nonneg _)
        _ = _ := by ring
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, norm_zero, mul_zero]
  rw [reflectionDeriv, mul_add]
  refine (norm_add_le _ _).trans (add_le_add (hb _ _ hA) (hb _ _ ?_))
  rwa [LinearIsometryEquiv.norm_map]

variable [MeasurableSpace V] [BorelSpace V]

/-- **Weak derivatives in flat coordinates**: if `g_i = ∂_{e_i} f` weakly on `Ω`, then the
derivative in flat coordinates `Rd.LipschitzGraph.flatDeriv` is the weak derivative
`∂_w (f ∘ F⁻¹)` on `H₊` (the chain rule `Rd.HasWeakLineDeriv.comp_lipschitzWith` for the
measure-preserving Lipschitz map `F⁻¹`). -/
theorem hasWeakLineDeriv_comp_unflatten {f : V → ℂ}
    (hfg : ∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) f (g i)) (w : V) :
    HasWeakLineDeriv (openHalfSpace Ω.e) (fun _ : Fin 1 => w) (f ∘ Ω.unflatten)
      (Ω.flatDeriv g w) :=
  HasWeakLineDeriv.comp_lipschitzWith hfg Ω.lipschitzWith_unflatten Ω.measurePreserving_unflatten
    Ω.mapsTo_unflatten w

/-- **The `L_p` bound in flat coordinates**: for `1 ≤ p`,
`‖D_w‖_{L_p(H₊)} ≤ (1 + M) ‖w‖ ∑_i ‖g_i‖_{L_p(Ω)}` (`Rd.eLpNorm_sum_inner_fderiv_mul_comp_le`). -/
theorem eLpNorm_flatDeriv_le {p : ℝ≥0∞} (hp : 1 ≤ p) (w : V) :
    eLpNorm (Ω.flatDeriv g w) p (volume.restrict (openHalfSpace Ω.e)) ≤
      ENNReal.ofReal (1 + Ω.M) * ‖w‖ₑ * ∑ i, eLpNorm (g i) p (volume.restrict Ω.domain) := by
  have h := eLpNorm_sum_inner_fderiv_mul_comp_le hp Ω.lipschitzWith_unflatten
    Ω.measurePreserving_unflatten Ω.measurableSet_domain Ω.mapsTo_unflatten w g
  rwa [ENNReal.ofReal_eq_coe_nnreal (add_nonneg zero_le_one Ω.M_nonneg)]

/-- **Functions in flat coordinates**: for `f ∈ L_p(Ω)`, `f ∘ F⁻¹ ∈ L_p(H₊)` with
`‖f ∘ F⁻¹‖_{L_p(H₊)} ≤ ‖f‖_{L_p(Ω)}` (`Rd.eLpNorm_comp_le_of_mapsTo`). -/
theorem memLp_comp_unflatten {p : ℝ≥0∞} {f : V → ℂ} (hf : MemLp f p (volume.restrict Ω.domain)) :
    MemLp (f ∘ Ω.unflatten) p (volume.restrict (openHalfSpace Ω.e)) :=
  memLp_iff.2 ((eLpNorm_comp_le_of_mapsTo Ω.measurePreserving_unflatten Ω.measurableSet_domain
    Ω.mapsTo_unflatten p).trans_lt hf)

/-- The derivatives in flat coordinates of `L_p` derivatives lie in `L_p(H₊)`
(`Rd.LipschitzGraph.eLpNorm_flatDeriv_le`). -/
theorem memLp_flatDeriv {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hg : ∀ i, MemLp (g i) p (volume.restrict Ω.domain)) (w : V) :
    MemLp (Ω.flatDeriv g w) p (volume.restrict (openHalfSpace Ω.e)) :=
  memLp_iff.2 ((Ω.eLpNorm_flatDeriv_le hp w).trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top eNorm_lt_top)
    (ENNReal.sum_lt_top.2 fun i _ => hg i)))

/-- **Functions in flat coordinates on bounded parts**: if `f` is integrable on every bounded part
`Ω ∩ B(0, R)` of `Ω`, then `f ∘ F⁻¹` is integrable on every bounded part `H₊ ∩ B(0, R)` of `H₊`
(`Rd.LipschitzGraph.mapsTo_unflatten_inter_ball`, `Rd.eLpNorm_comp_le_of_mapsTo`). -/
theorem integrableOn_comp_unflatten_inter_ball {f : V → ℂ}
    (hf : ∀ R, IntegrableOn f (Ω.domain ∩ ball 0 R)) (R : ℝ) :
    IntegrableOn (f ∘ Ω.unflatten) ((openHalfSpace Ω.e : Set V) ∩ ball 0 R) :=
  memLp_one_iff_integrable.1 (memLp_iff.2 ((eLpNorm_comp_le_of_mapsTo Ω.measurePreserving_unflatten
    (Ω.measurableSet_domain.inter measurableSet_ball) (Ω.mapsTo_unflatten_inter_ball R) 1).trans_lt
      (memLp_one_iff_integrable.2 (hf _)).eLpNorm_lt_top))

/-- **Derivatives in flat coordinates on bounded parts**: if every `g_i` is integrable on every
bounded part `Ω ∩ B(0, R)` of `Ω`, then every `D_w` is integrable on every bounded part
`H₊ ∩ B(0, R)` of `H₊` (`Rd.eLpNorm_sum_inner_fderiv_mul_comp_le` for `p = 1`). -/
theorem integrableOn_flatDeriv_inter_ball
    (hg : ∀ i R, IntegrableOn (g i) (Ω.domain ∩ ball 0 R)) (w : V) (R : ℝ) :
    IntegrableOn (Ω.flatDeriv g w) ((openHalfSpace Ω.e : Set V) ∩ ball 0 R) := by
  have h := eLpNorm_sum_inner_fderiv_mul_comp_le le_rfl Ω.lipschitzWith_unflatten
    Ω.measurePreserving_unflatten (Ω.measurableSet_domain.inter measurableSet_ball)
    (Ω.mapsTo_unflatten_inter_ball R) w g
  exact memLp_one_iff_integrable.1 (memLp_iff.2 (h.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.coe_lt_top eNorm_lt_top)
    (ENNReal.sum_lt_top.2 fun i _ => (memLp_one_iff_integrable.2 (hg i _)).eLpNorm_lt_top))))

/-- **The extension by reflection is weakly differentiable** (Evans–Gariepy, Section 4.4): if
`g_i = ∂_{e_i} f` weakly on the graph domain `Ω` and `f` and the `g_i` are integrable on every
bounded part `Ω ∩ B(0, R)` of `Ω`, then for every `v ∈ V` the derivative
`Rd.LipschitzGraph.reflectionDeriv` is the weak derivative `∂_v` of the extension by reflection on
`V`. The chain rule for the inverse flattening
(`Rd.LipschitzGraph.hasWeakLineDeriv_comp_unflatten`), the even reflection on the half-space
(`Rd.hasWeakLineDeriv_evenReflection_of_forall`) and the chain rule for the flattening
(`Rd.HasWeakLineDeriv.comp_lipschitzWith`) give it as a basis sum, which collapses by
`Rd.LipschitzGraph.sum_inner_mul_indicator_flatDeriv`. -/
theorem hasWeakLineDeriv_reflectionExtension_of_integrableOn {f : V → ℂ}
    (hf : ∀ R, IntegrableOn f (Ω.domain ∩ ball 0 R))
    (hg : ∀ i R, IntegrableOn (g i) (Ω.domain ∩ ball 0 R))
    (hfg : ∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) f (g i)) (v : V) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (Ω.reflectionExtension f) (Ω.reflectionDeriv g v) := by
  have hE : ∀ w, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => w) (evenReflection Ω.e (f ∘ Ω.unflatten))
      (fun y => (openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g w) y +
        (openHalfSpace Ω.e : Set V).indicator (Ω.flatDeriv g (halfSpaceReflection Ω.e w))
          (halfSpaceReflection Ω.e y)) := fun w =>
    hasWeakLineDeriv_evenReflection_of_forall Ω.norm_e
      (Ω.integrableOn_comp_unflatten_inter_ball hf)
      (fun w => Ω.integrableOn_flatDeriv_inter_ball hg w)
      (Ω.hasWeakLineDeriv_comp_unflatten hfg) w
  have h := HasWeakLineDeriv.comp_lipschitzWith (O := ⊤) (U := ⊤) (fun k => hE (gridBasis V k))
    Ω.lipschitzWith_flatten Ω.measurePreserving_flatten (fun _ _ => trivial) v
  exact h.congr_ae EventuallyEq.rfl (ae_of_all _ fun x =>
    Ω.sum_inner_mul_indicator_flatDeriv _ _)

/-- **The extension by reflection of `W^1_p` functions**: for `1 ≤ p`, `f ∈ L_p(Ω)` with weak
derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` on the graph domain `Ω`, and every `v ∈ V`, the derivative
`Rd.LipschitzGraph.reflectionDeriv` is the weak derivative `∂_v` of the extension by reflection on
`V` (`Rd.LipschitzGraph.hasWeakLineDeriv_reflectionExtension_of_integrableOn`; `L_p` functions are
integrable on the bounded parts, `Rd.integrableOn_inter_ball_of_memLp`). -/
theorem hasWeakLineDeriv_reflectionExtension {p : ℝ≥0∞} (hp : 1 ≤ p) {f : V → ℂ}
    (hf : MemLp f p (volume.restrict Ω.domain)) (hg : ∀ i, MemLp (g i) p (volume.restrict Ω.domain))
    (hfg : ∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) f (g i)) (v : V) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) (Ω.reflectionExtension f) (Ω.reflectionDeriv g v) :=
  Ω.hasWeakLineDeriv_reflectionExtension_of_integrableOn (integrableOn_inter_ball_of_memLp hp hf)
    (fun i => integrableOn_inter_ball_of_memLp hp (hg i)) hfg v

/-- **The `L_p` norm of the extension by reflection**: `‖E f‖_{L_p(V)} ≤ 2 ‖f‖_{L_p(Ω)}` for
`1 ≤ p` (`Rd.eLpNorm_evenReflection_le`; the flattening and its inverse preserve Lebesgue
measure). -/
theorem eLpNorm_reflectionExtension_le {p : ℝ≥0∞} (hp : 1 ≤ p) (f : V → ℂ) :
    eLpNorm (Ω.reflectionExtension f) p volume ≤ 2 * eLpNorm f p (volume.restrict Ω.domain) := by
  have h1 := eLpNorm_comp_le_of_mapsTo (h := evenReflection Ω.e (f ∘ Ω.unflatten)) (U := univ)
    Ω.measurePreserving_flatten MeasurableSet.univ (mapsTo_univ _ _) p
  rw [Measure.restrict_univ] at h1
  calc eLpNorm (Ω.reflectionExtension f) p volume
      ≤ eLpNorm (evenReflection Ω.e (f ∘ Ω.unflatten)) p volume := h1
    _ ≤ 2 * eLpNorm (f ∘ Ω.unflatten) p (volume.restrict (openHalfSpace Ω.e)) :=
        eLpNorm_evenReflection_le hp _
    _ ≤ 2 * eLpNorm f p (volume.restrict Ω.domain) := by
        gcongr
        exact eLpNorm_comp_le_of_mapsTo Ω.measurePreserving_unflatten Ω.measurableSet_domain
          Ω.mapsTo_unflatten p

/-- The `L_p` norm of `y ↦ ∑_i |g_i(F⁻¹ y)|` on `H₊` is at most `∑_i ‖g_i‖_{L_p(Ω)}` for `1 ≤ p`
and `g_i ∈ L_p(Ω)` (Minkowski's inequality and `Rd.eLpNorm_comp_le_of_mapsTo`). -/
theorem eLpNorm_sum_norm_comp_unflatten_le {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hg : ∀ i, MemLp (g i) p (volume.restrict Ω.domain)) :
    eLpNorm (fun y => ∑ i, ‖g i (Ω.unflatten y)‖) p (volume.restrict (openHalfSpace Ω.e)) ≤
      ∑ i, eLpNorm (g i) p (volume.restrict Ω.domain) := by
  have h1 := eLpNorm_comp_le_of_mapsTo (h := fun z => ∑ i, ‖g i z‖) Ω.measurePreserving_unflatten
    Ω.measurableSet_domain Ω.mapsTo_unflatten p
  have hfun : (fun z => ∑ i, ‖g i z‖) = ∑ i, fun z => ‖g i z‖ := by
    funext z
    simp [Finset.sum_apply]
  refine h1.trans ?_
  rw [hfun]
  refine (eLpNorm_sum_le hp).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  exact eLpNorm_norm _ (hg i).aestronglyMeasurable

/-- **The `L_p` bound of the reflection derivative**: for `1 ≤ p`, `f ∈ L_p(Ω)` with weak
derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` on `Ω`, and every `v ∈ V`, the reflection derivative
`Rd.LipschitzGraph.reflectionDeriv g v` (the weak derivative `∂_v` of the extension by reflection)
satisfies `‖Rd.LipschitzGraph.reflectionDeriv g v‖_{L_p(V)} ≤ 2 (1 + M)² ‖v‖ ∑_i ‖g_i‖_{L_p(Ω)}`;
the hypotheses give its measurability. The proof uses the pointwise bound
`Rd.LipschitzGraph.norm_reflectionDeriv_le`, the measure-preserving flattening and
`Rd.eLpNorm_indicator_add_indicator_comp_halfSpaceReflection_le`. -/
theorem eLpNorm_reflectionDeriv_le {p : ℝ≥0∞} (hp : 1 ≤ p) {f : V → ℂ}
    (hf : MemLp f p (volume.restrict Ω.domain)) (hg : ∀ i, MemLp (g i) p (volume.restrict Ω.domain))
    (hfg : ∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) f (g i)) (v : V) :
    eLpNorm (Ω.reflectionDeriv g v) p volume ≤
      2 * ENNReal.ofReal ((1 + Ω.M) ^ 2) * ‖v‖ₑ *
        ∑ i, eLpNorm (g i) p (volume.restrict Ω.domain) := by
  have hm : AEStronglyMeasurable (Ω.reflectionDeriv g v) volume :=
    (Ω.hasWeakLineDeriv_reflectionExtension hp hf hg hfg
      v).locallyIntegrable_deriv.aestronglyMeasurable
  have hc : 0 ≤ (1 + Ω.M) ^ 2 * ‖v‖ := by positivity
  set S : V → ℝ := fun y => ∑ i, ‖g i (Ω.unflatten y)‖
  set Ψ : V → ℝ := fun y => (openHalfSpace Ω.e : Set V).indicator S y +
    (openHalfSpace Ω.e : Set V).indicator S (halfSpaceReflection Ω.e y)
  have h1 := eLpNorm_comp_le_of_mapsTo (h := Ψ) (U := univ)
    Ω.measurePreserving_flatten MeasurableSet.univ (mapsTo_univ _ _) p
  rw [Measure.restrict_univ] at h1
  calc eLpNorm (Ω.reflectionDeriv g v) p volume
      ≤ eLpNorm (((1 + Ω.M) ^ 2 * ‖v‖) • (Ψ ∘ Ω.flatten)) p volume :=
        eLpNorm_mono_real hm fun x => (Ω.norm_reflectionDeriv_le v x).trans_eq rfl
    _ ≤ ‖(1 + Ω.M) ^ 2 * ‖v‖‖ₑ * eLpNorm Ψ p volume :=
        eLpNorm_const_smul_le.trans (by gcongr)
    _ ≤ ‖(1 + Ω.M) ^ 2 * ‖v‖‖ₑ * (∑ i, eLpNorm (g i) p (volume.restrict Ω.domain) +
          ∑ i, eLpNorm (g i) p (volume.restrict Ω.domain)) := by
        gcongr
        refine (eLpNorm_indicator_add_indicator_comp_halfSpaceReflection_le hp
          (openHalfSpace Ω.e).isOpen.measurableSet S S).trans ?_
        gcongr <;> exact Ω.eLpNorm_sum_norm_comp_unflatten_le hp hg
    _ = _ := by
        rw [Real.eNorm_eq_ofReal hc, ENNReal.ofReal_mul (by positivity), ofReal_norm]
        ring

end Derivatives

end LipschitzGraph

/-! ### The patches of bounded Lipschitz domains -/

section BoundedDomains

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞}

/-- **The arithmetic of the reflection bound**: if `a ≤ 2X` and `b_k ≤ K (Y + dX)` for all `k`,
then `a + ∑_k b_k ≤ (2 + N K (1 + d)) (X + Y)` with `N` the number of indices. -/
theorem add_sum_le_of_le_two_mul {ι : Type*} [Fintype ι] {a X Y K d : ℝ≥0∞} {b : ι → ℝ≥0∞}
    (ha : a ≤ 2 * X) (hb : ∀ k, b k ≤ K * (Y + d * X)) :
    a + ∑ k, b k ≤ (2 + Fintype.card ι * K * (1 + d)) * (X + Y) := by
  calc a + ∑ k, b k ≤ 2 * X + Fintype.card ι * (K * (Y + d * X)) := by
        refine add_le_add ha ((Finset.sum_le_sum fun k _ => hb k).trans_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 * X + Fintype.card ι * (K * (Y + d * X))) +
          (2 * Y + Fintype.card ι * K * (X + d * Y)) := le_self_add
    _ = _ := by ring

/-- The **constant of the boundary patches by reflection**: `2 + 2 n (1 + M)² (1 + d)` for the
dimension `n`, the Lipschitz constant `M` of the graph and the sum `d` of the bounds of the
derivatives of the cutoff
(`Rd.BoundedLipschitzDomain.exists_hasWeakLineDeriv_reflectionExtension_mul`). -/
noncomputable def reflectionConst (n : ℕ) (M : ℝ) (d : ℝ≥0∞) : ℝ≥0∞ :=
  2 + n * (2 * ENNReal.ofReal ((1 + M) ^ 2)) * (1 + d)

/-- The constant of the boundary patches by reflection is finite for finite `d`. -/
theorem reflectionConst_ne_top (n : ℕ) (M : ℝ) {d : ℝ≥0∞} (hd : d ≠ ∞) :
    reflectionConst n M d ≠ ∞ := by
  simp [reflectionConst, ENNReal.mul_eq_top, hd]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The graph domain near a boundary ball lies in `Ω`**: `Ω_j ∩ B(c_j, ρ_j) ⊆ Ω` as open sets
(`Rd.BoundedLipschitzDomain.inter_ball_eq`). -/
theorem graph_toOpens_inf_ball_le (j : Fin Ω.N) :
    ((Ω.graph j).toOpens ⊓ ⟨ball (Ω.center j) (Ω.radius j), isOpen_ball⟩ : Opens V) ≤
      Ω.toOpens := fun x hx => by
  have hx' : x ∈ (Ω.graph j).domain ∩ ball (Ω.center j) (Ω.radius j) := hx
  rw [← Ω.inter_ball_eq j le_rfl] at hx'
  exact hx'.1

/-- **Cutoffs carry weak derivatives from `Ω` to a graph domain**: if `g = ∂_w f` weakly on `Ω`
and the smooth `χ` has closed support in the boundary ball `B(c_j, ρ_j)`, then
`χ g + (∂_w χ) f = ∂_w (χ f)` weakly on the graph domain `Ω_j`
(`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`, `Rd.BoundedLipschitzDomain.inter_ball_eq`). -/
theorem hasWeakLineDeriv_mul_graph (j : Fin Ω.N) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχB : tsupport χ ⊆ ball (Ω.center j) (Ω.radius j)) {w : V} {f g : V → ℂ}
    (hfg : HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => w) f g) :
    HasWeakLineDeriv (Ω.graph j).toOpens (fun _ : Fin 1 => w) (fun x => (χ x : ℂ) * f x)
      (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) :=
  (hfg.mono (Ω.graph_toOpens_inf_ball_le j)).mul_of_tsupport_subset
    (B := ⟨ball (Ω.center j) (Ω.radius j), isOpen_ball⟩) hχ hχB

/-- **The `L_p` norm of a cutoff on a graph domain**: if `χ` is continuous with closed support in
the boundary ball `B(c_j, ρ_j)` and `|χ| ≤ C`, then `‖χ f‖_{L_p(Ω_j)} ≤ C ‖f‖_{L_p(Ω)}` for every
`f` and every `0 ≤ p ≤ ∞` (`Rd.eLpNorm_mul_le_of_tsupport_subset`). -/
theorem eLpNorm_mul_graph_le (j : Fin Ω.N) {χ : V → ℝ} (hχ : Continuous χ)
    (hχB : tsupport χ ⊆ ball (Ω.center j) (Ω.radius j)) {C : ℝ≥0} (hC : ∀ x, ‖χ x‖ ≤ C)
    (f : V → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => (χ x : ℂ) * f x) p (volume.restrict (Ω.graph j).domain) ≤
      C * eLpNorm f p (volume.restrict Ω.carrier) :=
  (eLpNorm_mul_le_of_tsupport_subset (O := (Ω.graph j).toOpens)
    (B := ⟨ball (Ω.center j) (Ω.radius j), isOpen_ball⟩) hχ hχB hC).trans
      (by gcongr; exact Ω.graph_toOpens_inf_ball_le j)

/-- **The `L_p` norm of a cutoff derivative on a graph domain**: for `1 ≤ p`, a smooth `χ` with
closed support in the boundary ball `B(c_j, ρ_j)`, `|χ| ≤ C` and `|∂_w χ| ≤ C'`,
`‖χ g + (∂_w χ) f‖_{L_p(Ω_j)} ≤ C ‖g‖_{L_p(Ω)} + C' ‖f‖_{L_p(Ω)}` for all `f`, `g`
(`Rd.eLpNorm_mul_add_fderiv_mul_le`). -/
theorem eLpNorm_mul_add_fderiv_mul_graph_le (j : Fin Ω.N) (hp : 1 ≤ p) {w : V} {f g : V → ℂ}
    {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχB : tsupport χ ⊆ ball (Ω.center j) (Ω.radius j)) {C C' : ℝ≥0} (hC : ∀ x, ‖χ x‖ ≤ C)
    (hC' : ∀ x, ‖fderiv ℝ χ x w‖ ≤ C') :
    eLpNorm (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) p
        (volume.restrict (Ω.graph j).domain) ≤
      C * eLpNorm g p (volume.restrict Ω.carrier) + C' * eLpNorm f p (volume.restrict Ω.carrier) :=
  (eLpNorm_mul_add_fderiv_mul_le (O := (Ω.graph j).toOpens)
    (B := ⟨ball (Ω.center j) (Ω.radius j), isOpen_ball⟩) hp hχ hχB hC hC').trans (by
      gcongr <;> exact Ω.graph_toOpens_inf_ball_le j)

/-- **The extension by reflection of a cutoff on a boundary patch, with its bound**: for `1 ≤ p`, a
smooth `χ` with values in `[0, 1]`, closed support in the boundary ball `B(c_j, ρ_j)` and
`|∂_{e_i} χ| ≤ d_i`, and `f ∈ L_p(Ω)` with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` on `Ω`, the
extension by reflection `F` of `χ f` in the graph domain `Ω_j` has weak derivatives
`G_k = ∂_{e_k} F` on `V` with
`‖F‖_p + ∑_k ‖G_k‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`,
`C = 2 + 2 n (1 + M_j)² (1 + ∑_i d_i)` (`Rd.reflectionConst`) with the Lipschitz constant `M_j` of
the graph of `Ω_j`
(`Rd.BoundedLipschitzDomain.hasWeakLineDeriv_mul_graph`,
`Rd.LipschitzGraph.hasWeakLineDeriv_reflectionExtension`, `Rd.add_sum_le_of_le_two_mul`). -/
theorem exists_hasWeakLineDeriv_reflectionExtension_mul (j : Fin Ω.N) (hp : 1 ≤ p) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχB : tsupport χ ⊆ ball (Ω.center j) (Ω.radius j)) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {d : Fin (finrank ℝ V) → ℝ≥0} (hd : ∀ i x, ‖fderiv ℝ χ x (gridBasis V i)‖ ≤ d i)
    {f : V → ℂ} {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict Ω.carrier))
    (hg : ∀ i, MemLp (g i) p (volume.restrict Ω.carrier))
    (hfg : ∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) f (g i)) :
    ∃ G : Fin (finrank ℝ V) → V → ℂ,
      (∀ k, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V k)
        ((Ω.graph j).reflectionExtension fun x => (χ x : ℂ) * f x) (G k)) ∧
      eLpNorm ((Ω.graph j).reflectionExtension fun x => (χ x : ℂ) * f x) p volume +
          ∑ k, eLpNorm (G k) p volume ≤
        reflectionConst (finrank ℝ V) (Ω.graph j).M (∑ i, (d i : ℝ≥0∞)) *
          (eLpNorm f p (volume.restrict Ω.carrier) +
            ∑ i, eLpNorm (g i) p (volume.restrict Ω.carrier)) := by
  have h1 : ∀ x, ‖χ x‖ ≤ ((1 : ℝ≥0) : ℝ) := fun x =>
    (norm_le_one_of_forall_mem_Icc hχ01 x).trans_eq NNReal.coe_one.symm
  have hloc := fun i => Ω.hasWeakLineDeriv_mul_graph j hχ hχB (hfg i)
  have hF0 : eLpNorm (fun x => (χ x : ℂ) * f x) p (volume.restrict (Ω.graph j).domain) ≤
      eLpNorm f p (volume.restrict Ω.carrier) :=
    (Ω.eLpNorm_mul_graph_le j hχ.continuous hχB h1 f p).trans_eq (by rw [ENNReal.coe_one, one_mul])
  have hG0 : ∀ i, eLpNorm (fun x => (χ x : ℂ) * g i x + (fderiv ℝ χ x (gridBasis V i) : ℂ) * f x)
      p (volume.restrict (Ω.graph j).domain) ≤ eLpNorm (g i) p (volume.restrict Ω.carrier) +
        d i * eLpNorm f p (volume.restrict Ω.carrier) := fun i =>
    (Ω.eLpNorm_mul_add_fderiv_mul_graph_le j hp hχ hχB h1 (hd i)).trans_eq
      (by rw [ENNReal.coe_one, one_mul])
  have hmf : MemLp (fun x => (χ x : ℂ) * f x) p (volume.restrict (Ω.graph j).domain) :=
    memLp_iff.2 (hF0.trans_lt hf)
  have hmg : ∀ i, MemLp (fun x => (χ x : ℂ) * g i x + (fderiv ℝ χ x (gridBasis V i) : ℂ) * f x)
      p (volume.restrict (Ω.graph j).domain) := fun i =>
    memLp_iff.2 ((hG0 i).trans_lt (ENNReal.add_lt_top.2 ⟨hg i, ENNReal.mul_lt_top
      ENNReal.coe_lt_top hf⟩))
  refine ⟨_, fun k => (Ω.graph j).hasWeakLineDeriv_reflectionExtension hp hmf hmg hloc
    (gridBasis V k), ?_⟩
  calc _ ≤ (2 + Fintype.card (Fin (finrank ℝ V)) * (2 * ENNReal.ofReal ((1 + (Ω.graph j).M) ^ 2)) *
        (1 + ∑ i, (d i : ℝ≥0∞))) * (eLpNorm f p (volume.restrict Ω.carrier) +
          ∑ i, eLpNorm (g i) p (volume.restrict Ω.carrier)) := by
        refine add_sum_le_of_le_two_mul
          ((LipschitzGraph.eLpNorm_reflectionExtension_le _ hp _).trans (by gcongr)) fun k => ?_
        refine ((Ω.graph j).eLpNorm_reflectionDeriv_le hp hmf hmg hloc _).trans ?_
        rw [← ofReal_norm, (gridBasis V).orthonormal.1 k, ENNReal.ofReal_one, mul_one]
        gcongr
        calc _ ≤ ∑ i, (eLpNorm (g i) p (volume.restrict Ω.carrier) +
              d i * eLpNorm f p (volume.restrict Ω.carrier)) :=
              Finset.sum_le_sum fun i _ => hG0 i
          _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [Fintype.card_fin]; rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The extension by reflection of a cutoff agrees with the function near the patch**: if
`χ = 1` near `closedBall(c_j, ρ_j - 2ε)` with `ε ≥ 0`, then the extension by reflection of `χ f`
in the
graph domain `Ω_j` is `f` on `Ω ∩ B(c_j, ρ_j - 2ε)`, a subset of `Ω_j`
(`Rd.BoundedLipschitzDomain.inter_ball_eq`, `Rd.LipschitzGraph.reflectionExtension_of_mem`). -/
theorem reflectionExtension_mul_eq_of_mem (j : Fin Ω.N) {ε : ℝ} (hε : 0 ≤ ε) {χ : V → ℝ}
    (hχ1 : ∀ᶠ x in 𝓝ˢ (closedBall (Ω.center j) (Ω.radius j - 2 * ε)), χ x = 1) (f : V → ℂ)
    {x : V} (hx : x ∈ Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) :
    (Ω.graph j).reflectionExtension (fun x => (χ x : ℂ) * f x) x = f x := by
  have hxG : x ∈ (Ω.graph j).domain := by
    have hx' := hx
    rw [Ω.inter_ball_eq j (by linarith)] at hx'
    exact hx'.1
  rw [LipschitzGraph.reflectionExtension_of_mem _ _ hxG,
    hχ1.self_of_nhdsSet x (ball_subset_closedBall hx.2), Complex.ofReal_one, one_mul]

/-- **The cutoff of a function on the inner patch, with its bound**: for `1 ≤ p`, a smooth `χ` with
values in `[0, 1]`, compact closed support in `Ω`, `|∂_{e_i} χ| ≤ d_i` and `χ = 1` near
`{infDist(·, Ωᶜ) ≥ 2δ}`, and `f` with weak derivatives `g_i = ∂_{e_i} f` on `Ω`, the function
`χ f` has weak derivatives `G_i = ∂_{e_i} (χ f)` on `V`, equals `f` on
`{x ∈ Ω : infDist(x, Ωᶜ) > 2δ}`, and
`‖χ f‖_p + ∑_i ‖G_i‖_p ≤ (1 + ∑_i d_i) (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`
(`Rd.HasWeakLineDeriv.cutoff_top`, `Rd.eLpNorm_mul_add_sum_le_of_tsupport_subset`). -/
theorem exists_hasWeakLineDeriv_mul_interior (hp : 1 ≤ p) {δ : ℝ} {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω.carrier) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {d : Fin (finrank ℝ V) → ℝ≥0} (hd : ∀ i x, ‖fderiv ℝ χ x (gridBasis V i)‖ ≤ d i)
    (hχ1 : ∀ᶠ x in 𝓝ˢ {x : V | 2 * δ ≤ infDist x Ω.carrierᶜ}, χ x = 1) {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ}
    (hfg : ∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) f (g i)) :
    ∃ G : Fin (finrank ℝ V) → V → ℂ,
      (∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (fun x => (χ x : ℂ) * f x)
        (G i)) ∧
      (∀ x ∈ Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}, (χ x : ℂ) * f x = f x) ∧
      eLpNorm (fun x => (χ x : ℂ) * f x) p volume + ∑ i, eLpNorm (G i) p volume ≤
        (1 + ∑ i, (d i : ℝ≥0∞)) * (eLpNorm f p (volume.restrict Ω.carrier) +
          ∑ i, eLpNorm (g i) p (volume.restrict Ω.carrier)) := by
  refine ⟨fun i x => (χ x : ℂ) * g i x + (fderiv ℝ χ x (gridBasis V i) : ℂ) * f x,
    fun i => ((hfg i).cutoff_top hχ hχc hχΩ).1, fun x hx => ?_,
    eLpNorm_mul_add_sum_le_of_tsupport_subset (O := Ω.toOpens) hp hχ hχΩ hχ01 hd f g⟩
  rw [hχ1.self_of_nhdsSet x (le_of_lt hx.2 : 2 * δ ≤ infDist x Ω.carrierᶜ), Complex.ofReal_one,
    one_mul]

end BoundedLipschitzDomain

end BoundedDomains

end Rd
