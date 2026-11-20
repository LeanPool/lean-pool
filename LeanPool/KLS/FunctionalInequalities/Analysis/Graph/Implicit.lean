/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Graph.Area
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local `C^∞` graph representation of a regular level set

General geometric analysis, independent of the KLS objects: the implicit function theorem in the
form needed by the codimension-one area formula of `Analysis/Graph/Area.lean`.  Every statement
here is proved and uses only the standard axioms; the module contains no hole.

## Setting

`H` and `V` are finite-dimensional real inner-product spaces, `ι : H →ₗᵢ[ℝ] V` a linear isometry
and `e : V` a unit vector orthogonal to the range of `ι`, spanning `V` together with that range
(`IsGraphSplitting ι e`).  Every `x : V` then decomposes as `x = ι (graphProj ι x) + ⟪e, x⟫ • e`.

For `φ : V → ℝ` of class `C^∞` with `φ x₀ = 0` and `gradient φ x₀ = c • e`, `c > 0`, the level set
`{φ = 0}` is, near `x₀`, exactly the graph `y ↦ x₀ + ι y + g y • e` of a function `g`, the sublevel
set `{φ < 0}` is exactly the part of the cylinder below that graph, and the normalized gradient of
`φ` along the graph is `(ι (-∇g y) + e) / √(1 + ‖∇g y‖²)`.

## Route to `C^∞` regularity

Mathlib's `HasStrictFDerivAt.implicitFunctionOfComplemented` gives strict differentiability of the
implicit function *at one point*, which is not enough for the area formula.  This module goes
through the inverse function theorem instead: the chart

  `flattenChart ι e φ x₀ x = ι (graphProj ι (x - x₀)) + φ x • e`

is `C^∞` and has invertible derivative at `x₀`, hence (`ContDiffAt.toOpenPartialHomeomorph`) is an
open partial homeomorphism near `x₀`.  Its derivative stays invertible on a neighbourhood because
the invertible operators form an open set (`ContinuousLinearEquiv.isOpen`), so
`OpenPartialHomeomorph.contDiffAt_symm` applies at *every* nearby point and the local inverse is
`C^∞` on a neighbourhood, not just differentiable at one point.

## From local to global regularity

`Analysis.hausdorffNormalized_image_graphMap` asks for a globally `C¹` height function, while the
inverse function theorem produces one that is `C^∞` only near the centre.  The gap is closed here,
inside `exists_graphRepr`, by multiplying the local height function by a `ContDiffBump`
supported in a ball on which it is smooth, and then restricting the parameter set to the ball where
the bump equals `1`.  The `g` handed to the caller is therefore **globally** `C^∞` and agrees with
the implicit function on the whole parameter neighbourhood, so no consumer ever has to turn a
`ContDiffOn` into a `ContDiff`, and there is only one gradient in play.

## Contents

* `IsGraphSplitting ι e`: the orthogonal splitting hypothesis.
* `exists_graphRepr`: the local graph representation, with the side condition and the
  gradient formula along the graph.
* `graphCylinder`, `graphChartMap`: the local cylinder and the graph parametrization, with the
  inverse parameter map `graphProj ι (· - x₀)`.
* `isGraphSplitting_orthogonal`: a unit vector and the orthogonal complement of its span form a
  splitting; this is the splitting used by every boundary chart and by the dimension induction of
  `Analysis/Graph/Divergence.lean`.
* `hausdorffNormalized_image_graphChartMap`: the area formula for a *translated* graph map,
  which is the form a boundary chart produces.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ContDiff ENNReal

namespace FunctionalInequalities.Analysis

universe u v

/-! ### The orthogonal splitting `V = ι H ⊕ ℝ e` -/

section Splitting

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The tangential retraction `V →L[ℝ] V`, `x ↦ ι (P x)` for `P = graphProj ι` the adjoint of
`ι`. -/
def graphRetract (ι : H →ₗᵢ[ℝ] V) : V →L[ℝ] V :=
  ι.toContinuousLinearMap.comp (graphProj ι)

theorem graphRetract_apply (ι : H →ₗᵢ[ℝ] V) (x : V) :
    graphRetract ι x = ι (graphProj ι x) := rfl

theorem graphRetract_ι (ι : H →ₗᵢ[ℝ] V) (y : H) : graphRetract ι (ι y) = ι y := by
  simp [graphRetract, graphProj_ι]

/-- `(ι, e)` is an *orthogonal splitting* of `V`: `e` is a unit vector orthogonal to the range of
`ι`, and every vector of `V` is the sum of its tangential retraction and its `e`-component.
Equivalently, `ι` is a linear isometry of `H` onto `(ℝ ∙ e)ᗮ`. -/
structure IsGraphSplitting (ι : H →ₗᵢ[ℝ] V) (e : V) : Prop where
  /-- `e` is a unit vector. -/
  norm_e : ‖e‖ = 1
  /-- The range of `ι` is orthogonal to `e`. -/
  perp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)
  /-- The range of `ι` and `e` together span `V`. -/
  split : ∀ x : V, graphRetract ι x + ⟪e, x⟫ • e = x

namespace IsGraphSplitting

variable {ι : H →ₗᵢ[ℝ] V} {e : V}

theorem perp' (h : IsGraphSplitting ι e) (v : H) : ⟪e, ι v⟫ = (0 : ℝ) := by
  rw [real_inner_comm]; exact h.perp v

theorem inner_e_self (h : IsGraphSplitting ι e) : ⟪e, e⟫ = (1 : ℝ) := by
  rw [real_inner_self_eq_norm_sq, h.norm_e]; norm_num

theorem retract_e (h : IsGraphSplitting ι e) : graphRetract ι e = 0 := by
  simp [graphRetract, graphProj_eq_zero ι h.perp]

theorem proj_e (h : IsGraphSplitting ι e) : graphProj ι e = 0 := graphProj_eq_zero ι h.perp

/-- The `H`-component of `ι y + t • e` is `y`. -/
theorem proj_add_smul (h : IsGraphSplitting ι e) (y : H) (t : ℝ) :
    graphProj ι (ι y + t • e) = y := by
  rw [map_add, graphProj_ι, ContinuousLinearMap.map_smul, h.proj_e, smul_zero, add_zero]

/-- The `e`-component of `ι y + t • e` is `t`. -/
theorem inner_add_smul (h : IsGraphSplitting ι e) (y : H) (t : ℝ) :
    ⟪e, ι y + t • e⟫ = t := by
  rw [inner_add_right, h.perp' y, real_inner_smul_right, h.inner_e_self, zero_add, mul_one]

/-- Pythagoras in the splitting. -/
theorem norm_add_smul_sq (h : IsGraphSplitting ι e) (y : H) (t : ℝ) :
    ‖ι y + t • e‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  rw [← @real_inner_self_eq_norm_sq V]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ι.inner_map_map, h.perp y, h.perp' y, h.inner_e_self]
  rw [← @real_inner_self_eq_norm_sq H]
  ring

theorem inner_e_retract (h : IsGraphSplitting ι e) (x : V) : ⟪e, graphRetract ι x⟫ = (0 : ℝ) :=
  h.perp' _

/-- Reconstruction of a vector from its two components. -/
theorem eq_ι_add_smul (h : IsGraphSplitting ι e) (x : V) :
    ι (graphProj ι x) + ⟪e, x⟫ • e = x := h.split x

/-- A vector of `V` is determined by its two components. -/
theorem ext_components (h : IsGraphSplitting ι e) {x x' : V}
    (h₁ : graphProj ι x = graphProj ι x') (h₂ : ⟪e, x⟫ = (⟪e, x'⟫ : ℝ)) : x = x' := by
  rw [← h.eq_ι_add_smul x, ← h.eq_ι_add_smul x', h₁, h₂]

end IsGraphSplitting

/-- The tangential component of a vector is determined by its tangential inner products. -/
theorem graphProj_eq_of_inner_ι (ι : H →ₗᵢ[ℝ] V) {a : V} {b : H}
    (hab : ∀ v : H, ⟪a, ι v⟫ = (⟪b, v⟫ : ℝ)) : graphProj ι a = b := by
  refine ext_inner_right ℝ fun w => ?_
  rw [graphProj, ContinuousLinearMap.adjoint_inner_left]
  exact hab w

/-- A functional annihilating the graph tangent has its representing vector in the normal line. -/
theorem IsGraphSplitting.eq_normal_of_comp_graphLinear_eq_zero
    {ι : H →ₗᵢ[ℝ] V} {e a : V} {b : H} (hsp : IsGraphSplitting ι e)
    (hkey : (innerSL ℝ a).comp (graphLinear ι e b) = 0) :
    a = (⟪a, e⟫ : ℝ) • (ι (-b) + e) := by
  have hinner : ∀ v : H, (⟪a, ι v⟫ : ℝ) = ⟪(⟪a, e⟫ • (-b) : H), v⟫ := by
    intro v
    have h := congrArg (fun L : H →L[ℝ] ℝ => L v) hkey
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, graphLinear_apply,
      zero_apply, innerSL_apply_apply, inner_add_right,
      real_inner_smul_right] at h
    rw [inner_smul_left, inner_neg_left]
    simp only [starRingEnd_apply, star_trivial]
    linear_combination h
  have hproj := graphProj_eq_of_inner_ι ι hinner
  have hrec := hsp.eq_ι_add_smul a
  rw [hproj, real_inner_comm a e] at hrec
  calc
    a = ι (⟪a, e⟫ • (-b)) + ⟪a, e⟫ • e := hrec.symm
    _ = ⟪a, e⟫ • (ι (-b) + e) := by rw [map_smul, smul_add]

end Splitting

section OrthogonalSplitting

variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **A unit vector splits the space.**  The orthogonal complement of the line spanned by a unit
vector `u`, with its natural isometric embedding, together with `u` itself, is an orthogonal
splitting.  This is the splitting used by every boundary chart and by the divergence computation
of `Analysis/Graph/Divergence.lean`. -/
theorem isGraphSplitting_orthogonal {u : W} (hu : ‖u‖ = 1) :
    IsGraphSplitting ((ℝ ∙ u)ᗮ : Submodule ℝ W).subtypeₗᵢ u := by
  have hee : (⟪u, u⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hap : ∀ y : ((ℝ ∙ u)ᗮ : Submodule ℝ W),
      ((ℝ ∙ u)ᗮ : Submodule ℝ W).subtypeₗᵢ y = (y : W) := fun _ => rfl
  have hperp : ∀ y : ((ℝ ∙ u)ᗮ : Submodule ℝ W), (⟪u, (y : W)⟫ : ℝ) = 0 := fun y =>
    (Submodule.mem_orthogonal _ _).mp y.2 u (Submodule.mem_span_singleton_self _)
  refine ⟨hu, ?_, ?_⟩
  · intro v
    rw [hap, real_inner_comm]
    exact hperp v
  · intro x
    have hb : x - (⟪u, x⟫ : ℝ) • u ∈ ((ℝ ∙ u)ᗮ : Submodule ℝ W) := by
      rw [Submodule.mem_orthogonal']
      intro w hw
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [inner_sub_left, real_inner_smul_right, real_inner_smul_right, real_inner_smul_left,
        hee, real_inner_comm x u]
      ring
    have hproj : graphProj (((ℝ ∙ u)ᗮ : Submodule ℝ W).subtypeₗᵢ) x
        = ⟨x - (⟪u, x⟫ : ℝ) • u, hb⟩ := by
      refine graphProj_eq_of_inner_ι _ fun v => ?_
      rw [hap, Submodule.coe_inner]
      simp only []
      rw [inner_sub_left, real_inner_smul_left, hperp v]
      ring
    rw [graphRetract_apply, hproj, hap]
    simp only []
    abel

end OrthogonalSplitting

/-! ### The flattening chart -/

section Flatten

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The chart that flattens the level sets of `φ` near `x₀`: the tangential component is the
tangential displacement from `x₀`, the normal component is the value of `φ`. -/
def flattenChart (ι : H →ₗᵢ[ℝ] V) (e : V) (φ : V → ℝ) (x₀ : V) : V → V :=
  fun x => graphRetract ι (x - x₀) + φ x • e

theorem contDiff_flattenChart (ι : H →ₗᵢ[ℝ] V) (e : V) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x₀ : V) : ContDiff ℝ ∞ (flattenChart ι e φ x₀) :=
  ((graphRetract ι).contDiff.comp (contDiff_id.sub contDiff_const)).add (hφ.smul contDiff_const)

theorem hasFDerivAt_flattenChart (ι : H →ₗᵢ[ℝ] V) (e : V) {φ : V → ℝ} {x : V}
    (hφ : DifferentiableAt ℝ φ x) (x₀ : V) :
    HasFDerivAt (flattenChart ι e φ x₀) (graphRetract ι + (fderiv ℝ φ x).smulRight e) x := by
  have h1 : HasFDerivAt (fun z : V => graphRetract ι (z - x₀)) (graphRetract ι) x := by
    have h := (graphRetract ι).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)
    rwa [ContinuousLinearMap.comp_id] at h
  exact h1.add (hφ.hasFDerivAt.smul_const e)

/-- The candidate derivative of the flattening chart: it acts as the identity in the tangential
directions and by the scalar `a` in the direction `e`. -/
def flattenCLM (ι : H →ₗᵢ[ℝ] V) (e : V) (a : ℝ) : V →L[ℝ] V :=
  graphRetract ι + a • ((innerSL ℝ e).smulRight e)

theorem flattenCLM_apply (ι : H →ₗᵢ[ℝ] V) (e : V) (a : ℝ) (w : V) :
    flattenCLM ι e a w = graphRetract ι w + (a * ⟪e, w⟫) • e := by
  simp [flattenCLM, innerSL_apply_apply, smul_smul]

/-- The two maps `flattenCLM ι e a` and `flattenCLM ι e b` compose to `flattenCLM ι e (a * b)`. -/
theorem flattenCLM_comp_apply (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e) (a b : ℝ)
    (w : V) : flattenCLM ι e a (flattenCLM ι e b w) = flattenCLM ι e (a * b) w := by
  rw [flattenCLM_apply, flattenCLM_apply, flattenCLM_apply]
  have h1 : graphRetract ι (graphRetract ι w + (b * ⟪e, w⟫) • e) = graphRetract ι w := by
    rw [map_add, ContinuousLinearMap.map_smul, hsp.retract_e, smul_zero, add_zero]
    exact graphRetract_ι ι _
  have h2 : (⟪e, graphRetract ι w + (b * ⟪e, w⟫) • e⟫ : ℝ) = b * ⟪e, w⟫ := by
    rw [inner_add_right, hsp.inner_e_retract, real_inner_smul_right, hsp.inner_e_self, zero_add,
      mul_one]
  rw [h1, h2, mul_assoc]

theorem flattenCLM_one (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e) (w : V) :
    flattenCLM ι e 1 w = w := by
  rw [flattenCLM_apply, one_mul]; exact hsp.split w

/-- The derivative of the flattening chart at the centre is a linear equivalence. -/
def flattenEquiv (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e) {c : ℝ} (hc : c ≠ 0) :
    V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse (flattenCLM ι e c) (flattenCLM ι e c⁻¹)
    (fun w => by rw [flattenCLM_comp_apply ι hsp, inv_mul_cancel₀ hc, flattenCLM_one ι hsp])
    (fun w => by rw [flattenCLM_comp_apply ι hsp, mul_inv_cancel₀ hc, flattenCLM_one ι hsp])

theorem coe_flattenEquiv (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e) {c : ℝ}
    (hc : c ≠ 0) : (flattenEquiv ι hsp hc : V →L[ℝ] V) = flattenCLM ι e c := rfl

/-- The derivative of a real function whose gradient is `c • e` is `c` times the inner product
with `e`. -/
theorem smulRight_fderiv_eq (ι : H →ₗᵢ[ℝ] V) {e : V} {φ : V → ℝ} {x₀ : V} {c : ℝ}
    (hgrad : gradient φ x₀ = c • e) :
    graphRetract ι + (fderiv ℝ φ x₀).smulRight e = flattenCLM ι e c := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [flattenCLM_apply]
  simp only [ContinuousLinearMap.smulRight_apply, add_apply]
  rw [← fderiv_eq_innerSL_gradient φ x₀, hgrad]
  simp only [innerSL_apply_apply, real_inner_smul_left]

end Flatten

/-! ### The local implicit function -/

section Implicit

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Local implicit function, `C^∞` on a neighbourhood.**  If `φ` is `C^∞`, vanishes at `x₀` and
has gradient `c • e` there with `c > 0`, then on an open tangential neighbourhood `Ω₀` of the
origin there is a height function `g₀`, smooth at every point of `Ω₀`, whose graph over `Ω₀` lies
in `{φ = 0}`.

The inverse function theorem is applied to `flattenChart ι e φ x₀`; smoothness on a whole
neighbourhood (rather than differentiability at one point, which is all that Mathlib's implicit
function theorem provides) comes from `OpenPartialHomeomorph.contDiffAt_symm` together with the
openness of the set of invertible operators. -/
theorem exists_local_implicit (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : V} (hφ0 : φ x₀ = 0) {c : ℝ} (hc : 0 < c)
    (hgrad : gradient φ x₀ = c • e) :
    ∃ (g₀ : H → ℝ) (Ω₀ : Set H), IsOpen Ω₀ ∧ (0 : H) ∈ Ω₀ ∧ g₀ 0 = 0 ∧
      (∀ y ∈ Ω₀, ContDiffAt ℝ ∞ g₀ y) ∧
      (∀ y ∈ Ω₀, φ (x₀ + ι y + g₀ y • e) = 0) := by
  set Φ : V → V := flattenChart ι e φ x₀ with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_flattenChart ι e hφ x₀
  have hΦdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΦ0 : Φ x₀ = 0 := by
    simp [hΦdef, flattenChart, hφ0]
  -- the derivative at the centre is a linear equivalence
  set L : V ≃L[ℝ] V := flattenEquiv ι hsp hc.ne' with hLdef
  have hLderiv : HasFDerivAt Φ (L : V →L[ℝ] V) x₀ := by
    have h := hasFDerivAt_flattenChart (x := x₀) ι e (hφ.differentiable (by simp) x₀) x₀
    rw [smulRight_fderiv_eq ι hgrad] at h
    rw [coe_flattenEquiv]
    exact h
  -- the local homeomorphism
  set F : OpenPartialHomeomorph V V := hΦ.contDiffAt.toOpenPartialHomeomorph Φ hLderiv (by simp)
    with hFdef
  have hFcoe : ⇑F = Φ := rfl
  have hFsource : x₀ ∈ F.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hΦ.contDiffAt hLderiv (by simp)
  have hFtarget : Φ x₀ ∈ F.target :=
    ContDiffAt.image_mem_toOpenPartialHomeomorph_target hΦ.contDiffAt hLderiv (by simp)
  -- the open set where the derivative of `Φ` stays invertible
  set N : Set V := F.source ∩ (fderiv ℝ Φ) ⁻¹'
      (Set.range (ContinuousLinearEquiv.toContinuousLinearMap :
        (V ≃L[ℝ] V) → (V →L[ℝ] V))) with hNdef
  have hNopen : IsOpen N :=
    F.open_source.inter (ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv (by simp)))
  have hx₀N : x₀ ∈ N := ⟨hFsource, ⟨L, hLderiv.fderiv.symm⟩⟩
  set T : Set V := F.target ∩ F.symm ⁻¹' N with hTdef
  have hTopen : IsOpen T := F.isOpen_inter_preimage_symm hNopen
  have h0T : (0 : V) ∈ T := by
    refine ⟨by rw [← hΦ0]; exact hFtarget, ?_⟩
    simp only [Set.mem_preimage]
    rw [← hΦ0, ← hFcoe, F.left_inv hFsource]
    exact hx₀N
  set Ω₀ : Set H := ι ⁻¹' T with hΩdef
  have hΩopen : IsOpen Ω₀ := hTopen.preimage ι.continuous
  have h0Ω : (0 : H) ∈ Ω₀ := by
    simp only [hΩdef, Set.mem_preimage, map_zero]
    exact h0T
  set g₀ : H → ℝ := fun y => ⟪e, F.symm (ι y) - x₀⟫ with hg₀def
  -- the key identification of the local inverse with the graph point
  have hkey : ∀ y ∈ Ω₀, F.symm (ι y) = x₀ + ι y + g₀ y • e ∧ φ (F.symm (ι y)) = 0 := by
    intro y hy
    have hmem : ι y ∈ F.target := hy.1
    have hΦinv : Φ (F.symm (ι y)) = ι y := by
      rw [← hFcoe]; exact F.right_inv hmem
    set z : V := F.symm (ι y) with hz
    have hsplit' : graphRetract ι (z - x₀) + φ z • e = ι y := hΦinv
    have hφz : φ z = 0 := by
      have := congrArg (fun w : V => (⟪e, w⟫ : ℝ)) hsplit'
      simp only [inner_add_right, hsp.inner_e_retract, real_inner_smul_right,
        hsp.inner_e_self, hsp.perp' y, zero_add, mul_one] at this
      exact this
    have hret : graphRetract ι (z - x₀) = ι y := by
      rw [hφz, zero_smul, add_zero] at hsplit'; exact hsplit'
    have hgy : g₀ y = (⟪e, z - x₀⟫ : ℝ) := rfl
    have hrec : ι y + g₀ y • e = z - x₀ := by
      rw [hgy, ← hret]; exact hsp.split (z - x₀)
    refine ⟨?_, hφz⟩
    rw [add_assoc, hrec]
    abel
  refine ⟨g₀, Ω₀, hΩopen, h0Ω, ?_, ?_, ?_⟩
  · -- `g₀ 0 = 0`
    have hz : F.symm (ι (0 : H)) = x₀ := by
      rw [map_zero, ← hΦ0, ← hFcoe, F.left_inv hFsource]
    change (⟪e, F.symm (ι (0 : H)) - x₀⟫ : ℝ) = 0
    rw [hz, sub_self, inner_zero_right]
  · -- smoothness on `Ω₀`
    intro y hy
    have hmem : ι y ∈ F.target := hy.1
    obtain ⟨L', hL'⟩ : ∃ L' : V ≃L[ℝ] V, (L' : V →L[ℝ] V) = fderiv ℝ Φ (F.symm (ι y)) := hy.2.2
    have hd : HasFDerivAt (⇑F) (L' : V →L[ℝ] V) (F.symm (ι y)) := by
      rw [hFcoe, hL']
      exact (hΦdiff _).hasFDerivAt
    have hsymm : ContDiffAt ℝ ∞ F.symm (ι y) :=
      F.contDiffAt_symm hmem hd (by rw [hFcoe]; exact hΦ.contDiffAt)
    have houter : ContDiffAt ℝ ∞ (fun x : V => (⟪e, x - x₀⟫ : ℝ)) (F.symm (ι y)) :=
      (((innerSL ℝ e).contDiff).comp (contDiff_id.sub contDiff_const)).contDiffAt
    have hι : ContDiffAt ℝ ∞ (fun y : H => ι y) y := ι.toContinuousLinearMap.contDiff.contDiffAt
    exact (houter.comp _ hsymm).comp y hι
  · intro y hy
    have h := hkey y hy
    rw [← h.1]; exact h.2

end Implicit

/-! ### The graph parametrization and its cylinder -/

section Chart

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The graph parametrization centred at `x₀`: `y ↦ x₀ + ι y + g y • e`. -/
def graphChartMap (ι : H →ₗᵢ[ℝ] V) (e : V) (x₀ : V) (g : H → ℝ) : H → V :=
  fun y => x₀ + graphMap ι e g y

section GraphChartIdentities

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ V]
theorem graphChartMap_apply (ι : H →ₗᵢ[ℝ] V) (e : V) (x₀ : V) (g : H → ℝ) (y : H) :
    graphChartMap ι e x₀ g y = x₀ + ι y + g y • e := by
  rw [graphChartMap, graphMap, add_assoc]

theorem graphChartMap_sub (ι : H →ₗᵢ[ℝ] V) (e : V) (x₀ : V) (g : H → ℝ) (y : H) :
    graphChartMap ι e x₀ g y - x₀ = ι y + g y • e := by
  rw [graphChartMap_apply, add_assoc]; abel

end GraphChartIdentities

/-- The tangential parameter of a point, the inverse of the graph parametrization. -/
def graphCoord (ι : H →ₗᵢ[ℝ] V) (x₀ : V) (x : V) : H := graphProj ι (x - x₀)

/-- The normal height of a point above the base point. -/
def graphHeight (e : V) (x₀ : V) (x : V) : ℝ := ⟪e, x - x₀⟫

/-- The open cylinder of tangential parameters in `Ω` and normal heights below `δ` in modulus. -/
def graphCylinder (ι : H →ₗᵢ[ℝ] V) (e : V) (x₀ : V) (Ω : Set H) (δ : ℝ) : Set V :=
  {x | graphCoord ι x₀ x ∈ Ω ∧ |graphHeight e x₀ x| < δ}

theorem mem_graphCylinder_iff {ι : H →ₗᵢ[ℝ] V} {e x₀ : V} {Ω : Set H} {δ : ℝ} {x : V} :
    x ∈ graphCylinder ι e x₀ Ω δ ↔ graphCoord ι x₀ x ∈ Ω ∧ |graphHeight e x₀ x| < δ := Iff.rfl

theorem isOpen_graphCylinder (ι : H →ₗᵢ[ℝ] V) (e x₀ : V) {Ω : Set H} (hΩ : IsOpen Ω) (δ : ℝ) :
    IsOpen (graphCylinder ι e x₀ Ω δ) := by
  have h1 : Continuous fun x : V => graphCoord ι x₀ x :=
    (graphProj ι).continuous.comp (continuous_id.sub continuous_const)
  have h2 : Continuous fun x : V => |graphHeight e x₀ x| :=
    (((innerSL ℝ e).continuous.comp (continuous_id.sub continuous_const))).abs
  exact (hΩ.preimage h1).inter (isOpen_Iio.preimage h2)

variable {ι : H →ₗᵢ[ℝ] V} {e : V}

theorem graphCoord_graphChartMap (hsp : IsGraphSplitting ι e) (x₀ : V) (g : H → ℝ) (y : H) :
    graphCoord ι x₀ (graphChartMap ι e x₀ g y) = y := by
  rw [graphCoord, graphChartMap_sub, hsp.proj_add_smul]

theorem graphHeight_graphChartMap (hsp : IsGraphSplitting ι e) (x₀ : V) (g : H → ℝ) (y : H) :
    graphHeight e x₀ (graphChartMap ι e x₀ g y) = g y := by
  rw [graphHeight, graphChartMap_sub, hsp.inner_add_smul]

/-- Reconstruction: a point is the graph point of its own coordinates and height. -/
theorem eq_graphChartMap_coord (hsp : IsGraphSplitting ι e) (x₀ x : V) :
    x = x₀ + ι (graphCoord ι x₀ x) + (graphHeight e x₀ x) • e := by
  rw [graphCoord, graphHeight, add_assoc, hsp.eq_ι_add_smul (x - x₀)]
  abel

/-- The graph parametrization is injective; orthogonality of the graph direction to the range of
`ι` is all that is used. -/
theorem graphChartMap_injective_of_perp (ι : H →ₗᵢ[ℝ] V) {e : V}
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (x₀ : V) (g : H → ℝ) :
    Function.Injective (graphChartMap ι e x₀ g) := by
  intro y y' h
  have h' : x₀ + graphMap ι e g y = x₀ + graphMap ι e g y' := h
  exact graphMap_injective ι hperp g (add_left_cancel h')

/-- The graph parametrization is injective. -/
theorem graphChartMap_injective (hsp : IsGraphSplitting ι e) (x₀ : V) (g : H → ℝ) :
    Function.Injective (graphChartMap ι e x₀ g) :=
  graphChartMap_injective_of_perp ι hsp.perp x₀ g

/-- Norm of the displacement in graph coordinates. -/
theorem norm_sub_sq_eq (hsp : IsGraphSplitting ι e) (x₀ x : V) :
    ‖x - x₀‖ ^ 2 = ‖graphCoord ι x₀ x‖ ^ 2 + (graphHeight e x₀ x) ^ 2 := by
  have h : x - x₀ = ι (graphCoord ι x₀ x) + (graphHeight e x₀ x) • e := by
    rw [graphCoord, graphHeight, hsp.eq_ι_add_smul (x - x₀)]
  rw [h, hsp.norm_add_smul_sq]

end Chart

/-! ### The gradient of the defining function along the graph -/

section GradientAlongGraph

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : H →ₗᵢ[ℝ] V} {e : V}

/-- If a `C¹` graph lies in the zero set of a differentiable `φ`, then at every graph point the
gradient of `φ` is the normal vector `ι (-∇g y) + e` scaled by its own `e`-component. -/
theorem gradient_eq_smul_of_graph (hsp : IsGraphSplitting ι e) {φ : V → ℝ}
    (hφ : Differentiable ℝ φ) {g : H → ℝ} (hg : ContDiff ℝ 1 g) {x₀ : V} {Ω : Set H}
    (hΩ : IsOpen Ω) (hzero : ∀ y ∈ Ω, φ (graphChartMap ι e x₀ g y) = 0) {y : H} (hy : y ∈ Ω) :
    gradient φ (graphChartMap ι e x₀ g y)
      = (⟪gradient φ (graphChartMap ι e x₀ g y), e⟫ : ℝ) • (ι (-(gradient g y)) + e) := by
  set Ψ : H → V := graphChartMap ι e x₀ g with hΨ
  set a : V := gradient φ (Ψ y) with ha
  set β : ℝ := ⟪a, e⟫ with hβ
  have hΨderiv : HasFDerivAt Ψ (graphLinear ι e (gradient g y)) y :=
    (hasFDerivAt_graphMap ι e (hg.differentiable (by norm_num) y)).const_add x₀
  have hcomp : HasFDerivAt (φ ∘ Ψ)
      ((fderiv ℝ φ (Ψ y)).comp (graphLinear ι e (gradient g y))) y :=
    (hφ (Ψ y)).hasFDerivAt.comp y hΨderiv
  have hzero' : (φ ∘ Ψ) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [hΩ.mem_nhds hy] with z hz using hzero z hz
  have hzeroderiv : HasFDerivAt (φ ∘ Ψ) (0 : H →L[ℝ] ℝ) y :=
    (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hzero'
  have hkey : (fderiv ℝ φ (Ψ y)).comp (graphLinear ι e (gradient g y)) = 0 :=
    hcomp.unique hzeroderiv
  have hnormal : (innerSL ℝ (gradient φ (Ψ y))).comp (graphLinear ι e (gradient g y)) = 0 := by
    rw [fderiv_eq_innerSL_gradient φ (Ψ y)]
    exact hkey
  exact hsp.eq_normal_of_comp_graphLinear_eq_zero hnormal
/-- Normalizing the gradient: the unit normal in graph coordinates. -/
theorem norm_inv_smul_eq_graphJacobian_inv_smul (hsp : IsGraphSplitting ι e) {a : V} {b : H}
    {β : ℝ} (hβ : 0 < β) (ha : a = β • (ι (-b) + e)) :
    ‖a‖⁻¹ • a = (graphJacobian b)⁻¹ • (ι (-b) + e) := by
  have hnorm : ‖ι (-b) + e‖ = graphJacobian b := by
    have hsq : ‖ι (-b) + e‖ ^ 2 = 1 + ‖b‖ ^ 2 := by
      have := hsp.norm_add_smul_sq (-b) 1
      rw [one_smul] at this
      rw [this, norm_neg]
      ring
    have hnn : (0 : ℝ) ≤ ‖ι (-b) + e‖ := norm_nonneg _
    rw [graphJacobian, ← hsq, Real.sqrt_sq hnn]
  have hJ : graphJacobian b ≠ 0 := (graphJacobian_pos b).ne'
  rw [ha, norm_smul, Real.norm_eq_abs, abs_of_pos hβ, hnorm, smul_smul]
  congr 1
  field_simp

end GradientAlongGraph


/-! ### The local graph representation -/

section Repr

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A **local `C^∞` graph representation** of the zero set of `φ` near `x₀`, in the orthogonal
splitting `(ι, e)`.  The height function is globally `C^∞` — the local smoothness produced by the
inverse function theorem is upgraded by a cutoff inside `exists_graphRepr` — so that the area
formula `Analysis.hausdorffNormalized_image_graphMap`, which needs a global `ContDiff` hypothesis,
applies verbatim to `graphChartMap ι e x₀ height` on measurable subsets of `param`.

Inside the cylinder `graphCylinder ι e x₀ param depth` the zero set of `φ` is *exactly* the graph
and the strict sublevel set is *exactly* the part below the graph; this is an equality of sets,
not an inclusion. -/
structure GraphRepr (ι : H →ₗᵢ[ℝ] V) (e : V) (φ : V → ℝ) (x₀ : V) where
  /-- The height function of the graph, globally `C^∞`. -/
  height : H → ℝ
  /-- The open tangential parameter neighbourhood of the origin. -/
  param : Set H
  /-- The half-height of the cylinder. -/
  depth : ℝ
  /-- The height function is `C^∞` on all of `H`. -/
  contDiff_height : ContDiff ℝ ∞ height
  /-- The parameter neighbourhood is open. -/
  isOpen_param : IsOpen param
  /-- The parameter neighbourhood contains the base point of the chart. -/
  zero_mem_param : (0 : H) ∈ param
  /-- The graph passes through `x₀`. -/
  height_zero : height 0 = 0
  /-- The cylinder is nondegenerate. -/
  depth_pos : 0 < depth
  /-- The graph stays strictly inside the cylinder. -/
  abs_height_lt : ∀ y ∈ param, |height y| < depth
  /-- `e` is a direction of strict increase of `φ` throughout the cylinder; this is what fixes the
  side convention. -/
  inner_gradient_pos : ∀ x ∈ graphCylinder ι e x₀ param depth, 0 < (⟪gradient φ x, e⟫ : ℝ)
  /-- Inside the cylinder, `{φ < 0}` is exactly the region below the graph. -/
  lt_iff : ∀ x ∈ graphCylinder ι e x₀ param depth,
    (φ x < 0 ↔ graphHeight e x₀ x < height (graphCoord ι x₀ x))
  /-- Inside the cylinder, `{φ = 0}` is exactly the graph. -/
  eq_iff : ∀ x ∈ graphCylinder ι e x₀ param depth,
    (φ x = 0 ↔ graphHeight e x₀ x = height (graphCoord ι x₀ x))

namespace GraphRepr

variable {ι : H →ₗᵢ[ℝ] V} {e : V} {φ : V → ℝ} {x₀ : V} (G : GraphRepr ι e φ x₀)

/-- The cylinder of the representation. -/
def cylinder : Set V := graphCylinder ι e x₀ G.param G.depth

/-- The graph parametrization of the representation. -/
def map : H → V := graphChartMap ι e x₀ G.height

theorem isOpen_cylinder : IsOpen G.cylinder :=
  isOpen_graphCylinder ι e x₀ G.isOpen_param G.depth

theorem map_apply (y : H) : G.map y = x₀ + ι y + G.height y • e :=
  graphChartMap_apply ι e x₀ G.height y

theorem coord_map (hsp : IsGraphSplitting ι e) (y : H) : graphCoord ι x₀ (G.map y) = y :=
  graphCoord_graphChartMap hsp x₀ G.height y

theorem height_map (hsp : IsGraphSplitting ι e) (y : H) :
    graphHeight e x₀ (G.map y) = G.height y :=
  graphHeight_graphChartMap hsp x₀ G.height y

theorem injective_map (hsp : IsGraphSplitting ι e) : Function.Injective G.map :=
  graphChartMap_injective hsp x₀ G.height

/-- Graph points lie in the cylinder. -/
theorem map_mem_cylinder (hsp : IsGraphSplitting ι e) {y : H} (hy : y ∈ G.param) :
    G.map y ∈ G.cylinder := by
  refine ⟨?_, ?_⟩
  · rw [G.coord_map hsp]; exact hy
  · rw [G.height_map hsp]; exact G.abs_height_lt y hy

/-- The graph lies in the zero set of `φ`. -/
theorem map_zero_of_mem (hsp : IsGraphSplitting ι e) {y : H} (hy : y ∈ G.param) :
    φ (G.map y) = 0 := by
  rw [G.eq_iff _ (G.map_mem_cylinder hsp hy), G.height_map hsp, G.coord_map hsp]

/-- **The zero set inside the cylinder is exactly the graph.** -/
theorem zeroSet_inter_cylinder (hsp : IsGraphSplitting ι e) :
    {x | φ x = 0} ∩ G.cylinder = G.map '' G.param := by
  ext x
  constructor
  · rintro ⟨hx0, hxcyl⟩
    refine ⟨graphCoord ι x₀ x, hxcyl.1, ?_⟩
    have ht := (G.eq_iff x hxcyl).mp hx0
    rw [map, graphChartMap_apply, ← ht]
    exact (eq_graphChartMap_coord hsp x₀ x).symm
  · rintro ⟨y, hy, rfl⟩
    exact ⟨G.map_zero_of_mem hsp hy, G.map_mem_cylinder hsp hy⟩

/-- **The sublevel set inside the cylinder is exactly the region below the graph.** -/
theorem sublevel_inter_cylinder :
    {x | φ x < 0} ∩ G.cylinder
      = {x ∈ G.cylinder | graphHeight e x₀ x < G.height (graphCoord ι x₀ x)} := by
  ext x
  constructor
  · rintro ⟨hx0, hxcyl⟩; exact ⟨hxcyl, (G.lt_iff x hxcyl).mp hx0⟩
  · rintro ⟨hxcyl, hlt⟩; exact ⟨(G.lt_iff x hxcyl).mpr hlt, hxcyl⟩

/-- **The gradient of `φ` along the graph**, unnormalized. -/
theorem gradient_map (hsp : IsGraphSplitting ι e) (hφ : Differentiable ℝ φ) {y : H}
    (hy : y ∈ G.param) :
    gradient φ (G.map y)
      = (⟪gradient φ (G.map y), e⟫ : ℝ) • (ι (-(gradient G.height y)) + e) :=
  gradient_eq_smul_of_graph hsp hφ (G.contDiff_height.of_le (by simp)) G.isOpen_param
    (fun z hz => G.map_zero_of_mem hsp hz) hy

/-- **The outward unit normal in graph coordinates.**  Normalizing the gradient of `φ` along the
graph gives `(ι (-∇g y) + e) / √(1 + ‖∇g y‖²)`; the sign is fixed, not only up to `±`, because the
`e`-component of the gradient is positive throughout the cylinder. -/
theorem normalized_gradient_map (hsp : IsGraphSplitting ι e) (hφ : Differentiable ℝ φ) {y : H}
    (hy : y ∈ G.param) :
    ‖gradient φ (G.map y)‖⁻¹ • gradient φ (G.map y)
      = (graphJacobian (gradient G.height y))⁻¹ • (ι (-(gradient G.height y)) + e) :=
  norm_inv_smul_eq_graphJacobian_inv_smul hsp
    (G.inner_gradient_pos _ (G.map_mem_cylinder hsp hy)) (G.gradient_map hsp hφ hy)

end GraphRepr

/--
**Local `C^∞` graph representation of a regular level set.**  If `φ` is `C^∞` with `φ x₀ = 0`
and `gradient φ x₀ = c • e`, `c > 0`, then inside a cylinder contained in any prescribed
neighbourhood `N₀` of `x₀` the zero set of `φ` is exactly the graph of a globally `C^∞` height
function over an open tangential neighbourhood of the origin, and `{φ < 0}` is exactly the part of
the cylinder below that graph.

The height function is globally `C^∞`: the inverse function theorem
(`exists_local_implicit`) gives smoothness only near the origin, and the cutoff by a
`ContDiffBump` supported in a ball on which that smoothness holds turns it into a global one
without changing the function on the parameter neighbourhood, which is shrunk to the ball where
the bump equals `1`. -/
theorem exists_graphRepr (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {x₀ : V} (hφ0 : φ x₀ = 0) {c : ℝ} (hc : 0 < c)
    (hgrad : gradient φ x₀ = c • e) {N₀ : Set V} (hN₀ : N₀ ∈ 𝓝 x₀) :
    ∃ G : GraphRepr ι e φ x₀, G.cylinder ⊆ N₀ := by
  classical
  obtain ⟨g₀, Ω₀, hΩopen, h0Ω, hg₀0, hg₀smooth, hg₀graph⟩ :=
    exists_local_implicit ι hsp hφ hφ0 hc
      hgrad
  -- a ball of tangential parameters on which `g₀` is smooth
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hΩopen 0 h0Ω
  set ρ : ℝ := r₀ / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  have hclosed : Metric.closedBall (0 : H) (2 * ρ) ⊆ Ω₀ := by
    refine subset_trans (fun y hy => ?_) hball₀
    simp only [Metric.mem_closedBall, dist_zero_right] at hy
    simp only [Metric.mem_ball, dist_zero_right]
    rw [hρdef] at hy
    linarith
  -- the cutoff
  set χ : ContDiffBump (0 : H) := ⟨ρ, 2 * ρ, hρ, by linarith⟩ with hχdef
  set g : H → ℝ := fun y => χ y * g₀ y with hgdef
  have hχrIn : χ.rIn = ρ := rfl
  have hχrOut : χ.rOut = 2 * ρ := rfl
  have hgsmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Ω₀
    · exact χ.contDiff.contDiffAt.mul (hg₀smooth y hy)
    · have hmem : y ∈ (Metric.closedBall (0 : H) (2 * ρ))ᶜ := fun hcon => hy (hclosed hcon)
      have heq : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hmem] with z hz
        have hz' : χ.rOut ≤ dist z 0 := by
          simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hz
          rw [hχrOut]; exact hz.le
        simp [hgdef, χ.zero_of_le_dist hz']
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hgeq : ∀ y ∈ Metric.closedBall (0 : H) ρ, g y = g₀ y := by
    intro y hy
    rw [hgdef]
    simp only
    rw [χ.one_of_mem_closedBall (by rwa [hχrIn]), one_mul]
  have hg0 : g 0 = 0 := by
    rw [hgeq 0 (Metric.mem_closedBall_self hρ.le), hg₀0]
  -- the region in which `e` is a direction of strict increase of `φ`
  have hgradcont : Continuous fun x : V => gradient φ x := by
    have hfd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
    exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp hfd
  have hW₁open : IsOpen {x : V | 0 < (⟪gradient φ x, e⟫ : ℝ)} :=
    isOpen_lt continuous_const (hgradcont.inner continuous_const)
  have hx₀W₁ : x₀ ∈ {x : V | 0 < (⟪gradient φ x, e⟫ : ℝ)} := by
    simp only [Set.mem_ofPred_eq, hgrad, real_inner_smul_left, hsp.inner_e_self, mul_one]
    exact hc
  obtain ⟨O, hON, hOopen, hx₀O⟩ := mem_nhds_iff.mp hN₀
  obtain ⟨r, hr, hballr⟩ := Metric.isOpen_iff.mp (hOopen.inter hW₁open) x₀ ⟨hx₀O, hx₀W₁⟩
  set δ : ℝ := r / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set ρ₂ : ℝ := min ρ (r / 2) with hρ₂def
  have hρ₂ : 0 < ρ₂ := lt_min hρ (by positivity)
  set Ω : Set H := Metric.ball (0 : H) ρ₂ ∩ {y | |g y| < δ} with hΩdef
  have hΩopen' : IsOpen Ω :=
    Metric.isOpen_ball.inter (isOpen_Iio.preimage hgsmooth.continuous.abs)
  have h0Ω' : (0 : H) ∈ Ω := ⟨by simpa using hρ₂, by simpa [hg0] using hδ⟩
  have hΩsub : Ω ⊆ Metric.closedBall (0 : H) ρ := by
    intro y hy
    have : ‖y‖ < ρ₂ := by simpa [Metric.mem_ball, dist_zero_right] using hy.1
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (lt_of_lt_of_le this (min_le_left _ _))
  have hΩsub₀ : Ω ⊆ Ω₀ := fun y hy =>
    hclosed (Metric.closedBall_subset_closedBall (by linarith) (hΩsub hy))
  have hΩnorm : ∀ y ∈ Ω, ‖y‖ < r / 2 := by
    intro y hy
    have : ‖y‖ < ρ₂ := by simpa [Metric.mem_ball, dist_zero_right] using hy.1
    exact lt_of_lt_of_le this (min_le_right _ _)
  have hΩgraph : ∀ y ∈ Ω, φ (x₀ + ι y + g y • e) = 0 := by
    intro y hy
    rw [hgeq y (hΩsub hy)]
    exact
      hg₀graph y
        (hΩsub₀ hy)
  -- points of the cylinder sit in the ball of radius `r`
  have hpt : ∀ y : H, ‖y‖ < r / 2 → ∀ u : ℝ, |u| ≤ δ → x₀ + ι y + u • e ∈ Metric.ball x₀ r := by
    intro y hy u hu
    have hsub : (x₀ + ι y + u • e) - x₀ = ι y + u • e := by abel
    simp only [Metric.mem_ball, dist_eq_norm, hsub]
    have hn := hsp.norm_add_smul_sq y u
    have hu2 : u ^ 2 ≤ δ ^ 2 := by rw [← sq_abs u]; nlinarith [abs_nonneg u]
    nlinarith [norm_nonneg (ι y + u • e), norm_nonneg y]
  have hcylball : graphCylinder ι e x₀ Ω δ ⊆ Metric.ball x₀ r := by
    intro x hx
    have hx' := eq_graphChartMap_coord hsp x₀ x
    rw [hx']
    exact
      hpt _ (hΩnorm _ hx.1) _
        (le_of_lt hx.2)
  -- strict monotonicity of `φ` in the direction `e` inside the cylinder
  have hderiv :
    ∀ (y : H) (u : ℝ),
      HasDerivAt (fun u : ℝ => φ (x₀ + ι y + u • e)) (⟪gradient φ (x₀ + ι y + u • e), e⟫ : ℝ)
        u := by
    intro y u
    have hpath : HasDerivAt (fun u : ℝ => x₀ + ι y + u • e) e u := by
      simpa using ((hasDerivAt_id u).smul_const e).const_add (x₀ + ι y)
    have h :=
      ((hφ.differentiable (by simp) (x₀ + ι y + u • e)).hasFDerivAt).comp_hasDerivAt u hpath
    have hg : fderiv ℝ φ (x₀ + ι y + u • e) e = (⟪gradient φ (x₀ + ι y + u • e), e⟫ : ℝ) := by
      rw [← fderiv_eq_innerSL_gradient φ (x₀ + ι y + u • e)]
      rw [innerSL_apply_apply]
    rwa [hg] at h
  have hmono : ∀ y ∈ Ω, StrictMonoOn (fun u : ℝ => φ (x₀ + ι y + u • e)) (Set.Icc (-δ) δ) := by
    intro y hy
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · exact (hφ.continuous.comp (by fun_prop)).continuousOn
    · intro u hu
      have huI : u ∈ Set.Icc (-δ) δ := interior_subset hu
      have habs : |u| ≤ δ := abs_le.mpr ⟨huI.1, huI.2⟩
      rw [(hderiv y u).deriv]
      exact
        (hballr (hpt y (hΩnorm y hy) u habs)).2
  -- the side condition
  have hside :
    ∀ x ∈ graphCylinder ι e x₀ Ω δ,
      (φ x < 0 ↔ graphHeight e x₀ x < g (graphCoord ι x₀ x)) ∧
        (φ x = 0 ↔ graphHeight e x₀ x = g (graphCoord ι x₀ x)) := by
    intro x hx
    obtain ⟨hy, ht⟩ := hx
    set y : H := graphCoord ι x₀ x with hydef
    set t : ℝ := graphHeight e x₀ x with htdef
    have hxeq : x = x₀ + ι y + t • e := eq_graphChartMap_coord hsp x₀ x
    have htI : t ∈ Set.Icc (-δ) δ := by rw [Set.mem_Icc, ← abs_le]; exact ht.le
    have hsI : g y ∈ Set.Icc (-δ) δ := by
      rw [Set.mem_Icc, ← abs_le]
      exact (hy.2 : |g y| < δ).le
    have hs0 : φ (x₀ + ι y + g y • e) = 0 := hΩgraph y hy
    have hM := hmono y hy
    constructor
    · rw [hxeq]
      constructor
      · intro hlt
        have :
          (fun u : ℝ => φ (x₀ + ι y + u • e)) t < (fun u : ℝ => φ (x₀ + ι y + u • e)) (g y) := by
          simpa [hs0] using hlt
        exact (hM.lt_iff_lt htI hsI).mp this
      · intro hlt
        have := hM htI hsI hlt
        simpa [hs0] using this
    · rw [hxeq]
      constructor
      · intro heq
        have :
          (fun u : ℝ => φ (x₀ + ι y + u • e)) t = (fun u : ℝ => φ (x₀ + ι y + u • e)) (g y) := by
          simpa [hs0] using heq
        exact hM.injOn htI hsI this
      · intro heq
        rw [heq]; exact hs0
  refine
    ⟨{  height := g
        param := Ω
        depth := δ
        contDiff_height := hgsmooth
        isOpen_param := hΩopen'
        zero_mem_param := h0Ω'
        height_zero := hg0
        depth_pos := hδ
        abs_height_lt := fun y hy => hy.2
        inner_gradient_pos := fun x hx => (hballr (hcylball hx)).2
        lt_iff := fun x hx => (hside x hx).1
        eq_iff := fun x hx => (hside x hx).2 }, ?_⟩
  exact fun x hx => hON (hballr (hcylball hx)).1

end Repr


/-! ### The area formula for a translated graph -/

section Area

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Translation invariance of the normalized Hausdorff measure. -/
theorem hausdorffNormalized_image_add_left (x₀ : V) (d : ℕ) (A : Set V) :
    KLS.hausdorffNormalized V d ((fun x => x₀ + x) '' A)
      = KLS.hausdorffNormalized V d A := by
  rw [KLS.hausdorffNormalized, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  congr 1
  exact (isometry_add_left x₀).hausdorffMeasure_image (Or.inl (Nat.cast_nonneg d)) A

/-- **Area formula for a graph centred at `x₀`.**  The normalized `k`-dimensional Hausdorff
measure of the piece of graph `y ↦ x₀ + ι y + g y • e` over a measurable parameter set `s` is the
integral of the graph Jacobian `√(1 + ‖∇g‖²)` over `s`, with `k = finrank ℝ H`.

This is `Analysis.hausdorffNormalized_image_graphMap` transported by the translation `x ↦ x₀ + x`,
which is an isometry and therefore preserves every Hausdorff measure. -/
theorem hausdorffNormalized_image_graphChartMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (x₀ : V) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) :
    KLS.hausdorffNormalized V (Module.finrank ℝ H) (graphChartMap ι e x₀ g '' s)
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y)) ∂(volume : Measure H) := by
  have himg : graphChartMap ι e x₀ g '' s = (fun x => x₀ + x) '' (graphMap ι e g '' s) := by
    rw [← Set.image_comp]; rfl
  rw [himg, hausdorffNormalized_image_add_left,
    hausdorffNormalized_image_graphMap ι he hperp hg hs]

end Area

end FunctionalInequalities.Analysis
