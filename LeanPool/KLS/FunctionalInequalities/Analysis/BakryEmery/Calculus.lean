/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Local differential calculus

Hessians, directional derivatives, gradients and standard-basis trace identities.
These are pointwise tools; there is no measure, semigroup or curvature estimate here.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

section Hessian

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bilinear second Fréchet derivative of a `C²` real-valued function is symmetric. -/
theorem bilinearIteratedFDerivTwo_symm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w =
      bilinearIteratedFDerivTwo ℝ f x w v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons

end Hessian

section PointwiseTools

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

section Pointwise

omit [CompleteSpace E] in
/-- The Laplacian of a function on a finite-dimensional inner product space is the trace of its
second Fréchet derivative in the standard orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv (f : E → ℝ) (x : E) :
    Laplacian.laplacian f x =
      ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) := by
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  rfl

/-- The inner product of two gradients is the sum of the products of the directional
derivatives in the standard orthonormal basis. -/
theorem inner_gradient_eq_sum_fderiv_mul_fderiv (f g : E → ℝ) (x : E) :
    ⟪gradient f x, gradient g x⟫ =
      ∑ i, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ g x (stdOrthonormalBasis ℝ E i) := by
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_gradient_left, real_inner_comm, inner_gradient_left]

section LaplacianRegularity

omit [CompleteSpace E]
/-- The Laplacian of a `C²` function is continuous. -/
theorem continuous_laplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) := h1.continuous_fderiv one_ne_zero
  have : Laplacian.laplacian f = fun x =>
      ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) :=
    funext fun x => laplacian_eq_sum_fderiv_fderiv f x
  rw [this]
  exact continuous_finsetSum _ fun i _ =>
    (h2.clm_apply continuous_const).clm_apply continuous_const

/-- The Laplacian of a compactly supported function has compact support. -/
theorem hasCompactSupport_laplacian {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (Laplacian.laplacian f) := by
  have : Laplacian.laplacian f = (fun A : E →L[ℝ] E →L[ℝ] ℝ =>
      ∑ i, A (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)) ∘ fderiv ℝ (fderiv ℝ f) :=
    funext fun x => laplacian_eq_sum_fderiv_fderiv f x
  rw [this]
  exact ((hfc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left (by simp)

end LaplacianRegularity

section GradientRegularity

omit [FiniteDimensional ℝ E]
/-- A function of nonzero differentiability order has a continuous gradient. -/
theorem continuous_gradient_of_contDiff {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {f : V → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (hn : n ≠ 0) : Continuous (gradient f) := by
  change Continuous (fun x ↦ (toDual ℝ V).symm (fderiv ℝ f x))
  exact (toDual ℝ V).symm.continuous.comp (hf.continuous_fderiv hn)

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  continuous_gradient_of_contDiff hf one_ne_zero

/-- The gradient of a compactly supported function has compact support. -/
theorem hasCompactSupport_gradient {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (gradient f) := by
  change HasCompactSupport ((toDual ℝ E).symm ∘ fderiv ℝ f)
  exact (hfc.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

end GradientRegularity

end Pointwise

end PointwiseTools

section LocalDirectionalCommutation
open Filter
open scoped Topology

private abbrev D {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (v : E) : E → ℝ := fun y => fderiv ℝ f y v

private theorem smooth_D_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {x : E} {k : ℕ∞ω} (hf : ContDiffAt ℝ (k + 1) f x) (v : E) : ContDiffAt ℝ k (D f v) x :=
  (hf.fderiv_right le_rfl).clm_apply contDiffAt_const

private theorem D_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    D f v =ᶠ[𝓝 x] D g v :=
  h.fderiv.mono fun _ hy => congrArg (fun L : E →L[ℝ] ℝ => L v) hy

private theorem D_comm_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    D (D f v) w x = D (D f w) v x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  have he (a b : E) : D (D f a) b x = fderiv ℝ (fderiv ℝ f) x b a := by
    change fderiv ℝ (fun y => fderiv ℝ f y a) x b = _
    rw [(hfd.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).fderiv]
    simp
  rw [he, he]
  exact (hf.isSymmSndFDerivAt (by norm_num)) w v

private theorem D_comm_near {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {x : E} (hf : ContDiffAt ℝ 3 f x) (v w : E) : D (D f v) w =ᶠ[𝓝 x] D (D f w) v := by
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y :=
    (hf.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)).eventually (by norm_num)
  exact hn.mono fun _ hy => D_comm_at hy v w

/-- Fourth directional derivatives of a locally `C⁴` function permit exchange of their pairs.
No inner-product, finite-dimensionality or completeness assumption is needed. -/
theorem fderiv_fourth_pair_comm_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x) (u v w z : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z' =>
      fderiv ℝ (fun t => fderiv ℝ f t v) z' u) y z) x w =
    fderiv ℝ (fun y => fderiv ℝ (fun z' =>
      fderiv ℝ (fun t => fderiv ℝ f t z) z' w) y v) x u := by
  change D (D (D (D f v) u) z) w x = D (D (D (D f z) w) v) u x
  have h3 (a : E) : ContDiffAt ℝ 3 (D f a) x := smooth_D_at hf a
  have h2 (a b : E) : ContDiffAt ℝ 2 (D (D f a) b) x := smooth_D_at (h3 a) b
  calc
    _ = D (D (D (D f v) z) u) w x :=
      (D_congr (D_comm_near (h3 v) u z) w).eq_of_nhds
    _ = D (D (D (D f z) v) u) w x :=
      (D_congr (D_congr (D_comm_near (hf.of_le (by norm_num)) v z) u) w).eq_of_nhds
    _ = D (D (D (D f z) u) v) w x :=
      (D_congr (D_comm_near (h3 z) v u) w).eq_of_nhds
    _ = D (D (D (D f z) u) w) v x := D_comm_at (h2 z u) v w
    _ = D (D (D (D f z) w) u) v x :=
      (D_congr (D_comm_near (h3 z) u w) v).eq_of_nhds
    _ = _ := D_comm_at (h2 z w) u v

/-- Actual third-derivative commutation, using only local finite-order data. -/
theorem fderiv_fderiv_fderiv_apply_comm_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v) x v := by
  change D (D (D f v) v) w x = D (D (D f w) v) v x
  have h2 : ContDiffAt ℝ 2 (D f v) x := smooth_D_at hf v
  calc
    _ = D (D (D f v) w) v x := D_comm_at h2 v w
    _ = _ := (D_congr (D_comm_near hf v w) v).eq_of_nhds

end LocalDirectionalCommutation

section DifferentialTools

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Directional derivatives -/

section Directional

/-- The directional derivative `y ↦ D f (y) v` of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem contDiff_fderiv_apply {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) (v : E) : ContDiff ℝ m (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- The directional derivative of a `C²` function is differentiable. -/
theorem differentiable_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v : E) :
    Differentiable ℝ (fun y => fderiv ℝ f y v) :=
  (contDiff_fderiv_apply hf (m := 1) (by norm_num) v).differentiable one_ne_zero

/-- The second derivative applied to `v, w` is the derivative in direction `v` of the directional
derivative in direction `w`. -/
theorem fderiv_fderiv_apply {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [(hf.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  simp

/-- The bilinear Hessian of a `C²` function as an iterated directional derivative:
`D²f(x)(v, w) = D (y ↦ D f (y) w) x v`. -/
theorem bilinearIteratedFDerivTwo_eq_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [fderiv_fderiv_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)]
  rfl

/-- Mixed directional derivatives of a `C²` function commute (in directional form). -/
theorem fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fun y => fderiv ℝ f y v) x w := by
  rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hf, ←
    bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
  exact bilinearIteratedFDerivTwo_symm hf x v w

/-- Third-order commutation for a `C³` function: `∂_w ∂_v ∂_v f = ∂_v ∂_v ∂_w f`. The first
step commutes the two outer derivatives of the `C²` function `∂_v f`; the second commutes the two
inner derivatives of `f` at every point. -/
theorem fderiv_fderiv_fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v) x v := by
  exact fderiv_fderiv_fderiv_apply_comm_at hf.contDiffAt v w

/-- Product rule for directional derivatives. -/
theorem fderiv_mul_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y * g y) x v = f x * fderiv ℝ g x v + g x * fderiv ℝ f x v := by
  rw [fderiv_fun_mul hf hg]
  simp

/-- Directional derivative of a constant multiple. -/
theorem fderiv_const_mul_apply {g : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x) (c : ℝ) (v : E) :
    fderiv ℝ (fun y => c * g y) x v = c * fderiv ℝ g x v := by
  rw [fderiv_const_mul hg c]
  simp

/-- Sum rule for directional derivatives. -/
theorem fderiv_sum_apply {ι : Type*} (s : Finset ι) {g : ι → E → ℝ} {x : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) (v : E) :
    fderiv ℝ (fun y => ∑ i ∈ s, g i y) x v = ∑ i ∈ s, fderiv ℝ (g i) x v := by
  rw [fderiv_fun_sum hg]
  simp

/-- Difference rule for directional derivatives. -/
theorem fderiv_sub_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y - g y) x v = fderiv ℝ f x v - fderiv ℝ g x v := by
  rw [fderiv_fun_sub hf hg]
  simp

/-- Sum rule for directional derivatives. -/
theorem fderiv_add_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y + g y) x v = fderiv ℝ f x v + fderiv ℝ g x v := by
  rw [fderiv_fun_add hf hg]
  simp

end Directional

section HessianCommutation

private theorem smooth_D {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) : ContDiff ℝ ∞ (D f v) :=
  contDiff_fderiv_apply hf (by simp) v

private theorem D_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v w : E) :
    D (D f v) w = D (D f w) v := by
  ext x
  exact fderiv_apply_comm (hf.of_le (WithTop.coe_le_coe.mpr le_top)) x w v

/-- Entries of the Hessian of a `C^∞` function are `C^∞`. -/
theorem contDiff_bilinearIteratedFDerivTwo_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (u v : E) :
    ContDiff ℝ ∞ (fun y => bilinearIteratedFDerivTwo ℝ f y u v) := by
  have heq : (fun y => bilinearIteratedFDerivTwo ℝ f y u v) = D (D f v) u :=
    funext fun y => bilinearIteratedFDerivTwo_eq_fderiv_apply
      (hf.of_le (WithTop.coe_le_coe.mpr le_top)) y u v
  rw [heq]
  exact smooth_D (smooth_D hf v) u

/-- The derivative of a genuine Hessian operatorEntry permits swapping its derivative direction
with either Hessian slot; no third-order symmetry is assumed. -/
theorem fderiv_bilinearIteratedFDerivTwo_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v w : E) :
    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ f y u v) x w =
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ f y w v) x u := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have heq (a c : E) : (fun y => bilinearIteratedFDerivTwo ℝ f y a c) = D (D f c) a :=
    funext fun y => bilinearIteratedFDerivTwo_eq_fderiv_apply h2 y a c
  rw [heq, heq]
  exact congrFun (D_comm (smooth_D hf v) u w) x

/-- The actual second derivative of a Hessian operatorEntry equals the fourth derivative with
its two pairs exchanged. This is proved by successive actual C² directional commutations. -/
theorem bilinearIteratedFDerivTwo_bilinearIteratedFDerivTwo_comm {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (x u v w z : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => bilinearIteratedFDerivTwo ℝ f y u v) x w z =
      bilinearIteratedFDerivTwo ℝ (fun y => bilinearIteratedFDerivTwo ℝ f y w z) x u v := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have heq (a c : E) : (fun y => bilinearIteratedFDerivTwo ℝ f y a c) = D (D f c) a :=
    funext fun y => bilinearIteratedFDerivTwo_eq_fderiv_apply h2 y a c
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply
      ((contDiff_bilinearIteratedFDerivTwo_apply hf u v).of_le (WithTop.coe_le_coe.mpr le_top)),
    bilinearIteratedFDerivTwo_eq_fderiv_apply
      ((contDiff_bilinearIteratedFDerivTwo_apply hf w z).of_le (WithTop.coe_le_coe.mpr le_top)),
    heq, heq]
  exact fderiv_fourth_pair_comm_at (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) u v w z

/--
Pointwise version of `bilinearIteratedFDerivTwo_eq_fderiv_apply` (only `C²` at the point). -/
theorem bilinearIteratedFDerivTwo_eq_fderiv_apply_at {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    bilinearIteratedFDerivTwo ℝ f x u v = fderiv ℝ (fun y => fderiv ℝ f y v) x u := by
  rw [fderiv_fderiv_apply
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]
  rfl

/-- Pointwise symmetry of the Hessian (only `C²` at the point). -/
theorem bilinearIteratedFDerivTwo_symm_at {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    bilinearIteratedFDerivTwo ℝ f x u v = bilinearIteratedFDerivTwo ℝ f x v u := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons

/-- The line `t ↦ x + t v` has derivative `v`. -/
theorem hasDerivAt_line (x v : E) (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

open Filter Topology in
/-- A `C²` function convex on an open set has positive semidefinite Hessian there. -/
theorem bilinearIteratedFDerivTwo_self_nonneg_of_convexOn_open {V : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 2 V U) (hc : ConvexOn ℝ U V)
    {x : E} (hx : x ∈ U) (v : E) : 0 ≤ bilinearIteratedFDerivTwo ℝ V x v v := by
  let S : Set ℝ := (fun t : ℝ => x + t • v) ⁻¹' U
  have hline : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hS : IsOpen S := hU.preimage hline
  have h0 : (0 : ℝ) ∈ S := by simpa [S] using hx
  have hlineMap : (AffineMap.lineMap x (x + v) : ℝ → E) = fun t : ℝ => x + t • v := by
    ext t
    simp [AffineMap.lineMap_apply_module', add_comm]
  have hfconv : ConvexOn ℝ S (fun t : ℝ => V (x + t • v)) := by
    simpa only [hlineMap, Function.comp_def] using hc.comp_affineMap (AffineMap.lineMap x (x + v))
  have hd (t : ℝ) (ht : t ∈ S) : HasDerivAt (fun t : ℝ => V (x + t • v))
      (fderiv ℝ V (x + t • v) v) t :=
    ((hV.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_line x v t)
  have hmono : MonotoneOn (deriv (fun t : ℝ => V (x + t • v))) S :=
    hfconv.monotoneOn_deriv (fun t ht => (hd t ht).differentiableAt)
  have hnonneg := hmono.derivWithin_nonneg (x := (0 : ℝ))
  rw [derivWithin_of_mem_nhds (hS.mem_nhds h0)] at hnonneg
  have heq : deriv (fun t : ℝ => V (x + t • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => fderiv ℝ V (x + t • v) v) := by
    filter_upwards [hS.mem_nhds h0] with t ht
    exact (hd t ht).deriv
  rw [heq.deriv_eq] at hnonneg
  have hVx := hV.contDiffAt (hU.mem_nhds hx)
  have hdF := (hVx.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hder : HasDerivAt (fun t : ℝ => fderiv ℝ V (x + t • v) v)
      (fderiv ℝ (fderiv ℝ V) x v v) 0 := by
    have hd0 : HasFDerivAt (fderiv ℝ V) (fderiv ℝ (fderiv ℝ V) x) (x + (0 : ℝ) • v) := by
      simp only [zero_smul, add_zero]
      exact hdF.hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ V (x + t • v))
        (fderiv ℝ (fderiv ℝ V) x v) 0 := hd0.comp_hasDerivAt 0 (hasDerivAt_line x v 0)
    simpa using hcomp.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [hder.deriv] at hnonneg
  exact hnonneg

end HessianCommutation

/-! ### Gradient calculus -/

section Quadratic

/-- The Hessian of `‖·‖²` is `2⟪v, v⟫`. -/
theorem bilinearIteratedFDerivTwo_norm_sq (x v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y : E => ‖y‖ ^ 2) x v v = 2 * ‖v‖ ^ 2 := by
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply (contDiff_norm_sq ℝ) x v v]
  have hfun : (fun y : E => fderiv ℝ (fun z : E => ‖z‖ ^ 2) y v) = fun y => 2 * ⟪y, v⟫ := by
    funext y
    rw [(hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv]
    simp
  rw [hfun]
  have h : HasFDerivAt (fun y : E => 2 * ⟪y, v⟫) ((2 : ℝ) • innerSL ℝ v) x := by
    simpa only [innerSL_apply_apply, real_inner_comm] using
      ((innerSL ℝ v).hasFDerivAt (x := x)).const_mul 2
  rw [h.fderiv]
  simp

/-- Adding `δ/2 ‖·‖²` adds `δ‖v‖²` to the Hessian quadratic form. -/
theorem bilinearIteratedFDerivTwo_add_quadratic {f : E → ℝ} (hf : ContDiff ℝ 2 f) (δ : ℝ)
    (x v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => f y + δ / 2 * ‖y‖ ^ 2) x v v =
      bilinearIteratedFDerivTwo ℝ f x v v + δ * ‖v‖ ^ 2 := by
  let q : E → ℝ := fun y => δ / 2 * ‖y‖ ^ 2
  have hq : ContDiff ℝ 2 q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hsum := iteratedFDeriv_add_apply (x := x) hf.contDiffAt hq.contDiffAt
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ 2 (f + q) x) ![v, v] = _
  rw [hsum]
  simp only [add_apply]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  have heq :
    bilinearIteratedFDerivTwo ℝ q x v v =
      δ / 2 * bilinearIteratedFDerivTwo ℝ (fun y : E => ‖y‖ ^ 2) x v v := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hq,
      bilinearIteratedFDerivTwo_eq_fderiv_apply (contDiff_norm_sq ℝ)]
    have hfun :
      (fun y => fderiv ℝ q y v) = fun y => δ / 2 * fderiv ℝ (fun z : E => ‖z‖ ^ 2) y v := by
      funext y
      dsimp only [q]
      rw [fderiv_const_mul]
      rfl
      exact
        (show ContDiff ℝ 2 (fun z : E => ‖z‖ ^ 2) from contDiff_norm_sq ℝ).differentiable
          (by norm_num) y
    rw [hfun, fderiv_const_mul]
    rfl
    exact differentiable_fderiv_apply (contDiff_norm_sq ℝ) v x
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, heq, bilinearIteratedFDerivTwo_norm_sq]
  ring

section AffineHessian
open Filter
open scoped Topology

/-- Local C2 chain rule for the Hessian form under an affine continuous linear equivalence.
No finite-dimensionality or completeness hypothesis is required. -/
theorem bilinearIteratedFDerivTwo_comp_affine_at {V : E → ℝ} (L : E ≃L[ℝ] E) (c x u v : E)
    (hV : ContDiffAt ℝ 2 V (L x + c)) :
    bilinearIteratedFDerivTwo ℝ (fun y => V (L y + c)) x u v =
      bilinearIteratedFDerivTwo ℝ V (L x + c) (L u) (L v) := by
  have hA (y : E) : HasFDerivAt (fun z => L z + c) (L : E →L[ℝ] E) y :=
    L.hasFDerivAt.add_const c
  have hW : ContDiffAt ℝ 2 (fun y => V (L y + c)) x :=
    hV.comp x (L.contDiff.add contDiff_const).contDiffAt
  have hn : ∀ᶠ z in 𝓝 (L x + c), DifferentiableAt ℝ V z :=
    ((hV.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)).mono
      (fun z hz => hz.differentiableAt one_ne_zero)
  have hf :
    (fun y => fderiv ℝ (fun z => V (L z + c)) y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ V (L y + c) (L v)) := by
    filter_upwards [(hA x).continuousAt.eventually hn] with y hy
    exact congrArg (fun T : E →L[ℝ] ℝ => T v) ((hy.hasFDerivAt.comp y (hA y)).fderiv)
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply_at hW,
    bilinearIteratedFDerivTwo_eq_fderiv_apply_at hV, hf.fderiv.eq_of_nhds]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ V y (L v)) (L x + c) :=
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  exact congrArg (fun T : E →L[ℝ] ℝ => T u) ((hd.hasFDerivAt.comp x (hA x)).fderiv)

/-- Chain rule for the Hessian quadratic form under an affine change of variables `y ↦ L y + c`. -/
theorem bilinearIteratedFDerivTwo_comp_affine {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (L : E ≃L[ℝ] E) (c x u v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => V (L y + c)) x u v =
      bilinearIteratedFDerivTwo ℝ V (L x + c) (L u) (L v) := by
  exact bilinearIteratedFDerivTwo_comp_affine_at L c x u v hV.contDiffAt

end AffineHessian

section CrossType
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Chain rule for the Hessian form under a continuous linear map `T : F → E` (possibly between
different spaces). -/
theorem bilinearIteratedFDerivTwo_comp_clm {V : E → ℝ} (hV : ContDiff ℝ 2 V) (T : F →L[ℝ] E)
    (x u v : F) :
    bilinearIteratedFDerivTwo ℝ (fun y => V (T y)) x u v =
      bilinearIteratedFDerivTwo ℝ V (T x) (T u) (T v) := by
  have hW : ContDiff ℝ 2 (fun y => V (T y)) := hV.comp T.contDiff
  have hfirst (y : F) : fderiv ℝ (fun z => V (T z)) y = (fderiv ℝ V (T y)).comp T :=
    ((hV.differentiable (by norm_num) (T y)).hasFDerivAt.comp y T.hasFDerivAt).fderiv
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hW x u v,
    bilinearIteratedFDerivTwo_eq_fderiv_apply hV (T x) (T u) (T v)]
  have hfun : (fun y => fderiv ℝ (fun z => V (T z)) y v) = fun y => fderiv ℝ V (T y) (T v) := by
    funext y
    rw [hfirst]
    rfl
  rw [hfun]
  have hsecond :=
    ((differentiable_fderiv_apply hV (T v) (T x)).hasFDerivAt.comp x T.hasFDerivAt).fderiv
  exact congrArg (fun S : F →L[ℝ] ℝ => S u) hsecond

end CrossType

/-- **Product rule for the Hessian quadratic/bilinear form**: for `f, g ∈ C²`,
`D²(fg)(x)(u, v) = f(x) D²g(x)(u, v) + g(x) D²f(x)(u, v) + Df(x)u · Dg(x)v + Dg(x)u · Df(x)v`
(Letwin (2.3) prerequisite; `laplacian_mul` is the identity-metric trace of this). -/
theorem bilinearIteratedFDerivTwo_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x u v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => f y * g y) x u v =
      f x * bilinearIteratedFDerivTwo ℝ g x u v + g x * bilinearIteratedFDerivTwo ℝ f x u v +
        fderiv ℝ f x u * fderiv ℝ g x v + fderiv ℝ g x u * fderiv ℝ f x v := by
    have hfd : ∀ y : E, DifferentiableAt ℝ f y := fun y =>
      hf.differentiable (by norm_num) y
    have hgd : ∀ y : E, DifferentiableAt ℝ g y := fun y =>
      hg.differentiable (by norm_num) y
    have h1 :
        (fun y => fderiv ℝ (fun z => f z * g z) y v) =
          fun y => f y * fderiv ℝ g y v + g y * fderiv ℝ f y v := by
      funext y
      exact fderiv_mul_apply (hfd y) (hgd y) v
    have hA : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y v) x :=
      (hfd x).mul (differentiable_fderiv_apply hg v x)
    have hB : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y v) x :=
      (hgd x).mul (differentiable_fderiv_apply hf v x)
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply (hf.mul hg) x u v,
      bilinearIteratedFDerivTwo_eq_fderiv_apply hg x u v,
      bilinearIteratedFDerivTwo_eq_fderiv_apply hf x u v,
      h1, fderiv_add_apply hA hB,
      fderiv_mul_apply (hfd x) (differentiable_fderiv_apply hg v x),
      fderiv_mul_apply (hgd x) (differentiable_fderiv_apply hf v x)]
    ring

end Quadratic

section Gradient

variable [CompleteSpace E]

/-- On an open domain the gradient of a genuine C^n function is C^m when
m+1<=n. No global smooth extension or finite-dimensional hypothesis is needed. -/
theorem contDiffOn_gradient {f : E → ℝ} {s : Set E} {n m : WithTop ℕ∞} (hs : IsOpen s)
    (hf : ContDiffOn ℝ n f s) (hmn : m + 1 ≤ n) : ContDiffOn ℝ m (gradient f) s := by
  change ContDiffOn ℝ m ((toDual ℝ E).symm ∘ fderiv ℝ f) s
  exact (toDual ℝ E).symm.contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hs hmn)

/-- The gradient of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem contDiff_gradient {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradient f) := by
  simpa only [contDiffOn_univ] using contDiffOn_gradient isOpen_univ hf.contDiffOn hmn

/-- The gradient vanishes outside the closed support, without differentiability assumptions. -/
theorem gradient_eq_zero_of_notMem_tsupport {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) :
    gradient f x = 0 := by
  rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]

/-- Product rule for the gradient. -/
theorem gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp

/-- The gradient of a negation, with no differentiability hypothesis. -/
theorem gradient_neg (f : E → ℝ) (x : E) : gradient (fun y => -f y) x = -gradient f x := by
  unfold gradient
  rw [fderiv_fun_neg, map_neg]

/-- Chain rule for the gradient: `∇(Φ ∘ g) = Φ'(g) ∇g`. -/
theorem gradient_comp {Φ : ℝ → ℝ} {g : E → ℝ} {x : E} (hΦ : DifferentiableAt ℝ Φ (g x))
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => Φ (g y)) x = deriv Φ (g x) • gradient g x := by
  have hcomp : HasFDerivAt (fun y => Φ (g y)) (deriv Φ (g x) • fderiv ℝ g x) x :=
    hΦ.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt
  unfold gradient
  rw [hcomp.fderiv, map_smul]

/-- Difference rule for the gradient. -/
theorem gradient_sub {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y - g y) x = gradient f x - gradient g x := by
  unfold gradient
  rw [fderiv_fun_sub hf hg, map_sub]

/-- `V ∘ ∇φ` is `C^∞` at `x` when `V` is `C^∞` on an open set containing `∇φ(x)` (`V` need not be
globally smooth). -/
theorem contDiffAt_comp_gradient_of_mem {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U) {x : E}
    (hx : gradient φ x ∈ U) : ContDiffAt ℝ ∞ (fun y => V (gradient φ y)) x := by
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  exact (hV.contDiffAt (hU.mem_nhds hx)).comp x hg.contDiffAt

/-- `V ∘ ∇φ` is `C^∞` when `V` is `C^∞` on an open set containing the range of `∇φ`. -/
theorem contDiff_comp_gradient_of_range_subset {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : ∀ x, gradient φ x ∈ U) : ContDiff ℝ ∞ (fun y => V (gradient φ y)) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  exact contDiffAt_comp_gradient_of_mem hφ hU hV (hRange x)

end Gradient

/-! ### Expansions in the standard orthonormal basis -/

section StdBasis

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A bilinear form on two expansions `∑ aᵢ vᵢ`. -/
theorem bilinear_sum_smul_sum_smul {ι : Type*} [Fintype ι] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (a : ι → ℝ) (v : ι → E) :
    B (∑ i, a i • v i) (∑ j, a j • v j) = ∑ i, ∑ j, a i * a j * B (v i) (v j) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [CompleteSpace E]

/-- The gradient expanded in the standard orthonormal basis. -/
theorem gradient_eq_sum_fderiv_smul (f : E → ℝ) (x : E) :
    gradient f x =
      ∑ i, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) • stdOrthonormalBasis ℝ E i := by
  conv_lhs => rw [← (stdOrthonormalBasis ℝ E).sum_repr' (gradient f x)]
  simp only [real_inner_comm, inner_gradient_left]

/-- `‖∇f‖²` is the sum of the squared directional derivatives in the standard orthonormal basis. -/
theorem norm_gradient_sq_eq_sum (f : E → ℝ) (y : E) :
    ‖gradient f y‖ ^ 2 = ∑ i, fderiv ℝ f y (stdOrthonormalBasis ℝ E i) ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  simp only [inner_gradient_left]

/-- A bilinear Hessian evaluated twice on a gradient, expanded in the standard basis. -/
theorem bilinearIteratedFDerivTwo_gradient_gradient (U f : E → ℝ) (x : E) :
    bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) =
      ∑ i,
        ∑ j,
          fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
            bilinearIteratedFDerivTwo ℝ U x (stdOrthonormalBasis ℝ E i)
              (stdOrthonormalBasis ℝ E j) := by
  rw [gradient_eq_sum_fderiv_smul]
  exact bilinear_sum_smul_sum_smul _ _ _

section LaplacianCoordinates

omit [CompleteSpace E]
/-- The Laplacian as the trace of the iterated directional derivatives, at a point where the
derivative is differentiable. -/
theorem laplacian_eq_sum_fderiv_apply_fderiv_apply {g : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) :
    Laplacian.laplacian g x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  exact Finset.sum_congr rfl fun i _ => (fderiv_fderiv_apply hg _ _).symm

/-- The Laplacian of a `C²` function as a function: the trace of the iterated directional
derivatives in the standard orthonormal basis. -/
theorem laplacian_eq_fun_sum {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    Laplacian.laplacian g = fun x =>
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) :=
  funext fun x => laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)

/-- The Laplacian of a `C^n` function is `C^m` when `m + 2 ≤ n`. -/
theorem contDiff_laplacian {g : E → ℝ} {n m : WithTop ℕ∞} (hg : ContDiff ℝ n g) (hmn : m + 2 ≤ n) :
    ContDiff ℝ m (Laplacian.laplacian g) := by
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by simp) hmn
  rw [laplacian_eq_fun_sum (hg.of_le h2)]
  refine ContDiff.sum fun i _ => ?_
  refine contDiff_fderiv_apply (contDiff_fderiv_apply hg ?_ _) le_rfl _
  calc m + 1 + 1 = m + 2 := by rw [add_assoc]; norm_num
    _ ≤ n := hmn

end LaplacianCoordinates

/-- **Chain rule for the Laplacian.** If `h` has derivative `h' (G y)` at every value `G y`, and
`h'` has derivative `h'' (G x)` at `G x`, then `Δ(h ∘ G)(x) = h'(G x) ΔG(x) + h''(G x) ‖∇G(x)‖²`
for a `C²` function `G`. No global smoothness of `h` is required, so `h = √(ε + ·)` is allowed
on nonnegative `G`. -/
theorem laplacian_comp {h h' h'' : ℝ → ℝ} {G : E → ℝ} (hG : ContDiff ℝ 2 G)
    (hh : ∀ y, HasDerivAt h (h' (G y)) (G y)) {x : E} (hh' : HasDerivAt h' (h'' (G x)) (G x)) :
    Laplacian.laplacian (fun y => h (G y)) x =
      h' (G x) * Laplacian.laplacian G x + h'' (G x) * ‖gradient G x‖ ^ 2 := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hfd : ∀ y, fderiv ℝ (fun y => h (G y)) y = h' (G y) • fderiv ℝ G y := fun y =>
    ((hh y).comp_hasFDerivAt y (hG1 y).hasFDerivAt).fderiv
  have hdG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have hh'G : DifferentiableAt ℝ (fun y => h' (G y)) x :=
    hh'.differentiableAt.comp x (hG1 x)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (fun y => h (G y))) x := by
    rw [show fderiv ℝ (fun y => h (G y)) = fun y => h' (G y) • fderiv ℝ G y from funext hfd]
    exact hh'G.smul hdG
  have hh'd : ∀ v, fderiv ℝ (fun y => h' (G y)) x v = h'' (G x) * fderiv ℝ G x v := fun v => by
    have hc : HasFDerivAt (fun y => h' (G y)) (h'' (G x) • fderiv ℝ G x) x :=
      hh'.comp_hasFDerivAt x (hG1 x).hasFDerivAt
    rw [hc.fderiv]; rfl
  rw [laplacian_eq_sum_fderiv_apply_fderiv_apply hdiff,
    laplacian_eq_sum_fderiv_apply_fderiv_apply hdG, norm_gradient_sq_eq_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun y => fderiv ℝ (fun y => h (G y)) y (stdOrthonormalBasis ℝ E i)) =
      fun y => h' (G y) * fderiv ℝ G y (stdOrthonormalBasis ℝ E i) :=
    funext fun y => by rw [hfd y]; rfl
  rw [hfun, fderiv_mul_apply hh'G (differentiable_fderiv_apply hG _ x), hh'd]
  ring

/-- Product rule for the Laplacian: `Δ(fg) = f Δg + g Δf + 2 ⟪∇f, ∇g⟫`. -/
theorem laplacian_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    Laplacian.laplacian (fun y => f y * g y) x =
      f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x +
        2 * ⟪gradient f x, gradient g x⟫ := by
  have hfg : ContDiff ℝ 2 (fun y => f y * g y) := hf.mul hg
  have hfd : ∀ y, DifferentiableAt ℝ f y := fun y => hf.differentiable (by norm_num) y
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by norm_num) y
  rw [laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hfg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    inner_gradient_eq_sum_fderiv_mul_fderiv]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => fderiv ℝ (fun z => f z * g z) y (stdOrthonormalBasis ℝ E i)) =
      fun y => f y * fderiv ℝ g y (stdOrthonormalBasis ℝ E i) +
        g y * fderiv ℝ f y (stdOrthonormalBasis ℝ E i) :=
    funext fun y => fderiv_mul_apply (hfd y) (hgd y) _
  have hA : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x :=
    (hfd x).mul (differentiable_fderiv_apply hg _ x)
  have hB : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y (stdOrthonormalBasis ℝ E i)) x :=
    (hgd x).mul (differentiable_fderiv_apply hf _ x)
  rw [h1, fderiv_add_apply hA hB, fderiv_mul_apply (hfd x) (differentiable_fderiv_apply hg _ x),
    fderiv_mul_apply (hgd x) (differentiable_fderiv_apply hf _ x)]
  ring

/--
The nondivergence operator `L_{A,b} f(x) = ∑_{ij} A(x)_{ij} D²f(x)(e_i, e_j) − ∑_i b(x)_i
Df(x)(e_i)` in
the standard orthonormal basis `e`, for an arbitrary real coefficient field `A` and drift `b`
(Letwin (2.3); there `A = (∇²φ)⁻¹`, `b_i = ∂_iV ∘ ∇φ`). -/
noncomputable def nondivergenceOperator
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (b : E → Fin (Module.finrank ℝ E) → ℝ) (f : E → ℝ) (x : E) : ℝ :=
  (∑ i,
      ∑ j,
        A x i j *
          bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j)) -
    ∑ i, b x i * fderiv ℝ f x (stdOrthonormalBasis ℝ E i)

section ProductFactors

omit [FiniteDimensional ℝ E] [CompleteSpace E]
private lemma nondivergenceOperator_mul_factor_double
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (x : E) (c : ℝ)
    (H : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i, ∑ j, A x i j * (c * H i j)) =
      c * ∑ i, ∑ j, A x i j * H i j := by
  calc
    (∑ i, ∑ j, A x i j * (c * H i j)) =
        ∑ i, ∑ j, c * (A x i j * H i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, c * ∑ j, A x i j * H i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = c * ∑ i, ∑ j, A x i j * H i j := by
      rw [Finset.mul_sum]

private lemma nondivergenceOperator_mul_factor_single
    (b : E → Fin (Module.finrank ℝ E) → ℝ) (x : E) (c : ℝ)
    (H : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i, b x i * (c * H i)) =
      c * ∑ i, b x i * H i := by
  calc
    (∑ i, b x i * (c * H i)) =
        ∑ i, c * (b x i * H i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i, b x i * H i := by
      rw [Finset.mul_sum]

end ProductFactors

section ProductExpansion

omit [CompleteSpace E]
private lemma nondivergenceOperator_mul_mixed_sum
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hA : ∀ x i j, A x i j = A x j i) (x : E)
    (f g : E → ℝ) :
    (∑ i, ∑ j, A x i j *
        (fderiv ℝ g x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E j))) =
      ∑ i, ∑ j, A x i j *
        (fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ g x (stdOrthonormalBasis ℝ E j)) := by
  classical
  calc
    (∑ i, ∑ j, A x i j *
        (fderiv ℝ g x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E j))) =
        ∑ j, ∑ i, A x j i *
          (fderiv ℝ g x (stdOrthonormalBasis ℝ E i) *
            fderiv ℝ f x (stdOrthonormalBasis ℝ E j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [hA x i j]
    _ = ∑ j, ∑ i, A x j i *
        (fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          fderiv ℝ g x (stdOrthonormalBasis ℝ E i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      ring
    _ = ∑ i, ∑ j, A x i j *
        (fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ g x (stdOrthonormalBasis ℝ E j)) := by
      rw [Finset.sum_comm]

/-- **Letwin (2.3), the product rule for `L_{A,b}`** with symmetric `A(x)`:
`L(fg) = f Lg + g Lf + 2 ∑_{ij} A_{ij} ∂_i f ∂_j g`. -/
theorem nondivergenceOperator_mul
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hA : ∀ x i j, A x i j = A x j i) (b : E → Fin (Module.finrank ℝ E) → ℝ)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    nondivergenceOperator A b (fun y => f y * g y) x =
      f x * nondivergenceOperator A b g x + g x * nondivergenceOperator A b f x +
        2 * ∑ i, ∑ j, A x i j * fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ g x (stdOrthonormalBasis ℝ E j) := by
    classical
    have hfd :
        ∀ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun y => f y * g y) x
              (stdOrthonormalBasis ℝ E i) =
            f x * fderiv ℝ g x (stdOrthonormalBasis ℝ E i) +
              g x * fderiv ℝ f x (stdOrthonormalBasis ℝ E i) := by
      intro i
      simpa using
        (fderiv_mul_apply
          (hf.differentiable (by norm_num) x)
          (hg.differentiable (by norm_num) x)
          (stdOrthonormalBasis ℝ E i))
    have hb :
        ∀ i j : Fin (Module.finrank ℝ E),
          bilinearIteratedFDerivTwo ℝ (fun y => f y * g y) x
              (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) =
            f x * bilinearIteratedFDerivTwo ℝ g x
                (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) +
              g x * bilinearIteratedFDerivTwo ℝ f x
                (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) +
              fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
                fderiv ℝ g x (stdOrthonormalBasis ℝ E j) +
              fderiv ℝ g x (stdOrthonormalBasis ℝ E i) *
                fderiv ℝ f x (stdOrthonormalBasis ℝ E j) := by
      intro i j
      exact bilinearIteratedFDerivTwo_mul hf hg x
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)
    have hfg :=
      nondivergenceOperator_mul_factor_double A x (f x)
        (fun i j =>
          bilinearIteratedFDerivTwo ℝ g x
            (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j))
    have hgf :=
      nondivergenceOperator_mul_factor_double A x (g x)
        (fun i j =>
          bilinearIteratedFDerivTwo ℝ f x
            (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j))
    have hbf :=
      nondivergenceOperator_mul_factor_single b x (f x)
        (fun i => fderiv ℝ g x (stdOrthonormalBasis ℝ E i))
    have hbg :=
      nondivergenceOperator_mul_factor_single b x (g x)
        (fun i => fderiv ℝ f x (stdOrthonormalBasis ℝ E i))
    have hmix :=
      nondivergenceOperator_mul_mixed_sum A hA x f g
    have hcanon :
        (∑ i, ∑ j, A x i j *
            fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
            fderiv ℝ g x (stdOrthonormalBasis ℝ E j)) =
          ∑ i, ∑ j, A x i j *
            (fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
              fderiv ℝ g x (stdOrthonormalBasis ℝ E j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    unfold nondivergenceOperator
    simp_rw [hb, hfd]
    simp only [Finset.sum_add_distrib, mul_add]
    rw [hfg, hgf, hbf, hbg, hcanon, hmix]
    ring

end ProductExpansion

end StdBasis

end DifferentialTools

section CompactSupport

/-- A `C^∞` function with compact support has a bounded second derivative. -/
theorem exists_bound_fderiv_fderiv_of_hasCompactSupport {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
    have hd1 : ContDiff ℝ 1 (fderiv ℝ g) :=
      hg.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
    have hcont : Continuous (fderiv ℝ (fderiv ℝ g)) :=
      hd1.continuous_fderiv one_ne_zero
    have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) :=
      (hc.fderiv ℝ).fderiv ℝ
    let D := fderiv ℝ (fderiv ℝ g)
    have hD : Continuous D := by
      simpa [D] using hcont
    have hsD : HasCompactSupport D := by
      simpa [D] using hs2
    obtain ⟨M, hM⟩ :=
      (hsD.isCompact).exists_bound_of_continuousOn
        (f := D) (s := tsupport D)
        (hD.continuousOn (s := tsupport D))
    refine ⟨max M 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport D
    · exact (hM x hx).trans (le_max_left _ _)
    · have hx0 : D x = 0 := image_eq_zero_of_notMem_tsupport hx
      change ‖D x‖ ≤ max M 0
      calc
        ‖D x‖ = 0 := by rw [hx0]; exact ContinuousLinearMap.opNorm_zero
        _ ≤ max M 0 := le_max_right _ _

end CompactSupport

end FunctionalInequalities.Analysis.BakryEmery

/-! ### Gradient of an affine precomposition

The gradient of `f (S x + z)` is `S† ∇f (S x + z)` for a continuous linear `S` between real inner
product spaces. -/

section
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

theorem gradient_comp_affine {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (S : E →L[ℝ] F) (z : F) {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (S x + z)) :
    gradient (fun y => f (S y + z)) x = S.adjoint (gradient f (S x + z)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]
  exact congrArg (fun T : E →L[ℝ] ℝ => T v)
    (hf.hasFDerivAt.comp x (S.hasFDerivAt.add_const z)).fderiv

end FunctionalInequalities.Analysis.BakryEmery

end
