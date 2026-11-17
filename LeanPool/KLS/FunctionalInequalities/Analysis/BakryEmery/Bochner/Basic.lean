/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Gamma
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Convex Hessians and the local Bochner identity

For
the diffusion generator `ℒ f = Δ f - ⟪∇U, ∇f⟫` on a finite-dimensional real inner product space
`E`, with `Γ` and `Γ₂` as defined in `Analysis/BakryEmery/Gamma.lean`.

* convex Hessian positivity (`bilinearIteratedFDerivTwo_nonneg_of_convexOn`): a `C²` convex function
  has a positive
  semidefinite Hessian, `0 ≤ D²U(x)(v, v)`. The proof restricts `U` to the line `t ↦ U (x + t v)`,
  whose convexity makes its derivative monotone (`ConvexOn.monotoneOn_deriv`) and hence its second
  derivative at `0` nonnegative (`Monotone.deriv_nonneg`); that second derivative is `D²U(x)(v, v)`.
* the Bochner identity (`gammaTwo_eq_hessianSqStdBasis_add`, `bochner_stdBasis`): for `C³` `f` and
  `C²` `U`,

  `Γ₂(f) = ℒ(‖∇f‖²)/2 - ⟪∇f, ∇(ℒf)⟫ = ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)`,

  where `eᵢ` is the **fixed** standard orthonormal basis `stdOrthonormalBasis ℝ E`. The double sum
  is the square of the Hessian in that basis (`hessianSqStdBasis`); its independence of the basis
  is not proved here, so no invariant Hilbert–Schmidt notation is introduced. The third-order
  derivatives `∑ⱼ ∂ⱼf ∑ᵢ ∂ᵢ∂ᵢ∂ⱼf` produced by `Δ‖∇f‖²/2` and by `⟪∇f, ∇Δf⟫` cancel exactly, after
  the commutation `∂ⱼ∂ᵢ∂ᵢ f = ∂ᵢ∂ᵢ∂ⱼ f` (`fderiv_fderiv_fderiv_apply_comm`); the drift
  contributions `-⟪∇U, ∇‖∇f‖²⟫/2` and `+⟪∇f, ∇⟪∇U, ∇f⟫⟫` leave exactly `+D²U(∇f, ∇f)` after the
  symmetry `∂ᵢ∂ⱼf = ∂ⱼ∂ᵢf`.
* Γ₂ nonnegativity (`gammaTwo_nonneg`, `bochner_nonneg_stdBasis`): for convex `U`, `0 ≤ Γ₂(f)`, as a
  sum of
  squares plus a value of the positive semidefinite Hessian of `U`.

* Improved Bochner (`norm_gradient_norm_gradient_sq_le`): for convex `U` and `C³` `f`,
  `‖∇‖∇f‖²‖² ≤ 4 ‖∇f‖² Γ₂(f)`, by Cauchy–Schwarz in the standard basis. Its consequence
  `weightedLaplacian_sqrt_sub_div_nonneg` is the pointwise `L¹` self-improvement inequality
  `0 ≤ ℒ(√(ε + Γ(f)) - √ε) - Γ(f, ℒf)/√(ε + Γ(f))` for `ε > 0`, via the chain rule
  `weightedLaplacian_comp`.

The identity holds in every finite dimension, including dimension zero, where both double sums are
empty.

## What this is not

Pointwise identities for classical smooth functions. Nothing is said about the heat semigroup
`P_t`, about `Γ(P_t f) ≤ P_t Γ(f)` or any gradient estimate, about non-smooth or lower-dimensional
log-concave laws, or about Buser's inequality.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### convex Hessian positivity: convexity gives a positive semidefinite Hessian -/

section ConvexHessian

/-- The restriction of a convex function to a line is convex. -/
theorem convexOn_line {U : E → ℝ} (hU : ConvexOn ℝ Set.univ U) (x v : E) :
    ConvexOn ℝ Set.univ (fun t : ℝ => U (x + t • v)) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  have h := hU.2 (Set.mem_univ (x + s • v)) (Set.mem_univ (x + t • v)) ha hb hab
  have hpt : x + (a • s + b • t) • v = a • (x + s • v) + b • (x + t • v) := by
    have hx : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hx]
    simp only [smul_add, smul_smul, add_smul, smul_eq_mul]
    abel
  simp only [smul_eq_mul] at hpt ⊢
  rw [hpt]
  exact h

/-- The derivative of a `C¹` function along a line is the directional derivative. -/
theorem deriv_line {U : E → ℝ} (hU : ContDiff ℝ 1 U) (x v : E) :
    deriv (fun t : ℝ => U (x + t • v)) = fun t => fderiv ℝ U (x + t • v) v :=
  funext fun t =>
    ((hU.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line x v t)).deriv

/-- The second derivative at `0` of a `C²` function along the line `t ↦ x + t v` is the Hessian
`D²U(x)(v, v)`. -/
theorem deriv_deriv_line {U : E → ℝ} (hU : ContDiff ℝ 2 U) (x v : E) :
    deriv (deriv (fun t : ℝ => U (x + t • v))) 0 = bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [deriv_line (hU.of_le (by norm_num)) x v]
  have hU1 : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (m := 1) (by norm_num)
  have hx0 : x + (0 : ℝ) • v = x := by simp
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ U (x + t • v)) (fderiv ℝ (fderiv ℝ U) x v) 0 := by
    have hd : HasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U) x) (x + (0 : ℝ) • v) := by
      rw [hx0]
      exact (hU1.differentiable one_ne_zero x).hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line x v 0)
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have h4 : deriv (fun t : ℝ => fderiv ℝ U (x + t • v) v) 0 = fderiv ℝ (fderiv ℝ U) x v v := by
    simpa using h3.deriv
  rw [h4]
  rfl

/-- **convex Hessian positivity**: the Hessian of a `C²` convex function is positive semidefinite,
`0 ≤ D²U(x)(v, v)` for all `x v`. -/
theorem bilinearIteratedFDerivTwo_nonneg_of_convexOn {U : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) (x v : E) :
    0 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [← deriv_deriv_line hU x v]
  have hφ : ∀ t : ℝ, DifferentiableAt ℝ (fun t : ℝ => U (x + t • v)) t := fun t =>
    ((hU.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_line x v t)).differentiableAt
  have hmono : Monotone (deriv (fun t : ℝ => U (x + t • v))) :=
    monotoneOn_univ.mp (ConvexOn.monotoneOn_deriv (convexOn_line hconv x v) fun t _ => hφ t)
  exact hmono.deriv_nonneg

end ConvexHessian

/-! ### The Hessian square in the standard orthonormal basis -/

section HessianSq

variable [FiniteDimensional ℝ E]

/-- The sum of the squared Hessian entries in the **fixed** standard orthonormal basis,
`∑ᵢ ∑ⱼ (D²f(x)(eᵢ, eⱼ))²`. Basis independence is not proved here; this is not yet an invariant
Hilbert–Schmidt norm. -/
def hessianSqStdBasis (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j,
    (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2

theorem hessianSqStdBasis_apply (f : E → ℝ) (x : E) :
    hessianSqStdBasis f x =
      ∑ i,
        ∑ j,
          (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
              (stdOrthonormalBasis ℝ E j)) ^
            2 :=
  rfl

theorem hessianSqStdBasis_nonneg (f : E → ℝ) (x : E) : 0 ≤ hessianSqStdBasis f x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

end HessianSq

/-! ### Finite-sum bookkeeping -/

section Sums

variable {ι : Type*} [Fintype ι]

theorem sum_two_mul_sum_add (p : ι → ι → ℝ) (a : ι → ℝ) (c : ι → ι → ℝ) :
    ∑ i, 2 * ∑ j, (p i j + a j * c i j) =
      2 * ∑ i, ∑ j, p i j + 2 * ∑ j, a j * ∑ i, c i j := by
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

theorem sum_mul_sum_add_swap (a u : ι → ℝ) (b w : ι → ι → ℝ) :
    ∑ j, a j * ∑ i, (u i * b i j + a i * w j i) =
      ∑ i, ∑ j, a i * a j * w i j + ∑ i, ∑ j, u i * a j * b i j := by
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Sums

/-! ### The four terms of `Γ₂` in the standard orthonormal basis -/

section Terms

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- `‖∇f‖²` as a sum of products of directional derivatives. -/
theorem norm_gradient_sq_fun (f : E → ℝ) :
    (fun y => ‖gradient f y‖ ^ 2) = fun y =>
      ∑ j, fderiv ℝ f y (stdOrthonormalBasis ℝ E j) * fderiv ℝ f y (stdOrthonormalBasis ℝ E j) :=
  funext fun y => by rw [norm_gradient_sq_eq_sum]; simp only [sq]

/-- The directional derivative of `‖∇f‖²`: `∂ᵥ‖∇f‖² = 2 ∑ⱼ ∂ⱼf ∂ᵥ∂ⱼf`. -/
theorem fderiv_norm_gradient_sq_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    fderiv ℝ (fun y => ‖gradient f y‖ ^ 2) x v =
      2 * ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        fderiv ℝ (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ E j)) x v := by
  rw [norm_gradient_sq_fun]
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), DifferentiableAt ℝ
      (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ E j) * fderiv ℝ f y (stdOrthonormalBasis ℝ E j))
      x := fun j _ => (differentiable_fderiv_apply hf _ x).mul (differentiable_fderiv_apply hf _ x)
  rw [fderiv_sum_apply _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_mul_apply (differentiable_fderiv_apply hf _ x) (differentiable_fderiv_apply hf _ x)]
  ring

/-- Drift term: `⟪∇U, ∇‖∇f‖²⟫ = 2 ∑ᵢ ∑ⱼ ∂ᵢU ∂ⱼf D²f(eᵢ, eⱼ)`. -/
theorem inner_gradient_gradient_norm_sq (U : E → ℝ) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    ⟪gradient U x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫ =
      2 *
        ∑ i,
          ∑ j,
            fderiv ℝ U x (stdOrthonormalBasis ℝ E i) *
                fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
              bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
                (stdOrthonormalBasis ℝ E j) := by
  rw [inner_gradient_eq_sum_fderiv_mul_fderiv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_norm_gradient_sq_apply hf, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
  ring

/-- Laplacian of `‖∇f‖²`: `Δ‖∇f‖² = 2 ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + 2 ∑ⱼ ∂ⱼf ∑ᵢ ∂ᵢ∂ᵢ∂ⱼf`. -/
theorem laplacian_norm_gradient_sq {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x =
      2 *
          ∑ i,
            ∑ j,
              (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
                  (stdOrthonormalBasis ℝ E j)) ^
                2 +
        2 *
          ∑ j,
            fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
              ∑ i,
                fderiv ℝ
                  (fun y =>
                    fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
                      (stdOrthonormalBasis ℝ E i))
                  x (stdOrthonormalBasis ℝ E i) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hg2 : ContDiff ℝ 2 (gradient f) := contDiff_gradient hf (by norm_num)
  have hN : ContDiff ℝ 2 (fun y => ‖gradient f y‖ ^ 2) := hg2.norm_sq (𝕜 := ℝ)
  rw [laplacian_eq_sum_fderiv_apply_fderiv_apply
      ((hN.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    ← sum_two_mul_sum_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 :
    (fun y => fderiv ℝ (fun z => ‖gradient f z‖ ^ 2) y (stdOrthonormalBasis ℝ E i)) = fun y =>
      2 *
        ∑ j,
          fderiv ℝ f y (stdOrthonormalBasis ℝ E j) *
            fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
              (stdOrthonormalBasis ℝ E i) :=
    funext fun y => fderiv_norm_gradient_sq_apply hf2 y _
  have hd :
    ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      DifferentiableAt ℝ
        (fun y =>
          fderiv ℝ f y (stdOrthonormalBasis ℝ E j) *
            fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
              (stdOrthonormalBasis ℝ E i))
        x :=
    fun j _ =>
    (differentiable_fderiv_apply hf2 _ x).mul
      ((contDiff_fderiv_apply (contDiff_fderiv_apply hf (m := 2) (by norm_num) _) (m := 1)
            (by norm_num) _).differentiable
        one_ne_zero x)
  have hs :
    DifferentiableAt ℝ
      (fun y =>
        ∑ j,
          fderiv ℝ f y (stdOrthonormalBasis ℝ E j) *
            fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
              (stdOrthonormalBasis ℝ E i))
      x :=
    DifferentiableAt.fun_sum hd
  rw [h1, fderiv_const_mul_apply hs, fderiv_sum_apply _ hd]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_mul_apply (differentiable_fderiv_apply hf2 _ x)
      ((contDiff_fderiv_apply (contDiff_fderiv_apply hf (m := 2) (by norm_num) _) (m := 1)
            (by norm_num) _).differentiable
        one_ne_zero x),
    bilinearIteratedFDerivTwo_eq_fderiv_apply hf2]
  ring

/-- Third-order term: `⟪∇f, ∇(Δf)⟫ = ∑ⱼ ∂ⱼf ∑ᵢ ∂ᵢ∂ᵢ∂ⱼf`, after commuting `∂ⱼ∂ᵢ∂ᵢ f = ∂ᵢ∂ᵢ∂ⱼ f`. -/
theorem inner_gradient_gradient_laplacian {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    ⟪gradient f x, gradient (Laplacian.laplacian f) x⟫ =
      ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
          (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  rw [inner_gradient_eq_sum_fderiv_mul_fderiv, laplacian_eq_fun_sum hf2]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E i)) y
        (stdOrthonormalBasis ℝ E i)) x := fun i _ =>
    (contDiff_fderiv_apply (contDiff_fderiv_apply hf (m := 2) (by norm_num) _) (m := 1)
      (by norm_num) _).differentiable one_ne_zero x
  rw [fderiv_sum_apply _ hd]
  exact Finset.sum_congr rfl fun i _ => fderiv_fderiv_fderiv_apply_comm hf x _ _

/-- Drift term of `Γ(f, ℒf)`:
`⟪∇f, ∇⟪∇U, ∇f⟫⟫ = D²U(∇f, ∇f) + ∑ᵢ ∑ⱼ ∂ᵢU ∂ⱼf D²f(eᵢ, eⱼ)`, using the symmetry of `D²f`. -/
theorem inner_gradient_gradient_inner {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x : E) :
    ⟪gradient f x, gradient (fun y => ⟪gradient U y, gradient f y⟫) x⟫ =
      bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) +
        ∑ i, ∑ j, fderiv ℝ U x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j) := by
  have h0 : (fun y => ⟪gradient U y, gradient f y⟫) = fun y =>
      ∑ i, fderiv ℝ U y (stdOrthonormalBasis ℝ E i) * fderiv ℝ f y (stdOrthonormalBasis ℝ E i) :=
    funext fun y => inner_gradient_eq_sum_fderiv_mul_fderiv U f y
  rw [inner_gradient_eq_sum_fderiv_mul_fderiv, h0, bilinearIteratedFDerivTwo_gradient_gradient,
    ← sum_mul_sum_add_swap]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), DifferentiableAt ℝ
      (fun y => fderiv ℝ U y (stdOrthonormalBasis ℝ E i) * fderiv ℝ f y (stdOrthonormalBasis ℝ E i))
      x := fun i _ => (differentiable_fderiv_apply hU _ x).mul (differentiable_fderiv_apply hf _ x)
  rw [fderiv_sum_apply _ hd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_mul_apply (differentiable_fderiv_apply hU _ x) (differentiable_fderiv_apply hf _ x),
    ← bilinearIteratedFDerivTwo_eq_fderiv_apply hf, ← bilinearIteratedFDerivTwo_eq_fderiv_apply hU,
    bilinearIteratedFDerivTwo_symm hf x]

end Terms

/-! ### the Bochner identity and Γ₂ nonnegativity -/

section Bochner

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/--
**the Bochner identity, the Bochner identity in the standard orthonormal basis**: for `C²` `U` and
`C³`
`f`, `Γ₂(f) = ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)`. -/
theorem gammaTwo_eq_hessianSqStdBasis_add {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (x : E) :
    gammaTwo U f x =
      hessianSqStdBasis f x + bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hΔ : DifferentiableAt ℝ (Laplacian.laplacian f) x :=
    (contDiff_laplacian hf (m := 1) (by norm_num)).differentiable one_ne_zero x
  have hgU : ContDiff ℝ 1 (gradient U) := contDiff_gradient hU (by norm_num)
  have hgf : ContDiff ℝ 1 (gradient f) := contDiff_gradient hf (by norm_num)
  have hI : DifferentiableAt ℝ (fun y => ⟪gradient U y, gradient f y⟫) x :=
    (hgU.inner ℝ hgf).differentiable one_ne_zero x
  rw [gammaTwo_eq_expanded, gradient_sub hΔ hI, inner_sub_right, laplacian_norm_gradient_sq hf,
    inner_gradient_gradient_norm_sq U hf2, inner_gradient_gradient_laplacian hf,
    inner_gradient_gradient_inner hU hf2, hessianSqStdBasis_apply]
  ring

/-- **the Bochner identity in expanded form**: for `C³` `U` and `f`,
`(Δ‖∇f‖² - ⟪∇U, ∇‖∇f‖²⟫)/2 - ⟪∇f, ∇(Δf - ⟪∇U, ∇f⟫)⟫ = ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)`. -/
theorem bochner_stdBasis {U f : E → ℝ} (hU : ContDiff ℝ 3 U) (hf : ContDiff ℝ 3 f) (x : E) :
    (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
        ⟪gradient U x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫) / 2 -
      ⟪gradient f x,
        gradient (fun y => Laplacian.laplacian f y - ⟪gradient U y, gradient f y⟫) x⟫ =
    (∑ i, ∑ j,
        (bilinearIteratedFDerivTwo ℝ f x
          (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2) +
      bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) := by
  rw [← gammaTwo_eq_expanded, gammaTwo_eq_hessianSqStdBasis_add (hU.of_le (by norm_num)) hf,
    hessianSqStdBasis_apply]

/-- **Γ₂ nonnegativity**: for a `C²` convex potential and a `C³` function, `0 ≤ Γ₂(f)`. -/
theorem gammaTwo_nonneg {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hconv : ConvexOn ℝ Set.univ U)
    (hf : ContDiff ℝ 3 f) (x : E) : 0 ≤ gammaTwo U f x := by
  rw [gammaTwo_eq_hessianSqStdBasis_add hU hf]
  exact add_nonneg (hessianSqStdBasis_nonneg f x)
    (bilinearIteratedFDerivTwo_nonneg_of_convexOn hU hconv x _)

/-- **Γ₂ nonnegativity in expanded form**: for a `C³` convex potential and a `C³` function,
`0 ≤ (Δ‖∇f‖² - ⟪∇U, ∇‖∇f‖²⟫)/2 - ⟪∇f, ∇(Δf - ⟪∇U, ∇f⟫)⟫`. -/
theorem bochner_nonneg_stdBasis {U f : E → ℝ} (hU : ContDiff ℝ 3 U)
    (hconv : ConvexOn ℝ Set.univ U) (hf : ContDiff ℝ 3 f) (x : E) :
    0 ≤ (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
          ⟪gradient U x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫) / 2 -
        ⟪gradient f x,
          gradient (fun y => Laplacian.laplacian f y - ⟪gradient U y, gradient f y⟫) x⟫ := by
  rw [← gammaTwo_eq_expanded]
  exact gammaTwo_nonneg (hU.of_le (by norm_num)) hconv hf x

/--
**The improved Bochner inequality** `|∇Γ(f)|² ≤ 4 Γ(f) Γ₂(f)` for a `C²` convex potential and
a `C³` function, with `Γ(f) = ‖∇f‖²`. Since `∂ᵢ‖∇f‖² = 2 ∑ⱼ ∂ⱼf D²f(eᵢ, eⱼ)`, Cauchy–Schwarz in
`j` gives `‖∇Γ(f)‖² ≤ 4 ‖∇f‖² ∑ᵢⱼ (D²f(eᵢ, eⱼ))²`, and the potential term of `Γ₂` is
nonnegative by convexity. This is the Kato-type input of Bakry's `L¹` self-improvement. -/
theorem norm_gradient_norm_gradient_sq_le {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) (hf : ContDiff ℝ 3 f) (x : E) :
    ‖gradient (fun y => ‖gradient f y‖ ^ 2) x‖ ^ 2 ≤ 4 * ‖gradient f x‖ ^ 2 * gammaTwo U f x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hpart :
    ∀ i,
      fderiv ℝ (fun y => ‖gradient f y‖ ^ 2) x (stdOrthonormalBasis ℝ E i) =
        2 *
          ∑ j,
            fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
              bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
                (stdOrthonormalBasis ℝ E j) := by
    intro i
    rw [fderiv_norm_gradient_sq_apply hf2]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hf2]
  have hU0 := bilinearIteratedFDerivTwo_nonneg_of_convexOn hU hconv x (gradient f x)
  rw [norm_gradient_sq_eq_sum (fun y => ‖gradient f y‖ ^ 2),
    gammaTwo_eq_hessianSqStdBasis_add hU hf x, norm_gradient_sq_eq_sum f x,
    hessianSqStdBasis_apply]
  simp_rw [hpart]
  have hcs :
    ∀ i,
      (∑ j,
            fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
              bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
                (stdOrthonormalBasis ℝ E j)) ^
          2 ≤
        (∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) ^ 2) *
          ∑ j,
            bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
                (stdOrthonormalBasis ℝ E j) ^
              2 :=
    fun i => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum :=
    Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) => hcs i
  rw [← Finset.mul_sum] at hsum
  have hA : 0 ≤ ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlhs :
    ∑ i,
        (2 *
            ∑ j,
              fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
                bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
                  (stdOrthonormalBasis ℝ E j)) ^
          2 =
      4 *
        ∑ i,
          (∑ j,
              fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
                bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
                  (stdOrthonormalBasis ℝ E j)) ^
            2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [hlhs]
  nlinarith [mul_nonneg hA hU0]

/-- **The pointwise `L¹` self-improvement inequality.** For `ε > 0`, a `C²` convex potential and a
`C³` function `f`, `0 ≤ ℒ(√(ε + Γ(f)) - √ε) - Γ(f, ℒf) / √(ε + Γ(f))`. With `r = √(ε + Γ(f))`
the left side is `Γ₂(f)/r - |∇Γ(f)|²/(4 r³) ≥ ε Γ₂(f)/r³`, by
`norm_gradient_norm_gradient_sq_le`. The constant `√ε` makes the function vanish where
`∇f = 0`, so it is compactly supported for compactly supported `f`. -/
theorem weightedLaplacian_sqrt_sub_div_nonneg {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) (hf : ContDiff ℝ 3 f) {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 ≤ weightedLaplacian U (fun y => √(ε + gamma f f y) - √ε) x -
      gamma f (weightedLaplacian U f) x / √(ε + gamma f f x) := by
  have hG : ContDiff ℝ 2 (gamma f f) := contDiff_gamma hf hf (by norm_num) (by norm_num)
  have hpos : ∀ s, 0 ≤ s → 0 < ε + s := fun s hs => by linarith
  have hGnn : ∀ y, 0 ≤ gamma f f y := fun y => by rw [gamma_self]; positivity
  set h' : ℝ → ℝ := fun s => (2 * √(ε + s))⁻¹ with hh'def
  set h'' : ℝ → ℝ := fun s => -(1 / (4 * (ε + s) * √(ε + s))) with hh''def
  have hh : ∀ y, HasDerivAt (fun s => √(ε + s) - √ε) (h' (gamma f f y)) (gamma f f y) := by
    intro y
    have h1 := (((hasDerivAt_id (gamma f f y)).const_add ε).sqrt (hpos _ (hGnn y)).ne').sub_const
      (√ε)
    simpa [hh'def, div_eq_inv_mul] using h1
  have hh' : HasDerivAt h' (h'' (gamma f f x)) (gamma f f x) := by
    have hp := hpos _ (hGnn x)
    have hs : 0 < √(ε + gamma f f x) := Real.sqrt_pos.mpr hp
    have h1 := (((hasDerivAt_id' (gamma f f x)).const_add ε).sqrt hp.ne').const_mul 2
    have h2 := HasDerivAt.inv h1 (by positivity)
    refine h2.congr_deriv ?_
    simp only [hh''def]
    rw [mul_pow, Real.sq_sqrt hp.le]
    field_simp
    norm_num
  rw [weightedLaplacian_comp U hG hh hh']
  have hsq := norm_gradient_norm_gradient_sq_le hU hconv hf x
  have hΓ2 := gammaTwo_nonneg hU hconv hf x
  rw [gammaTwo_apply] at hΓ2 hsq
  have hfun : (fun y => gamma f f y) = fun y => ‖gradient f y‖ ^ 2 := gamma_self_fun f
  rw [← hfun, ← gamma_self f x] at hsq
  rw [← gamma_self] at hsq
  set G := gamma f f x with hGdef
  set L := weightedLaplacian U (fun y => gamma f f y) x
  set M := gamma f (weightedLaplacian U f) x
  set N := gamma (fun y => gamma f f y) (fun y => gamma f f y) x
  have hp := hpos _ (hGnn x)
  set r := √(ε + G) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hp
  have hr2 : r ^ 2 = ε + G := Real.sq_sqrt hp.le
  simp only [hh'def, hh''def]
  rw [← hrdef]
  have hN : N ≤ 4 * G * (L / 2 - M) := hsq
  have key : 0 ≤ (2 * r ^ 2 * (L / 2 - M) - N / 2) / (2 * r ^ 3) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  have hexpr : (2 * r)⁻¹ * L + -(1 / (4 * (ε + G) * r)) * N - M / r =
      (2 * r ^ 2 * (L / 2 - M) - N / 2) / (2 * r ^ 3) := by
    rw [← hr2]; field_simp; ring
  rw [hexpr]
  exact key

end Bochner

/-! ### Boundary cases -/

section Boundary

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- With the zero potential, `Γ₂` is the Euclidean Bochner quantity `Δ‖∇f‖²/2 - ⟪∇f, ∇Δf⟫` and
equals the Hessian square. -/
theorem gammaTwo_zero_potential {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    gammaTwo (fun _ => (0 : ℝ)) f x = hessianSqStdBasis f x := by
  rw [gammaTwo_eq_hessianSqStdBasis_add contDiff_const hf]
  have :
    bilinearIteratedFDerivTwo ℝ (fun _ : E => (0 : ℝ)) x (gradient f x) (gradient f x) = 0 := by
    change fderiv ℝ (fderiv ℝ fun _ : E => (0 : ℝ)) x (gradient f x) (gradient f x) = 0
    simp [fderiv_fun_const]
  rw [this, add_zero]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The Hessian of an affine function vanishes. -/
theorem bilinearIteratedFDerivTwo_affine (L : E →L[ℝ] ℝ) (c : ℝ) (x v w : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => L y + c) x v w = 0 := by
  change fderiv ℝ (fderiv ℝ fun y => L y + c) x v w = 0
  have : (fderiv ℝ fun y => L y + c) = fun _ => L :=
    funext fun y => (L.hasFDerivAt.add_const c).fderiv
  rw [this, fderiv_fun_const]
  simp

omit [CompleteSpace E] in
/-- For an affine `f`, the Hessian square vanishes. -/
theorem hessianSqStdBasis_affine (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    hessianSqStdBasis (fun y => L y + c) x = 0 := by
  simp [hessianSqStdBasis_apply, bilinearIteratedFDerivTwo_affine]

/-- For an affine `f`, `Γ₂(f) = D²U(∇f, ∇f)`: the second derivative of the potential along the
constant gradient. -/
theorem gammaTwo_affine {U : E → ℝ} (hU : ContDiff ℝ 2 U) (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    gammaTwo U (fun y => L y + c) x =
      bilinearIteratedFDerivTwo ℝ U x (gradient (fun y => L y + c) x)
        (gradient (fun y => L y + c) x) := by
  rw [gammaTwo_eq_hessianSqStdBasis_add hU (L.contDiff.add contDiff_const),
    hessianSqStdBasis_affine, zero_add]

/-- In a zero-dimensional space, `Γ₂` vanishes for every `U` and `f`, with no regularity
hypothesis. -/
theorem gammaTwo_of_subsingleton [Subsingleton E] (U f : E → ℝ) (x : E) : gammaTwo U f x = 0 := by
  have hU : ContDiff ℝ 2 U := by
    have : U = fun _ => U x := funext fun y => by rw [Subsingleton.elim y x]
    rw [this]
    exact contDiff_const
  have hf : ContDiff ℝ 3 f := by
    have : f = fun _ => f x := funext fun y => by rw [Subsingleton.elim y x]
    rw [this]
    exact contDiff_const
  rw [gammaTwo_eq_hessianSqStdBasis_add hU hf, Subsingleton.elim (gradient f x) 0, map_zero,
    add_zero, hessianSqStdBasis_apply]
  exact Finset.sum_eq_zero fun i _ => by
    have h1 := i.isLt
    have h0 : Module.finrank ℝ E = 0 := Module.finrank_zero_of_subsingleton
    omega

end Boundary

end FunctionalInequalities.Analysis.BakryEmery
