/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.ConvexInteraction
public import LeanPool.CutoffRigidity.Eigenmap
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Affine chain rules for the projected Langevin generator

The proof of Lemma `lem_proj_ou` in `cutcur-lean.tex` applies the diffusion
chain rule to an affine normalized eigenmap. Here the derivative and Hessian
chain rules are proved for actual continuous linear maps and actual Fréchet
derivatives, and then traced to compute the Euclidean Laplacian.

These are pointwise differential calculations. They do not establish that a
projected stochastic process is Markov or identify its law: those steps also
require construction of the diffusion and uniqueness for its SDE or martingale
problem.
-/

public section

namespace CutoffRigidity

/-- The actual continuous linear map associated with the normalized
eigenmap rows already used in `Eigenmap.lean`. -/
@[expose] noncomputable def eigenmapCLM {d k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin d)) (rate : ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearMap.toContinuousLinearMap
    { toFun := eigenmapLinear v rate
      map_add' := by
        intro x y
        ext i
        simp only [eigenmapLinear]
        change Real.sqrt rate * inner ℝ (v i) (x + y) =
          Real.sqrt rate * inner ℝ (v i) x + Real.sqrt rate * inner ℝ (v i) y
        rw [inner_add_right, mul_add]
      map_smul' := by
        intro r x
        ext i
        simp only [eigenmapLinear]
        change Real.sqrt rate * inner ℝ (v i) (r • x) =
          r * (Real.sqrt rate * inner ℝ (v i) x)
        rw [inner_smul_right]
        ring }

theorem eigenmapCLM_apply {d k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin d)) (rate : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    eigenmapCLM v rate x = eigenmapLinear v rate x := rfl

/-- The scaled orthonormal rows have Gram matrix `rate * I`, as required
by the covariance and Laplacian computations in Lemma `lem_proj_ou`. -/
theorem eigenmapCLM_row_identity {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) (i l : Fin k) :
    (∑ j : Fin d, eigenmapCLM v rate (EuclideanSpace.single j 1) i *
      eigenmapCLM v rate (EuclideanSpace.single j 1) l) =
        if i = l then rate else 0 := by
  simp only [eigenmapCLM_apply, eigenmapLinear]
  change (∑ j : Fin d,
    (Real.sqrt rate * inner ℝ (v i) (EuclideanSpace.single j 1)) *
      (Real.sqrt rate * inner ℝ (v l) (EuclideanSpace.single j 1))) = _
  simp only [EuclideanSpace.inner_single_right, one_mul]
  calc
    _ = rate * ∑ j : Fin d, v i j * v l j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [RCLike.conj_to_real]
      calc
        _ = (Real.sqrt rate) ^ 2 * (v i j * v l j) := by ring
        _ = _ := by rw [Real.sq_sqrt hr]
    _ = rate * inner ℝ (v i) (v l) := by
      rw [PiLp.inner_apply]
      simp only [Real.inner_apply]
    _ = _ := by
      rw [orthonormal_iff_ite.mp hv i l]
      split_ifs <;> simp_all

/-- Coordinate expansion of a continuous bilinear form, used for its trace. -/
theorem bilinear_euclidean_coordinate_expansion {k : ℕ}
    (H : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (u v : EuclideanSpace ℝ (Fin k)) :
    H u v = ∑ i : Fin k, ∑ l : Fin k,
      u i * v l * H (EuclideanSpace.single i 1) (EuclideanSpace.single l 1) := by
  have hrepr (y : EuclideanSpace ℝ (Fin k)) :
      y = ∑ i : Fin k, y i • EuclideanSpace.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hrepr u, hrepr v]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Scaled orthonormal rows contract any bilinear Hessian trace by the
square of the row scale. The row identity is stated on the actual matrix
coefficients of the continuous linear map. -/
theorem bilinear_trace_comp_of_row_identity {d k : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (H : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (rate : ℝ)
    (hrows : ∀ i l : Fin k,
      (∑ j : Fin d, A (EuclideanSpace.single j 1) i * A (EuclideanSpace.single j 1) l) =
        if i = l then rate else 0) :
    (∑ j : Fin d, H (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single j 1))) =
      rate * ∑ i : Fin k, H (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  calc
    _ = ∑ i : Fin k, ∑ l : Fin k,
        (∑ j : Fin d, A (EuclideanSpace.single j 1) i * A (EuclideanSpace.single j 1) l) *
          H (EuclideanSpace.single i 1) (EuclideanSpace.single l 1) := by
      have hexp := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin d))) rfl
        (fun j _ => bilinear_euclidean_coordinate_expansion H
          (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single j 1)))
      rw [hexp, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
    _ = _ := by simp [hrows, Finset.mul_sum]

/-- First derivative of a function pulled back by an affine map. -/
theorem fderiv_comp_affine_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (b : F) {g : F → ℝ} {x v : E}
    (hg : DifferentiableAt ℝ g (A x + b)) :
    fderiv ℝ (fun y => g (A y + b)) x v = fderiv ℝ g (A x + b) (A v) := by
  have hA : DifferentiableAt ℝ (fun y => A y + b) x := A.differentiableAt.add_const b
  rw [fderiv_fun_comp x hg hA, fderiv_add_const, A.fderiv]
  rfl

/-- The affine map has no second derivative, so the second chain rule
contains only the Hessian of the outer function evaluated on the linear images
of the two directions. -/
theorem second_fderiv_comp_affine_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (b : F) {g : F → ℝ}
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (fderiv ℝ g))
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => g (A z + b)) y v) x w =
      fderiv ℝ (fderiv ℝ g) (A x + b) (A w) (A v) := by
  have hfirst : (fun y => fderiv ℝ (fun z => g (A z + b)) y v) =
      fun y => fderiv ℝ g (A y + b) (A v) := by
    funext y
    exact fderiv_comp_affine_apply A b (hg (A y + b))
  rw [hfirst]
  have hA : DifferentiableAt ℝ (fun y => A y + b) x := A.differentiableAt.add_const b
  have hcomp : DifferentiableAt ℝ (fun y => fderiv ℝ g (A y + b)) x :=
    (hg' (A x + b)).comp x hA
  rw [fderiv_clm_apply hcomp (differentiableAt_const (A v)),
    fderiv_const_apply, fderiv_fun_comp x (hg' (A x + b)) hA,
    fderiv_add_const, A.fderiv]
  simp

/-- Differentiating a first derivative in a fixed direction is evaluation
of the genuine second Fréchet derivative in that direction. -/
theorem second_fderiv_apply_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x : E} (hg' : DifferentiableAt ℝ (fderiv ℝ g) x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
  rw [fderiv_clm_apply hg' (differentiableAt_const v), fderiv_const_apply]
  simp

theorem euclideanLaplacian_eq_second_fderiv_trace
    {k : ℕ} {g : EuclideanSpace ℝ (Fin k) → ℝ} {x : EuclideanSpace ℝ (Fin k)}
    (hg' : DifferentiableAt ℝ (fderiv ℝ g) x) :
    euclideanLaplacian g x = ∑ i : Fin k, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i _
  exact second_fderiv_apply_const hg' _ _

/-- Taking the trace of the affine Hessian chain rule gives the exact
Laplacian before the scaled orthonormal-row identities are substituted. -/
theorem euclideanLaplacian_comp_affine
    {d k : ℕ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin k)) {g : EuclideanSpace ℝ (Fin k) → ℝ}
    (hg : ContDiff ℝ 2 g) (x : EuclideanSpace ℝ (Fin d)) :
    euclideanLaplacian (fun y => g (A y + b)) x =
      ∑ j : Fin d, fderiv ℝ (fderiv ℝ g) (A x + b)
        (A (EuclideanSpace.single j 1)) (A (EuclideanSpace.single j 1)) := by
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro j _
  exact second_fderiv_comp_affine_apply A b (hg.differentiable (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
    (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)

/-- The Laplacian part of the diffusion chain rule for an affine map with
scaled orthonormal rows, exactly as used in Lemma `lem_proj_ou`. -/
theorem euclideanLaplacian_comp_affine_of_row_identity
    {d k : ℕ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin k)) {g : EuclideanSpace ℝ (Fin k) → ℝ}
    (hg : ContDiff ℝ 2 g) (rate : ℝ)
    (hrows : ∀ i l : Fin k,
      (∑ j : Fin d, A (EuclideanSpace.single j 1) i * A (EuclideanSpace.single j 1) l) =
        if i = l then rate else 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    euclideanLaplacian (fun y => g (A y + b)) x = rate * euclideanLaplacian g (A x + b) := by
  rw [euclideanLaplacian_comp_affine A b hg,
    bilinear_trace_comp_of_row_identity A _ rate hrows,
    euclideanLaplacian_eq_second_fderiv_trace
      (((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) (A x + b))]

/-- Affine scalar functions have zero Euclidean Laplacian. -/
theorem euclideanLaplacian_affine {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    euclideanLaplacian (fun y => L y + c) x = 0 := by
  simp only [euclideanLaplacian, fderiv_add_const, L.fderiv, fderiv_const_apply,
    zero_apply, Finset.sum_const_zero]

/-- On an affine scalar test function, the Langevin differential operator
is just minus the linear functional evaluated at the potential gradient. -/
theorem langevinDifferentialOperator_affine {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    langevinDifferentialOperator V (fun y => L y + c) x = -L (gradient V x) := by
  rw [langevinDifferentialOperator, euclideanLaplacian_affine,
    real_inner_comm, inner_gradient_left, fderiv_add_const, L.fderiv]
  simp

/-- The coordinate eigenfunction equations for an actual affine map force
its projected drift to be linear, as in the proof of Lemma `lem_proj_ou`. -/
theorem affine_projected_drift_of_coordinate_equations {d k : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin k)) (rate : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (heigen : ∀ i : Fin k,
      langevinDifferentialOperator V (fun y => (A y + b) i) x = -rate * (A x + b) i) :
    A (gradient V x) = rate • (A x + b) := by
  ext i
  have hi := heigen i
  have heq : (fun y => (A y + b) i) =
      fun y => ((innerSL ℝ (EuclideanSpace.single i 1)).comp A) y + b i := by
    funext y
    simp [EuclideanSpace.inner_single_left]
  rw [heq, langevinDifferentialOperator_affine] at hi
  change -inner ℝ (EuclideanSpace.single i 1) (A (gradient V x)) =
    -rate * (A x + b) i at hi
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hi
  change A (gradient V x) i = rate * (A x + b) i
  linarith

/-- The pointwise generator-intertwining identity in Lemma `lem_proj_ou`.
It combines the actual affine chain rule, scaled orthonormal-row identity,
and coordinate eigenfunction equations. Turning this into a statement about
the projected stochastic process still requires the diffusion construction
and uniqueness argument. -/
theorem langevinDifferentialOperator_comp_affine_of_coordinate_equations {d k : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin k)) (rate : ℝ)
    (hrows : ∀ i l : Fin k,
      (∑ j : Fin d, A (EuclideanSpace.single j 1) i * A (EuclideanSpace.single j 1) l) =
        if i = l then rate else 0)
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin d))
    (heigen : ∀ i : Fin k,
      langevinDifferentialOperator V (fun y => (A y + b) i) x = -rate * (A x + b) i) :
    langevinDifferentialOperator V (fun y => g (A y + b)) x =
      rate * euclideanLaplacian g (A x + b) -
        rate * inner ℝ (gradient g (A x + b)) (A x + b) := by
  have hdrift := affine_projected_drift_of_coordinate_equations V A b rate x heigen
  rw [langevinDifferentialOperator,
    euclideanLaplacian_comp_affine_of_row_identity A b hg rate hrows,
    real_inner_comm, inner_gradient_left,
    fderiv_comp_affine_apply A b ((hg.differentiable (by norm_num)) (A x + b)), hdrift]
  rw [map_smul, smul_eq_mul, inner_gradient_left]

/-- The Laplacian identity specialized to the paper's scaled orthonormal
row construction, with its row Gram identity now proved rather than supplied. -/
theorem euclideanLaplacian_comp_eigenmapAffine {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) (b : EuclideanSpace ℝ (Fin k))
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin d)) :
    euclideanLaplacian (fun y => g (eigenmapCLM v rate y + b)) x =
      rate * euclideanLaplacian g (eigenmapCLM v rate x + b) :=
  euclideanLaplacian_comp_affine_of_row_identity (eigenmapCLM v rate) b hg rate
    (eigenmapCLM_row_identity hv hr) x

/-- The full pointwise generator calculation for the paper's actual
scaled orthonormal-row eigenmap. The remaining assumption is the explicitly
stated differential equation on each coordinate; spectral rigidity and
the stochastic projection theorem are separate obligations. -/
theorem langevinDifferentialOperator_comp_eigenmapAffine {d k : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    {rate : ℝ} (hr : 0 ≤ rate) (b : EuclideanSpace ℝ (Fin k))
    {g : EuclideanSpace ℝ (Fin k) → ℝ} (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin d))
    (heigen : ∀ i : Fin k,
      langevinDifferentialOperator V (fun y => (eigenmapCLM v rate y + b) i) x =
        -rate * (eigenmapCLM v rate x + b) i) :
    langevinDifferentialOperator V (fun y => g (eigenmapCLM v rate y + b)) x =
      rate * euclideanLaplacian g (eigenmapCLM v rate x + b) -
        rate * inner ℝ (gradient g (eigenmapCLM v rate x + b))
          (eigenmapCLM v rate x + b) :=
  langevinDifferentialOperator_comp_affine_of_coordinate_equations V
    (eigenmapCLM v rate) b rate (eigenmapCLM_row_identity hv hr) hg x heigen

end CutoffRigidity
