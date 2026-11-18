/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates

/-!
# Quadratic functions and their differential calculus

Supporting interfaces for Letwin arXiv:2607.24164v1 Lemma 2.2 through
Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii). Each declaration retains
its own hypotheses and scope; this layout does not assert further regularity.
-/

@[expose] public section

noncomputable section

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/-- The quadratic function with constant `c`, slope `b` and Hessian matrix `A` centred at `x₀`:
`Q x = c + ⟪b, x − x₀⟫ + ½ ⟪x − x₀, A (x − x₀)⟫` (viscosity tests). -/
def quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  c + ⟪b, x - x₀⟫ + (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin A (x - x₀)⟫

/-- Adding a scalar identity to the quadratic Hessian adds exactly the
corresponding squared-distance term, for every real scalar. -/
theorem quadraticAt_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    quadraticAt (A + t • 1) x₀ b c x =
      quadraticAt A x₀ b c x + t / 2 * ‖x - x₀‖ ^ 2 := by
  unfold quadraticAt
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  rw [show Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) =
    LinearMap.id by exact Matrix.toLpLin_one 2]
  simp only [LinearMap.id_apply, real_inner_self_eq_norm_sq]
  ring

open scoped ContDiff in
/--
One actual polynomial proof for ALL orders, shared by the C2 interface and classical C4 consumers.
-/
theorem contDiff_quadraticAt_all {n : ℕ} {k : ℕ∞ω} (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ContDiff ℝ k (quadraticAt A x₀ b c) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  change
    ContDiff ℝ k (fun x => c + inner ℝ b (x - x₀) + (1 / 2 : ℝ) * inner ℝ (x - x₀) (T (x - x₀)))
  exact
    (contDiff_const.add (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).add
      (contDiff_const.mul
        ((contDiff_id.sub contDiff_const).inner ℝ
          (T.contDiff.comp (contDiff_id.sub contDiff_const))))

/-- `quadraticAt A x₀ b c` is smooth. -/
theorem contDiff_quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ContDiff ℝ 2 (quadraticAt A x₀ b c) := by
  exact contDiff_quadraticAt_all A x₀ b c

private lemma quadraticAt_fderiv_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (y w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (quadraticAt A x₀ b c) y w =
      ⟪b, w⟫ + (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x₀
  have ht := T.hasFDerivAt.comp y hd
  have hb := (hasFDerivAt_const (𝕜 := ℝ) b y).inner ℝ hd
  have hq := hd.inner ℝ ht
  have hh := (hb.const_add c).add (hq.const_mul (1 / 2 : ℝ))
  change HasFDerivAt (quadraticAt A x₀ b c) _ y at hh
  rw [hh.fderiv]
  simp [fderivInnerCLM_apply, T]

/-- The actual gradient of a symmetric quadratic, with arbitrary affine and
constant terms. -/
theorem gradient_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (quadraticAt A x₀ b c) x = b + Matrix.toEuclideanLin A (x - x₀) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, quadraticAt_fderiv_apply, inner_add_left]
  have hs := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (x - x₀) v
  rw [← hs, real_inner_comm v (Matrix.toEuclideanLin A (x - x₀))]
  ring

private lemma quadraticAt_second_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ w x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ
      (fun y => (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫)) x v =
      (1 / 2 : ℝ) *
        (⟪v, Matrix.toEuclideanLin A w⟫ + ⟪w, Matrix.toEuclideanLin A v⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
  have ht := T.hasFDerivAt.comp x hd
  have h₁ := hd.inner ℝ (hasFDerivAt_const (𝕜 := ℝ) (T w) x)
  have h₂ := (hasFDerivAt_const (𝕜 := ℝ) w x).inner ℝ ht
  have hh := (h₁.add h₂).const_mul (1 / 2 : ℝ)
  simpa [fderivInnerCLM_apply, T, mul_add] using
    congrArg (fun L => L v) hh.fderiv

/-- The `(i, j)` entry of a real matrix as an inner product of standard basis vectors. -/
theorem inner_basisFun_toEuclideanLin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = A i j := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, Matrix.toLpLin_apply 2 2]
  simp [Matrix.mulVec, dotProduct]

/-- The coordinate Hessian of `quadraticAt A x₀ b c` is `A` at every point when `A` is symmetric
. -/
theorem hessianMatrix_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (quadraticAt A x₀ b c) x = A := by
  ext i j
  change bilinearIteratedFDerivTwo ℝ (quadraticAt A x₀ b c) x
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) = A i j
  rw [BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
    (contDiff_quadraticAt A x₀ b c)]
  simp_rw [quadraticAt_fderiv_apply]
  rw [fderiv_const_add, quadraticAt_second_apply,
    inner_basisFun_toEuclideanLin, inner_basisFun_toEuclideanLin]
  have hs : A j i = A i j := by simpa using hA.apply i j
  rw [hs]
  ring


/-! ## Squared-distance Hessians for elliptic barriers -/

private lemma max_quad_eq {n : ℕ} (ε : ℝ) (c : EuclideanSpace ℝ (Fin n)) :
    (fun y => ε * ‖y - c‖ ^ 2) = quadraticAt ((2 * ε) • 1) c 0 0 := by
  funext y
  symm
  calc
    quadraticAt ((2 * ε) • 1) c 0 0 y =
        quadraticAt (0 : Matrix (Fin n) (Fin n) ℝ) c 0 0 y + (2 * ε) / 2 * ‖y - c‖ ^ 2 := by
      simpa only [zero_add] using quadraticAt_shift (0 : Matrix (Fin n) (Fin n) ℝ) c 0 0 y (2 * ε)
    _ = ε * ‖y - c‖ ^ 2 := by simp [quadraticAt]

theorem hessianMatrix_mul_norm_sub_sq {n : ℕ} (ε : ℝ) (c x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => ε * ‖y - c‖ ^ 2) x = (2 * ε) • 1 := by
  rw [max_quad_eq]
  exact hessianMatrix_quadraticAt (by simp) c 0 0 x

end FunctionalInequalities.Analysis
