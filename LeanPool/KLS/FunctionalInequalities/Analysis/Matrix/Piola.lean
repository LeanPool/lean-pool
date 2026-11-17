/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.SmoothBall
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.WeakDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Mollification.Hessian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# The Piola identity for Hessian adjugates

`Σⱼ ∂ⱼ adj(∇²u)ᵢⱼ = 0` for `C³` functions `u` (`sum_fderiv_adjugate_hessianMatrix_eq_zero`), in
terms of
`Probability.Stein.hessianMatrix`; the smooth input of the weak Piola identity on the moment-map
route to Letwin
arXiv:2607.24164v1. The cofactor consumers also supply essential boundedness from a Lipschitz
gradient and weak adjugate derivatives from a given local-L2 Hessian tensor; they do not assume
smoothness of that tensor or prove the main bound.
-/

@[expose] public section

section

open Matrix
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma det_swap_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j k : Fin n)
    (a b : Fin n → ℝ) (h : j ≠ k) :
    ((A.updateRow j a).updateRow k b).det =
      -((A.updateRow k a).updateRow j b).det := by
  let M := (A.updateRow k a).updateRow j b
  have hkj : k ≠ j := Ne.symm h
  have he :
      M.submatrix (Equiv.swap j k) id =
        (A.updateRow j a).updateRow k b := by
    ext r l
    by_cases hrj : r = j
    · subst r
      simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, h, hkj]
    · by_cases hrk : r = k
      · subst r
        simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply]
      · simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, hrj, hrk,
          Equiv.swap_apply_of_ne_of_ne hrj hrk]
  rw [← he, Matrix.det_permute]
  simp [M, Equiv.Perm.sign_swap h]

private lemma fderiv_apply_clm
    {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E → G →L[ℝ] H} {x : E} (hf : DifferentiableAt ℝ f x)
    (v : G) (w : E) :
    fderiv ℝ (fun y => f y v) x w = fderiv ℝ f x w v := by
  have h :=
    congrArg (fun L : E →L[ℝ] H => L w)
      (((ContinuousLinearMap.apply ℝ H v).hasFDerivAt.comp x hf.hasFDerivAt).fderiv)
  change fderiv ℝ (fun y => f y v) x w = fderiv ℝ f x w v at h
  exact h

private lemma fderiv_det_updateRow
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Fin n → Fin n → ℝ) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
    (j : Fin n) (c : Fin n → ℝ) (v : E) :
    fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
  let D : E →L[ℝ] Fin n → Fin n → ℝ :=
    ContinuousLinearMap.pi (fun k =>
      ContinuousLinearMap.pi (fun l =>
        if k = j then (0 : E →L[ℝ] ℝ)
        else fderiv ℝ (fun y => A y k l) x))
  let B : E → Fin n → Fin n → ℝ :=
    fun y k l => if k = j then c l else A y k l
  have hD : HasFDerivAt B D x := by
    apply hasFDerivAt_pi.mpr
    intro k
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases h : k = j
    · simpa only [B, h, ite_true] using (hasFDerivAt_const (c l) x)
    · simpa only [B, h, ite_false] using (hA k l).hasFDerivAt
  have he :
      (fun y => (Matrix.updateRow (A y) j c).det) =
        (fun y => (Matrix.of (B y)).det) := by
    funext y
    congr 1
    ext k l
    exact Matrix.updateRow_apply
  rw [he]
  have hd :=
    congrArg (fun L : E →L[ℝ] ℝ => L v)
      ((differentiableAt_det (Matrix.of (B x))).hasFDerivAt.comp x hD).fderiv
  change
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
      fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
        (B x) (D v) at hd
  have hdet :=
    fderiv_det_eq_sum_updateRow (Matrix.of (B x)) (Matrix.of (D v))
  change
    fderiv ℝ Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) =
      ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det at hdet
  have hB : Matrix.of (B x) = Matrix.updateRow (Matrix.of (A x)) j c := by
    ext k l
    exact Matrix.updateRow_apply.symm
  calc
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
        fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
          (B x) (D v) := hd
    _ = ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det := hdet
    _ = ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
      rw [hB]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = j
      · subst k
        rw [ite_eq_left rfl]
        apply Matrix.det_eq_zero_of_row_eq_zero j
        intro l
        rw [Matrix.updateRow_self]
        simp [D]
      · rw [ite_eq_right h]
        have hr :
            (Matrix.of (D v)) k =
              fun l => fderiv ℝ (fun y => A y k l) x v := by
          funext l
          simp only [Matrix.of_apply, D, ContinuousLinearMap.pi_apply, ite_eq_right h]
        rw [hr]
        rfl

/-- **Piola identity for the adjugate of a smooth Hessian** (smooth
case): for a `C³` function `u` on `ℝⁿ`, the rows of the adjugate (cofactor) matrix of the Hessian
`H = ∇²u` are divergence-free: `∑ⱼ ∂ⱼ (adj H)ᵢⱼ = 0`. Here `hessianMatrix u y i j = D²u(y)(eᵢ, eⱼ)`
in the standard basis `eⱼ = EuclideanSpace.basisFun (Fin n) ℝ j`. -/
theorem sum_fderiv_adjugate_hessianMatrix_eq_zero {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 3 u) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x
      (EuclideanSpace.basisFun (Fin n) ℝ j) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have h₂ : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have h₁ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    h₂.fderiv_right (by norm_num)
  have hentry :
      ∀ k l, DifferentiableAt ℝ (fun y => hessianMatrix u y k l) x := by
    intro k l
    have hclm :
        ContDiff ℝ 1
          (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) :=
      (h₁.clm_apply contDiff_const).clm_apply contDiff_const
    change DifferentiableAt ℝ
      (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) x
    exact (hclm.differentiable (by norm_num)).differentiableAt
  have hsym :
      ∀ j k l,
        fderiv ℝ (fun y => hessianMatrix u y k l) x (e j) =
          fderiv ℝ (fun y => hessianMatrix u y j l) x (e k) := by
    intro j k l
    change
      fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) x (e j) =
        fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e j)) (e l)) x (e k)
    have hc :
        DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x :=
      (h₁.differentiable (by norm_num)).differentiableAt
    have hck :
        DifferentiableAt ℝ
          (fun y => (fderiv ℝ (fderiv ℝ u) y) (e k)) x :=
      ((h₁.clm_apply contDiff_const).differentiable (by norm_num)).differentiableAt
    have hcj :
        DifferentiableAt ℝ
          (fun y => (fderiv ℝ (fderiv ℝ u) y) (e j)) x :=
      ((h₁.clm_apply contDiff_const).differentiable (by norm_num)).differentiableAt
    have hleft :=
      fderiv_apply_clm (f := fun y => (fderiv ℝ (fderiv ℝ u) y) (e k))
        hck (e l) (e j)
    have hright :=
      fderiv_apply_clm (f := fun y => (fderiv ℝ (fderiv ℝ u) y) (e j))
        hcj (e l) (e k)
    have hmiddle0 :=
      fderiv_apply_clm (f := fun y => fderiv ℝ (fderiv ℝ u) y)
        hc (e k) (e j)
    have hmiddle :
        (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (e k)) x (e j)) (e l) =
          ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e j)) (e k)) (e l) :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => q (e l)) hmiddle0
    have hs :=
      (h₂.contDiffAt (x := x)).isSymmSndFDerivAt
        (by rw [minSmoothness_of_isRCLikeNormedField])
        (e j) (e k)
    have hmiddle' :
        ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e j)) (e k)) (e l) =
          ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e k)) (e j)) (e l) :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => q (e l)) hs
    have hmiddle'' :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => q (e l))
        (fderiv_apply_clm (f := fun y => fderiv ℝ (fderiv ℝ u) y)
          hc (e j) (e k))
    calc
      fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) x (e j) =
          (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (e k)) x (e j)) (e l) :=
        hleft
      _ = ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e j)) (e k)) (e l) :=
        hmiddle
      _ = ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e k)) (e j)) (e l) :=
        hmiddle'
      _ = (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (e j)) x (e k)) (e l) :=
        hmiddle''.symm
      _ = fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e j)) (e l)) x (e k) :=
        hright.symm
  let C : Fin n → Fin n → ℝ :=
    fun j k =>
      if k = j then 0
      else (((Matrix.of (hessianMatrix u x)).updateRow j (Pi.single i 1)).updateRow k
        (fun l => fderiv ℝ (fun y => hessianMatrix u y k l) x (e j))).det
  have hdiv :
      ∀ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) =
        ∑ k, C j k := by
    intro j
    have heq :
        (fun y => (hessianMatrix u y).adjugate i j) =
          (fun y =>
            ((Matrix.of (hessianMatrix u y)).updateRow j
              (Pi.single i 1)).det) := by
      funext y
      rw [Matrix.adjugate_apply]
      rfl
    rw [heq]
    exact fderiv_det_updateRow
      (fun y => hessianMatrix u y) x hentry j (Pi.single i 1) (e j)
  have hanti : ∀ j k, C j k = -C k j := by
    intro j k
    by_cases h : j = k
    · subst k
      simp only [C, ite_eq_left rfl, neg_zero]
    · have hw :
          (fun l => fderiv ℝ (fun y => hessianMatrix u y k l) x (e j)) =
            (fun l => fderiv ℝ (fun y => hessianMatrix u y j l) x (e k)) := by
        funext l
        exact hsym j k l
      simp only [C, ite_eq_right h, ite_eq_right (Ne.symm h)]
      rw [hw]
      exact det_swap_rows (Matrix.of (hessianMatrix u x)) j k (Pi.single i 1)
        (fun l => fderiv ℝ (fun y => hessianMatrix u y j l) x (e k)) h
  calc
    ∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) =
        ∑ j, ∑ k, C j k := by
          apply Finset.sum_congr rfl
          intro j _
          exact hdiv j
    _ = 0 := by
      have hS :
          (∑ j, ∑ k, C j k) = -(∑ j, ∑ k, C j k) := by
        calc
          ∑ j, ∑ k, C j k = ∑ j, ∑ k, -C k j := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            exact hanti j k
          _ = ∑ j, -(∑ k, C k j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_neg_distrib _
          _ = -(∑ j, ∑ k, C k j) := by
            rw [Finset.sum_neg_distrib]
          _ = -(∑ j, ∑ k, C j k) := by
            congr 1
            exact Finset.sum_comm
      linarith

end FunctionalInequalities.Analysis

section WeakPiola

open MeasureTheory Matrix Filter
open scoped Topology
open FunctionalInequalities.Probability.Stein

/-! The weak Piola identity for `C¹` functions with Lipschitz gradient. -/

namespace FunctionalInequalities.Analysis

private lemma continuous_adjugate_gradientDerivativeMatrix {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        (gradientDerivativeMatrix L).adjugate i j) := by
  exact (continuous_apply j).comp
    ((continuous_apply i).comp continuous_gradientDerivativeMatrix.matrix_adjugate)

private lemma contDiff_adjugate_hessianMatrix {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 3 u)
    (i j : Fin n) :
    ContDiff ℝ 1 (fun x => (hessianMatrix u x).adjugate i j) := by
  classical
  have h₂ : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have h₁ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    h₂.fderiv_right (by norm_num)
  have hentry : ∀ r s, ContDiff ℝ 1 (fun x => hessianMatrix u x r s) := by
    intro r s
    exact (h₁.clm_apply contDiff_const).clm_apply contDiff_const
  simp only [Matrix.adjugate_apply, Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  apply ContDiff.const_smul
  apply contDiff_prod
  intro r _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hentry _ _

private lemma weakPiola_integration_by_parts {n : ℕ}
    {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, f x * fderiv ℝ ψ x v) =
      - ∫ x, fderiv ℝ f x v * ψ x := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact
      (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  · exact
      (hf.continuous.mul
        ((hψ.continuous_fderiv one_ne_zero).clm_apply
          continuous_const)).integrable_of_hasCompactSupport
            (hψc.fderiv_apply ℝ v).mul_left
  · exact
      (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  · exact fun x _ => hf.differentiable one_ne_zero x
  · exact fun x _ => hψ.differentiable one_ne_zero x

private lemma weakPiola_smooth {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 3 u)
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j *
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hA := contDiff_adjugate_hessianMatrix hu i
  have hInt : ∀ j : Fin n,
      Integrable (fun x =>
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro j
    exact
      ((((hA j).continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  calc
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (e j) =
        ∑ j, -(∫ x,
          fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact weakPiola_integration_by_parts (hA j) hψ hψc (e j)
    _ = -(∑ j, ∫ x,
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) :=
      Finset.sum_neg_distrib _
    _ = -(∫ x, ∑ j,
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) := by
      congr 1
      exact (integral_finsetSum Finset.univ (fun j _ => hInt j)).symm
    _ = 0 := by
      have hz : ∀ x, (∑ j,
          fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) *
            ψ x) = 0 := by
        intro x
        rw [← Finset.sum_mul]
        change
          (∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x
            (EuclideanSpace.basisFun (Fin n) ℝ j)) * ψ x = 0
        rw [sum_fderiv_adjugate_hessianMatrix_eq_zero hu x i, zero_mul]
      simp only [hz, integral_zero, neg_zero]

/-- **Weak Piola identity for a `C¹` function with Lipschitz gradient**:
the rows of the adjugate of the a.e. Hessian `H = D(∇u)` are weakly divergence-free,
`∑ⱼ ∫ (adj H)ᵢⱼ ∂ⱼψ = 0` for every `C¹` test `ψ` with compact support. Here
`hessianMatrix u x i j = D²u(x)(eᵢ, eⱼ)` is the true Hessian at every point where `∇u` is
differentiable (almost everywhere, Rademacher), and the identity is obtained by mollification from
the smooth case `sum_fderiv_adjugate_hessianMatrix_eq_zero`. -/
theorem sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
  classical
  obtain ⟨Uk, hUk, _, hLip, _, hconv⟩ :=
    exists_contDiff_approx_of_lipschitz_gradient hu hG
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hUk₃ : ∀ k, ContDiff ℝ 3 (Uk k) :=
    fun k => (hUk k).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hA : ∀ k j, ContDiff ℝ 1
      (fun x => (hessianMatrix (Uk k) x).adjugate i j) :=
    fun k j => contDiff_adjugate_hessianMatrix (hUk₃ k) i j
  have hψD : ∀ j : Fin n, Continuous (fun x => fderiv ℝ ψ x (e j)) :=
    fun _ => (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hlim : ∀ j : Fin n,
      Tendsto
        (fun k => ∫ x, (hessianMatrix (Uk k) x).adjugate i j *
          fderiv ℝ ψ x (e j))
        atTop
        (𝓝 (∫ x, (hessianMatrix u x).adjugate i j *
          fderiv ℝ ψ x (e j))) := by
    intro j
    have hco := continuous_adjugate_gradientDerivativeMatrix i j
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (G : ℝ)).exists_bound_of_continuousOn hco.continuousOn
    have hbound : ∀ k x, ‖(hessianMatrix (Uk k) x).adjugate i j‖ ≤ C := by
      intro k x
      rw [hessianMatrix_eq_gradientDerivativeMatrix]
      apply hC
      change dist (fderiv ℝ (gradient (Uk k)) x) 0 ≤ (G : ℝ)
      rw [dist_zero_right]
      exact norm_fderiv_le_of_lipschitz ℝ (hLip k)
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => C * ‖fderiv ℝ ψ x (e j)‖)
    · exact Filter.Eventually.of_forall fun k =>
        ((hA k j).continuous.mul (hψD j)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun k =>
        Filter.Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hbound k x) (norm_nonneg _)
    · exact
        ((hψD j).integrable_of_hasCompactSupport
          (hψc.fderiv_apply ℝ (e j))).norm.const_mul C
    · filter_upwards [hconv] with x hx
      have ht :=
        (hco.continuousAt.tendsto.comp hx).mul_const (fderiv ℝ ψ x (e j))
      simpa only [hessianMatrix_eq_gradientDerivativeMatrix, Function.comp_def] using ht
  have hsum :=
    tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  have hzero : ∀ k,
      (∑ j, ∫ x, (hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (e j)) = 0 :=
    fun k => weakPiola_smooth (hUk₃ k) hψ hψc i
  have hsumzero : Tendsto
      (fun k => ∑ j, ∫ x, (hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (e j)) atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hsumzero

end FunctionalInequalities.Analysis

end WeakPiola

section InverseHessianDivergence

open MeasureTheory Set Filter
open scoped Topology
open FunctionalInequalities.Probability.Stein

/-! The weak Piola identity for Lipschitz gradients and the divergence form of the inverse Hessian.
-/

namespace FunctionalInequalities.Analysis

section StructuredSpace

variable {E : Type*}
  [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E]

end NormedSpace

section FiniteDimensional

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section MeasurableSpace

variable [MeasurableSpace E] [BorelSpace E]

private lemma integrable_of_measurable_bounded_compact
    {f : E → ℝ} (hm : Measurable f) (hc : HasCompactSupport f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (volume : Measure E) := by
  have hl : LocallyIntegrable f (volume : Measure E) :=
    (memLp_top_of_bound hm.aestronglyMeasurable C
      (Eventually.of_forall hb)).locallyIntegrable le_top
  exact (hl.integrableOn_isCompact hc.isCompact).integrable_of_forall_notMem_eq_zero
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx)

private lemma integrable_fderiv_apply_of_lipschitz
    {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) (v : E) :
    Integrable (fun x => fderiv ℝ f x v) (volume : Measure E) :=
  integrable_of_measurable_bounded_compact (measurable_fderiv_apply_const ℝ f v)
    (hc.fderiv_apply ℝ v) (norm_fderiv_apply_le_of_lipschitz hf v)

private lemma integrable_weight_mul_fderiv_apply
    {f w : E → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) (hw : Continuous w) (v : E) :
    Integrable (fun x => w x * fderiv ℝ f x v) (volume : Measure E) := by
  have hd : LocallyIntegrable (fun x => fderiv ℝ f x v) (volume : Measure E) :=
    (memLp_top_of_bound (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable
      ((L : ℝ) * ‖v‖)
      (Eventually.of_forall (norm_fderiv_apply_le_of_lipschitz hf v))).locallyIntegrable le_top
  have hl := LocallyIntegrable.continuous_mul hw hd
  apply (hl.integrableOn_isCompact hc.isCompact).integrable_of_forall_notMem_eq_zero
  intro x hx
  simp only [fderiv_of_notMem_tsupport ℝ hx, _root_.zero_apply, mul_zero]

end MeasurableSpace

end FiniteDimensional

/-- Localization lets Lipschitz integration by parts act on a smooth coefficient. -/
private lemma integral_smooth_mul_fderiv_lipschitz {n : ℕ}
    {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψc : HasCompactSupport ψ) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, f x * fderiv ℝ ψ x v) =
      - ∫ x, fderiv ℝ f x v * ψ x := by
  obtain ⟨χ, hχ, hχc, hχeq⟩ := exists_compact_contDiff_eq_one_near hψc.isCompact
  let g := fun x => χ x * f x
  have hgd : ContDiff ℝ 1 g := hχ.mul hf
  have hgc : HasCompactSupport g := hχc.mul_right
  obtain ⟨D, hg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hgd one_ne_zero
  have heq (x) (hx : x ∈ tsupport ψ) : g =ᶠ[𝓝 x] f := by
    filter_upwards [hχeq x hx] with y hy
    change χ y * f y = f y
    rw [hy, one_mul]
  have hb := hg.integral_lineDeriv_mul_eq
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hψ hψc v
  have hl :
      (∫ x, lineDeriv ℝ g x v * ψ x) =
        ∫ x, fderiv ℝ f x v * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change lineDeriv ℝ g x v * ψ x = fderiv ℝ f x v * ψ x
      rw [(hgd.differentiable one_ne_zero x).lineDeriv_eq_fderiv]
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).fderiv_eq]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
  have hr :
      (∫ x, lineDeriv ℝ ψ x (-v) * g x) =
        -(∫ x, f x * fderiv ℝ ψ x v) := by
    calc
      (∫ x, lineDeriv ℝ ψ x (-v) * g x) =
          ∫ x, -(f x * fderiv ℝ ψ x v) := by
        apply integral_congr_ae
        filter_upwards [hψ.ae_differentiableAt
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hxD
        rw [hxD.lineDeriv_eq_fderiv, map_neg]
        by_cases hx : x ∈ tsupport ψ
        · rw [(heq x hx).eq_of_nhds]
          ring
        · rw [fderiv_of_notMem_tsupport ℝ hx]
          simp
      _ = _ := integral_neg _
  rw [hl, hr] at hb
  linarith

private lemma measurable_adjugate_hessianMatrix {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => (hessianMatrix u x).adjugate i j) := by
  simpa only [hessianMatrix_eq_gradientDerivativeMatrix, Function.comp_def] using
    (continuous_adjugate_gradientDerivativeMatrix i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))

private lemma norm_adjugate_hessianMatrix_le {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n) :
    ∃ C : ℝ, ∀ x, ‖(hessianMatrix u x).adjugate i j‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G : ℝ)).exists_bound_of_continuousOn
        (continuous_adjugate_gradientDerivativeMatrix i j).continuousOn
  refine ⟨C, fun x => ?_⟩
  rw [hessianMatrix_eq_gradientDerivativeMatrix]
  apply hC
  change dist (fderiv ℝ (gradient u) x) 0 ≤ (G : ℝ)
  rw [dist_zero_right]
  exact norm_fderiv_le_of_lipschitz ℝ hG

private lemma integral_smooth_adjugate_hessianMatrix_mul_fderiv {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 3 u)
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j *
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hA := contDiff_adjugate_hessianMatrix hu i
  have hInt : ∀ j : Fin n,
      Integrable (fun x =>
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro j
    exact
      ((((hA j).continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  calc
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (e j) =
        ∑ j, -(∫ x,
          fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_smooth_mul_fderiv_lipschitz (hA j) hψ hψc (e j)
    _ = -(∑ j, ∫ x,
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) :=
      Finset.sum_neg_distrib _
    _ = -(∫ x, ∑ j,
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) := by
      congr 1
      exact (integral_finsetSum Finset.univ (fun j _ => hInt j)).symm
    _ = 0 := by
      have hz : ∀ x, (∑ j,
          fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) = 0 := by
        intro x
        rw [← Finset.sum_mul]
        change
          (∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x
            (EuclideanSpace.basisFun (Fin n) ℝ j)) * ψ x = 0
        rw [sum_fderiv_adjugate_hessianMatrix_eq_zero hu x i, zero_mul]
      simp only [hz, integral_zero, neg_zero]

/-- Dominated convergence for smooth potentials with a fixed Lipschitz test. -/
private lemma tendsto_integral_adjugate_hessianMatrix {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {Uk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hLip : ∀ k, LipschitzWith G (gradient (Uk k)))
    (hconv : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k => fderiv ℝ (gradient (Uk k)) x) atTop
        (𝓝 (fderiv ℝ (gradient u) x)))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ) (i j : Fin n) :
    Tendsto
      (fun k => ∫ x, (hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
      atTop
      (𝓝 (∫ x, (hessianMatrix u x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))) := by
  let v := EuclideanSpace.basisFun (Fin n) ℝ j
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G : ℝ)).exists_bound_of_continuousOn
        (continuous_adjugate_gradientDerivativeMatrix i j).continuousOn
  have hb : ∀ k x, ‖(hessianMatrix (Uk k) x).adjugate i j‖ ≤ C := by
    intro k x
    rw [hessianMatrix_eq_gradientDerivativeMatrix]
    apply hC
    change dist (fderiv ℝ (gradient (Uk k)) x) 0 ≤ (G : ℝ)
    rw [dist_zero_right]
    exact norm_fderiv_le_of_lipschitz ℝ (hLip k)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => C * ‖fderiv ℝ ψ x v‖)
  · exact Eventually.of_forall fun k =>
      ((measurable_adjugate_hessianMatrix (Uk k) i j).mul
        (measurable_fderiv_apply_const ℝ ψ v)).aestronglyMeasurable
  · exact Eventually.of_forall fun k => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _)
  · exact (integrable_fderiv_apply_of_lipschitz hψ hψc v).norm.const_mul C
  · filter_upwards [hconv] with x hx
    have ht :=
      ((continuous_adjugate_gradientDerivativeMatrix i j).continuousAt.tendsto.comp hx).mul_const
        (fderiv ℝ ψ x v)
    simpa only [hessianMatrix_eq_gradientDerivativeMatrix, Function.comp_def] using ht

/-- **Weak Piola identity with Lipschitz tests**: for `u ∈ C¹` with Lipschitz
gradient and a Lipschitz `ψ` with compact support (`fderiv ℝ ψ` its a.e. derivative),
`∑ⱼ ∫ (adj ∇²u)ᵢⱼ ∂ⱼψ = 0`. -/
theorem sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal}
    (hψ : LipschitzWith Lψ ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
  classical
  obtain ⟨Uk, hUk, _, hLip, _, hconv⟩ :=
    exists_contDiff_approx_of_lipschitz_gradient hu hG
  have hUk₃ : ∀ k, ContDiff ℝ 3 (Uk k) :=
    fun k => (hUk k).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hsum := tendsto_finsetSum Finset.univ
    (fun j _ => tendsto_integral_adjugate_hessianMatrix hLip hconv hψ hψc i j)
  have hzero : ∀ k,
      (∑ j, ∫ x, (hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)) = 0 :=
    fun k => integral_smooth_adjugate_hessianMatrix_mul_fderiv (hUk₃ k) hψ hψc i
  have hsumzero : Tendsto
      (fun k => ∑ j, ∫ x, (hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
      atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hsumzero

private lemma lipschitzWith_compact_smooth_mul_lipschitz
    {f g : E → ℝ} {Lf Lg : NNReal}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hgb : ∃ D : ℝ, ∀ x, ‖g x‖ ≤ D) :
    ∃ L : NNReal, LipschitzWith L (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  let L : NNReal :=
    ⟨max C 0 * (Lg : ℝ) + max D 0 * (Lf : ℝ), by positivity⟩
  refine ⟨L, lipschitzWith_iff_norm_sub_le.mpr ?_⟩
  intro x y
  calc
    ‖f x * g x - f y * g y‖ =
        ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
      congr 1
      ring
    _ ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ max C 0 * ((Lg : ℝ) * ‖x - y‖) +
        ((Lf : ℝ) * ‖x - y‖) * max D 0 := by
      apply add_le_add
      · exact mul_le_mul ((hC x).trans (le_max_left _ _))
          (hg.norm_sub_le x y) (norm_nonneg _) (le_max_right _ _)
      · exact mul_le_mul (hf.norm_sub_le x y)
          ((hD y).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = (L : ℝ) * ‖x - y‖ := by
      change max C 0 * ((Lg : ℝ) * ‖x - y‖) +
        ((Lf : ℝ) * ‖x - y‖) * max D 0 =
          (max C 0 * (Lg : ℝ) + max D 0 * (Lf : ℝ)) * ‖x - y‖
      ring

end StructuredSpace

private lemma lipschitzWith_exp_neg_mul_test {n : ℕ}
    {F ψ : EuclideanSpace ℝ (Fin n) → ℝ} {LF Lψ : NNReal}
    (hF : LipschitzWith LF F) (hψ : LipschitzWith Lψ ψ)
    (hψc : HasCompactSupport ψ) :
    ∃ L : NNReal, LipschitzWith L (fun x => Real.exp (-F x) * ψ x) := by
  obtain ⟨χ, hχ, hχc, hχeq⟩ :=
    exists_compact_contDiff_eq_one_near (hψc.isCompact.image hF.continuous)
  let q : ℝ → ℝ := fun t => χ t * Real.exp (-t)
  have hq : ContDiff ℝ 1 q := hχ.mul contDiff_id.neg.exp
  have hqc : HasCompactSupport q := hχc.mul_right
  obtain ⟨Lq, hLq⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hqc hq one_ne_zero
  obtain ⟨C, hC⟩ := hqc.exists_bound_of_continuous hq.continuous
  obtain ⟨L, hL⟩ := lipschitzWith_compact_smooth_mul_lipschitz (hLq.comp hF) hψ
    ⟨C, fun x => hC (F x)⟩
    (hψc.exists_bound_of_continuous hψ.continuous)
  have he :
      (fun x => q (F x) * ψ x) =
        (fun x => Real.exp (-F x) * ψ x) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · have hh := (hχeq (F x) (mem_image_of_mem F hx)).eq_of_nhds
      change (χ (F x) * Real.exp (-F x)) * ψ x = _
      rw [hh, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  refine ⟨L, ?_⟩
  change LipschitzWith L (fun x => q (F x) * ψ x) at hL
  rw [he] at hL
  exact hL

/-- **Divergence of the inverse Hessian**: if moreover `det ∇²u = e^F` a.e. for a
Lipschitz `F`, then for Lipschitz `ψ` with compact support
`∑ⱼ ∫ (∇²u)⁻¹ᵢⱼ ∂ⱼψ = ∑ⱼ ∫ (∇²u)⁻¹ᵢⱼ ∂ⱼF ψ`, i.e. `div (∇²u)⁻¹ = −(∇²u)⁻¹ ∇F` weakly. -/
theorem sum_integral_inv_hessianMatrix_mul_fderiv_eq {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal} (hψ : LipschitzWith Lψ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ j) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hw : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.continuous.neg
  have htc : HasCompactSupport (fun x => Real.exp (-F x) * ψ x) :=
    hψc.mul_left
  obtain ⟨Lt, ht⟩ := lipschitzWith_exp_neg_mul_test hF hψ hψc
  have hzero :=
    sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz
      hu hG ht htc i
  have hinv :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ r s, (hessianMatrix u x)⁻¹ r s =
          Real.exp (-F x) * (hessianMatrix u x).adjugate r s := by
    filter_upwards [hdet] with x hx
    intro r s
    simp only [Matrix.inv_def, hx, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Real.exp_neg]
  have hd :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ v, fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x v =
          Real.exp (-F x) * (fderiv ℝ ψ x v - ψ x * fderiv ℝ F x v) := by
    filter_upwards [hF.ae_differentiableAt
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      hψ.ae_differentiableAt
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx hy
    have he :
        fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x =
          Real.exp (-F x) • fderiv ℝ ψ x +
            ψ x • (Real.exp (-F x) • (-fderiv ℝ F x)) :=
      ((hx.hasFDerivAt.neg.exp).mul hy.hasFDerivAt).fderiv
    intro v
    rw [he]
    simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
    ring
  have hA : ∀ j : Fin n,
      Integrable (fun x => (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro j
    obtain ⟨C, hC⟩ := norm_adjugate_hessianMatrix_le hG i j
    have hi := (integrable_weight_mul_fderiv_apply hψ hψc hw (e j)).bdd_mul
      (measurable_adjugate_hessianMatrix u i j).aestronglyMeasurable
      (Eventually.of_forall hC)
    apply hi.congr
    filter_upwards [hinv] with x hx
    change (hessianMatrix u x).adjugate i j *
        (Real.exp (-F x) * fderiv ℝ ψ x (e j)) =
      (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j)
    rw [hx i j]
    ring
  have hB : ∀ j : Fin n,
      Integrable (fun x =>
        (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro j
    obtain ⟨C, hC⟩ := norm_adjugate_hessianMatrix_le hG i j
    have hi :=
      (hw.mul hψ.continuous).integrable_of_hasCompactSupport
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) htc
    have hi' := hi.bdd_mul (measurable_fderiv_apply_const ℝ F (e j)).aestronglyMeasurable
      (Eventually.of_forall (norm_fderiv_apply_le_of_lipschitz hF (e j)))
    have hi'' := hi'.bdd_mul (measurable_adjugate_hessianMatrix u i j).aestronglyMeasurable
      (Eventually.of_forall hC)
    apply hi''.congr
    filter_upwards [hinv] with x hx
    change (hessianMatrix u x).adjugate i j *
        (fderiv ℝ F x (e j) * (Real.exp (-F x) * ψ x)) =
      (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x
    rw [hx i j]
    ring
  have hsplit (j : Fin n) :
      (∫ x, (hessianMatrix u x).adjugate i j *
        fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x (e j)) =
      (∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j)) -
      (∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x) := by
    calc
      (∫ x, (hessianMatrix u x).adjugate i j *
          fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x (e j)) =
          ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j) -
            (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x := by
        apply integral_congr_ae
        filter_upwards [hinv, hd] with x hx hxD
        rw [hxD (e j), hx i j]
        ring
      _ = _ := integral_sub (hA j) (hB j)
  change (∑ j, ∫ x, (hessianMatrix u x).adjugate i j *
    fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x (e j)) = 0 at hzero
  simp only [hsplit, Finset.sum_sub_distrib] at hzero
  exact sub_eq_zero.mp hzero

/-- Compactly supported bounded multipliers are integrable against inverse-Hessian
entries under the existing weak Monge-Ampere assumptions for Letwin (2.2). -/
theorem integrable_inv_hessianMatrix_mul_of_bounded_compact {n : ℕ}
    {u F f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : NNReal} (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hf : Measurable f) (hfc : HasCompactSupport f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (i j : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hw : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.neg
  -- The bounded-compact argument of `integrable_of_measurable_bounded_compact`,
  -- with continuous multiplication as in `integrable_weight_mul_fderiv_apply`.
  have hl : LocallyIntegrable f
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_top_of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).locallyIntegrable le_top
  have hwl := LocallyIntegrable.continuous_mul hw hl
  have hwi : Integrable (fun x => Real.exp (-F x) * f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hwl.integrableOn_isCompact hfc.isCompact).integrable_of_forall_notMem_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  obtain ⟨B, hB⟩ := norm_adjugate_hessianMatrix_le hG i j
  have hi := hwi.bdd_mul
    (measurable_adjugate_hessianMatrix u i j).aestronglyMeasurable
    (Filter.Eventually.of_forall hB)
  -- The AE inverse representation and congruence argument of
  -- `sum_integral_inv_hessianMatrix_mul_fderiv_eq` above.
  have hinv :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x)⁻¹ i j =
          Real.exp (-F x) * (hessianMatrix u x).adjugate i j := by
    filter_upwards [hdet] with x hx
    simp only [Matrix.inv_def, hx, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Real.exp_neg]
  apply hi.congr
  filter_upwards [hinv] with x hx
  change (hessianMatrix u x).adjugate i j * (Real.exp (-F x) * f x) =
    (hessianMatrix u x)⁻¹ i j * f x
  rw [hx]
  ring

end FunctionalInequalities.Analysis

end InverseHessianDivergence


section WeakHessianAdjugateConsumers
open MeasureTheory Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Analysis

theorem memLp_hessian_adjugate_top {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n) :
    MemLp (fun x => (hessianMatrix u x).adjugate i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨C, hC⟩ := norm_adjugate_hessianMatrix_le hG i j
  exact memLp_top_of_bound (measurable_adjugate_hessianMatrix u i j).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-- Existing cofactor proof core, for the same supplied actual tensor. -/
theorem exists_weak_hessian_adjugate_derivative {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hbound : ∀ r s : Fin n, MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (k i j : Fin n) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HasWeakDerivAlong (fun x => (hessianMatrix u x).adjugate i j) g
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  let A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (hessianMatrix u x).updateRow j (Pi.single i 1)
  let DA : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (Matrix.of fun r s => T x k r s).updateRow j (fun _ => 0)
  have hA (r s : Fin n) : HasWeakDerivAlong (fun x => A x r s)
      (fun x => DA x r s) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    by_cases hr : r = j
    · subst r
      simpa [A, DA, Matrix.updateRow_apply] using
        (hasWeakDerivAlong_of_contDiff
          (f := fun _ : EuclideanSpace ℝ (Fin n) => (Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          contDiff_const (EuclideanSpace.basisFun (Fin n) ℝ k))
    · simpa [A, DA, Matrix.updateRow_apply, hr] using (hT k r s).1
  have hAb (r s : Fin n) : MemLp (fun x => A x r s) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    by_cases hr : r = j
    · subst r
      simpa [A, Matrix.updateRow_apply] using
        (memLp_top_const ((Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
    · simpa [A, Matrix.updateRow_apply, hr] using hbound r s
  have hDA2 (r s : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => DA x r s) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    by_cases hr : r = j
    · subst r
      simp [DA, Matrix.updateRow_apply]
    · simpa [DA, Matrix.updateRow_apply, hr] using (hT k r s).2 S hS
  have hp := hasWeakDerivAlong_det_of_locally_memLp_two hA hAb hDA2
  refine ⟨_, ?_, hp.2⟩
  simpa only [Matrix.adjugate_apply] using hp.1
end FunctionalInequalities.Analysis
end WeakHessianAdjugateConsumers
