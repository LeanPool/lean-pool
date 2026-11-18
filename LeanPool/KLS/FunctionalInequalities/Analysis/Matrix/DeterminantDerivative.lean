/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.RingInverseDerivative
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Derivative of the determinant and of the log-determinant (Jacobi's formula)

The determinant of a real square matrix is a continuous multilinear map of its rows; its derivative
in a direction `N` is the sum of row replacements and, for invertible `M`, equals `det M · tr(M⁻¹
N)`.
Hence `D(log det)(M)[N] = tr(M⁻¹ N)`, also along a differentiable matrix-valued map.
-/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.Elementwise

namespace FunctionalInequalities.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def detML : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by
      change Continuous (fun M : ι → ι → ℝ => (Matrix.of M).det)
      simp only [Matrix.det_apply, Matrix.of_apply]
      fun_prop }

/-- The determinant is differentiable (it is a continuous multilinear map of the rows). -/
theorem differentiableAt_det (M : Matrix ι ι ℝ) : DifferentiableAt ℝ Matrix.det M :=
  (detML.hasFDerivAt (fun i => M i)).differentiableAt

/-- The derivative of the determinant is the sum of row replacements. -/
theorem fderiv_det_eq_sum_updateRow (M N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det M N = ∑ i, (M.updateRow i (N i)).det := by
  change fderiv ℝ (detML : (ι → ι → ℝ) → ℝ) (fun i => M i) (fun i => N i) = _
  rw [(detML.hasFDerivAt (fun i => M i)).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/--
**Jacobi's formula**: `D(det)(M)[N] = det M · tr(M⁻¹ N)` for invertible `M` and any direction `N`.
-/
theorem fderiv_det_eq_det_mul_trace (M N : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    fderiv ℝ Matrix.det M N = M.det * Matrix.trace (M⁻¹ * N) := by
  have hNM : (N * M⁻¹) * M = N := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.mul_one]
  have hrow (i : ι) : N i = ∑ j, (N * M⁻¹) i j • M j := by
    calc
      N i = ((N * M⁻¹) * M) i := congrArg (fun Q : Matrix ι ι ℝ => Q i) hNM.symm
      _ = _ := by
        ext k
        simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_det_eq_sum_updateRow]
  calc
    (∑ i, (M.updateRow i (N i)).det) = ∑ i, (N * M⁻¹) i i * M.det := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hrow, Matrix.det_updateRow_sum]
      rfl
    _ = Matrix.trace (N * M⁻¹) * M.det := by
      rw [Matrix.trace, Finset.sum_mul]
      rfl
    _ = M.det * Matrix.trace (M⁻¹ * N) := by
      rw [Matrix.trace_mul_comm]
      ring

/-- `D(log det)(M)[N] = tr(M⁻¹ N)` for `det M ≠ 0`. -/
theorem fderiv_logDet_apply (M N : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M N = Matrix.trace (M⁻¹ * N) := by
  have hd := (differentiableAt_det M).hasFDerivAt.log hM
  calc
    fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M N =
        M.det⁻¹ * fderiv ℝ Matrix.det M N := by
      have h := congrArg (fun L : Matrix ι ι ℝ →L[ℝ] ℝ => L N) hd.fderiv
      exact h.trans rfl
    _ = Matrix.trace (M⁻¹ * N) := by
      rw [fderiv_det_eq_det_mul_trace M N (isUnit_iff_ne_zero.mpr hM)]
      rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]

theorem differentiableAt_logDet (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    DifferentiableAt ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M :=
  ((differentiableAt_det M).hasFDerivAt.log hM).differentiableAt

/-- Chain rule: `D(log det ∘ M)(x)[v] = tr(M(x)⁻¹ DM(x)[v])`. -/
theorem fderiv_logDet_comp_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : G → Matrix ι ι ℝ} {x : G} (hM : DifferentiableAt ℝ M x) (hdet : (M x).det ≠ 0) (v : G) :
    fderiv ℝ (fun y => Real.log (M y).det) x v = Matrix.trace ((M x)⁻¹ * fderiv ℝ M x v) := by
  have hc : fderiv ℝ (fun y => Real.log (M y).det) x =
      fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) (M x) ∘L fderiv ℝ M x :=
    fderiv_comp x (differentiableAt_logDet (M x) hdet) hM
  rw [hc, ContinuousLinearMap.comp_apply, fderiv_logDet_apply (M x) _ hdet]

end FunctionalInequalities.Analysis


section DeterminantPolynomialIdentification

open scoped BigOperators Matrix.Norms.Elementwise

namespace FunctionalInequalities.Analysis

section FiniteIndex

variable {ι : Type*}
  [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]

/-- Derivative of the finite determinant polynomial along a scalar affine path.
No outer matrix chain rule, invertibility, or nonempty-index assumption. -/
private theorem deriv_det_add_smul_zero
    (A N : Matrix ι ι ℝ) :
    deriv (fun t : ℝ => Matrix.det (A + t • N)) 0 =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j := by
  have hentry (σ : Equiv.Perm ι) (i : ι) :
      HasDerivAt (fun t : ℝ => A (σ i) i + t * N (σ i) i)
        (N (σ i) i) 0 := by
    simpa only [id_eq, one_mul] using
      HasDerivAt.const_add (A (σ i) i)
        ((hasDerivAt_id (0 : ℝ)).mul_const (N (σ i) i))
  have hprod (σ : Equiv.Perm ι) :
      HasDerivAt
        (fun t : ℝ => ∏ i : ι, (A (σ i) i + t * N (σ i) i))
        (∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j) 0 := by
    simpa only [zero_mul, add_zero, smul_eq_mul, mul_comm] using
      (HasDerivAt.fun_finsetProd (u := Finset.univ)
        (fun i _ => hentry σ i))
  have hpoly :
      HasDerivAt (fun t : ℝ => Matrix.det (A + t • N))
        (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i : ι, N (σ i) i *
            ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j) 0 := by
    simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact HasDerivAt.fun_sum
      (fun σ _ =>
        HasDerivAt.const_mul ((Equiv.Perm.sign σ : ℤ) : ℝ) (hprod σ))
  exact hpoly.deriv


/-- The signed permutation-polynomial determinant density is its existing
outer matrix derivative, including singular and empty matrices. -/
theorem fderiv_det_eq_sum_permutation
    (A N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det A N =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j := by
  have hd : DifferentiableAt ℝ Matrix.det (A + (0 : ℝ) • N) := by
    simpa only [zero_smul, add_zero] using differentiableAt_det A
  calc
    fderiv ℝ Matrix.det A N =
        deriv (fun t : ℝ => Matrix.det (A + t • N)) 0 := by
      simpa only [zero_smul, add_zero] using! hd.deriv_comp_add_smul.symm
    _ = _ := deriv_det_add_smul_zero A N

end FiniteIndex


end FunctionalInequalities.Analysis

end DeterminantPolynomialIdentification

/-! ## Smoothness of the log-determinant -/

section LogDetSmoothness

namespace FunctionalInequalities.Analysis

section LogDetContDiff

open scoped Matrix.Norms.Elementwise ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant is a polynomial in the entries, hence `C^k` for every `k`. -/
private theorem contDiff_det {k : ℕ∞ω} :
    ContDiff ℝ k (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change ContDiff ℝ k (fun M : Matrix ι ι ℝ => M.det)
  simp only [Matrix.det_apply]
  fun_prop

/--
`M ↦ log det M` is `C^k` (every `k`, including `ω`) at each matrix with nonzero determinant. This is
smoothness of the
matrix function only; nothing is claimed about a matrix field. -/
theorem contDiffAt_log_det {k : ℕ∞ω} {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) :
    ContDiffAt ℝ k (fun M : Matrix ι ι ℝ => Real.log M.det) A :=
  contDiff_det.contDiffAt.log hA

/-- `M ↦ log det M` is `C^k` at each positive definite matrix. -/
theorem contDiffAt_log_det_of_posDef {k : ℕ∞ω} {A : Matrix ι ι ℝ}
    (hA : A.PosDef) :
    ContDiffAt ℝ k (fun M : Matrix ι ι ℝ => Real.log M.det) A :=
  contDiffAt_log_det hA.det_pos.ne'

end LogDetContDiff

end FunctionalInequalities.Analysis

end LogDetSmoothness

/-! ## Local inverse-field and second log-determinant variations

The first and mixed second differential identities for a locally constant
determinant are the coordinate-invariant form of Savin, The obstacle problem
for Monge Ampere equation, DOI10.1007/s00526-004-0275-8, Proposition4.1 proof
(10)-(11), p13. They support the reference-regularity step in Letwin
arXiv2607.24164v1 Lemma2.2 via BB1207.6128v1 Theorem2.24(ii), without asserting
a Pogorelov bound or producing classical regularity for an unknown solution.
-/
noncomputable section
namespace FunctionalInequalities.Analysis
open Filter
open scoped Matrix.Norms.Elementwise Topology

private def endEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ ≃ₐ[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  AlgEquiv.ofLinearEquiv
    ((Matrix.toLinAlgEquiv' : Matrix ι ι ℝ ≃ₐ[ℝ] _).toLinearEquiv.trans
      LinearMap.toContinuousLinearMap)
    (by ext v i; simp)
    (by intro A B; ext v i; simp [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_mulVec])

private lemma end_inverse {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : IsUnit A.det) : Ring.inverse (endEquiv ι A) = endEquiv ι A⁻¹ := by
  apply left_inv_eq_right_inv
  · exact
      Ring.inverse_mul_cancel _
        (((Matrix.isUnit_iff_isUnit_det A).mpr hA).map (endEquiv ι).toRingHom)
  · rw [← map_mul, Matrix.mul_nonsing_inv A hA, map_one]

private lemma inverse_comp_derivative {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {M : G → Matrix ι ι ℝ} {x : G}
    (hM : DifferentiableAt ℝ M x) (hdet : (M x).det ≠ 0) :
    ∃ L : G →L[ℝ] Matrix ι ι ℝ,
      HasFDerivAt (fun y => (M y)⁻¹) L x ∧ ∀ v, L v = -((M x)⁻¹ * fderiv ℝ M x v * (M x)⁻¹) := by
  let e := endEquiv ι
  let ec := e.toLinearEquiv.toContinuousLinearEquiv
  have hu : IsUnit (e (M x)) :=
    ((Matrix.isUnit_iff_isUnit_det (M x)).mpr (isUnit_iff_ne_zero.mpr hdet)).map e.toRingHom
  have hE := ec.hasFDerivAt.comp x hM.hasFDerivAt
  have hI := hasFDerivAt_ringInverse_comp hE hu
  have hD := ec.symm.hasFDerivAt.comp x hI
  have hev : (fun y => ec.symm (Ring.inverse (ec (M y)))) =ᶠ[𝓝 x] (fun y => (M y)⁻¹) := by
    have hopen : IsOpen {A : Matrix ι ι ℝ | IsUnit A.det} := Units.isOpen.preimage (by fun_prop)
    filter_upwards [hM.continuousAt.preimage_mem_nhds
        (hopen.mem_nhds (isUnit_iff_ne_zero.mpr hdet))] with
      y hy
    apply e.injective
    change e (e.symm (Ring.inverse (e (M y)))) = e (M y)⁻¹
    rw [e.apply_symm_apply, end_inverse (M y) hy]
  have hd := hD.congr_of_eventuallyEq hev.symm
  refine ⟨_, hd, ?_⟩
  intro v
  change e.symm (-(Ring.inverse (e (M x)) * e (fderiv ℝ M x v) * Ring.inverse (e (M x)))) = _
  rw [end_inverse (M x) (isUnit_iff_ne_zero.mpr hdet)]
  apply e.injective
  simp only [map_neg, map_mul, AlgEquiv.apply_symm_apply]
  rfl

/-- Actual inverse-field derivative under the original elementwise matrix API.
The existing generic RingInverseDerivative is reused through the genuine
finite-dimensional matrix/endomorphism equivalence, without a norm change
in the statement, nonempty index, adjugate expansion or second inverse proof. -/
theorem fderiv_inverse_comp_apply {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {M : G → Matrix ι ι ℝ} {x : G}
    (hM : DifferentiableAt ℝ M x) (hdet : (M x).det ≠ 0) (v : G) :
    fderiv ℝ (fun y => (M y)⁻¹) x v = -((M x)⁻¹ * fderiv ℝ M x v * (M x)⁻¹) := by
  obtain ⟨L, hd, he⟩ := inverse_comp_derivative hM hdet
  have hv := congrArg (fun D : G →L[ℝ] Matrix ι ι ℝ => D v) hd.fderiv
  exact hv.trans (he v)

private lemma fderiv_trace_mul_apply {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {A B : G → Matrix ι ι ℝ} {x : G}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v : G) :
    fderiv ℝ (fun y => (A y * B y).trace) x v =
      (fderiv ℝ A x v * B x + A x * fderiv ℝ B x v).trace := by
  classical
  let T : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun a =>
        { toFun := fun b => (a * b).trace
          map_add' := by intros; simp [Matrix.mul_add, Matrix.trace_add]
          map_smul' := by intros; simp [Matrix.trace_smul] }
      map_add' := by intros; ext; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intros; ext; simp [Matrix.trace_smul] }
  let Tc := (LinearMap.toContinuousLinearMap.toLinearMap.comp T).toContinuousLinearMap
  have hd := Tc.hasFDerivAt_of_bilinear hA.hasFDerivAt hB.hasFDerivAt
  have hv := congrArg (fun L : G →L[ℝ] ℝ => L v) hd.fderiv
  change
    fderiv ℝ (fun y => (A y * B y).trace) x v =
      (A x * fderiv ℝ B x v).trace + (fderiv ℝ A x v * B x).trace at hv
  rw [Matrix.trace_add]
  linarith

/-- Actual mixed second variation of logdet along a C2 matrix field. Local
nonzero determinant suffices; no positive-definite, finite-dimensional source
space, complete source, nonempty index or linearized-equation premise. -/
theorem fderiv_logDet_comp_second_apply {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {M : G → Matrix ι ι ℝ} {x : G}
    (hM : ContDiffAt ℝ 2 M x) (hdet : (M x).det ≠ 0) (v w : G) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => Real.log (M z).det) y w) x v =
      ((M x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ M y w) x v).trace -
        ((M x)⁻¹ * fderiv ℝ M x v * (M x)⁻¹ * fderiv ℝ M x w).trace := by
  have hM0 : DifferentiableAt ℝ M x := hM.differentiableAt (by norm_num)
  have hDM : DifferentiableAt ℝ (fun y => fderiv ℝ M y w) x :=
    ((hM.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const w)
  obtain ⟨L, hInv, hInvApply⟩ := inverse_comp_derivative hM0 hdet
  have hnear :
    (fun y => fderiv ℝ (fun z => Real.log (M z).det) y w) =ᶠ[𝓝 x]
      (fun y => ((M y)⁻¹ * fderiv ℝ M y w).trace) := by
    have hn := hM.eventually (by norm_num)
    have hnz : ∀ᶠ y in 𝓝 x, (M y).det ≠ 0 :=
      (((differentiableAt_det (M x)).continuousAt.comp hM0.continuousAt).eventually_ne hdet)
    filter_upwards [hn, hnz] with y hy hyz
    exact fderiv_logDet_comp_apply (hy.differentiableAt (by norm_num)) hyz w
  rw [hnear.fderiv_eq, fderiv_trace_mul_apply hInv.differentiableAt hDM v, hInv.fderiv,
    hInvApply v, Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg]
  ring

/-- Savin Proposition4.1 proof (10)-(11): actual local constant determinant
generates BOTH differential identities. No linearized equation is assumed. -/
theorem trace_identities_of_eventually_det_const {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {M : G → Matrix ι ι ℝ} {x : G} {c : ℝ}
    (hM : ContDiffAt ℝ 2 M x) (hc : c ≠ 0) (heq : ∀ᶠ y in 𝓝 x, (M y).det = c) :
    (∀ v : G, ((M x)⁻¹ * fderiv ℝ M x v).trace = 0) ∧
      ∀ v w : G,
        ((M x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ M y w) x v).trace =
          ((M x)⁻¹ * fderiv ℝ M x v * (M x)⁻¹ * fderiv ℝ M x w).trace := by
  have hd : (M x).det ≠ 0 := by rw [mem_of_mem_nhds heq]; exact hc
  have hg : (fun y => Real.log (M y).det) =ᶠ[𝓝 x] (fun _ => Real.log c) := by
    filter_upwards [heq] with y hy
    rw [hy]
  constructor
  · intro v
    rw [← fderiv_logDet_comp_apply (hM.differentiableAt (by norm_num)) hd v, hg.fderiv_eq]
    simp
  · intro v w
    have hz :
      (fun y => fderiv ℝ (fun z => Real.log (M z).det) y w) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hg.eventually_nhds] with y hy
      have hyy : (fun z => Real.log (M z).det) =ᶠ[𝓝 y] (fun _ => Real.log c) := hy
      rw [hyy.fderiv_eq]
      simp
    have hs := fderiv_logDet_comp_second_apply hM hd v w
    rw [hz.fderiv_eq] at hs
    have hz0 : fderiv ℝ (fun _ : G => (0 : ℝ)) x v = 0 := by simp
    rw [hz0] at hs
    exact sub_eq_zero.mp hs.symm


end FunctionalInequalities.Analysis
