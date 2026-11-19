/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Hessian operators and their inverses

The Hessian as a continuous linear operator, its symmetry, positivity,
inverse entries and their local regularity, the contraction
`Σ_{a,c} ((∇²φ)⁻¹)_{ac} φ_{ai} φ_{ci} = φ_{ii}` for a positive definite Hessian, and the trace
bound `∇²φ(x)[v, v] ≤ Δφ(x) ‖v‖²` for a positive semidefinite Hessian form. Supports Letwin
arXiv:2607.24164v1, pp. 5--7, without assuming an equation or constructing
any moment potential. Coordinate matrices and the diffusion generator are
defined in separate modules.
-/

@[expose] public section

noncomputable section
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hessian operator `∇²φ(x) = D(∇φ)(x) : E →L[ℝ] E`. The Euclidean coordinate object
`Probability.Stein.hessianMatrix` is its standard-basis entry matrix
(`Probability.Stein.hessianMatrix_eq_operatorEntry_hessianOperator`). -/
def hessianOperator (φ : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (gradient φ) x

/-- The Hessian/gradient derivative identity needs C2 only at the point.
It applies to a reference given C2 on an open domain without a global extension. -/
theorem bilinearIteratedFDerivTwo_eq_inner_hessianOperator_at {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (u v : E) :
    bilinearIteratedFDerivTwo ℝ φ x u v = ⟪hessianOperator φ x u, v⟫ := by
  have hg : ContDiffAt ℝ 1 (gradient φ) x := by
    change ContDiffAt ℝ 1 ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ φ) x
    exact (InnerProductSpace.toDual ℝ E).symm.contDiff.contDiffAt.comp x
      (hφ.fderiv_right (m := 1) (by norm_num))
  have hfun : (fun y : E => fderiv ℝ φ y v) = fun y => ⟪gradient φ y, v⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply_at hφ, hfun,
    fderiv_inner_apply ℝ (hg.differentiableAt one_ne_zero) (differentiableAt_const v)]
  simp [hessianOperator]

/--
`D²φ(x)(u, v) = ⟪∇²φ(x) u, v⟫` (the same identity as
`Probability.Stein.hessian_eq_inner_fderiv_gradient`,
restated for the operator; the Hessian–Stein chain source is credited). -/
theorem bilinearIteratedFDerivTwo_eq_inner_hessianOperator {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x u v : E) : bilinearIteratedFDerivTwo ℝ φ x u v = ⟪hessianOperator φ x u, v⟫ := by
  exact bilinearIteratedFDerivTwo_eq_inner_hessianOperator_at hφ.contDiffAt u v

theorem operatorEntry_hessianOperator {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : E) (i j : Fin m) :
    operatorEntry b (hessianOperator φ x) i j = bilinearIteratedFDerivTwo ℝ φ x (b i) (b j) := by
  rw [bilinearIteratedFDerivTwo_symm hφ x (b i) (b j),
    bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ]
  exact real_inner_comm _ _

/-- A positive definite Hessian is a unit (including rank zero). -/
theorem hessianOperator_isUnit_of_posDef {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    IsUnit (hessianOperator φ x) := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot (hessianOperator φ x).toLinearMap).2
  apply LinearMap.ker_eq_bot.mpr
  intro u v huv
  change hessianOperator φ x u = hessianOperator φ x v at huv
  apply sub_eq_zero.mp
  by_contra hne
  have hp := hPD (u - v) hne
  have hz : hessianOperator φ x (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ, hz, inner_zero_left] at hp
  exact (lt_irrefl 0) hp

/-- The Hessian operator is self-adjoint. -/
theorem hessianOperator_isSelfAdjoint {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) :
    IsSelfAdjoint (hessianOperator φ x) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
  intro u v
  change ⟪hessianOperator φ x u, v⟫ = ⟪u, hessianOperator φ x v⟫
  calc
    ⟪hessianOperator φ x u, v⟫ = bilinearIteratedFDerivTwo ℝ φ x u v :=
      (bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ x u v).symm
    _ = bilinearIteratedFDerivTwo ℝ φ x v u := bilinearIteratedFDerivTwo_symm hφ x u v
    _ = ⟪hessianOperator φ x v, u⟫ :=
      bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ x v u
    _ = ⟪u, hessianOperator φ x v⟫ := real_inner_comm _ _

/-- The inverse of a positive definite Hessian is positive definite. -/
theorem inner_ringInverse_hessianOperator_pos {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (v : E) (hv : v ≠ 0) :
    0 < ⟪Ring.inverse (hessianOperator φ x) v, v⟫ := by
  have hunit := hessianOperator_isUnit_of_posDef hφ x hPD
  have hright : hessianOperator φ x (Ring.inverse (hessianOperator φ x) v) = v := by
    have h :=
      congrArg (fun L : E →L[ℝ] E => L v) (Ring.mul_inverse_cancel (hessianOperator φ x) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have hne : Ring.inverse (hessianOperator φ x) v ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hright
    exact hv hright.symm
  have hp := hPD (Ring.inverse (hessianOperator φ x) v) hne
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ, hright] at hp
  calc
    0 < ⟪v, Ring.inverse (hessianOperator φ x) v⟫ := hp
    _ = ⟪Ring.inverse (hessianOperator φ x) v, v⟫ := real_inner_comm _ _

/-- The entries `((∇²φ)⁻¹)_{ij}` of the inverse Hessian in an orthonormal basis. -/
def inverseHessianEntry {m : ℕ} (φ : E → ℝ) (b : OrthonormalBasis (Fin m) ℝ E)
    (x : E) (i j : Fin m) : ℝ := operatorEntry b (Ring.inverse (hessianOperator φ x)) i j

/-- The inverse Hessian is symmetric. -/
theorem inverseHessianEntry_symm {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) (i j : Fin m) :
    inverseHessianEntry φ b x i j = inverseHessianEntry φ b x j i := by
  have h := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
    (hessianOperator_isSelfAdjoint hφ x).ringInverse
  change ⟪b i, Ring.inverse (hessianOperator φ x) (b j)⟫ =
    ⟪b j, Ring.inverse (hessianOperator φ x) (b i)⟫
  calc
    ⟪b i, Ring.inverse (hessianOperator φ x) (b j)⟫ =
        ⟪Ring.inverse (hessianOperator φ x) (b j), b i⟫ := real_inner_comm _ _
    _ = ⟪b j, Ring.inverse (hessianOperator φ x) (b i)⟫ := h (b j) (b i)

/-- `(∇²φ)⁻¹ ∇²φ = Id` in coordinates. -/
theorem sum_inverseHessianEntry_mul_hessian {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j : Fin m) :
    (∑ a, inverseHessianEntry φ b x i a * bilinearIteratedFDerivTwo ℝ φ x (b a) (b j)) =
      if i = j then 1 else 0 := by
  obtain ⟨U, hU⟩ := hessianOperator_isUnit_of_posDef hφ x hPD
  have hInv : Ring.inverse (hessianOperator φ x) * hessianOperator φ x = 1 := by
    rw [← hU, Ring.inverse_unit]
    simp
  simp_rw [← operatorEntry_hessianOperator b hφ x]
  change
    (∑ a,
        operatorEntry b (Ring.inverse (hessianOperator φ x)) i a *
          operatorEntry b (hessianOperator φ x) a j) =
      _
  rw [← operatorEntry_mul, hInv]
  simp [operatorEntry, b.inner_eq_ite]

/-- `Σ_{a,c} ((∇²φ)⁻¹)_{ac} φ_{ai} φ_{ci} = φ_{ii}` in the standard orthonormal basis. -/
theorem sum_inverseHessianEntry_mul_hessian_hessian {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (i : Fin (Module.finrank ℝ E)) :
    (∑ a, ∑ c, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a c *
      bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E a) (stdOrthonormalBasis ℝ E i) *
      bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E c) (stdOrthonormalBasis ℝ E i)) =
      bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  calc
    (∑ a, ∑ c, inverseHessianEntry φ b x a c * bilinearIteratedFDerivTwo ℝ φ x (b a) (b i) *
        bilinearIteratedFDerivTwo ℝ φ x (b c) (b i)) =
        ∑ a, bilinearIteratedFDerivTwo ℝ φ x (b a) (b i) *
          ∑ c, inverseHessianEntry φ b x a c * bilinearIteratedFDerivTwo ℝ φ x (b c) (b i) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ a, bilinearIteratedFDerivTwo ℝ φ x (b a) (b i) * (if a = i then 1 else 0) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [sum_inverseHessianEntry_mul_hessian b hφ x hPD a i]
    _ = bilinearIteratedFDerivTwo ℝ φ x (b i) (b i) := by simp

/--
**Letwin (2.5), operator form**: `D((∇²φ)⁻¹)(x)[v] = −(∇²φ)⁻¹ (D(∇²φ)(x)[v]) (∇²φ)⁻¹` for a smooth
`φ`
with positive definite Hessian at `x`. -/
theorem fderiv_ringInverse_hessianOperator_apply {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (v : E) :
    fderiv ℝ (fun y => Ring.inverse (hessianOperator φ y)) x v =
      -(Ring.inverse (hessianOperator φ x) * fderiv ℝ (hessianOperator φ) x v *
          Ring.inverse (hessianOperator φ x)) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator φ) := hg.fderiv_right (by simp)
  exact
    fderiv_ringInverse_comp_apply (hH.differentiable (by simp) x)
      (hessianOperator_isUnit_of_posDef h2 x hPD) v

/-- Exact directional (2.5): the middle factor is the ACTUAL derivative of the Hessian
operatorEntry, hence source `partial_abk phi`. No such identity is supplied as a premise. -/
theorem fderiv_inverseHessianEntry_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j k : Fin m) :
    fderiv ℝ (fun y => inverseHessianEntry φ b y i j) x (b k) =
      -(∑ a,
          ∑ c,
            inverseHessianEntry φ b x i a *
                fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b k) *
              inverseHessianEntry φ b x c j) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator φ) := hg.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (hessianOperator φ) x := hH.differentiable (by simp) x
  have h :=
    operatorEntry_ringInverse_fderiv_apply b hd (hessianOperator_isUnit_of_posDef h2 x hPD) i j
      (b k)
  change
    fderiv ℝ (fun y => operatorEntry b (Ring.inverse (hessianOperator φ y)) i j) x (b k) = _
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro c _hc
  have heq :
    (fun y => operatorEntry b (hessianOperator φ y) a c) = fun y =>
      bilinearIteratedFDerivTwo ℝ φ y (b a) (b c) := by
    ext y
    exact operatorEntry_hessianOperator b h2 y a c
  rw [← operatorEntry_fderiv_apply b hd a c (b k), heq]
  rfl

section TraceBound

omit [FiniteDimensional ℝ E] in
/-- `⟪T v, v⟫ ≤ tr T ‖v‖²` for a positive semidefinite operator `T`, with the trace taken in an
orthonormal basis. -/
private theorem inner_le_basis_trace_mul_norm_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E)
    (hT : ∀ w : E, 0 ≤ ⟪T w, w⟫) (v : E) :
    ⟪T v, v⟫ ≤ (∑ i, ⟪T (b i), b i⟫) * ‖v‖ ^ 2 := by
  classical
  by_cases hv : v = 0
  · simp [hv]
  let a : ι → ℝ := fun i => ⟪b i, v⟫
  let s : ℝ := ‖v‖ ^ 2
  have hs : 0 < s := pow_pos (norm_pos_iff.mpr hv) 2
  have ha : (∑ i, a i • b i) = v := by
    simpa only [a, OrthonormalBasis.repr_apply_apply] using b.sum_repr v
  have hsq : (∑ i, (a i) ^ 2) = s := by
    simpa only [sum_inner, real_inner_smul_left, real_inner_self_eq_norm_sq, a, s, pow_two] using
      congrArg (fun w : E => ⟪w, v⟫) ha
  have h₁ : (∑ i, a i * ⟪T (b i), v⟫) = ⟪T v, v⟫ := by
    calc
      _ = ⟪T (∑ i, a i • b i), v⟫ := by
        simp only [map_sum, map_smul, sum_inner, real_inner_smul_left]
      _ = _ := by rw [ha]
  have h₂ : (∑ i, a i * ⟪T v, b i⟫) = ⟪T v, v⟫ := by
    calc
      _ = ⟪T v, ∑ i, a i • b i⟫ := by simp only [inner_sum, real_inner_smul_right]
      _ = _ := by rw [ha]
  have hexp (i : ι) :
      ⟪T (s • b i - a i • v), s • b i - a i • v⟫ =
        s ^ 2 * ⟪T (b i), b i⟫ - s * (a i * ⟪T (b i), v⟫) - s * (a i * ⟪T v, b i⟫) +
          (a i) ^ 2 * ⟪T v, v⟫ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    ring
  have hnonneg : 0 ≤ s ^ 2 * (∑ i, ⟪T (b i), b i⟫) - s * ⟪T v, v⟫ := by
    have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hT (s • b i - a i • v))
    simp_rw [hexp] at h
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul] at h
    rw [h₁, h₂, hsq] at h
    nlinarith
  exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith [hnonneg])

/-- A positive semidefinite Hessian form is bounded by its trace:
`∇²φ(x)[v, v] ≤ (Σ_i ∇²φ(x)[e_i, e_i]) ‖v‖²`. -/
theorem bilinearIteratedFDerivTwo_le_trace_mul_norm_sq {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPSD : ∀ v : E, 0 ≤ bilinearIteratedFDerivTwo ℝ φ x v v) (v : E) :
    bilinearIteratedFDerivTwo ℝ φ x v v ≤
      (∑ i, bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
        (stdOrthonormalBasis ℝ E i)) * ‖v‖ ^ 2 := by
  simp_rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ x] at hPSD ⊢
  exact inner_le_basis_trace_mul_norm_sq (stdOrthonormalBasis ℝ E) (hessianOperator φ x) hPSD v

end TraceBound

section LocalRegularity

/-- The inverse-Hessian entries are `C^∞` at a point of positive definiteness. -/
theorem contDiffAt_inverseHessianEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j : Fin m) :
    ContDiffAt ℝ ∞ (fun y => inverseHessianEntry φ b y i j) x := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator φ) := hg.fderiv_right (by simp)
  obtain ⟨Q, hQ⟩ := hessianOperator_isUnit_of_posDef h2 x hPD
  have hInvAt : ContDiffAt ℝ ∞ Ring.inverse (hessianOperator φ x) :=
    hQ ▸ contDiffAt_ringInverse ℝ Q
  have hInv := hInvAt.comp x hH.contDiffAt
  exact contDiffAt_const.inner ℝ (hInv.clm_apply contDiffAt_const)

/--
Derivative of the drift coordinate `∂_a V ∘ ∇φ`: `∂_j (∂_aV(∇φ)) = Σ_c ∂_{ac}V(∇φ) ∂_{cj}φ`, for `V`
smooth on an
open set containing `∇φ(x)`. -/
theorem fderiv_fderiv_comp_gradient_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    {x : E} (hx : gradient φ x ∈ U) (a j : Fin m) :
    fderiv ℝ (fun y => fderiv ℝ V (gradient φ y) (b a)) x (b j) =
      ∑ c,
        bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
          bilinearIteratedFDerivTwo ℝ φ x (b c) (b j) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hVx : ContDiffAt ℝ ∞ V (gradient φ x) := hV.contDiffAt (hU.mem_nhds hx)
  have hV2 : ContDiffAt ℝ 2 V (gradient φ x) := hVx.of_le (WithTop.coe_le_coe.mpr le_top)
  have ha : ContDiffAt ℝ ∞ (fun z => fderiv ℝ V z (b a)) (gradient φ x) :=
    (hVx.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hc :
    fderiv ℝ (fun y => fderiv ℝ V (gradient φ y) (b a)) x =
      fderiv ℝ (fun z => fderiv ℝ V z (b a)) (gradient φ x) ∘L fderiv ℝ (gradient φ) x :=
    fderiv_comp x (ha.differentiableAt (by simp)) ((hg.differentiable (by simp)) x)
  rw [hc, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (fun z => fderiv ℝ V z (b a)) (gradient φ x) (hessianOperator φ x (b j)) = _
  conv_lhs => rw [← b.sum_repr' (hessianOperator φ x (b j))]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _hc
  change operatorEntry b (hessianOperator φ x) c j * _ = _
  rw [operatorEntry_hessianOperator b h2, ← bilinearIteratedFDerivTwo_eq_fderiv_apply_at hV2,
    bilinearIteratedFDerivTwo_symm_at hV2 (b c) (b a)]
  ring

end LocalRegularity

end FunctionalInequalities.Analysis.BakryEmery
