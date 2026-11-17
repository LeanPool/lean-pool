/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Diffusion
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Operator
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Matrix.Positivity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Monge–Ampère log-determinant relation: right-hand-side derivative

Letwin arXiv:2607.24164v1, (2.2)–(2.4): for a smooth `φ` and a `V` smooth on an open set containing
the gradient image, the zero-order equation `log det ∇²φ = −φ + V ∘ ∇φ` (a hypothesis here)
differentiates on its right-hand side to `−Dφ + DV(∇φ)[∇²φ ·]`; Jacobi's formula for the Hessian
gives the
left-hand side, hence the first derivative (2.4) of the equation; differentiating once more gives
(2.6)
with the inverse-Hessian operator, whose two right-hand-side matrices (`∇²φ ∇²V(∇φ) ∇²φ` for convex
`V`,
and the inverse-Hessian-weighted third-derivative Gram matrix) are positive semidefinite. Section
`LocalMaximum`: the pointwise maximum principle `L F ≤ 0` at a local maximum of a `C²` function `F`
where `∇²φ` is positive definite (`hessianInverseOperator_nonpos_of_isLocalMax`); no equation for
`φ`
and no global maximum principle are involved. Section
`QuadraticForm` (Letwin Lemma A.4, p. 17): at a point with positive definite `C²` Hessian, the
inverse-Hessian quadratic
form `Σ_ij ((∇²φ)⁻¹)_{ij} a_i a_j` is nonnegative in every orthonormal basis and every rank
(`sum_inverseHessianEntry_mul_mul_nonneg`). Section
`Divergence`: the coordinate divergence of the inverse Hessian `Σ_i ∂_i A_{ij} = Σ_i A_{ij} ∂_iφ −
∂_jV(∇φ)`
(from the zero-order equation, Jacobi and the third-slot commutation), the flux form
`Σ_i ∂_i (e^{−φ} A_{ij}) = −e^{−φ} ∂_jV(∇φ)` and the density divergence form of the operator `L` of
(2.2). The
potential `φ` is given; moment-map existence (Lemma 2.2), Theorem 2.5, Brascamp–Lieb and Proposition
2.8 are
not provided.
-/

@[expose] public section

noncomputable section
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open Filter Topology

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hessian matrix `(D²φ(x)(b i, b j))_{ij}` of `φ` in an orthonormal basis `b`. -/
def hessianMatrixIn {m : ℕ} (φ : E → ℝ) (b : OrthonormalBasis (Fin m) ℝ E) (x : E) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)

/-- `log det ∇²φ` in the basis `b`. -/
def logDetHessian {m : ℕ} (φ : E → ℝ) (b : OrthonormalBasis (Fin m) ℝ E) (x : E) : ℝ :=
  Real.log (hessianMatrixIn φ b x).det

/--
**Derivative of the right-hand side of the Monge–Ampère equation** `log det ∇²φ = −φ + V ∘ ∇φ`,
taken as a
hypothesis (Letwin (2.2)): `D(log det ∇²φ)(x)[v] = −Dφ(x)[v] + DV(∇φ x)[∇²φ(x) v]`, for `V` smooth
on an open set
containing `∇φ(x)`. Jacobi's derivative of the determinant (the left-hand side, Lemma 2.4) is not
provided. -/
theorem fderiv_logDetHessian_of_mongeAmpere {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ b y = -φ y + V (gradient φ y)) {x : E} (hx : gradient φ x ∈ U)
    (v : E) :
    fderiv ℝ (logDetHessian φ b) x v =
      -fderiv ℝ φ x v + fderiv ℝ V (gradient φ x) (hessianOperator φ x v) := by
  have heq : logDetHessian φ b = fun y => -φ y + V (gradient φ y) := funext hMA
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hp := hφ.differentiable (by simp) x
  have hVx := (hV.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hcomp := (contDiffAt_comp_gradient_of_mem hφ hU hV hx).differentiableAt (by simp)
  rw [heq, fderiv_fun_add (f := fun y => -φ y) (g := fun y => V (gradient φ y)) hp.neg hcomp,
    fderiv_fun_neg]
  have hc :
    fderiv ℝ (fun y => V (gradient φ y)) x =
      fderiv ℝ V (gradient φ x) ∘L fderiv ℝ (gradient φ) x :=
    fderiv_comp x hVx (hg.differentiable (by simp) x)
  rw [hc]
  simp only [add_apply, neg_apply, ContinuousLinearMap.comp_apply, hessianOperator]

section MatrixBridge

/-- The Hessian matrix is the matrix of the Hessian operator in the basis. -/
theorem hessianMatrixIn_eq_toMatrix {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : E) :
    hessianMatrixIn φ b x =
      LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator φ x).toLinearMap := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact (operatorEntry_hessianOperator b hφ x i j).symm

theorem inverseHessianEntry_mul_hessianMatrixIn {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    Matrix.of (fun i j => inverseHessianEntry φ b x i j) * hessianMatrixIn φ b x = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  exact sum_inverseHessianEntry_mul_hessian b hφ x hPD i j

theorem inv_hessianMatrixIn {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (hessianMatrixIn φ b x)⁻¹ = Matrix.of (fun i j => inverseHessianEntry φ b x i j) :=
  Matrix.inv_eq_left_inv (inverseHessianEntry_mul_hessianMatrixIn b hφ x hPD)

/-- A positive definite Hessian has nonzero determinant. -/
theorem det_hessianMatrixIn_ne_zero {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (hessianMatrixIn φ b x).det ≠ 0 := by
  have h := congrArg Matrix.det (inverseHessianEntry_mul_hessianMatrixIn b hφ x hPD)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, mul_zero] at h
  norm_num at h

/-- The Hessian matrix of a `C^∞` function is `C^∞`. -/
theorem contDiff_hessianMatrixIn {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (hessianMatrixIn φ b) := by
  let L₀ : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    (LinearMap.toMatrix b.toBasis b.toBasis).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  let L : (E →L[ℝ] E) →L[ℝ] Matrix (Fin m) (Fin m) ℝ := L₀.toContinuousLinearMap
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator φ) := hg.fderiv_right (by simp)
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : hessianMatrixIn φ b = L ∘ hessianOperator φ := by
    ext x i j
    exact congrArg (fun Q : Matrix (Fin m) (Fin m) ℝ => Q i j) (hessianMatrixIn_eq_toMatrix b h2 x)
  rw [heq]
  exact L.contDiff.comp hH

end MatrixBridge

section Jacobi

theorem fderiv_hessianMatrixIn_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x v : E) (i j : Fin m) :
    (fderiv ℝ (hessianMatrixIn φ b) x v) i j =
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b j)) x v := by
  let L₀ : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ := L₀.toContinuousLinearMap
  have hD :=
    L.hasFDerivAt.comp x
      ((contDiff_hessianMatrixIn b hφ).differentiable (by simp) x).hasFDerivAt
  symm
  change fderiv ℝ (L ∘ hessianMatrixIn φ b) x v = L (fderiv ℝ (hessianMatrixIn φ b) x v)
  rw [hD.fderiv]
  rfl

/--
**Jacobi for the Hessian**: `D(log det ∇²φ)(x)[v] = tr((∇²φ)⁻¹ D(∇²φ)(x)[v])` at a point of positive
definiteness. -/
theorem fderiv_logDetHessian_eq_trace {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (v : E) :
    fderiv ℝ (logDetHessian φ b) x v =
      Matrix.trace ((hessianMatrixIn φ b x)⁻¹ * fderiv ℝ (hessianMatrixIn φ b) x v) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  exact
    fderiv_logDet_comp_apply ((contDiff_hessianMatrixIn b hφ).differentiable (by simp) x)
      (det_hessianMatrixIn_ne_zero b h2 x hPD) v

/--
Jacobi for the Hessian in coordinates: `D(log det ∇²φ)[v] = Σ_{a,c} ((∇²φ)⁻¹)_{ac} ∂_v ∂_{ac}φ`. -/
theorem fderiv_logDetHessian_eq_sum {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (v : E) :
    fderiv ℝ (logDetHessian φ b) x v =
      ∑ a,
        ∑ c,
          inverseHessianEntry φ b x a c *
            fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x v := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [fderiv_logDetHessian_eq_trace b hφ x hPD v, inv_hessianMatrixIn b h2 x hPD]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro c _hc
  rw [fderiv_hessianMatrixIn_apply b hφ x v c a]
  have heq :
    (fun y => bilinearIteratedFDerivTwo ℝ φ y (b c) (b a)) = fun y =>
      bilinearIteratedFDerivTwo ℝ φ y (b a) (b c) := by
    ext y
    exact bilinearIteratedFDerivTwo_symm h2 y (b c) (b a)
  rw [heq]

/--
**Letwin (2.4), first derivative of the Monge–Ampère equation**: given `log det ∇²φ = −φ + V∘∇φ` and
`V`
smooth on an open set containing `∇φ(x)`, `Σ_{a,c} ((∇²φ)⁻¹)_{ac} ∂_{iac}φ = −∂_iφ + Σ_a ∂_aV(∇φ)
∂_{ai}φ`. -/
theorem mongeAmpere_first_derivative {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ b y = -φ y + V (gradient φ y)) {x : E} (hx : gradient φ x ∈ U)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i : Fin m) :
    (∑ a,
        ∑ c,
          inverseHessianEntry φ b x a c *
            fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b i)) =
      -fderiv ℝ φ x (b i) +
        ∑ a, fderiv ℝ V (gradient φ x) (b a) * bilinearIteratedFDerivTwo ℝ φ x (b a) (b i) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [← fderiv_logDetHessian_eq_sum b hφ x hPD (b i),
    fderiv_logDetHessian_of_mongeAmpere b hφ hU hV hMA hx (b i)]
  congr 1
  conv_lhs => rw [← b.sum_repr' (hessianOperator φ x (b i))]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  change operatorEntry b (hessianOperator φ x) a i * fderiv ℝ V (gradient φ x) (b a) = _
  rw [operatorEntry_hessianOperator b h2 x a i]
  ring


/--
(2.4) with the source scope: `V` smooth on an open neighbourhood `U` of `closure K`, `∇φ` ranging in
`K`. -/
theorem mongeAmpere_first_derivative_on_range {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {K U : Set E} (hU : IsOpen U) (hKU : closure K ⊆ U)
    (hV : ContDiffOn ℝ ∞ V U) (hRange : Set.range (gradient φ) ⊆ K)
    (hMA : ∀ y, logDetHessian φ b y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (x : E) (i : Fin m) :
    (∑ a,
        ∑ c,
          inverseHessianEntry φ b x a c *
            fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b i)) =
      -fderiv ℝ φ x (b i) +
        ∑ a, fderiv ℝ V (gradient φ x) (b a) * bilinearIteratedFDerivTwo ℝ φ x (b a) (b i) := by
  exact
    mongeAmpere_first_derivative b hφ hU hV hMA
      (hKU (subset_closure (hRange (Set.mem_range_self x)))) (hPD x) i

end Jacobi

section Positivity

section HessianPositivity

omit [FiniteDimensional ℝ E]
/-- A nonnegative Hessian form gives a positive semidefinite Hessian matrix (pointwise `C²`). -/
theorem hessianMatrixIn_posSemidef {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x)
    (hH : ∀ v : E, 0 ≤ bilinearIteratedFDerivTwo ℝ φ x v v) :
    (hessianMatrixIn φ b x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, hessianMatrixIn]
    exact bilinearIteratedFDerivTwo_symm_at hφ (b j) (b i)
  · intro v
    have heq : dotProduct (star v) ((hessianMatrixIn φ b x).mulVec v) =
        bilinearIteratedFDerivTwo ℝ φ x (∑ i, v i • b i) (∑ j, v j • b j) := by
      simp only [dotProduct, Matrix.mulVec, hessianMatrixIn, Pi.star_apply, star_trivial,
        map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [bilinearIteratedFDerivTwo_symm_at hφ (b j) (b i)]
      ring
    rw [heq]
    exact hH _

/-- The inverse Hessian matrix of a positive definite Hessian is positive semidefinite. -/
theorem inv_hessianMatrixIn_posSemidef {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} {x : E} (hφ : ContDiff ℝ 2 φ)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (hessianMatrixIn φ b x)⁻¹.PosSemidef := by
  apply Matrix.PosSemidef.inv
  apply hessianMatrixIn_posSemidef b hφ.contDiffAt
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · exact (hPD v hv).le

end HessianPositivity

section LocalMaximum

section HessianSign

omit [FiniteDimensional ℝ E]

/-- A one-variable second-derivative test: at a local maximum `0` of a differentiable `g`,
a derivative `d` of `g'` at `0` is nonpositive. -/
private theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ}
    (hg : Differentiable ℝ g) (hm : IsLocalMax g 0) {d : ℝ}
    (hd : HasDerivAt (deriv g) d 0) : d ≤ 0 := by
  by_contra hn
  have hdpos : 0 < d := lt_of_not_ge hn
  have hs : Tendsto (fun t : ℝ => t⁻¹ * (deriv g t - deriv g 0)) (𝓝[≠] 0) (𝓝 d) := by
    simpa [smul_eq_mul, slope] using hd.tendsto_slope_zero
  have he : ∀ᶠ t : ℝ in 𝓝 0, t ≠ 0 → 0 < t⁻¹ * (deriv g t - deriv g 0) := by
    simpa only [eventually_nhdsWithin_iff, Set.mem_compl_iff, Set.mem_singleton_iff] using
      hs.eventually (lt_mem_nhds hdpos)
  have hm' : ∀ᶠ t : ℝ in 𝓝 0, g t ≤ g 0 := hm
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp (he.and hm')
  have hb : (0 : ℝ) < ε / 2 := by linarith
  have hgb : g (ε / 2) ≤ g 0 := (hεprop (by rw [Real.dist_eq, sub_zero, abs_of_pos hb]; linarith)).2
  obtain ⟨c, hc, heq⟩ :=
    exists_deriv_eq_slope g hb hg.continuous.continuousOn hg.differentiableOn
  have hcp := (hεprop (show dist c 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos hc.1]; linarith [hc.2])).1 (ne_of_gt hc.1)
  rw [hm.deriv_eq_zero, sub_zero] at hcp
  have hcderiv : 0 < deriv g c := by
    by_contra h
    have hmul : c⁻¹ * deriv g c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hc.1).le (le_of_not_gt h)
    linarith
  have hslope : (g (ε / 2) - g 0) / (ε / 2 - 0) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hgb) (by linarith)
  rw [heq] at hcderiv
  exact (not_lt_of_ge hslope) hcderiv

/-- At a local maximum of a `C²` function the Hessian form is nonpositive. -/
private theorem bilinearIteratedFDerivTwo_self_nonpos_of_isLocalMax {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {x : E} (hmax : IsLocalMax F x) (v : E) :
    bilinearIteratedFDerivTwo ℝ F x v v ≤ 0 := by
  let g : ℝ → ℝ := fun t => F (x + t • v)
  have hg : ∀ t, HasDerivAt g (fderiv ℝ F (x + t • v) v) t := fun t =>
    (hF.differentiable (by norm_num) (x + t • v)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_line x v t)
  have hderiv : deriv g = fun t => fderiv ℝ F (x + t • v) v := funext fun t => (hg t).deriv
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using (hasDerivAt_line x v 0).continuousAt.tendsto
  have hm : IsLocalMax g 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, F (x + t • v) ≤ F (x + (0 : ℝ) • v)
    simpa only [zero_smul, add_zero] using ht.eventually (show ∀ᶠ y in 𝓝 x, F y ≤ F x from hmax)
  have hd : HasDerivAt (fun t : ℝ => fderiv ℝ F (x + t • v) v)
      (bilinearIteratedFDerivTwo ℝ F x v v) 0 := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hF x v v]
    simpa [Function.comp_def] using
      (differentiable_fderiv_apply hF v (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0
        (hasDerivAt_line x v 0)
  rw [← hderiv] at hd
  exact deriv_deriv_nonpos_of_isLocalMax (fun t => (hg t).differentiableAt) hm hd

private theorem bilinearIteratedFDerivTwo_neg_apply {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    (x u v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => -F y) x u v = -bilinearIteratedFDerivTwo ℝ F x u v := by
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hF.neg x u v,
    bilinearIteratedFDerivTwo_eq_fderiv_apply hF x u v]
  have he : (fun y => fderiv ℝ (fun z => -F z) y v) = fun y => -(fderiv ℝ F y v) := by
    funext y
    exact congrArg (fun L : E →L[ℝ] ℝ => L v)
      (hF.differentiable (by norm_num) y).hasFDerivAt.neg.fderiv
  rw [he]
  exact congrArg (fun L : E →L[ℝ] ℝ => L u)
    (differentiable_fderiv_apply hF v x).hasFDerivAt.neg.fderiv

end HessianSign

/-- **Maximum principle, pointwise form**: `L F ≤ 0` at a local maximum of a `C²` function `F`,
when `∇²φ` is positive definite at that point. -/
theorem hessianInverseOperator_nonpos_of_isLocalMax {φ F : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (V : E → ℝ) (hF : ContDiff ℝ 2 F) {x : E} (hmax : IsLocalMax F x)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    hessianInverseOperator φ V F x ≤ 0 := by
  let b := stdOrthonormalBasis ℝ E
  have hC : (hessianMatrixIn (fun y => -F y) b x).PosSemidef := by
    apply hessianMatrixIn_posSemidef b hF.neg.contDiffAt
    intro v
    rw [bilinearIteratedFDerivTwo_neg_apply hF x v v]
    exact neg_nonneg.mpr (bilinearIteratedFDerivTwo_self_nonpos_of_isLocalMax hF hmax v)
  have hA := inv_hessianMatrixIn_posSemidef b hφ hPD
  rw [inv_hessianMatrixIn b hφ x hPD] at hA
  have hsum := sum_entry_mul_nonneg hA hC
  change 0 ≤ ∑ i, ∑ j, inverseHessianEntry φ b x i j *
    bilinearIteratedFDerivTwo ℝ (fun y => -F y) x (b i) (b j) at hsum
  simp_rw [bilinearIteratedFDerivTwo_neg_apply hF, mul_neg, Finset.sum_neg_distrib] at hsum
  simpa only [hessianInverseOperator, nondivergenceOperator, hmax.fderiv_eq_zero,
    zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] using
    neg_nonneg.mp hsum

end LocalMaximum

end Positivity

section SecondDerivative

/-- Derivative of the left-hand side of (2.4) in the direction `b j`. -/
theorem fderiv_mongeAmpere_first_lhs {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j : Fin m) :
    fderiv ℝ
        (fun y =>
          ∑ a,
            ∑ c,
              inverseHessianEntry φ b y a c *
                fderiv ℝ (fun z => bilinearIteratedFDerivTwo ℝ φ z (b a) (b c)) y (b i))
        x (b j) =
      (∑ a,
          ∑ c,
            inverseHessianEntry φ b x a c *
              bilinearIteratedFDerivTwo ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b j))
                x (b a) (b c)) -
        ∑ a,
          ∑ c,
            ∑ p,
              ∑ q,
                inverseHessianEntry φ b x a p * inverseHessianEntry φ b x c q *
                    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b i) *
                  fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b p) (b q)) x (b j) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hA (a c : Fin m) : DifferentiableAt ℝ (fun y => inverseHessianEntry φ b y a c) x :=
    (contDiffAt_inverseHessianEntry b hφ x hPD a c).differentiableAt (by simp)
  have hT (a c : Fin m) :
    ContDiff ℝ ∞
      (fun y => fderiv ℝ (fun z => bilinearIteratedFDerivTwo ℝ φ z (b a) (b c)) y (b i)) :=
    contDiff_fderiv_apply (contDiff_bilinearIteratedFDerivTwo_apply hφ (b a) (b c)) (by simp)
      (b i)
  have hp (a c : Fin m) :
    DifferentiableAt ℝ
      (fun y =>
        inverseHessianEntry φ b y a c *
          fderiv ℝ (fun z => bilinearIteratedFDerivTwo ℝ φ z (b a) (b c)) y (b i))
      x :=
    (hA a c).mul ((hT a c).differentiable (by simp) x)
  have hs (a : Fin m) :
    DifferentiableAt ℝ
      (fun y =>
        ∑ c,
          inverseHessianEntry φ b y a c *
            fderiv ℝ (fun z => bilinearIteratedFDerivTwo ℝ φ z (b a) (b c)) y (b i))
      x :=
    DifferentiableAt.fun_sum (fun c _ => hp a c)
  rw [fderiv_sum_apply Finset.univ (fun a _ => hs a)]
  simp_rw [fderiv_sum_apply Finset.univ (fun c _ => hp _ c)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [fderiv_mul_apply (hA a c) ((hT a c).differentiable (by simp) x),
    fderiv_inverseHessianEntry_apply b hφ x hPD a c j]
  have hH2 : ContDiff ℝ 2 (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) :=
    (contDiff_bilinearIteratedFDerivTwo_apply hφ (b a) (b c)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hH2,
    bilinearIteratedFDerivTwo_symm hH2 x (b j) (b i),
    bilinearIteratedFDerivTwo_bilinearIteratedFDerivTwo_comm hφ x (b a) (b c) (b i) (b j)]
  simp only [mul_neg, sub_eq_add_neg]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [inverseHessianEntry_symm b h2 x q c]
  ring


/-- Derivative of the right-hand side of (2.4) in the direction `b j` (local `V`). -/
theorem fderiv_mongeAmpere_first_rhs {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U) {x : E} (hx : gradient φ x ∈ U) (i j : Fin m) :
    fderiv ℝ (fun y => -fderiv ℝ φ y (b i) + ∑ a, fderiv ℝ V (gradient φ y) (b a) *
      bilinearIteratedFDerivTwo ℝ φ y (b a) (b i)) x (b j) =
      -bilinearIteratedFDerivTwo ℝ φ x (b i) (b j) +
      (∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ φ x (b i) (b a) *
        bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
        bilinearIteratedFDerivTwo ℝ φ x (b c) (b j)) +
      ∑ a, fderiv ℝ V (gradient φ x) (b a) *
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b j)) x (b a) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hVx : ContDiffAt ℝ ∞ V (gradient φ x) := hV.contDiffAt (hU.mem_nhds hx)
  have hDVa (a : Fin m) : ContDiffAt ℝ ∞ (fun y => fderiv ℝ V (gradient φ y) (b a)) x :=
    ((hVx.fderiv_right (by simp)).clm_apply contDiffAt_const).comp x hg.contDiffAt
  have hH (a : Fin m) := contDiff_bilinearIteratedFDerivTwo_apply hφ (b a) (b i)
  have hp (a : Fin m) : DifferentiableAt ℝ (fun y => fderiv ℝ V (gradient φ y) (b a) *
      bilinearIteratedFDerivTwo ℝ φ y (b a) (b i)) x :=
    ((hDVa a).differentiableAt (by simp)).mul ((hH a).differentiable (by simp) x)
  have hs : DifferentiableAt ℝ (fun y => ∑ a, fderiv ℝ V (gradient φ y) (b a) *
      bilinearIteratedFDerivTwo ℝ φ y (b a) (b i)) x :=
    DifferentiableAt.fun_sum (fun a _ => hp a)
  have hDi := contDiff_fderiv_apply hφ (m := ∞) (by simp) (b i)
  have hn : DifferentiableAt ℝ (fun y => -fderiv ℝ φ y (b i)) x :=
    (hDi.differentiable (by simp) x).neg
  rw [fderiv_add_apply hn hs,
    fderiv_fun_neg, neg_apply, ← bilinearIteratedFDerivTwo_eq_fderiv_apply h2,
    bilinearIteratedFDerivTwo_symm h2 x (b j) (b i),
    fderiv_sum_apply Finset.univ (fun a _ => hp a)]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fderiv_mul_apply ((hDVa a).differentiableAt (by simp)) ((hH a).differentiable (by simp) x),
    fderiv_fderiv_comp_gradient_apply b hφ hU hV hx a j,
    fderiv_bilinearIteratedFDerivTwo_comm hφ x (b a) (b i) (b j)]
  have heq : (fun y => bilinearIteratedFDerivTwo ℝ φ y (b j) (b i)) =
      fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b j) :=
    funext fun y => bilinearIteratedFDerivTwo_symm h2 y (b j) (b i)
  rw [heq, bilinearIteratedFDerivTwo_symm h2 x (b a) (b i), Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  ring

theorem posSemidef_hessian_conj_hessian {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ 2 φ) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ 2 V U) (hc : ConvexOn ℝ U V)
    {x : E} (hx : gradient φ x ∈ U) :
    (Matrix.of fun i j => ∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ φ x (b i) (b a) *
      bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
      bilinearIteratedFDerivTwo ℝ φ x (b c) (b j)).PosSemidef := by
  have hVP := hessianMatrixIn_posSemidef b (hV.contDiffAt (hU.mem_nhds hx))
    (bilinearIteratedFDerivTwo_self_nonneg_of_convexOn_open hU hV hc hx)
  have hHerm : (hessianMatrixIn φ b x).conjTranspose = hessianMatrixIn φ b x := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, hessianMatrixIn]
    exact FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm hφ x (b j) (b i)
  have h := hVP.mul_mul_conjTranspose_same (hessianMatrixIn φ b x)
  rw [hHerm] at h
  have heq : hessianMatrixIn φ b x * hessianMatrixIn V b (gradient φ x) * hessianMatrixIn φ b x =
      Matrix.of (fun i j => ∑ a, ∑ c, bilinearIteratedFDerivTwo ℝ φ x (b i) (b a) *
        bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
        bilinearIteratedFDerivTwo ℝ φ x (b c) (b j)) := by
    rw [Matrix.mul_assoc]
    ext i j
    change (∑ a, bilinearIteratedFDerivTwo ℝ φ x (b i) (b a) *
      (∑ c, bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
        bilinearIteratedFDerivTwo ℝ φ x (b c) (b j))) = _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro c _hc
    ring
  exact heq ▸ h

/--
The same with the source scope: `V` convex on the open `K ⊇ range ∇φ` and smooth on a neighbourhood
of
`closure K`. -/
theorem posSemidef_hessian_conj_hessian_on_range {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ 2 φ) {K U : Set E} (hK : IsOpen K) (hKU : closure K ⊆ U)
    (hV : ContDiffOn ℝ 2 V U) (hc : ConvexOn ℝ K V) (hRange : Set.range (gradient φ) ⊆ K)
    (x : E) :
    (Matrix.of fun i j =>
        ∑ a,
          ∑ c,
            bilinearIteratedFDerivTwo ℝ φ x (b i) (b a) *
                bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
              bilinearIteratedFDerivTwo ℝ φ x (b c) (b j)).PosSemidef := by
  exact
    posSemidef_hessian_conj_hessian b hφ hK (hV.mono (subset_closure.trans hKU)) hc
      (hRange (Set.mem_range_self x))

/--
The third-derivative Gram matrix weighted by the inverse Hessian (the second term of (2.6)) is
positive
semidefinite. -/
theorem posSemidef_inverseHessian_third_gram {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (Matrix.of fun i j =>
        ∑ a,
          ∑ c,
            ∑ p,
              ∑ q,
                inverseHessianEntry φ b x a p * inverseHessianEntry φ b x c q *
                    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b i) *
                  fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b p) (b q)) x
                    (b j)).PosSemidef := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hA := inv_hessianMatrixIn_posSemidef b h2 hPD
  rw [inv_hessianMatrixIn b h2 x hPD] at hA
  exact
    posSemidef_weightedGram _ hA
      (fun i =>
        Matrix.of fun a c =>
          fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b i))

/--
**Letwin (2.6), second derivative of the Monge–Ampère equation** in coordinates: given the
zero-order equation,
`Σ_{ac} ((∇²φ)⁻¹)_{ac} ∂_{ac}∂_{ij}φ − Σ_a ∂_aV(∇φ) ∂_a∂_{ij}φ + ∂_{ij}φ = (∇²φ ∇²V(∇φ) ∇²φ)_{ij} +
Gram_{ij}`. -/
theorem mongeAmpere_second_derivative_coordinate {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ b y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) {x : E}
    (hx : gradient φ x ∈ U) (i j : Fin m) :
    (∑ a,
            ∑ c,
              inverseHessianEntry φ b x a c *
                bilinearIteratedFDerivTwo ℝ
                  (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b j)) x (b a) (b c)) -
          (∑ a,
            fderiv ℝ V (gradient φ x) (b a) *
              fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b j)) x (b a)) +
        bilinearIteratedFDerivTwo ℝ φ x (b i) (b j) =
      (∑ a,
          ∑ c,
            bilinearIteratedFDerivTwo ℝ φ x (b i) (b a) *
                bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
              bilinearIteratedFDerivTwo ℝ φ x (b c) (b j)) +
        ∑ a,
          ∑ c,
            ∑ p,
              ∑ q,
                inverseHessianEntry φ b x a p * inverseHessianEntry φ b x c q *
                    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b i) *
                  fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b p) (b q)) x (b j) := by
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hmem : ∀ᶠ y in 𝓝 x, gradient φ y ∈ U :=
    hg.continuous.continuousAt.tendsto.eventually (hU.mem_nhds hx)
  have heq :
    (fun y =>
        ∑ a,
          ∑ c,
            inverseHessianEntry φ b y a c *
              fderiv ℝ (fun z => bilinearIteratedFDerivTwo ℝ φ z (b a) (b c)) y (b i)) =ᶠ[𝓝 x]
      (fun y =>
        -fderiv ℝ φ y (b i) +
          ∑ a, fderiv ℝ V (gradient φ y) (b a) * bilinearIteratedFDerivTwo ℝ φ y (b a) (b i)) := by
    filter_upwards [hmem] with y hy
    exact mongeAmpere_first_derivative b hφ hU hV hMA hy (hPD y) i
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L (b j)) heq.fderiv_eq
  rw [fderiv_mongeAmpere_first_lhs b hφ x (hPD x) i j,
    fderiv_mongeAmpere_first_rhs b hφ hU hV hx i j] at hd
  linarith

/--
**Letwin (2.6)** with the inverse-Hessian operator: `L(∂_{ij}φ) + ∂_{ij}φ = (∇²φ ∇²V(∇φ) ∇²φ)_{ij} +
Gram_{ij}`
(the zero-order Monge–Ampère equation is a hypothesis; moment-map existence is not provided). -/
theorem mongeAmpere_second_derivative {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {U : Set E}
    (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) {x : E}
    (hx : gradient φ x ∈ U) (i j : Fin (Module.finrank ℝ E)) :
    hessianInverseOperator φ V
          (fun y =>
            bilinearIteratedFDerivTwo ℝ φ y (stdOrthonormalBasis ℝ E i)
              (stdOrthonormalBasis ℝ E j))
          x +
        bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j) =
      (∑ a,
          ∑ c,
            bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
                  (stdOrthonormalBasis ℝ E a) *
                bilinearIteratedFDerivTwo ℝ V (gradient φ x) (stdOrthonormalBasis ℝ E a)
                  (stdOrthonormalBasis ℝ E c) *
              bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E c)
                (stdOrthonormalBasis ℝ E j)) +
        ∑ a,
          ∑ c,
            ∑ p,
              ∑ q,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a p *
                      inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x c q *
                    fderiv ℝ
                      (fun y =>
                        bilinearIteratedFDerivTwo ℝ φ y (stdOrthonormalBasis ℝ E a)
                          (stdOrthonormalBasis ℝ E c))
                      x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ
                    (fun y =>
                      bilinearIteratedFDerivTwo ℝ φ y (stdOrthonormalBasis ℝ E p)
                        (stdOrthonormalBasis ℝ E q))
                    x (stdOrthonormalBasis ℝ E j) := by
  exact
    mongeAmpere_second_derivative_coordinate (stdOrthonormalBasis ℝ E) hφ hU hV hMA hPD hx i j

/--
(2.6) with the source scope: `V` smooth on an open neighbourhood of `closure K`, `∇φ` ranging in
`K`. -/
theorem mongeAmpere_second_derivative_on_range {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {K U : Set E}
    (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ K)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    hessianInverseOperator φ V
          (fun y =>
            bilinearIteratedFDerivTwo ℝ φ y (stdOrthonormalBasis ℝ E i)
              (stdOrthonormalBasis ℝ E j))
          x +
        bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j) =
      (∑ a,
          ∑ c,
            bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
                  (stdOrthonormalBasis ℝ E a) *
                bilinearIteratedFDerivTwo ℝ V (gradient φ x) (stdOrthonormalBasis ℝ E a)
                  (stdOrthonormalBasis ℝ E c) *
              bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E c)
                (stdOrthonormalBasis ℝ E j)) +
        ∑ a,
          ∑ c,
            ∑ p,
              ∑ q,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x a p *
                      inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x c q *
                    fderiv ℝ
                      (fun y =>
                        bilinearIteratedFDerivTwo ℝ φ y (stdOrthonormalBasis ℝ E a)
                          (stdOrthonormalBasis ℝ E c))
                      x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ
                    (fun y =>
                      bilinearIteratedFDerivTwo ℝ φ y (stdOrthonormalBasis ℝ E p)
                        (stdOrthonormalBasis ℝ E q))
                    x (stdOrthonormalBasis ℝ E j) := by
  exact
    mongeAmpere_second_derivative hφ hU hV hMA hPD
      (hKU (subset_closure (hRange (Set.mem_range_self x)))) i j

end SecondDerivative

section Divergence

/-- The inverse-Hessian entries are `C^∞` when the Hessian is positive definite everywhere. -/
theorem contDiff_inverseHessianEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j : Fin m) :
    ContDiff ℝ ∞ (fun y => inverseHessianEntry φ b y i j) :=
  contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_inverseHessianEntry b hφ x (hPD x) i j)

omit [FiniteDimensional ℝ E] in
/-- Cyclic third-slot equality from the `C²` symmetry and the derivative/Hessian commutation. -/
private theorem third_cyclic {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x u v w : E) :
    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y u v) x w =
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y w u) x v := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have he : (fun y => bilinearIteratedFDerivTwo ℝ φ y u v) =
      (fun y => bilinearIteratedFDerivTwo ℝ φ y v u) :=
    funext fun y => bilinearIteratedFDerivTwo_symm h2 y u v
  rw [he]
  exact fderiv_bilinearIteratedFDerivTwo_comm hφ x v u w

/--
**Divergence of the inverse Hessian** (Letwin (2.2)–(2.4) consequence): with `A = (∇²φ)⁻¹` and the
zero-order equation `log det ∇²φ = −φ + V ∘ ∇φ` near `∇φ(x)`,
`Σ_i ∂_i A_{ij}(x) = Σ_i A_{ij}(x) ∂_iφ(x) − ∂_jV(∇φ(x))`. -/
theorem inverseHessian_divergence {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ b y = -φ y + V (gradient φ y)) {x : E} (hx : gradient φ x ∈ U)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (j : Fin m) :
    (∑ i, fderiv ℝ (fun y => inverseHessianEntry φ b y i j) x (b i)) =
      (∑ i, inverseHessianEntry φ b x i j * fderiv ℝ φ x (b i)) -
        fderiv ℝ V (gradient φ x) (b j) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hHA (d : Fin m) :
    (∑ c, bilinearIteratedFDerivTwo ℝ φ x (b d) (b c) * inverseHessianEntry φ b x c j) =
      if d = j then 1 else 0 := by
    calc
      _ = ∑ c, inverseHessianEntry φ b x j c * bilinearIteratedFDerivTwo ℝ φ x (b c) (b d) := by
        apply Finset.sum_congr rfl
        intro c _hc
        rw [inverseHessianEntry_symm b h2 x c j,
          bilinearIteratedFDerivTwo_symm h2 x (b d) (b c)]
        ring
      _ = if j = d then 1 else 0 := sum_inverseHessianEntry_mul_hessian b h2 x hPD j d
      _ = _ := by simp only [eq_comm]
  calc
    _ =
        -(∑ i,
            ∑ a,
              ∑ c,
                inverseHessianEntry φ b x i a *
                    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b a)) x (b c) *
                  inverseHessianEntry φ b x c j) := by
      simp_rw [fderiv_inverseHessianEntry_apply b hφ x hPD, third_cyclic hφ]
      rw [Finset.sum_neg_distrib]
    _ =
        -(∑ c,
            (∑ i,
                ∑ a,
                  inverseHessianEntry φ b x i a *
                    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b a)) x (b c)) *
              inverseHessianEntry φ b x c j) := by
      congr 1
      calc
        _ =
            ∑ i,
              ∑ c,
                ∑ a,
                  inverseHessianEntry φ b x i a *
                      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b i) (b a)) x (b c) *
                    inverseHessianEntry φ b x c j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ =
        -(∑ c,
            (-fderiv ℝ φ x (b c) +
                ∑ d,
                  fderiv ℝ V (gradient φ x) (b d) *
                    bilinearIteratedFDerivTwo ℝ φ x (b d) (b c)) *
              inverseHessianEntry φ b x c j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro c _hc
      rw [mongeAmpere_first_derivative b hφ hU hV hMA hx hPD c]
    _ =
        (∑ c, inverseHessianEntry φ b x c j * fderiv ℝ φ x (b c)) -
          ∑ d,
            fderiv ℝ V (gradient φ x) (b d) *
              (∑ c,
                bilinearIteratedFDerivTwo ℝ φ x (b d) (b c) * inverseHessianEntry φ b x c j) := by
      simp_rw [add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm (f := fun c d => _)]
      simp only [neg_add, neg_neg, sub_eq_add_neg]
      congr 1
      · apply Finset.sum_congr rfl; intro c _hc; ring
      · congr 1
        apply Finset.sum_congr rfl; intro d _hd
        apply Finset.sum_congr rfl; intro c _hc; ring
    _ = _ := by
      simp_rw [hHA]
      simp

omit [FiniteDimensional ℝ E] in
private theorem fderiv_exp_neg_apply {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (fun y => Real.exp (-φ y)) x v = -Real.exp (-φ x) * fderiv ℝ φ x v := by
  have hd : HasFDerivAt (fun y => Real.exp (-φ y))
      (Real.exp (-φ x) • -fderiv ℝ φ x) x := by
    simpa only [Pi.neg_apply] using (hφ.differentiable (by simp) x).hasFDerivAt.neg.exp
  rw [hd.fderiv]
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

/--
**Flux form**: `Σ_i ∂_i (e^{−φ} A_{ij}) = −e^{−φ} ∂_jV(∇φ)` (no normalisation needed pointwise). -/
theorem density_inverseHessian_divergence {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ b y = -φ y + V (gradient φ y)) {x : E} (hx : gradient φ x ∈ U)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (j : Fin m) :
    (∑ i, fderiv ℝ (fun y => Real.exp (-φ y) * inverseHessianEntry φ b y i j) x (b i)) =
      -Real.exp (-φ x) * fderiv ℝ V (gradient φ x) (b j) := by
  have hw := (hφ.neg.exp).differentiable (by simp) x
  have hA (i : Fin m) :=
    (contDiffAt_inverseHessianEntry b hφ x hPD i j).differentiableAt (by simp)
  simp_rw [fderiv_mul_apply hw (hA _), fderiv_exp_neg_apply hφ]
  rw [Finset.sum_add_distrib]
  have he :
    (∑ i, inverseHessianEntry φ b x i j * (-Real.exp (-φ x) * fderiv ℝ φ x (b i))) =
      -Real.exp (-φ x) * ∑ i, inverseHessianEntry φ b x i j * fderiv ℝ φ x (b i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _hi; ring
  rw [he, ← Finset.mul_sum, inverseHessian_divergence b hφ hU hV hMA hx hPD j]
  ring

/--
**Density divergence form of `L`** (Letwin (2.2)): `Σ_{ij} ∂_i (e^{−φ} A_{ij} ∂_jf) = e^{−φ} L f` in
the
standard orthonormal basis, where `L f = Σ_{ij} A_{ij} ∂_{ij}f − Σ_i ∂_iV(∇φ) ∂_if`. -/
theorem density_hessianInverseOperator_flux {φ V f : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiff ℝ ∞ f) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y)) {x : E}
    (hx : gradient φ x ∈ U) (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (∑ i,
        ∑ j,
          fderiv ℝ
            (fun y =>
              Real.exp (-φ y) * inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y i j *
                fderiv ℝ f y (stdOrthonormalBasis ℝ E j))
            x (stdOrthonormalBasis ℝ E i)) =
      Real.exp (-φ x) * hessianInverseOperator φ V f x := by
  let b := stdOrthonormalBasis ℝ E
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hw := (hφ.neg.exp).differentiable (by simp) x
  have hA (i j : Fin (Module.finrank ℝ E)) :=
    (contDiffAt_inverseHessianEntry b hφ x hPD i j).differentiableAt (by simp)
  have hwa (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (fun y => Real.exp (-φ y) * inverseHessianEntry φ b y i j) x := by
    exact hw.fun_mul (hA i j)
  have hdf (j : Fin (Module.finrank ℝ E)) :=
    (contDiff_fderiv_apply hf (m := ∞) (by simp) (b j)).differentiable (by simp) x
  have hFirst :
    (∑ i,
        ∑ j,
          (Real.exp (-φ x) * inverseHessianEntry φ b x i j) *
            bilinearIteratedFDerivTwo ℝ f x (b i) (b j)) =
      Real.exp (-φ x) *
        ∑ i, ∑ j, inverseHessianEntry φ b x i j * bilinearIteratedFDerivTwo ℝ f x (b i) (b j) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _hi
    apply Finset.sum_congr rfl; intro j _hj; ring
  have hSecond :
    (∑ i,
        ∑ j,
          fderiv ℝ f x (b j) *
            fderiv ℝ (fun y => Real.exp (-φ y) * inverseHessianEntry φ b y i j) x (b i)) =
      -Real.exp (-φ x) * ∑ j, fderiv ℝ V (gradient φ x) (b j) * fderiv ℝ f x (b j) := by
    rw [Finset.sum_comm]
    calc
      _ =
          ∑ j,
            fderiv ℝ f x (b j) *
              ∑ i,
                fderiv ℝ (fun y => Real.exp (-φ y) * inverseHessianEntry φ b y i j) x (b i) := by
        simp_rw [Finset.mul_sum]
      _ = _ := by
        simp_rw [density_inverseHessian_divergence b hφ hU hV hMA hx hPD]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _hj; ring
  calc
    _ =
        ∑ i,
          ∑ j,
            ((Real.exp (-φ x) * inverseHessianEntry φ b x i j) *
                bilinearIteratedFDerivTwo ℝ f x (b i) (b j) +
              fderiv ℝ f x (b j) *
                fderiv ℝ (fun y => Real.exp (-φ y) * inverseHessianEntry φ b y i j) x (b i)) := by
      apply Finset.sum_congr rfl; intro i _hi
      apply Finset.sum_congr rfl; intro j _hj
      change
        fderiv ℝ (fun y => Real.exp (-φ y) * inverseHessianEntry φ b y i j * fderiv ℝ f y (b j))
            x (b i) =
          _
      rw [fderiv_mul_apply (hwa i j) (hdf j), ← bilinearIteratedFDerivTwo_eq_fderiv_apply hf2]
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hFirst, hSecond]
      change
        _ =
          Real.exp (-φ x) *
            ((∑ i,
                ∑ j,
                  inverseHessianEntry φ b x i j * bilinearIteratedFDerivTwo ℝ f x (b i) (b j)) -
              ∑ i, fderiv ℝ V (gradient φ x) (b i) * fderiv ℝ f x (b i))
      ring

end Divergence

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

section QuadraticForm

/--
**Nonnegative inverse-Hessian quadratic form** (Letwin Lemma A.4, p. 17, `φ^{ij}∂_iW∂_jW ≥ 0`): for
a `C²` `φ`
whose Hessian at `x` is positive definite, any orthonormal basis `b` (any rank `m`) and any
coefficients `a`,
`0 ≤ Σ_ij ((∇²φ(x))⁻¹)_{ij} a_i a_j`. -/
theorem sum_inverseHessianEntry_mul_mul_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (a : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, inverseHessianEntry φ b x i j * a i * a j := by
  have hquad :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg
      (inv_hessianMatrixIn_posSemidef (b := b) (x := x) (hφ := hφ) (hPD := hPD)) a
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul,
    inv_hessianMatrixIn b hφ x hPD, mul_assoc, mul_comm, mul_left_comm] using hquad

end QuadraticForm

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis

section StandardBasisLogDet

open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/--
`log det ∇²u` in the standard orthonormal basis equals the log-determinant of the coordinate Hessian
matrix. -/
theorem logDetHessian_std_eq_log_det_hessianMatrix {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    logDetHessian u (stdOrthonormalBasis ℝ E) x = Real.log (hessianMatrix u x).det := by
  unfold logDetHessian
  have hb : hessianMatrixIn u (EuclideanSpace.basisFun (Fin n) ℝ) x = hessianMatrix u x := rfl
  rw [hessianMatrixIn_eq_toMatrix _ hu]
  rw [LinearMap.det_toMatrix_eq_det_toMatrix (stdOrthonormalBasis ℝ E).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  rw [← hessianMatrixIn_eq_toMatrix _ hu, hb]

end StandardBasisLogDet

end FunctionalInequalities.Analysis
