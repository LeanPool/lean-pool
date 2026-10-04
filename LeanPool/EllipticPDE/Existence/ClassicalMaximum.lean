/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Sobolev.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Connected.Clopen


/-!
# Classical weak maximum principle

The weak maximum principle for a `C²` subsolution of a non-divergence-form elliptic equation
on a bounded open set: the maximum over the closure is attained on the boundary. Two pointwise
facts drive the proof. At an interior maximum of a `C²` function the gradient vanishes and the
Hessian is negative semidefinite, so the principal part `-∑ aᵢⱼ ∂ᵢ∂ⱼ u` is nonnegative there,
the coefficient matrix being positive semidefinite; this rests on the trace inequality
`∑ aᵢⱼ hᵢⱼ ≤ 0` for `a` positive semidefinite and `h` negative semidefinite, proved through the
spectral theorem. A strict subsolution therefore has no interior maximum. The general case
perturbs by `ε exp(λ x₁)`, which is a strict subsolution for `λ` large by uniform ellipticity
and the bound on the transport coefficient, and lets `ε` tend to zero.

The coefficients are asked to be symmetric, uniformly elliptic and, for the transport term,
bounded on the set; the sources also ask for continuity, which the proof does not use.

## Main declarations

* `EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef`: the trace inequality.
* `EllipticPdes.Classical.sndFDeriv_nonpos_of_isLocalMax`: the Hessian is negative
  semidefinite at an interior local maximum.
* `EllipticPdes.Classical.nondivOp`: the non-divergence-form operator.
* `EllipticPdes.Classical.weak_maximum_principle`: the weak maximum principle for a
  subsolution with no zeroth-order term.
* `EllipticPdes.Classical.weak_minimum_principle`: the same for a supersolution.
* `EllipticPdes.Classical.weak_maximum_principle_of_nonneg`: the weak maximum principle with
  nonnegative zeroth-order coefficient, through the positive part on the boundary.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.1 Theorem 1 (p. 343) and
Theorem 2 (p. 344);
D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§3.1 Theorem 3.1 (p. 32) and Corollary 3.2 (p. 33);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem XI.3.7.
-/

@[expose] public section

open Set Filter Topology Matrix

noncomputable section

namespace EllipticPdes.Classical

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The trace inequality -/

/-- A real matrix is Hermitian when it is symmetric. -/
theorem isHermitian_of_symm {A : Matrix (Fin d) (Fin d) ℝ} (h : ∀ i j, A i j = A j i) :
    A.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  ext i j
  exact h j i

/-- A symmetric real matrix with nonnegative quadratic form is positive semidefinite. -/
theorem posSemidef_of_forall {A : Matrix (Fin d) (Fin d) ℝ} (hsymm : ∀ i j, A i j = A j i)
    (hnn : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j) : A.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_symm hsymm) fun ξ => ?_
  have : star ξ ⬝ᵥ (A *ᵥ ξ) = ∑ i, ∑ j, A i j * ξ i * ξ j := by
    simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  exact hnn ξ

/-- **Trace inequality.** For `A` positive semidefinite and `-H` positive semidefinite,
`∑ᵢⱼ Aᵢⱼ Hᵢⱼ ≤ 0`. Through the spectral theorem `A = U D U*`, the sum is the trace of `A H`,
which is the trace of `D (U* H U)`, a sum of nonnegative eigenvalues times the nonpositive
diagonal entries of `U* H U`. -/
theorem sum_mul_nonpos_of_posSemidef {A H : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef)
    (hH : (-H).PosSemidef) : ∑ i, ∑ j, A i j * H i j ≤ 0 := by
  classical
  have hHs : ∀ i j, H i j = H j i := by
    intro i j
    have h := hH.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
    have := congrFun (congrFun h i) j
    simp only [transpose_apply, Matrix.neg_apply] at this
    linarith
  -- the sum as a trace
  have htr : ∑ i, ∑ j, A i j * H i j = trace (A * H) := by
    simp only [trace, diag_apply, mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hHs i j]
  rw [htr]
  -- the spectral decomposition of `A`
  set U : Matrix (Fin d) (Fin d) ℝ := (hA.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
    with hUdef
  have hspec : A = U * diagonal hA.1.eigenvalues * star U := by
    have := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [RCLike.ofReal_real_eq_id, hUdef] using this
  have hcycle : trace (U * diagonal hA.1.eigenvalues * star U * H)
      = trace (diagonal hA.1.eigenvalues * (star U * H * U)) := by
    have hassoc : U * diagonal hA.1.eigenvalues * star U * H
        = U * (diagonal hA.1.eigenvalues * (star U * H)) := by
      simp only [Matrix.mul_assoc]
    rw [hassoc, trace_mul_comm, Matrix.mul_assoc]
  have hAH : trace (A * H) = trace (U * diagonal hA.1.eigenvalues * star U * H) := by
    conv_lhs => rw [hspec]
  rw [hAH, hcycle]
  -- `U* (-H) U` is positive semidefinite, so the diagonal of `U* H U` is nonpositive
  have hconj : (star U * (-H) * U).PosSemidef := by
    have := hH.conjTranspose_mul_mul_same U
    rwa [← star_eq_conjTranspose] at this
  have hdiag : ∀ k, (star U * H * U) k k ≤ 0 := by
    intro k
    have h1 := hconj.diag_nonneg (i := k)
    have h2 : (star U * (-H) * U) k k = -((star U * H * U) k k) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    rw [h2] at h1
    linarith
  simp only [trace, diag_apply, diagonal_mul]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hA.eigenvalues_nonneg k)
    (hdiag k)

/-! ### The second-order test at a local maximum -/

/-- **One-dimensional second-order test.** A function with a continuous second derivative
near `0` and a local maximum at `0` has nonpositive second derivative at `0`. -/
theorem deriv2_nonpos_of_isLocalMax {φ φ' φ'' : ℝ → ℝ}
    (h1 : ∀ᶠ t in 𝓝 0, HasDerivAt φ (φ' t) t) (h2 : ∀ᶠ t in 𝓝 0, HasDerivAt φ' (φ'' t) t)
    (hc : ContinuousAt φ'' 0) (hmax : IsLocalMax φ 0) : φ'' 0 ≤ 0 := by
  by_contra hpos
  have hpos' : 0 < φ'' 0 := lt_of_not_ge hpos
  have h0 : φ' 0 = 0 := hmax.hasDerivAt_eq_zero h1.self_of_nhds
  -- a radius on which everything holds
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp
    (h1.and (h2.and (hc.eventually (lt_mem_nhds hpos'))))
  have hmem : ∀ t : ℝ, t ∈ Ioo (-ε) ε → dist t 0 < ε := fun t ht => by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  -- `φ'` is strictly increasing on `(-ε, ε)`, so positive on `(0, ε)`
  have hmono : StrictMonoOn φ' (Ioo (-ε) ε) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
    · intro t ht
      exact (hall (hmem t ht)).2.1.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hall (hmem t ht)).2.1.deriv]
      exact (hall (hmem t ht)).2.2
  have hφ'pos : ∀ t, t ∈ Ioo 0 ε → 0 < φ' t := by
    intro t ht
    have := hmono ⟨by linarith, by linarith⟩ ⟨ht.1.trans' (by linarith), ht.2⟩ ht.1
    rwa [h0] at this
  -- so `φ` is strictly increasing on `[0, ε)`
  have hφmono : StrictMonoOn φ (Ico 0 ε) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _) ?_ ?_
    · intro t ht
      have ht' : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], ht.2⟩
      exact (hall (hmem t ht')).1.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have ht' : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], ht.2⟩
      rw [(hall (hmem t ht')).1.deriv]
      exact hφ'pos t ht
  -- which contradicts the local maximum
  obtain ⟨η, hη, hmax'⟩ := Metric.eventually_nhds_iff.mp hmax
  set t : ℝ := min ε η / 2 with htdef
  have ht0 : 0 < t := by positivity
  have htε : t < ε := by
    have := min_le_left ε η
    linarith
  have htη : t < η := by
    have := min_le_right ε η
    linarith
  have hlt : φ 0 < φ t := hφmono ⟨le_rfl, hε⟩ ⟨ht0.le, htε⟩ ht0
  have hle : φ t ≤ φ 0 := hmax' (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htη)
  linarith

/-- The derivative of a `C²` function along a line, and the derivative of that. -/
theorem hasDerivAt_line {u : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ ξ : EuclideanSpace ℝ (Fin d)}
    {t : ℝ} (hu : DifferentiableAt ℝ u (x₀ + t • ξ)) :
    HasDerivAt (fun s => u (x₀ + s • ξ)) (fderiv ℝ u (x₀ + t • ξ) ξ) t := by
  have hline : HasDerivAt (fun s : ℝ => x₀ + s • ξ) ξ t := by
    have := ((hasDerivAt_id t).smul_const ξ).const_add x₀
    simpa using this
  exact hu.hasFDerivAt.comp_hasDerivAt t hline

/-- The second derivative along a line. -/
theorem hasDerivAt_line_fderiv {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ ξ : EuclideanSpace ℝ (Fin d)} {t : ℝ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) (x₀ + t • ξ)) :
    HasDerivAt (fun s => fderiv ℝ u (x₀ + s • ξ) ξ)
      (fderiv ℝ (fderiv ℝ u) (x₀ + t • ξ) ξ ξ) t := by
  have hline : HasDerivAt (fun s : ℝ => x₀ + s • ξ) ξ t := by
    have := ((hasDerivAt_id t).smul_const ξ).const_add x₀
    simpa using this
  have h := (hu.hasFDerivAt.clm_apply (hasFDerivAt_const ξ (x₀ + t • ξ))).comp_hasDerivAt t hline
  exact h.congr_deriv (by simp)

/-- **Hessian at an interior local maximum.** A `C²` function with a local maximum at `x₀`
has `D²u(x₀)(ξ, ξ) ≤ 0` for every direction `ξ`. -/
theorem sndFDeriv_nonpos_of_isLocalMax {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} (hu : ContDiffAt ℝ 2 u x₀) (hmax : IsLocalMax u x₀)
    (ξ : EuclideanSpace ℝ (Fin d)) : fderiv ℝ (fderiv ℝ u) x₀ ξ ξ ≤ 0 := by
  have hline : Continuous fun s : ℝ => x₀ + s • ξ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hline0 : Tendsto (fun s : ℝ => x₀ + s • ξ) (𝓝 0) (𝓝 x₀) := by
    have := hline.tendsto 0
    simpa using this
  -- `C²` near `x₀`, hence along the line near `0`
  have hev : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 2 u y := hu.eventually (by decide)
  have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 u (x₀ + s • ξ) := hline0.eventually hev
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s => u (x₀ + s • ξ)) (fderiv ℝ u (x₀ + s • ξ) ξ) s := by
    filter_upwards [hev'] with s hs
    exact hasDerivAt_line (hs.differentiableAt (by simp))
  have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s => fderiv ℝ u (x₀ + s • ξ) ξ)
      (fderiv ℝ (fderiv ℝ u) (x₀ + s • ξ) ξ ξ) s := by
    filter_upwards [hev'] with s hs
    exact hasDerivAt_line_fderiv ((hs.fderiv_right (m := 1) (by decide)).differentiableAt (by simp))
  have hc : ContinuousAt (fun s : ℝ => fderiv ℝ (fderiv ℝ u) (x₀ + s • ξ) ξ ξ) 0 := by
    have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ u)) x₀ :=
      ((hu.fderiv_right (m := 1) (by decide)).fderiv_right (m := 0) (by decide)).continuousAt
    have h : ContinuousAt (fun s : ℝ => fderiv ℝ (fderiv ℝ u) (x₀ + s • ξ)) 0 :=
      hcont.comp_of_eq hline.continuousAt (by simp)
    exact (h.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hmax' : IsLocalMax (fun s : ℝ => u (x₀ + s • ξ)) 0 := by
    have : IsLocalMax u ((fun s : ℝ => x₀ + s • ξ) 0) := by
      simp only [zero_smul, add_zero]
      exact hmax
    exact IsLocalMax.comp_continuous (g := fun s : ℝ => x₀ + s • ξ) (b := 0) this
      hline.continuousAt
  have := deriv2_nonpos_of_isLocalMax h1 h2 hc hmax'
  simpa using this

/-! ### The Hessian in coordinates -/

/-- The coordinate vectors. -/
abbrev e (i : Fin d) : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1

/-- A vector is the sum of its coordinates times the coordinate vectors. -/
theorem sum_coord_smul_e (ξ : EuclideanSpace ℝ (Fin d)) : ∑ i, ξ i • e i = ξ := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr ξ
  simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this

/-- **Second derivative in coordinates.** -/
theorem sndFDeriv_apply_eq_sum (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    L ξ ξ = ∑ i, ∑ j, ξ i * ξ j * L (e i) (e j) := by
  have h := sum_coord_smul_e ξ
  calc L ξ ξ = L (∑ i, ξ i • e i) (∑ j, ξ j • e j) := by rw [h]
    _ = ∑ i, ∑ j, ξ i * ξ j * L (e i) (e j) := by
        simp only [map_sum, map_smul, _root_.sum_apply,
          _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

/-- The partial derivative, unapplied. -/
theorem partialD_eq (i : Fin d) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    partialD i u = fun x => fderiv ℝ u x (e i) := rfl

/-- **Second partials as entries of the Hessian.** -/
theorem partialD_partialD_eq {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : Fin d) :
    partialD i (partialD j u) x = fderiv ℝ (fderiv ℝ u) x (e i) (e j) := by
  rw [partialD_eq i, partialD_eq j]
  simp only
  rw [fderiv_clm_apply hu (differentiableAt_const _)]
  simp

/-- **Nonpositivity of the coefficient-weighted Hessian at a local maximum.** -/
theorem sum_coeff_sndPartial_nonpos {a : Fin d → Fin d → ℝ} (hsymm : ∀ i j, a i j = a j i)
    (hpsd : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, a i j * ξ i * ξ j)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    (hu : ContDiffAt ℝ 2 u x₀) (hmax : IsLocalMax u x₀) :
    ∑ i, ∑ j, a i j * partialD i (partialD j u) x₀ ≤ 0 := by
  classical
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) x₀ :=
    (hu.fderiv_right (m := 1) (by decide)).differentiableAt (by simp)
  set H : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => fderiv ℝ (fderiv ℝ u) x₀ (e i) (e j)
    with hHdef
  set A : Matrix (Fin d) (Fin d) ℝ := Matrix.of a with hAdef
  have hsym2 : IsSymmSndFDerivAt ℝ u x₀ := hu.isSymmSndFDerivAt (by simp)
  have hA : A.PosSemidef := posSemidef_of_forall (fun i j => by simp [hAdef, hsymm i j]) fun ξ =>
    by simpa [hAdef] using hpsd ξ
  have hH : (-H).PosSemidef := by
    refine posSemidef_of_forall (fun i j => ?_) fun ξ => ?_
    · simp only [hHdef, Matrix.neg_apply, Matrix.of_apply]
      rw [hsym2.eq]
    · have hξ := sndFDeriv_nonpos_of_isLocalMax hu hmax (WithLp.toLp 2 ξ)
      rw [sndFDeriv_apply_eq_sum] at hξ
      have : ∑ i, ∑ j, (-H) i j * ξ i * ξ j
          = -∑ i, ∑ j, (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) i
            * (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) j
            * fderiv ℝ (fderiv ℝ u) x₀ (e i) (e j) := by
        simp only [hHdef, Matrix.neg_apply, Matrix.of_apply, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this]
      linarith
  have := sum_mul_nonpos_of_posSemidef hA hH
  simp only [hAdef, hHdef, Matrix.of_apply] at this
  calc ∑ i, ∑ j, a i j * partialD i (partialD j u) x₀
      = ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ u) x₀ (e i) (e j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [partialD_partialD_eq hdiff]
    _ ≤ 0 := this

/-! ### The operator -/

/-- **Non-divergence-form operator** `L u = -∑ aᵢⱼ ∂ᵢ∂ⱼ u + ∑ bᵢ ∂ᵢ u + c u`. -/
def nondivOp (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(∑ i, ∑ j, a x i j * partialD i (partialD j u) x) + ∑ i, b x i * partialD i u x + c x * u x

/-- **Operator at an interior local maximum.** The gradient vanishes and the
coefficient-weighted Hessian is nonpositive, so `L u ≥ c u` there. -/
theorem le_nondivOp_of_isLocalMax {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} (hsymm : ∀ i j, a x₀ i j = a x₀ j i)
    (hpsd : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, a x₀ i j * ξ i * ξ j)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffAt ℝ 2 u x₀) (hmax : IsLocalMax u x₀) :
    c x₀ * u x₀ ≤ nondivOp a b c u x₀ := by
  have hgrad : ∀ i, partialD i u x₀ = 0 := fun i => by
    simp only [partialD, hmax.fderiv_eq_zero, _root_.zero_apply]
  have hb : ∑ i, b x₀ i * partialD i u x₀ = 0 := by simp [hgrad]
  have hH := sum_coeff_sndPartial_nonpos hsymm hpsd hu hmax
  unfold nondivOp
  rw [hb]
  linarith

/-! ### The exponential perturbation -/

/-- The perturbation `exp (λ x_{i₀})`. -/
def expFn (lam : ℝ) (i₀ : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ := Real.exp (lam * x i₀)

/-- The perturbation is positive. -/
theorem expFn_pos (lam : ℝ) (i₀ : Fin d) (x : EuclideanSpace ℝ (Fin d)) : 0 < expFn lam i₀ x :=
  Real.exp_pos _

/-- The perturbation is smooth. -/
theorem contDiff_expFn (lam : ℝ) (i₀ : Fin d) : ContDiff ℝ 2 (expFn lam i₀) := by
  have h1 : ContDiff ℝ 2 fun x : EuclideanSpace ℝ (Fin d) => lam * x i₀ :=
    contDiff_const.mul (EuclideanSpace.proj i₀ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff
  exact Real.contDiff_exp.comp h1

/-- The derivative of the perturbation. -/
theorem hasFDerivAt_expFn (lam : ℝ) (i₀ : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (expFn lam i₀)
      (expFn lam i₀ x • (lam • (EuclideanSpace.proj i₀ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))) x := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => lam * y i₀)
      (lam • (EuclideanSpace.proj i₀ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x :=
    (EuclideanSpace.proj i₀ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt.const_mul lam
  exact (Real.hasDerivAt_exp (lam * x i₀)).comp_hasFDerivAt x h1

/-- The projection is the coordinate. -/
theorem proj_apply' (i : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) y = y i := rfl

/-- The first partials of the perturbation. -/
theorem partialD_expFn (lam : ℝ) (i₀ i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (expFn lam i₀) x = lam * (if i₀ = i then 1 else 0) * expFn lam i₀ x := by
  simp only [partialD, (hasFDerivAt_expFn lam i₀ x).fderiv, _root_.smul_apply,
    smul_eq_mul, proj_apply', PiLp.single_apply]
  ring

/-- The second partials of the perturbation. -/
theorem partialD_partialD_expFn (lam : ℝ) (i₀ i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (partialD j (expFn lam i₀)) x
      = lam * (if i₀ = j then 1 else 0) * (lam * (if i₀ = i then 1 else 0) * expFn lam i₀ x) := by
  have hfun : partialD j (expFn lam i₀)
      = fun y => (lam * (if i₀ = j then 1 else 0)) * expFn lam i₀ y := by
    funext y
    rw [partialD_expFn]
  rw [hfun]
  have hdiff : Differentiable ℝ (expFn lam i₀) := fun y =>
    (hasFDerivAt_expFn lam i₀ y).differentiableAt
  have := EllipticPdes.Sobolev.partialD_const_smul hdiff (lam * (if i₀ = j then 1 else 0)) i
  have h2 : (fun y => (lam * (if i₀ = j then 1 else 0)) * expFn lam i₀ y)
      = (lam * (if i₀ = j then 1 else 0)) • expFn lam i₀ := by
    funext y
    simp [smul_eq_mul]
  rw [h2, this, Pi.smul_apply, smul_eq_mul, partialD_expFn]

/-- **Operator on the perturbation.** -/
theorem nondivOp_expFn (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (lam : ℝ) (i₀ : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    nondivOp a b c (expFn lam i₀) x
      = (-(a x i₀ i₀ * lam ^ 2) + b x i₀ * lam + c x) * expFn lam i₀ x := by
  classical
  have hsum : ∑ i, ∑ j, a x i j * (lam * (if i₀ = j then 1 else 0)
      * (lam * (if i₀ = i then 1 else 0) * expFn lam i₀ x))
      = a x i₀ i₀ * lam ^ 2 * expFn lam i₀ x := by
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single i₀]
      · simp only [ite_true]
        ring
      · intro j _ hj
        simp [Ne.symm hj]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      simp [Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsum1 : ∑ i, b x i * (lam * (if i₀ = i then 1 else 0) * expFn lam i₀ x)
      = b x i₀ * lam * expFn lam i₀ x := by
    rw [Finset.sum_eq_single i₀]
    · simp only [ite_true]
      ring
    · intro i _ hi
      simp [Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold nondivOp
  simp only [partialD_partialD_expFn, partialD_expFn]
  rw [hsum, hsum1]
  ring

/-! ### Linearity of the operator at a point -/

/-- **Linearity of the operator** at a point of an open set on which both functions are `C²`. -/
theorem nondivOp_add_smul {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    nondivOp a b c (fun y => u y + ε * v y) x = nondivOp a b c u x + ε * nondivOp a b c v x := by
  classical
  -- differentiability of the pieces on the open set
  have hud : ∀ y ∈ U, DifferentiableAt ℝ u y := fun y hy =>
    (hu.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hvd : ∀ y ∈ U, DifferentiableAt ℝ v y := fun y hy =>
    (hv.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hud2 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ u) y := fun y hy =>
    ((hu.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by decide)).differentiableAt
      (by simp)
  have hvd2 : ∀ y ∈ U, DifferentiableAt ℝ (fderiv ℝ v) y := fun y hy =>
    ((hv.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by decide)).differentiableAt
      (by simp)
  -- first partials
  have h1 : ∀ i, ∀ y ∈ U, partialD i (fun y => u y + ε * v y) y
      = partialD i u y + ε * partialD i v y := by
    intro i y hy
    simp only [partialD]
    rw [fderiv_fun_add (hud y hy) ((hvd y hy).const_mul ε), fderiv_const_mul (hvd y hy) ε,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  -- second partials
  have h2 : ∀ i j, partialD i (partialD j (fun y => u y + ε * v y)) x
      = partialD i (partialD j u) x + ε * partialD i (partialD j v) x := by
    intro i j
    have hev : partialD j (fun y => u y + ε * v y)
        =ᶠ[𝓝 x] fun y => partialD j u y + ε * partialD j v y := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact h1 j y hy
    have hdu : DifferentiableAt ℝ (partialD j u) x := by
      rw [partialD_eq]
      exact (hud2 x hx).clm_apply (differentiableAt_const _)
    have hdv : DifferentiableAt ℝ (partialD j v) x := by
      rw [partialD_eq]
      exact (hvd2 x hx).clm_apply (differentiableAt_const _)
    simp only [partialD]
    rw [hev.fderiv_eq, fderiv_fun_add hdu (hdv.const_mul ε), fderiv_const_mul hdv ε,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hA : ∑ i, ∑ j, a x i j * (partialD i (partialD j u) x + ε * partialD i (partialD j v) x)
      = ∑ i, ∑ j, a x i j * partialD i (partialD j u) x
        + ε * ∑ i, ∑ j, a x i j * partialD i (partialD j v) x := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hB : ∑ i, b x i * (partialD i u x + ε * partialD i v x)
      = ∑ i, b x i * partialD i u x + ε * ∑ i, b x i * partialD i v x := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold nondivOp
  simp only [h2, h1 _ x hx]
  rw [hA, hB]
  ring

/-! ### The weak maximum principle -/

/-- A bounded nonempty set has nonempty frontier. -/
theorem frontier_nonempty_of_isBounded (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) : (frontier U).Nonempty := by
  obtain ⟨x₁, hx₁⟩ := hUne
  rw [Set.nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff]
  rintro (h | h)
  · exact (Set.nonempty_iff_ne_empty.mp ⟨x₁, hx₁⟩) h
  · obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    have hR0 : 0 ≤ R := (norm_nonneg x₁).trans (by simpa using hR hx₁)
    have hmem : (R + 1) • e (⟨0, hd⟩ : Fin d) ∈ U := by rw [h]; exact Set.mem_univ _
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, PiLp.norm_single,
      norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at this
    linarith

/-- **Weak maximum principle** (Evans §6.4.1 Theorem 1(i), Gilbarg and Trudinger Theorem 3.1,
Guo Theorem XI.3.7(i)). Let `U` be a bounded open nonempty set, `L` a non-divergence-form
operator with symmetric uniformly elliptic coefficients, bounded transport coefficients and no
zeroth-order term, and `u` a function `C²` on `U` and continuous on its closure with `L u ≤ 0`
on `U`. Then the maximum of `u` over the closure is attained on the boundary. -/
theorem weak_maximum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b (fun _ => 0) u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y := by
  classical
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  obtain ⟨x₁, hx₁⟩ := hUne
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb x₁ hx₁ i₀)
  -- the closure and the frontier are compact, the frontier nonempty
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  have hfr : IsCompact (frontier U) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfrne : (frontier U).Nonempty := frontier_nonempty_of_isBounded hd hUb ⟨x₁, hx₁⟩
  -- the maximum of `u` over the frontier
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn hfrne (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  -- the perturbation
  set lam : ℝ := (B + 1) / θ with hlam
  have hlam_pos : 0 < lam := div_pos (by linarith) hθ
  have hθlam : θ * lam = B + 1 := by rw [hlam]; field_simp
  set v : EuclideanSpace ℝ (Fin d) → ℝ := expFn lam i₀ with hvdef
  have hvpos : ∀ z, 0 < v z := expFn_pos lam i₀
  have hvc : Continuous v := (contDiff_expFn lam i₀).continuous
  obtain ⟨z₀, -, hz₀⟩ := hcl.exists_isMaxOn ⟨x, hx⟩ hvc.continuousOn
  set M : ℝ := v z₀ with hMdef
  have hMpos : 0 < M := hvpos z₀
  -- positive semidefiniteness and the diagonal lower bound from ellipticity
  have hpsd : ∀ z ∈ U, ∀ ξ : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, a z i j * ξ i * ξ j := fun z hz ξ =>
    (mul_nonneg hθ.le (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans (hell z hz ξ)
  have ha00 : ∀ z ∈ U, θ ≤ a z i₀ i₀ := by
    intro z hz
    have h := hell z hz (Pi.single i₀ (1 : ℝ) : Fin d → ℝ)
    have hs1 : ∑ i, ((Pi.single i₀ (1 : ℝ) : Fin d → ℝ) i) ^ 2 = 1 := by
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hs2 : ∑ i, ∑ j, a z i j * (Pi.single i₀ (1 : ℝ) : Fin d → ℝ) i
        * (Pi.single i₀ (1 : ℝ) : Fin d → ℝ) j = a z i₀ i₀ := by
      rw [Finset.sum_eq_single i₀]
      · rw [Finset.sum_eq_single i₀]
        · simp
        · intro j _ hj
          simp [hj]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hs1, hs2, mul_one] at h
    exact h
  -- the perturbed function is a strict subsolution
  have hstrict : ∀ ε > 0, ∀ z ∈ U,
      nondivOp a b (fun _ => 0) (fun w => u w + ε * v w) z < 0 := by
    intro ε hε z hz
    rw [nondivOp_add_smul hU hu (contDiff_expFn lam i₀).contDiffOn a b _ ε hz, nondivOp_expFn]
    have hb0 : b z i₀ ≤ B := (le_abs_self _).trans (hb z hz i₀)
    have h1 : θ * lam ^ 2 ≤ a z i₀ i₀ * lam ^ 2 :=
      mul_le_mul_of_nonneg_right (ha00 z hz) (sq_nonneg _)
    have hLv : -(a z i₀ i₀ * lam ^ 2) + b z i₀ * lam + 0 < 0 := by
      have h2 : b z i₀ * lam ≤ B * lam := mul_le_mul_of_nonneg_right hb0 hlam_pos.le
      have h3 : θ * lam ^ 2 = (B + 1) * lam := by rw [pow_two, ← mul_assoc, hθlam]
      nlinarith
    have hLu := hsub z hz
    have hv0 := expFn_pos lam i₀ z
    nlinarith [mul_pos hε hv0]
  -- for every `ε > 0` the maximum of `u + ε v` over the closure is on the frontier
  have hbound : ∀ ε > 0, u x ≤ u y + ε * M := by
    intro ε hε
    obtain ⟨z, hzcl, hzmax⟩ := hcl.exists_isMaxOn ⟨x, hx⟩
      (huc.add (continuousOn_const.mul hvc.continuousOn))
    have hzfr : z ∈ frontier U := by
      have hzcl' : z ∈ U ∪ frontier U := by
        rw [← closure_eq_self_union_frontier]
        exact hzcl
      rcases hzcl' with hzU | hzfr
      · exfalso
        have hloc : IsLocalMax (fun w => u w + ε * v w) z :=
          hzmax.isLocalMax (Filter.mem_of_superset (hU.mem_nhds hzU) subset_closure)
        have hC2 : ContDiffAt ℝ 2 (fun w => u w + ε * v w) z :=
          (hu.contDiffAt (hU.mem_nhds hzU)).add
            (contDiffAt_const.mul (contDiff_expFn lam i₀).contDiffAt)
        have h1 := le_nondivOp_of_isLocalMax (b := b) (c := fun _ => (0 : ℝ)) (hsymm z hzU)
          (hpsd z hzU) hC2 hloc
        have h2 := hstrict ε hε z hzU
        simp only [zero_mul] at h1
        linarith
      · exact hzfr
    calc u x ≤ u x + ε * v x := by nlinarith [hvpos x]
      _ ≤ u z + ε * v z := hzmax hx
      _ ≤ u y + ε * M := by
          have h1 : u z ≤ u y := hymax hzfr
          have h2 : v z ≤ M := hz₀ hzcl
          nlinarith
  -- let `ε` tend to zero
  refine le_of_forall_pos_le_add fun η hη => ?_
  have := hbound (η / M) (div_pos hη hMpos)
  rwa [div_mul_cancel₀ _ hMpos.ne'] at this

/-- The operator vanishes on the zero function. -/
theorem nondivOp_zero (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : nondivOp a b c (fun _ => (0 : ℝ)) x = 0 := by
  have h0 : ∀ i, partialD i (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) = fun _ => 0 :=
    fun i => EllipticPdes.Sobolev.partialD_zero i
  unfold nondivOp
  simp [h0]

/-- The operator on a constant. -/
theorem nondivOp_const (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : nondivOp a b c (fun _ => K) x = c x * K := by
  have h0 : ∀ (i : Fin d) (L : ℝ),
      partialD i (fun _ : EuclideanSpace ℝ (Fin d) => L) = fun _ => 0 := fun i L => by
      funext y
      simp [partialD]
  unfold nondivOp
  simp [h0]

/-- The operator on a function minus a constant. -/
theorem nondivOp_sub_const {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    nondivOp a b c (fun y => u y - K) x = nondivOp a b c u x - c x * K := by
  have h := nondivOp_add_smul hU hu (contDiffOn_const (c := (1 : ℝ))) a b c (-K) hx
  have e : (fun y => u y + (-K) * (1 : ℝ)) = fun y => u y - K := by
    funext y
    ring
  rw [e, nondivOp_const] at h
  rw [h]
  ring

/-- The operator on a difference. -/
theorem nondivOp_sub {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    nondivOp a b c (fun y => u y - v y) x = nondivOp a b c u x - nondivOp a b c v x := by
  have h := nondivOp_add_smul hU hu hv a b c (-1) hx
  have e : (fun y => u y + (-1) * v y) = fun y => u y - v y := by
    funext y
    ring
  rw [e] at h
  rw [h]
  ring

/-- Changing the zeroth-order coefficient changes the operator by the difference times the
function. -/
theorem nondivOp_congr_zeroth (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c c' : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    nondivOp a b c' u x = nondivOp a b c u x + (c' x - c x) * u x := by
  unfold nondivOp
  ring

/-- The operator on the negative. -/
theorem nondivOp_neg {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    nondivOp a b c (fun y => -u y) x = -nondivOp a b c u x := by
  have h := nondivOp_add_smul hU (contDiffOn_const (c := (0 : ℝ))) hu a b c (-1) hx
  have e : (fun y => (0 : ℝ) + (-1) * u y) = fun y => -u y := by
    funext y
    ring
  rw [e, nondivOp_zero] at h
  rw [h]
  ring

/-- **Weak maximum principle for supersolutions** (Evans §6.4.1 Theorem 1(ii)). A
supersolution attains its minimum over the closure on the boundary. -/
theorem weak_minimum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOp a b (fun _ => 0) u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u y ≤ u x := by
  have hneg : ∀ x ∈ U, nondivOp a b (fun _ => 0) (fun y => -u y) x ≤ 0 := fun x hx => by
    rw [nondivOp_neg hU hu a b _ hx]
    linarith [hsup x hx]
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle hd hU hUb hUne hθ hsymm hell hb hu.neg huc.neg hneg
  exact ⟨y, hy, fun x hx => by linarith [hmax x hx]⟩

/-- **Weak maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(i), Gilbarg and Trudinger Corollary 3.2, Guo Theorem XI.3.7(ii)). With `c ≥ 0`, a
subsolution is bounded on the closure by the maximum of its positive part over the boundary. -/
theorem weak_maximum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ max (u y) 0 := by
  classical
  -- `u` attains its maximum over the frontier
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  have hfr : IsCompact (frontier U) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (frontier_nonempty_of_isBounded hd hUb hUne)
    (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  -- the set where `u` is positive
  set V : Set (EuclideanSpace ℝ (Fin d)) := U ∩ u ⁻¹' Ioi 0 with hVdef
  have hVo : IsOpen V := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hVU : V ⊆ U := inter_subset_left
  -- an interior point outside `V` has `u ≤ 0`
  have hnotV : ∀ z ∈ U, z ∉ V → u z ≤ 0 := by
    intro z hzU hz
    by_contra hpos
    exact hz ⟨hzU, lt_of_not_ge hpos⟩
  -- on the closure of `V` the bound comes from the transport-free principle on `V`
  have hVbound : ∀ z ∈ closure V, u z ≤ max (u y) 0 := by
    rcases V.eq_empty_or_nonempty with hVe | hVne
    · intro z hz
      rw [hVe, closure_empty] at hz
      exact absurd hz (Set.notMem_empty z)
    · have hsubV : ∀ z ∈ V, nondivOp a b (fun _ => 0) u z ≤ 0 := by
        intro z hz
        have h1 : nondivOp a b (fun _ => (0 : ℝ)) u z = nondivOp a b c u z - c z * u z := by
          unfold nondivOp
          ring
        have h2 := hsub z (hVU hz)
        have hz2 : 0 < u z := hz.2
        have h3 : 0 ≤ c z * u z := mul_nonneg (hc z (hVU hz)) hz2.le
        linarith
      obtain ⟨y', hy'fr, hy'max⟩ := weak_maximum_principle hd hVo (hUb.subset hVU) hVne hθ
        (fun z hz => hsymm z (hVU hz)) (fun z hz => hell z (hVU hz)) (fun z hz => hb z (hVU hz))
        (hu.mono hVU) (huc.mono (closure_mono hVU)) hsubV
      have hy' : u y' ≤ max (u y) 0 := by
        have hy'cl : y' ∈ closure U := closure_mono hVU (frontier_subset_closure hy'fr)
        have hy'U : y' ∈ U ∪ frontier U := by
          rw [← closure_eq_self_union_frontier]
          exact hy'cl
        rcases hy'U with hy'U | hy'fr'
        · have hnot : y' ∉ V := by
            rw [← hVo.interior_eq]
            exact hy'fr.2
          exact (hnotV y' hy'U hnot).trans (le_max_right _ _)
        · exact (hymax hy'fr').trans (le_max_left _ _)
      intro z hz
      exact (hy'max z hz).trans hy'
  by_cases hxV : x ∈ closure V
  · exact hVbound x hxV
  · have hxU : x ∈ U ∪ frontier U := by
      rw [← closure_eq_self_union_frontier]
      exact hx
    rcases hxU with hxU | hxfr
    · exact (hnotV x hxU fun h => hxV (subset_closure h)).trans (le_max_right _ _)
    · exact (hymax hxfr).trans (le_max_left _ _)

/-! ### Corollaries -/

/-- **Strict maximum principle** (Guo Theorem XI.3.5). A strict subsolution, meaning
`L u < 0` at a point, has no local maximum at that point whenever `c u ≥ 0` there: in
particular when `c = 0`, when `c ≥ 0` and the maximum is nonnegative, and when the maximum is
zero. -/
theorem not_isLocalMax_of_nondivOp_neg {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} (hsymm : ∀ i j, a x₀ i j = a x₀ j i)
    (hpsd : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, a x₀ i j * ξ i * ξ j)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffAt ℝ 2 u x₀) (hcu : 0 ≤ c x₀ * u x₀)
    (hstrict : nondivOp a b c u x₀ < 0) : ¬ IsLocalMax u x₀ := fun hmax =>
  absurd (le_nondivOp_of_isLocalMax hsymm hpsd hu hmax) (not_le.mpr (hstrict.trans_le hcu))

/-- **Comparison principle** (Gilbarg and Trudinger Theorem 3.3, Guo Corollary XI.3.11). With
`c ≥ 0`, if `L u ≤ L v` on the set and `u ≤ v` on the boundary, then `u ≤ v` on the closure. -/
theorem comparison_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x)
    (hbd : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x := by
  have hsub : ∀ x ∈ U, nondivOp a b c (fun y => u y + (-1) * v y) x ≤ 0 := by
    intro x hx
    rw [nondivOp_add_smul hU hu hv a b c (-1) hx]
    linarith [hL x hx]
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle_of_nonneg hd hU hUb hUne hθ hsymm hell hb hc
    (hu.add (contDiffOn_const.mul hv)) (huc.add (continuousOn_const.mul hvc)) hsub
  intro x hx
  have h1 := hmax x hx
  have h2 : u y + (-1) * v y ≤ 0 := by linarith [hbd y hy]
  rw [max_eq_right h2] at h1
  linarith

/-- **Bound by the boundary values** (Gilbarg and Trudinger Corollary 3.2, second clause). With
`c ≥ 0`, a solution of `L u = 0` on a bounded open set is bounded in absolute value on the
closure by the maximum of `|u|` over the boundary. -/
theorem abs_le_of_nondivOp_eq_zero (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOp a b c u x = 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, |u x| ≤ |u y| := by
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  have hfr : IsCompact (frontier U) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (frontier_nonempty_of_isBounded hd hUb hUne)
    ((huc.mono frontier_subset_closure).abs)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  obtain ⟨y₁, hy₁, h₁⟩ := weak_maximum_principle_of_nonneg hd hU hUb hUne hθ hsymm hell hb hc hu
    huc fun z hz => (hsol z hz).le
  obtain ⟨y₂, hy₂, h₂⟩ := weak_maximum_principle_of_nonneg hd hU hUb hUne hθ hsymm hell hb hc
    hu.neg huc.neg fun z hz => by
      rw [nondivOp_neg hU hu a b c hz, hsol z hz, neg_zero]
  have hb₁ : u y₁ ≤ |u y| := (le_abs_self _).trans (hymax hy₁)
  have hb₂ : -u y₂ ≤ |u y| := (neg_le_abs _).trans (hymax hy₂)
  have hx₁ : u x ≤ |u y| := (h₁ x hx).trans (max_le hb₁ (abs_nonneg _))
  have hx₂ : -u x ≤ |u y| := (h₂ x hx).trans (max_le hb₂ (abs_nonneg _))
  exact abs_le.mpr ⟨by linarith, hx₁⟩

/-- **Weak minimum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(ii)). With `c ≥ 0`, a supersolution is bounded below on the closure by the minimum
of its negative part over the boundary. -/
theorem weak_minimum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOp a b c u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, min (u y) 0 ≤ u x := by
  have hneg : ∀ x ∈ U, nondivOp a b c (fun y => -u y) x ≤ 0 := fun x hx => by
    rw [nondivOp_neg hU hu a b c hx]
    linarith [hsup x hx]
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle_of_nonneg hd hU hUb hUne hθ hsymm hell hb hc
    hu.neg huc.neg hneg
  refine ⟨y, hy, fun x hx => ?_⟩
  have h := hmax x hx
  rcases le_or_gt (u y) 0 with h0 | h0
  · rw [min_eq_left h0]
    rw [max_eq_left (by linarith)] at h
    linarith
  · rw [min_eq_right h0.le]
    rw [max_eq_right (by linarith)] at h
    linarith

/-- **Uniqueness for the Dirichlet problem** (Guo Corollary XI.3.9). With `c ≥ 0`, two
functions with the same image under `L` on the set and the same boundary values agree on the
closure. -/
theorem dirichlet_unique (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x = nondivOp a b c v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := fun x hx =>
  le_antisymm
    (comparison_principle hd hU hUb hUne hθ hsymm hell hb hc hu hv huc hvc
      (fun x hx => (hL x hx).le) (fun x hx => (hbd x hx).le) x hx)
    (comparison_principle hd hU hUb hUne hθ hsymm hell hb hc hv hu hvc huc
      (fun x hx => (hL x hx).ge) (fun x hx => (hbd x hx).ge) x hx)

end EllipticPdes.Classical
