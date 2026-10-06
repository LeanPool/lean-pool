/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.MollifySlice
public import LeanPool.CIVAxisymmetric.Comparison.SliceBounds
public import LeanPool.CIVAxisymmetric.Statements.IsDistributionalDriftDiffusion

/-!
# The mollified equation of `lem:aniso:comparison`

Mollifying `eq:aniso:comparison:equation` in space turns a bounded distributional solution
into the pointwise-in-space identity `eq:aniso:comparison:mollified`,

`∂_τ q_ε + B·∇q_ε = Δ_X q_ε + R_ε`,

where `q_ε = η_ε * q` is the spatial mollification of `q` and `R_ε` is the commutator of
DiPerna and Lions. This module proves that identity in the form in which the distributional
hypothesis delivers it: for every scalar test function `χ` of time supported in `I`,

`∫ q_ε(x, τ) (-χ'(τ)) dτ = ∫ χ(τ) (Δ_X q_ε - ∇q_ε·B + R_ε)(x, τ) dτ`.

The proof tests the distributional equation with the product `φ(y, τ) = η_ε(x - y) χ(τ)`,
computes the three derivatives of `φ` in closed form, exchanges the order of integration,
and reassembles the drift and divergence contributions into the explicit integral form of
`diPernaLionsCommutator` by adding and subtracting `B(x, τ)·∇q_ε(x, τ)`.
-/

public section

open MeasureTheory Set
open CKN
open scoped Convolution

noncomputable section

namespace CIV

/-! ### Coordinates of a continuous linear form -/

/-- A continuous linear form on `Vec m` is determined by its values on the coordinate basis. -/
theorem apply_eq_sum_basisVec {m : ℕ} (L : Vec m →L[ℝ] ℝ) (v : Vec m) :
    L v = ∑ i, v i * L (basisVec i) := by
  conv_lhs => rw [← sum_smul_basisVec v]
  rw [map_sum]
  simp

/-! ### Smoothness of a directional derivative -/

/-- A directional derivative of a smooth function is smooth. -/
theorem contDiff_fderiv_apply {m : ℕ} {k : Vec m → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (v : Vec m) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec m => fderiv ℝ k w v) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ k) := hk.fderiv_right (by simp)
  have happ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousLinearMap.apply ℝ ℝ v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff
  exact happ.comp hfd

/-- A directional derivative of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_fderiv_apply {m : ℕ} {k : Vec m → ℝ} (hk : HasCompactSupport k)
    (v : Vec m) : HasCompactSupport (fun w : Vec m => fderiv ℝ k w v) := by
  have hfd : HasCompactSupport (fderiv ℝ k) := hk.fderiv ℝ
  have hzero : (fun L : Vec m →L[ℝ] ℝ => L v) 0 = 0 := rfl
  have hcomp : HasCompactSupport ((fun L : Vec m →L[ℝ] ℝ => L v) ∘ fderiv ℝ k) :=
    hfd.comp_left hzero
  exact hcomp

/-! ### The chain rule for the reflected kernel -/

/-- The derivative of `y ↦ k (x - y) c` in the direction `v`. -/
theorem fderiv_const_sub_mul_const {m : ℕ} {k : Vec m → ℝ} (hk : Differentiable ℝ k)
    (x : Vec m) (c : ℝ) (y v : Vec m) :
    fderiv ℝ (fun y' : Vec m => k (x - y') * c) y v = -(fderiv ℝ k (x - y) v) * c := by
  have hid : HasFDerivAt (fun y' : Vec m => x - y') (-ContinuousLinearMap.id ℝ (Vec m)) y :=
    (hasFDerivAt_id y).const_sub x
  have hk' : HasFDerivAt k (fderiv ℝ k (x - y)) (x - y) := (hk (x - y)).hasFDerivAt
  have hcomp : HasFDerivAt (fun y' : Vec m => k (x - y'))
      ((fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ (Vec m))) y := hk'.comp y hid
  have hmul := hcomp.mul_const c
  rw [hmul.fderiv]
  simp [mul_comm]

/-! ### The product test function -/

/-- The test function `φ(y, τ) = η_ε(x - y) χ(τ)` used to mollify the equation at `x`. -/
@[expose] def mollifierTest (m : ℕ) (ε : ℝ) (x : Vec m) (χ : ℝ → ℝ) (z : Vec m × ℝ) : ℝ :=
  mollifierKernel m ε (x - z.1) * χ z.2

theorem mollifierTest_apply {m : ℕ} (ε : ℝ) (x : Vec m) (χ : ℝ → ℝ) (y : Vec m) (τ : ℝ) :
    mollifierTest m ε x χ (y, τ) = mollifierKernel m ε (x - y) * χ τ := rfl

/-- The test function is smooth. -/
theorem contDiff_mollifierTest {m : ℕ} (ε : ℝ) (x : Vec m) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : ContDiff ℝ (⊤ : ℕ∞) (mollifierTest m ε x χ) := by
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec m × ℝ => x - z.1) :=
    contDiff_const.sub contDiff_fst
  have hker : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec m × ℝ => mollifierKernel m ε (x - z.1)) :=
    (contDiff_mollifierKernel ε).comp hsub
  have htime : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec m × ℝ => χ z.2) := hχ.comp contDiff_snd
  exact hker.mul htime

/-- The test function vanishes off a product of the closed `ε`-ball with the support of `χ`. -/
theorem mollifierTest_eq_zero {m : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec m) (χ : ℝ → ℝ)
    {z : Vec m × ℝ} (hz : z ∉ Metric.closedBall x ε ×ˢ tsupport χ) :
    mollifierTest m ε x χ z = 0 := by
  by_cases hτ : z.2 ∈ tsupport χ
  · have hx : z.1 ∉ Metric.closedBall x ε := fun h => hz ⟨h, hτ⟩
    have hgt : ε < ‖x - z.1‖ := by
      have h := (Metric.mem_closedBall.not).mp hx
      rw [not_le] at h
      rwa [dist_comm, dist_eq_norm] at h
    rw [mollifierTest, mollifierKernel_eq_zero hε (le_of_lt hgt), zero_mul]
  · rw [mollifierTest, image_eq_zero_of_notMem_tsupport hτ, mul_zero]

/-- The test function has compact support. -/
theorem hasCompactSupport_mollifierTest {m : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec m) {χ : ℝ → ℝ}
    (hχc : HasCompactSupport χ) : HasCompactSupport (mollifierTest m ε x χ) :=
  HasCompactSupport.intro ((isCompact_closedBall x ε).prod hχc)
    (fun _ hz => mollifierTest_eq_zero hε x χ hz)

/-- The support of the test function lies over the support of `χ`. -/
theorem tsupport_mollifierTest_subset {m : ℕ} (ε : ℝ) (x : Vec m) (χ : ℝ → ℝ) :
    tsupport (mollifierTest m ε x χ) ⊆ (univ : Set (Vec m)) ×ˢ tsupport χ := by
  have hs : Function.support (mollifierTest m ε x χ)
      ⊆ (univ : Set (Vec m)) ×ˢ Function.support χ := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    intro hcon
    exact hz (by rw [mollifierTest, hcon, mul_zero])
  have hcl := closure_mono hs
  rwa [closure_prod_eq, closure_univ] at hcl

/-- Stage (i): the product `η_ε(x - ·) χ` is a test function on `Vec m × I`. -/
theorem mollifierTest_mem_testFunctions {m : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec m) {I : Set ℝ}
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχI : tsupport χ ⊆ I) : mollifierTest m ε x χ ∈ testFunctions m I :=
  ⟨contDiff_mollifierTest ε x hχ, hasCompactSupport_mollifierTest hε x hχc,
    (tsupport_mollifierTest_subset ε x χ).trans fun _ hz => ⟨hz.1, hχI hz.2⟩⟩

/-! ### The second-order kernel -/

/-- The partial Laplacian, in the first `d` coordinates, of the kernel `η_ε`. -/
@[expose] def partialLaplacianKernel (m d : ℕ) (ε : ℝ) (w : Vec m) : ℝ :=
  ∑ i : Fin m, if (i : ℕ) < d then
    fderiv ℝ (fun w' : Vec m => fderiv ℝ (mollifierKernel m ε) w' (basisVec i)) w (basisVec i)
  else 0

theorem continuous_partialLaplacianKernel (m d : ℕ) (ε : ℝ) :
    Continuous (partialLaplacianKernel m d ε) := by
  have h : Continuous fun w : Vec m => ∑ i : Fin m, if (i : ℕ) < d then
      fderiv ℝ (fun w' : Vec m => fderiv ℝ (mollifierKernel m ε) w' (basisVec i)) w (basisVec i)
      else 0 := by
    refine continuous_finsetSum _ fun i _ => ?_
    by_cases hi : (i : ℕ) < d
    · simp only [hi, ite_true]
      exact (contDiff_fderiv_apply
        (contDiff_fderiv_apply (contDiff_mollifierKernel ε) (basisVec i)) (basisVec i)).continuous
    · simp only [hi, ite_false]
      exact continuous_const
  exact h

theorem hasCompactSupport_partialLaplacianKernel {m : ℕ} (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (partialLaplacianKernel m d ε) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec m) ε) fun w hw => ?_
  have hwmem : w ∈ {z : Vec m | ε < ‖z‖} := by
    by_contra hcon
    exact hw (by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hcon)
  have hopen : IsOpen {z : Vec m | ε < ‖z‖} := isOpen_lt continuous_const continuous_norm
  simp only [partialLaplacianKernel]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · have hev : (fun w' : Vec m => fderiv ℝ (mollifierKernel m ε) w' (basisVec i))
        =ᶠ[nhds w] fun _ : Vec m => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hwmem) fun _ hz =>
        fderiv_mollifierKernel_eq_zero hε hz (basisVec i)
    rw [hev.fderiv_eq]
    simp
  · rfl

/-! ### Stage (ii): the derivatives of the test function -/

/-- The time derivative of `φ(y, τ) = η_ε(x - y) χ(τ)`. -/
theorem timeDeriv_mollifierTest {m : ℕ} (ε : ℝ) (x : Vec m) {χ : ℝ → ℝ}
    (hχ : Differentiable ℝ χ) (y : Vec m) (τ : ℝ) :
    timeDeriv m (mollifierTest m ε x χ) (y, τ) = mollifierKernel m ε (x - y) * deriv χ τ := by
  have h : deriv (fun τ' : ℝ => mollifierKernel m ε (x - y) * χ τ') τ
      = mollifierKernel m ε (x - y) * deriv χ τ := deriv_const_mul _ (hχ τ)
  rw [timeDeriv]
  exact h

/-- The spatial gradient of `φ(y, τ) = η_ε(x - y) χ(τ)` paired with a vector. -/
theorem gradPair_mollifierTest {m : ℕ} (ε : ℝ) (x : Vec m) (χ : ℝ → ℝ) (y : Vec m) (τ : ℝ)
    (v : Vec m) :
    gradPair m (mollifierTest m ε x χ) (y, τ) v
      = -(fderiv ℝ (mollifierKernel m ε) (x - y) v) * χ τ := by
  rw [gradPair]
  exact fderiv_const_sub_mul_const (differentiable_mollifierKernel ε) x (χ τ) y v

/-- The first spatial derivative of `φ(y, τ) = η_ε(x - y) χ(τ)` as a function of the base
point, in the direction `v`. -/
theorem fderiv_slice_mollifierTest {m : ℕ} (ε : ℝ) (x : Vec m) (χ : ℝ → ℝ) (τ : ℝ)
    (v : Vec m) :
    (fun y : Vec m => fderiv ℝ (fun y' : Vec m => mollifierTest m ε x χ (y', τ)) y v)
      = fun y : Vec m => fderiv ℝ (mollifierKernel m ε) (x - y) v * (-(χ τ)) := by
  funext y
  have h : fderiv ℝ (fun y' : Vec m => mollifierKernel m ε (x - y') * χ τ) y v
      = -(fderiv ℝ (mollifierKernel m ε) (x - y) v) * χ τ :=
    fderiv_const_sub_mul_const (differentiable_mollifierKernel ε) x (χ τ) y v
  show fderiv ℝ (fun y' : Vec m => mollifierKernel m ε (x - y') * χ τ) y v = _
  rw [h]
  ring

/-- The partial Laplacian of `φ(y, τ) = η_ε(x - y) χ(τ)`. -/
theorem partialLaplacian_mollifierTest {m : ℕ} (d : ℕ) (ε : ℝ) (x : Vec m) (χ : ℝ → ℝ)
    (y : Vec m) (τ : ℝ) :
    partialLaplacian m d (mollifierTest m ε x χ) (y, τ)
      = partialLaplacianKernel m d ε (x - y) * χ τ := by
  rw [partialLaplacian, partialLaplacianKernel, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [fderiv_slice_mollifierTest ε x χ τ (basisVec i)]
    have hdiff : Differentiable ℝ
        (fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w (basisVec i)) :=
      (contDiff_fderiv_apply (contDiff_mollifierKernel ε) (basisVec i)).differentiable (by simp)
    have h := fderiv_const_sub_mul_const hdiff x (-(χ τ)) y (basisVec i)
    rw [h]
    ring
  · rw [zero_mul]

/-! ### Derivatives of an integral against a smooth compactly supported kernel -/

theorem mollifySlice_apply {m : ℕ} (ε : ℝ) (q : Vec m × ℝ → ℝ) (x : Vec m) (τ : ℝ) :
    mollifySlice m ε q (x, τ) = ∫ y, mollifierKernel m ε (x - y) * q (y, τ) := rfl


/-- Differentiating under the integral sign against a smooth compactly supported kernel. -/
theorem fderiv_kernelIntegral {m : ℕ} {k : Vec m → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hkc : HasCompactSupport k) {g : Vec m → ℝ} (hg : LocallyIntegrable g volume)
    (x v : Vec m) :
    fderiv ℝ (fun x' : Vec m => ∫ y, k (x' - y) * g y) x v = ∫ y, fderiv ℝ k (x - y) v * g y := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have heq : (fun x' : Vec m => ∫ y, k (x' - y) * g y)
      = (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ] k) := by
    funext x'
    simp [convolution_def, ContinuousLinearMap.lsmul_apply, mul_comm]
  have hfd : HasFDerivAt (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ] k)
      ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec m), volume] fderiv ℝ k) x) x :=
    hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hg hk1 x
  rw [heq, hfd.fderiv, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hg
    (hkc.fderiv ℝ) (hk1.continuous_fderiv one_ne_zero)]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]

/-- Integrability of a bounded measurable function against a continuous compactly supported
kernel. -/
theorem integrable_kernel_mul {m : ℕ} {k : Vec m → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) {g : Vec m → ℝ} {M : ℝ}
    (hmeas : AEStronglyMeasurable g volume) (hbdd : ∀ᵐ y ∂volume, |g y| ≤ M) (x : Vec m) :
    Integrable (fun y : Vec m => k (x - y) * g y) volume := by
  have hk_int : Integrable k volume := hk.integrable_of_hasCompactSupport hkc
  have hshift : Integrable (fun y : Vec m => k (x - y)) volume :=
    (integrable_comp_sub_left k x).mpr hk_int
  have hnorm : ∀ᵐ y ∂volume, ‖g y‖ ≤ M := by
    filter_upwards [hbdd] with y hy
    simpa [Real.norm_eq_abs] using hy
  exact hshift.mul_bdd hmeas (c := M) hnorm

/-- The spatial gradient of the mollified slice, obtained by moving `∇` onto the kernel. -/
theorem gradPair_mollifySlice {m : ℕ} {ε : ℝ} (hε : 0 < ε) (q : Vec m × ℝ → ℝ) (τ : ℝ) (M : ℝ)
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) (x v : Vec m) :
    gradPair m (mollifySlice m ε q) (x, τ) v
      = ∫ y, fderiv ℝ (mollifierKernel m ε) (x - y) v * q (y, τ) :=
  fderiv_mollifySlice hε τ q M hmeas hbdd x v

/-- The partial Laplacian of the mollified slice, obtained by moving `Δ_X` onto the kernel. -/
theorem partialLaplacian_mollifySlice {m : ℕ} (d : ℕ) {ε : ℝ} (hε : 0 < ε)
    (q : Vec m × ℝ → ℝ) (τ : ℝ) (M : ℝ)
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) (x : Vec m) :
    partialLaplacian m d (mollifySlice m ε q) (x, τ)
      = ∫ y, partialLaplacianKernel m d ε (x - y) * q (y, τ) := by
  have hloc : LocallyIntegrable (fun y => q (y, τ)) volume :=
    locallyIntegrable_of_bounded hmeas hbdd
  have hfirst : ∀ i : Fin m,
      (fun x' : Vec m => fderiv ℝ (fun y : Vec m => mollifySlice m ε q (y, τ)) x' (basisVec i))
        = fun x' : Vec m => ∫ y, fderiv ℝ (mollifierKernel m ε) (x' - y) (basisVec i)
            * q (y, τ) := by
    intro i
    funext x'
    exact fderiv_mollifySlice hε τ q M hmeas hbdd x' (basisVec i)
  have hsecond : ∀ i : Fin m,
      fderiv ℝ (fun x' : Vec m =>
          fderiv ℝ (fun y : Vec m => mollifySlice m ε q (y, τ)) x' (basisVec i)) x (basisVec i)
        = ∫ y, fderiv ℝ (fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w (basisVec i))
            (x - y) (basisVec i) * q (y, τ) := by
    intro i
    rw [hfirst i]
    exact fderiv_kernelIntegral (contDiff_fderiv_apply (contDiff_mollifierKernel ε) (basisVec i))
      (hasCompactSupport_fderiv_apply (hasCompactSupport_mollifierKernel hε) (basisVec i))
      hloc x (basisVec i)
  have hint : ∀ i : Fin m, Integrable (fun y : Vec m =>
      (if (i : ℕ) < d then
        fderiv ℝ (fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w (basisVec i)) (x - y)
          (basisVec i) else 0) * q (y, τ)) volume := by
    intro i
    by_cases hi : (i : ℕ) < d
    · simp only [hi, ite_true]
      refine integrable_kernel_mul (k := fun w : Vec m =>
        fderiv ℝ (fun w' : Vec m => fderiv ℝ (mollifierKernel m ε) w' (basisVec i)) w
          (basisVec i)) ?_ ?_ hmeas hbdd x
      · exact (contDiff_fderiv_apply
          (contDiff_fderiv_apply (contDiff_mollifierKernel ε) (basisVec i)) (basisVec i)).continuous
      · exact hasCompactSupport_fderiv_apply
          (hasCompactSupport_fderiv_apply (hasCompactSupport_mollifierKernel hε) (basisVec i))
          (basisVec i)
    · simp only [hi, ite_false, zero_mul]
      exact integrable_zero _ _ _
  have hswap : ∫ y, partialLaplacianKernel m d ε (x - y) * q (y, τ)
      = ∑ i : Fin m, ∫ y, (if (i : ℕ) < d then
          fderiv ℝ (fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w (basisVec i)) (x - y)
            (basisVec i) else 0) * q (y, τ) := by
    rw [← integral_finsetSum _ fun i _ => hint i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [partialLaplacianKernel, Finset.sum_mul]
  rw [hswap, partialLaplacian]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < d
  · simp only [hi, ite_true]
    exact hsecond i
  · simp only [hi, ite_false, zero_mul]
    exact (integral_zero _ _).symm

/-! ### The tested integrand vanishes off the support of the test function -/

/-- The time derivative of a test function vanishes off its support. -/
theorem timeDeriv_eq_zero_of_notMem_tsupport {m : ℕ} {φ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hz : z ∉ tsupport φ) : timeDeriv m φ z = 0 := by
  have hopen : IsOpen ((tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl
  have hcont : Continuous fun τ : ℝ => ((z.1, τ) : Vec m × ℝ) :=
    continuous_const.prodMk continuous_id
  have hU : IsOpen {τ : ℝ | (z.1, τ) ∈ (tsupport φ)ᶜ} := hopen.preimage hcont
  have hmem : z.2 ∈ {τ : ℝ | (z.1, τ) ∈ (tsupport φ)ᶜ} := hz
  have hev : (fun τ : ℝ => φ (z.1, τ)) =ᶠ[nhds z.2] fun _ : ℝ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hmem) fun _ hτ => image_eq_zero_of_notMem_tsupport hτ
  rw [timeDeriv, hev.fderiv_eq]
  simp

/-- The spatial gradient of a test function vanishes off its support. -/
theorem gradPair_eq_zero_of_notMem_tsupport {m : ℕ} {φ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hz : z ∉ tsupport φ) (v : Vec m) : gradPair m φ z v = 0 := by
  have hopen : IsOpen ((tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl
  have hcont : Continuous fun y : Vec m => ((y, z.2) : Vec m × ℝ) :=
    continuous_id.prodMk continuous_const
  have hU : IsOpen {y : Vec m | (y, z.2) ∈ (tsupport φ)ᶜ} := hopen.preimage hcont
  have hmem : z.1 ∈ {y : Vec m | (y, z.2) ∈ (tsupport φ)ᶜ} := hz
  have hev : (fun y : Vec m => φ (y, z.2)) =ᶠ[nhds z.1] fun _ : Vec m => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hmem) fun _ hy => image_eq_zero_of_notMem_tsupport hy
  rw [gradPair, hev.fderiv_eq]
  simp

/-- The partial Laplacian of a test function vanishes off its support. -/
theorem partialLaplacian_eq_zero_of_notMem_tsupport {m : ℕ} (d : ℕ) {φ : Vec m × ℝ → ℝ}
    {z : Vec m × ℝ} (hz : z ∉ tsupport φ) : partialLaplacian m d φ z = 0 := by
  have hopen : IsOpen ((tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl
  have hcont : Continuous fun y : Vec m => ((y, z.2) : Vec m × ℝ) :=
    continuous_id.prodMk continuous_const
  have hU : IsOpen {y : Vec m | (y, z.2) ∈ (tsupport φ)ᶜ} := hopen.preimage hcont
  have hmem : z.1 ∈ {y : Vec m | (y, z.2) ∈ (tsupport φ)ᶜ} := hz
  rw [partialLaplacian]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · have hev : (fun x' : Vec m => fderiv ℝ (fun y : Vec m => φ (y, z.2)) x' (basisVec i))
        =ᶠ[nhds z.1] fun _ : Vec m => (0 : ℝ) := by
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hmem) fun y hy => ?_
      exact gradPair_eq_zero_of_notMem_tsupport (z := (y, z.2)) hy (basisVec i)
    rw [hev.fderiv_eq]
    simp
  · rfl

/-- The integrand of `IsDistributionalDriftDiffusion` vanishes off the support of the test
function. -/
theorem testedIntegrand_eq_zero_of_notMem_tsupport {m : ℕ} (d : ℕ) (B : Vec m × ℝ → Vec m)
    (divB q φ : Vec m × ℝ → ℝ) {z : Vec m × ℝ} (hz : z ∉ tsupport φ) :
    q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z
      - partialLaplacian m d φ z) = 0 := by
  rw [timeDeriv_eq_zero_of_notMem_tsupport hz, gradPair_eq_zero_of_notMem_tsupport hz,
    partialLaplacian_eq_zero_of_notMem_tsupport d hz, image_eq_zero_of_notMem_tsupport hz]
  ring

/-! ### Stage (iii): the tested equation with the order of integration exchanged -/

/-- The integrand of `IsDistributionalDriftDiffusion` is integrable on all of `Vec m × ℝ`. -/
theorem integrable_testedIntegrand {m : ℕ} (d : ℕ) {I : Set ℝ} {B : Vec m × ℝ → Vec m}
    {divB q : Vec m × ℝ → ℝ} (heq : IsDistributionalDriftDiffusion m d I B divB q)
    {φ : Vec m × ℝ → ℝ} (hφ : φ ∈ testFunctions m I) :
    Integrable (fun z => q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z
      - partialLaplacian m d φ z)) volume := by
  have hon := (heq φ hφ).1
  have hms : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hind := (integrable_indicator_iff hms).mpr hon
  have hfun : (tsupport φ).indicator (fun z => q z * (-(timeDeriv m φ z)
      - gradPair m φ z (B z) - divB z * φ z - partialLaplacian m d φ z))
      = fun z => q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z
        - partialLaplacian m d φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz,
        testedIntegrand_eq_zero_of_notMem_tsupport d B divB q φ hz]
  rwa [hfun] at hind

/-- Stage (iii): the tested equation, with the space integral inside the time integral. -/
theorem integral_integral_testedIntegrand {m : ℕ} (d : ℕ) {I : Set ℝ} {B : Vec m × ℝ → Vec m}
    {divB q : Vec m × ℝ → ℝ} (heq : IsDistributionalDriftDiffusion m d I B divB q)
    {φ : Vec m × ℝ → ℝ} (hφ : φ ∈ testFunctions m I) :
    ∫ τ : ℝ, ∫ y : Vec m, q (y, τ) * (-(timeDeriv m φ (y, τ))
        - gradPair m φ (y, τ) (B (y, τ)) - divB (y, τ) * φ (y, τ)
        - partialLaplacian m d φ (y, τ)) = 0 := by
  have hint := integrable_testedIntegrand d heq hφ
  have hvol : (volume : Measure (Vec m × ℝ))
      = (volume : Measure (Vec m)).prod (volume : Measure ℝ) := Measure.volume_eq_prod _ _
  have hint' : Integrable (fun z : Vec m × ℝ => q z * (-(timeDeriv m φ z)
      - gradPair m φ z (B z) - divB z * φ z - partialLaplacian m d φ z))
      ((volume : Measure (Vec m)).prod (volume : Measure ℝ)) := by rwa [hvol] at hint
  have hswap := integral_prod_symm _ hint'
  rw [← hvol] at hswap
  rw [← hswap]
  exact (heq φ hφ).2

/-- Linearity of the integral over a sum of four integrable functions. -/
theorem integral_add_four {m : ℕ} {f₁ f₂ f₃ f₄ : Vec m → ℝ} (h₁ : Integrable f₁ volume)
    (h₂ : Integrable f₂ volume) (h₃ : Integrable f₃ volume) (h₄ : Integrable f₄ volume) :
    ∫ y : Vec m, (f₁ y + f₂ y + f₃ y + f₄ y)
      = (∫ y : Vec m, f₁ y) + (∫ y : Vec m, f₂ y) + (∫ y : Vec m, f₃ y)
        + ∫ y : Vec m, f₄ y := by
  have h₁₂ : Integrable (fun y : Vec m => f₁ y + f₂ y) volume := h₁.add h₂
  have h₁₂₃ : Integrable (fun y : Vec m => f₁ y + f₂ y + f₃ y) volume := h₁₂.add h₃
  rw [integral_add h₁₂₃ h₄, integral_add h₁₂ h₃, integral_add h₁ h₂]

/-! ### Stage (iv): one time slice of the tested equation -/

/-- On a time slice on which `q` is bounded and the drift obeys `eq:aniso:comparison:drift`,
the space integral of the tested integrand is the slice of the mollified equation: adding and
subtracting `B(x, τ)·∇q_ε(x, τ)` turns the drift and divergence contributions into the
explicit integral form of `diPernaLionsCommutator`. -/
theorem integral_slice_testedIntegrand {m : ℕ} (d : ℕ) {ε : ℝ} (hε : 0 < ε) (x : Vec m)
    {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ} {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    {τ M : ℝ} {Λ : NNReal}
    (hqm : AEStronglyMeasurable (fun y : Vec m => q (y, τ)) volume)
    (hqb : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M)
    (hBm : Measurable fun y : Vec m => B (y, τ))
    (hdm : Measurable fun y : Vec m => divB (y, τ))
    (hBb : ∀ y : Vec m, ‖B (y, τ)‖ ≤ (Λ : ℝ)) (hdb : ∀ y : Vec m, |divB (y, τ)| ≤ (Λ : ℝ)) :
    ∫ y : Vec m, q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
        - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
        - divB (y, τ) * mollifierTest m ε x χ (y, τ)
        - partialLaplacian m d (mollifierTest m ε x χ) (y, τ))
      = mollifySlice m ε q (x, τ) * (-(deriv χ τ))
        - χ τ * (partialLaplacian m d (mollifySlice m ε q) (x, τ)
            - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
            + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
                (fun y => q (y, τ)) x) := by
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := Λ.coe_nonneg
  have hBcoord : ∀ (y : Vec m) (i : Fin m), |B (y, τ) i| ≤ (Λ : ℝ) := by
    intro y i
    have h1 : |B (y, τ) i| ≤ ‖B (y, τ)‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (B (y, τ)) i
    exact h1.trans (hBb y)
  have hT1 : Integrable (fun y : Vec m => mollifierKernel m ε (x - y) * q (y, τ)) volume :=
    integrable_kernel_mul (contDiff_mollifierKernel ε).continuous
      (hasCompactSupport_mollifierKernel hε) hqm hqb x
  have hT3 : Integrable
      (fun y : Vec m => mollifierKernel m ε (x - y) * (divB (y, τ) * q (y, τ))) volume := by
    have hdqm : AEStronglyMeasurable (fun y : Vec m => divB (y, τ) * q (y, τ)) volume :=
      hdm.aestronglyMeasurable.mul hqm
    refine integrable_kernel_mul (M := (Λ : ℝ) * M) (contDiff_mollifierKernel ε).continuous
      (hasCompactSupport_mollifierKernel hε) hdqm ?_ x
    filter_upwards [hqb] with y hy
    rw [abs_mul]
    exact mul_le_mul (hdb y) hy (abs_nonneg _) hΛ
  have hT4 : Integrable
      (fun y : Vec m => partialLaplacianKernel m d ε (x - y) * q (y, τ)) volume :=
    integrable_kernel_mul (continuous_partialLaplacianKernel m d ε)
      (hasCompactSupport_partialLaplacianKernel d hε) hqm hqb x
  have hTi : ∀ i : Fin m, Integrable (fun y : Vec m =>
      q (y, τ) * (B (y, τ) i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))) volume := by
    intro i
    have hqBm : AEStronglyMeasurable (fun y : Vec m => q (y, τ) * B (y, τ) i) volume :=
      hqm.mul ((measurable_pi_apply i).comp hBm).aestronglyMeasurable
    have hbase : Integrable (fun y : Vec m =>
        fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
          * (q (y, τ) * B (y, τ) i)) volume := by
      refine integrable_kernel_mul (M := M * (Λ : ℝ))
        (k := fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w (basisVec i))
        (contDiff_fderiv_apply (contDiff_mollifierKernel ε) (basisVec i)).continuous
        (hasCompactSupport_fderiv_apply (hasCompactSupport_mollifierKernel hε) (basisVec i))
        hqBm ?_ x
      filter_upwards [hqb] with y hy
      rw [abs_mul]
      exact mul_le_mul hy (hBcoord y i) (abs_nonneg _) (le_trans (abs_nonneg _) hy)
    refine hbase.congr ?_
    filter_upwards with y
    ring
  have hTsum : Integrable (fun y : Vec m => q (y, τ) *
      ∑ i, B (y, τ) i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume := by
    have h := integrable_finsetSum (μ := (volume : Measure (Vec m))) Finset.univ
      fun i (_ : i ∈ Finset.univ) => hTi i
    refine h.congr ?_
    filter_upwards with y
    rw [Finset.mul_sum]
  have hTc : Integrable (fun y : Vec m =>
      fderiv ℝ (mollifierKernel m ε) (x - y) (B (x, τ)) * q (y, τ)) volume :=
    integrable_kernel_mul (k := fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w (B (x, τ)))
      (contDiff_fderiv_apply (contDiff_mollifierKernel ε) (B (x, τ))).continuous
      (hasCompactSupport_fderiv_apply (hasCompactSupport_mollifierKernel hε) (B (x, τ)))
      hqm hqb x
  have hL : ∀ y : Vec m, fderiv ℝ (mollifierKernel m ε) (x - y) (B (x, τ)) * q (y, τ)
      - q (y, τ) * ∑ i, B (y, τ) i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
      = q (y, τ) * ∑ i, (B (x, τ) i - B (y, τ) i)
          * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) := by
    intro y
    rw [apply_eq_sum_basisVec (fderiv ℝ (mollifierKernel m ε) (x - y)) (B (x, τ)),
      Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hTcomm : Integrable (fun y : Vec m => q (y, τ) *
      ∑ i, (B (x, τ) i - B (y, τ) i)
        * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume := by
    refine (hTc.sub hTsum).congr ?_
    filter_upwards with y
    exact hL y
  have hsplit : (∫ y : Vec m, q (y, τ) *
        ∑ i, B (y, τ) i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      + (∫ y : Vec m, q (y, τ) * ∑ i, (B (x, τ) i - B (y, τ) i)
          * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      = ∫ y : Vec m, fderiv ℝ (mollifierKernel m ε) (x - y) (B (x, τ)) * q (y, τ) := by
    rw [← integral_add hTsum hTcomm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have h := hL y
    linarith only [h]
  have hpt : ∀ y : Vec m, q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
      - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
      - divB (y, τ) * mollifierTest m ε x χ (y, τ)
      - partialLaplacian m d (mollifierTest m ε x χ) (y, τ))
      = mollifierKernel m ε (x - y) * q (y, τ) * (-(deriv χ τ))
        + χ τ * (q (y, τ) *
            ∑ i, B (y, τ) i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
        + (-(χ τ)) * (mollifierKernel m ε (x - y) * (divB (y, τ) * q (y, τ)))
        + (-(χ τ)) * (partialLaplacianKernel m d ε (x - y) * q (y, τ)) := by
    intro y
    rw [timeDeriv_mollifierTest ε x hχ, gradPair_mollifierTest ε x χ,
      partialLaplacian_mollifierTest d ε x χ, mollifierTest_apply,
      apply_eq_sum_basisVec (fderiv ℝ (mollifierKernel m ε) (x - y)) (B (y, τ))]
    ring
  have hi1 : Integrable (fun y : Vec m =>
      mollifierKernel m ε (x - y) * q (y, τ) * (-(deriv χ τ))) volume := hT1.mul_const _
  have hi2 : Integrable (fun y : Vec m => χ τ * (q (y, τ) *
      ∑ i, B (y, τ) i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))) volume :=
    hTsum.const_mul _
  have hi3 : Integrable (fun y : Vec m => (-(χ τ)) *
      (mollifierKernel m ε (x - y) * (divB (y, τ) * q (y, τ)))) volume := hT3.const_mul _
  have hi4 : Integrable (fun y : Vec m => (-(χ τ)) *
      (partialLaplacianKernel m d ε (x - y) * q (y, τ))) volume := hT4.const_mul _
  simp only [hpt]
  rw [integral_add_four hi1 hi2 hi3 hi4, integral_mul_const, integral_const_mul,
    integral_const_mul, integral_const_mul, mollifySlice_apply,
    partialLaplacian_mollifySlice d hε q τ M hqm hqb x,
    gradPair_mollifySlice hε q τ M hqm hqb x (B (x, τ))]
  simp only [diPernaLionsCommutator]
  linear_combination (χ τ) * hsplit

/-! ### Integrability of the mollified slice against a test function of time -/

/-- A function on `Vec m × ℝ` vanishing off `univ ×ˢ J` and integrable there is integrable. -/
theorem integrable_of_vanishing_outside {m : ℕ} {J : Set ℝ} (hJ : MeasurableSet J)
    {f : Vec m × ℝ → ℝ} (hzero : ∀ z : Vec m × ℝ, z.2 ∉ J → f z = 0)
    (hint : IntegrableOn f ((univ : Set (Vec m)) ×ˢ J) volume) : Integrable f volume := by
  have hms : MeasurableSet ((univ : Set (Vec m)) ×ˢ J) := MeasurableSet.univ.prod hJ
  have hind := (integrable_indicator_iff hms).mpr hint
  have hfun : ((univ : Set (Vec m)) ×ˢ J).indicator f = f := by
    funext z
    by_cases hz : z ∈ (univ : Set (Vec m)) ×ˢ J
    · rw [Set.indicator_of_mem hz]
    · have hz2 : z.2 ∉ J := fun hc => hz (Set.mem_prod.mpr ⟨mem_univ _, hc⟩)
      rw [Set.indicator_of_notMem hz, hzero z hz2]
  rwa [hfun] at hind

/-- A locally bounded function is integrable against a continuous compactly supported weight
whose support lies over `I`. -/
theorem integrable_mul_of_isLocallyBoundedOn {m : ℕ} {I : Set ℝ} {q : Vec m × ℝ → ℝ}
    (hq : IsLocallyBoundedOn m I q) {g : Vec m × ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgI : tsupport g ⊆ (univ : Set (Vec m)) ×ˢ I) :
    Integrable (fun z : Vec m × ℝ => g z * q z) volume := by
  have hJ : IsCompact (Prod.snd '' tsupport g) := IsCompact.image hgc continuous_snd
  have hJI : (Prod.snd '' tsupport g) ⊆ I := by
    rintro τ ⟨z, hz, rfl⟩
    exact (hgI hz).2
  have hJm : MeasurableSet (Prod.snd '' tsupport g) := hJ.isClosed.measurableSet
  obtain ⟨M, hM⟩ := hq.2 _ hJ hJI
  refine integrable_of_vanishing_outside hJm ?_ ?_
  · intro z hz
    have hzt : z ∉ tsupport g := fun hc => hz (Set.mem_image_of_mem Prod.snd hc)
    rw [image_eq_zero_of_notMem_tsupport hzt, zero_mul]
  · have hmaj : Integrable (fun z : Vec m × ℝ => |M| * ‖g z‖) volume :=
      ((hg.norm).integrable_of_hasCompactSupport hgc.norm).const_mul _
    have hsub : ((univ : Set (Vec m)) ×ˢ (Prod.snd '' tsupport g))
        ⊆ (univ : Set (Vec m)) ×ˢ I := fun z hz => ⟨hz.1, hJI hz.2⟩
    have hqJ : AEStronglyMeasurable q
        (volume.restrict ((univ : Set (Vec m)) ×ˢ (Prod.snd '' tsupport g))) :=
      hq.1.mono_measure (Measure.restrict_mono hsub le_rfl)
    refine Integrable.mono' hmaj.restrict (hg.aestronglyMeasurable.mul hqJ) ?_
    filter_upwards [hM] with z hz
    rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs (g z), mul_comm]
    refine mul_le_mul_of_nonneg_right (hz.trans (le_abs_self M)) (norm_nonneg _)

/-- The mollified slice is integrable in time against a test function of time. -/
theorem integrable_mollifySlice_mul {m : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec m) {I : Set ℝ}
    {q : Vec m × ℝ → ℝ} (hq : IsLocallyBoundedOn m I q) {c : ℝ → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c) (hcI : tsupport c ⊆ I) :
    Integrable (fun τ : ℝ => mollifySlice m ε q (x, τ) * c τ) volume := by
  have hψ : mollifierTest m ε x c ∈ testFunctions m I :=
    mollifierTest_mem_testFunctions hε x hc hcc hcI
  have hG : Integrable (fun z : Vec m × ℝ => mollifierTest m ε x c z * q z) volume :=
    integrable_mul_of_isLocallyBoundedOn hq hψ.1.continuous hψ.2.1 hψ.2.2
  have hvol : (volume : Measure (Vec m × ℝ))
      = (volume : Measure (Vec m)).prod (volume : Measure ℝ) := Measure.volume_eq_prod _ _
  have hG' : Integrable (fun z : Vec m × ℝ => mollifierTest m ε x c z * q z)
      ((volume : Measure (Vec m)).prod (volume : Measure ℝ)) := by rwa [hvol] at hG
  have hslice : Integrable
      (fun τ : ℝ => ∫ y : Vec m, mollifierTest m ε x c (y, τ) * q (y, τ)) volume :=
    hG'.integral_prod_right
  refine hslice.congr ?_
  filter_upwards with τ
  calc ∫ y : Vec m, mollifierTest m ε x c (y, τ) * q (y, τ)
      = ∫ y : Vec m, mollifierKernel m ε (x - y) * q (y, τ) * c τ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [mollifierTest_apply]
        ring
    _ = (∫ y : Vec m, mollifierKernel m ε (x - y) * q (y, τ)) * c τ := integral_mul_const _ _
    _ = mollifySlice m ε q (x, τ) * c τ := by rw [mollifySlice_apply]

/-! ### The mollified equation -/

/-- Step 2 of `lem:aniso:comparison`: the mollified equation
`eq:aniso:comparison:mollified`, tested against a smooth compactly supported function of time
supported in `I`. Here `q_ε = mollifySlice m ε q` and the commutator of DiPerna and Lions is
`diPernaLionsCommutator`. -/
theorem mollified_equation (m d : ℕ) (I : Set ℝ) (hI : IsOpen I)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (q : Vec m × ℝ → ℝ)
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε) (x : Vec m)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχI : tsupport χ ⊆ I) :
    ∫ τ, mollifySlice m ε q (x, τ) * (-(deriv χ τ))
      = ∫ τ, χ τ * (partialLaplacian m d (mollifySlice m ε q) (x, τ)
          - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
          + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
              (fun y => q (y, τ)) x) := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφ : mollifierTest m ε x χ ∈ testFunctions m I :=
    mollifierTest_mem_testFunctions hε x hχ hχc hχI
  have hJm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  obtain ⟨M, -, hMae⟩ := hq.ae_slice_bound hχc hχI
  obtain ⟨Λ, hΛae⟩ := hB.ae_slice hχc hχI
  have hBm : ∀ τ : ℝ, Measurable fun y : Vec m => B (y, τ) := fun τ =>
    hB.1.comp measurable_prodMk_right
  have hdm : ∀ τ : ℝ, Measurable fun y : Vec m => divB (y, τ) := fun τ =>
    hB.2.1.comp measurable_prodMk_right
  have hqmAll : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ I →
      AEStronglyMeasurable (fun y : Vec m => q (y, τ)) volume :=
    (ae_restrict_iff' hI.measurableSet).mp hq.ae_slice_measurable
  have hMall : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ tsupport χ → ∀ᵐ y : Vec m, |q (y, τ)| ≤ M :=
    (ae_restrict_iff' hJm).mp hMae
  have hΛall : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ tsupport χ →
      ((∀ y, ‖B (y, τ)‖ ≤ (Λ : ℝ)) ∧ LipschitzWith Λ (fun y => B (y, τ)) ∧
        (∀ y, |divB (y, τ)| ≤ (Λ : ℝ))) := (ae_restrict_iff' hJm).mp hΛae
  -- the slice identity, valid for almost every time
  have hgood : ∀ᵐ τ ∂(volume : Measure ℝ),
      (∫ y : Vec m, q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
          - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
          - divB (y, τ) * mollifierTest m ε x χ (y, τ)
          - partialLaplacian m d (mollifierTest m ε x χ) (y, τ)))
        = mollifySlice m ε q (x, τ) * (-(deriv χ τ))
          - χ τ * (partialLaplacian m d (mollifySlice m ε q) (x, τ)
              - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
              + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
                  (fun y => q (y, τ)) x) := by
    filter_upwards [hqmAll, hMall, hΛall] with τ h1 h2 h3
    by_cases hτ : τ ∈ tsupport χ
    · exact integral_slice_testedIntegrand d hε x hχd (h1 (hχI hτ)) (h2 hτ) (hBm τ) (hdm τ)
        (h3 hτ).1 (h3 hτ).2.2
    · have hχ0 : χ τ = 0 := image_eq_zero_of_notMem_tsupport hτ
      have hdχ0 : deriv χ τ = 0 := deriv_of_notMem_tsupport hτ
      have hz : ∀ y : Vec m, q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
          - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
          - divB (y, τ) * mollifierTest m ε x χ (y, τ)
          - partialLaplacian m d (mollifierTest m ε x χ) (y, τ)) = 0 := by
        intro y
        rw [timeDeriv_mollifierTest ε x hχd, gradPair_mollifierTest ε x χ,
          partialLaplacian_mollifierTest d ε x χ, mollifierTest_apply, hχ0, hdχ0]
        ring
      rw [integral_congr_ae (g := fun _ : Vec m => (0 : ℝ))
        (Filter.Eventually.of_forall hz), hχ0, hdχ0]
      simp
  -- the tested equation, with the order of integration exchanged
  have hzero := integral_integral_testedIntegrand d heq hφ
  -- integrability in time of the slice integral and of the two sides
  have hprod := integrable_testedIntegrand d heq hφ
  have hvol : (volume : Measure (Vec m × ℝ))
      = (volume : Measure (Vec m)).prod (volume : Measure ℝ) := Measure.volume_eq_prod _ _
  have hprod' : Integrable (fun z : Vec m × ℝ => q z *
      (-(timeDeriv m (mollifierTest m ε x χ) z)
        - gradPair m (mollifierTest m ε x χ) z (B z)
        - divB z * mollifierTest m ε x χ z
        - partialLaplacian m d (mollifierTest m ε x χ) z))
      ((volume : Measure (Vec m)).prod (volume : Measure ℝ)) := by rwa [hvol] at hprod
  have hAint : Integrable (fun τ : ℝ => ∫ y : Vec m,
      q (y, τ) * (-(timeDeriv m (mollifierTest m ε x χ) (y, τ))
        - gradPair m (mollifierTest m ε x χ) (y, τ) (B (y, τ))
        - divB (y, τ) * mollifierTest m ε x χ (y, τ)
        - partialLaplacian m d (mollifierTest m ε x χ) (y, τ))) volume :=
    hprod'.integral_prod_right
  have hdχc : HasCompactSupport (fun τ : ℝ => -(deriv χ τ)) := by
    have h : HasCompactSupport (-(deriv χ)) := (hχc.deriv).neg
    exact h
  have hdχI : tsupport (fun τ : ℝ => -(deriv χ τ)) ⊆ I := by
    have h : tsupport (-(deriv χ)) ⊆ I :=
      (tsupport_neg (deriv χ)) ▸ tsupport_deriv_subset.trans hχI
    exact h
  have hLint : Integrable (fun τ : ℝ => mollifySlice m ε q (x, τ) * (-(deriv χ τ))) volume :=
    integrable_mollifySlice_mul hε x hq (hχ.deriv'.neg) hdχc hdχI
  have hRint : Integrable (fun τ : ℝ => χ τ *
      (partialLaplacian m d (mollifySlice m ε q) (x, τ)
        - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
        + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
            (fun y => q (y, τ)) x)) volume := by
    refine (hLint.sub hAint).congr ?_
    filter_upwards [hgood] with τ hτ
    simp only [Pi.sub_apply]
    linarith only [hτ]
  have hstep : (∫ τ : ℝ, mollifySlice m ε q (x, τ) * (-(deriv χ τ)))
      - ∫ τ : ℝ, χ τ * (partialLaplacian m d (mollifySlice m ε q) (x, τ)
          - gradPair m (mollifySlice m ε q) (x, τ) (B (x, τ))
          + diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ))
              (fun y => q (y, τ)) x) = 0 := by
    rw [← integral_sub hLint hRint, ← hzero]
    refine integral_congr_ae ?_
    filter_upwards [hgood] with τ hτ
    exact hτ.symm
  linarith only [hstep]

end CIV
