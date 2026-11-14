/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderExcess
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ
public import Mathlib.Analysis.Convolution

/-!
# OneStepSchauderLapTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Laplacian dictionary and the mollification calculus (Weyl, part 1)

The competitor of the Schauder gradient-Hölder estimate is produced by
`ResidualCorrectorExistence` as an `H¹` function satisfying the **variational**
condition `Support.IsWeaklyHarmonicOn`; the interior Schauder estimate consumes
the **classical** object, Mathlib's `InnerProductSpace.HarmonicOnNhd`.  Bridging
the two is Weyl's lemma.  This module carries the two calculus halves of that
bridge:

* **the Laplacian dictionary** — `Δ (v ∘ toEuc.symm) (toEuc x) =
  euclideanCoordLaplacian v x` for `v ∈ C²`, and its packaging into
  `HarmonicOnNhd` on an open set / a sup-metric ball, through the
  orthonormal-basis formula for `Δ`;
* **the mollification calculus** — the coordinate Laplacian commutes with left
  convolution by a smooth compactly supported kernel, is invariant under the
  point reflection `y ↦ A - y`, and scales quadratically under an affine
  homothety `y ↦ a • y + b` (this last is what converts CoarseGraining's
  *convex* smoothing operator back into a plain convolution Laplacian).
-/

-- ==== Weyl: Laplacian transfer ====
open InnerProductSpace
open HCPolySupport (Vec basisVec euclideanBall euclideanCoordDeriv euclideanCoordSecondDeriv
  euclideanCoordLaplacian)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

open scoped Laplacian

/-! ### Basis vectors and `fderiv` across the identification -/

/-- **Chain rule for the pullback along `toEuc.symm`.**  No differentiability hypothesis is needed:
`toEuc.symm` is a continuous linear equivalence, and right-composition with such an equivalence
commutes with `fderiv` unconditionally. -/
theorem fderiv_comp_toEuc_symm (v : Vec d → ℝ) (z : 𝔼) :
    fderiv ℝ (v ∘ toEuc.symm) z
      = (fderiv ℝ v (toEuc.symm z)).comp ((toEuc.symm : 𝔼 ≃L[ℝ] Vec d) : 𝔼 →L[ℝ] Vec d) :=
  ContinuousLinearEquiv.comp_right_fderiv _

/-- The derivative of the pullback in a standard basis direction is the
CoarseGraining coordinate derivative. -/
theorem fderiv_comp_toEuc_symm_single (v : Vec d → ℝ) (z : 𝔼) (i : Fin d) :
    fderiv ℝ (v ∘ toEuc.symm) z (EuclideanSpace.single i (1 : ℝ))
      = euclideanCoordDeriv i v (toEuc.symm z) := by
  rw [fderiv_comp_toEuc_symm]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, toEuc_symm_single]
  rfl

/-- As a function identity: the standard-direction derivative of the pullback is
the pullback of the CoarseGraining coordinate derivative. -/
theorem fderiv_comp_toEuc_symm_single_eq (v : Vec d → ℝ) (i : Fin d) :
    (fun z : 𝔼 => fderiv ℝ (v ∘ toEuc.symm) z (EuclideanSpace.single i (1 : ℝ)))
      = (euclideanCoordDeriv i v) ∘ toEuc.symm := by
  funext z
  exact fderiv_comp_toEuc_symm_single v z i

/-! ### Second derivatives -/

/-- The second directional derivative of the pullback, in a standard basis
direction, is the CoarseGraining coordinate second derivative.  Unconditional. -/
theorem dirDeriv2_single_comp_toEuc_symm (v : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    dirDeriv2 (EuclideanSpace.single i (1 : ℝ)) (v ∘ toEuc.symm) (toEuc x)
      = euclideanCoordSecondDeriv i i v x := by
  rw [dirDeriv2, fderiv_comp_toEuc_symm_single_eq v i,
    fderiv_comp_toEuc_symm (euclideanCoordDeriv i v) (toEuc x)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, toEuc_symm_single,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-! ### The Laplacian dictionary -/

/-- **The Laplacian dictionary.**  For a `C²` function `v` on the CoarseGraining
coordinate carrier, mathlib's coordinate-free Laplacian of the pullback `v ∘
toEuc.symm` at `toEuc x` is the CoarseGraining coordinate Laplacian of `v` at
`x`.

Proof: read `Δ` in the orthonormal basis `EuclideanSpace.basisFun`, convert
each diagonal iterated derivative into a second directional derivative
(`iteratedFDeriv_two_eq_dirDeriv2`), and transfer each along `toEuc`
(`dirDeriv2_single_comp_toEuc_symm`). -/
theorem laplacian_comp_toEuc_symm_apply {v : Vec d → ℝ} (hv : ContDiff ℝ 2 v) (x : Vec d) :
    Δ (v ∘ toEuc.symm) (toEuc x) = euclideanCoordLaplacian v x := by
  classical
  have hcd : ContDiff ℝ 2 (v ∘ toEuc.symm) :=
    hv.comp (toEuc.symm : 𝔼 ≃L[ℝ] Vec d).contDiff
  have hbasis :=
    congrFun
      (laplacian_eq_iteratedFDeriv_orthonormalBasis (v ∘ toEuc.symm)
        (EuclideanSpace.basisFun (Fin d) ℝ))
      (toEuc x)
  rw [hbasis]
  simp only [EuclideanSpace.basisFun_apply, euclideanCoordLaplacian]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_eq_dirDeriv2 hcd, dirDeriv2_single_comp_toEuc_symm]

/-- Pointwise form: the coordinate Laplacian of `v` at `toEuc.symm z`. -/
theorem euclideanCoordLaplacian_eq_laplacian_comp_toEuc_symm {v : Vec d → ℝ}
    (hv : ContDiff ℝ 2 v) (z : 𝔼) :
    euclideanCoordLaplacian v (toEuc.symm z) = Δ (v ∘ toEuc.symm) z := by
  have h := laplacian_comp_toEuc_symm_apply hv (toEuc.symm z)
  rwa [ContinuousLinearEquiv.apply_symm_apply, eq_comm] at h

/-! ### Packaging as mathlib harmonicity -/

/-- **From a vanishing coordinate Laplacian to mathlib harmonicity.**  If `v` is
`C²` on the CoarseGraining coordinate carrier and its coordinate Laplacian
vanishes on an *open* set `S`, then the pullback `v ∘ toEuc.symm` is
`HarmonicOnNhd` on the preimage of `S`. -/
theorem harmonicOnNhd_comp_toEuc_symm {v : Vec d → ℝ} (hv : ContDiff ℝ 2 v)
    {S : Set (Vec d)} (hS : IsOpen S) (hzero : ∀ y ∈ S, euclideanCoordLaplacian v y = 0) :
    HarmonicOnNhd (v ∘ toEuc.symm) (toEuc.symm ⁻¹' S) := by
  have hcd : ContDiff ℝ 2 (v ∘ toEuc.symm) :=
    hv.comp (toEuc.symm : 𝔼 ≃L[ℝ] Vec d).contDiff
  have hopen : IsOpen (toEuc.symm ⁻¹' S) :=
    hS.preimage (toEuc.symm : 𝔼 ≃L[ℝ] Vec d).continuous
  intro z hz
  refine ⟨hcd.contDiffAt, ?_⟩
  filter_upwards [hopen.mem_nhds hz] with w hw
  rw [Pi.zero_apply, ← euclideanCoordLaplacian_eq_laplacian_comp_toEuc_symm hv w]
  exact hzero _ hw

/-- **Sup-metric ball version.**  A vanishing coordinate Laplacian on the product-metric ball
`Metric.ball x r ⊆ Vec d` gives mathlib harmonicity of the pullback on the *Euclidean* ball
`Metric.ball (toEuc x) r ⊆ EuclideanSpace ℝ (Fin d)` of the same radius.

There is no loss of radius: the `L²` norm dominates the sup norm on the same data, so the Euclidean
ball is contained in the preimage of the sup ball (`Homogenization.euclideanBall_subset_metricBall`
via the ball dictionary `mem_euclideanBall_toEuc_iff`). -/
theorem harmonicOnNhd_ball_comp_toEuc_symm {v : Vec d → ℝ} (hv : ContDiff ℝ 2 v)
    {x : Vec d} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y ∈ Metric.ball x r, euclideanCoordLaplacian v y = 0) :
    HarmonicOnNhd (v ∘ toEuc.symm) (Metric.ball (toEuc x) r) := by
  refine (harmonicOnNhd_comp_toEuc_symm hv Metric.isOpen_ball hzero).mono ?_
  intro z hz
  have hz' : (toEuc (toEuc.symm z) : 𝔼) ∈ Metric.ball (toEuc x) r := by
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hzE : toEuc.symm z ∈ euclideanBall x r :=
    (mem_euclideanBall_toEuc_iff _ _ hr).mp hz'
  exact HCPolySupport.euclideanBall_subset_metricBall hr hzE

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== Weyl: the convolution Laplacian ====
open scoped Convolution
open HCPolySupport (Vec basisVec euclideanCoordDeriv euclideanCoordSecondDeriv
  euclideanCoordLaplacian)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open scoped Laplacian

noncomputable section

variable {d : ℕ}

/-! ### Convolution commutes with coordinate differentiation -/

/-- **Coordinate differentiation commutes with left convolution** by a smooth compactly supported
kernel. -/
theorem euclideanCoordDeriv_convolution_left {K g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) (i : Fin d) :
    euclideanCoordDeriv i (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) =
      (euclideanCoordDeriv i K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) := by
  funext x
  unfold HCPolySupport.euclideanCoordDeriv
  have hderiv :
      fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) x =
        ((fderiv ℝ K ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d),
          MeasureTheory.volume] g) x) :=
    (hK_supp.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := MeasureTheory.volume) (hf := hK.of_le (by norm_num)) hg x).fderiv
  rw [hderiv]
  calc
    ((fderiv ℝ K ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d),
          MeasureTheory.volume] g) x) (basisVec i)
        = ((g ⋆[((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)).flip,
            MeasureTheory.volume] fderiv ℝ K) x) (basisVec i) := by
          rw [MeasureTheory.convolution_flip]
    _ = ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip.precompR (Vec d),
            MeasureTheory.volume] fderiv ℝ K) x) (basisVec i) := rfl
    _ = (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, MeasureTheory.volume]
            (fun y => (fderiv ℝ K y) (basisVec i))) x :=
          MeasureTheory.convolution_precompR_apply
            (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (f := g) (g := fderiv ℝ K)
            (μ := MeasureTheory.volume) hg (hK_supp.fderiv ℝ)
            (hK.continuous_fderiv (by norm_num)) x (basisVec i)
    _ = ((fun y => (fderiv ℝ K y) (basisVec i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
            MeasureTheory.volume] g) x := by
          rw [MeasureTheory.convolution_flip]

/-- Coordinate second derivatives commute with left convolution by a smooth compact kernel. -/
theorem euclideanCoordSecondDeriv_convolution_left {K g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) (i j : Fin d) :
    euclideanCoordSecondDeriv i j
        (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) =
      (euclideanCoordSecondDeriv i j K ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        MeasureTheory.volume] g) := by
  unfold HCPolySupport.euclideanCoordSecondDeriv
  rw [euclideanCoordDeriv_convolution_left hK_supp hK hg i]
  exact euclideanCoordDeriv_convolution_left
    (HCPolySupport.hasCompactSupport_euclideanCoordDeriv hK_supp i)
    (HCPolySupport.contDiff_euclideanCoordDeriv hK i) hg j

/-- **The coordinate Laplacian commutes with left convolution** by a smooth compactly supported
kernel: `Δ (K ⋆ g) = (Δ K) ⋆ g`. -/
theorem euclideanCoordLaplacian_convolution_left {K g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) :
    euclideanCoordLaplacian (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) =
      (euclideanCoordLaplacian K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g) := by
  funext x
  unfold HCPolySupport.euclideanCoordLaplacian
  simp_rw [euclideanCoordSecondDeriv_convolution_left hK_supp hK hg]
  simp_rw [MeasureTheory.convolution_def]
  symm
  have hterm : ∀ i : Fin d,
      MeasureTheory.Integrable
        (fun t : Vec d =>
          ContinuousLinearMap.lsmul ℝ ℝ (euclideanCoordSecondDeriv i i K t) (g (x - t)))
        MeasureTheory.volume := by
    intro i
    have h :=
      ((HCPolySupport.hasCompactSupport_euclideanCoordSecondDeriv hK_supp i
            i).convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (hf := (HCPolySupport.contDiff_euclideanCoordSecondDeriv hK i i).continuous)
        (hg := hg) x).integrable
    simpa using h
  calc
    ∫ t : Vec d, ContinuousLinearMap.lsmul ℝ ℝ
          (∑ i, euclideanCoordSecondDeriv i i K t) (g (x - t)) ∂MeasureTheory.volume
        = ∫ t : Vec d, ∑ i : Fin d,
            ContinuousLinearMap.lsmul ℝ ℝ (euclideanCoordSecondDeriv i i K t) (g (x - t))
              ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          simp
    _ = ∑ i : Fin d, ∫ t : Vec d,
            ContinuousLinearMap.lsmul ℝ ℝ (euclideanCoordSecondDeriv i i K t) (g (x - t))
              ∂MeasureTheory.volume :=
          MeasureTheory.integral_finsetSum Finset.univ fun i _ => hterm i

/-! ### Behaviour under the point reflection `y ↦ A - y` -/

/-- Coordinate derivative after precomposition with the point reflection `y ↦ A - y`. -/
theorem euclideanCoordDeriv_comp_const_sub {K : Vec d → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (A : Vec d) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => K (A - y)) x = -euclideanCoordDeriv i K (A - x) := by
  unfold HCPolySupport.euclideanCoordDeriv
  have hcomp :
      fderiv ℝ (fun y : Vec d => K (A - y)) x =
        (fderiv ℝ K (A - x)).comp (-(1 : Vec d →L[ℝ] Vec d)) := by
    change fderiv ℝ (K ∘ fun y : Vec d => A - y) x =
      (fderiv ℝ K (A - x)).comp (-(1 : Vec d →L[ℝ] Vec d))
    rw [fderiv_comp]
    · have harg : fderiv ℝ (fun y : Vec d => A - y) x = -(1 : Vec d →L[ℝ] Vec d) := by
        simpa using! (fderiv_const_sub (𝕜 := ℝ) (f := fun y : Vec d => y) (x := x) A)
      rw [harg]
    · exact (hK.differentiable (by simp)) (A - x)
    · fun_prop
  rw [hcomp]
  simp

/-- **The coordinate Laplacian is invariant under the point reflection** `y ↦ A - y`. -/
theorem euclideanCoordLaplacian_comp_const_sub {K : Vec d → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (A : Vec d) (x : Vec d) :
    euclideanCoordLaplacian (fun y => K (A - y)) x = euclideanCoordLaplacian K (A - x) := by
  unfold HCPolySupport.euclideanCoordLaplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold HCPolySupport.euclideanCoordSecondDeriv
  have hfirst :
      euclideanCoordDeriv i (fun y : Vec d => K (A - y)) =
        fun y => -euclideanCoordDeriv i K (A - y) := by
    funext y
    exact euclideanCoordDeriv_comp_const_sub hK A i y
  rw [hfirst]
  have hD : ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i K) :=
    HCPolySupport.contDiff_euclideanCoordDeriv hK i
  have href := euclideanCoordDeriv_comp_const_sub hD A i x
  calc
    (fderiv ℝ (fun y : Vec d => -euclideanCoordDeriv i K (A - y)) x) (basisVec i)
        = (-(fderiv ℝ (fun y : Vec d => euclideanCoordDeriv i K (A - y)) x)) (basisVec i) := by
          rw [fderiv_fun_neg]
    _ = -(fderiv ℝ (fun y : Vec d => euclideanCoordDeriv i K (A - y)) x) (basisVec i) := by simp
    _ = -euclideanCoordDeriv i (fun y : Vec d => euclideanCoordDeriv i K (A - y)) x := rfl
    _ = -(-euclideanCoordDeriv i (euclideanCoordDeriv i K) (A - x)) := by rw [href]
    _ = (fderiv ℝ (euclideanCoordDeriv i K) (A - x)) (basisVec i) := by
          simp [HCPolySupport.euclideanCoordDeriv]

/-! ### Behaviour under the affine homothety `y ↦ a • y + b` -/

/-! ### Reflecting a convolution integral onto the domain -/

/-- **Change of variables by the point reflection** `t ↦ A - t`, converting a global indicator
integral into a set integral over `U`.  This is what turns the value of a convolution against the
zero-extension `1_U u` into a test-function pairing on `U`. -/
theorem integral_mul_indicator_const_sub_eq_setIntegral {U : Set (Vec d)} (hU : MeasurableSet U)
    (A : Vec d) (f u : Vec d → ℝ) :
    ∫ t : Vec d, f t * Set.indicator U u (A - t) ∂MeasureTheory.volume =
      ∫ y in U, u y * f (A - y) ∂MeasureTheory.volume := by
  classical
  let e : Homeomorph (Vec d) (Vec d) := (Homeomorph.neg (Vec d)).trans (Homeomorph.addRight A)
  have heq : (fun y : Vec d => e y) = fun y => A - y := by
    funext y
    simp [e, sub_eq_add_neg, add_comm]
  have hmp_e :
      MeasureTheory.MeasurePreserving e
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume := by
    have hneg :
        MeasureTheory.MeasurePreserving (fun y : Vec d => -y)
          (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
      MeasureTheory.Measure.measurePreserving_neg _
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : Vec d => y + A)
          (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
      MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) A
    simpa [e] using! hadd.comp hneg
  have hcv :
      ∫ y : Vec d, (fun t : Vec d => f t * Set.indicator U u (A - t)) (e y)
          ∂MeasureTheory.volume =
        ∫ t : Vec d, f t * Set.indicator U u (A - t) ∂MeasureTheory.volume :=
    hmp_e.integral_comp e.measurableEmbedding
      (fun t : Vec d => f t * Set.indicator U u (A - t))
  calc
    ∫ t : Vec d, f t * Set.indicator U u (A - t) ∂MeasureTheory.volume
        = ∫ y : Vec d, f (A - y) * Set.indicator U u y ∂MeasureTheory.volume := by
          rw [← hcv]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          simp [heq, sub_sub_cancel]
    _ = ∫ y : Vec d, Set.indicator U (fun y : Vec d => f (A - y) * u y) y
          ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          by_cases hy : y ∈ U
          · simp [hy]
          · simp [hy]
    _ = ∫ y in U, f (A - y) * u y ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_indicator hU]
    _ = ∫ y in U, u y * f (A - y) ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun hU fun y _ => ?_
          ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

