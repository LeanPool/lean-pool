/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Physical weak divergence of Fourier multiplier ranges

The frequency orthogonality in `lem:reg-multiplier-bounds` implies the
physical weak-divergence identity by Plancherel.
-/

public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform LineDeriv SchwartzMap ComplexInnerProductSpace
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The canonical continuous linear equivalence between coordinate triples and the Hilbert `L²`
vector. -/
@[expose]
def l2Vec3Equiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- The coordinate representative on Vec3 of a real spatial `L²` field. -/
@[expose]
def realVectorL2Representative (f : RealVectorL2) : Vec3 → Vec3 :=
  fun x => l2Vec3Equiv (f (WithLp.toLp 2 x))

/-- The Hilbert-space representative of the `i`th standard basis vector. -/
@[expose]
def l2BasisVec (i : Fin 3) : L2Vec3 :=
  WithLp.toLp 2 (CKN.basisVec i)

private theorem l2BasisVec_norm (i : Fin 3) : ‖l2BasisVec i‖ = 1 := by
  simp [l2BasisVec, CKN.basisVec]

/-- The complex-linear gradient vector associated to a continuous linear covector on Hilbert
vectors. -/
@[expose]
def gradientOfCovectorLinear :
    (L2Vec3 →L[ℝ] ℂ) →ₗ[ℂ] ComplexVec3 where
  toFun D := WithLp.toLp 2 (fun i => D (l2BasisVec i))
  map_add' D E := by
    apply PiLp.ext
    intro i
    simp
  map_smul' c D := by
    apply PiLp.ext
    intro i
    simp

theorem gradientOfCovectorLinear_norm_bound (D : L2Vec3 →L[ℝ] ℂ) :
    ‖gradientOfCovectorLinear D‖ ≤ 2 * ‖D‖ := by
  have hcoord (i : Fin 3) : ‖D (l2BasisVec i)‖ ≤ ‖D‖ := by
    calc
      ‖D (l2BasisVec i)‖ ≤ ‖D‖ * ‖l2BasisVec i‖ := D.le_opNorm _
      _ = ‖D‖ := by rw [l2BasisVec_norm]; ring
  have hsq : ‖gradientOfCovectorLinear D‖ ^ 2 ≤ (2 * ‖D‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      (∑ i : Fin 3, ‖D (l2BasisVec i)‖ ^ 2) ≤
          ∑ i : Fin 3, ‖D‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            nlinarith only [hcoord i, norm_nonneg (D (l2BasisVec i)), norm_nonneg D]
      _ = 3 * ‖D‖ ^ 2 := by simp
      _ ≤ (2 * ‖D‖) ^ 2 := by nlinarith only [sq_nonneg ‖D‖]
  have hnonneg : 0 ≤ ‖gradientOfCovectorLinear D‖ := norm_nonneg _
  have htarget : 0 ≤ 2 * ‖D‖ := by positivity
  nlinarith only [hsq, hnonneg, htarget]

/-- The bounded gradient vector associated to a continuous linear covector. -/
@[expose]
def gradientOfCovector :
    (L2Vec3 →L[ℝ] ℂ) →L[ℂ] ComplexVec3 :=
  gradientOfCovectorLinear.mkContinuous 2 (by
    intro D
    exact gradientOfCovectorLinear_norm_bound D)

/-- The Fourier transform commutes with bounded complex linear postcomposition. -/
theorem fourier_postcompCLM
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : F →L[ℂ] G) (f : SchwartzMap L2Vec3 F) :
    𝓕 (f.postcompCLM L) = (𝓕 f).postcompCLM L := by
  ext ξ
  change 𝓕 (fun x : L2Vec3 => L (f x)) ξ =
    L (𝓕 (f : L2Vec3 → F) ξ)
  rw [Real.fourier_eq]
  rw [Real.fourier_eq]
  calc
    (∫ v : L2Vec3, 𝐞 (-inner ℝ v ξ) • L (f v)) =
        ∫ v : L2Vec3, L (𝐞 (-inner ℝ v ξ) • f v) := by
          apply integral_congr_ae
          filter_upwards [] with v
          simp
    _ = L (∫ v : L2Vec3, 𝐞 (-inner ℝ v ξ) • f v) :=
      L.integral_comp_comm (by simpa using f.integrable)

private theorem inner_l2BasisVec (ξ : L2Vec3) (i : Fin 3) :
    inner ℝ ξ (l2BasisVec i) = ξ i := by
  rw [PiLp.inner_apply]
  simp [l2BasisVec, CKN.basisVec]

/-- The Schwartz representative of a compactly supported smooth weak test function. -/
@[expose]
def weakTestSourceSchwartz
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) : SchwartzMap Vec3 ℝ :=
  ψ.hasCompactSupport.toSchwartzMap ψ.contDiff

/-- The Schwartz-map encoding of a scalar weak test function. -/
@[expose]
def weakTestSchwartz {ψ : WeakTestFunction (Set.univ : Set Vec3)} :
    SchwartzMap L2Vec3 ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ l2Vec3Equiv
    (weakTestSourceSchwartz ψ)

/-- The complex-valued Schwartz encoding of a scalar weak test function on the Hilbert
coordinates. -/
@[expose]
def weakTestComplexSchwartz {ψ : WeakTestFunction (Set.univ : Set Vec3)} :
    SchwartzMap L2Vec3 ℂ :=
  (weakTestSchwartz (ψ := ψ)).postcompCLM Complex.ofRealCLM

/-- The Schwartz encoding of the gradient of a weak test function. -/
@[expose]
def weakTestGradientSchwartz
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    SchwartzMap L2Vec3 ComplexVec3 :=
  (SchwartzMap.fderivCLM ℂ L2Vec3 ℂ (weakTestComplexSchwartz (ψ := ψ))).postcompCLM
    gradientOfCovector

private theorem weakTestGradientSchwartz_apply
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) (x : L2Vec3) (i : Fin 3) :
    weakTestGradientSchwartz ψ x i =
      (ψ.partialDeriv i (l2Vec3Equiv x) : ℂ) := by
  have hψSource : ContDiff ℝ (⊤ : ℕ∞) (weakTestSourceSchwartz ψ) := by
    change ContDiff ℝ (⊤ : ℕ∞) ψ.toFun
    simpa using ψ.contDiff
  have hL : fderiv ℝ (fun z : L2Vec3 =>
      (l2Vec3Equiv : L2Vec3 →L[ℝ] Vec3) z) x =
        (l2Vec3Equiv : L2Vec3 →L[ℝ] Vec3) :=
    l2Vec3Equiv.hasFDerivAt.fderiv
  have hcomp' :
    fderiv ℝ (fun z : L2Vec3 => weakTestSourceSchwartz ψ (l2Vec3Equiv z)) x =
        (fderiv ℝ (weakTestSourceSchwartz ψ) (l2Vec3Equiv x)).comp
          (l2Vec3Equiv : L2Vec3 →L[ℝ] Vec3) := by
    calc
      fderiv ℝ (fun z : L2Vec3 => weakTestSourceSchwartz ψ (l2Vec3Equiv z)) x =
          (fderiv ℝ (weakTestSourceSchwartz ψ) (l2Vec3Equiv x)).comp
            (fderiv ℝ (fun z : L2Vec3 => (l2Vec3Equiv : L2Vec3 →L[ℝ] Vec3) z) x) := by
              exact fderiv_comp (x := x)
                (hψSource.differentiable (by simp) (l2Vec3Equiv x))
                l2Vec3Equiv.differentiableAt
      _ = _ := by rw [hL]
  have hψL : ContDiff ℝ (⊤ : ℕ∞) (fun z : L2Vec3 => weakTestSchwartz (ψ := ψ) z) := by
    change ContDiff ℝ (⊤ : ℕ∞) (ψ.toFun ∘ l2Vec3Equiv)
    exact (ψ.contDiff.comp l2Vec3Equiv.contDiff)
  change (fderiv ℝ ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘
      (fun z : L2Vec3 => weakTestSchwartz (ψ := ψ) z)) x) (l2BasisVec i) = _
  rw [fderiv_comp (x := x) Complex.ofRealCLM.differentiableAt
    (hψL.differentiable (by simp) x)]
  rw [Complex.ofRealCLM.hasFDerivAt.fderiv]
  change Complex.ofReal
      ((fderiv ℝ (fun z : L2Vec3 =>
        weakTestSourceSchwartz ψ (l2Vec3Equiv z)) x) (l2BasisVec i)) = _
  rw [hcomp']
  simp only [ContinuousLinearMap.comp_apply]
  change Complex.ofReal ((fderiv ℝ (weakTestSourceSchwartz ψ)
      (l2Vec3Equiv x)) ((l2Vec3Equiv : L2Vec3 → Vec3) (l2BasisVec i))) =
    Complex.ofReal ((fderiv ℝ ψ.toFun (l2Vec3Equiv x)) (CKN.basisVec i))
  rw [show (l2Vec3Equiv : L2Vec3 → Vec3) (l2BasisVec i) = CKN.basisVec i by
    ext j
    simp [l2BasisVec, l2Vec3Equiv, CKN.basisVec, Pi.single_apply]]
  rfl

private theorem weakTestGradientSchwartz_fourier
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) (ξ : L2Vec3) :
    𝓕 (weakTestGradientSchwartz ψ) ξ =
      ((2 * Real.pi * Complex.I) * (𝓕 (weakTestComplexSchwartz (ψ := ψ)) ξ)) •
        complexifyFrequency ξ := by
  have hpost := fourier_postcompCLM gradientOfCovector
    (SchwartzMap.fderivCLM ℂ L2Vec3 ℂ (weakTestComplexSchwartz (ψ := ψ)))
  rw [weakTestGradientSchwartz, hpost, SchwartzMap.fourier_fderivCLM_eq]
  apply PiLp.ext
  intro i
  rw [SchwartzMap.postcompCLM_apply]
  simp [gradientOfCovector, gradientOfCovectorLinear,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply ℝ,
    inner_l2BasisVec, complexifyFrequency]
  ring

private theorem weakTestPairing_zero_of_fourier_orthogonal
    (v : ComplexVectorL2)
    (hv : ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ) ((MeasureTheory.Lp.fourierTransformₗᵢ
        L2Vec3 ComplexVec3) v ξ) = 0)
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    inner ℂ v ((weakTestGradientSchwartz ψ).toLp 2) = 0 := by
  let gS := weakTestGradientSchwartz ψ
  let gLp : ComplexVectorL2 := gS.toLp 2
  have hFourierG :
      (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) gLp =
        (𝓕 gS).toLp 2 := by
    change 𝓕 (gS.toLp 2) = (𝓕 gS).toLp 2
    exact SchwartzMap.toLp_fourier_eq gS
  have hFourierGAE :
      (fun ξ : L2Vec3 =>
        (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) gLp ξ) =ᵐ[volume]
        fun ξ => 𝓕 gS ξ := by
    rw [hFourierG]
    exact ((𝓕 gS).memLp 2 volume).coeFn_toLp
  have hPlanch : inner ℂ
      ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) v)
      ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) gLp) =
        inner ℂ v gLp :=
    (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).inner_map_map v gLp
  rw [← hPlanch]
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hv, hFourierGAE] with ξ hξ hGξ
  have hsym : inner ℂ
      ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) v ξ)
      (complexifyFrequency ξ) = 0 := inner_eq_zero_symm.mp hξ
  have hGξ' :
      (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) gLp ξ = 𝓕 gS ξ := hGξ
  rw [hGξ', weakTestGradientSchwartz_fourier]
  rw [inner_smul_right, hsym]
  simp

/-- The real coordinate representative of a complex Euclidean `L²` field,
used for the weak-divergence conclusion in `lem:reg-multiplier-bounds`. -/
@[expose]
def realPartVectorL2Representative (v : ComplexVectorL2) : Vec3 → Vec3 :=
  fun x => l2Vec3Equiv
    (realPartValue (v (WithLp.toLp 2 x)))

/-- A complex `L²` field whose Fourier transform is orthogonal to frequency
has real part with zero physical weak divergence, as in
`lem:reg-multiplier-bounds`. -/
theorem realPart_isWeakDivFree_of_fourierOrthogonal
    (v : ComplexVectorL2)
    (hv : ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ) ((MeasureTheory.Lp.fourierTransformₗᵢ
        L2Vec3 ComplexVec3) v ξ) = 0) :
    CKN.IsWeakDivFreeL2 (realPartVectorL2Representative v) := by
  have hmemL2 : MemLp (fun x : L2Vec3 => realPartValue (v x)) 2 volume :=
    (Lp.memLp v).continuousLinearMap_comp realPartValue
  have hmemCoord : MemLp
      (fun x : Vec3 => realPartValue (v (WithLp.toLp 2 x))) 2 volume :=
    hmemL2.comp_measurePreserving vec3ToL2Vec3_measurePreserving
  have hmem : MemLp (realPartVectorL2Representative v) 2 volume :=
    hmemCoord.continuousLinearMap_comp l2Vec3Equiv.toContinuousLinearMap
  refine ⟨hmem, ?_⟩
  intro ψ
  let gS := weakTestGradientSchwartz ψ
  let gLp : ComplexVectorL2 := gS.toLp 2
  have hPair := weakTestPairing_zero_of_fourier_orthogonal v hv ψ
  have hPairIntegral :
      (∫ x : L2Vec3, inner ℂ (v x) (gLp x)) = 0 := by
    rw [← MeasureTheory.L2.inner_def]
    exact hPair
  have hPairIntegrable : Integrable
      (fun x : L2Vec3 => inner ℂ (v x) (gLp x)) volume :=
    MeasureTheory.L2.integrable_inner v gLp
  have hRealPairIntegral :
      ∫ x : L2Vec3, Complex.re (inner ℂ (v x) (gLp x)) = 0 := by
    calc
      ∫ x : L2Vec3, Complex.re (inner ℂ (v x) (gLp x)) =
          Complex.re (∫ x : L2Vec3, inner ℂ (v x) (gLp x)) :=
        Complex.reCLM.integral_comp_comm hPairIntegrable
      _ = 0 := by rw [hPairIntegral]; rfl
  have hGradAE : (fun x : L2Vec3 => gLp x) =ᵐ[volume] fun x => gS x :=
    (gS.memLp 2 volume).coeFn_toLp
  have hRealPairIntegralS :
      ∫ x : L2Vec3, Complex.re (inner ℂ (v x) (gS x)) = 0 := by
    apply (integral_congr_ae ?_).trans hRealPairIntegral
    filter_upwards [hGradAE] with x hx
    simp [hx]
  have hpoint (x : L2Vec3) :
      (∑ i : Fin 3,
        realPartValue (v x) i * ψ.partialDeriv i (l2Vec3Equiv x)) =
        Complex.re (inner ℂ (v x) (gS x)) := by
    rw [PiLp.inner_apply]
    simp only [realPartValue, realPartValueLinear, LinearMap.mkContinuous_apply,
      LinearMap.coe_mk, AddHom.coe_mk, weakTestGradientSchwartz_apply,
      RCLike.inner_apply, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.conj_re, Complex.ofReal_im, Complex.conj_im, mul_neg, zero_mul,
      neg_zero, sub_zero, gS]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume :=
    vec3ToL2Vec3_measurePreserving
  have hEmbedding : MeasurableEmbedding (WithLp.toLp 2 : Vec3 → L2Vec3) :=
    l2Vec3Equiv.symm.toHomeomorph.measurableEmbedding
  let F : L2Vec3 → ℝ := fun x => Complex.re (inner ℂ (v x) (gS x))
  calc
      ∫ x : Vec3, ∑ i : Fin 3,
        realPartVectorL2Representative v x i * ψ.partialDeriv i x =
      ∫ x : Vec3, F (WithLp.toLp 2 x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hp := hpoint (WithLp.toLp 2 x)
        change (∑ i : Fin 3,
          (realPartValue (v (WithLp.toLp 2 x))).ofLp i *
            ψ.partialDeriv i x) =
          Complex.re (inner ℂ (v (WithLp.toLp 2 x))
            (gS (WithLp.toLp 2 x))) at hp
        simpa [F, realPartVectorL2Representative, l2Vec3Equiv] using hp
    _ = ∫ x : L2Vec3, F x := htransport.integral_comp hEmbedding F
    _ = 0 := hRealPairIntegralS

/-- Weak divergence freedom is invariant under almost everywhere equality. -/
theorem isWeakDivFree_congr_ae {a b : Vec3 → Vec3}
    (hab : a =ᵐ[volume] b) (ha : CKN.IsWeakDivFreeL2 a) :
    CKN.IsWeakDivFreeL2 b := by
  refine ⟨MemLp.ae_eq hab ha.1, ?_⟩
  intro ψ
  have hsum : (fun x : Vec3 => ∑ i : Fin 3, b x i * ψ.partialDeriv i x) =ᵐ[volume]
      fun x => ∑ i : Fin 3, a x i * ψ.partialDeriv i x := by
    filter_upwards [hab] with x hx
    rw [hx]
  calc
    ∫ x : Vec3, ∑ i : Fin 3, b x i * ψ.partialDeriv i x =
      ∫ x : Vec3, ∑ i : Fin 3, a x i * ψ.partialDeriv i x := integral_congr_ae hsum
    _ = 0 := ha.2 ψ

/-- The representative of the real part agrees almost everywhere with the
real part of the complex representative. -/
theorem realPartVectorL2Representative_eq_ae
    (z : ComplexVectorL2) :
    realVectorL2Representative (realPartVectorL2 z) =ᵐ[volume]
      realPartVectorL2Representative z := by
  have hcomp := realPartValue.coeFn_compLpL z
  have hcompAE : ∀ᵐ x : L2Vec3, realPartVectorL2 z x = realPartValue (z x) := hcomp
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume :=
    vec3ToL2Vec3_measurePreserving
  have hcomp' :
      (fun x : Vec3 => realPartVectorL2 z (WithLp.toLp 2 x)) =ᵐ[volume]
        fun x => realPartValue (z (WithLp.toLp 2 x)) :=
    htransport.quasiMeasurePreserving.ae hcompAE
  filter_upwards [hcomp'] with x hx
  simp [realVectorL2Representative, realPartVectorL2Representative, hx]

/-- The physical Leray projection has weakly divergence-free real range, the
physical-space assertion in `lem:reg-multiplier-bounds`. -/
theorem realLerayProjectionRepresentative_isWeakDivFree (f : RealVectorL2) :
    CKN.IsWeakDivFreeL2
      (realPartVectorL2Representative
        (lerayProjectionL2 (complexifyVectorL2 f))) := by
  apply realPart_isWeakDivFree_of_fourierOrthogonal
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have htransform :
      ℱ (lerayProjectionL2 (complexifyVectorL2 f)) =
        lerayFourierMultiplier (ℱ (complexifyVectorL2 f)) := by
    change ℱ (ℱ.symm (lerayFourierMultiplier (ℱ (complexifyVectorL2 f)))) = _
    exact ℱ.apply_symm_apply _
  have htransformAE := (Lp.ext_iff).mp htransform
  filter_upwards [htransformAE,
    lerayFourierMultiplier_divergence_free_ae (ℱ (complexifyVectorL2 f))]
    with ξ hξ hrange
  rw [hξ]
  exact hrange

/-- The representative of `realLerayProjection` is weakly divergence-free in
physical space, as asserted in `lem:reg-multiplier-bounds`. -/
theorem realLerayProjection_isWeakDivFree (f : RealVectorL2) :
    CKN.IsWeakDivFreeL2 (realVectorL2Representative (realLerayProjection f)) := by
  let z := lerayProjectionL2 (complexifyVectorL2 f)
  have hRange := realLerayProjectionRepresentative_isWeakDivFree f
  have hAE := realPartVectorL2Representative_eq_ae z
  change CKN.IsWeakDivFreeL2 (realVectorL2Representative (realPartVectorL2 z))
  exact isWeakDivFree_congr_ae hAE.symm hRange

/-- The physical Stokes operator has weakly divergence-free real range, the
physical-space assertion in `lem:reg-multiplier-bounds`. -/
theorem realStokesOperatorRepresentative_isWeakDivFree {t : ℝ}
    (ht : 0 < t) (F : RealTensorL2) :
    CKN.IsWeakDivFreeL2
      (realPartVectorL2Representative (stokesL2Operator ht
        (complexifyTensorL2 F))) := by
  apply realPart_isWeakDivFree_of_fourierOrthogonal
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have htransform :
      ℱV (stokesL2Operator ht (complexifyTensorL2 F)) =
        stokesFourierMultiplier ht (ℱT (complexifyTensorL2 F)) := by
    change ℱV (ℱV.symm
      (stokesFourierMultiplier ht (ℱT (complexifyTensorL2 F)))) = _
    exact ℱV.apply_symm_apply _
  have htransformAE := (Lp.ext_iff).mp htransform
  filter_upwards [htransformAE,
    stokesFourierMultiplier_divergence_free_ae ht
      (ℱT (complexifyTensorL2 F))] with ξ hξ hrange
  rw [hξ]
  exact hrange

/-- The representative of `realStokesOperator` is weakly divergence-free in
physical space, as asserted in `lem:reg-multiplier-bounds`. -/
theorem realStokesOperator_isWeakDivFree {t : ℝ} (ht : 0 < t)
    (F : RealTensorL2) :
    CKN.IsWeakDivFreeL2 (realVectorL2Representative (realStokesOperator ht F)) := by
  let z := stokesL2Operator ht (complexifyTensorL2 F)
  have hRange := realStokesOperatorRepresentative_isWeakDivFree ht F
  have hAE := realPartVectorL2Representative_eq_ae z
  change CKN.IsWeakDivFreeL2 (realVectorL2Representative (realPartVectorL2 z))
  exact isWeakDivFree_congr_ae hAE.symm hRange

end CKN.Leray
