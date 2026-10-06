/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.VectorPotential
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourier
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# JSpace Fourier Potential Base

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open Filter
open scoped ENNReal FourierTransform LineDeriv SchwartzMap
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- One complex Fourier-space coordinate of an `L²` vector field. -/
@[expose]
def weakFieldFourierComponent {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (i : Fin 3) :
    Lp (α := L2Vec3) ℂ 2 :=
  let h := complexifyVec3_memLp ha
  (h.eval_piLp i).toLp (fun x : L2Vec3 => complexifyVec3 a x i)

/-- The regularized potential coordinate as a complex `L²` function. -/
@[expose]
def regularizedPotentialComponentLp {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) (i : Fin 3) :
    Lp (α := L2Vec3) ℂ 2 :=
  regularizedPotentialL2Component δ hδ i
    (fun j => 𝓕 (weakFieldFourierComponent ha j))

/-- The real vector field represented by the regularized potential. -/
@[expose]
def regularizedPotentialVec3 {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) : Vec3 → Vec3 :=
  fun x i => Complex.re (regularizedPotentialComponentLp ha δ hδ i (WithLp.toLp 2 x))

/-- A first derivative of a coordinate of the regularized vector potential,
represented as a complex `L²` function on the native Euclidean carrier. -/
@[expose]
def regularizedPotentialDerivativeComponentLp {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (_hδ : 0 < δ)
    (i k : Fin 3) : Lp (α := L2Vec3) ℂ 2 :=
  𝓕⁻ (let f := fun j => 𝓕 (weakFieldFourierComponent ha j)
      if _hi : i = 0 then
        regularizedDerivativeEntryApply δ k 1 (f 2) -
          regularizedDerivativeEntryApply δ k 2 (f 1)
      else if _hi : i = 1 then
        regularizedDerivativeEntryApply δ k 2 (f 0) -
          regularizedDerivativeEntryApply δ k 0 (f 2)
      else
        regularizedDerivativeEntryApply δ k 0 (f 1) -
          regularizedDerivativeEntryApply δ k 1 (f 0))

/-- The real first derivatives of the regularized potential. -/
@[expose]
def regularizedPotentialGradientVec3 {a : Vec3 → Vec3}
    (ha : MemLp a (2 : ℝ≥0∞) volume) (δ : ℝ) (hδ : 0 < δ) :
    Vec3 → Fin 3 → Fin 3 → ℝ :=
  fun x i k => Complex.re
    (regularizedPotentialDerivativeComponentLp ha δ hδ i k (WithLp.toLp 2 x))

private theorem regularizedDerivativeEntry_fourierMultiplier_eq
    (δ : ℝ) (hδ : 0 < δ) (k j : Fin 3)
    (f : Lp (α := L2Vec3) ℂ 2) :
    TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k j)
        (f : 𝓢'(L2Vec3, ℂ)) =
      ((2 * Real.pi : ℂ) * Complex.I) •
        TemperedDistribution.fourierMultiplierCLM ℂ
          (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord k ξ))
          (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
            (f : 𝓢'(L2Vec3, ℂ))) := by
  let m : L2Vec3 → ℂ := fun ξ => Complex.ofReal (frequencyL2Coord k ξ)
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  have hm : m.HasTemperateGrowth := by
    change (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord k ξ)).HasTemperateGrowth
    fun_prop
  have hsymbol : regularizedDerivativeEntry δ k j =
      fun ξ => regularizedPotentialEntry δ j ξ * (c * m ξ) := by
    funext ξ
    simp only [m, c]
    rw [regularizedDerivativeEntry_eq_frequency_mul_potential δ hδ ξ k j]
    simp [frequencyL2Coord, PiLp.proj_apply]
    ring
  have hcomp := TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (regularizedPotentialEntry_hasTemperateGrowth δ j)
    (by
      change (fun ξ : L2Vec3 => ((2 * Real.pi : ℂ) * Complex.I) *
        Complex.ofReal (frequencyL2Coord k ξ)).HasTemperateGrowth
      fun_prop)
    (f : 𝓢'(L2Vec3, ℂ))
  calc
    TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k j)
        (f : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ => regularizedPotentialEntry δ j ξ * (c * m ξ))
        (f : 𝓢'(L2Vec3, ℂ)) := by rw [hsymbol]
    _ = TemperedDistribution.fourierMultiplierCLM ℂ (fun ξ => c * m ξ)
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
          (f : 𝓢'(L2Vec3, ℂ))) := hcomp.symm
    _ = c • TemperedDistribution.fourierMultiplierCLM ℂ m
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
          (f : 𝓢'(L2Vec3, ℂ))) := by
        change TemperedDistribution.fourierMultiplierCLM ℂ (c • m)
            (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
              (f : 𝓢'(L2Vec3, ℂ))) = _
        exact congrArg (fun T => T
          (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
          (f : 𝓢'(L2Vec3, ℂ))))
          (TemperedDistribution.fourierMultiplierCLM_smul hm c)

private theorem inverseFourier_regularizedPotentialEntryApply_toTemperedDistribution
    (δ : ℝ) (hδ : 0 < δ) (j : Fin 3)
    (f : Lp (α := L2Vec3) ℂ 2) :
    ((𝓕⁻ (regularizedPotentialEntryApply δ hδ j (𝓕 f)) :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
        (f : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (fourierMultiplyScalarL2 (regularizedPotentialEntry δ j)
    (regularizedPotentialEntry_memLp δ hδ j) (𝓕 f)) :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  exact inverseFourier_fourierMultiplyScalarL2_eq_fourierMultiplierCLM
    (regularizedPotentialEntry δ j)
    (regularizedPotentialEntry_hasTemperateGrowth δ j)
    (regularizedPotentialEntry_memLp δ hδ j) f

private theorem inverseFourier_regularizedDerivativeEntryApply_toTemperedDistribution
    (δ : ℝ) (k j : Fin 3)
    (f : Lp (α := L2Vec3) ℂ 2) :
    ((𝓕⁻ (regularizedDerivativeEntryApply δ k j (𝓕 f)) :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k j)
        (f : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (fourierMultiplyScalarL2 (regularizedDerivativeEntry δ k j)
    (regularizedDerivativeEntry_memLp δ k j) (𝓕 f)) :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  exact inverseFourier_fourierMultiplyScalarL2_eq_fourierMultiplierCLM
    (regularizedDerivativeEntry δ k j)
    (regularizedDerivativeEntry_hasTemperateGrowth δ k j)
    (regularizedDerivativeEntry_memLp δ k j) f

/-- The coordinatewise equivalence between the native vector carrier and `L²` Pi space. -/
@[expose]
def l2Vec3Equiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

/-- A coordinate directional derivative on the `L²` Pi carrier. -/
@[expose]
def l2SpatialDeriv (ψ : SchwartzMap L2Vec3 ℝ) (i : Fin 3) :
    L2Vec3 → ℝ :=
  fun x => fderiv ℝ ψ x (l2Vec3Equiv.symm (basisVec i))

/-- The coordinate basis vector in the `L²` Pi carrier. -/
@[expose]
def l2BasisVec3 (i : Fin 3) : L2Vec3 :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))

/-- The coordinate equivalence sends each native basis vector to its Pi representative. -/
theorem l2Vec3Equiv_symm_basisVec (i : Fin 3) :
    l2Vec3Equiv.symm (basisVec i) = l2BasisVec3 i := by
  apply l2Vec3Equiv.injective
  ext j
  simp [l2BasisVec3, l2Vec3Equiv, basisVec]

/-- The Pi inner product with a coordinate basis vector is the corresponding coordinate. -/
theorem inner_l2BasisVec3 (ξ : L2Vec3) (i : Fin 3) :
    inner ℝ ξ (l2BasisVec3 i) = frequencyL2Coord i ξ := by
  rw [PiLp.inner_apply]
  simp [l2BasisVec3, frequencyL2Coord, PiLp.proj_apply]

private theorem temperedDistribution_lineDeriv_sub
    (m : L2Vec3) (u v : 𝓢'(L2Vec3, ℂ)) :
    ∂_{m} (u - v) = ∂_{m} u - ∂_{m} v := by
  change ∂_{m} (u + -v) = _
  rw [LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_neg]
  rfl

private theorem inverseFourierLp_sub_toTemperedDistribution
    (u v : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) :
    ((𝓕⁻ (u - v) : Lp (α := L2Vec3) ℂ 2
        (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      ((𝓕⁻ u : Lp (α := L2Vec3) ℂ 2
        (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) -
      ((𝓕⁻ v : Lp (α := L2Vec3) ℂ 2
        (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) := by
  have hFourierInv : 𝓕⁻ (u - v) = (𝓕⁻ u - 𝓕⁻ v :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) := by
    exact (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ℂ).symm.map_sub u v
  let T : Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3) →L[ℂ]
      𝓢'(L2Vec3, ℂ) :=
    MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 2
  calc
    T (𝓕⁻ (u - v)) = T (𝓕⁻ u - 𝓕⁻ v) := congrArg T hFourierInv
    _ = T (𝓕⁻ u) - T (𝓕⁻ v) := T.map_sub _ _

private theorem regularizedPotentialComponentLp_real_schwartz_weakDeriv
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (i k : Fin 3)
    (hdist :
      ((regularizedPotentialDerivativeComponentLp ha δ hδ i k :
        Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
        ∂_{l2BasisVec3 k}
          ((regularizedPotentialComponentLp ha δ hδ i :
            Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)))
    (ψ : SchwartzMap L2Vec3 ℝ) :
    ∫ x : L2Vec3,
        Complex.re (regularizedPotentialComponentLp ha δ hδ i x) *
          l2SpatialDeriv ψ k x ∂volume =
      -∫ x : L2Vec3,
        Complex.re (regularizedPotentialDerivativeComponentLp ha δ hδ i k x) *
          ψ x ∂volume := by
  let ψC : SchwartzMap L2Vec3 ℂ := ψ.postcompCLM Complex.ofRealCLM
  have hψCderiv (x : L2Vec3) :
      (∂_{l2BasisVec3 k} ψC) x =
        (l2SpatialDeriv ψ k x : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hOfReal (x : ℝ) :
        fderiv ℝ (fun y : ℝ => (y : ℂ)) x = Complex.ofRealCLM :=
      Complex.ofRealCLM.hasFDerivAt.fderiv
    have hgd : DifferentiableAt ℝ (fun y : ℝ => (y : ℂ)) (ψ x) := by
      fun_prop
    have hcomp : fderiv ℝ (fun y : L2Vec3 => (ψ y : ℂ)) x =
        Complex.ofRealCLM ∘L fderiv ℝ ψ x := by
      change fderiv ℝ ((fun y : ℝ => (y : ℂ)) ∘ ψ) x = _
      rw [fderiv_comp (f := ψ) (g := fun y : ℝ => (y : ℂ)) (x := x)
        hgd ψ.differentiableAt, hOfReal]
    change (fderiv ℝ (fun y : L2Vec3 => (ψ y : ℂ)) x)
        (l2Vec3Equiv.symm (basisVec k)) = _
    rw [hcomp]
    rfl
  have hEval := congrArg (fun T : 𝓢'(L2Vec3, ℂ) => T ψC) hdist
  have hPair :
    ∫ x : L2Vec3, ψC x * regularizedPotentialDerivativeComponentLp ha δ hδ i k x
          ∂volume =
        -∫ x : L2Vec3, (∂_{l2BasisVec3 k} ψC) x *
          regularizedPotentialComponentLp ha δ hδ i x ∂volume := by
    have hnegfun : (fun x : L2Vec3 => (-∂_{l2BasisVec3 k} ψC) x *
        regularizedPotentialComponentLp ha δ hδ i x) =
        fun x => -((∂_{l2BasisVec3 k} ψC) x *
          regularizedPotentialComponentLp ha δ hδ i x) := by
      funext x
      simp
    have hnegint :
        ∫ x : L2Vec3, (-∂_{l2BasisVec3 k} ψC) x *
          regularizedPotentialComponentLp ha δ hδ i x ∂volume =
          -∫ x : L2Vec3, (∂_{l2BasisVec3 k} ψC) x *
            regularizedPotentialComponentLp ha δ hδ i x ∂volume := by
      rw [hnegfun]
      exact integral_neg _
    calc
      _ = ∫ x : L2Vec3, (-∂_{l2BasisVec3 k} ψC) x *
          regularizedPotentialComponentLp ha δ hδ i x ∂volume := by
            simpa only [TemperedDistribution.lineDerivOp_apply_apply,
              MeasureTheory.Lp.toTemperedDistribution_apply,
              smul_eq_mul] using hEval
      _ = _ := hnegint
  have hIntLeft : Integrable
      (fun x : L2Vec3 => ψC x * regularizedPotentialDerivativeComponentLp ha δ hδ i k x)
      volume := (ψC.memLp (2 : ℝ≥0∞) volume).integrable_mul
        (Lp.memLp (regularizedPotentialDerivativeComponentLp ha δ hδ i k))
  have hIntRight : Integrable
      (fun x : L2Vec3 => (∂_{l2BasisVec3 k} ψC) x *
        regularizedPotentialComponentLp ha δ hδ i x) volume :=
    ((∂_{l2BasisVec3 k} ψC).memLp (2 : ℝ≥0∞) volume).integrable_mul
      (Lp.memLp (regularizedPotentialComponentLp ha δ hδ i))
  have hPairRe := congrArg Complex.re hPair
  have hRealPair :
      ∫ x : L2Vec3, Complex.re (ψC x *
          regularizedPotentialDerivativeComponentLp ha δ hδ i k x) ∂volume =
        -∫ x : L2Vec3, Complex.re ((∂_{l2BasisVec3 k} ψC) x *
          regularizedPotentialComponentLp ha δ hδ i x) ∂volume := by
    calc
      _ = Complex.re (∫ x : L2Vec3, ψC x *
          regularizedPotentialDerivativeComponentLp ha δ hδ i k x ∂volume) :=
        Complex.reCLM.integral_comp_comm hIntLeft
      _ = Complex.re (-∫ x : L2Vec3, (∂_{l2BasisVec3 k} ψC) x *
          regularizedPotentialComponentLp ha δ hδ i x ∂volume) := hPairRe
      _ = _ := by
        simp only [Complex.neg_re]
        congr 1
        exact (Complex.reCLM.integral_comp_comm hIntRight).symm
  have hReal :
      ∫ x : L2Vec3, ψ x * Complex.re
          (regularizedPotentialDerivativeComponentLp ha δ hδ i k x) ∂volume =
        -∫ x : L2Vec3, l2SpatialDeriv ψ k x * Complex.re
          (regularizedPotentialComponentLp ha δ hδ i x) ∂volume := by
    simpa [ψC, Complex.mul_re, hψCderiv] using hRealPair
  calc
    ∫ x : L2Vec3,
        Complex.re (regularizedPotentialComponentLp ha δ hδ i x) *
          l2SpatialDeriv ψ k x ∂volume =
      ∫ x : L2Vec3,
        l2SpatialDeriv ψ k x * Complex.re
          (regularizedPotentialComponentLp ha δ hδ i x) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
    _ = -∫ x : L2Vec3,
        ψ x * Complex.re
          (regularizedPotentialDerivativeComponentLp ha δ hδ i k x) ∂volume := by
          simpa only [mul_comm] using (neg_eq_iff_eq_neg).mp hReal.symm
    _ = -∫ x : L2Vec3,
        Complex.re (regularizedPotentialDerivativeComponentLp ha δ hδ i k x) *
          ψ x ∂volume := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          ring

/-- The regularized potential has the distributional derivatives represented by its Fourier derivatives. -/
theorem regularizedPotentialVec3_hasWeakPartialDerivOn
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (i k : Fin 3)
    (hdist :
      ((regularizedPotentialDerivativeComponentLp ha δ hδ i k :
        Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
        ∂_{l2BasisVec3 k}
          ((regularizedPotentialComponentLp ha δ hδ i :
            Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ))) :
    CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) k
      (fun x => regularizedPotentialVec3 ha δ hδ x i)
      (fun x => regularizedPotentialGradientVec3 ha δ hδ x i k) := by
  intro φ hφSmooth hφCompact hφSupport
  let φS : SchwartzMap Vec3 ℝ := hφCompact.toSchwartzMap hφSmooth
  let ψ : SchwartzMap L2Vec3 ℝ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ l2Vec3Equiv φS
  let p : L2Vec3 → ℝ := fun x =>
    Complex.re (regularizedPotentialComponentLp ha δ hδ i x)
  let g : L2Vec3 → ℝ := fun x =>
    Complex.re (regularizedPotentialDerivativeComponentLp ha δ hδ i k x)
  let F : L2Vec3 → ℝ := fun x => p x * l2SpatialDeriv ψ k x
  let G : L2Vec3 → ℝ := fun x => g x * ψ x
  have hweak := regularizedPotentialComponentLp_real_schwartz_weakDeriv ha δ hδ i k
    hdist ψ
  have htransport : MeasurePreserving (l2Vec3Equiv.symm : Vec3 → L2Vec3)
      volume volume := PiLp.volume_preserving_toLp (Fin 3)
  have hembedding : MeasurableEmbedding (l2Vec3Equiv.symm : Vec3 → L2Vec3) :=
    l2Vec3Equiv.symm.toHomeomorph.measurableEmbedding
  have hcoordinate (x : Vec3) :
      l2Vec3Equiv.symm x = WithLp.toLp 2 x := rfl
  have htest (x : Vec3) : ψ (l2Vec3Equiv.symm x) = φ x := by
    simp [ψ, φS]
  have hderiv (x : Vec3) :
      l2SpatialDeriv ψ k (l2Vec3Equiv.symm x) =
        spatialDeriv (fun y : Vec3 => φ y) k x := by
    change (∂_{l2Vec3Equiv.symm (basisVec k)} ψ) (l2Vec3Equiv.symm x) =
      (∂_{basisVec k} φS) x
    rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv ℝ
      (l2Vec3Equiv.symm (basisVec k)) l2Vec3Equiv φS]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hleft (x : Vec3) :
      regularizedPotentialVec3 ha δ hδ x i * spatialDeriv
        (fun y : Vec3 => φ y) k x = F (l2Vec3Equiv.symm x) := by
    dsimp [F, p, regularizedPotentialVec3]
    rw [← hcoordinate x, hderiv x]
  have hright (x : Vec3) :
      regularizedPotentialGradientVec3 ha δ hδ x i k * φ x =
        G (l2Vec3Equiv.symm x) := by
    dsimp [G, g, regularizedPotentialGradientVec3]
    rw [← hcoordinate x, htest x]
  rw [MeasureTheory.setIntegral_univ, MeasureTheory.setIntegral_univ]
  calc
    ∫ x : Vec3, regularizedPotentialVec3 ha δ hδ x i * spatialDeriv
        (fun y : Vec3 => φ y) k x ∂volume =
      ∫ x : Vec3, F (l2Vec3Equiv.symm x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hleft x
    _ = ∫ x : L2Vec3, F x ∂volume :=
      htransport.integral_comp hembedding F
    _ = -∫ x : L2Vec3, G x ∂volume := hweak
    _ = -∫ x : Vec3, G (l2Vec3Equiv.symm x) ∂volume := by
      exact congrArg Neg.neg (htransport.integral_comp hembedding G).symm
    _ = -∫ x : Vec3, regularizedPotentialGradientVec3 ha δ hδ x i k * φ x
        ∂volume := by
          apply congrArg Neg.neg
          apply integral_congr_ae
          filter_upwards [] with x
          exact (hright x).symm

private theorem cknMollify_sub_of_locallyIntegrable
    {f g : Vec3 → ℝ}
    (hf : LocallyIntegrable f (volume : Measure Vec3))
    (hg : LocallyIntegrable g (volume : Measure Vec3))
    {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    CKN.mollify (fun y => f y - g y) ε hε x =
      CKN.mollify f ε hε x - CKN.mollify g ε hε x := by
  let kernel := CKN.mollifier (d := 3) ε hε
  have hkernelSmooth : ContDiff ℝ (⊤ : ℕ∞) kernel := CKN.mollifier_contDiff hε
  have hkernelCompact : HasCompactSupport kernel := CKN.mollifier_hasCompactSupport hε
  have hconvf : ConvolutionExists kernel f
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure Vec3) :=
    hkernelCompact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hkernelSmooth.continuous hf
  have hconvg : ConvolutionExists kernel g
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure Vec3) :=
    hkernelCompact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hkernelSmooth.continuous hg
  have hfun : (fun y : Vec3 => kernel y * (f - g) (x - y)) =
      (fun y => kernel y * f (x - y)) - (fun y => kernel y * g (x - y)) := by
    funext y
    simp [Pi.sub_apply]
    ring
  change (∫ y, kernel y * (f - g) (x - y) ∂volume) =
    (∫ y, kernel y * f (x - y) ∂volume) -
      ∫ y, kernel y * g (x - y) ∂volume
  calc
    (∫ y, kernel y * (f - g) (x - y) ∂volume) =
        ∫ y, (kernel y * f (x - y)) - (kernel y * g (x - y)) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp only [Pi.sub_apply]
          ring
    _ = (∫ y, kernel y * f (x - y) ∂volume) -
        ∫ y, kernel y * g (x - y) ∂volume :=
      integral_sub (hconvf x).integrable (hconvg x).integrable

/-- The coordinate curl formed from a represented weak gradient. -/
@[expose]
def curlOfGradient (G : Vec3 → Fin 3 → Fin 3 → ℝ) : Vec3 → Vec3 :=
  fun x i => if i = 0 then G x 2 1 - G x 1 2
    else if i = 1 then G x 0 2 - G x 2 0
    else G x 1 0 - G x 0 1

/-- An `L²` matrix field has an `L²` coordinate curl. -/
theorem curlOfGradient_memLp {G : Vec3 → Fin 3 → Fin 3 → ℝ}
    (hG : ∀ i k, MemLp (fun x : Vec3 => G x i k) (2 : ℝ≥0∞) volume) :
    MemLp (curlOfGradient G) (2 : ℝ≥0∞) volume := by
  apply MemLp.of_eval
  intro i
  fin_cases i
  · change MemLp (fun x : Vec3 => G x 2 1 - G x 1 2) (2 : ℝ≥0∞) volume
    exact (hG 2 1).sub (hG 1 2)
  · change MemLp (fun x : Vec3 => G x 0 2 - G x 2 0) (2 : ℝ≥0∞) volume
    exact (hG 0 2).sub (hG 2 0)
  · change MemLp (fun x : Vec3 => G x 1 0 - G x 0 1) (2 : ℝ≥0∞) volume
    exact (hG 1 0).sub (hG 0 1)

/-- Spatial mollification commutes with the curl of a represented weak gradient. -/
theorem curl_spatialMollify_eq_spatialMollify_curlOfGradient
    {A : Vec3 → Vec3} {G : Vec3 → Fin 3 → Fin 3 → ℝ}
    (hA : MemLp A (2 : ℝ≥0∞) volume)
    (hG : MemLp G (2 : ℝ≥0∞) volume)
    (hweak : ∀ i k,
      CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) k
        (fun x => A x i) (fun x => G x i k))
    {ε : ℝ} (hε : 0 < ε) (x : Vec3) :
    curlVec3 (spatialMollifyVec3 A ε hε) x =
      spatialMollifyVec3 (curlOfGradient G) ε hε x := by
  have hderiv (i k : Fin 3) :
      spatialDeriv (fun y => spatialMollifyVec3 A ε hε y i) k x =
        CKN.mollify (fun y => G y i k) ε hε x := by
    exact CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn
      isOpen_univ
      ((hA.eval i).locallyIntegrable (by norm_num))
      (((hG.eval i).eval k).locallyIntegrable (by norm_num)) (hweak i k) hε
      (by intro y hy; trivial)
  funext i
  fin_cases i
  · change spatialDeriv (fun y => spatialMollifyVec3 A ε hε y 2) 1 x -
      spatialDeriv (fun y => spatialMollifyVec3 A ε hε y 1) 2 x =
        CKN.mollify (fun y => curlOfGradient G y 0) ε hε x
    rw [hderiv 2 1, hderiv 1 2]
    change CKN.mollify (fun y => G y 2 1) ε hε x -
      CKN.mollify (fun y => G y 1 2) ε hε x =
        CKN.mollify (fun y => G y 2 1 - G y 1 2) ε hε x
    rw [← cknMollify_sub_of_locallyIntegrable
      (((hG.eval 2).eval 1).locallyIntegrable (by norm_num))
      (((hG.eval 1).eval 2).locallyIntegrable (by norm_num)) hε x]
  · change spatialDeriv (fun y => spatialMollifyVec3 A ε hε y 0) 2 x -
      spatialDeriv (fun y => spatialMollifyVec3 A ε hε y 2) 0 x =
        CKN.mollify (fun y => curlOfGradient G y 1) ε hε x
    rw [hderiv 0 2, hderiv 2 0]
    change CKN.mollify (fun y => G y 0 2) ε hε x -
      CKN.mollify (fun y => G y 2 0) ε hε x =
        CKN.mollify (fun y => G y 0 2 - G y 2 0) ε hε x
    rw [← cknMollify_sub_of_locallyIntegrable
      (((hG.eval 0).eval 2).locallyIntegrable (by norm_num))
      (((hG.eval 2).eval 0).locallyIntegrable (by norm_num)) hε x]
  · change spatialDeriv (fun y => spatialMollifyVec3 A ε hε y 1) 0 x -
      spatialDeriv (fun y => spatialMollifyVec3 A ε hε y 0) 1 x =
        CKN.mollify (fun y => curlOfGradient G y 2) ε hε x
    rw [hderiv 1 0, hderiv 0 1]
    change CKN.mollify (fun y => G y 1 0) ε hε x -
      CKN.mollify (fun y => G y 0 1) ε hε x =
        CKN.mollify (fun y => G y 1 0 - G y 0 1) ε hε x
    rw [← cknMollify_sub_of_locallyIntegrable
      (((hG.eval 1).eval 0).locallyIntegrable (by norm_num))
      (((hG.eval 0).eval 1).locallyIntegrable (by norm_num)) hε x]

private theorem regularizedPotentialEntry_lineDeriv
    (δ : ℝ) (k j : Fin 3) (f : Lp (α := L2Vec3) ℂ 2) :
    ∂_{l2BasisVec3 k}
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
          (f : 𝓢'(L2Vec3, ℂ))) =
      ((2 * Real.pi : ℂ) * Complex.I) •
        TemperedDistribution.fourierMultiplierCLM ℂ
          (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord k ξ))
          (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
            (f : 𝓢'(L2Vec3, ℂ))) := by
  rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM]
  congr 2
  congr 1
  funext ξ
  simp [l2BasisVec3, frequencyL2Coord, PiLp.proj_apply, PiLp.inner_apply]

private theorem regularizedPotentialComponentLp_toDist_zero
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) :
    ((regularizedPotentialComponentLp ha δ hδ 0 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 1)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ)) -
    TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 2)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (regularizedPotentialEntryApply δ hδ 1
      (𝓕 (weakFieldFourierComponent ha 2)) -
    regularizedPotentialEntryApply δ hδ 2
      (𝓕 (weakFieldFourierComponent ha 1))) : Lp (α := L2Vec3) ℂ 2
      (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  rw [inverseFourierLp_sub_toTemperedDistribution,
    inverseFourier_regularizedPotentialEntryApply_toTemperedDistribution,
    inverseFourier_regularizedPotentialEntryApply_toTemperedDistribution]

private theorem regularizedPotentialComponentLp_toDist_one
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) :
    ((regularizedPotentialComponentLp ha δ hδ 1 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 2)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 0)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (regularizedPotentialEntryApply δ hδ 2
      (𝓕 (weakFieldFourierComponent ha 0)) -
    regularizedPotentialEntryApply δ hδ 0
      (𝓕 (weakFieldFourierComponent ha 2))) : Lp (α := L2Vec3) ℂ 2
      (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  rw [inverseFourierLp_sub_toTemperedDistribution,
    inverseFourier_regularizedPotentialEntryApply_toTemperedDistribution,
    inverseFourier_regularizedPotentialEntryApply_toTemperedDistribution]

private theorem regularizedPotentialComponentLp_toDist_two
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) :
    ((regularizedPotentialComponentLp ha δ hδ 2 :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 0)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 1)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (regularizedPotentialEntryApply δ hδ 0
      (𝓕 (weakFieldFourierComponent ha 1)) -
    regularizedPotentialEntryApply δ hδ 1
      (𝓕 (weakFieldFourierComponent ha 0))) : Lp (α := L2Vec3) ℂ 2
      (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  rw [inverseFourierLp_sub_toTemperedDistribution,
    inverseFourier_regularizedPotentialEntryApply_toTemperedDistribution,
    inverseFourier_regularizedPotentialEntryApply_toTemperedDistribution]

/-- Distributional formula for the first coordinate of the regularized potential derivative. -/
theorem regularizedPotentialDerivativeComponentLp_toDist_zero
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (k : Fin 3) :
    ((regularizedPotentialDerivativeComponentLp ha δ hδ 0 k :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k 1)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k 2)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (regularizedDerivativeEntryApply δ k 1
      (𝓕 (weakFieldFourierComponent ha 2)) -
    regularizedDerivativeEntryApply δ k 2
      (𝓕 (weakFieldFourierComponent ha 1))) : Lp (α := L2Vec3) ℂ 2
      (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  rw [inverseFourierLp_sub_toTemperedDistribution,
    inverseFourier_regularizedDerivativeEntryApply_toTemperedDistribution,
    inverseFourier_regularizedDerivativeEntryApply_toTemperedDistribution]

/-- Distributional formula for the second coordinate of the regularized potential derivative. -/
theorem regularizedPotentialDerivativeComponentLp_toDist_one
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (k : Fin 3) :
    ((regularizedPotentialDerivativeComponentLp ha δ hδ 1 k :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k 2)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k 0)
          (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (regularizedDerivativeEntryApply δ k 2
      (𝓕 (weakFieldFourierComponent ha 0)) -
    regularizedDerivativeEntryApply δ k 0
      (𝓕 (weakFieldFourierComponent ha 2))) : Lp (α := L2Vec3) ℂ 2
      (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  rw [inverseFourierLp_sub_toTemperedDistribution,
    inverseFourier_regularizedDerivativeEntryApply_toTemperedDistribution,
    inverseFourier_regularizedDerivativeEntryApply_toTemperedDistribution]

/-- Distributional formula for the third coordinate of the regularized potential derivative. -/
theorem regularizedPotentialDerivativeComponentLp_toDist_two
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (k : Fin 3) :
    ((regularizedPotentialDerivativeComponentLp ha δ hδ 2 k :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k 0)
          (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ)) -
        TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k 1)
          (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ)) := by
  change ((𝓕⁻ (regularizedDerivativeEntryApply δ k 0
      (𝓕 (weakFieldFourierComponent ha 1)) -
    regularizedDerivativeEntryApply δ k 1
      (𝓕 (weakFieldFourierComponent ha 0))) : Lp (α := L2Vec3) ℂ 2
      (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) = _
  rw [inverseFourierLp_sub_toTemperedDistribution,
    inverseFourier_regularizedDerivativeEntryApply_toTemperedDistribution,
    inverseFourier_regularizedDerivativeEntryApply_toTemperedDistribution]

private theorem regularizedDerivativeEntry_is_distDeriv
    (δ : ℝ) (hδ : 0 < δ) (k j : Fin 3)
    (f : Lp (α := L2Vec3) ℂ 2) :
    TemperedDistribution.fourierMultiplierCLM ℂ (regularizedDerivativeEntry δ k j)
        (f : 𝓢'(L2Vec3, ℂ)) =
      ∂_{l2BasisVec3 k}
        (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
          (f : 𝓢'(L2Vec3, ℂ))) := by
  calc
    _ = ((2 * Real.pi : ℂ) * Complex.I) •
        TemperedDistribution.fourierMultiplierCLM ℂ
          (fun ξ : L2Vec3 => Complex.ofReal (frequencyL2Coord k ξ))
          (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ j)
            (f : 𝓢'(L2Vec3, ℂ))) :=
      regularizedDerivativeEntry_fourierMultiplier_eq δ hδ k j f
    _ = _ := (regularizedPotentialEntry_lineDeriv δ k j f).symm

/-- The regularized potential derivatives are its distributional first derivatives. -/
theorem regularizedPotentialComponentLp_is_weakDeriv
    {a : Vec3 → Vec3} (ha : MemLp a (2 : ℝ≥0∞) volume)
    (δ : ℝ) (hδ : 0 < δ) (i k : Fin 3) :
    ((regularizedPotentialDerivativeComponentLp ha δ hδ i k :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) :
        𝓢'(L2Vec3, ℂ)) =
      ∂_{l2BasisVec3 k}
        ((regularizedPotentialComponentLp ha δ hδ i :
          Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) :
            𝓢'(L2Vec3, ℂ)) := by
  fin_cases i
  · change ((regularizedPotentialDerivativeComponentLp ha δ hδ 0 k :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      ∂_{l2BasisVec3 k}
        ((regularizedPotentialComponentLp ha δ hδ 0 :
          Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ))
    rw [regularizedPotentialDerivativeComponentLp_toDist_zero ha δ hδ k,
      regularizedPotentialComponentLp_toDist_zero ha δ hδ]
    calc
      _ = ∂_{l2BasisVec3 k}
            (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 1)
              (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ))) -
          ∂_{l2BasisVec3 k}
            (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 2)
              (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ))) := by
        rw [regularizedDerivativeEntry_is_distDeriv δ hδ k 1,
          regularizedDerivativeEntry_is_distDeriv δ hδ k 2]
      _ = _ :=
        (temperedDistribution_lineDeriv_sub (l2BasisVec3 k) _ _).symm
  · change ((regularizedPotentialDerivativeComponentLp ha δ hδ 1 k :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      ∂_{l2BasisVec3 k}
        ((regularizedPotentialComponentLp ha δ hδ 1 :
          Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ))
    rw [regularizedPotentialDerivativeComponentLp_toDist_one ha δ hδ k,
      regularizedPotentialComponentLp_toDist_one ha δ hδ]
    calc
      _ = ∂_{l2BasisVec3 k}
            (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 2)
              (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ))) -
          ∂_{l2BasisVec3 k}
            (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 0)
              (weakFieldFourierComponent ha 2 : 𝓢'(L2Vec3, ℂ))) := by
        rw [regularizedDerivativeEntry_is_distDeriv δ hδ k 2,
          regularizedDerivativeEntry_is_distDeriv δ hδ k 0]
      _ = _ :=
        (temperedDistribution_lineDeriv_sub (l2BasisVec3 k) _ _).symm
  · change ((regularizedPotentialDerivativeComponentLp ha δ hδ 2 k :
      Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ)) =
      ∂_{l2BasisVec3 k}
        ((regularizedPotentialComponentLp ha δ hδ 2 :
          Lp (α := L2Vec3) ℂ 2 (volume : Measure L2Vec3)) : 𝓢'(L2Vec3, ℂ))
    rw [regularizedPotentialDerivativeComponentLp_toDist_two ha δ hδ k,
      regularizedPotentialComponentLp_toDist_two ha δ hδ]
    calc
      _ = ∂_{l2BasisVec3 k}
            (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 0)
              (weakFieldFourierComponent ha 1 : 𝓢'(L2Vec3, ℂ))) -
          ∂_{l2BasisVec3 k}
            (TemperedDistribution.fourierMultiplierCLM ℂ (regularizedPotentialEntry δ 1)
              (weakFieldFourierComponent ha 0 : 𝓢'(L2Vec3, ℂ))) := by
        rw [regularizedDerivativeEntry_is_distDeriv δ hδ k 0,
          regularizedDerivativeEntry_is_distDeriv δ hδ k 1]
      _ = _ :=
        (temperedDistribution_lineDeriv_sub (l2BasisVec3 k) _ _).symm


end CKN

end
