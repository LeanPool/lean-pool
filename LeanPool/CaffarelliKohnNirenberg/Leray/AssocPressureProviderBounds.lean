/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureProviderIntegrand

/-!
# Helmholtz cutoff derivative bounds

Common spatial profiles bound derivatives of the compact Helmholtz tests.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

private theorem associatedPressureTimePartialProd_eq_zero_of_timeSupport
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x, f (x, t) = 0)
    {z : Vec3 × ℝ} (ht : z.2 ∉ K) :
    CKN.timePartialProd f z = 0 := by
  have hO : IsOpen ((Set.univ : Set Vec3) ×ˢ Kᶜ) :=
    isOpen_univ.prod hK.isOpen_compl
  have hnear : ((Set.univ : Set Vec3) ×ˢ Kᶜ) ∈ 𝓝 z :=
    hO.mem_nhds ⟨Set.mem_univ _, ht⟩
  have hlocal : f =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with q hq
    exact hzero q.2 hq.2 q.1
  have hfd : HasFDerivAt f (0 : (Vec3 × ℝ) →L[ℝ] ℝ) z :=
    hasFDerivAt_zero_of_eventually_const 0 hlocal
  have hdiff : DifferentiableAt ℝ f z := (hf.differentiable (by simp)) z
  change CKN.timePartial f z = 0
  rw [CKN.timePartial_eq_product_fderiv hdiff, hfd.fderiv]
  simp

/-- Decay coefficient for the potential gradient after multiplying by a spatial cutoff. -/
@[expose]
def associatedPressurePotentialDirectionCutoffCoefficient
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ) : ℝ :=
  Classical.choose hdecay.gradient_bound +
    CKN.cutoffGradientConstant * Classical.choose hdecay.value_bound

/-- Decay coefficient for the potential Hessian after multiplying by a spatial cutoff. -/
@[expose]
def associatedPressurePotentialHessianCutoffCoefficient
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ) : ℝ :=
  2 * Classical.choose hdecay.hessian_bound +
    6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
    9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound

private theorem associatedPressurePotentialDirectionCutoffCoefficient_nonneg
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ)
    (hgrad : 0 ≤ CKN.cutoffGradientConstant) :
    0 ≤ associatedPressurePotentialDirectionCutoffCoefficient hdecay := by
  have h0 : 0 ≤ Classical.choose hdecay.value_bound :=
    (Classical.choose_spec hdecay.value_bound).1
  have h1 : 0 ≤ Classical.choose hdecay.gradient_bound :=
    (Classical.choose_spec hdecay.gradient_bound).1
  exact add_nonneg h1 (mul_nonneg hgrad h0)

private theorem associatedPressurePotentialHessianCutoffCoefficient_nonneg
    {ψ : Vec3 × ℝ → ℝ} (hdecay : RieszPressurePotentialDecay ψ)
    (hgrad : 0 ≤ CKN.cutoffGradientConstant)
    (hsecond : 0 ≤ CKN.cutoffSecondDerivativeConstant) :
    0 ≤ associatedPressurePotentialHessianCutoffCoefficient hdecay := by
  have h0 : 0 ≤ Classical.choose hdecay.value_bound :=
    (Classical.choose_spec hdecay.value_bound).1
  have h1 : 0 ≤ Classical.choose hdecay.gradient_bound :=
    (Classical.choose_spec hdecay.gradient_bound).1
  have h2 : 0 ≤ Classical.choose hdecay.hessian_bound :=
    (Classical.choose_spec hdecay.hessian_bound).1
  dsimp [associatedPressurePotentialHessianCutoffCoefficient]
  positivity

private theorem associatedPressureJointDirection_eq_spatialPartialProd
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 3) :
    rieszPressureJointDirection f i = CKN.spatialPartialProd f i := by
  funext z
  exact (rieszPressure_sliceSpatialDeriv_eq_joint hf i z).symm

private theorem associatedPressureSpatialSecondPartialProd_eq_jointHessian
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialSecondPartialProd f i j z =
      rieszPressureJointHessian f i j z := by
  change CKN.mixedSecond (fun x : Vec3 => f (x, z.2)) j i z.1 = _
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => f (x, z.2)) :=
    hf.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  calc
    CKN.mixedSecond (fun x : Vec3 => f (x, z.2)) j i z.1 =
        CKN.mixedSecond (fun x : Vec3 => f (x, z.2)) i j z.1 :=
      CKN.mixedSecond_swap hslice j i z.1
    _ = rieszPressureJointHessian f i j z :=
      rieszPressure_sliceMixedSecond_eq_joint hf i j z

private theorem associatedPressureCutoffJointDirection_eq_vorticityPartial
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 3) (n : ℕ) (z : Vec3 × ℝ) :
    rieszPressureJointDirection (rieszPressurePotentialCutoffTest f n) i z =
      associatedPressureTestPartial
        (fun q => rieszPressurePotentialCutoff n q.1 * f q) i z := by
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoffTest f n) :=
    rieszPressurePotentialCutoffTest_contDiff hf n
  have hdir := congrFun
    (associatedPressureJointDirection_eq_spatialPartialProd hcut i) z
  calc
    rieszPressureJointDirection (rieszPressurePotentialCutoffTest f n) i z =
        CKN.spatialPartialProd (rieszPressurePotentialCutoffTest f n) i z := hdir
    _ = associatedPressureTestPartial
        (fun q => rieszPressurePotentialCutoff n q.1 * f q) i z := by
      rw [associatedPressureTestPartial_eq_spatialPartial]
      rfl

private theorem associatedPressureTestCurl_spatialPartial_formula
    {A : Vec3 × ℝ → Vec3} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j z =
      match i with
      | 0 => CKN.spatialSecondPartialProd (fun q => A q 2) 1 j z -
          CKN.spatialSecondPartialProd (fun q => A q 1) 2 j z
      | 1 => CKN.spatialSecondPartialProd (fun q => A q 0) 2 j z -
          CKN.spatialSecondPartialProd (fun q => A q 2) 0 j z
      | 2 => CKN.spatialSecondPartialProd (fun q => A q 1) 0 j z -
          CKN.spatialSecondPartialProd (fun q => A q 0) 1 j z := by
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hpart (k l : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => associatedPressureTestPartial (fun w => A w k) l q) := by
    have h := CKN.spatialPartial_contDiff (hAcomp k) l
    convert h using 1
    funext q
    exact associatedPressureTestPartial_eq_spatialPartial (fun w => A w k) l q
  fin_cases i
  · change CKN.spatialPartial
      (fun q => associatedPressureTestPartial (fun w => A w 2) 1 q -
        associatedPressureTestPartial (fun w => A w 1) 2 q) j z = _
    rw [CKN.spatialPartial_sub_at
      ((hpart 2 1).differentiable (by simp) z)
      ((hpart 1 2).differentiable (by simp) z) j]
    rfl
  · change CKN.spatialPartial
      (fun q => associatedPressureTestPartial (fun w => A w 0) 2 q -
        associatedPressureTestPartial (fun w => A w 2) 0 q) j z = _
    rw [CKN.spatialPartial_sub_at
      ((hpart 0 2).differentiable (by simp) z)
      ((hpart 2 0).differentiable (by simp) z) j]
    rfl
  · change CKN.spatialPartial
      (fun q => associatedPressureTestPartial (fun w => A w 1) 0 q -
        associatedPressureTestPartial (fun w => A w 0) 1 q) j z = _
    rw [CKN.spatialPartial_sub_at
      ((hpart 1 0).differentiable (by simp) z)
      ((hpart 0 1).differentiable (by simp) z) j]
    rfl

private theorem associatedPressureCurlComponent_bound
    (d : Fin 3 → Fin 3 → ℝ) (C : Fin 3 → ℝ) (P : ℝ)
    (hC : ∀ k, 0 ≤ C k) (hP : 0 ≤ P)
    (hterm : ∀ k l, |d k l| ≤ C k * P) :
    ∀ i : Fin 3,
      |(match i with
        | 0 => d 2 1 - d 1 2
        | 1 => d 0 2 - d 2 0
        | 2 => d 1 0 - d 0 1)| ≤ 2 * (∑ k : Fin 3, C k) * P := by
  intro i
  have hsum (k l : Fin 3) : C k + C l ≤ 2 * (∑ m : Fin 3, C m) := by
    calc
      _ ≤ (∑ m : Fin 3, C m) + (∑ m : Fin 3, C m) :=
        add_le_add
          (Finset.single_le_sum (fun m hm => hC m) (Finset.mem_univ k))
          (Finset.single_le_sum (fun m hm => hC m) (Finset.mem_univ l))
      _ = _ := by ring
  fin_cases i
  · calc
      |d 2 1 - d 1 2| ≤ |d 2 1| + |d 1 2| := associatedPressureAbs_sub_le _ _
      _ ≤ (C 2 + C 1) * P := by
        calc
          _ ≤ C 2 * P + C 1 * P := add_le_add (hterm 2 1) (hterm 1 2)
          _ = _ := by ring
      _ ≤ 2 * (∑ k : Fin 3, C k) * P := mul_le_mul_of_nonneg_right (hsum 2 1) hP
  · calc
      |d 0 2 - d 2 0| ≤ |d 0 2| + |d 2 0| := associatedPressureAbs_sub_le _ _
      _ ≤ (C 0 + C 2) * P := by
        calc
          _ ≤ C 0 * P + C 2 * P := add_le_add (hterm 0 2) (hterm 2 0)
          _ = _ := by ring
      _ ≤ 2 * (∑ k : Fin 3, C k) * P := mul_le_mul_of_nonneg_right (hsum 0 2) hP
  · calc
      |d 1 0 - d 0 1| ≤ |d 1 0| + |d 0 1| := associatedPressureAbs_sub_le _ _
      _ ≤ (C 1 + C 0) * P := by
        calc
          _ ≤ C 1 * P + C 0 * P := add_le_add (hterm 1 0) (hterm 0 1)
          _ = _ := by ring
      _ ≤ 2 * (∑ k : Fin 3, C k) * P := mul_le_mul_of_nonneg_right (hsum 1 0) hP

private theorem associatedPressureSpatialProfile_nonneg (K : Set ℝ) (z : Vec3 × ℝ) :
    0 ≤ associatedPressureSpatialProfile K 2 z := by
  by_cases ht : z.2 ∈ K
  · simp only [associatedPressureSpatialProfile, Set.indicator_of_mem ht, one_mul]
    positivity
  · simp only [associatedPressureSpatialProfile, Set.indicator_of_notMem ht, zero_mul, le_refl]

private theorem associatedPressurePotentialCutoff_direction_bound
    {K : Set ℝ} (f : Vec3 × ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hzero : ∀ t ∉ K, ∀ x, f (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay f) (i : Fin 3) (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressureJointDirection (rieszPressurePotentialCutoffTest f n) i z| ≤
      associatedPressurePotentialDirectionCutoffCoefficient hdecay *
        associatedPressureSpatialProfile K 2 z :=
  associatedPressurePotentialCutoff_direction_profile_bound hf hzero hdecay i n z

private theorem associatedPressurePotentialCutoff_hessian_bound
    {K : Set ℝ} (f : Vec3 × ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hzero : ∀ t ∉ K, ∀ x, f (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay f) (i j : Fin 3) (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressureJointHessian (rieszPressurePotentialCutoffTest f n) i j z| ≤
      associatedPressurePotentialHessianCutoffCoefficient hdecay *
        associatedPressureSpatialProfile K 2 z := by
  simpa [associatedPressurePotentialHessianCutoffCoefficient] using
    associatedPressurePotentialCutoff_hessian_profile_bound hf hzero hdecay i j n z

private theorem associatedPressureHelmholtzScalarCutoff_derivative_bounds
    {T : ℝ} {φ : Vec3 × ℝ → Vec3} {K : Set ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (hzeroψ : ∀ t ∉ K, ∀ x, associatedPressureHelmholtzScalarPotential φ (x, t) = 0)
    (hzeroψt : ∀ t ∉ K, ∀ x,
      CKN.timePartialProd (associatedPressureHelmholtzScalarPotential φ) (x, t) = 0)
    (hψdecay : RieszPressurePotentialDecay (associatedPressureHelmholtzScalarPotential φ))
    (hψtdecay : RieszPressurePotentialDecay
      (CKN.timePartialProd (associatedPressureHelmholtzScalarPotential φ))) :
    (∀ (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ),
      |CKN.timePartialProd (CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) i) z| ≤
        associatedPressurePotentialDirectionCutoffCoefficient hψtdecay *
          associatedPressureSpatialProfile K 2 z) ∧
    (∀ (n : ℕ) (i j : Fin 3) (z : Vec3 × ℝ),
      |CKN.spatialPartialProd (fun q => associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) q i) j z| ≤
        associatedPressurePotentialHessianCutoffCoefficient hψdecay *
          associatedPressureSpatialProfile K 2 z) := by
  let ψ := associatedPressureHelmholtzScalarPotential φ
  let ψt := CKN.timePartialProd ψ
  let Dψt := associatedPressurePotentialDirectionCutoffCoefficient hψtdecay
  let Hψ := associatedPressurePotentialHessianCutoffCoefficient hψdecay
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hψt : ContDiff ℝ (⊤ : ℕ∞) ψt := CKN.contDiff_timePartial hψ
  have htimeScalar (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ) :
      |CKN.timePartialProd (CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) i) z| ≤
        Dψt * associatedPressureSpatialProfile K 2 z := by
    have hψcut : ContDiff ℝ (⊤ : ℕ∞)
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) :=
      (associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction hφ n).1
    have htimeCut : CKN.timePartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) =
          rieszPressurePotentialCutoffTest ψt n := by
      change CKN.timePartialProd (rieszPressurePotentialCutoffTest ψ n) = _
      rw [associatedPressureCutoffTimePartial_eq hψ n]
    calc
      _ = |CKN.spatialPartialProd
          (CKN.timePartialProd
            (associatedPressureHelmholtzScalarPotentialCutoff φ n)) i z| := by
          rw [associatedPressureTimeSpatialPartialProd_commute hψcut i z]
      _ = |CKN.spatialPartialProd
          (rieszPressurePotentialCutoffTest ψt n) i z| := by rw [htimeCut]
      _ = |rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest ψt n) i z| := by
          congr 1
          exact (congrFun
            (associatedPressureJointDirection_eq_spatialPartialProd
              (rieszPressurePotentialCutoffTest_contDiff hψt n) i) z).symm
      _ ≤ Dψt * associatedPressureSpatialProfile K 2 z := by
          exact
            associatedPressurePotentialCutoff_direction_bound ψt hψt hzeroψt hψtdecay i n z
  have hspaceScalar (n : ℕ) (i j : Fin 3) (z : Vec3 × ℝ) :
      |CKN.spatialPartialProd
        (fun q => associatedPressureTestGradient
          (associatedPressureHelmholtzScalarPotentialCutoff φ n) q i) j z| ≤
        Hψ * associatedPressureSpatialProfile K 2 z := by
    let ψcut := associatedPressureHelmholtzScalarPotentialCutoff φ n
    have hψcut : ContDiff ℝ (⊤ : ℕ∞) ψcut :=
      (associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction hφ n).1
    have hEq := associatedPressureSpatialSecondPartialProd_eq_jointHessian hψcut i j z
    have hBound :=
      associatedPressurePotentialCutoff_hessian_bound ψ hψ hzeroψ hψdecay i j n z
    have hCutEq : ψcut = rieszPressurePotentialCutoffTest ψ n := by
      rfl
    calc
      _ = |CKN.spatialSecondPartialProd ψcut i j z| := by
        rfl
      _ = |rieszPressureJointHessian ψcut i j z| := by rw [hEq]
      _ = |rieszPressureJointHessian
          (rieszPressurePotentialCutoffTest ψ n) i j z| := by rw [hCutEq]
      _ ≤ Hψ * associatedPressureSpatialProfile K 2 z := hBound
  exact ⟨htimeScalar, hspaceScalar⟩

private theorem associatedPressureHelmholtzCutoffCurl_derivative_bounds
    {T : ℝ} {φ : Vec3 × ℝ → Vec3} {K : Set ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (hGradC : 0 ≤ CKN.cutoffGradientConstant)
    (hHessC : 0 ≤ CKN.cutoffSecondDerivativeConstant)
    (hzeroA : ∀ (i : Fin 3) (t : ℝ), t ∉ K → ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) i = 0)
    (hzeroAt : ∀ (i : Fin 3) (t : ℝ), t ∉ K → ∀ x,
      associatedPressureHelmholtzVectorPotentialTimePartial φ (x, t) i = 0)
    (hAdecay : ∀ i : Fin 3, RieszPressurePotentialDecay
      (fun q => associatedPressureHelmholtzVectorPotential φ q i))
    (hAtdecay : ∀ i : Fin 3, RieszPressurePotentialDecay
      (fun q => associatedPressureHelmholtzVectorPotentialTimePartial φ q i)) :
    (∀ (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ),
      |CKN.timePartialProd (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) z| ≤
        (2 * (∑ k : Fin 3, associatedPressurePotentialDirectionCutoffCoefficient
          (hAtdecay k))) * associatedPressureSpatialProfile K 2 z) ∧
    (∀ (n : ℕ) (i j : Fin 3) (z : Vec3 × ℝ),
      |CKN.spatialPartialProd (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j z| ≤
        (2 * (∑ k : Fin 3, associatedPressurePotentialHessianCutoffCoefficient
          (hAdecay k))) * associatedPressureSpatialProfile K 2 z) := by
  let A := associatedPressureHelmholtzVectorPotential φ
  let At := associatedPressureHelmholtzVectorPotentialTimePartial φ
  let DA (i : Fin 3) := associatedPressurePotentialDirectionCutoffCoefficient (hAtdecay i)
  let HA (i : Fin 3) := associatedPressurePotentialHessianCutoffCoefficient (hAdecay i)
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q i) :=
    (contDiff_apply ℝ ℝ i).comp hA
  have hAtcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => At q i) := by
    simpa [At, associatedPressureHelmholtzVectorPotentialTimePartial,
      CKN.timePartialProd] using CKN.contDiff_timePartial (hAcomp i)
  have hDA (i : Fin 3) : 0 ≤ DA i :=
    associatedPressurePotentialDirectionCutoffCoefficient_nonneg (hAtdecay i) hGradC
  have hHA (i : Fin 3) : 0 ≤ HA i :=
    associatedPressurePotentialHessianCutoffCoefficient_nonneg (hAdecay i) hGradC hHessC
  have hprofile (z : Vec3 × ℝ) : 0 ≤ associatedPressureSpatialProfile K 2 z :=
    associatedPressureSpatialProfile_nonneg K z
  have hcurlTimeFormula (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ) :
      CKN.timePartialProd
        (fun q => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) z =
        associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 • At q) z i := by
    have h := associatedPressureHelmholtzCutoffCurl_timePartial_eq hφ n i z
    convert h using 1
    rfl
  have hdir (n : ℕ) (z : Vec3 × ℝ) (k l : Fin 3) :
      |associatedPressureTestPartial
        (fun q => rieszPressurePotentialCutoff n q.1 * At q k) l z| ≤
        DA k * associatedPressureSpatialProfile K 2 z := by
    have hb :=
      associatedPressurePotentialCutoff_direction_bound (fun q => At q k) (hAtcomp k)
      (hzeroAt k) (hAtdecay k) l n z
    have heq := associatedPressureCutoffJointDirection_eq_vorticityPartial
      (hAtcomp k) l n z
    rw [heq] at hb
    simpa [DA] using hb
  have hcurlTime (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ) :
      |CKN.timePartialProd
        (fun q => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) z| ≤
        (2 * (∑ k : Fin 3, DA k)) * associatedPressureSpatialProfile K 2 z := by
    rw [hcurlTimeFormula]
    have hbound := associatedPressureCurlComponent_bound
      (fun k l => associatedPressureTestPartial
        (fun q => rieszPressurePotentialCutoff n q.1 * At q k) l z)
      DA (associatedPressureSpatialProfile K 2 z) hDA (hprofile z)
      (fun k l => hdir n z k l) i
    fin_cases i <;>
      simpa only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        associatedPressureTestCurl_zero, associatedPressureTestCurl_one,
        associatedPressureTestCurl_two, Pi.smul_apply, smul_eq_mul] using hbound
  have hcurlSpatial (n : ℕ) (i j : Fin 3) (z : Vec3 × ℝ) :
      |CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j z| ≤
        (2 * (∑ k : Fin 3, HA k)) * associatedPressureSpatialProfile K 2 z := by
    let Ac := associatedPressureHelmholtzCutoffVectorPotential φ n
    have hAc : ContDiff ℝ (⊤ : ℕ∞) Ac :=
      (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1
    have hAcComp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => Ac q k) :=
      (contDiff_apply ℝ ℝ k).comp hAc
    have hterm (k l : Fin 3) :
        |CKN.spatialSecondPartialProd (fun q => Ac q k) l j z| ≤
          HA k * associatedPressureSpatialProfile K 2 z := by
      have hEq := associatedPressureSpatialSecondPartialProd_eq_jointHessian
        (hAcComp k) l j z
      have hBound :=
        associatedPressurePotentialCutoff_hessian_bound (fun q => A q k) (hAcomp k)
        (hzeroA k) (hAdecay k) l j n z
      calc
        _ = |rieszPressureJointHessian (fun q => Ac q k) l j z| := by rw [hEq]
        _ = |rieszPressureJointHessian
            (rieszPressurePotentialCutoffTest (fun q => A q k) n) l j z| := rfl
        _ ≤ HA k * associatedPressureSpatialProfile K 2 z := by simpa [HA] using hBound
    rw [associatedPressureTestCurl_spatialPartial_formula hAc i j z]
    exact associatedPressureCurlComponent_bound
      (fun k l => CKN.spatialSecondPartialProd (fun q => Ac q k) l j z)
      HA (associatedPressureSpatialProfile K 2 z) hHA (hprofile z) hterm i
  exact ⟨hcurlTime, hcurlSpatial⟩

/-- The Helmholtz cutoffs and both Helmholtz components have common spatial
derivative profiles for `thm:assoc-pressure`. -/
theorem associatedPressureHelmholtzTestCutoff_derivative_profile_bounds
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo 0 T ∧
      ∃ C ≥ 0, ∀ (n : ℕ) (z : Vec3 × ℝ) (i j : Fin 3),
        |CKN.timePartialProd
          (fun q => associatedPressureHelmholtzTestCutoff φ n q i) z| ≤
            C * associatedPressureSpatialProfile K 2 z ∧
        |CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzTestCutoff φ n q i) j z| ≤
            C * associatedPressureSpatialProfile K 2 z := by
  let ψ := associatedPressureHelmholtzScalarPotential φ
  let A := associatedPressureHelmholtzVectorPotential φ
  let At := associatedPressureHelmholtzVectorPotentialTimePartial φ
  let φt := associatedPressureVectorTimePartial φ
  let ψt := CKN.timePartialProd ψ
  let K : Set ℝ := (tsupport φ).image Prod.snd
  have hK : IsCompact K := hφ.2.1.isCompact.image continuous_snd
  have hKsub : K ⊆ Ioo 0 T := by
    rintro t ⟨z, hz, rfl⟩
    exact hφ.2.2 hz |>.2
  refine ⟨K, hK, hKsub, ?_⟩
  have hzeroψ (t : ℝ) (ht : t ∉ K) (x : Vec3) : ψ (x, t) = 0 :=
    (associatedPressureHelmholtzPotentials_zero_off_time_support
      (by simpa [K] using ht) x).1
  have hzeroA (i : Fin 3) (t : ℝ) (ht : t ∉ K) (x : Vec3) : A (x, t) i = 0 :=
    congrArg (fun w : Vec3 => w i)
      (associatedPressureHelmholtzPotentials_zero_off_time_support
        (by simpa [K] using ht) x).2
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hψdecay : RieszPressurePotentialDecay ψ :=
    associatedPressureHelmholtzScalarPotential_decay hφ
  have hφt : φt ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
    exact associatedPressureVectorTimePartial_mem_spaceTimeTestFunction hφ
  have hψtSourceEq : ψt = associatedPressureHelmholtzScalarPotential φt := by
    funext q
    have h := associatedPressureHelmholtzScalarPotential_timePartial hφ q
    simpa [ψ, ψt, φt, CKN.timePartialProd] using h
  have hψtdecay : RieszPressurePotentialDecay ψt := by
    rw [hψtSourceEq]
    exact associatedPressureHelmholtzScalarPotential_decay hφt
  have hzeroψt (t : ℝ) (ht : t ∉ K) (x : Vec3) : ψt (x, t) = 0 := by
    exact associatedPressureTimePartialProd_eq_zero_of_timeSupport hψ hK.isClosed
      hzeroψ (show (x, t).2 ∉ K from ht)
  have hAcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q i) :=
    (contDiff_apply ℝ ℝ i).comp hA
  have hAdecay (i : Fin 3) : RieszPressurePotentialDecay (fun q => A q i) :=
    (associatedPressureHelmholtzVectorPotential_component_decay hφ i).1
  have hAtdecay (i : Fin 3) : RieszPressurePotentialDecay (fun q => At q i) := by
    have h := (associatedPressureHelmholtzVectorPotential_component_decay hφ i).2
    simpa [At, associatedPressureHelmholtzVectorPotentialTimePartial] using h
  have hzeroAt (i : Fin 3) (t : ℝ) (ht : t ∉ K) (x : Vec3) : At (x, t) i = 0 := by
    exact associatedPressureTimePartialProd_eq_zero_of_timeSupport (hAcomp i) hK.isClosed
      (hzeroA i) (show (x, t).2 ∉ K from ht)
  have hGradC : 0 ≤ CKN.cutoffGradientConstant := by
    have hg := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    have h := le_trans (CKN.vecEuclideanNorm_nonneg _) hg
    simpa using h
  have hHessC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
    have hh := CKN.mollifiedBallCutoff_second_derivative_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    have h := le_trans (norm_nonneg _) hh
    simpa using h
  let Dψt := associatedPressurePotentialDirectionCutoffCoefficient hψtdecay
  let Hψ := associatedPressurePotentialHessianCutoffCoefficient hψdecay
  let DA (i : Fin 3) := associatedPressurePotentialDirectionCutoffCoefficient (hAtdecay i)
  let HA (i : Fin 3) := associatedPressurePotentialHessianCutoffCoefficient (hAdecay i)
  have hDψt : 0 ≤ Dψt := by
    exact associatedPressurePotentialDirectionCutoffCoefficient_nonneg hψtdecay hGradC
  have hHψ : 0 ≤ Hψ := by
    exact associatedPressurePotentialHessianCutoffCoefficient_nonneg hψdecay hGradC hHessC
  have hDA (i : Fin 3) : 0 ≤ DA i :=
    associatedPressurePotentialDirectionCutoffCoefficient_nonneg (hAtdecay i) hGradC
  have hHA (i : Fin 3) : 0 ≤ HA i :=
    associatedPressurePotentialHessianCutoffCoefficient_nonneg (hAdecay i) hGradC hHessC
  let Ctime := 1 + 2 * (∑ i : Fin 3, DA i) + Dψt
  let Cspace := 1 + 2 * (∑ i : Fin 3, HA i) + Hψ
  let C := Ctime + Cspace
  have hsumDA : 0 ≤ ∑ i : Fin 3, DA i :=
    Finset.sum_nonneg (fun i hi => hDA i)
  have hsumHA : 0 ≤ ∑ i : Fin 3, HA i :=
    Finset.sum_nonneg (fun i hi => hHA i)
  have hCtime : 0 ≤ Ctime := by
    dsimp [Ctime]
    exact add_nonneg (add_nonneg (by norm_num)
      (mul_nonneg (by norm_num) hsumDA)) hDψt
  have hCspace : 0 ≤ Cspace := by
    dsimp [Cspace]
    exact add_nonneg (add_nonneg (by norm_num)
      (mul_nonneg (by norm_num) hsumHA)) hHψ
  have hC : 0 ≤ C := by dsimp [C]; exact add_nonneg hCtime hCspace
  have hprofile (z : Vec3 × ℝ) : 0 ≤ associatedPressureSpatialProfile K 2 z :=
    associatedPressureSpatialProfile_nonneg K z
  obtain ⟨htimeScalar, hspaceScalar⟩ :=
    associatedPressureHelmholtzScalarCutoff_derivative_bounds
      hφ hzeroψ hzeroψt hψdecay hψtdecay
  obtain ⟨hcurlTime, hcurlSpatial⟩ :=
    associatedPressureHelmholtzCutoffCurl_derivative_bounds
      hφ hGradC hHessC hzeroA hzeroAt hAdecay hAtdecay
  have hVn (n : ℕ) := associatedPressureTestCurl_mem_spaceTimeTestFunction
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n)
  have hGn (n : ℕ) :=
    associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction hφ n
  refine ⟨C, hC, ?_⟩
  intro n z i j
  constructor
  · let v : Vec3 × ℝ → Vec3 :=
      associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φ n)
    let g : Vec3 × ℝ → Vec3 := associatedPressureTestGradient
      (associatedPressureHelmholtzScalarPotentialCutoff φ n)
    have hsum := associatedPressureTimePartialProd_add
      ((contDiff_apply ℝ ℝ i).comp (hVn n).1)
      ((contDiff_apply ℝ ℝ i).comp (hGn n).1) z
    have htime : CKN.timePartialProd
        (fun q => associatedPressureHelmholtzTestCutoff φ n q i) z =
        CKN.timePartialProd (fun q => v q i) z +
          CKN.timePartialProd (fun q => g q i) z := by
      change CKN.timePartialProd (fun q => v q i + g q i) z = _
      exact hsum
    calc
      _ = |CKN.timePartialProd (fun q => v q i) z +
          CKN.timePartialProd (fun q => g q i) z| := congrArg abs htime
      _ ≤ |CKN.timePartialProd (fun q => v q i) z| +
          |CKN.timePartialProd (fun q => g q i) z| := abs_add_le _ _
      _ ≤ (2 * (∑ k : Fin 3, DA k)) * associatedPressureSpatialProfile K 2 z +
          Dψt * associatedPressureSpatialProfile K 2 z :=
        add_le_add (hcurlTime n i z) (htimeScalar n i z)
      _ ≤ C * associatedPressureSpatialProfile K 2 z := by
        calc
          _ = (2 * (∑ k : Fin 3, DA k) + Dψt) *
              associatedPressureSpatialProfile K 2 z := by ring
          _ ≤ Ctime * associatedPressureSpatialProfile K 2 z := by
            apply mul_le_mul_of_nonneg_right _ (hprofile z)
            dsimp [Ctime]
            linarith only [show 0 ≤ (1 : ℝ) by norm_num]
          _ ≤ C * associatedPressureSpatialProfile K 2 z := by
            apply mul_le_mul_of_nonneg_right _ (hprofile z)
            dsimp [C]
            exact le_add_of_nonneg_right hCspace
  · let v : Vec3 × ℝ → Vec3 :=
      associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φ n)
    let g : Vec3 × ℝ → Vec3 := associatedPressureTestGradient
      (associatedPressureHelmholtzScalarPotentialCutoff φ n)
    have hsum := associatedPressureSpatialPartialProd_add
      ((contDiff_apply ℝ ℝ i).comp (hVn n).1)
      ((contDiff_apply ℝ ℝ i).comp (hGn n).1) j z
    have hspace : CKN.spatialPartialProd
        (fun q => associatedPressureHelmholtzTestCutoff φ n q i) j z =
        CKN.spatialPartialProd (fun q => v q i) j z +
          CKN.spatialPartialProd (fun q => g q i) j z := by
      change CKN.spatialPartialProd (fun q => v q i + g q i) j z = _
      exact hsum
    calc
      _ = |CKN.spatialPartialProd (fun q => v q i) j z +
          CKN.spatialPartialProd (fun q => g q i) j z| := congrArg abs hspace
      _ ≤ |CKN.spatialPartialProd (fun q => v q i) j z| +
          |CKN.spatialPartialProd (fun q => g q i) j z| := abs_add_le _ _
      _ ≤ (2 * (∑ k : Fin 3, HA k)) * associatedPressureSpatialProfile K 2 z +
          Hψ * associatedPressureSpatialProfile K 2 z :=
        add_le_add (hcurlSpatial n i j z) (hspaceScalar n i j z)
      _ ≤ C * associatedPressureSpatialProfile K 2 z := by
        calc
          _ = (2 * (∑ k : Fin 3, HA k) + Hψ) *
              associatedPressureSpatialProfile K 2 z := by ring
          _ ≤ Cspace * associatedPressureSpatialProfile K 2 z := by
            apply mul_le_mul_of_nonneg_right _ (hprofile z)
            dsimp [Cspace]
            linarith only [show 0 ≤ (1 : ℝ) by norm_num]
          _ ≤ C * associatedPressureSpatialProfile K 2 z := by
            apply mul_le_mul_of_nonneg_right _ (hprofile z)
            dsimp [C]
            exact le_add_of_nonneg_left hCtime

end CKN.Leray

end
