/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureCompactGradientCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureCompactGradientNonlinear

/-!
# Assoc Pressure Test Cutoff

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open Filter
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatial cutoff of the scalar Newtonian potential in the Helmholtz
decomposition of a compact vector test. -/
@[expose]
def associatedPressureHelmholtzScalarPotentialCutoff
    (φ : Vec3 × ℝ → Vec3) (n : ℕ) : Vec3 × ℝ → ℝ :=
  rieszPressurePotentialCutoffTest (associatedPressureHelmholtzScalarPotential φ) n

private theorem associatedPressureHelmholtzScalarPotential_zero_off_projection
    {φ : Vec3 × ℝ → Vec3}
    {t : ℝ} (ht : t ∉ (tsupport φ).image Prod.snd) (x : Vec3) :
    associatedPressureHelmholtzScalarPotential φ (x, t) = 0 := by
  have hslice (i : Fin 3) : (fun y : Vec3 => φ (y, t) i) = fun _ => (0 : ℝ) := by
    funext y
    have hnot : (y, t) ∉ tsupport φ := by
      intro hz
      exact ht ⟨(y, t), hz, rfl⟩
    have hz := image_eq_zero_of_notMem_tsupport hnot
    exact congrArg (fun w : Vec3 => w i) hz
  have hpartial (i : Fin 3) (y : Vec3) :
      CKN.spatialPartialProd (fun z : Vec3 × ℝ => φ z i) i (y, t) = 0 := by
    change (fderiv ℝ (fun w : Vec3 => φ (w, t) i) y) (CKN.basisVec i) = 0
    rw [hslice i]
    simp
  have hsource : (fun y : Vec3 => associatedPressureTestDivergence φ (y, t)) =
      fun _ => (0 : ℝ) := by
    funext y
    simp [associatedPressureTestDivergence, hpartial]
  rw [associatedPressureHelmholtzScalarPotential,
    associatedPressureNewtonianPotential]
  change CKN.pressureNewtonianPotential
      (fun y : Vec3 => associatedPressureTestDivergence φ (y, t)) x = 0
  rw [hsource]
  simp [CKN.pressureNewtonianPotential]

/-- The cutoff scalar potential is a compactly supported space-time test, with
support inside the original test interval. -/
theorem associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    associatedPressureHelmholtzScalarPotentialCutoff φ n ∈
      CKN.spaceTimeTestFunction (V := ℝ) Set.univ (Ioo 0 T) := by
  let ψ := associatedPressureHelmholtzScalarPotential φ
  let Kφ : Set ℝ := (tsupport φ).image Prod.snd
  obtain ⟨Kψ, hKψ, hzeroψ⟩ :=
    (associatedPressureHelmholtzScalarPotential_decay hφ).timeSupport
  have hKφ : IsCompact Kφ := hφ.2.1.isCompact.image continuous_snd
  have hKφsub : Kφ ⊆ Ioo 0 T := by
    rintro t ⟨z, hz, rfl⟩
    exact hφ.2.2 hz |>.2
  let K : Set ℝ := Kψ ∩ Kφ
  have hK : IsCompact K := hKψ.inter hKφ
  have hKsub : K ⊆ Ioo 0 T := fun t ht => hKφsub ht.2
  have hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0 := by
    intro t ht x
    change ¬ (t ∈ Kψ ∧ t ∈ Kφ) at ht
    by_cases htψ : t ∈ Kψ
    · have htφ : t ∉ Kφ := fun htφ => ht ⟨htψ, htφ⟩
      exact associatedPressureHelmholtzScalarPotential_zero_off_projection
        (by simpa [Kφ] using htφ) x
    · exact hzeroψ t htψ x
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hcutSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzScalarPotentialCutoff φ n) := by
    dsimp [associatedPressureHelmholtzScalarPotentialCutoff, ψ]
    exact rieszPressurePotentialCutoffTest_contDiff hψsmooth n
  have hcutCompact : HasCompactSupport
      (associatedPressureHelmholtzScalarPotentialCutoff φ n) := by
    simpa [associatedPressureHelmholtzScalarPotentialCutoff, ψ] using
      (rieszPressurePotentialCutoffTest_hasCompactSupport hK hzero n)
  have hcutZero : ∀ z : Vec3 × ℝ, z.2 ∉ K →
      associatedPressureHelmholtzScalarPotentialCutoff φ n z = 0 := by
    intro z hz
    simp [associatedPressureHelmholtzScalarPotentialCutoff,
      rieszPressurePotentialCutoffTest, ψ, hzero z.2 hz z.1]
  have hclosed : IsClosed ((Set.univ : Set Vec3) ×ˢ K) :=
    IsClosed.prod isClosed_univ hK.isClosed
  have hsupport : tsupport
      (associatedPressureHelmholtzScalarPotentialCutoff φ n) ⊆
      (Set.univ : Set Vec3) ×ˢ K := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      have ht : z.2 ∉ K := by
        intro hmem
        exact hnot ⟨Set.mem_univ _, hmem⟩
      exact hz (hcutZero z ht)
    · exact hclosed
  refine ⟨hcutSmooth, hcutCompact, ?_⟩
  exact hsupport.trans (Set.prod_mono (Set.subset_univ _) hKsub)

/-- The gradient of the cutoff scalar potential is a compact vector test in
the same time slab. -/
theorem associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
  let ψ := associatedPressureHelmholtzScalarPotentialCutoff φ n
  have hψ := associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction
    hφ n
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureTestGradient ψ) := by
    apply contDiff_pi.2
    intro i
    exact CKN.spatialPartial_contDiff hψ.1 i
  have hcompact : HasCompactSupport (associatedPressureTestGradient ψ) :=
    HasCompactSupport.of_support_subset_isCompact hψ.2.1.isCompact (by
      intro z hz
      by_contra hnot
      apply hz
      funext i
      exact CKN.spatialPartial_eq_zero_off_tsupport hnot i)
  have hsupport : tsupport (associatedPressureTestGradient ψ) ⊆ tsupport ψ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      funext i
      exact CKN.spatialPartial_eq_zero_off_tsupport hnot i
    · exact isClosed_tsupport ψ
  refine ⟨hcont, hcompact, ?_⟩
  exact hsupport.trans hψ.2.2

/-- Time differentiation commutes with a spatial cutoff of a smooth scalar
potential. -/
theorem associatedPressureCutoffTimePartial_eq
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ) :
    CKN.timePartialProd (rieszPressurePotentialCutoffTest ψ n) =
      rieszPressurePotentialCutoffTest (CKN.timePartialProd ψ) n := by
  funext z
  let η := rieszPressurePotentialCutoff n z.1
  have hψt : DifferentiableAt ℝ (fun t : ℝ => ψ (z.1, t)) z.2 := by
    exact ((hψ.differentiable (by simp)).differentiableAt).comp z.2 (by fun_prop)
  have hcutfun : (fun t : ℝ =>
      rieszPressurePotentialCutoffTest ψ n (z.1, t)) =
      fun t => η * ψ (z.1, t) := by
    funext t
    rfl
  change (fderiv ℝ (fun t : ℝ =>
    rieszPressurePotentialCutoffTest ψ n (z.1, t)) z.2) 1 = _
  rw [hcutfun, fderiv_const_mul hψt η]
  change η * CKN.timePartialProd ψ z =
    rieszPressurePotentialCutoff n z.1 * CKN.timePartialProd ψ z
  rfl

/-- Spatial Hessians of the cutoff scalar potential eventually agree at each
fixed space-time point with the uncut Hessian. -/
theorem associatedPressureHelmholtzScalarPotentialCutoff_spatial_eventually_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i j : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      CKN.spatialSecondPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φ n) i j z =
        CKN.spatialSecondPartialProd
          (associatedPressureHelmholtzScalarPotential φ) i j z := by
  let ψ := associatedPressureHelmholtzScalarPotential φ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    associatedPressureHelmholtzScalarPotential_contDiff hφ
  obtain ⟨N, hN⟩ := exists_nat_gt (CKN.vecEuclideanNorm z.1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnorm : CKN.vecEuclideanNorm z.1 < rieszPressurePotentialCutoffScale n := by
    dsimp [rieszPressurePotentialCutoffScale]
    linarith only [hN, hNn]
  have hxBall : z.1 ∈ CKN.euclideanBall 0
      (rieszPressurePotentialCutoffScale n) :=
    (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (rieszPressurePotentialCutoffScale_pos n)).2 (by simpa using hnorm)
  have hxClosed : z.1 ∈ CKN.euclideanClosedBall 0
      (rieszPressurePotentialCutoffScale n) :=
    (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (le_trans (by norm_num) (rieszPressurePotentialCutoffScale_ge_one n))).2
      (by simpa using hnorm.le)
  have hcutSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzScalarPotentialCutoff φ n) :=
    rieszPressurePotentialCutoffTest_contDiff hψ n
  have hcutJoint := rieszPressure_sliceMixedSecond_eq_joint hcutSmooth j i z
  have hψJoint := rieszPressure_sliceMixedSecond_eq_joint hψ j i z
  change CKN.mixedSecond
      (fun x : Vec3 => associatedPressureHelmholtzScalarPotentialCutoff φ n (x, z.2))
      j i z.1 = _
  exact hcutJoint.trans
    ((associatedPressurePotentialCutoff_hessian_eq_of_inner hψ j i n z
      hxBall hxClosed).trans hψJoint.symm)

/-- Time derivatives of the cutoff scalar gradient eventually agree at each
fixed point with the uncut scalar gradient time derivative. -/
theorem associatedPressureHelmholtzScalarPotentialCutoff_timeSpatial_eventually_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      CKN.timePartialProd (CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) i) z =
      CKN.timePartialProd (CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotential φ) i) z := by
  let ψ := associatedPressureHelmholtzScalarPotential φ
  let ψt := CKN.timePartialProd ψ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hψt : ContDiff ℝ (⊤ : ℕ∞) ψt :=
    CKN.contDiff_timePartial hψ
  have hcommute n :
      CKN.timePartialProd (CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φ n) i) z =
        CKN.spatialPartialProd
          (CKN.timePartialProd
            (associatedPressureHelmholtzScalarPotentialCutoff φ n)) i z := by
    exact associatedPressureTimeSpatialPartialProd_commute
      (rieszPressurePotentialCutoffTest_contDiff hψ n) i z
  have hcommuteBase :
      CKN.timePartialProd (CKN.spatialPartialProd ψ i) z =
        CKN.spatialPartialProd (CKN.timePartialProd ψ) i z :=
    associatedPressureTimeSpatialPartialProd_commute hψ i z
  have htimeCut n :
      CKN.timePartialProd (associatedPressureHelmholtzScalarPotentialCutoff φ n) =
        rieszPressurePotentialCutoffTest ψt n := by
    change CKN.timePartialProd (rieszPressurePotentialCutoffTest ψ n) =
      rieszPressurePotentialCutoffTest ψt n
    rw [associatedPressureCutoffTimePartial_eq hψ n]
  have hdir := associatedPressurePotentialCutoff_direction_eventually_eq hψt i z
  filter_upwards [hdir] with n hn
  calc
    CKN.timePartialProd (CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) i) z =
      CKN.spatialPartialProd
        (CKN.timePartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φ n)) i z := hcommute n
    _ = CKN.spatialPartialProd (rieszPressurePotentialCutoffTest ψt n) i z := by
      rw [htimeCut n]
    _ = rieszPressureJointDirection (rieszPressurePotentialCutoffTest ψt n) i z := by
      have hdir : rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest ψt n) i z =
          CKN.spatialPartialProd (rieszPressurePotentialCutoffTest ψt n) i z := by
        exact (rieszPressure_sliceSpatialDeriv_eq_joint
          (rieszPressurePotentialCutoffTest_contDiff hψt n) i z).symm
      exact hdir.symm
    _ = rieszPressureJointDirection ψt i z := hn
    _ = CKN.spatialPartialProd ψt i z := by
      have hdir : rieszPressureJointDirection ψt i z =
          CKN.spatialPartialProd ψt i z := by
        exact (rieszPressure_sliceSpatialDeriv_eq_joint hψt i z).symm
      exact hdir
    _ = CKN.timePartialProd (CKN.spatialPartialProd ψ i) z := hcommuteBase.symm

/-- The complete momentum functional vanishes on the compactly supported
gradient cutoff used in the Helmholtz decomposition. -/
theorem associatedPressureHelmholtzScalarPotentialCutoffGradient_momentum_zero
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    ∫ z : Vec3 × ℝ,
      (-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
          CKN.timePartialProd (CKN.spatialPartialProd
            (associatedPressureHelmholtzScalarPotentialCutoff φ n) i) z))
        - (∑ i : Fin 3, ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd
              (associatedPressureHelmholtzScalarPotentialCutoff φ n) i j z)
        + (∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd
              (associatedPressureHelmholtzScalarPotentialCutoff φ n) i j z)
        - rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (associatedPressureTensor T u)
            (associatedPressureTensor_memLp_fiveThirds hLH) z *
            rieszPressureJointLaplacian
              (associatedPressureHelmholtzScalarPotentialCutoff φ n) z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  obtain ⟨hψ, hψc, hψs⟩ :=
    (associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction
      hφ n)
  have hsupport : tsupport
      (associatedPressureHelmholtzScalarPotentialCutoff φ n) ⊆
        (Set.univ : Set Vec3) ×ˢ Ioo 0 T := by
    exact hψs
  exact associatedPressureCompactGradient_momentum_zero hLH hψ hψc hsupport

end CKN.Leray

end
