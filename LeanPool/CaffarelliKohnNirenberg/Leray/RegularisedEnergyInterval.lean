/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEnergyIntervalDissipation
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEnergyFourier
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# The energy equality of the regularized solutions on an interval

The energy equality (R5) of `thm:regularised`, in its local form on `[0, T]`:
a velocity that solves the regularized mild equation `eq:reg-mild` on `[0, T]`
with the mollified datum, has divergence-free square-integrable slices that
depend continuously on time, and is classically differentiable in space at
positive times, satisfies `‖u(t)‖² + 2∫₀ᵗ‖∇u‖² = ‖J_ε a‖²` for every
`t ∈ [0, T]`.

The proof works on the Fourier side. The frequency-wise damped Duhamel identity
integrates to the energy balance of the mild equation; the Fourier solution is
real because the heat and Stokes symbols respect the reflected conjugation;
the transport term vanishes because the transporting field `J_ε u` is
divergence free; and the frequency dissipation equals the classical
dissipation because the classical spatial derivatives of `u` are its weak
derivatives.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

local instance regularisedEnergyIntervalNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regularisedEnergyIntervalNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The squared spatial `L²` seminorm of a CKN vector field is the squared
norm of its Fourier-space `L²` class. -/
theorem regUniformSpatialField_eLpNorm_sq_eq_ofReal (f : Vec3 → Vec3)
    (hf : MemLp f 2 volume) :
    eLpNorm (regUniformSpatialField f) 2 volume ^ (2 : ℕ) =
      ENNReal.ofReal (‖realVectorL2OfCoordinateFunction f hf‖ ^ 2) := by
  have hrep : regUniformSpatialField f =ᵐ[volume]
      realVectorL2OfCoordinateFunction f hf := by
    have hcoord := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (realVectorL2OfCoordinateFunction_rep f hf).symm
    filter_upwards [hcoord] with x hx
    change WithLp.toLp 2 (f (WithLp.ofLp x)) = realVectorL2OfCoordinateFunction f hf x
    change f (WithLp.ofLp x) =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))
        (realVectorL2OfCoordinateFunction f hf x) at hx
    have hy := congrArg (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm hx
    simpa only [PiLp.coe_symm_continuousLinearEquiv,
      PiLp.coe_continuousLinearEquiv, WithLp.toLp_ofLp] using hy
  rw [eLpNorm_congr_ae hrep, ← Lp.enorm_def, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The energy equality (R5) of `thm:regularised` on `[0, T]` from the
hypotheses its proof uses: square-integrable, divergence-free slices depending
continuously on time, spatial derivatives continuous at positive times, joint
continuous differentiability at positive times, and the mild equation
`eq:reg-mild` with the mollified datum. -/
theorem regularised_R5_on_interval_of_mild
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3)
    (T : ℝ) (hT : 0 < T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hL2Continuous : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)))
    (hDivFree : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hDcontinuous : ∀ i j, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hUjoint : ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hMild : ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSlice t ht) =
      realHeatOperator t ht.1
        (realVectorL2OfCoordinateFunction
          (regUniformMollifiedInitial ρ ε hε a)
          (regMollifiedInitial_isInJ ρ ε hε ha).1) -
      regularizedMildStokesIntegral
        (regularizedMildTensorTrajectory ρ ε hε
          (fun s => realVectorL2OfCoordinateFunction
            (fun x : Vec3 =>
              u (x, (regularizedMildTimeClamp T hT.le s : Set.Icc 0 T).1))
            (hSlice
              (regularizedMildTimeClamp T hT.le s : Set.Icc 0 T).1
              (regularizedMildTimeClamp T hT.le s : Set.Icc 0 T).2))) t) :
    ∀ t : ℝ, t ∈ Set.Icc 0 T →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u
          (fun z i j => spatialPartial (fun y => u y i) j z) t =
      eLpNorm
        (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ) := by
  intro t ht
  -- the continuous trajectory, the datum and the clamped tensor path
  set U' : C(Set.Icc (0 : ℝ) T, RealVectorL2) :=
    ⟨fun s => realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, s.1))
      (hSlice s.1 s.2), hL2Continuous⟩ with hU'def
  set b : RealVectorL2 := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a) (regMollifiedInitial_isInJ ρ ε hε ha).1 with hbdef
  set F : ℝ → RealTensorL2 :=
    regularizedMildClampedTensorTrajectory ρ ε hε T hT.le U' with hFdef
  have hFsm : StronglyMeasurable F :=
    (regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT.le U').stronglyMeasurable
  have hR : 0 ≤ ‖U'‖ := norm_nonneg _
  have hUR : ∀ s, ‖U' s‖ ≤ ‖U'‖ := fun s => U'.norm_coe_le_norm s
  have hK : 0 ≤ regularizedMildMollifierConstant ρ ε := ENNReal.toReal_nonneg
  have hC : 0 ≤ regularizedMildMollifierConstant ρ ε * ‖U'‖ ^ 2 := by positivity
  have hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ regularizedMildMollifierConstant ρ ε * ‖U'‖ ^ 2 :=
    fun s _ => regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT.le U' ‖U'‖ hR hUR s
  have hbJ : RegularizedMildJData b :=
    CKN.isInJ_iff_weakDivFree.2 (isWeakDivFree_congr_ae
      (realVectorL2OfCoordinateFunction_rep _ _).symm
      (CKN.isInJ_iff_weakDivFree.1 (regMollifiedInitial_isInJ ρ ε hε ha)))
  -- the zero force
  set h0 : ℝ → RealVectorL2 := fun _ => 0 with hh0def
  have hh0 : StronglyMeasurable h0 := stronglyMeasurable_const
  have hH2 : IntegrableOn (fun s => ‖h0 s‖ ^ 2) (Ioc 0 T) := by
    simp [h0]
  have hH1 : ∀ s, IntegrableOn (fun r => ‖h0 r‖) (Ioc 0 s) := fun s => by
    simp [h0]
  have hduhamel : ∀ s, forcedForceDuhamel h0 s = 0 := by
    intro s
    have hz : ∀ τ (hτ : 0 ≤ τ), forcedHeatLeray τ hτ (0 : RealVectorL2) = 0 := by
      intro τ hτ
      have hProj : lerayProjectionL2 (0 : ComplexVectorL2) = 0 :=
        norm_eq_zero.mp (le_antisymm
          ((lerayProjectionL2_norm_le (0 : ComplexVectorL2)).trans_eq norm_zero)
          (norm_nonneg _))
      have hHeat : heatSemigroup τ hτ (0 : ComplexVectorL2) = 0 :=
        norm_eq_zero.mp (le_antisymm
          ((heatSemigroup_norm_le τ hτ (0 : ComplexVectorL2)).trans_eq norm_zero)
          (norm_nonneg _))
      simp [forcedHeatLeray, hProj, hHeat]
    simp [forcedForceDuhamel, forcedForceIntegrand, h0, hz]
  -- the complex solution curve
  set v : ℝ → ComplexVectorL2 := fun s => forcedComplexCurve b F h0 s with hvdef
  have hU : ∀ s (hs : s ∈ Icc 0 T),
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, s)) (hSlice s hs) =
        realPartVectorL2 (v s) := by
    intro s hs
    rw [hvdef, ← forcedMildCurve_eq_realPart b hFsm hh0 hs.1
      (fun r hr => hFC r ⟨hr.1, hr.2.trans hs.2⟩) (hH1 s)]
    unfold forcedMildCurve
    rw [dite_eq_left hs.1]
    unfold forcedMildRHS
    rw [hduhamel, add_zero]
    exact hMild s hs
  have hv : ∀ s, v s = complexifyVectorL2 (realPartVectorL2 (v s)) :=
    fun s => forcedComplexCurve_eq_complexify b F h0 s
  have hnorm : ∀ s, ‖v s‖ = ‖realPartVectorL2 (v s)‖ := by
    intro s
    conv_lhs => rw [hv s]
    apply le_antisymm (complexifyVectorL2_norm_le _)
    calc ‖realPartVectorL2 (v s)‖ =
          ‖realPartVectorL2 (complexifyVectorL2 (realPartVectorL2 (v s)))‖ := by
            rw [realPartVectorL2_complexifyVectorL2]
      _ ≤ ‖complexifyVectorL2 (realPartVectorL2 (v s))‖ := realPartVectorL2_norm_le _
  have hreal : ∀ s, conjReflectLp complexVecConj
      (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (v s)) =
      Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (v s) := by
    intro s
    rw [hv s]
    exact conjReflectLp_fourier_complexifyVectorL2 _
  -- the energy balance of the mild equation
  obtain ⟨hae, hint, hbal⟩ :=
    forcedMild_energy_balance_eq b hbJ hFsm hh0 hC hFC hH2 ht.1 ht.2
  have hgrad : ∀ s, Integrable (fun ξ => forcedFourierLam ξ *
      ‖(Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (v s) : L2Vec3 → ComplexVec3) ξ‖ ^ 2) →
      MemLp (forcedFourierGradHat (v s)) 2 volume := by
    intro s hs
    refine (memLp_two_iff_integrable_sq_norm
      (measurable_forcedFourierGradHat (v s)).aestronglyMeasurable).2 ?_
    exact hs.congr (Eventually.of_forall fun ξ => (norm_sq_forcedFourierGradHat (v s) ξ).symm)
  -- the transport term vanishes
  have hpair : ∫ s in Ioc 0 t,
      forcedStokesPairing (v s) (complexifyTensorL2 (F s)) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with s hs hsI
    have hsT : s ∈ Icc 0 T := ⟨hsI.1.le, hsI.2.trans ht.2⟩
    have hFs : F s = forcedTruncTensor ρ ε hε ‖realPartVectorL2 (v s)‖
        (realPartVectorL2 (v s)) := by
      unfold forcedTruncTensor
      rw [forcedTrunc_of_norm_le le_rfl, hFdef]
      unfold regularizedMildClampedTensorTrajectory
      rw [regularizedMildTimeClamp_eq_of_mem T hT.le hsT, ← hU s hsT]
      rfl
    have hJ : RegularizedMildJData (realPartVectorL2 (v s)) := by
      rw [← hU s hsT]
      exact CKN.isInJ_iff_weakDivFree.2 (isWeakDivFree_congr_ae
        (realVectorL2OfCoordinateFunction_rep _ _).symm (hDivFree s hsT))
    rw [hFs]
    exact forcedStokesPairing_truncTensor_eq_zero ρ ε hε (v s) (hgrad s hs) hJ
  have hforce : ∫ s in Ioc 0 t, inner ℝ (forcedMildCurve b h0 F s) (h0 s) = 0 := by
    simp [h0]
  rw [hpair, hforce, mul_zero, add_zero, add_zero] at hbal
  -- the dissipation
  have hd0 : ∀ s, 0 ≤ forcedFourierDissipation (v s) := fun s =>
    integral_nonneg fun ξ => mul_nonneg (forcedFourierLam_nonneg ξ) (sq_nonneg _)
  have hslice : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)),
      ∫⁻ x, ENNReal.ofReal (CKN.spatialGradientSq u
        (fun z i j => spatialPartial (fun y => u y i) j z) (x, s)) =
        ENNReal.ofReal (forcedFourierDissipation (v s)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae,
      ae_restrict_mem measurableSet_Ioo] with s hs hsI
    have hsT : s ∈ Icc 0 T := ⟨hsI.1.le, hsI.2.le.trans ht.2⟩
    have hrep : (fun x => u (x, s)) =ᵐ[volume] realPartVectorL2Representative (v s) := by
      have h1 := (realVectorL2OfCoordinateFunction_rep (fun x : Vec3 => u (x, s))
        (hSlice s hsT)).symm
      rw [hU s hsT] at h1
      exact h1.trans (realPartVectorL2Representative_eq_ae (v s))
    have hC1 : ∀ i, ContDiff ℝ 1 (fun x : Vec3 => u (x, s) i) := by
      intro i
      have hU1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z i)
          ((Set.univ : Set Vec3) ×ˢ Set.Ioc 0 T) := hUjoint i
      rw [contDiff_iff_contDiffAt]
      intro x
      have hmem : (Set.univ : Set Vec3) ×ˢ Set.Ioc 0 T ∈ 𝓝 ((x, s) : Vec3 × ℝ) :=
        mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds
          ⟨mem_univ x, hsI.1, hsI.2.trans_le ht.2⟩)
          (prod_mono subset_rfl Ioo_subset_Ioc_self)
      exact (hU1.contDiffAt hmem).comp x
        ((contDiff_id.prodMk contDiff_const).contDiffAt)
    exact lintegral_spatialGradientSq_slice_eq (v s) (hgrad s hs) (hreal s) hrep hC1
  have hdiss := regUniformDissipation_eq_ofReal_integral ht.2 (fun i j => hDcontinuous i j)
    (fun s => forcedFourierDissipation (v s)) hint hd0 hslice
  -- assembly
  have hslicet : eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) =
      ENNReal.ofReal (‖v t‖ ^ 2) := by
    rw [hnorm t, ← hU t ht]
    exact regUniformSpatialField_eLpNorm_sq_eq_ofReal (fun x : Vec3 => u (x, t)) (hSlice t ht)
  have hinit : eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume ^ (2 : ℕ) =
      ENNReal.ofReal (‖b‖ ^ 2) := by
    have hfield : regMollifyVector ρ ε hε (regUniformSpatialField a) =
        regUniformSpatialField (regUniformMollifiedInitial ρ ε hε a) := by
      funext x
      simp [regUniformSpatialField, regUniformMollifiedInitial]
    rw [hfield]
    exact regUniformSpatialField_eLpNorm_sq_eq_ofReal _ _
  have hI0 : 0 ≤ ∫ s in Ioc 0 t, forcedFourierDissipation (v s) :=
    setIntegral_nonneg measurableSet_Ioc fun s _ => hd0 s
  rw [hslicet, hdiss, hinit, ← hbal, ENNReal.ofReal_add (sq_nonneg _) (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- The energy equality (R5) of `thm:regularised` on the interval `[0, T]`,
for the regularized mild solution with the mollified datum. -/
theorem regularised_R5_on_interval
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3)
    (T : ℝ) (hT : 0 < T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hL2Continuous : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2))
    )
    (hDivFree : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hDcontinuous : ∀ i j, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hUjoint : ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hMild : ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSlice t ht) =
      realHeatOperator t ht.1
        (realVectorL2OfCoordinateFunction
          (regUniformMollifiedInitial ρ ε hε a)
          (regMollifiedInitial_isInJ ρ ε hε ha).1) -
      regularizedMildStokesIntegral
        (regularizedMildTensorTrajectory ρ ε hε
          (fun s => realVectorL2OfCoordinateFunction
            (fun x : Vec3 =>
              u (x, (regularizedMildTimeClamp T hT.le s : Set.Icc 0 T).1))
            (hSlice
              (regularizedMildTimeClamp T hT.le s : Set.Icc 0 T).1
              (regularizedMildTimeClamp T hT.le s : Set.Icc 0 T).2))) t) :
    ∀ t : ℝ, t ∈ Set.Icc 0 T →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u
          (fun z i j => spatialPartial (fun y => u y i) j z) t =
      eLpNorm
        (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ) :=
  regularised_R5_on_interval_of_mild ρ ε hε a ha u T hT hSlice hL2Continuous hDivFree
    hDcontinuous hUjoint hMild

end CKN.Leray

end
