/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.SpaceTimeMollifier
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivMollify
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Density extension for weighted Carleman inequalities

This module is intended to extend smooth compactly supported inequalities to
fields with space-time weak derivatives (`lem:carleman-sobolev` of the Escauriaza–Seregin–Šverák
manuscript).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private def piEvalCLM {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i : ι) : (ι → E) →L[ℝ] E :=
  ContinuousLinearMap.mk (LinearMap.proj i) (by
    have hL : LipschitzWith 1 (fun x : ι → E => x i) := by
      intro x y
      have hdist : dist (x i) (y i) ≤ dist x y := by
        calc
          dist (x i) (y i) = ‖(x - y) i‖ := by simp [dist_eq_norm]
          _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
          _ = dist x y := by rw [dist_eq_norm]
      simpa [edist_dist] using hdist
    exact hL.continuous)

/-- The pointwise zero extension of a field from a set. -/
@[expose]
noncomputable def zeroExtendField {E V : Type} [Zero V]
    (U : Set E) (f : E → V) : E → V := by
  classical
  exact fun z => if z ∈ U then f z else 0

/-- If a field has support inside `U`, its pointwise zero extension from `U` is the
field itself. This is the support fact used when extending the weak derivative
identities in `lem:carleman-sobolev` (ESS). -/
theorem zeroExtend_eq_of_tsupport_subset {E V : Type} [Zero V]
    [TopologicalSpace E] (U : Set E) (f : E → V)
    (hfsupport : tsupport f ⊆ U) : zeroExtendField U f = f := by
  classical
  change (fun z => if z ∈ U then f z else 0) = f
  funext z
  by_cases hz : z ∈ U
  · simp [hz]
  · have hzero : f z = 0 := by
      by_contra hne
      exact hz (hfsupport (subset_tsupport f (Function.mem_support.mpr hne)))
    simp [hz, hzero]

/-- Local integrability on a CKN space-time product transfers to its product coordinates. -/
theorem locallyIntegrableOn_parabolic_to_product
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {E : Type*} [NormedAddCommGroup E]
    {f : ParabolicPoint → E}
    (hf : LocallyIntegrableOn f (spaceTimeSet Ω I) (volume : Measure ParabolicPoint)) :
    LocallyIntegrableOn (fun q : Vec3 × ℝ => f (parabolicHomeomorph.symm q))
      (Ω ×ˢ I) (volume : Measure (Vec3 × ℝ)) := by
  rw [locallyIntegrableOn_iff ((hΩ.prod hI).isLocallyClosed)]
  intro K hKU hK
  let Kp : Set ParabolicPoint := parabolicHomeomorph.symm '' K
  have hKp : IsCompact Kp := parabolicHomeomorph.symm.isCompact_image.mpr hK
  have hKpU : Kp ⊆ spaceTimeSet Ω I := by
    rintro p ⟨q, hq, rfl⟩
    exact hKU hq
  have hInt : IntegrableOn f Kp (volume : Measure ParabolicPoint) :=
    hf.integrableOn_compact_subset hKpU hKp
  exact (parabolicHomeomorphSymm_measurePreserving.integrableOn_image
    parabolicHomeomorph.symm.measurableEmbedding).mp hInt

/-- Nonnegative set integrals on a space-time product agree in CKN and product coordinates. -/
theorem setLIntegral_parabolic_to_product
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ≥0∞} :
    (∫⁻ p in spaceTimeSet Ω I, F p ∂(volume : Measure ParabolicPoint)) =
      ∫⁻ q in Ω ×ˢ I, F (parabolicHomeomorph.symm q)
        ∂(volume : Measure (Vec3 × ℝ)) := by
  have himage : parabolicHomeomorph.symm '' (Ω ×ˢ I) = spaceTimeSet Ω I := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      refine ⟨parabolicHomeomorph p, ?_, ?_⟩
      · exact hp
      · exact parabolicHomeomorph.symm_apply_apply p
  have htrans := parabolicHomeomorphSymm_measurePreserving.setLIntegral_comp_emb
    parabolicHomeomorph.symm.measurableEmbedding F (Ω ×ˢ I)
  rw [himage] at htrans
  exact htrans.symm

/-- The weak spatial integration-by-parts identity in product coordinates
(`lem:carleman-sobolev`, ESS). -/
theorem weak_spatial_identity_product
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ Ω ×ˢ I)
    (i j : Fin 3) :
    (∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
      (fderiv ℝ φ y) (basisVec j, 0) ∂(volume : Measure (Vec3 × ℝ))) =
    -∫ y in Ω ×ˢ I, Dw (parabolicHomeomorph.symm y) i j * φ y
      ∂(volume : Measure (Vec3 × ℝ)) := by
  let φp : ParabolicPoint → ℝ := fun p => φ (parabolicHomeomorph p)
  have hφpEq : φp = (show ParabolicPoint → ℝ from φ) := by
    funext p
    rfl
  have htest : (show Vec3 × ℝ → ℝ from φp) ∈ spaceTimeTestFunction Ω I := by
    change (φp : Vec3 × ℝ → ℝ) ∈ spaceTimeTestFunction Ω I
    rw [hφpEq]
    exact ⟨hφ, hφc, hφU⟩
  have hsource := (hderiv.2.2.2.2 φp htest).1 i j
  have hleftTrans :
      (∫ p in spaceTimeSet Ω I, w p i * spatialPartial φp j p
        ∂(volume : Measure ParabolicPoint)) =
        ∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
          spatialPartial φp j (parabolicHomeomorph.symm y)
            ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => w p i * spatialPartial φp j p)
  have hrightTrans :
      (∫ p in spaceTimeSet Ω I, Dw p i j * φp p
        ∂(volume : Measure ParabolicPoint)) =
        ∫ y in Ω ×ˢ I, Dw (parabolicHomeomorph.symm y) i j * φ y
          ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [φp, parabolicHomeomorph] using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => Dw p i j * φp p)
  have hfactor (y : Vec3 × ℝ) :
      spatialPartial φp j (parabolicHomeomorph.symm y) =
        (fderiv ℝ φ y) (basisVec j, 0) := by
    rw [hφpEq]
    simpa using spatialPartial_eq_joint_fderiv hφ y j
  calc
    (∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
        (fderiv ℝ φ y) (basisVec j, 0) ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
        spatialPartial φp j (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ)) := by
            apply setIntegral_congr_ae (hΩ.prod hI).measurableSet
            filter_upwards [] with y hy
            rw [hfactor]
    _ = ∫ p in spaceTimeSet Ω I, w p i * spatialPartial φp j p
        ∂(volume : Measure ParabolicPoint) := hleftTrans.symm
    _ = -∫ p in spaceTimeSet Ω I, Dw p i j * φp p
        ∂(volume : Measure ParabolicPoint) := hsource
    _ = -∫ y in Ω ×ˢ I, Dw (parabolicHomeomorph.symm y) i j * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by rw [hrightTrans]

private theorem spatialWeakDerivative_ae_zero_off_support
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I)
    (i j : Fin 3) :
    ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        Dw (parabolicHomeomorph.symm y) i j = 0 := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' tsupport w
  have hUopen : IsOpen U := hΩ.prod hI
  have hKcompact : IsCompact K := parabolicHomeomorph.isCompact_image.mpr hcompact.isCompact
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKU : K ⊆ U := by
    rintro y ⟨p, hp, rfl⟩
    exact htsupport hp
  let O : Set (Vec3 × ℝ) := U ∩ Kᶜ
  have hOopen : IsOpen O := by
    exact hUopen.inter hKclosed.isOpen_compl
  have hOU : O ⊆ U := Set.inter_subset_left
  have hlocal : LocallyIntegrableOn
      (fun y : Vec3 × ℝ => Dw (parabolicHomeomorph.symm y) i j) U
      (volume : Measure (Vec3 × ℝ)) := by
    have hpara_i : LocallyIntegrableOn (fun p : ParabolicPoint => Dw p i)
        (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
      exact locallyIntegrableOn_pi_eval hderiv.2.1 i
    have hpara : LocallyIntegrableOn (fun p : ParabolicPoint => Dw p i j)
        (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
      exact locallyIntegrableOn_pi_eval hpara_i j
    have hprod := locallyIntegrableOn_parabolic_to_product hΩ hI hpara
    exact hprod.mono_set (by simp [U])
  have hlocalO := hlocal.mono_set hOU
  have htestIntegral : ∀ φ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ O →
      ∫ y, φ y * Dw (parabolicHomeomorph.symm y) i j
        ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    intro φ hφ hφc hφO
    let φp : ParabolicPoint → ℝ := fun p => φ (parabolicHomeomorph p)
    have hφpEq : φp = (show ParabolicPoint → ℝ from φ) := by
      funext p
      rfl
    have hφtest : (show Vec3 × ℝ → ℝ from φp) ∈ spaceTimeTestFunction Ω I := by
      change (φp : Vec3 × ℝ → ℝ) ∈ spaceTimeTestFunction Ω I
      rw [hφpEq]
      exact ⟨hφ, hφc, hφO.trans hOU⟩
    have hsource := (hderiv.2.2.2.2 φp hφtest).1 i j
    have hfactor (y : Vec3 × ℝ) :
        spatialPartial φp j (parabolicHomeomorph.symm y) =
          (fderiv ℝ φ y) (basisVec j, 0) := by
      rw [hφpEq]
      simpa using spatialPartial_eq_joint_fderiv hφ y j
    have hleftzero :
        (∫ y in U, w (parabolicHomeomorph.symm y) i *
          (fderiv ℝ φ y) (basisVec j, 0)
            ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with y hyU
      by_cases hyK : y ∈ K
      · have hφnot : y ∉ tsupport φ := by
          intro hφmem
          exact (hφO hφmem).2 hyK
        have hfd : fderiv ℝ φ y = 0 := fderiv_of_notMem_tsupport ℝ hφnot
        rw [hfd]
        simp
      · have hw : w (parabolicHomeomorph.symm y) i = 0 := by
          by_contra hne
          have hvec : w (parabolicHomeomorph.symm y) ≠ 0 := by
            intro h
            exact hne (congrArg (fun v : Vec3 => v i) h)
          have hmem : parabolicHomeomorph.symm y ∈ tsupport w :=
            subset_tsupport w (Function.mem_support.mpr hvec)
          exact hyK ⟨parabolicHomeomorph.symm y, hmem,
            parabolicHomeomorph.apply_symm_apply y⟩
        change w (parabolicHomeomorph.symm y) i *
          (fderiv ℝ φ y) (basisVec j, 0) = 0
        rw [hw]
        simp
    have hsetzero :
        (∫ y in U, Dw (parabolicHomeomorph.symm y) i j * φ y
          ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
      have hweak := weak_spatial_identity_product hΩ hI hderiv hφ hφc
        (hφO.trans hOU) i j
      rw [hleftzero] at hweak
      have hneg : -∫ y in U, Dw (parabolicHomeomorph.symm y) i j * φ y
          ∂(volume : Measure (Vec3 × ℝ)) = 0 := hweak.symm
      exact neg_eq_zero.mp hneg
    have hfull :
        (∫ y, φ y * Dw (parabolicHomeomorph.symm y) i j
          ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
      calc
        (∫ y, φ y * Dw (parabolicHomeomorph.symm y) i j
            ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ y in U, φ y * Dw (parabolicHomeomorph.symm y) i j
            ∂(volume : Measure (Vec3 × ℝ)) := by
              symm
              apply setIntegral_eq_integral_of_ae_compl_eq_zero
              filter_upwards [] with y hyU
              have hφzero : φ y = 0 := by
                by_contra hne
                exact hyU (hφO (subset_tsupport φ (Function.mem_support.mpr hne))).1
              simp [hφzero]
        _ = 0 := by
          simpa only [mul_comm] using hsetzero
    simpa only [smul_eq_mul] using hfull
  have hzero := hOopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocalO
    htestIntegral
  filter_upwards [hzero] with y hy
  intro hyU hyK
  apply hy
  exact ⟨hyU, hyK⟩

private theorem weakData_ae_zero_off_support
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} (hcompact : HasCompactSupport w)
    {u g : ParabolicPoint → ℝ} (v : Vec3 × ℝ)
    (hg : LocallyIntegrableOn g (spaceTimeSet Ω I) (volume : Measure ParabolicPoint))
    (hprev : ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        u (parabolicHomeomorph.symm y) = 0)
    (hweak : ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω ×ˢ I →
      (∫ y in Ω ×ˢ I, u (parabolicHomeomorph.symm y) *
        (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ))) =
        -∫ y in Ω ×ˢ I, g (parabolicHomeomorph.symm y) * φ y
          ∂(volume : Measure (Vec3 × ℝ))) :
    ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        g (parabolicHomeomorph.symm y) = 0 := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' tsupport w
  have hUopen : IsOpen U := hΩ.prod hI
  have hKcompact : IsCompact K := parabolicHomeomorph.isCompact_image.mpr hcompact.isCompact
  have hKclosed : IsClosed K := hKcompact.isClosed
  let O : Set (Vec3 × ℝ) := U ∩ Kᶜ
  have hOopen : IsOpen O := hUopen.inter hKclosed.isOpen_compl
  have hOU : O ⊆ U := Set.inter_subset_left
  have hlocal : LocallyIntegrableOn
      (fun y : Vec3 × ℝ => g (parabolicHomeomorph.symm y)) U
      (volume : Measure (Vec3 × ℝ)) := by
    have hprod := locallyIntegrableOn_parabolic_to_product hΩ hI hg
    exact hprod.mono_set (by simp [U])
  have hlocalO := hlocal.mono_set hOU
  have htestIntegral : ∀ φ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ O →
      ∫ y, φ y * g (parabolicHomeomorph.symm y)
        ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    intro φ hφ hφc hφO
    have hleftzero :
        (∫ y in U, u (parabolicHomeomorph.symm y) *
          (fderiv ℝ φ y) v ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      filter_upwards [hprev] with y hprevY
      intro hyU
      by_cases hyK : y ∈ K
      · have hφnot : y ∉ tsupport φ := by
          intro hφmem
          exact (hφO hφmem).2 hyK
        have hfd : fderiv ℝ φ y = 0 := fderiv_of_notMem_tsupport ℝ hφnot
        rw [hfd]
        simp
      · have hu : u (parabolicHomeomorph.symm y) = 0 := hprevY hyU hyK
        change u (parabolicHomeomorph.symm y) * (fderiv ℝ φ y) v = 0
        rw [hu]
        simp
    have hsetzero :
        (∫ y in U, g (parabolicHomeomorph.symm y) * φ y
          ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
      have hiden := hweak φ hφ hφc (hφO.trans hOU)
      rw [hleftzero] at hiden
      exact neg_eq_zero.mp hiden.symm
    have hfull :
        (∫ y, φ y * g (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ))) = 0 := by
      calc
        (∫ y, φ y * g (parabolicHomeomorph.symm y)
            ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ y in U, φ y * g (parabolicHomeomorph.symm y)
            ∂(volume : Measure (Vec3 × ℝ)) := by
              symm
              apply setIntegral_eq_integral_of_ae_compl_eq_zero
              filter_upwards [] with y hyU
              have hφzero : φ y = 0 := by
                by_contra hne
                exact hyU (hφO (subset_tsupport φ (Function.mem_support.mpr hne))).1
              simp [hφzero]
        _ = 0 := by simpa only [mul_comm] using hsetzero
    simpa only [smul_eq_mul] using hfull
  have hzero := hOopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocalO
    htestIntegral
  filter_upwards [hzero] with y hy
  intro hyU hyK
  apply hy
  exact ⟨hyU, hyK⟩

/-- The weak second spatial integration-by-parts identity in product coordinates
(`lem:carleman-sobolev`, ESS). -/
theorem weak_spatialSecond_identity_product
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ Ω ×ˢ I)
    (i j k : Fin 3) :
    (∫ y in Ω ×ˢ I, Dw (parabolicHomeomorph.symm y) i j *
      (fderiv ℝ φ y) (basisVec k, 0) ∂(volume : Measure (Vec3 × ℝ))) =
    -∫ y in Ω ×ˢ I, D2w (parabolicHomeomorph.symm y) i j k * φ y
      ∂(volume : Measure (Vec3 × ℝ)) := by
  let φp : ParabolicPoint → ℝ := fun p => φ (parabolicHomeomorph p)
  have hφpEq : φp = (show ParabolicPoint → ℝ from φ) := by
    funext p
    rfl
  have htest : (show Vec3 × ℝ → ℝ from φp) ∈ spaceTimeTestFunction Ω I := by
    change (φp : Vec3 × ℝ → ℝ) ∈ spaceTimeTestFunction Ω I
    rw [hφpEq]
    exact ⟨hφ, hφc, hφU⟩
  have hsource := (hderiv.2.2.2.2 φp htest).2.1 i j k
  have hleftTrans :
      (∫ p in spaceTimeSet Ω I, Dw p i j * spatialPartial φp k p
        ∂(volume : Measure ParabolicPoint)) =
        ∫ y in Ω ×ˢ I, Dw (parabolicHomeomorph.symm y) i j *
          spatialPartial φp k (parabolicHomeomorph.symm y)
            ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => Dw p i j * spatialPartial φp k p)
  have hrightTrans :
      (∫ p in spaceTimeSet Ω I, D2w p i j k * φp p
        ∂(volume : Measure ParabolicPoint)) =
        ∫ y in Ω ×ˢ I, D2w (parabolicHomeomorph.symm y) i j k * φ y
          ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [φp, parabolicHomeomorph] using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => D2w p i j k * φp p)
  have hfactor (y : Vec3 × ℝ) :
      spatialPartial φp k (parabolicHomeomorph.symm y) =
        (fderiv ℝ φ y) (basisVec k, 0) := by
    rw [hφpEq]
    simpa using spatialPartial_eq_joint_fderiv hφ y k
  calc
    (∫ y in Ω ×ˢ I, Dw (parabolicHomeomorph.symm y) i j *
        (fderiv ℝ φ y) (basisVec k, 0) ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ y in Ω ×ˢ I, Dw (parabolicHomeomorph.symm y) i j *
        spatialPartial φp k (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ)) := by
            apply setIntegral_congr_ae (hΩ.prod hI).measurableSet
            filter_upwards [] with y hy
            rw [hfactor]
    _ = ∫ p in spaceTimeSet Ω I, Dw p i j * spatialPartial φp k p
        ∂(volume : Measure ParabolicPoint) := hleftTrans.symm
    _ = -∫ p in spaceTimeSet Ω I, D2w p i j k * φp p
        ∂(volume : Measure ParabolicPoint) := hsource
    _ = -∫ y in Ω ×ˢ I, D2w (parabolicHomeomorph.symm y) i j k * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by rw [hrightTrans]

/-- The weak time integration-by-parts identity in product coordinates
(`lem:carleman-sobolev`, ESS). -/
theorem weak_time_identity_product
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ Ω ×ˢ I)
    (i : Fin 3) :
    (∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
      (fderiv ℝ φ y) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
    -∫ y in Ω ×ˢ I, Dtw (parabolicHomeomorph.symm y) i * φ y
      ∂(volume : Measure (Vec3 × ℝ)) := by
  let φp : ParabolicPoint → ℝ := fun p => φ (parabolicHomeomorph p)
  have hφpEq : φp = (show ParabolicPoint → ℝ from φ) := by
    funext p
    rfl
  have htest : (show Vec3 × ℝ → ℝ from φp) ∈ spaceTimeTestFunction Ω I := by
    change (φp : Vec3 × ℝ → ℝ) ∈ spaceTimeTestFunction Ω I
    rw [hφpEq]
    exact ⟨hφ, hφc, hφU⟩
  have hsource := (hderiv.2.2.2.2 φp htest).2.2 i
  have hleftTrans :
      (∫ p in spaceTimeSet Ω I, w p i * timePartial φp p
        ∂(volume : Measure ParabolicPoint)) =
        ∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
          timePartial φp (parabolicHomeomorph.symm y)
            ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => w p i * timePartial φp p)
  have hrightTrans :
      (∫ p in spaceTimeSet Ω I, Dtw p i * φp p
        ∂(volume : Measure ParabolicPoint)) =
        ∫ y in Ω ×ˢ I, Dtw (parabolicHomeomorph.symm y) i * φ y
          ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [φp, parabolicHomeomorph] using setIntegral_parabolic_to_product
      (F := fun p : ParabolicPoint => Dtw p i * φp p)
  have hfactor (y : Vec3 × ℝ) :
      timePartial φp (parabolicHomeomorph.symm y) = (fderiv ℝ φ y) (0, 1) := by
    rw [hφpEq]
    simpa using timePartial_eq_joint_fderiv hφ y
  calc
    (∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
        (fderiv ℝ φ y) (0, 1) ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ y in Ω ×ˢ I, w (parabolicHomeomorph.symm y) i *
        timePartial φp (parabolicHomeomorph.symm y)
          ∂(volume : Measure (Vec3 × ℝ)) := by
            apply setIntegral_congr_ae (hΩ.prod hI).measurableSet
            filter_upwards [] with y hy
            rw [hfactor]
    _ = ∫ p in spaceTimeSet Ω I, w p i * timePartial φp p
        ∂(volume : Measure ParabolicPoint) := hleftTrans.symm
    _ = -∫ p in spaceTimeSet Ω I, Dtw p i * φp p
        ∂(volume : Measure ParabolicPoint) := hsource
    _ = -∫ y in Ω ×ˢ I, Dtw (parabolicHomeomorph.symm y) i * φ y
        ∂(volume : Measure (Vec3 × ℝ)) := by rw [hrightTrans]

/-- A component of a compactly supported field vanishes outside its closed support. -/
theorem field_component_ae_zero_off_support
    {Ω : Set Vec3} {I : Set ℝ} {w : ParabolicPoint → Vec3}
    (i : Fin 3) :
    ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        w (parabolicHomeomorph.symm y) i = 0 := by
  filter_upwards [] with y
  intro hyU hyK
  by_contra hne
  have hvec : w (parabolicHomeomorph.symm y) ≠ 0 := by
    intro h
    exact hne (congrArg (fun v : Vec3 => v i) h)
  have hmem : parabolicHomeomorph.symm y ∈ tsupport w :=
    subset_tsupport w (Function.mem_support.mpr hvec)
  exact hyK ⟨parabolicHomeomorph.symm y, hmem, parabolicHomeomorph.apply_symm_apply y⟩

private theorem secondSpatialWeakDerivative_ae_zero_off_support
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I)
    (i j k : Fin 3) :
    ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        D2w (parabolicHomeomorph.symm y) i j k = 0 := by
  have hprev := spatialWeakDerivative_ae_zero_off_support
    hΩ hI hderiv hcompact htsupport i j
  have hpara_i : LocallyIntegrableOn (fun p : ParabolicPoint => D2w p i)
      (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) :=
    locallyIntegrableOn_pi_eval hderiv.2.2.1 i
  have hpara_ij : LocallyIntegrableOn (fun p : ParabolicPoint => D2w p i j)
      (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) :=
    locallyIntegrableOn_pi_eval hpara_i j
  have hpara : LocallyIntegrableOn (fun p : ParabolicPoint => D2w p i j k)
      (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) :=
    locallyIntegrableOn_pi_eval hpara_ij k
  exact weakData_ae_zero_off_support hΩ hI hcompact (basisVec k, 0)
    (u := fun p => Dw p i j) (g := fun p => D2w p i j k) hpara hprev (by
      intro φ hφ hφc hφU
      exact weak_spatialSecond_identity_product hΩ hI hderiv hφ hφc hφU i j k)

private theorem timeWeakDerivative_ae_zero_off_support
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (i : Fin 3) :
    ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        Dtw (parabolicHomeomorph.symm y) i = 0 := by
  have hprev := field_component_ae_zero_off_support (Ω := Ω) (I := I) (w := w) i
  have hpara : LocallyIntegrableOn (fun p : ParabolicPoint => Dtw p i)
      (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) :=
    locallyIntegrableOn_pi_eval hderiv.2.2.2.1 i
  exact weakData_ae_zero_off_support hΩ hI hcompact (0, 1)
    (u := fun p => w p i) (g := fun p => Dtw p i) hpara hprev (by
      intro φ hφ hφc hφU
      exact weak_time_identity_product hΩ hI hderiv hφ hφc hφU i)

/-- The first spatial, second spatial, and time weak derivatives vanish almost everywhere
outside the closed support of a compactly supported field (`lem:carleman-sobolev`, ESS). -/
theorem spaceTimeWeakDerivs_ae_zero_off_tsupport
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hcompact : HasCompactSupport w)
    (htsupport : tsupport w ⊆ spaceTimeSet Ω I) :
    (∀ i j : Fin 3, ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        Dw (parabolicHomeomorph.symm y) i j = 0) ∧
    (∀ i j k : Fin 3, ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        D2w (parabolicHomeomorph.symm y) i j k = 0) ∧
    (∀ i : Fin 3, ∀ᵐ y ∂(volume : Measure (Vec3 × ℝ)),
      y ∈ Ω ×ˢ I → y ∉ parabolicHomeomorph '' tsupport w →
        Dtw (parabolicHomeomorph.symm y) i = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact spatialWeakDerivative_ae_zero_off_support hΩ hI hderiv hcompact htsupport i j
  · intro i j k
    exact secondSpatialWeakDerivative_ae_zero_off_support hΩ hI hderiv hcompact htsupport i j k
  · intro i
    exact timeWeakDerivative_ae_zero_off_support hΩ hI hderiv hcompact i


end CKN
