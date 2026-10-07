/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingEstimate

/-!
# Spatial change of variables in the blow-up pairing

The source momentum flux against the pulled-back test is exactly the rescaled
momentum flux against the original test on its compact support.
-/

public section


open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The source test associated with a spatially rescaled compact test. -/
@[expose] def blowupLimitPairingSpatialPullback (x₀ : Vec3) (r : ℝ)
    (w : Vec3 → L2Vec3) : Vec3 → Vec3 :=
  fun y => weakContL3OfLp (w (r⁻¹ • (y - x₀)))

private theorem blowupLimitPairingSpatialPullback_deriv
    {w : Vec3 → L2Vec3}
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    (i j : Fin 3) (x : Vec3) :
    spatialDeriv (fun y => blowupLimitPairingSpatialPullback x₀ r w y i) j
        (x₀ + r • x) =
      r⁻¹ * spatialDeriv (fun y => w y i) j x := by
  let f : Vec3 → ℝ := fun z => w z i
  let g : Vec3 → ℝ := fun z => f (r⁻¹ • z)
  have hcoord (z : Vec3) : weakContL3OfLp (w z) i = w z i := by
    simp [weakContL3OfLp]
  have hfun : (fun y : Vec3 =>
      blowupLimitPairingSpatialPullback x₀ r w y i) =
      fun y => g (y - x₀) := by
    funext y
    simp [blowupLimitPairingSpatialPullback, g, f, hcoord]
  have hshift : (fun y : Vec3 => g (y - x₀)) = fun y => g (-x₀ + y) := by
    funext y
    congr 1
    abel
  have hrescale : fderiv ℝ g (r • x) = r⁻¹ • fderiv ℝ f x := by
    change fderiv ℝ (fun z => f (r⁻¹ • z)) (r • x) = _
    rw [fderiv_comp_smul]
    congr 1
    simp [smul_smul, inv_mul_cancel₀ hr.ne']
  have harg : -x₀ + (x₀ + r • x) = r • x := by abel
  rw [hfun, spatialDeriv, hshift, fderiv_comp_add_left, harg,
    hrescale, spatialDeriv]
  simp [f, smul_eq_mul]

private theorem blowupLimitPairingSpatialPullback_support
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hwsupport : tsupport w ⊆ C) (hC : IsCompact C)
    (x₀ : Vec3) (r : ℝ) (hr : r ≠ 0) :
    tsupport (blowupLimitPairingSpatialPullback x₀ r w) ⊆
      (fun x : Vec3 => x₀ + r • x) '' C := by
  have hclosed : IsClosed ((fun x : Vec3 => x₀ + r • x) '' C) :=
    hC.image (continuous_const.add (continuous_const_smul r)) |>.isClosed
  apply closure_minimal
  · intro y hy
    by_contra hnot
    apply hy
    let x : Vec3 := r⁻¹ • (y - x₀)
    have hAx : x₀ + r • x = y := by
      dsimp [x]
      rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
      abel
    have hxC : x ∉ C := by
      intro hxC
      exact hnot ⟨x, hxC, hAx⟩
    have hxnot : x ∉ tsupport w := fun hx => hxC (hwsupport hx)
    have hwzero : w x = 0 := image_eq_zero_of_notMem_tsupport hxnot
    have hzero : blowupLimitPairingSpatialPullback x₀ r w y = 0 := by
      simp [blowupLimitPairingSpatialPullback, x, hwzero]
    simp [hzero]
  · exact hclosed

private theorem blowupLimitPairingSpatialPullback_compactSupport
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hwsupport : tsupport w ⊆ C) (hC : IsCompact C)
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (blowupLimitPairingSpatialPullback x₀ r w) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hC.image (continuous_const.add (continuous_const_smul r)))
  exact (subset_tsupport _).trans
    (blowupLimitPairingSpatialPullback_support hwsupport hC x₀ r hr.ne')

private theorem blowupLimitPairingSpatial_component_tsupport_subset
    {w : Vec3 → L2Vec3} (i : Fin 3) :
    tsupport (fun x : Vec3 => w x i) ⊆ tsupport w := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    apply hx
    have hwzero : w x = 0 := image_eq_zero_of_notMem_tsupport hnot
    simp [hwzero]
  · exact isClosed_tsupport w

private theorem blowupLimitPairingSpatial_deriv_eq_zero_of_notMem
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hwsupport : tsupport w ⊆ C) {x : Vec3} (hx : x ∉ C)
    (i j : Fin 3) : spatialDeriv (fun y => w y i) j x = 0 := by
  have hcomp : tsupport (fun y : Vec3 => w y i) ⊆ tsupport w :=
    blowupLimitPairingSpatial_component_tsupport_subset i
  have hx' : x ∉ tsupport (spatialDeriv (fun y => w y i) j) := by
    intro hderiv
    exact hx (hwsupport (hcomp (CKN.tsupport_spatialDeriv_subset j hderiv)))
  exact image_eq_zero_of_notMem_tsupport hx'

/-- The source spatial momentum-flux integral against the pulled-back test
equals the rescaled flux integral over the compact support. -/
theorem blowup_limit_rescaled_momentum_flux_spatial_integral
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hwsupport : tsupport w ⊆ C) (hC : IsCompact C)
    (x₀ : Vec3) (t₀ r t : ℝ) (hr : 0 < r)
    (himage : (fun x : Vec3 => x₀ + r • x) '' C ⊆
      vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (htime : t₀ + r ^ 2 * t ∈ Ioo (-1 : ℝ) 0) :
    (∫ y in vec3Ball (0 : Vec3) 1,
      (∑ i : Fin 3, ∑ j : Fin 3,
        u (y, t₀ + r ^ 2 * t) i * u (y, t₀ + r ^ 2 * t) j *
          spatialDeriv
            (fun z => blowupLimitPairingSpatialPullback x₀ r w z i) j y) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        Du (y, t₀ + r ^ 2 * t) i j *
          spatialDeriv
            (fun z => blowupLimitPairingSpatialPullback x₀ r w z i) j y) +
      p (y, t₀ + r ^ 2 * t) *
        ∑ i : Fin 3, spatialDeriv
          (fun z => blowupLimitPairingSpatialPullback x₀ r w z i) i y) =
    ∫ x in C,
      (∑ i : Fin 3, ∑ j : Fin 3,
        blowupVelocity x₀ t₀ r u (x,t) i *
          blowupVelocity x₀ t₀ r u (x,t) j *
          spatialDeriv (fun z => w z i) j x) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        blowupGradient x₀ t₀ r Du (x,t) i j *
          spatialDeriv (fun z => w z i) j x) +
      blowupPressure x₀ t₀ r p (x,t) *
        ∑ i : Fin 3, spatialDeriv (fun z => w z i) i x := by
  let A : Vec3 → Vec3 := fun x => x₀ + r • x
  let ψ := blowupLimitPairingSpatialPullback x₀ r w
  let H : Vec3 → ℝ := fun y =>
    (∑ i : Fin 3, ∑ j : Fin 3,
      u (y, t₀ + r ^ 2 * t) i * u (y, t₀ + r ^ 2 * t) j *
        spatialDeriv (fun z => ψ z i) j y) -
    (∑ i : Fin 3, ∑ j : Fin 3,
      Du (y, t₀ + r ^ 2 * t) i j *
        spatialDeriv (fun z => ψ z i) j y) +
    p (y, t₀ + r ^ 2 * t) *
      ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
  let T : Vec3 → ℝ := fun x =>
    (∑ i : Fin 3, ∑ j : Fin 3,
      blowupVelocity x₀ t₀ r u (x,t) i *
        blowupVelocity x₀ t₀ r u (x,t) j *
        spatialDeriv (fun z => w z i) j x) -
    (∑ i : Fin 3, ∑ j : Fin 3,
      blowupGradient x₀ t₀ r Du (x,t) i j *
        spatialDeriv (fun z => w z i) j x) +
    blowupPressure x₀ t₀ r p (x,t) *
      ∑ i : Fin 3, spatialDeriv (fun z => w z i) i x
  have hAx (x : Vec3) : A (r⁻¹ • (A x - x₀)) = A x := by
    dsimp [A]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hAinv (y : Vec3) : A (r⁻¹ • (y - x₀)) = y := by
    dsimp [A]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hBallSub : vec3Ball (0 : Vec3) (3 / 4 : ℝ) ⊆
      vec3Ball (0 : Vec3) 1 := by
    intro z hz
    have hnorm : vec3EuclideanNorm (z - 0) < 3 / 4 := by
      simpa only [mem_vec3Ball] using hz
    have hnorm' : vec3EuclideanNorm (z - 0) < 1 :=
      lt_trans hnorm (by norm_num)
    simpa only [mem_vec3Ball] using hnorm'
  have hderiv (x : Vec3) (i j : Fin 3) :
      spatialDeriv (fun z => ψ z i) j (A x) =
        r⁻¹ * spatialDeriv (fun z => w z i) j x := by
    simpa only [A, ψ] using
      blowupLimitPairingSpatialPullback_deriv x₀ r hr i j x
  have htestzero (x : Vec3) (hx : x ∉ C) (i j : Fin 3) :
      spatialDeriv (fun z => w z i) j x = 0 :=
    blowupLimitPairingSpatial_deriv_eq_zero_of_notMem hwsupport hx i j
  have hpoint (x : Vec3) : T x = r ^ 3 * H (A x) := by
    by_cases hx : x ∈ C
    · have hball : A x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) :=
        himage ⟨x, hx, rfl⟩
      have hball₁ : A x ∈ vec3Ball (0 : Vec3) 1 := by
        have hnorm : vec3EuclideanNorm (A x - 0) < 3 / 4 := by
          simpa only [mem_vec3Ball] using hball
        have hnorm' : vec3EuclideanNorm (A x - 0) < 1 :=
          lt_trans hnorm (by norm_num)
        simpa only [mem_vec3Ball] using hnorm'
      have hmem : (A x, t₀ + r ^ 2 * t) ∈ goodPointDomain := by
        exact ⟨hball₁, htime⟩
      have hU (i : Fin 3) :
          blowupVelocity x₀ t₀ r u (x,t) i =
            r * u (A x, t₀ + r ^ 2 * t) i := by
        rw [blowupVelocity_eq_of_mem x₀ t₀ r u (x,t) hmem]
        simp [A, parabolicTranslate, parabolicScale, Pi.smul_apply, smul_eq_mul]
      have hDU (i j : Fin 3) :
          blowupGradient x₀ t₀ r Du (x,t) i j =
            r ^ 2 * Du (A x, t₀ + r ^ 2 * t) i j := by
        rw [blowupGradient_eq_of_mem x₀ t₀ r Du (x,t) hmem]
        simp [A, parabolicTranslate, parabolicScale, Pi.smul_apply, smul_eq_mul]
      have hP : blowupPressure x₀ t₀ r p (x,t) =
          r ^ 2 * p (A x, t₀ + r ^ 2 * t) := by
        rw [blowupPressure_eq_of_mem x₀ t₀ r p (x,t) hmem]
        simp [A, parabolicTranslate, parabolicScale]
      have hconv :
          (∑ i : Fin 3, ∑ j : Fin 3,
            blowupVelocity x₀ t₀ r u (x,t) i *
              blowupVelocity x₀ t₀ r u (x,t) j *
              spatialDeriv (fun z => w z i) j x) =
          r ^ 3 * (∑ i : Fin 3, ∑ j : Fin 3,
            u (A x, t₀ + r ^ 2 * t) i *
              u (A x, t₀ + r ^ 2 * t) j *
              spatialDeriv (fun z => ψ z i) j (A x)) := by
        calc
          _ = ∑ i : Fin 3, ∑ j : Fin 3,
              r ^ 3 * (u (A x, t₀ + r ^ 2 * t) i *
                u (A x, t₀ + r ^ 2 * t) j *
                spatialDeriv (fun z => ψ z i) j (A x)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hU i, hU j, hderiv x i j]
                  field_simp [hr.ne']
          _ = _ := by simp [Finset.mul_sum]
      have hdiff :
          (∑ i : Fin 3, ∑ j : Fin 3,
            blowupGradient x₀ t₀ r Du (x,t) i j *
              spatialDeriv (fun z => w z i) j x) =
          r ^ 3 * (∑ i : Fin 3, ∑ j : Fin 3,
            Du (A x, t₀ + r ^ 2 * t) i j *
              spatialDeriv (fun z => ψ z i) j (A x)) := by
        calc
          _ = ∑ i : Fin 3, ∑ j : Fin 3,
              r ^ 3 * (Du (A x, t₀ + r ^ 2 * t) i j *
                spatialDeriv (fun z => ψ z i) j (A x)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hDU i j, hderiv x i j]
                  field_simp [hr.ne']
          _ = _ := by simp [Finset.mul_sum]
      have hsum :
          (∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i (A x)) =
            r⁻¹ * ∑ i : Fin 3, spatialDeriv (fun z => w z i) i x := by
        simp_rw [hderiv]
        rw [← Finset.mul_sum]
      have hpres :
          blowupPressure x₀ t₀ r p (x,t) *
              ∑ i : Fin 3, spatialDeriv (fun z => w z i) i x =
          r ^ 3 * (p (A x, t₀ + r ^ 2 * t) *
              ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i (A x)) := by
        rw [hP, hsum]
        field_simp [hr.ne']
      dsimp [T, H]
      rw [hconv, hdiff, hpres]
      ring
    · have hDw (i j : Fin 3) : spatialDeriv (fun z => w z i) j x = 0 :=
        htestzero x hx i j
      have hH : H (A x) = 0 := by
        dsimp [H]
        simp_rw [hderiv, hDw]
        simp
      have hT : T x = 0 := by
        dsimp [T]
        simp_rw [hDw]
        simp
      rw [hT, hH]
      ring
  have hzeroH (y : Vec3) (hy : y ∉ vec3Ball (0 : Vec3) 1) : H y = 0 := by
    let x : Vec3 := r⁻¹ • (y - x₀)
    have hAx : A x = y := by simpa [x] using hAinv y
    have hxC : x ∉ C := by
      intro hx
      have hyball := himage ⟨x, hx, hAx⟩
      exact hy (hBallSub hyball)
    have hDw (i j : Fin 3) : spatialDeriv (fun z => w z i) j x = 0 :=
      htestzero x hxC i j
    have hpull (i j : Fin 3) : spatialDeriv (fun z => ψ z i) j y = 0 := by
      have h := hderiv x i j
      rw [hAx] at h
      rw [h]
      simp [hDw]
    dsimp [H]
    simp_rw [hpull]
    simp
  have hwhole : (∫ x : Vec3, T x) = ∫ y : Vec3, H y := by
    calc
      (∫ x : Vec3, T x) = ∫ x : Vec3, r ^ 3 * H (A x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = r ^ 3 * ∫ x : Vec3, H (A x) := by rw [integral_const_mul]
      _ = r ^ 3 * (r⁻¹ ^ 3 * ∫ y : Vec3, H y) := by
        rw [show (fun x : Vec3 => H (A x)) = fun x => H (x₀ + r • x) by
          rfl, blowup_limit_integral_comp_affine H x₀ r hr]
      _ = ∫ y : Vec3, H y := by
        have hrne : r ≠ 0 := ne_of_gt hr
        field_simp [hrne]
  have hTzero (x : Vec3) (hx : x ∉ C) : T x = 0 := by
    dsimp [T]
    simp_rw [htestzero x hx]
    simp
  have hsource : (∫ y in vec3Ball (0 : Vec3) 1, H y) =
      ∫ y : Vec3, H y := by
    symm
    rw [← integral_indicator (isOpen_vec3Ball (0 : Vec3) 1).measurableSet]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ vec3Ball (0 : Vec3) 1
    · simp [hy]
    · simp [hy, hzeroH y hy]
  have htarget : (∫ x in C, T x) = ∫ x : Vec3, T x := by
    symm
    rw [← integral_indicator hC.measurableSet]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ C
    · simp [hx]
    · simp [hx, hTzero x hx]
  dsimp [H, T, ψ] at hsource htarget ⊢
  calc
    _ = ∫ y in vec3Ball (0 : Vec3) 1, H y := rfl
    _ = ∫ y : Vec3, H y := hsource
    _ = ∫ x : Vec3, T x := hwhole.symm
    _ = ∫ x in C, T x := htarget.symm

end ESS

end
