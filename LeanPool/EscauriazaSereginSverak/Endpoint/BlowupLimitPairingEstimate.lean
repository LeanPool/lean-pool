/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingAllTests
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitRepresentativeExtension
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGeometry
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Pairings under parabolic rescaling

Spatial test functions and their momentum pairings transform covariantly
under the affine maps used in `prop:blowup-limit`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Change variables in an integral under a spatial translation and positive
dilation. -/
theorem blowup_limit_integral_comp_affine (f : Vec3 → ℝ)
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    (∫ x : Vec3, f (x₀ + r • x)) = r⁻¹ ^ 3 * ∫ y : Vec3, f y := by
  let g : Vec3 → ℝ := fun y => f (x₀ + y)
  have htrans : (∫ y : Vec3, g y) = ∫ y : Vec3, f y := by
    calc
      (∫ y : Vec3, g y) = ∫ y : Vec3, f (x₀ - (-y)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [g]
        congr 1
        abel
      _ = ∫ y : Vec3, f (x₀ - y) := by
        exact (Measure.measurePreserving_neg (volume : Measure Vec3)).integral_comp
          (Homeomorph.neg Vec3).measurableEmbedding (fun y => f (x₀ - y))
      _ = ∫ y : Vec3, f y := by
        exact (Measure.measurePreserving_sub_left (volume : Measure Vec3) x₀).integral_comp
          (Homeomorph.subLeft x₀).measurableEmbedding f
  have hscale := Measure.integral_comp_smul (volume : Measure Vec3) g r
  have hdim : Module.finrank ℝ Vec3 = 3 := by
    simp [Vec3]
  rw [show (fun x : Vec3 => f (x₀ + r • x)) = fun x => g (r • x) by
    funext x
    rfl, hscale, hdim, abs_of_pos (inv_pos.mpr (pow_pos hr 3)), htrans]
  simp only [smul_eq_mul, inv_pow]

private theorem blowupLimit_interval_integral_comp_add_mul
    (f : ℝ → ℝ) (x₀ r s t : ℝ) (hr : 0 < r) :
    r⁻¹ ^ 2 * (∫ τ in (x₀ + r ^ 2 * s)..(x₀ + r ^ 2 * t), f τ) =
      ∫ τ in s..t, f (x₀ + r ^ 2 * τ) := by
  have hchange := intervalIntegral.mul_integral_comp_add_mul
    (f := f) (a := s) (b := t) (c := r ^ 2) (d := x₀)
  have hcoeff : r⁻¹ ^ 2 * r ^ 2 = 1 := by
    field_simp [hr.ne']
  calc
    r⁻¹ ^ 2 * (∫ τ in (x₀ + r ^ 2 * s)..(x₀ + r ^ 2 * t), f τ) =
        r⁻¹ ^ 2 * (r ^ 2 * ∫ τ in s..t, f (x₀ + r ^ 2 * τ)) := by
          congr 1
          simp
    _ = ∫ τ in s..t, f (x₀ + r ^ 2 * τ) := by
      calc
        _ = (r⁻¹ ^ 2 * r ^ 2) * ∫ τ in s..t, f (x₀ + r ^ 2 * τ) := by ring
        _ = _ := by rw [hcoeff]; simp

/-- A vector test pulled back along translation and parabolic spatial rescaling. -/
@[expose] def blowupLimitPullbackTest (x₀ : Vec3) (r : ℝ)
    (w : Vec3 → L2Vec3) : Vec3 → Vec3 :=
  fun y => weakContL3OfLp (w (r⁻¹ • (y - x₀)))

private theorem blowupLimitPullbackTest_contDiff
    {w : Vec3 → L2Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (x₀ : Vec3) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (blowupLimitPullbackTest x₀ r w) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => r⁻¹ • (y - x₀)) :=
    (contDiff_const_smul r⁻¹).comp (contDiff_id.sub contDiff_const)
  exact weakContL3OfLp.contDiff.comp (hw.comp hA)

private theorem blowupLimitPullbackTest_spatialDeriv
    {w : Vec3 → L2Vec3} (x₀ : Vec3) (r : ℝ) (hr : r ≠ 0)
    (i j : Fin 3) (x : Vec3) :
    spatialDeriv (fun y => blowupLimitPullbackTest x₀ r w y i) j
        (x₀ + r • x) =
      r⁻¹ * spatialDeriv (fun y => weakContL3OfLp (w y) i) j x := by
  let f : Vec3 → ℝ := fun z => weakContL3OfLp (w z) i
  let g : Vec3 → ℝ := fun z => f (r⁻¹ • z)
  have hfun : (fun y : Vec3 =>
      blowupLimitPullbackTest x₀ r w y i) =
      fun y => g (y - x₀) := rfl
  have hshift : (fun y : Vec3 => g (y - x₀)) = fun y => g (-x₀ + y) := by
    funext y
    congr 1
    abel
  have hrescale : fderiv ℝ g (r • x) = r⁻¹ • fderiv ℝ f x := by
    change fderiv ℝ (fun z => f (r⁻¹ • z)) (r • x) = _
    rw [fderiv_comp_smul]
    congr 1
    simp [smul_smul, inv_mul_cancel₀ hr]
  have harg : -x₀ + (x₀ + r • x) = r • x := by abel
  rw [hfun, spatialDeriv, hshift, fderiv_comp_add_left, harg, hrescale,
    spatialDeriv]
  simp [f, smul_eq_mul]

private theorem blowupLimitPullbackTest_support
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hwsupport : tsupport w ⊆ C) (hC : IsCompact C)
    (x₀ : Vec3) (r : ℝ) (hr : r ≠ 0) :
    tsupport (blowupLimitPullbackTest x₀ r w) ⊆
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
    have hzero : blowupLimitPullbackTest x₀ r w y = 0 := by
      simp [blowupLimitPullbackTest, x, hwzero]
    simp [hzero]
  · exact hclosed

private theorem blowupLimitPullbackTest_hasCompactSupport
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hwsupport : tsupport w ⊆ C) (hC : IsCompact C)
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (blowupLimitPullbackTest x₀ r w) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hC.image (continuous_const.add (continuous_const_smul r)))
  exact (subset_tsupport _).trans
    (blowupLimitPullbackTest_support hwsupport hC x₀ r hr.ne')

private theorem blowupLimit_affine_image_ball_subset
    {C : Set Vec3} (S : ℝ) (hC : C ⊆ vec3Ball (0 : Vec3) S)
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    (hball : vec3Ball x₀ (r * S) ⊆
      vec3Ball (0 : Vec3) (3 / 4 : ℝ)) :
    (fun x : Vec3 => x₀ + r • x) '' C ⊆
      vec3Ball (0 : Vec3) (3 / 4 : ℝ) := by
  intro y hy
  rcases hy with ⟨x, hxC, rfl⟩
  apply hball
  have hxnorm : vec3EuclideanNorm (x - 0) < S := by
    simpa only [mem_vec3Ball, sub_zero] using hC hxC
  have hscaled : vec3EuclideanNorm (r • x) < r * S := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hr]
    exact mul_lt_mul_of_pos_left (by simpa only [sub_zero] using hxnorm) hr
  simpa only [mem_vec3Ball, add_sub_cancel_left] using hscaled

private theorem blowupLimitOfLp_coordinate (z : L2Vec3) (i : Fin 3) :
    weakContL3OfLp z i = z i := by
  simp [weakContL3OfLp]

private theorem blowupLimit_trace_pairing_affine
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hW : ∀ t,
      (fun x => W (x, t)) =ᵐ[volume.restrict
        (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
        (fun x => weakContL3OfLp (v t x)))
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hwsupport : tsupport w ⊆ C) (hC : IsCompact C)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (himage : (fun x : Vec3 => x₀ + r • x) '' C ⊆
      vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (t : ℝ) (ht : t₀ + r ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) :
    (∫ x : Vec3, ∑ i : Fin 3,
      blowupLimitTraceRescaling W x₀ t₀ r (x, t) i * w x i) =
      r⁻¹ ^ 2 * (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3,
          v ⟨t₀ + r ^ 2 * t, ht⟩ y i *
            blowupLimitPullbackTest x₀ r w y i) := by
  let B : Set Vec3 := vec3Ball (0 : Vec3) (3 / 4 : ℝ)
  let τ : Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨t₀ + r ^ 2 * t, ht⟩
  let ψ := blowupLimitPullbackTest x₀ r w
  have hψsupport : tsupport ψ ⊆ B := by
    dsimp [ψ, B]
    exact (blowupLimitPullbackTest_support hwsupport hC x₀ r hr.ne').trans
      (by simpa using himage)
  have hτpoint (x : Vec3) :
      blowupLimitTraceRescaling W x₀ t₀ r (x, t) =
        r • B.indicator (fun y => W (y,τ)) (x₀ + r • x) := by
    by_cases hx : x₀ + r • x ∈ B
    · have hpair : x₀ + r • x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ∧
          t₀ + r ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨hx, ht⟩
      have hτeq : (⟨t₀ + r ^ 2 * t, hpair.2⟩ :
          Icc (-(3 / 4 : ℝ) ^ 2) 0) = τ := by
        apply Subtype.ext
        rfl
      simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
        parabolicTranslate, parabolicScale, B, τ, hpair, hτeq]
    · simp [blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
        parabolicTranslate, parabolicScale, B, τ, hx]
  let f : Vec3 → ℝ := B.indicator
    (fun y => ∑ i : Fin 3, W (y,τ) i * ψ y i)
  have hpoint : (fun x : Vec3 =>
      ∑ i : Fin 3, blowupLimitTraceRescaling W x₀ t₀ r (x, t) i * w x i) =
      fun x => r * f (x₀ + r • x) := by
    funext x
    by_cases hx : x₀ + r • x ∈ B
    · have htest : ψ (x₀ + r • x) = weakContL3OfLp (w x) := by
        simp [ψ, blowupLimitPullbackTest, smul_smul,
          inv_mul_cancel₀ hr.ne']
      rw [hτpoint x]
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hx]
      simp only [f, Set.indicator_of_mem hx]
      change ∑ i : Fin 3, (r * W (x₀ + r • x,τ) i) * w x i =
        r * ∑ i : Fin 3, W (x₀ + r • x,τ) i * ψ (x₀ + r • x) i
      rw [htest]
      simp only [blowupLimitOfLp_coordinate]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    · have hxnot : x ∉ tsupport w := by
        intro hxw
        exact hx (himage ⟨x, hwsupport hxw, rfl⟩)
      have hwzero : w x = 0 := image_eq_zero_of_notMem_tsupport hxnot
      simp [f, hτpoint x, B, hx, hwzero]
  have hsource :
      (∫ y : Vec3, f y) =
        ∫ y in B, ∑ i : Fin 3,
          v τ y i * ψ y i := by
    calc
      (∫ y : Vec3, f y) =
          ∫ y in B, ∑ i : Fin 3, W (y,τ) i * ψ y i := by
            rw [show f = B.indicator
              (fun y => ∑ i : Fin 3, W (y,τ) i * ψ y i) by rfl]
            exact integral_indicator (isOpen_vec3Ball _ _).measurableSet
      _ = ∫ y in B, ∑ i : Fin 3, v τ y i * ψ y i := by
            apply setIntegral_congr_ae (isOpen_vec3Ball _ _).measurableSet
            filter_upwards [(ae_restrict_iff'
              (isOpen_vec3Ball (0 : Vec3) (3 / 4 : ℝ)).measurableSet).mp (hW τ)]
              with y hy hBy
            rw [hy hBy]
            simp only [blowupLimitOfLp_coordinate]
  calc
    _ = ∫ x : Vec3, r * f (x₀ + r • x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact congrFun hpoint x
    _ = r * ∫ x : Vec3, f (x₀ + r • x) := integral_const_mul _ _
    _ = r * (r⁻¹ ^ 3 * ∫ y : Vec3, f y) := by
          rw [blowup_limit_integral_comp_affine f x₀ r hr]
    _ = r⁻¹ ^ 2 * (∫ y in B, ∑ i : Fin 3,
          v τ y i * ψ y i) := by
          rw [hsource]
          have hcoef : r * r⁻¹ ^ 3 = r⁻¹ ^ 2 := by
            field_simp [hr.ne']
          calc
            r * (r⁻¹ ^ 3 * ∫ y in B, ∑ i : Fin 3,
                v τ y i * ψ y i) =
              (r * r⁻¹ ^ 3) * ∫ y in B, ∑ i : Fin 3,
                v τ y i * ψ y i := by ring
            _ = _ := by rw [hcoef]

/-- A compactly supported rescaled test pairs with the all-time source trace
by the source momentum formula, with the exact parabolic time factor. -/
theorem blowup_limit_rescaled_trace_pairing_source_formula
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hW : ∀ t,
      (fun x => W (x, t)) =ᵐ[volume.restrict
        (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
        (fun x => weakContL3OfLp (v t x)))
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hformula : ∀ ψ : Vec3 → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) →
      ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v t y i * ψ y i) -
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v s y i * ψ y i) =
        ∫ τ in s.1..t.1, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y,τ) i * u (y,τ) j * spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y,τ) i j * spatialDeriv (fun z => ψ z i) j y)
          + p (y,τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
          ∂volume)
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupport : tsupport w ⊆ C)
    (hC : IsCompact C)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (himage : (fun x : Vec3 => x₀ + r • x) '' C ⊆
      vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (a b : ℝ)
    (htime : ∀ t, t ∈ Icc a b →
      t₀ + r ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) :
    ∀ s t : Icc a b,
      (∫ x : Vec3, ∑ i : Fin 3,
        blowupLimitTraceRescaling W x₀ t₀ r (x,t.1) i * w x i) -
      (∫ x : Vec3, ∑ i : Fin 3,
        blowupLimitTraceRescaling W x₀ t₀ r (x,s.1) i * w x i) =
      r⁻¹ ^ 2 *
        (∫ τ in (t₀ + r ^ 2 * s.1)..(t₀ + r ^ 2 * t.1),
          ∫ y in vec3Ball (0 : Vec3) 1,
            (∑ i : Fin 3, ∑ j : Fin 3,
              u (y,τ) i * u (y,τ) j *
                spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) j y)
            - (∑ i : Fin 3, ∑ j : Fin 3,
              Du (y,τ) i j *
                spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) j y)
            + p (y,τ) * ∑ i : Fin 3,
                spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) i y
            ∂volume) := by
  let ψ : Vec3 → Vec3 := blowupLimitPullbackTest x₀ r w
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    dsimp [ψ]
    exact blowupLimitPullbackTest_contDiff hw x₀ r
  have hψsupport : tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) := by
    dsimp [ψ]
    exact (blowupLimitPullbackTest_support hwsupport hC x₀ r hr.ne').trans
      himage
  have hψcompact : HasCompactSupport ψ := by
    dsimp [ψ]
    exact blowupLimitPullbackTest_hasCompactSupport hwsupport hC x₀ r hr
  have hformula' := hformula ψ hψsmooth hψcompact hψsupport
  intro s t
  let τs : Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨t₀ + r ^ 2 * s.1, htime s.1 s.2⟩
  let τt : Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨t₀ + r ^ 2 * t.1, htime t.1 t.2⟩
  have hleft := blowupLimit_trace_pairing_affine v W hW
    hwsupport hC x₀ t₀ r hr himage s.1 (htime s.1 s.2)
  have hright := blowupLimit_trace_pairing_affine v W hW
    hwsupport hC x₀ t₀ r hr himage t.1 (htime t.1 t.2)
  rw [hright, hleft]
  have htimeFormula := hformula' τs τt
  change r⁻¹ ^ 2 *
      (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v τt y i * ψ y i) -
      r⁻¹ ^ 2 *
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v τs y i * ψ y i) = _
  calc
    _ = r⁻¹ ^ 2 *
        ((∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
            ∑ i : Fin 3, v τt y i * ψ y i) -
          (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
            ∑ i : Fin 3, v τs y i * ψ y i)) := by ring
    _ = r⁻¹ ^ 2 *
        (∫ τ in τs.1..τt.1, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y,τ) i * u (y,τ) j * spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y,τ) i j * spatialDeriv (fun z => ψ z i) j y)
          + p (y,τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
          ∂volume) := by rw [htimeFormula]
    _ = _ := rfl

/-- The source formula remains an interval-integral identity after parabolic
time reparameterization, including either endpoint of the closed interval. -/
theorem blowup_limit_rescaled_trace_pairing_source_time_formula
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hW : ∀ t,
      (fun x => W (x, t)) =ᵐ[volume.restrict
        (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
        (fun x => weakContL3OfLp (v t x)))
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hformula : ∀ ψ : Vec3 → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) →
      ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v t y i * ψ y i) -
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v s y i * ψ y i) =
        ∫ τ in s.1..t.1, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y,τ) i * u (y,τ) j * spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y,τ) i j * spatialDeriv (fun z => ψ z i) j y)
          + p (y,τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
          ∂volume)
    {w : Vec3 → L2Vec3} {C : Set Vec3}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupport : tsupport w ⊆ C)
    (hC : IsCompact C)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (himage : (fun x : Vec3 => x₀ + r • x) '' C ⊆
      vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (a b : ℝ)
    (htime : ∀ t, t ∈ Icc a b →
      t₀ + r ^ 2 * t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) :
    ∀ s t : Icc a b,
      (∫ x : Vec3, ∑ i : Fin 3,
        blowupLimitTraceRescaling W x₀ t₀ r (x,t.1) i * w x i) -
      (∫ x : Vec3, ∑ i : Fin 3,
        blowupLimitTraceRescaling W x₀ t₀ r (x,s.1) i * w x i) =
      ∫ τ in s.1..t.1, ∫ y in vec3Ball (0 : Vec3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u (y,t₀ + r ^ 2 * τ) i * u (y,t₀ + r ^ 2 * τ) j *
            spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) j y)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          Du (y,t₀ + r ^ 2 * τ) i j *
            spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) j y)
        + p (y,t₀ + r ^ 2 * τ) * ∑ i : Fin 3,
            spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) i y
        ∂volume := by
  have hsource := blowup_limit_rescaled_trace_pairing_source_formula
    v W hW hformula hw hwsupport hC x₀ t₀ r hr himage a b htime
  intro s t
  let F : ℝ → ℝ := fun τ =>
    ∫ y in vec3Ball (0 : Vec3) 1,
      (∑ i : Fin 3, ∑ j : Fin 3,
        u (y,τ) i * u (y,τ) j *
          spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) j y)
      - (∑ i : Fin 3, ∑ j : Fin 3,
        Du (y,τ) i j *
          spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) j y)
      + p (y,τ) * ∑ i : Fin 3,
          spatialDeriv (fun z => blowupLimitPullbackTest x₀ r w z i) i y
      ∂volume
  rw [hsource s t]
  simpa only [F] using
    blowupLimit_interval_integral_comp_add_mul F t₀ r s.1 t.1 hr


end ESS

end
