/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.MixedTermTransferBounds
public import LeanPool.CIVAxisymmetric.Closure.MixedTermErrorBound
public import LeanPool.CIVAxisymmetric.Closure.MixedTermEllipticCauchySchwarz
public import LeanPool.CIVAxisymmetric.Closure.MixedTermBound

/-!
# The mixed-term estimate `eq:aniso:closure:mixed:bound` of `lem:aniso:closure`

This assembles the mixed-term bound of `lem:aniso:closure` from its four already-proved
pieces:

* the `z` integration by parts of `eq:aniso:closure:mixed`
  (`integral_cutoff_sq_stretchMixedTerm_eq`);
* the swirl bound `|u_θ| ≤ W` on `tsupport χ` (`hW`, carried the same way
  `energy_inequality_of_mixed_term_bound_of_split` carries it);
* the representative-to-Cartesian `L²` transfer of `CIV.Closure.MixedTermTransferBounds`,
  feeding the elliptic and div–curl bounds of `CIV.Closure.EllipticBoundsAnnulusBound`;
* the elliptic Cauchy–Schwarz step (`abs_integral_mul_le_sqrt_mul_sqrt`) and the final
  Young's-inequality absorption (`mixed_term_bound_of_cauchy_schwarz`).

The `∂_zχ`-carrying error term of the integration by parts is bounded separately, by a
constant that does not depend on `t` (`CIV.Closure.MixedTermErrorBound`), from the same
order-`≤ 2` annulus data that supplies the elliptic bounds.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



private theorem mixedTerm_factors_memLp
    {u : ParabolicPoint → Vec3} {χ : Vec3 → ℝ} {t : ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) (htmem : t ∈ Ioo (-1 : ℝ) 0) :
    MemLp (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1 * χ x *
      spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) 2 volume ∧
    MemLp (fun x : Vec3 => χ x * curlComp u 2 (meridional (polarR x) (x 2), t)) 2 volume ∧
    MemLp (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1 * χ x *
      spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) 2 volume ∧
    MemLp (fun x : Vec3 => χ x *
      spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t)) 2 volume := by
  set f2 : Vec3 → ℝ := fun x => u (meridional (polarR x) (x 2), t) 1 * χ x
      * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t) with hf2_def
  set g2 : Vec3 → ℝ := fun x => χ x * curlComp u 2 (meridional (polarR x) (x 2), t) with hg2_def
  set f3 : Vec3 → ℝ := fun x => u (meridional (polarR x) (x 2), t) 1 * χ x
      * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t) with hf3_def
  set g3 : Vec3 → ℝ := fun x => χ x
      * spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t) with hg3_def
  have hMemF2 : MemLp f2 2 volume := by
    have hcontA : ContinuousOn
        (fun x : Vec3 => spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t))
        (vec3Ball (0 : Vec3) 1) := by
      have hsmoothA : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y : Vec3 => spatialSecondPartial (fun w => u w 2) 0 2 (y, t))
          (vec3Ball (0 : Vec3) 1) :=
        ((contDiffOn_slice_partial hu 2 0 htmem).fderiv_of_isOpen (isOpen_vec3Ball 0 1)
          (by simp)).clm_apply contDiffOn_const
      exact hsmoothA.continuousOn.comp' mixedTerm_continuousOn_repMap mixedTerm_mapsTo_repMap
    have hcontSwirl : ContinuousOn (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1)
        (vec3Ball (0 : Vec3) 1) :=
      (continuousOn_vel_slice hu 1 htmem).comp' mixedTerm_continuousOn_repMap
        mixedTerm_mapsTo_repMap
    refine memLp_two_of_cutoff hχs hsupp
      ((hcontSwirl.mul hχ.continuous.continuousOn).mul hcontA) (fun x hx => ?_)
    rw [hf2_def]; simp [image_eq_zero_of_notMem_tsupport hx]
  have hMemG2 : MemLp g2 2 volume := by
    have hcontWz : ContinuousOn (fun x : Vec3 => curlComp u 2 (meridional (polarR x) (x 2), t))
        (vec3Ball (0 : Vec3) 1) :=
      (continuousOn_curl_slice hu 2 htmem).comp' mixedTerm_continuousOn_repMap
        mixedTerm_mapsTo_repMap
    refine memLp_two_of_cutoff hχs hsupp (hχ.continuous.continuousOn.mul hcontWz)
      (fun x hx => ?_)
    rw [hg2_def]; simp [image_eq_zero_of_notMem_tsupport hx]
  have hMemF3 : MemLp f3 2 volume := by
    have hcontA : ContinuousOn
        (fun x : Vec3 => spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t))
        (vec3Ball (0 : Vec3) 1) :=
      (continuousOn_dvel_slice hu 2 0 htmem).comp' mixedTerm_continuousOn_repMap
        mixedTerm_mapsTo_repMap
    have hcontSwirl : ContinuousOn (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1)
        (vec3Ball (0 : Vec3) 1) :=
      (continuousOn_vel_slice hu 1 htmem).comp' mixedTerm_continuousOn_repMap
        mixedTerm_mapsTo_repMap
    refine memLp_two_of_cutoff hχs hsupp
      ((hcontSwirl.mul hχ.continuous.continuousOn).mul hcontA) (fun x hx => ?_)
    rw [hf3_def]; simp [image_eq_zero_of_notMem_tsupport hx]
  have hMemG3 : MemLp g3 2 volume := by
    have hcontdWz : ContinuousOn
        (fun x : Vec3 => spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x
          2), t))
        (vec3Ball (0 : Vec3) 1) :=
      (continuousOn_dcurl_slice hu 2 2 htmem).comp' mixedTerm_continuousOn_repMap
        mixedTerm_mapsTo_repMap
    refine memLp_two_of_cutoff hχs hsupp (hχ.continuous.continuousOn.mul hcontdWz)
      (fun x hx => ?_)
    rw [hg3_def]; simp [image_eq_zero_of_notMem_tsupport hx]
  exact ⟨hMemF2, hMemG2, hMemF3, hMemG3⟩

/-- **`eq:aniso:closure:mixed:bound`.** For a classical solution with a cutoff `χ` supported
in `B(ρ)`, `0 < ρ`, order-`≤ 2` derivative bounds for `u` on the closed annulus `A` carrying
`∇χ`, and a swirl bound `|u_θ| ≤ W` on `B(ρ)`, the mixed summand `I(t) = ∫ χ² (∂_r u_z) ω_r ω_z`
of the tested vortex-stretching term satisfies
`I(t) ≤ (1/4) M(t) + C (W(t)² + 1) (Y(t) + 1)` on `(t₀, 0)`, for some `C ≥ 0`. -/
theorem step_closure_mixed_term
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1) (hρpos : 0 < ρ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ} (hMu : 0 ≤ Mu)
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu)
    {W : ℝ → ℝ}
    (hW : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ), |∫ x : Vec3, χ x ^ 2 * stretchMixedTerm u x t|
      ≤ (1 / 4) * cutoffEnstrophyDissipation χ u t
        + C * (W t ^ 2 + 1) * (cutoffEnstrophy χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hmerid0 : (meridional (0 : ℝ) (0 : ℝ) : Vec3) = 0 := by
    funext i; fin_cases i <;> simp [meridional]
  have h0mem : (meridional (0 : ℝ) (0 : ℝ) : Vec3) ∈ vec3Ball (0 : Vec3) ρ := by
    rw [hmerid0, mem_vec3Ball, sub_zero, vec3EuclideanNorm_zero]
    exact hρpos
  obtain ⟨C1, hC1nn, hC1⟩ := exists_integral_sq_swirl_mul_cutoff_mul_firstPartial_rep_le
    hsol haxi hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound hW
  obtain ⟨C2, hC2nn, hC2⟩ := exists_integral_sq_swirl_mul_cutoff_mul_secondPartial_rep_le
    hsol haxi hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound hW
  obtain ⟨C0, hC0nn, hC0⟩ := exists_abs_integral_swirl_mul_dzChi_error_le
    hsol hχ hχs hρU hρ1 ht₀ hχA hMu hAsub hbound
  set Cs1 : ℝ := Real.sqrt C1 with hCs1_def
  set Cs2 : ℝ := Real.sqrt C2 with hCs2_def
  have hCs1nn : 0 ≤ Cs1 := Real.sqrt_nonneg _
  have hCs2nn : 0 ≤ Cs2 := Real.sqrt_nonneg _
  set C₁ : ℝ := max Cs1 Cs2 with hC1_def
  have hC₁nn : 0 ≤ C₁ := le_trans hCs1nn (le_max_left _ _)
  refine ⟨C0 + 1 / 8 + 4 * C₁ ^ 2, by positivity, fun t ht => ?_⟩
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hWnn : 0 ≤ W t := le_trans (abs_nonneg _) (hW t ht 0 0 h0mem)
  -- The `z` integration by parts.
  have hIBP := integral_cutoff_sq_stretchMixedTerm_eq haxi hu hχ hχs (hρU.trans hρ1) htmem
  -- The two Cauchy–Schwarz factor pairs.
  set f2 : Vec3 → ℝ := fun x => u (meridional (polarR x) (x 2), t) 1 * χ x
      * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t) with hf2_def
  set g2 : Vec3 → ℝ := fun x => χ x * curlComp u 2 (meridional (polarR x) (x 2), t) with hg2_def
  set f3 : Vec3 → ℝ := fun x => u (meridional (polarR x) (x 2), t) 1 * χ x
      * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t) with hf3_def
  set g3 : Vec3 → ℝ := fun x => χ x
      * spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t) with hg3_def
  obtain ⟨hMemF2, hMemG2, hMemF3, hMemG3⟩ :=
    mixedTerm_factors_memLp hu hχ hχs (hρU.trans hρ1) htmem
  -- The `∂_zχ`-carrying error term, as a raw function of `x`.
  set errTerm : Vec3 → ℝ := fun x => u (meridional (polarR x) (x 2), t) 1
      * (2 * χ x * fderiv ℝ χ x (basisVec 2)
        * (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
          * curlComp u 2 (meridional (polarR x) (x 2), t))) with herr_def
  have hErrBound : |∫ x : Vec3, errTerm x| ≤ C0 := hC0 t ht
  -- Integrability of the error term.
  have hErrInt : Integrable errTerm := by
    have hrepMap : ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2))
        (vec3Ball (0 : Vec3) 1) := mixedTerm_continuousOn_repMap
    have hmapsTo : Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
        (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := mixedTerm_mapsTo_repMap
    have hcontDz : Continuous (fun x : Vec3 => fderiv ℝ χ x (basisVec 2)) := by
      have hpair : Continuous (fun p : Vec3 × Vec3 => (fderiv ℝ χ p.1) p.2) :=
        hχ.continuous_fderiv_apply (by simp)
      exact hpair.comp (continuous_id.prodMk continuous_const)
    refine integrable_of_cutoff hχs (hρU.trans hρ1)
      (((continuousOn_vel_slice hu 1 htmem).comp' hrepMap hmapsTo).mul
        (((continuousOn_const.mul hχ.continuous.continuousOn).mul hcontDz.continuousOn).mul
          (((continuousOn_dvel_slice hu 2 0 htmem).comp' hrepMap hmapsTo).mul
            ((continuousOn_curl_slice hu 2 htmem).comp' hrepMap hmapsTo))))
      (fun x hx => ?_)
    rw [herr_def]; simp [image_eq_zero_of_notMem_tsupport hx]
  have hInt2 : Integrable (fun x : Vec3 => f2 x * g2 x) := hMemF2.integrable_mul hMemG2
  have hInt3 : Integrable (fun x : Vec3 => f3 x * g3 x) := hMemF3.integrable_mul hMemG3
  -- The pointwise split of the vertical derivative of the cutoff-carrying factor.
  have hsplit_pt : ∀ x : Vec3,
      u (meridional (polarR x) (x 2), t) 1 * mixedTermFactorDz u χ x t
        = errTerm x + f2 x * g2 x + f3 x * g3 x := by
    intro x
    rw [herr_def, hf2_def, hg2_def, hf3_def, hg3_def]
    unfold mixedTermFactorDz
    ring
  have hsplitInt : (∫ x : Vec3, u (meridional (polarR x) (x 2), t) 1
        * mixedTermFactorDz u χ x t)
      = (∫ x : Vec3, errTerm x) + (∫ x : Vec3, f2 x * g2 x) + ∫ x : Vec3, f3 x * g3 x := by
    have hcongr : (∫ x : Vec3, u (meridional (polarR x) (x 2), t) 1
          * mixedTermFactorDz u χ x t)
        = ∫ x : Vec3, errTerm x + f2 x * g2 x + f3 x * g3 x :=
      integral_congr_ae (Filter.Eventually.of_forall hsplit_pt)
    have hInt12 : Integrable (fun x : Vec3 => errTerm x + f2 x * g2 x) := hErrInt.add hInt2
    rw [hcongr, integral_add hInt12 hInt3, integral_add hErrInt hInt2]
  -- The Cauchy–Schwarz bounds for the two remaining pieces.
  have hCS2 : |∫ x : Vec3, f2 x * g2 x| ≤ Real.sqrt (∫ x : Vec3, f2 x ^ 2)
      * Real.sqrt (∫ x : Vec3, g2 x ^ 2) :=
    abs_integral_mul_le_sqrt_mul_sqrt hMemF2 hMemG2
  have hCS3 : |∫ x : Vec3, f3 x * g3 x| ≤ Real.sqrt (∫ x : Vec3, f3 x ^ 2)
      * Real.sqrt (∫ x : Vec3, g3 x ^ 2) :=
    abs_integral_mul_le_sqrt_mul_sqrt hMemF3 hMemG3
  have hf2sq : (∫ x : Vec3, f2 x ^ 2)
      ≤ W t ^ 2 * C2 * (cutoffEnstrophyDissipation χ u t + 1) := hC2 t ht
  have hg2sq : (∫ x : Vec3, g2 x ^ 2) ≤ cutoffEnstrophy χ u t :=
    integral_sq_cutoff_mul_curlComp_two_rep_le haxi hu hχ hχs (hρU.trans hρ1) htmem
  have hf3sq : (∫ x : Vec3, f3 x ^ 2)
      ≤ W t ^ 2 * C1 * (cutoffEnstrophy χ u t + 1) := hC1 t ht
  have hg3sq : (∫ x : Vec3, g3 x ^ 2) ≤ cutoffEnstrophyDissipation χ u t :=
    integral_sq_cutoff_mul_dzcurlComp_two_rep_le haxi hu hχ hχs (hρU.trans hρ1) htmem
  -- Package the square-root bounds.
  have hYnn : (0 : ℝ) ≤ cutoffEnstrophy χ u t :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg (χ x))
      (Finset.sum_nonneg fun i _ => sq_nonneg (vorticityField u (x, t) i)))
  have hMnn : (0 : ℝ) ≤ cutoffEnstrophyDissipation χ u t :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg (χ x))
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        sq_nonneg (spatialPartial (fun w => vorticityField u w i) j (x, t))))
  have hsqrtF2 : Real.sqrt (∫ x : Vec3, f2 x ^ 2)
      ≤ W t * Cs2 * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1) := by
    have hle : Real.sqrt (∫ x : Vec3, f2 x ^ 2)
        ≤ Real.sqrt (W t ^ 2 * C2 * (cutoffEnstrophyDissipation χ u t + 1)) :=
      Real.sqrt_le_sqrt hf2sq
    have heq : Real.sqrt (W t ^ 2 * C2 * (cutoffEnstrophyDissipation χ u t + 1))
        = W t * Cs2 * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1) := by
      rw [hCs2_def, show W t ^ 2 * C2 * (cutoffEnstrophyDissipation χ u t + 1)
          = W t ^ 2 * (C2 * (cutoffEnstrophyDissipation χ u t + 1)) by ring,
        Real.sqrt_mul (sq_nonneg (W t)), Real.sqrt_sq hWnn,
        Real.sqrt_mul hC2nn]
      ring
    rwa [heq] at hle
  have hsqrtG2 : Real.sqrt (∫ x : Vec3, g2 x ^ 2) ≤ Real.sqrt (cutoffEnstrophy χ u t) :=
    Real.sqrt_le_sqrt hg2sq
  have hsqrtF3 : Real.sqrt (∫ x : Vec3, f3 x ^ 2)
      ≤ W t * Cs1 * Real.sqrt (cutoffEnstrophy χ u t + 1) := by
    have hle : Real.sqrt (∫ x : Vec3, f3 x ^ 2)
        ≤ Real.sqrt (W t ^ 2 * C1 * (cutoffEnstrophy χ u t + 1)) :=
      Real.sqrt_le_sqrt hf3sq
    have heq : Real.sqrt (W t ^ 2 * C1 * (cutoffEnstrophy χ u t + 1))
        = W t * Cs1 * Real.sqrt (cutoffEnstrophy χ u t + 1) := by
      rw [hCs1_def, show W t ^ 2 * C1 * (cutoffEnstrophy χ u t + 1)
          = W t ^ 2 * (C1 * (cutoffEnstrophy χ u t + 1)) by ring,
        Real.sqrt_mul (sq_nonneg (W t)), Real.sqrt_sq hWnn,
        Real.sqrt_mul hC1nn]
      ring
    rwa [heq] at hle
  have hsqrtG3 : Real.sqrt (∫ x : Vec3, g3 x ^ 2)
      ≤ Real.sqrt (cutoffEnstrophyDissipation χ u t) := Real.sqrt_le_sqrt hg3sq
  -- Combine into the Cauchy–Schwarz shape `mixed_term_bound_of_cauchy_schwarz` expects.
  have hnn1 : (0:ℝ) ≤ W t * Cs2 * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1) :=
    mul_nonneg (mul_nonneg hWnn hCs2nn) (Real.sqrt_nonneg _)
  have hnn2 : (0:ℝ) ≤ Real.sqrt (cutoffEnstrophy χ u t) := Real.sqrt_nonneg _
  have hnn3 : (0:ℝ) ≤ W t * Cs1 * Real.sqrt (cutoffEnstrophy χ u t + 1) :=
    mul_nonneg (mul_nonneg hWnn hCs1nn) (Real.sqrt_nonneg _)
  have hnn4 : (0:ℝ) ≤ Real.sqrt (cutoffEnstrophyDissipation χ u t) := Real.sqrt_nonneg _
  have hbound2 : |∫ x : Vec3, f2 x * g2 x|
      ≤ (W t * Cs2 * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1))
        * Real.sqrt (cutoffEnstrophy χ u t) :=
    le_trans hCS2 (mul_le_mul hsqrtF2 hsqrtG2 (Real.sqrt_nonneg _) hnn1)
  have hbound3 : |∫ x : Vec3, f3 x * g3 x|
      ≤ (W t * Cs1 * Real.sqrt (cutoffEnstrophy χ u t + 1))
        * Real.sqrt (cutoffEnstrophyDissipation χ u t) :=
    le_trans hCS3 (mul_le_mul hsqrtF3 hsqrtG3 (Real.sqrt_nonneg _) hnn3)
  have hbound2' : |∫ x : Vec3, f2 x * g2 x|
      ≤ C₁ * W t * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1)
        * Real.sqrt (cutoffEnstrophy χ u t) := by
    refine le_trans hbound2 ?_
    have : W t * Cs2 * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1)
        ≤ C₁ * W t * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1) := by
      have hCle : Cs2 ≤ C₁ := le_max_right _ _
      have h1 : W t * Cs2 ≤ W t * C₁ := mul_le_mul_of_nonneg_left hCle hWnn
      have h2 : W t * Cs2 * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1)
          ≤ W t * C₁ * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1) :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      calc W t * Cs2 * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1)
          ≤ W t * C₁ * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1) := h2
        _ = C₁ * W t * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1) := by ring
    exact mul_le_mul_of_nonneg_right this hnn2
  have hbound3' : |∫ x : Vec3, f3 x * g3 x|
      ≤ C₁ * W t * Real.sqrt (cutoffEnstrophy χ u t + 1)
        * Real.sqrt (cutoffEnstrophyDissipation χ u t) := by
    refine le_trans hbound3 ?_
    have : W t * Cs1 * Real.sqrt (cutoffEnstrophy χ u t + 1)
        ≤ C₁ * W t * Real.sqrt (cutoffEnstrophy χ u t + 1) := by
      have hCle : Cs1 ≤ C₁ := le_max_left _ _
      have h1 : W t * Cs1 ≤ W t * C₁ := mul_le_mul_of_nonneg_left hCle hWnn
      have h2 : W t * Cs1 * Real.sqrt (cutoffEnstrophy χ u t + 1)
          ≤ W t * C₁ * Real.sqrt (cutoffEnstrophy χ u t + 1) :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      calc W t * Cs1 * Real.sqrt (cutoffEnstrophy χ u t + 1)
          ≤ W t * C₁ * Real.sqrt (cutoffEnstrophy χ u t + 1) := h2
        _ = C₁ * W t * Real.sqrt (cutoffEnstrophy χ u t + 1) := by ring
    exact mul_le_mul_of_nonneg_right this hnn4
  have hIfinal : |∫ x : Vec3, u (meridional (polarR x) (x 2), t) 1
        * mixedTermFactorDz u χ x t|
      ≤ C0 + C₁ * W t * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1)
          * Real.sqrt (cutoffEnstrophy χ u t)
        + C₁ * W t * Real.sqrt (cutoffEnstrophy χ u t + 1)
          * Real.sqrt (cutoffEnstrophyDissipation χ u t) := by
    rw [hsplitInt]
    calc |(∫ x : Vec3, errTerm x) + (∫ x : Vec3, f2 x * g2 x) + ∫ x : Vec3, f3 x * g3 x|
        ≤ |(∫ x : Vec3, errTerm x) + (∫ x : Vec3, f2 x * g2 x)| + |∫ x : Vec3, f3 x * g3 x| :=
          abs_add_le _ _
      _ ≤ (|∫ x : Vec3, errTerm x| + |∫ x : Vec3, f2 x * g2 x|) + |∫ x : Vec3, f3 x * g3 x| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ C0 + C₁ * W t * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1)
            * Real.sqrt (cutoffEnstrophy χ u t)
          + C₁ * W t * Real.sqrt (cutoffEnstrophy χ u t + 1)
            * Real.sqrt (cutoffEnstrophyDissipation χ u t) :=
          add_le_add (add_le_add hErrBound hbound2') hbound3'
  have hIabs : |∫ x : Vec3, χ x ^ 2 * stretchMixedTerm u x t|
      ≤ C0 + C₁ * W t * Real.sqrt (cutoffEnstrophyDissipation χ u t + 1)
          * Real.sqrt (cutoffEnstrophy χ u t)
        + C₁ * W t * Real.sqrt (cutoffEnstrophy χ u t + 1)
          * Real.sqrt (cutoffEnstrophyDissipation χ u t) := by
    rw [hIBP]; exact hIfinal
  have hfinal := mixed_term_bound_of_cauchy_schwarz hC0nn hMnn hYnn hIabs
  exact hfinal

end CIV
