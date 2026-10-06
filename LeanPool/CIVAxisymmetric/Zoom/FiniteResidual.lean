/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisCutoff

/-!
# The finite-`n` residual of the lifted equation tends to zero

`tendsto_finResidual` is the input of the finite branch to the limit equation
`eq:aniso:zoom:finite:limit` at `(m, d) = (5, 4)` (the lift to `ℝ⁴` together with the
vanishing terms of the passage to the limit, deviation D17): against a test function `φ` on
`ℝ⁴ × ℝ × (-∞, -1)`, the pairing of the lifted potential vorticity `Ω̃_n` with the adjoint limit
operator `-∂_τ φ - B_n · ∇φ - (div B_n) φ - Δ_X φ` tends to zero.

The test function is split with the axis cutoff `finAxisCutoff ε` as `φ = φ χ_ε + φ (1 - χ_ε)`.

* Near the axis, `Ω̃_n`, `B_n` and `div B_n` are bounded uniformly in `n` (`finDrift_bounds`),
  the derivatives of `φ χ_ε` of order at most two are `O(ε⁻²)`, and the support has volume
  `O(ε⁴)`: this part is `O(ε²)` uniformly in `n` (`abs_integral_residual_nearAxis_le`).
* Off the axis, the lifted equation holds classically and the integration by parts of
  `integral_finResidual_eq_of_subset_finLiftDomain` leaves `δ_n² ∫ Ω̃_n ∂_ZZ ψ - ∫ F̃_n ∂_Z ψ
  + ∫ G̃_n ψ`. Here `|Ω̃_n| ≤ 2C`, the swirl flux obeys `F_n = S_n² / R² ≤ C_Γ² δ_n² / ε⁴` by
  `eq:aniso:zoom:circulation`, and `|G_n| ≤ C λ_n⁵ δ_n`; all three tend to zero with `λ_n`
  (`tendsto_integral_residual_offAxis`).
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- A function vanishing off a measurable set of finite measure and bounded on it has integral
bounded by the bound times the measure. -/
theorem abs_integral_le_of_forall_notMem {S : Set (Vec 5 × ℝ)} (hS : volume S < ⊤)
    {g : Vec 5 × ℝ → ℝ} {Q : ℝ} (h0 : ∀ z, z ∉ S → g z = 0) (hQ : ∀ z ∈ S, |g z| ≤ Q) :
    |∫ z, g z| ≤ Q * (volume S).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const hS fun z hz => by
    rw [Real.norm_eq_abs]
    exact hQ z hz

/-- The box `{|X_j| ≤ 2ε, |Z| ≤ r, |τ| ≤ r}` around the axis of the lifted variables. -/
theorem volume_axisBox (ε r : ℝ) (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    (volume ((Set.univ.pi fun j : Fin 5 => Icc (-(if j = 4 then r else 2 * ε))
        (if j = 4 then r else 2 * ε)) ×ˢ Icc (-r) r)).toReal
      = (4 * ε) ^ 4 * (2 * r) * (2 * r) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal (by linarith only [hr]),
    Fin.prod_univ_five]
  simp only [Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by norm_num; positivity), ENNReal.toReal_ofReal (by norm_num;
    positivity),
    ENNReal.toReal_ofReal (by norm_num; positivity), ENNReal.toReal_ofReal (by norm_num;
      positivity),
    ENNReal.toReal_ofReal (by norm_num; positivity)]
  norm_num
  ring

/-- The support of the cutoff lies where the rescaled radial part has norm at most two. -/
theorem tsupport_finAxisCutoff_subset (ε : ℝ) :
    tsupport (finAxisCutoff ε) ⊆ {z | ‖(ε⁻¹ • finAxisProj) z‖ ≤ 2} := by
  refine closure_minimal (fun z hz => ?_)
    (isClosed_le (continuous_norm.comp (ε⁻¹ • finAxisProj).continuous) continuous_const)
  by_contra hlt
  exact hz (finAxisCutoff_eq_zero (le_of_lt (not_le.mp hlt)))

/-- The part of the residual near the axis is `O(ε²)`, uniformly in the coefficients as long as
they are bounded by `M` on the support. -/
theorem abs_integral_residual_nearAxis_le {K : Set (Vec 5 × ℝ)} {r : ℝ} (hr : 0 ≤ r)
    (hKr : ∀ z ∈ K, ‖z‖ ≤ r) {q d : Vec 5 × ℝ → ℝ} {b : Vec 5 × ℝ → Vec 5} {M : ℝ}
    (hM : 0 ≤ M) (hbd : ∀ z ∈ K, |q z| ≤ M ∧ ‖b z‖ ≤ M ∧ |d z| ≤ M)
    {φ : Vec 5 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφK : tsupport φ ⊆ K) {A : ℝ}
    (hA : ∀ j : ℕ, j ≤ 2 → ∀ z, ‖iteratedFDeriv ℝ j φ z‖ ≤ A) {Cb : ℝ}
    (hCb : ∀ j : ℕ, j ≤ 2 → ∀ y : Vec 5, ‖iteratedFDeriv ℝ j (finAxisBump : Vec 5 → ℝ) y‖ ≤ Cb)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ z, q z * (-(timeDeriv 5 (fun y => φ y * finAxisCutoff ε y) z)
        - gradPair 5 (fun y => φ y * finAxisCutoff ε y) z (b z)
        - d z * (φ z * finAxisCutoff ε z)
        - partialLaplacian 5 4 (fun y => φ y * finAxisCutoff ε y) z)|
      ≤ M * (2 * M + 5) * (4 * (A * (Cb * ε⁻¹ ^ 2))) * ((4 * ε) ^ 4 * (2 * r) * (2 * r)) := by
  set ψ := fun y => φ y * finAxisCutoff ε y with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.mul (contDiff_finAxisCutoff ε)
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by norm_num) 0)
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0 (by norm_num) 0)
  have hε1' : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  -- derivative bounds for `ψ`
  have hχ : ∀ j : ℕ, j ≤ 2 → ∀ z, ‖iteratedFDeriv ℝ j (finAxisCutoff ε) z‖ ≤ Cb * ε⁻¹ ^ 2 :=
    fun j hj z => (norm_iteratedFDeriv_finAxisCutoff_le hCb hε hj z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hε1' hj) hCb0)
  have hψb : ∀ j : ℕ, j ≤ 2 → ∀ z, ‖iteratedFDeriv ℝ j ψ z‖ ≤ 4 * (A * (Cb * ε⁻¹ ^ 2)) :=
    fun j hj z => norm_iteratedFDeriv_mul_le_of_forall_le hφ (contDiff_finAxisCutoff ε)
      (fun i hi => hA i hi z) (fun i hi => hχ i hi z) hj
  set X := 4 * (A * (Cb * ε⁻¹ ^ 2)) with hX
  have hX0 : 0 ≤ X := by positivity
  -- the box containing the support
  set a : Fin 5 → ℝ := fun j => if j = 4 then r else 2 * ε with ha
  set S : Set (Vec 5 × ℝ) := (Set.univ.pi fun j : Fin 5 => Icc (-(a j)) (a j)) ×ˢ Icc (-r) r
    with hS
  have hSfin : volume S < ⊤ :=
    ((isCompact_univ_pi fun j => isCompact_Icc).prod isCompact_Icc).measure_lt_top
  have hsupp : tsupport ψ ⊆ K ∩ S := by
    intro z hz
    have hzφ : z ∈ tsupport φ := tsupport_mul_subset_left hz
    have hzχ : z ∈ tsupport (finAxisCutoff ε) := tsupport_mul_subset_right hz
    have hzK := hφK hzφ
    have hzr := hKr z hzK
    have hχz := tsupport_finAxisCutoff_subset ε hzχ
    refine ⟨hzK, ?_, ?_⟩
    · intro j _
      by_cases hj : j = 4
      · subst hj
        have : |z.1 4| ≤ r :=
          ((norm_le_pi_norm z.1 4).trans (norm_fst_le z)).trans hzr
        simp only [ha, ↓reduceIte]
        exact abs_le.mp this
      · have := abs_apply_le_of_norm_le_two hε hχz hj
        simp only [ha, hj, ↓reduceIte]
        exact abs_le.mp this
    · exact abs_le.mp ((norm_snd_le z).trans hzr)
  have hQ0 : 0 ≤ M * (2 * M + 5) * X := by positivity
  have hmain := abs_integral_le_of_forall_notMem hSfin
    (g := fun z => q z * (-(timeDeriv 5 ψ z) - gradPair 5 ψ z (b z) - d z * ψ z
      - partialLaplacian 5 4 ψ z)) (Q := M * (2 * M + 5) * X)
    (fun z hz => by
      rw [residualIntegrand_eq_zero_of_notMem hψ2 (fun h => hz (hsupp h).2), mul_zero])
    (fun z _ => by
      by_cases hzψ : z ∈ tsupport ψ
      · obtain ⟨hq, hb, hd⟩ := hbd z (hsupp hzψ).1
        have hr' := abs_residualIntegrand_le hψ2 z (b z) (d z)
        have hbr : |-(timeDeriv 5 ψ z) - gradPair 5 ψ z (b z) - d z * ψ z
            - partialLaplacian 5 4 ψ z| ≤ (2 * M + 5) * X := by
          refine hr'.trans ?_
          calc (1 + ‖b z‖) * ‖iteratedFDeriv ℝ 1 ψ z‖ + |d z| * ‖iteratedFDeriv ℝ 0 ψ z‖
                + 4 * ‖iteratedFDeriv ℝ 2 ψ z‖
              ≤ (1 + M) * X + M * X + 4 * X := by
                gcongr
                · exact hψb 1 (by norm_num) z
                · exact hψb 0 (by norm_num) z
                · exact hψb 2 (by norm_num) z
            _ = (2 * M + 5) * X := by ring
        rw [abs_mul]
        calc |q z| * |-(timeDeriv 5 ψ z) - gradPair 5 ψ z (b z) - d z * ψ z
              - partialLaplacian 5 4 ψ z| ≤ M * ((2 * M + 5) * X) :=
              mul_le_mul hq hbr (abs_nonneg _) hM
          _ = M * (2 * M + 5) * X := by ring
      · rw [residualIntegrand_eq_zero_of_notMem hψ2 hzψ, mul_zero, abs_zero]
        exact hQ0)
  rw [volume_axisBox ε r hε.le hr] at hmain
  exact hmain

/-- A first derivative in a coordinate direction is bounded by the first derivative. -/
theorem abs_fderiv_apply_basisVec_le {ψ : Vec 5 × ℝ → ℝ} (z : Vec 5 × ℝ) (i : Fin 5) :
    |fderiv ℝ ψ z (basisVec i, 0)| ≤ ‖iteratedFDeriv ℝ 1 ψ z‖ := by
  rw [norm_iteratedFDeriv_one, ← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  have hb : ‖((basisVec i, 0) : Vec 5 × ℝ)‖ ≤ 1 := by
    rw [Prod.norm_def]
    refine max_le ?_ (by simp)
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    show ‖basisVec i j‖ ≤ 1
    rw [basisVec_apply]
    split_ifs <;> simp
  calc ‖fderiv ℝ ψ z‖ * ‖((basisVec i, 0) : Vec 5 × ℝ)‖ ≤ ‖fderiv ℝ ψ z‖ * 1 :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖fderiv ℝ ψ z‖ := mul_one _

/-- A second derivative in a coordinate direction is bounded by the second derivative. -/
theorem abs_fderiv_fderiv_apply_basisVec_le {ψ : Vec 5 × ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (z : Vec 5 × ℝ) (i : Fin 5) :
    |fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec i, 0)) z (basisVec i, 0)|
      ≤ ‖iteratedFDeriv ℝ 2 ψ z‖ := by
  have hD1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  have hh : HasFDerivAt (fun w => fderiv ℝ ψ w (basisVec i, 0))
      ((fderiv ℝ (fderiv ℝ ψ) z).flip (basisVec i, 0)) z := by
    have := (hD1.differentiable (by norm_num) z).hasFDerivAt.clm_apply
      (hasFDerivAt_const ((basisVec i, 0) : Vec 5 × ℝ) z)
    simpa using this
  have hbv : ‖((basisVec i, 0) : Vec 5 × ℝ)‖ ≤ 1 := by
    rw [Prod.norm_def]
    refine max_le ?_ (by simp)
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    show ‖basisVec i j‖ ≤ 1
    rw [basisVec_apply]
    split_ifs <;> simp
  rw [hh.fderiv, ContinuousLinearMap.flip_apply, ← Real.norm_eq_abs, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_one]
  calc ‖fderiv ℝ (fderiv ℝ ψ) z (basisVec i, 0) (basisVec i, 0)‖
      ≤ ‖fderiv ℝ (fderiv ℝ ψ) z (basisVec i, 0)‖ * ‖((basisVec i, 0) : Vec 5 × ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) z‖ * ‖((basisVec i, 0) : Vec 5 × ℝ)‖
          * ‖((basisVec i, 0) : Vec 5 × ℝ)‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) z‖ * 1 * 1 := by gcongr
    _ = ‖fderiv ℝ (fderiv ℝ ψ) z‖ := by ring

/-- The support of `1 - χ_ε` lies where the rescaled radial part has norm at least one. -/
theorem tsupport_one_sub_finAxisCutoff_subset (ε : ℝ) :
    tsupport (fun y => 1 - finAxisCutoff ε y) ⊆ {z | 1 ≤ ‖(ε⁻¹ • finAxisProj) z‖} := by
  refine closure_minimal (fun z hz => ?_)
    (isClosed_le continuous_const (continuous_norm.comp (ε⁻¹ • finAxisProj).continuous))
  by_contra hlt
  exact hz (by show 1 - finAxisCutoff ε z = 0; rw [finAxisCutoff_eq_one (le_of_lt (not_le.mp
    hlt)), sub_self])

/-- The swirl flux off the axis: `S_n² / R² ≤ C_Γ² δ² / ε⁴` where `R ≥ ε` and the circulation is
bounded by `C_Γ` (`eq:aniso:zoom:circulation`). -/
theorem abs_zoomSwirlFlux_le {lam h zc CΓ ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε)
    {u : ParabolicPoint → Vec3} {p : (ℝ × ℝ) × ℝ} (hR : ε ≤ p.1.1)
    (hΓ : |circulation u (zoomPoint lam h zc p)| ≤ CΓ) :
    |zoomS lam h zc u p ^ 2 / p.1.1 ^ 2| ≤ CΓ ^ 2 * (lam ^ (2 * h)) ^ 2 / ε ^ 4 := by
  have h1 := abs_mul_zoomS_le_of_circulation hlam hΓ
  have hRpos : 0 < p.1.1 := hε.trans_le hR
  have heq : zoomS lam h zc u p ^ 2 / p.1.1 ^ 2 = (p.1.1 * zoomS lam h zc u p) ^ 2 / p.1.1 ^ 4 := by
    field_simp
  rw [heq, abs_div, abs_pow, abs_pow, abs_of_pos hRpos]
  have hnum : |p.1.1 * zoomS lam h zc u p| ^ 2 ≤ (CΓ * lam ^ (2 * h)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hden : ε ^ 4 ≤ p.1.1 ^ 4 := pow_le_pow_left₀ hε.le hR 4
  calc |p.1.1 * zoomS lam h zc u p| ^ 2 / p.1.1 ^ 4 ≤ (CΓ * lam ^ (2 * h)) ^ 2 / p.1.1 ^ 4 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (CΓ * lam ^ (2 * h)) ^ 2 / ε ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = CΓ ^ 2 * (lam ^ (2 * h)) ^ 2 / ε ^ 4 := by ring

/-- The part of the residual off the axis tends to zero, for each fixed cutoff scale `ε`. -/
theorem tendsto_integral_residual_offAxis {C h CΓ ρ Rstar tstar : ℝ} {u : ParabolicPoint → Vec3}
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {lam zc : ℕ → ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    (htstar : tstar < 0) (hzc : ∀ n, |zc n| ≤ ρ) (hC : 0 ≤ C) (hb : AnisotropicBounds C h u)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f) (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    {φ : Vec 5 × ℝ → ℝ} (hφ : φ ∈ testFunctions 5 (Iio (-1))) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ∫ z, zoomOmegaLift (lam n) h (zc n) u z *
      (-(timeDeriv 5 (fun y => φ y * (1 - finAxisCutoff ε y)) z)
        - gradPair 5 (fun y => φ y * (1 - finAxisCutoff ε y)) z (zoomDrift (lam n) h (zc n) u z)
        - finDriftDiv (lam n) h (zc n) u z * (φ z * (1 - finAxisCutoff ε z))
        - partialLaplacian 5 4 (fun y => φ y * (1 - finAxisCutoff ε y)) z)) atTop (𝓝 0) := by
  obtain ⟨hφs, hφc, hφK⟩ := hφ
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder := hsol.2.2.1
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρR hR1
  set ψ := fun y => φ y * (1 - finAxisCutoff ε y) with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφs.mul (contDiff_const.sub (contDiff_finAxisCutoff ε))
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hψc : HasCompactSupport ψ := hφc.mul_right
  obtain ⟨A, hA0, hA⟩ := exists_norm_iteratedFDeriv_le_of_hasCompactSupport hψ hψc
  obtain ⟨Cf, hCf0, hCf⟩ := abs_potentialVorticity_force_le hf hfaxi hforce
  -- the support off the axis
  set K2 : Set (Vec 5 × ℝ) := tsupport φ ∩ {z | 1 ≤ ‖(ε⁻¹ • finAxisProj) z‖} with hK2def
  have hK2 : IsCompact K2 := hφc.inter_right
    (isClosed_le continuous_const (continuous_norm.comp (ε⁻¹ • finAxisProj).continuous))
  have hψK2 : tsupport ψ ⊆ K2 := fun z hz =>
    ⟨tsupport_mul_subset_left hz, tsupport_one_sub_finAxisCutoff_subset ε
      (tsupport_mul_subset_right hz)⟩
  have hRK2 : ∀ z ∈ K2, ε ≤ zoomLiftRadius z.1 := fun z hz =>
    le_zoomLiftRadius_of_one_le_norm hε hz.2
  have hτK2 : ∀ z ∈ K2, z.2 < -1 := fun z hz => (hφK hz.1).2
  have hL : IsCompact (zoomLiftPoint '' K2) := hK2.image continuous_zoomLiftPoint
  have hLt : ∀ p ∈ zoomLiftPoint '' K2, p.2 < 0 := by
    rintro _ ⟨z, hz, rfl⟩
    show z.2 < 0
    linarith only [hτK2 z hz]
  have ev1 := eventually_forall_zoomPoint_mem_unitCylinder_moving hh hρ0 hρ1 hzc hlam_lim _ hL hLt
  have hcz : ∀ n, ((fun _ : ℕ => (0 : ℝ)) n) ^ 2 + zc n ^ 2 ≤ ρ ^ 2 := fun n => by
    have := sq_le_sq' (abs_le.mp (hzc n)).1 (abs_le.mp (hzc n)).2
    simpa using this
  have ev2 := eventually_mem_zoomPointRec_moving hh hρ0 hρR htstar hcz hlam_lim _ hL hLt
  have ev3 := eventually_lam_lt_one_and_zoomDelta_le_one hh.1.le hlam_lim
  -- the bound
  set V := (volume K2).toReal with hV
  set c1 : ℝ := (2 * C * A + CΓ ^ 2 / ε ^ 4 * A) * V with hc1
  set c2 : ℝ := Cf * A * V with hc2
  set Fb : ℝ → ℝ := fun l => (l ^ (2 * h)) ^ 2 * c1 + (l ^ 5 * l ^ (2 * h)) * c2 with hFb
  have hFb0 : Tendsto (fun n => Fb (lam n)) atTop (𝓝 0) := by
    have hcont : ContinuousAt Fb 0 := by
      have hr : ContinuousAt (fun l : ℝ => l ^ (2 * h)) 0 :=
        Real.continuousAt_rpow_const 0 (2 * h) (Or.inr (by linarith only [hh.1]))
      exact ((hr.pow 2).mul continuousAt_const).add
        (((continuousAt_id.pow 5).mul hr).mul continuousAt_const)
    have hz : Fb 0 = 0 := by
      simp only [hFb]
      rw [Real.zero_rpow (by linarith only [hh.1])]
      ring
    rw [← hz]
    exact hcont.tendsto.comp (hlam_lim.mono_right nhdsWithin_le_nhds)
  refine squeeze_zero_norm' ?_ hFb0
  filter_upwards [ev1, ev2, ev3] with n h1 h2 h3
  obtain ⟨hlamn, _, hδ⟩ := h3
  have hsub : K2 ⊆ finLiftDomain (lam n) h (zc n) := fun z hz =>
    ⟨hε.trans_le (hRK2 z hz), h1 _ (mem_image_of_mem _ hz)⟩
  rw [integral_finResidual_eq_of_subset_finLiftDomain hlamn hsol haxi hK2 hsub hψ hψc hψK2,
    Real.norm_eq_abs]
  have hFbn : Fb (lam n) = ((lam n ^ (2 * h)) ^ 2 * (2 * C) * A
      + CΓ ^ 2 * (lam n ^ (2 * h)) ^ 2 / ε ^ 4 * A + Cf * (lam n ^ 5 * lam n ^ (2 * h)) * A)
        * V := by
    simp only [hFb, hc1, hc2]
    ring
  rw [hFbn]
  refine abs_integral_le_of_forall_notMem hK2.measure_lt_top (fun z hz => ?_) (fun z hz => ?_)
  · have hz' : z ∉ tsupport ψ := fun h => hz (hψK2 h)
    have hz'' : z ∉ tsupport (fun w => fderiv ℝ ψ w (basisVec 4, 0)) := fun h =>
      hz' (tsupport_fderiv_apply_subset ℝ _ h)
    rw [fderiv_apply_eq_zero_of_notMem_tsupport hz'', fderiv_apply_eq_zero_of_notMem_tsupport hz',
      image_eq_zero_of_notMem_tsupport hz']
    ring
  · have hp : zoomPoint (lam n) h (zc n) (zoomLiftPoint z) ∈ unitCylinder :=
      h1 _ (mem_image_of_mem _ hz)
    have hq := abs_zoomOmegaLift_le_two_mul_const hlamn hb hu2 haxi hp hC hδ hh.1 hh.2
      (le_of_lt (hτK2 z hz))
    have hpr := h2 _ (mem_image_of_mem _ hz)
    have hrec : zoomPointRec (lam n) h 0 (zc n) (zoomLiftPoint z)
        = zoomPoint (lam n) h (zc n) (zoomLiftPoint z) := by
      unfold zoomPointRec zoomPoint
      rw [zero_add]
    rw [hrec] at hpr
    have hcirc : |circulation u (zoomPoint (lam n) h (zc n) (zoomLiftPoint z))| ≤ CΓ :=
      hΓ _ hpr.1 _ hpr.2
    have hF := abs_zoomSwirlFlux_le hlamn hε (hRK2 z hz) hcirc
    have hG : |zoomForce (lam n) h (zc n) f (zoomLiftPoint z)|
        ≤ Cf * (lam n ^ 5 * lam n ^ (2 * h)) := by
      have hpv := hCf _ _ _ hp
      have hpos : (0 : ℝ) ≤ lam n ^ 5 * lam n ^ (2 * h) := by positivity
      rw [zoomForce, abs_mul, abs_of_nonneg hpos, mul_comm]
      exact mul_le_mul_of_nonneg_right hpv hpos
    have hd2 := (abs_fderiv_fderiv_apply_basisVec_le hψ2 z 4).trans (hA 2 (by norm_num) z)
    have hd1 := (abs_fderiv_apply_basisVec_le (ψ := ψ) z 4).trans (hA 1 (by norm_num) z)
    have hd0 : |ψ z| ≤ A := by
      have := hA 0 (by norm_num) z
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have hδ0 : 0 ≤ (lam n ^ (2 * h)) ^ 2 := by positivity
    calc |(lam n ^ (2 * h)) ^ 2 * zoomOmegaLift (lam n) h (zc n) u z
            * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 4, 0)) z (basisVec 4, 0)
          - zoomS (lam n) h (zc n) u (zoomLiftPoint z) ^ 2 / (zoomLiftPoint z).1.1 ^ 2
            * fderiv ℝ ψ z (basisVec 4, 0)
          + zoomForce (lam n) h (zc n) f (zoomLiftPoint z) * ψ z|
        ≤ (lam n ^ (2 * h)) ^ 2 * |zoomOmegaLift (lam n) h (zc n) u z|
            * |fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 4, 0)) z (basisVec 4, 0)|
          + |zoomS (lam n) h (zc n) u (zoomLiftPoint z) ^ 2 / (zoomLiftPoint z).1.1 ^ 2|
            * |fderiv ℝ ψ z (basisVec 4, 0)|
          + |zoomForce (lam n) h (zc n) f (zoomLiftPoint z)| * |ψ z| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [abs_mul, abs_mul, abs_of_nonneg hδ0]
          · rw [abs_mul]
          · rw [abs_mul]
      _ ≤ (lam n ^ (2 * h)) ^ 2 * (2 * C) * A + CΓ ^ 2 * (lam n ^ (2 * h)) ^ 2 / ε ^ 4 * A
          + Cf * (lam n ^ 5 * lam n ^ (2 * h)) * A := by
          gcongr

/-- The lift to `ℝ⁴` and the vanishing terms of the passage to the limit: the finite-`n`
residual of `eq:aniso:zoom:lifted` against a test function on `ℝ⁴ × ℝ × (-∞, -1)` tends to
zero. -/
theorem tendsto_finResidual {C h CΓ ρ Rstar tstar : ℝ} {u : ParabolicPoint → Vec3}
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {lam zc : ℕ → ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    (htstar : tstar < 0) (hzc : ∀ n, |zc n| ≤ ρ) (hC : 0 ≤ C) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f) (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    ∀ φ ∈ testFunctions 5 (Iio (-1)), Tendsto (fun n => ∫ z,
      zoomOmegaLift (lam n) h (zc n) u z *
        (-(timeDeriv 5 φ z) - gradPair 5 φ z (zoomDrift (lam n) h (zc n) u z)
          - finDriftDiv (lam n) h (zc n) u z * φ z - partialLaplacian 5 4 φ z))
      atTop (nhds 0) := by
  intro φ hφ
  have hφ' := hφ
  obtain ⟨hφs, hφc, hφK⟩ := hφ
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρR hR1
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hφc
  obtain ⟨M0, hM⟩ := finDrift_bounds hh hρ0 hρ1 hC hb hu haxi hzc hlam_lim K hK hφK
  set M := max M0 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  obtain ⟨r0, hr0⟩ := hK.exists_bound_of_continuousOn (f := fun z : Vec 5 × ℝ => z)
    continuousOn_id
  set r := max r0 0 with hrdef
  have hr : 0 ≤ r := le_max_right _ _
  have hKr : ∀ z ∈ K, ‖z‖ ≤ r := fun z hz => (hr0 z hz).trans (le_max_left _ _)
  obtain ⟨A, hA0, hA⟩ := exists_norm_iteratedFDeriv_le_of_hasCompactSupport hφs hφc
  obtain ⟨Cb, hCb0, hCb⟩ := exists_norm_iteratedFDeriv_finAxisBump_le
  set Cn := M * (2 * M + 5) * 4 * A * Cb * 1024 * r ^ 2 with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  refine Metric.tendsto_nhds.mpr fun η hη => ?_
  set ε := min 1 (η / (2 * (Cn + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : Cn * ε ^ 2 < η / 2 := by
    have h1 : ε ≤ η / (2 * (Cn + 1)) := min_le_right _ _
    have h2 : ε ^ 2 ≤ ε := by nlinarith only [hε, hε1]
    have h3 : Cn * ε ≤ Cn * (η / (2 * (Cn + 1))) := mul_le_mul_of_nonneg_left h1 hCn0
    have h4 : Cn * (η / (2 * (Cn + 1))) < η / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hη, hCn0]
    calc Cn * ε ^ 2 ≤ Cn * ε := mul_le_mul_of_nonneg_left h2 hCn0
      _ < η / 2 := lt_of_le_of_lt h3 h4
  have hoff := tendsto_integral_residual_offAxis hh hρ0 hρR hR1 htstar hzc hC hb hsol haxi hfaxi
    hΓ hforce hlam_lim hφ' hε
  filter_upwards [hM, Metric.tendsto_nhds.mp hoff (η / 2) (half_pos hη)] with n hMn hoffn
  obtain ⟨hqm, hbm, hdm, hbd⟩ := hMn
  have hbd' : ∀ z ∈ K, |zoomOmegaLift (lam n) h (zc n) u z| ≤ M ∧
      ‖zoomDrift (lam n) h (zc n) u z‖ ≤ M ∧ |finDriftDiv (lam n) h (zc n) u z| ≤ M :=
    fun z hz => by
      obtain ⟨h1, h2, h3⟩ := hbd z hz
      exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_left _ _), h3.trans (le_max_left _ _)⟩
  -- the splitting `φ = φ χ_ε + φ (1 - χ_ε)`
  have hψ1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y * finAxisCutoff ε y) :=
    hφs.mul (contDiff_finAxisCutoff ε)
  have hψ2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y * (1 - finAxisCutoff ε y)) :=
    hφs.mul (contDiff_const.sub (contDiff_finAxisCutoff ε))
  have hfun : φ = fun y => φ y * finAxisCutoff ε y + φ y * (1 - finAxisCutoff ε y) := by
    funext y
    ring
  have hpt : ∀ z, zoomOmegaLift (lam n) h (zc n) u z *
      (-(timeDeriv 5 φ z) - gradPair 5 φ z (zoomDrift (lam n) h (zc n) u z)
        - finDriftDiv (lam n) h (zc n) u z * φ z - partialLaplacian 5 4 φ z)
      = zoomOmegaLift (lam n) h (zc n) u z *
          (-(timeDeriv 5 (fun y => φ y * finAxisCutoff ε y) z)
            - gradPair 5 (fun y => φ y * finAxisCutoff ε y) z (zoomDrift (lam n) h (zc n) u z)
            - finDriftDiv (lam n) h (zc n) u z * (φ z * finAxisCutoff ε z)
            - partialLaplacian 5 4 (fun y => φ y * finAxisCutoff ε y) z)
        + zoomOmegaLift (lam n) h (zc n) u z *
          (-(timeDeriv 5 (fun y => φ y * (1 - finAxisCutoff ε y)) z)
            - gradPair 5 (fun y => φ y * (1 - finAxisCutoff ε y)) z
              (zoomDrift (lam n) h (zc n) u z)
            - finDriftDiv (lam n) h (zc n) u z * (φ z * (1 - finAxisCutoff ε z))
            - partialLaplacian 5 4 (fun y => φ y * (1 - finAxisCutoff ε y)) z) := by
    intro z
    have hadd := residualIntegrand_add (hψ1.of_le (by simp)) (hψ2.of_le (by simp)) z
      (zoomDrift (lam n) h (zc n) u z) (finDriftDiv (lam n) h (zc n) u z)
    rw [← hfun] at hadd
    linear_combination zoomOmegaLift (lam n) h (zc n) u z * hadd
  have hint1 := integrable_mul_residualIntegrand hK hqm hbm hdm hbd' hψ1
    (hφc.mul_right) (tsupport_mul_subset_left)
  have hint2 := integrable_mul_residualIntegrand hK hqm hbm hdm hbd' hψ2
    (hφc.mul_right) (tsupport_mul_subset_left)
  have hnear := abs_integral_residual_nearAxis_le hr hKr hM0 hbd' hφs le_rfl hA hCb hε hε1
  have hnear' : M * (2 * M + 5) * (4 * (A * (Cb * ε⁻¹ ^ 2))) * ((4 * ε) ^ 4 * (2 * r) * (2 * r))
      = Cn * ε ^ 2 := by
    simp only [hCn]
    field_simp
    ring
  rw [hnear'] at hnear
  rw [Real.dist_eq, sub_zero] at hoffn ⊢
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint1 hint2]
  calc _ ≤ _ := abs_add_le _ _
    _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (hnear.trans hεη.le) hoffn
    _ = η := add_halves η

end CIV
