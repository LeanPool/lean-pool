/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinMollifiedMeasurable

/-!
# Bounds for mollified pairings

At almost every time the mollified components of a Leray–Hopf velocity are
bounded uniformly, and the tested fluxes over a compact set of mollification
points are dominated by an integrable function of time. These are the
domination hypotheses of the Fubini exchange in `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem serrin_enorm_mul_le_half (a b : ℝ) :
    ‖a * b‖ₑ ≤ ENNReal.ofReal (1 / 2 : ℝ) * (‖a‖ₑ ^ (2 : ℝ) + ‖b‖ₑ ^ (2 : ℝ)) := by
  have hreal : |a * b| ≤ (1 / 2 : ℝ) * (a ^ 2 + b ^ 2) := by
    rw [abs_mul]
    nlinarith only [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg a) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg b) (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have ha : |a| ^ (2 : ℝ) = a ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  have hb : |b| ^ (2 : ℝ) = b ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  rw [ha, hb]
  exact hreal

/-- The mollified components of a Leray–Hopf velocity are uniformly bounded at
almost every time. -/
theorem serrinMol_bound_ae {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p)
    {ρ : Vec3 → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    ∃ B : ℝ, ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), ∀ (k : Fin 3) (y : Vec3),
      |serrinMol u ρ k y τ| ≤ B := by
  have hL2 := hU.slice_bound
  set M := essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T)) with hMdef
  have hρ2 : (∫⁻ x : Vec3, ‖ρ x‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have hmem : MemLp ρ 2 volume := hρ.memLp_of_hasCompactSupport hρc
    have h := hmem.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hρ.aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofNat] at h
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h
  set R := ∫⁻ x : Vec3, ‖ρ x‖ₑ ^ (2 : ℝ)
  refine ⟨(ENNReal.ofReal (1 / 2 : ℝ) * (M + R)).toReal, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))]
    with τ hτ k y
  have htrans : (∫⁻ x : Vec3, ‖ρ (y - x)‖ₑ ^ (2 : ℝ)) = R := by
    exact lintegral_sub_left_eq_self (μ := (volume : Measure Vec3))
      (fun x : Vec3 => ‖ρ x‖ₑ ^ (2 : ℝ)) y
  have hpoint (x : Vec3) : ‖u (x, τ) k * ρ (y - x)‖ₑ ≤
      ENNReal.ofReal (1 / 2 : ℝ) *
        (‖u (x, τ)‖ₑ ^ (2 : ℝ) + ‖ρ (y - x)‖ₑ ^ (2 : ℝ)) := by
    refine (serrin_enorm_mul_le_half _ _).trans ?_
    gcongr
    exact norm_le_pi_norm (u (x, τ)) k |>.trans_eq rfl |> fun h =>
      enorm_le_iff_norm_le.mpr h
  have hlint : (∫⁻ x : Vec3, ‖u (x, τ) k * ρ (y - x)‖ₑ) ≤
      ENNReal.ofReal (1 / 2 : ℝ) * (M + R) := by
    calc
      (∫⁻ x : Vec3, ‖u (x, τ) k * ρ (y - x)‖ₑ) ≤
          ∫⁻ x : Vec3, ENNReal.ofReal (1 / 2 : ℝ) *
            (‖u (x, τ)‖ₑ ^ (2 : ℝ) + ‖ρ (y - x)‖ₑ ^ (2 : ℝ)) :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal (1 / 2 : ℝ) *
            ((∫⁻ x : Vec3, ‖u (x, τ)‖ₑ ^ (2 : ℝ)) +
              ∫⁻ x : Vec3, ‖ρ (y - x)‖ₑ ^ (2 : ℝ)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_add_right']
        exact ((hρ.comp (continuous_const.sub continuous_id)).aemeasurable.enorm).pow_const _
      _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * (M + R) := by
        rw [htrans]
        gcongr
  have hfin : ENNReal.ofReal (1 / 2 : ℝ) * (M + R) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hL2.ne, hρ2.ne⟩)
  calc
    |serrinMol u ρ k y τ| = ‖∫ x : Vec3, u (x, τ) k * ρ (y - x)‖ := rfl
    _ ≤ (∫⁻ x : Vec3, ‖u (x, τ) k * ρ (y - x)‖ₑ).toReal := by
      have h := norm_integral_le_lintegral_norm (μ := volume)
        (fun x : Vec3 => u (x, τ) k * ρ (y - x))
      simpa only [ofReal_norm] using h
    _ ≤ (ENNReal.ofReal (1 / 2 : ℝ) * (M + R)).toReal :=
      ENNReal.toReal_mono hfin hlint

/-- Over a compact set of mollification points, the tested fluxes are dominated
at almost every time by an integrable function of time. -/
theorem serrinMolFlux_bound_ae {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p)
    {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    {K : Set Vec3} (hK : IsCompact K) :
    ∃ m : ℝ → ℝ, IntegrableOn m (Ioo 0 T) ∧
      ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)), ∀ y ∈ K, ∀ k : Fin 3,
        |serrinMolFlux u Du p ρ k y τ| ≤ m τ := by
  let K' : Set Vec3 := (fun q : Vec3 × Vec3 => q.1 - q.2) '' (K ×ˢ tsupport ρ)
  have hK' : IsCompact K' := (hK.prod hρc.isCompact).image (by fun_prop)
  have hdρc (j : Fin 3) : Continuous (spatialDeriv ρ j) :=
    (hρ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdρcs (j : Fin 3) : HasCompactSupport (spatialDeriv ρ j) := by
    apply HasCompactSupport.of_support_subset_isCompact hρc.isCompact
    intro x hx
    by_contra hnot
    exact hx (serrin_spatialDeriv_eq_zero_of_not_mem_tsupport hnot j)
  choose Cj hCj using fun j : Fin 3 => (hdρcs j).exists_bound_of_continuous (hdρc j)
  let C : ℝ := ∑ j : Fin 3, |Cj j|
  have hC (j : Fin 3) (x : Vec3) : |spatialDeriv ρ j x| ≤ C := by
    calc
      |spatialDeriv ρ j x| ≤ |Cj j| := (hCj j x).trans (le_abs_self _)
      _ ≤ C := Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let G : ParabolicPoint → ℝ := fun z =>
    (∑ k : Fin 3, ∑ j : Fin 3, |u z k * u z j|) +
      (∑ k : Fin 3, ∑ j : Fin 3, |Du z k j|) + |p z|
  have hq53 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (5 / 3 : ℝ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hp := hU.pressure
  have huu := serrinWeak_tensor_memLp_one hU
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have hGint : Integrable (fun z : Vec3 × ℝ => G z)
      ((volume.restrict K').prod (volume.restrict (Ioo 0 T))) := by
    refine ((integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => ?_).add
      (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => ?_)).add ?_
    · exact (serrin_integrable_restrict_of_memLp hK' le_rfl (huu k j)).abs
    · exact (serrin_integrable_restrict_of_memLp hK' (by norm_num)
        ((hDu2.eval k).eval j)).abs
    · exact (serrin_integrable_restrict_of_memLp hK' hq53 hp).abs
  refine ⟨fun τ => C * ∫ x, G (x, τ) ∂(volume.restrict K'), ?_, ?_⟩
  · exact hGint.integral_prod_right.const_mul C
  · filter_upwards [hGint.prod_left_ae] with τ hτ y hy k
    have hbound : ∀ x : Vec3, ‖serrinMolFluxDensity u Du p ρ k y (x, τ)‖ ≤
        C * K'.indicator (fun x => G (x, τ)) x := by
      intro x
      by_cases hx : x ∈ K'
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
        unfold serrinMolFluxDensity
        have h1 : |∑ j : Fin 3, u (x, τ) k * u (x, τ) j * spatialDeriv ρ j (y - x)| ≤
            C * ∑ j : Fin 3, |u (x, τ) k * u (x, τ) j| := by
          rw [Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hC j _) (abs_nonneg _)
        have h2 : |∑ j : Fin 3, Du (x, τ) k j * spatialDeriv ρ j (y - x)| ≤
            C * ∑ j : Fin 3, |Du (x, τ) k j| := by
          rw [Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hC j _) (abs_nonneg _)
        have h3 : |p (x, τ) * spatialDeriv ρ k (y - x)| ≤ C * |p (x, τ)| := by
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hC k _) (abs_nonneg _)
        have hk1 : (∑ j : Fin 3, |u (x, τ) k * u (x, τ) j|) ≤
            ∑ k' : Fin 3, ∑ j : Fin 3, |u (x, τ) k' * u (x, τ) j| :=
          Finset.single_le_sum (f := fun k' => ∑ j : Fin 3, |u (x, τ) k' * u (x, τ) j|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
        have hk2 : (∑ j : Fin 3, |Du (x, τ) k j|) ≤
            ∑ k' : Fin 3, ∑ j : Fin 3, |Du (x, τ) k' j| :=
          Finset.single_le_sum (f := fun k' => ∑ j : Fin 3, |Du (x, τ) k' j|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
        calc
          |-(∑ j : Fin 3, u (x, τ) k * u (x, τ) j * spatialDeriv ρ j (y - x)) +
              (∑ j : Fin 3, Du (x, τ) k j * spatialDeriv ρ j (y - x)) -
              p (x, τ) * spatialDeriv ρ k (y - x)| ≤
              |∑ j : Fin 3, u (x, τ) k * u (x, τ) j * spatialDeriv ρ j (y - x)| +
              |∑ j : Fin 3, Du (x, τ) k j * spatialDeriv ρ j (y - x)| +
              |p (x, τ) * spatialDeriv ρ k (y - x)| := by
            refine (abs_sub _ _).trans ?_
            gcongr
            exact (abs_add_le _ _).trans (by rw [abs_neg])
          _ ≤ C * (∑ j : Fin 3, |u (x, τ) k * u (x, τ) j|) +
              C * (∑ j : Fin 3, |Du (x, τ) k j|) + C * |p (x, τ)| := by
            gcongr
          _ ≤ C * G (x, τ) := by
            simp only [G]
            have := mul_le_mul_of_nonneg_left hk1 hCnn
            have := mul_le_mul_of_nonneg_left hk2 hCnn
            nlinarith only [this, mul_le_mul_of_nonneg_left hk1 hCnn,
              mul_le_mul_of_nonneg_left hk2 hCnn]
      · rw [indicator_of_notMem hx, mul_zero]
        have hyx : y - x ∉ tsupport ρ := by
          intro hmem
          apply hx
          exact ⟨(y, y - x), ⟨hy, hmem⟩, by simp⟩
        have hz (j : Fin 3) : spatialDeriv ρ j (y - x) = 0 :=
          serrin_spatialDeriv_eq_zero_of_not_mem_tsupport hyx j
        simp [serrinMolFluxDensity, hz]
    have hgint : Integrable (fun x => C * K'.indicator (fun x => G (x, τ)) x) volume :=
      ((integrable_indicator_iff hK'.measurableSet).mpr hτ).const_mul C
    calc
      |serrinMolFlux u Du p ρ k y τ| = ‖∫ x : Vec3, serrinMolFluxDensity u Du p ρ k y (x, τ)‖ :=
        rfl
      _ ≤ ∫ x : Vec3, C * K'.indicator (fun x => G (x, τ)) x :=
        norm_integral_le_of_norm_le hgint (Eventually.of_forall hbound)
      _ = C * ∫ x, G (x, τ) ∂(volume.restrict K') := by
        rw [integral_const_mul, integral_indicator hK'.measurableSet]

end ESS
