/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.Propagation

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.Decrement

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: Step 2, the logarithmic decrement and its budget

Step 2 of the printed proof (`p.initial.fixed.grid.scale`): along
the synchronized scales `T_ℓ = R + 2Q + ℓ·2Q` the logarithm
`W_ℓ = log(1 + η₀⁻¹(𝒫_Id(T_ℓ;j_*) + D_{Id,j_*}(T_ℓ)))` drops by `log(16/9)` per step up to a
determinant-loss defect, the accumulated synchronized losses are bounded by
`C log₃(2 + Π)`, and the starting value is bounded by `C(d,γ,η₀) log₃(2 + Π)`.
-/

open HCPolySupport.HighContrast (CoeffSpace aspectRatio)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- E4. `e.initial.log.decrement` (`p.initial.fixed.grid.scale`) at the synchronized scales
`T_ℓ = R + 2Q + ℓ·2Q`, with `W_ℓ = log(1 + η₀⁻¹(𝒫_Id(T_ℓ;j_*) + D_{Id,j_*}(T_ℓ)))`. -/
theorem initial_log_decrement (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ η₀ : ℝ, η₀ ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (Src : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K Src →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ R : ℤ, (jStar : ℤ) ≤ R →
                ∀ ℓ : ℕ,
                  η₀ <
                      profile P γ (1 : Mat d) jStar (jStar : ℤ)
                          (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
                        determinantDrift P γ (1 : Mat d) jStar
                          (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) →
                    Real.log (1 + η₀⁻¹ *
                        (profile P γ (1 : Mat d) jStar (jStar : ℤ)
                            (R + 2 * (bigQ d γ : ℤ) + ((ℓ + 1 : ℕ) : ℤ) * (2 * (bigQ d γ : ℤ))) +
                          determinantDrift P γ (1 : Mat d) jStar
                            (R + 2 * (bigQ d γ : ℤ) + ((ℓ + 1 : ℕ) : ℤ) * (2 * (bigQ d γ : ℤ))))) ≤
                      Real.log (1 + η₀⁻¹ *
                          (profile P γ (1 : Mat d) jStar (jStar : ℤ)
                              (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
                            determinantDrift P γ (1 : Mat d) jStar
                              (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))))) -
                        Real.log (16 / 9) +
                        C * synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
                          (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) := by
  obtain ⟨Csrc, hCsrc, Cp, hCp, hprop⟩ := synchronized_propagation_one d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro η₀ hη₀
  have hη₀pos : (0 : ℝ) < η₀ := hη₀.1
  have hη₀inv : (0 : ℝ) < η₀⁻¹ := inv_pos.mpr hη₀pos
  have hQpos : (0 : ℝ) < (bigQ d γ : ℝ) := bigQ_real_pos d γ hγ
  have hCdiv : (0 : ℝ) < Cp / η₀ := div_pos hCp hη₀pos
  refine ⟨(bigQ d γ : ℝ) + 8 / 9 * (Cp / η₀) * (bigQ d γ : ℝ),
    add_pos hQpos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8 / 9) hCdiv) hQpos), ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr R hR ℓ hbig
  have : NeZero d := ⟨by omega⟩
  have := hP
  have hQZ : (0 : ℤ) ≤ (bigQ d γ : ℤ) := Int.natCast_nonneg _
  have hLnn : (0 : ℤ) ≤ (ℓ : ℤ) := Int.natCast_nonneg _
  have hprod : (0 : ℤ) ≤ (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)) :=
    mul_nonneg hLnn (by linarith only [hQZ])
  have hTge : (jStar : ℤ) + ((2 * bigQ d γ : ℕ) : ℤ) ≤
      R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)) := by
    push_cast
    linarith only [hR, hprod]
  have HP := hprop P E Ψ K Src hP hstat hunit hdag (2 * bigQ d γ) le_rfl jStar hjStar hthr
    (jStar : ℤ) (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) le_rfl hTge
  push_cast at HP
  have hsucc : R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)) + 2 * (bigQ d γ : ℤ) =
      R + 2 * (bigQ d γ : ℤ) + ((ℓ + 1 : ℕ) : ℤ) * (2 * (bigQ d γ : ℤ)) := by
    push_cast
    ring
  rw [hsucc] at HP
  have hTnext : (jStar : ℤ) ≤
      R + 2 * (bigQ d γ : ℤ) + ((ℓ + 1 : ℕ) : ℤ) * (2 * (bigQ d γ : ℤ)) := by
    have hprod' : (0 : ℤ) ≤ ((ℓ + 1 : ℕ) : ℤ) * (2 * (bigQ d γ : ℤ)) :=
      mul_nonneg (Int.natCast_nonneg _) (by linarith only [hQZ])
    linarith only [hR, hQZ, hprod']
  have hpnn' := profile_one_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag jStar hjStar
    (jStar : ℤ) (R + 2 * (bigQ d γ : ℤ) + ((ℓ + 1 : ℕ) : ℤ) * (2 * (bigQ d γ : ℤ))) le_rfl hTnext
  have hdnn' := determinantDrift_one_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag jStar
    hjStar (R + 2 * (bigQ d γ : ℤ) + ((ℓ + 1 : ℕ) : ℤ) * (2 * (bigQ d γ : ℤ)))
  have hy : 0 ≤ synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
      (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) := by
    rw [synchCharge]
    refine Finset.sum_nonneg ?_
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hja : (jStar : ℤ) ≤ a - 2 * (bigQ d γ : ℤ) := by
      linarith only [ha.1, hR, hprod]
    have haa : a - 2 * (bigQ d γ : ℤ) ≤ a := by linarith only [hQZ]
    have hdl := HCPolySupport.HighContrast.Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d)
      (a - 2 * (bigQ d γ : ℤ)) a hja haa
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at hdl
  have hx : (1 : ℝ) ≤ η₀⁻¹ *
      (profile P γ (1 : Mat d) jStar (jStar : ℤ)
          (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
        determinantDrift P γ (1 : Mat d) jStar
          (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) := by
    have hcancel : η₀⁻¹ * η₀ = 1 := inv_mul_cancel₀ (ne_of_gt hη₀pos)
    have hmono := mul_le_mul_of_nonneg_left (le_of_lt hbig) (le_of_lt hη₀inv)
    linarith only [hcancel, hmono]
  have hexpand : η₀⁻¹ *
      (1 / 8 *
          Real.exp ((bigQ d γ : ℝ) * synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) *
          (profile P γ (1 : Mat d) jStar (jStar : ℤ)
              (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
            determinantDrift P γ (1 : Mat d) jStar
              (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) +
        Cp *
          (Real.exp ((bigQ d γ : ℝ) * synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) - 1)) =
      1 / 8 *
          Real.exp ((bigQ d γ : ℝ) * synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) *
          (η₀⁻¹ *
            (profile P γ (1 : Mat d) jStar (jStar : ℤ)
                (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
              determinantDrift P γ (1 : Mat d) jStar
                (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))))) +
        Cp / η₀ *
          (Real.exp ((bigQ d γ : ℝ) * synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) - 1) := by
    rw [div_eq_mul_inv]
    ring
  have hkey := mul_le_mul_of_nonneg_left HP (le_of_lt hη₀inv)
  rw [hexpand] at hkey
  exact scalar_log_decrement (bigQ d γ : ℝ) (Cp / η₀) _ _ _ (le_of_lt hQpos)
    (le_of_lt hCdiv) hx hy (by positivity) hkey

/-- E5. The synchronized determinant budget (`p.initial.fixed.grid.scale`):
`∑_{ℓ<K} Δ̂_h(T_ℓ) ≤ h Δ_{T_0+1−h, T_0+Kh} ≤ C log₃(2+Π)`. -/
theorem synchronized_loss_budget_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (Src : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K Src →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
            ∀ R : ℤ, (jStar : ℤ) ≤ R →
              ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                (∑ ℓ ∈ Finset.range Ksteps,
                    synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
                      (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) ≤
                  C * Real.logb 3 (2 + aspectRatio E) := by
  obtain ⟨Cs₁, hCs₁, hmult⟩ := synchronized_multiplicity_one d hd γ hγ
  obtain ⟨Cs₂, hCs₂, hnorm⟩ := initial_normalization_bounds_all d hd γ hγ
  have hQpos : (0 : ℝ) < (bigQ d γ : ℝ) := bigQ_real_pos d γ hγ
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hlog24 : (0 : ℝ) < Real.log 24 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  refine ⟨max Cs₁ Cs₂, lt_of_lt_of_le hCs₁ (le_max_left _ _),
    2 * (bigQ d γ : ℝ) * (2 * (d : ℝ) * (Real.log 24 + Real.log 3)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 * (bigQ d γ : ℝ) := by linarith only [hQpos]
    have h2 : (0 : ℝ) < 2 * (d : ℝ) * (Real.log 24 + Real.log 3) := by
      have : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hdR]
      exact mul_pos this (by linarith only [hlog24, hlog3])
    exact mul_pos h1 h2
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr R hR Ksteps hK
  have : NeZero d := ⟨by omega⟩
  have := hP
  have h₁ : ⌈Cs₁ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cs₁ (max Cs₁ Cs₂)
      (le_max_left _ _) jStar hthr
  have h₂ : ⌈Cs₂ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cs₂ (max Cs₁ Cs₂)
      (le_max_right _ _) jStar hthr
  have hQZ : (2 : ℤ) ≤ (bigQ d γ : ℤ) := by exact_mod_cast hQ2
  have hm₀ : (jStar : ℤ) + ((2 * bigQ d γ : ℕ) : ℤ) ≤ R + 2 * (bigQ d γ : ℤ) := by
    push_cast
    linarith only [hR]
  have HM := hmult P E Ψ K Src hP hstat hunit hdag (2 * bigQ d γ) le_rfl jStar hjStar h₁
    (R + 2 * (bigQ d γ : ℤ)) hm₀ Ksteps hK
  push_cast at HM
  have harg : R + 2 * (bigQ d γ : ℤ) + 1 - 2 * (bigQ d γ : ℤ) = R + 1 := by ring
  rw [harg] at HM
  have hjle : (jStar : ℤ) ≤ R + 1 := by linarith only [hR]
  have hKnn : (0 : ℤ) ≤ (Ksteps : ℤ) * (2 * (bigQ d γ : ℤ)) :=
    mul_nonneg (Int.natCast_nonneg _) (by linarith only [hQZ])
  have hmle : R + 1 ≤ R + 2 * (bigQ d γ : ℤ) + (Ksteps : ℤ) * (2 * (bigQ d γ : ℤ)) := by
    linarith only [hQZ, hKnn]
  obtain ⟨-, -, -, -, -, hlog⟩ := hnorm P E Ψ K Src hP hstat hunit hdag jStar hjStar h₂
    (R + 1) (R + 2 * (bigQ d γ : ℤ) + (Ksteps : ℤ) * (2 * (bigQ d γ : ℤ))) hjle hmle
  have hPi : 1 ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hlogb := log_aspect_le_logb (aspectRatio E) hPi
  have h2Qnn : (0 : ℝ) ≤ 2 * (bigQ d γ : ℝ) := by linarith only [hQpos]
  have hdnn : (0 : ℝ) ≤ 2 * (d : ℝ) := by linarith only [hdR]
  have hstep1 := mul_le_mul_of_nonneg_left hlog h2Qnn
  have hstep2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogb hdnn) h2Qnn
  nlinarith only [HM, hstep1, hstep2]

/-- E6. `e.initial.starting.log`: `W ≤ C(d,γ,η₀) log₃(2+Π)` at every `m ≥ j_*`. -/
theorem starting_log_le_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ η₀ : ℝ, η₀ ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (Src : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K Src →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ m : ℤ, (jStar : ℤ) ≤ m →
                Real.log (1 + η₀⁻¹ *
                    (profile P γ (1 : Mat d) jStar (jStar : ℤ) m +
                      determinantDrift P γ (1 : Mat d) jStar m)) ≤
                  C * Real.logb 3 (2 + aspectRatio E) := by
  obtain ⟨Csrc, hCsrc, C₁, hC₁, N, hcrude⟩ := initial_crude_profile d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro η₀ hη
  obtain ⟨hη0, hη1⟩ := hη
  have hηinv : (0 : ℝ) < η₀⁻¹ := inv_pos.mpr hη0
  have hA1 : (1 : ℝ) ≤ 1 + η₀⁻¹ * C₁ := by
    have hnn : (0 : ℝ) ≤ η₀⁻¹ * C₁ := mul_nonneg hηinv.le hC₁.le
    linarith only [hnn]
  have hlogA : (0 : ℝ) ≤ Real.log (1 + η₀⁻¹ * C₁) := Real.log_nonneg hA1
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hNlog3 : (0 : ℝ) ≤ (N : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg N) hlog3.le
  refine ⟨Real.log (1 + η₀⁻¹ * C₁) + (N : ℝ) * Real.log 3 + 1,
    by linarith only [hlogA, hNlog3], ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr m hm
  have := hP
  have : NeZero d := ⟨by omega⟩
  have hPi : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have h3le : (3 : ℝ) ≤ 2 + aspectRatio E := by linarith only [hPi]
  have hXpos : (0 : ℝ) < 2 + aspectRatio E := by linarith only [hPi]
  have hXN1 : (1 : ℝ) ≤ (2 + aspectRatio E) ^ N := one_le_pow₀ (by linarith only [hPi])
  have hXNpos : (0 : ℝ) < (2 + aspectRatio E) ^ N := by positivity
  have hL : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) :=
    one_le_logb_three_of_three_le _ h3le
  have hcr := hcrude P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr m hm
  have hp0 := profile_one_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag jStar hjStar
    (jStar : ℤ) m le_rfl hm
  have hd0 := determinantDrift_one_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag jStar hjStar m
  have hsum0 : (0 : ℝ) ≤ profile P γ (1 : Mat d) jStar (jStar : ℤ) m +
      determinantDrift P γ (1 : Mat d) jStar m := by linarith only [hp0, hd0]
  have hpos : (0 : ℝ) < 1 + η₀⁻¹ * (profile P γ (1 : Mat d) jStar (jStar : ℤ) m +
      determinantDrift P γ (1 : Mat d) jStar m) := by
    have := mul_nonneg hηinv.le hsum0
    linarith only [this]
  have harg : 1 + η₀⁻¹ * (profile P γ (1 : Mat d) jStar (jStar : ℤ) m +
        determinantDrift P γ (1 : Mat d) jStar m) ≤
      (1 + η₀⁻¹ * C₁) * (2 + aspectRatio E) ^ N := by
    have hstep : η₀⁻¹ * (profile P γ (1 : Mat d) jStar (jStar : ℤ) m +
        determinantDrift P γ (1 : Mat d) jStar m) ≤ η₀⁻¹ * (C₁ * (2 + aspectRatio E) ^ N) :=
      mul_le_mul_of_nonneg_left hcr hηinv.le
    have hexp : (1 + η₀⁻¹ * C₁) * (2 + aspectRatio E) ^ N =
        (2 + aspectRatio E) ^ N + η₀⁻¹ * (C₁ * (2 + aspectRatio E) ^ N) := by ring
    rw [hexp]
    linarith only [hstep, hXN1]
  have hlogle := Real.log_le_log hpos harg
  have hprod : Real.log ((1 + η₀⁻¹ * C₁) * (2 + aspectRatio E) ^ N) =
      Real.log (1 + η₀⁻¹ * C₁) + (N : ℝ) * Real.log (2 + aspectRatio E) := by
    rw [Real.log_mul (ne_of_gt (by linarith only [hA1])) (ne_of_gt hXNpos), Real.log_pow]
  have hlogb : Real.log (2 + aspectRatio E) =
      Real.log 3 * Real.logb 3 (2 + aspectRatio E) := by
    rw [Real.logb]
    field_simp
  rw [hprod, hlogb] at hlogle
  have hR : (Real.log (1 + η₀⁻¹ * C₁) + (N : ℝ) * Real.log 3 + 1) *
      Real.logb 3 (2 + aspectRatio E) =
      Real.log (1 + η₀⁻¹ * C₁) * Real.logb 3 (2 + aspectRatio E) +
        (N : ℝ) * Real.log 3 * Real.logb 3 (2 + aspectRatio E) +
        Real.logb 3 (2 + aspectRatio E) := by ring
  have hmid : Real.log (1 + η₀⁻¹ * C₁) + (N : ℝ) *
      (Real.log 3 * Real.logb 3 (2 + aspectRatio E)) =
      Real.log (1 + η₀⁻¹ * C₁) +
        (N : ℝ) * Real.log 3 * Real.logb 3 (2 + aspectRatio E) := by ring
  have hkey : Real.log (1 + η₀⁻¹ * C₁) * Real.logb 3 (2 + aspectRatio E) -
      Real.log (1 + η₀⁻¹ * C₁) =
      Real.log (1 + η₀⁻¹ * C₁) * (Real.logb 3 (2 + aspectRatio E) - 1) := by ring
  have hkey0 : (0 : ℝ) ≤ Real.log (1 + η₀⁻¹ * C₁) * (Real.logb 3 (2 + aspectRatio E) - 1) :=
    mul_nonneg hlogA (by linarith only [hL])
  rw [hR]
  linarith only [hlogle, hmid, hkey, hkey0, hL]

end

end HCPolySupport.HighContrast.Multiscale
