/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.Decrement

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.EntryGeneration

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: Steps 3 and 4, the entry generation and the geometry there

Step 3 (`p.initial.fixed.grid.scale`): the per-step decrement and
the determinant budget force a generation `n₀` in
`[R, R + ⌈C log₃(2+Π)⌉]` at which `𝒫_Id(n₀;j_*) + D_{Id,j_*}(n₀) ≤ η₀`, and the carried
history majorization converts that into the bound on
`ℋ_Id(n₀) + D_{Id,j_*}(n₀)`.  Step 4 of `p.initial.fixed.grid.scale` supplies the deterministic
geometry at that
generation from the entry-radius estimate.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- E7 (kernel). Step 3, the hitting index: some `n₀ = T_ℓ`, `ℓ < K`, has
`𝒫_Id(n₀;j_*) + D_{Id,j_*}(n₀) ≤ η₀`, and `R ≤ n₀ ≤ R + ⌈C log₃(2+Π)⌉`. -/
theorem exists_entry_generation_eta0 (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
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
                ∃ n₀ : ℤ,
                  R ≤ n₀ ∧
                    n₀ ≤ R + ⌈C * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                    profile P γ (1 : Mat d) jStar (jStar : ℤ) n₀ +
                        determinantDrift P γ (1 : Mat d) jStar n₀ ≤ η₀ := by
  obtain ⟨Csrc1, hCsrc1pos, hDecr⟩ := initial_log_decrement d hd γ hγ
  obtain ⟨Csrc2, hCsrc2pos, C2, hC2pos, hBudget⟩ := synchronized_loss_budget_one d hd γ hγ
  obtain ⟨Csrc3, hCsrc3pos, hStart⟩ := starting_log_le_one d hd γ hγ
  refine ⟨max Csrc1 (max Csrc2 Csrc3), lt_of_lt_of_le hCsrc1pos (le_max_left _ _), ?_⟩
  intro η₀ hη₀
  obtain ⟨C1, hC1pos, hDecrEta⟩ := hDecr η₀ hη₀
  obtain ⟨C3, hC3pos, hStartEta⟩ := hStart η₀ hη₀
  have hQpos : (0:ℝ) < (bigQ d γ : ℝ) := bigQ_real_pos d γ hγ
  have ha : (0:ℝ) < Real.log (16 / 9) := Real.log_pos (by norm_num)
  set a : ℝ := Real.log (16 / 9) with ha_def
  have hBpos : 0 < C3 + C1 * C2 := add_pos hC3pos (mul_pos hC1pos hC2pos)
  set B : ℝ := C3 + C1 * C2 with hB_def
  have hBdivpos : 0 < B / a + 2 := by
    have hnn : 0 ≤ B / a := div_nonneg (le_of_lt hBpos) (le_of_lt ha)
    linarith only [hnn]
  have h2Qpos : 0 < 2 * (bigQ d γ : ℝ) := by linarith only [hQpos]
  set Cfin : ℝ := 2 * (bigQ d γ : ℝ) * (B / a + 2) with hCfin_def
  have hCfinpos : 0 < Cfin := by rw [hCfin_def]; exact mul_pos h2Qpos hBdivpos
  refine ⟨Cfin, hCfinpos, ?_⟩
  intro P E Ψ K Src hProb hStat hUnit hdag jStar hjStar hCsrc R hR
  have : NeZero d := ⟨by omega⟩
  have := hProb
  have hPi := HCPolySupport.HighContrast.Annealed.aspectRatio_pos_and_three_le hdag
  have hPipos : 0 < aspectRatio E := hPi.1
  have hPige3 : 3 ≤ 2 + aspectRatio E := hPi.2
  have hlogb1 : 1 ≤ Real.logb 3 (2 + aspectRatio E) :=
    one_le_logb_three_of_three_le (2 + aspectRatio E) hPige3
  have hlogbnn : 0 ≤ Real.logb 3 (2 + aspectRatio E) := le_trans zero_le_one hlogb1
  have hCsrc1' : ⌈Csrc1 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Csrc1
      (max Csrc1 (max Csrc2 Csrc3)) (le_max_left _ _) jStar hCsrc
  have hCsrc2' : ⌈Csrc2 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Csrc2
      (max Csrc1 (max Csrc2 Csrc3))
      (le_trans (le_max_left Csrc2 Csrc3) (le_max_right Csrc1 (max Csrc2 Csrc3)))
      jStar hCsrc
  have hCsrc3' : ⌈Csrc3 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Csrc3
      (max Csrc1 (max Csrc2 Csrc3))
      (le_trans (le_max_right Csrc2 Csrc3) (le_max_right Csrc1 (max Csrc2 Csrc3)))
      jStar hCsrc
  have hMnonneg : 0 ≤ B * Real.logb 3 (2 + aspectRatio E) := mul_nonneg (le_of_lt hBpos) hlogbnn
  set M : ℝ := B * Real.logb 3 (2 + aspectRatio E) with hM_def
  set Ksteps : ℕ := ⌈M / a⌉₊ + 1 with hKsteps_def
  have hKsteps1 : 1 ≤ Ksteps := Nat.le_add_left 1 _
  have hMdivnn : 0 ≤ M / a := div_nonneg hMnonneg (le_of_lt ha)
  have hMdiv_le : M ≤ (⌈M / a⌉₊ : ℝ) * a := (div_le_iff₀ ha).mp (Nat.le_ceil (M / a))
  have hceil_lt : (⌈M / a⌉₊ : ℝ) < M / a + 1 := Nat.ceil_lt_add_one hMdivnn
  have hKstepsCast : (Ksteps : ℝ) = (⌈M / a⌉₊ : ℝ) + 1 := by rw [hKsteps_def]; push_cast; ring
  have hKa : M < (Ksteps : ℝ) * a := by
    have heq : (Ksteps : ℝ) * a = (⌈M / a⌉₊ : ℝ) * a + a := by rw [hKstepsCast]; ring
    linarith only [hMdiv_le, heq, ha]
  have hW : ∀ ℓ : ℕ, 0 ≤
      Real.log (1 + η₀⁻¹ *
        (profile P γ (1 : Mat d) jStar (jStar : ℤ)
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
          determinantDrift P γ (1 : Mat d) jStar
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))))) := by
    intro ℓ
    have hQZnn : (0:ℤ) ≤ (bigQ d γ : ℤ) := Nat.cast_nonneg _
    have hLnn : (0:ℤ) ≤ (ℓ:ℤ) := Nat.cast_nonneg _
    have hprod : (0:ℤ) ≤ (ℓ:ℤ) * (2 * (bigQ d γ : ℤ)) := mul_nonneg hLnn (by linarith only [hQZnn])
    have hTge : (jStar : ℤ) ≤ R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)) := by
      linarith only [hR, hQZnn, hprod]
    have hp := profile_one_nonneg d hd γ hγ P E Ψ K Src hProb hStat hUnit hdag jStar hjStar
      jStar (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) le_rfl hTge
    have hdt := determinantDrift_one_nonneg d hd γ hγ P E Ψ K Src hProb hStat hUnit hdag jStar
      hjStar (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))
    have hη0inv : 0 ≤ η₀⁻¹ := le_of_lt (inv_pos.mpr hη₀.1)
    have hge1 : (1:ℝ) ≤ 1 + η₀⁻¹ * (profile P γ (1 : Mat d) jStar (jStar : ℤ)
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
          determinantDrift P γ (1 : Mat d) jStar
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) := by
      nlinarith only [mul_nonneg hη0inv (add_nonneg hp hdt)]
    exact Real.log_nonneg hge1
  have hdec : ∀ ℓ : ℕ, ℓ < Ksteps →
      (η₀ < profile P γ (1 : Mat d) jStar (jStar : ℤ)
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
          determinantDrift P γ (1 : Mat d) jStar
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) →
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
        a +
        C1 * synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
          (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) := by
    intro ℓ _hℓ hbad
    exact hDecrEta P E Ψ K Src hProb hStat hUnit hdag jStar hjStar hCsrc1' R hR ℓ hbad
  have hW0le : Real.log (1 + η₀⁻¹ *
        (profile P γ (1 : Mat d) jStar (jStar : ℤ)
            (R + 2 * (bigQ d γ : ℤ) + ((0:ℕ) : ℤ) * (2 * (bigQ d γ : ℤ))) +
          determinantDrift P γ (1 : Mat d) jStar
            (R + 2 * (bigQ d γ : ℤ) + ((0:ℕ) : ℤ) * (2 * (bigQ d γ : ℤ))))) ≤
      C3 * Real.logb 3 (2 + aspectRatio E) := by
    have hQZnn : (0:ℤ) ≤ (bigQ d γ : ℤ) := Nat.cast_nonneg _
    have hm0 : (jStar : ℤ) ≤ R + 2 * (bigQ d γ : ℤ) + ((0:ℕ) : ℤ) * (2 * (bigQ d γ : ℤ)) := by
      push_cast
      linarith only [hR, hQZnn]
    exact hStartEta P E Ψ K Src hProb hStat hUnit hdag jStar hjStar hCsrc3' _ hm0
  have hSumle : (∑ ℓ ∈ Finset.range Ksteps,
      synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
        (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) ≤
      C2 * Real.logb 3 (2 + aspectRatio E) :=
    hBudget P E Ψ K Src hProb hStat hUnit hdag jStar hjStar hCsrc2' R hR Ksteps hKsteps1
  have hKfinal :
      Real.log (1 + η₀⁻¹ *
        (profile P γ (1 : Mat d) jStar (jStar : ℤ)
            (R + 2 * (bigQ d γ : ℤ) + ((0:ℕ) : ℤ) * (2 * (bigQ d γ : ℤ))) +
          determinantDrift P γ (1 : Mat d) jStar
            (R + 2 * (bigQ d γ : ℤ) + ((0:ℕ) : ℤ) * (2 * (bigQ d γ : ℤ))))) +
        C1 * (∑ ℓ ∈ Finset.range Ksteps,
          synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) <
      (Ksteps : ℝ) * a := by
    have h1 : C1 * (∑ ℓ ∈ Finset.range Ksteps,
          synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)))) ≤
        C1 * (C2 * Real.logb 3 (2 + aspectRatio E)) :=
      mul_le_mul_of_nonneg_left hSumle (le_of_lt hC1pos)
    have heqM : C3 * Real.logb 3 (2 + aspectRatio E) + C1 * (C2 * Real.logb 3 (2 + aspectRatio E))
        = M := by rw [hM_def, hB_def]; ring
    linarith only [hW0le, h1, heqM, hKa]
  obtain ⟨ℓ, hℓK, hnbad⟩ :=
    exists_good_index_of_decrement
      (fun ℓ => Real.log (1 + η₀⁻¹ *
        (profile P γ (1 : Mat d) jStar (jStar : ℤ)
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
          determinantDrift P γ (1 : Mat d) jStar
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))))))
      (fun ℓ => synchCharge P (1 : Mat d) (2 * (bigQ d γ : ℤ))
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))))
      (fun ℓ => η₀ < profile P γ (1 : Mat d) jStar (jStar : ℤ)
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) +
          determinantDrift P γ (1 : Mat d) jStar
            (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))))
      Ksteps a C1 hW hdec hKfinal
  refine ⟨R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ)), ?_, ?_, ?_⟩
  · have hQZnn : (0:ℤ) ≤ (bigQ d γ : ℤ) := Nat.cast_nonneg _
    have hLnn : (0:ℤ) ≤ (ℓ:ℤ) := Nat.cast_nonneg _
    have hprod : (0:ℤ) ≤ (ℓ:ℤ) * (2 * (bigQ d γ : ℤ)) := mul_nonneg hLnn (by linarith only [hQZnn])
    linarith only [hR, hQZnn, hprod]
  · have hℓK1 : ℓ + 1 ≤ Ksteps := hℓK
    have hcast1 : ((ℓ + 1 : ℕ) : ℝ) ≤ (Ksteps : ℝ) := by exact_mod_cast hℓK1
    have hstep : (Ksteps : ℝ) < M / a + 2 := by rw [hKstepsCast]; linarith only [hceil_lt]
    have hlt1 : ((ℓ + 1 : ℕ) : ℝ) < M / a + 2 := lt_of_le_of_lt hcast1 hstep
    have hlt2 : 2 * (bigQ d γ : ℝ) * ((ℓ + 1 : ℕ) : ℝ) <
        2 * (bigQ d γ : ℝ) * (M / a + 2) :=
      mul_lt_mul_of_pos_left hlt1 h2Qpos
    have hle3 : 4 * (bigQ d γ : ℝ) ≤ 4 * (bigQ d γ : ℝ) * Real.logb 3 (2 + aspectRatio E) := by
      nlinarith only [hlogb1, hQpos]
    have hCfineq : Cfin * Real.logb 3 (2 + aspectRatio E) =
        2 * (bigQ d γ : ℝ) * (M / a) + 4 * (bigQ d γ : ℝ) * Real.logb 3 (2 + aspectRatio E) := by
      rw [hCfin_def, hM_def]
      have hane : a ≠ 0 := ne_of_gt ha
      field_simp
      ring
    have hfinalreal : 2 * (bigQ d γ : ℝ) * ((ℓ + 1 : ℕ) : ℝ) ≤
        Cfin * Real.logb 3 (2 + aspectRatio E) := by
      rw [hCfineq]
      nlinarith only [hlt2, hle3]
    have hcastdiff : ((R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) - R : ℝ)
        = 2 * (bigQ d γ : ℝ) * ((ℓ + 1 : ℕ) : ℝ) := by push_cast; ring
    have hdiffle : ((R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) - R : ℝ) ≤
        Cfin * Real.logb 3 (2 + aspectRatio E) := by rw [hcastdiff]; exact hfinalreal
    have hceilge : Cfin * Real.logb 3 (2 + aspectRatio E) ≤
        (⌈Cfin * Real.logb 3 (2 + aspectRatio E)⌉ : ℝ) := Int.le_ceil _
    have hfin : ((R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) - R : ℝ) ≤
        (⌈Cfin * Real.logb 3 (2 + aspectRatio E)⌉ : ℝ) := le_trans hdiffle hceilge
    have hfinZ : (R + 2 * (bigQ d γ : ℤ) + (ℓ : ℤ) * (2 * (bigQ d γ : ℤ))) - R ≤
        ⌈Cfin * Real.logb 3 (2 + aspectRatio E)⌉ := by exact_mod_cast hfin
    linarith only [hfinZ]
  · exact not_lt.mp hnbad

/-- E8. `e.renormalization.entry` (`p.initial.fixed.grid.scale`): the smallness at `n₀` in the
form `𝒫_Id(n₀;n₀) + D_{Id,j_*}(n₀) ≤ η_init`, via carried majorization and
`η₀ := η_init / max 1 C`. -/
theorem exists_entry_generation (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ ηinit : ℝ, ηinit ∈ Set.Ioc (0 : ℝ) 1 →
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
                ∃ n₀ : ℤ,
                  R ≤ n₀ ∧
                    n₀ ≤ R + ⌈C * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                    profile P γ (1 : Mat d) jStar n₀ n₀ +
                        determinantDrift P γ (1 : Mat d) jStar n₀ ≤ ηinit := by
  obtain ⟨Cs₁, hCs₁, Cmaj, hCmaj, hmaj⟩ := carried_history_majorization_one d hd γ hγ
  obtain ⟨Cs₂, hCs₂, hgen⟩ := exists_entry_generation_eta0 d hd γ hγ
  refine ⟨max Cs₁ Cs₂, lt_of_lt_of_le hCs₁ (le_max_left _ _), ?_⟩
  intro ηinit hηinit
  have hMpos : (0 : ℝ) < max 1 Cmaj := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hη₀ : ηinit / max 1 Cmaj ∈ Set.Ioc (0 : ℝ) 1 := by
    refine ⟨div_pos hηinit.1 hMpos, ?_⟩
    rw [div_le_one hMpos]
    exact le_trans hηinit.2 (le_max_left _ _)
  obtain ⟨C, hCpos, hgen'⟩ := hgen (ηinit / max 1 Cmaj) hη₀
  refine ⟨C, hCpos, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr R hR
  have : NeZero d := ⟨by omega⟩
  have := hP
  have h₁ : ⌈Cs₁ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cs₁ (max Cs₁ Cs₂)
      (le_max_left _ _) jStar hthr
  have h₂ : ⌈Cs₂ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cs₂ (max Cs₁ Cs₂)
      (le_max_right _ _) jStar hthr
  obtain ⟨n₀, hn₀R, hn₀up, hn₀le⟩ :=
    hgen' P E Ψ K Src hP hstat hunit hdag jStar hjStar h₂ R hR
  refine ⟨n₀, hn₀R, hn₀up, ?_⟩
  have hjn : (jStar : ℤ) ≤ n₀ := le_trans hR hn₀R
  have hposdef := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src
    hstat hdag
    jStar hjStar (1 : Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) n₀
  rw [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at hposdef
  have hself : profile P γ (1 : Mat d) jStar n₀ n₀ = history P γ (1 : Mat d) jStar n₀ :=
    profile_self_of_posDef P γ (1 : Mat d) jStar n₀ hposdef
  have hmaj' := hmaj P E Ψ K Src hP hstat hunit hdag jStar hjStar h₁ (jStar : ℤ) n₀ le_rfl hjn
  have hpnn := profile_one_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag jStar hjStar
    (jStar : ℤ) n₀ le_rfl hjn
  have hdnn := determinantDrift_one_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag jStar
    hjStar n₀
  have hmono : Cmaj * (profile P γ (1 : Mat d) jStar (jStar : ℤ) n₀ +
      determinantDrift P γ (1 : Mat d) jStar n₀) ≤
      max 1 Cmaj * (profile P γ (1 : Mat d) jStar (jStar : ℤ) n₀ +
        determinantDrift P γ (1 : Mat d) jStar n₀) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg hpnn hdnn)
  have hscale : max 1 Cmaj * (profile P γ (1 : Mat d) jStar (jStar : ℤ) n₀ +
      determinantDrift P γ (1 : Mat d) jStar n₀) ≤ max 1 Cmaj * (ηinit / max 1 Cmaj) :=
    mul_le_mul_of_nonneg_left hn₀le (le_of_lt hMpos)
  have hcancel : max 1 Cmaj * (ηinit / max 1 Cmaj) = ηinit :=
    mul_div_cancel₀ ηinit (ne_of_gt hMpos)
  rw [hself]
  show fluctuationHistory P γ (1 : Mat d) jStar n₀ +
      meanHistory P γ (1 : Mat d) (jStar : ℤ) n₀ +
      determinantDrift P γ (1 : Mat d) jStar n₀ ≤ ηinit
  linarith only [hmaj', hmono, hscale, hcancel.ge, hcancel.le]

/-! ## F. Step 4 — geometry (`p.initial.fixed.grid.scale`) -/

/-- F1. `e.initial.geometry.bounds` at every generation `n₀ ≥ j_*`: the two-sided block
comparison and the entry radius; `Cgeom` depends on `d` alone and is chosen before `γ`. -/
theorem geometry_at_generation (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1),
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (Src : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K Src →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
            ∀ n₀ : ℤ, (jStar : ℤ) ≤ n₀ →
              BlockMatLoewnerLE
                  (blockScale (1 / 2)
                    (ofFullBlockMat
                      (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
                        toFullBlockMat (blockSwap d))))
                  (adaptedMean P (1 : Mat d) n₀) ∧
                BlockMatLoewnerLE (adaptedMean P (1 : Mat d) n₀) (blockScale 2 E) ∧
                projectiveDistance (1 : Mat d)
                    (explicitCanonicalMetric (adaptedMean P (1 : Mat d) n₀)) ≤
                  Cgeom * Real.log (2 + 4 * aspectRatio E) := by
  obtain ⟨Cgeom, hCgeom, hrad⟩ := entry_radius d hd
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro γ hγ
  obtain ⟨Csrc, hCsrc, hsrc⟩ := initial_source_bounds_all d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hCsrcle n₀ hn₀
  have := hP
  have : NeZero d := ⟨by omega⟩
  obtain ⟨h1, h2⟩ := hsrc P E Ψ K Src hP hstat hunit hdag jStar hjStar hCsrcle n₀ hn₀
  refine ⟨h1, h2, ?_⟩
  have hposdef := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src
    hstat hdag jStar
      hjStar (1 : Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) n₀
  rw [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at hposdef
  exact hrad E (adaptedMean P (1 : Mat d) n₀) hdag.refBlock_isSymm hdag.refBlock_posDef
    (HCPolySupport.HighContrast.Annealed.refBlock_reference_order hdag) hposdef h1 h2

end

end HCPolySupport.HighContrast.Multiscale
