/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.PotentialDecreases

/-!
# High-contrast homogenization: Entry.Multiscale.Global.OutputAndRun

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The selected output and the run

The profile bound satisfied by the selected output, the two inputs
(`p.scale.selection` and `p.initial.fixed.grid.scale`), the predicate `SelectedOutput`
describing the tuple the run produces, and the run itself.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## §F Selected-output estimates (`p.global.selection`) -/

/-- `p.global.selection` (`e.global.selection.profile`), scalar assembly with `ρ = σ^((1-γ)/8)`:
change-of-geometry output `pss + dss ≤ Cout ρ`, fixed-span `s → t` with `Δ_{s,t} < dσ`, the
exponential bound `exp(Qdσ) - 1 ≤ Cexp ρ`, majorization `ptt ≤ Cmaj pts`. The resulting
`Cprof = 2 Cout + (2 + Cmaj) Cfs H (Cout + Cexp)` is free of `σ`. -/
theorem output_profile_bound (Cout Cfs Cmaj Cexp Q ρ σ H d pss dss pts dt ptt Δ : ℝ)
    (hρ : 0 ≤ ρ) (hCout : 0 ≤ Cout) (hCfs : 0 ≤ Cfs) (hCmaj : 0 ≤ Cmaj) (hCexp : 0 ≤ Cexp)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q) (hd : 0 ≤ d) (hσ : 0 ≤ σ)
    (hpss : 0 ≤ pss) (hdss : 0 ≤ dss) (hpts : 0 ≤ pts) (hdt : 0 ≤ dt) (hptt : 0 ≤ ptt)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ < d * σ)
    (h1 : pss + dss ≤ Cout * ρ)
    (h2 : pts + dt ≤ Cfs * H * (pss + dss + (Real.exp (Q * Δ) - 1)))
    (hexp : Real.exp (Q * d * σ) - 1 ≤ Cexp * ρ)
    (h3 : ptt ≤ Cmaj * pts) :
    max (max pss pts) ptt + dss + dt ≤
      (2 * Cout + (2 + Cmaj) * Cfs * H * (Cout + Cexp)) * ρ := by
  have hdσ_nonneg : 0 ≤ d * σ := mul_nonneg hd hσ
  have hQΔ_le_aux : Δ * Q ≤ (d * σ) * Q :=
    mul_le_mul (le_of_lt hΔ) (le_refl Q) hQ hdσ_nonneg
  have hQΔ_le : Q * Δ ≤ Q * d * σ := by
    calc
      Q * Δ = Δ * Q := by ring
      _ ≤ (d * σ) * Q := hQΔ_le_aux
      _ = Q * d * σ := by ring
  have hexp_le : Real.exp (Q * Δ) ≤ Real.exp (Q * d * σ) :=
    Real.exp_le_exp.mpr hQΔ_le
  have hexpΔ : Real.exp (Q * Δ) - 1 ≤ Cexp * ρ := by
    linarith only [hexp_le, hexp]
  have hexpΔ_nonneg : 0 ≤ Real.exp (Q * Δ) - 1 := by
    have hone : (1 : ℝ) ≤ Real.exp (Q * Δ) := by
      simpa using
        (Real.exp_le_exp.mpr (mul_nonneg hQ hΔ0) :
          Real.exp 0 ≤ Real.exp (Q * Δ))
    linarith only [hone]
  have hA : 0 ≤ Cfs * H := mul_nonneg hCfs hH
  have hbracket_nonneg : 0 ≤ pss + dss + (Real.exp (Q * Δ) - 1) := by
    linarith only [hpss, hdss, hexpΔ_nonneg]
  have hsum :
      pss + dss + (Real.exp (Q * Δ) - 1) ≤ Cout * ρ + Cexp * ρ := by
    linarith only [h1, hexpΔ]
  have hmul :
      Cfs * H * (pss + dss + (Real.exp (Q * Δ) - 1)) ≤
        Cfs * H * (Cout * ρ + Cexp * ρ) :=
    mul_le_mul (le_refl (Cfs * H)) hsum hbracket_nonneg hA
  have hptsdt : pts + dt ≤ Cfs * H * (Cout * ρ + Cexp * ρ) :=
    le_trans h2 hmul
  have bpts : pts ≤ Cfs * H * (Cout * ρ + Cexp * ρ) := by
    linarith only [hptsdt, hdt]
  have bdt : dt ≤ Cfs * H * (Cout * ρ + Cexp * ρ) := by
    linarith only [hptsdt, hpts]
  have bpss : pss ≤ Cout * ρ := by
    linarith only [h1, hdss]
  have bdss : dss ≤ Cout * ρ := by
    linarith only [h1, hpss]
  have bptt : ptt ≤ Cmaj * (Cfs * H * (Cout * ρ + Cexp * ρ)) :=
    le_trans h3 (mul_le_mul_of_nonneg_left bpts hCmaj)
  have hCoutρ : 0 ≤ Cout * ρ := mul_nonneg hCout hρ
  have hCexpρ : 0 ≤ Cexp * ρ := mul_nonneg hCexp hρ
  have hAterm : 0 ≤ Cfs * H * (Cout * ρ + Cexp * ρ) :=
    mul_nonneg hA (by linarith only [hCoutρ, hCexpρ])
  have hCmajA : 0 ≤ Cmaj * (Cfs * H * (Cout * ρ + Cexp * ρ)) :=
    le_trans hptt bptt
  have hmax1 :
      max pss pts ≤
        Cout * ρ + Cfs * H * (Cout * ρ + Cexp * ρ) +
          Cmaj * (Cfs * H * (Cout * ρ + Cexp * ρ)) := by
    apply max_le
    · linarith only [bpss, hAterm, hCmajA]
    · linarith only [bpts, hCoutρ, hCmajA]
  have bptt' :
      ptt ≤
        Cout * ρ + Cfs * H * (Cout * ρ + Cexp * ρ) +
          Cmaj * (Cfs * H * (Cout * ρ + Cexp * ρ)) := by
    linarith only [bptt, hCoutρ, hAterm]
  have hmax2 :
      max (max pss pts) ptt ≤
        Cout * ρ + Cfs * H * (Cout * ρ + Cexp * ρ) +
          Cmaj * (Cfs * H * (Cout * ρ + Cexp * ρ)) :=
    max_le hmax1 bptt'
  calc
    max (max pss pts) ptt + dss + dt
        ≤ (Cout * ρ + Cfs * H * (Cout * ρ + Cexp * ρ) +
              Cmaj * (Cfs * H * (Cout * ρ + Cexp * ρ))) + Cout * ρ +
            Cfs * H * (Cout * ρ + Cexp * ρ) := by
          linarith only [hmax2, bdss, bdt]
    _ = (2 * Cout + (2 + Cmaj) * Cfs * H * (Cout + Cexp)) * ρ := by
          ring

/-! ## §G The proposition inputs and the run assembly -/

/-- `p.initial.fixed.grid.scale`, exact type declared in
`HCPoly/Entry/Statements/InitialFixedGridScale.lean`;
applies `Entry.initial_fixed_grid_scale` directly. -/
theorem initial_provider_input
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1),
      ∀ (S : SelectionData) (_hS : S.Selects d γ),
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ηinit : ℝ, ηinit ∈ Set.Ioc (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ ε σ : ℝ, 0 < σ → σ ≤ ε → ε ≤ S.eps0 →
              ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                (Src : CoeffSpace d → ℝ),
                IsProbabilityMeasure P →
                IsStationaryLaw P →
                IsUnitRangeLaw P →
                CoarseEllipticityDagger P γ E Ψ K Src →
                ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                  ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                    ∀ B : ℝ, S.B0 ε σ ≤ B →
                      ∃ n₀ : ℤ,
                        (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀ ∧
                          n₀ ≤ (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ +
                            ⌈C * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                          profile P γ (1 : Mat d) jStar n₀ n₀ +
                              determinantDrift P γ (1 : Mat d) jStar n₀ ≤ ηinit ∧
                          BlockMatLoewnerLE
                            (blockScale (1 / 2)
                              (ofFullBlockMat
                                (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
                                  toFullBlockMat (blockSwap d))))
                            (adaptedMean P (1 : Mat d) n₀) ∧
                          BlockMatLoewnerLE (adaptedMean P (1 : Mat d) n₀) (blockScale 2 E) ∧
                          projectiveDistance (1 : Mat d)
                              (explicitCanonicalMetric (adaptedMean P (1 : Mat d) n₀)) ≤
                            Cgeom * Real.log (2 + 4 * aspectRatio E)  :=
  Entry.initial_fixed_grid_scale d hd

/-- The output tuple of the run (`p.global.selection`), as a predicate, so `global_run` and
`global_selection` share one interface. -/
@[expose]
def SelectedOutput {d : ℕ} (P : Measure (CoeffSpace d)) (γ ε σ Cprof C : ℝ) (E : BlockMat d)
    (H jStar : ℕ) (B : ℝ) : Prop :=
  ∃ (F : BlockMat d) (s t : ℤ),
    IsSymmetricBlockMat F ∧
      Book.Ch02.BlockPosDef F ∧
      s < t ∧
      t = s + (H : ℤ) ∧
      (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s ∧
      t ≤ (jStar : ℤ) + ⌈(B + C) * Real.logb 3 (2 + aspectRatio E)⌉ ∧
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
        HighContrast.centeredCube d (2 * (jStar : ℤ)) ∧
      BlockMatLoewnerLE (blockScale (1 - Real.sqrt ε * σ) F)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s) ∧
      BlockMatLoewnerLE (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
        (blockScale (1 + Real.sqrt ε * σ) F) ∧
      (d : ℝ)⁻¹ * detIncrement P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t < σ ∧
      max
          (max (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s s)
            (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s t))
          (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t t) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t ≤
        Cprof * σ ^ ((1 - γ) / 8) ∧
      (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^ ((1 : ℝ) / 2) ≤ (2 + aspectRatio E) ^ C

end

end HCPolySupport.HighContrast.Multiscale
