/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.RunResidue

/-!
# High-contrast homogenization: Entry.Multiscale.Global.RunAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The run assembly

The assembly of `global_run` from `global_run_residue`
(`HCPoly.Entry.Multiscale.Global.RunResidue`). From the residue — the
`GlobalRunGapObligation` with its two run-independent constant choices left open — it makes
those choices and discharges the two `Selects` projections with the per-step case analysis
`run_step_any` (`HCPoly.Entry.Multiscale.Global.RunStepAny`), producing the global selection
run: for every `S` with `S.Selects d γ`, constants `ε`, `Csrc`, `Cprof`, `C` and the
`SelectedOutput` estimate for each coefficient law with the dagger ellipticity. This is the
type of Proposition `p.global.selection`, and through that proposition it is part of the
assembly of Theorem `t.polynomial.entry`.
-/

open HCPolySupport.HighContrast (CoeffSpace aspectRatio aspectRatio_nonneg)
open HCPolySupport.HighContrast (aspectRatio_nonneg)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section


/-! ## §4 The assembly -/

/-- `source_threshold_mono` with the sign case removed. -/
private theorem src_threshold_of_bundled (x y C C' : ℝ) (j : ℤ) (hy : 0 ≤ y) (hC' : 0 < C')
    (hCC : C' ≤ C) (hj0 : 0 ≤ j) (hj : ⌈y + C * x⌉ ≤ j) : ⌈C' * x⌉ ≤ j := by
  rcases le_or_gt 0 x with hx | hx
  · exact source_threshold_mono x y C C' j hx hy hCC hj
  · have hneg : C' * x < 0 := mul_neg_of_pos_of_neg hC' hx
    have hceil : ⌈C' * x⌉ ≤ 0 := Int.ceil_le.mpr (by simpa using hneg.le)
    omega

/-- **`global_run_of_gap` with the residue as an explicit binder.** The statement below the
binder `hrun` is the `global_run` conclusion verbatim. This layer performs the two constant
choices that do not depend on the run: `ε` from `comparison_choice` at the residue's
`CS`, and the source-threshold discharge at every consumer. The residue produces
`CS` and `Csrc` so that they can be maxima over the Skolem constants of `hS` and of the
source estimates, which the residue alone can name. -/
theorem global_run_of_gap_outer
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ)
    (hrun : ∃ CS : ℝ, 1 ≤ CS ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
          (∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
            1 / 2 * Real.log ((1 + Real.sqrt ε * σ) / (1 - Real.sqrt ε * σ)) +
                2 * CS * ((S.h : ℝ) + 2) * Real.log (1 + Real.sqrt ε * σ) ≤
              min (ε / 2) (CS * σ / 4)) →
            GlobalRunGapObligation d γ S ε Csrc) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ H : ℕ, max 4 S.h ≤ H →
          ∃ Cprof : ℝ, 0 < Cprof ∧
            ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
              ∃ C : ℝ, 0 < C ∧
                ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                  (Src : CoeffSpace d → ℝ),
                  IsProbabilityMeasure P →
                  IsStationaryLaw P →
                  IsUnitRangeLaw P →
                  CoarseEllipticityDagger P γ E Ψ K Src →
                  ∀ B : ℝ, S.B0 ε σ ≤ B →
                    ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                      ⌈C * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                          Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                        SelectedOutput P γ ε σ Cprof C E H jStar B := by
  have _ := hd
  have _ := hγ
  have _ := hS
  obtain ⟨CS, hCS, Csrc, hCsrc0, htail⟩ := hrun
  obtain ⟨ε, hε, hcmp⟩ := comparison_choice CS hCS S.h S.eps0 S.eps0_mem
  refine ⟨ε, hε, Csrc, hCsrc0, ?_⟩
  have hob := htail ε hε hcmp
  intro H hH
  obtain ⟨Cprof, hCprof, hrest⟩ := hob H hH
  refine ⟨Cprof, hCprof, ?_⟩
  intro σ hσ
  obtain ⟨C, hC0, hfin⟩ := hrest σ hσ
  refine ⟨C, hC0, ?_⟩
  intro P E Ψ K Src hP hst hur hce B hB jStar hjStar hthr
  refine hfin P E Ψ K Src hP hst hur hce B hB jStar hjStar hthr ?_
  intro C' hC'0 hC'le
  have hAR : 0 ≤ aspectRatio E := aspectRatio_nonneg E
  have hlogb : 0 ≤ Real.logb 3 (2 + aspectRatio E) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hAR])
  have hB1 : (1 : ℝ) ≤ B := le_trans (S.one_le_B0 ε σ hε hσ) hB
  have hy : 0 ≤ C * (B + 1) * Real.logb 3 (2 + aspectRatio E) := by
    have : 0 ≤ C * (B + 1) := mul_nonneg hC0.le (by linarith only [hB1])
    exact mul_nonneg this hlogb
  exact src_threshold_of_bundled (Real.logb 3 (2 * K))
    (C * (B + 1) * Real.logb 3 (2 + aspectRatio E)) Csrc C' (jStar : ℤ)
    hy hC'0 hC'le (Int.natCast_nonneg jStar) hthr

/-- **`global_run` with the two `Selects` projections as explicit binders.** Conclusion
byte-identical to `global_run`. Constant order:
`ε` from `comparison_choice` at the residue's `CS = max 1 C_S` (so both branches of
`min (ε/2) (Cσ/4)` hold at `δ = √ε σ` for every `σ ∈ (0,ε]`) → `Csrc` the maximum of the
source constants of `hS`, `initial_provider_input`, `fixed_geometry_one_grid_propagation_full`
and `successful_short_bridge` → `H` → `Cprof` from `run_output_profile` → `σ` →
`C := max` of the `weight_choice_ge_d`, `scales_arith`, `eccentricity_arith` and
`containment_arith` constants (the last instantiated at `d := 4d`).
Then `run_initial` + `run_initial_reserve` give `Φ_tilde 0`, `run_step_any` gives the step
alternative, `run_exists_stop` gives the stopping state, and `run_stop_output` extracts
`SelectedOutput`. `1 ≤ S.h` is `hh` together with `Multiscale.bigQ_pos`. -/
theorem global_run_of_gap
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ)
    (hh : 2 * bigQ d γ ≤ S.h)
    (hL : ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε → 1 ≤ S.L ε σ) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ H : ℕ, max 4 S.h ≤ H →
          ∃ Cprof : ℝ, 0 < Cprof ∧
            ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
              ∃ C : ℝ, 0 < C ∧
                ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                  (Src : CoeffSpace d → ℝ),
                  IsProbabilityMeasure P →
                  IsStationaryLaw P →
                  IsUnitRangeLaw P →
                  CoarseEllipticityDagger P γ E Ψ K Src →
                  ∀ B : ℝ, S.B0 ε σ ≤ B →
                    ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                      ⌈C * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                          Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                        SelectedOutput P γ ε σ Cprof C E H jStar B :=
  global_run_of_gap_outer d hd γ hγ S hS
    (global_run_residue d hd γ hγ S hS hh hL)

/-- **Run assembly**: with the constants of
`comparison_choice`/`weight_choice`/`scales_arith`/`eccentricity_arith`/`containment_arith` and
the entry generation of `initial_provider_input`, iterate the alternatives of `hS : S.Selects d γ`
(each application discharged by `source_threshold_mono` and the containment budget), apply
`exists_stop_of_potential` with the four decreases and the telescoping of the per-step
charges into the budget, and extract `SelectedOutput`. This is the statement of
`global_selection` with the constants already
quantified in the order given above; only `SelectedOutput` has to be unfolded. The two
binders of `global_run_of_gap` are discharged by `selects_two_bigQ_le_h` (conjunct C1) and
`selects_one_le_L` (conjunct C2a). -/
theorem global_run
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ H : ℕ, max 4 S.h ≤ H →
          ∃ Cprof : ℝ, 0 < Cprof ∧
            ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
              ∃ C : ℝ, 0 < C ∧
                ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                  (Src : CoeffSpace d → ℝ),
                  IsProbabilityMeasure P →
                  IsStationaryLaw P →
                  IsUnitRangeLaw P →
                  CoarseEllipticityDagger P γ E Ψ K Src →
                  ∀ B : ℝ, S.B0 ε σ ≤ B →
                    ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                      ⌈C * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                          Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                        SelectedOutput P γ ε σ Cprof C E H jStar B := by
  exact global_run_of_gap d hd γ _hγ S _hS (selects_two_bigQ_le_h d hd γ _hγ S _hS)
    (fun ε σ hε hσ => selects_one_le_L d hd γ _hγ S _hS ε σ hε hσ)

end

end HCPolySupport.HighContrast.Multiscale
