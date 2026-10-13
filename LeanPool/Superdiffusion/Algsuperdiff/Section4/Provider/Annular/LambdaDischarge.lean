/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.LambdaBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.TransposeDischarge

/-!
# LambdaDischarge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `hlam` slot discharged, and the one-slot clause-(i) endpoint

ABK26, Section 4.1, `p.mathcalE.annular.decomp` Step 2.

`LambdaBudget.sigmaBar_mul_inv_unitCubeLambda_two_gamma_le_of_mem_eventG0` proves
the ugly chain's `λ`-budget outright, on `𝒢₀(m)` and at the gapped gauge
`s = 2γ`, at the explicit constant

```
C_l = annularLambdaConstant d C_cg = 8 (1 + 9^d) (1 + C_cg) .
```

This module feeds it into the endpoint.  `exists_clauseOne_final_one` is the
transposed clause-(i) endpoint with the `hlam` binder **gone** and `C_l` pinned
to that constant: its remaining mathematical input is exactly `hpref`, the
Step-1 leg.

## `N`-invariance

`hlam` is consumed at `ω` **and** at `Nω = −ω`.  The discharge respects that with
no extra work and introduces **no** sub-event: it consumes only

* membership in `𝒢₀(m)` itself, which is pointwise `N`-invariant
  (`mem_eventG0_negateCutoffSample_iff`), and
* deterministic triadic geometry plus the induction state, neither of which
  sees the sample at all.

So the same lemma applies verbatim at `Nω` via `hmemN`, and the transposed leg
below does exactly that.

## Why the endpoint is re-run rather than composed

The endpoint cannot be composed on top of its predecessor: the induction state
that discharges `hlam` is produced *inside* the predecessor's proof from a
constant `C₀` of an `∃`-package whose `C_shom` is opaque from outside.  The
proof below is therefore the same composition re-run with the slot filled in
place — a forced re-derivation, not new mathematics.  The display, the ranges,
the event, the `s`-scaling and `clauseOneOutConstant C₁ C_shom` are unchanged.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The clause-(i) endpoint at ONE remaining slot.**

The transposed clause-(i) endpoint with `hlam` discharged by
`LambdaBudget.sigmaBar_mul_inv_unitCubeLambda_two_gamma_le_of_mem_eventG0` at
`C_l = annularLambdaConstant d C_cg = 8(1+9^d)(1+C_cg)`, so that the remaining
inputs are exactly

* the printed ranges `s ≤ 1/4`, `8γ ≤ s`, `c⋆⁴ ≤ 6`, `1 ≤ |log γ|` and the
  standing regime `γ ≤ C_shom^{−10} c⋆^{10}`;
* the typing nondegeneracies `0 ≤ C_cg`, `0 < C₁`, `0 < C` and the constant
  inequality fixing `C`; **and**
* the single mathematical obligation `hpref`, the Step-1 leg.

Nothing else is assumed. -/
theorem exists_clauseOne_final_one (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ Cs Cshom : ℝ, 0 < Cs ∧ 6 ≤ Cshom ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (Cshom ^ (10 : ℕ))⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ (Ccg : ℝ), 0 ≤ Ccg →
        ∀ (m : ℤ) (s : {s : ℝ // 0 < s}),
          (s : ℝ) ≤ 1 / 4 → 8 * M.gamma ≤ (s : ℝ) → Disorder.cstar M ^ 4 ≤ 6 →
          1 ≤ |Real.log M.gamma| →
        ∀ C₁ C : ℝ,
          0 < C₁ → 0 < C →
          Cs * (1 + 196 * annularLambdaConstant d Ccg) ^ 2 * 4
                * (1 + annularLambdaConstant d Ccg)
              + 16 * Cs * (1 + 196 * annularLambdaConstant d Ccg) ^ 2
                  * annularLambdaConstant d Ccg * (1 + centeringConst d ^ 2)
              + 4 * Cs * (1 + 4 * annularLambdaConstant d Ccg ^ 2) ≤ C →
          (∀ omega ∈ Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
            ∀ L : ℤ, m ≤ L →
              IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega)
                (annularResponseMax M L m omega) C₁) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          Set.indicator (Support.eventG0 M Ccg m ∩
              Support.eventG1 M m (s : ℝ)
                (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
              (Support.fluxCorrectedErrorObservableSqSup M m s) omega
            ≤ ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom * (s : ℝ))
                * clauseOneTermOne M m s omega
              + ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom
                  * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
                  * M.gamma ^ 2 * |Real.log M.gamma| ^ 4)
              + ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom
                  * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
                * clauseOneTermThree M m omega
              + ENNReal.ofReal (clauseOneOutConstant C₁ C 2 Cshom
                  * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
                * clauseOneTermFour M m s omega := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, hCs, hugly⟩ := exists_uglyJEstimate_annulus_of_eventG1 d dimension
  obtain ⟨C₀, hC₀6, -, hstate⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d 0
  obtain ⟨Cshom, hC6, hC₀le, hshomGen⟩ := exists_shomSlot_ge d C₀
  refine ⟨Cs, Cshom, hCs, hC6, ?_⟩
  intro M hreg Ccg hCcg m s hs14 hsg hcstar4 hlog C₁ C hC₁ hC0 hCconst hpref
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs14]
  have hCl : (0 : ℝ) ≤ annularLambdaConstant d Ccg :=
    annularLambdaConstant_nonneg d hCcg
  have hregA : M.gamma ≤ (Cshom⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) := by
    rwa [inv_pow]
  have hshom := hshomGen M hregA m
  have hC₀0 : (0 : ℝ) < C₀ := lt_of_lt_of_le (by norm_num) hC₀6
  have hregC : M.gamma ≤ (C₀⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregA.trans ?_
    have hinv : Cshom⁻¹ ≤ C₀⁻¹ := inv_anti₀ hC₀0 hC₀le
    have h10 : (Cshom⁻¹) ^ (10 : ℕ) ≤ (C₀⁻¹) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (inv_nonneg.mpr (le_trans hC₀0.le hC₀le)) hinv 10
    exact mul_le_mul_of_nonneg_right h10 (pow_nonneg hcs0.le 10)
  obtain ⟨E, -, -, hSall⟩ := hstate M hregC
  have hsignlow : ∀ n : ℤ, n ≤ m - 1 →
      1 / 4 * ((Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹)
          * (3 : ℝ) ^ (M.gamma * (n : ℝ)))
        ≤ (Annealed.sigmaBar M (n - 2) : ℝ) := fun n hn =>
    sigmaBar_sub_two_lower_quarter_of_inductionState M (hSall m) (by omega)
  -- the `λ`-budget, from `𝒢₀` and the state
  have hlam : ∀ omega ∈ Support.eventG0 M Ccg m ∩
      Support.eventG1 M m (s : ℝ)
        (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
      ∀ (n : ℤ) (v : Fin d → ℤ), n ≤ m - 1 →
        v ∈ Support.latticeAnnulusSet d n m n →
        (Annealed.sigmaBar M (n - 2) : ℝ) *
            (unitCubeLambda (2 * M.gamma) (.finite 2)
              (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2)
                omega))⁻¹ ≤
          annularLambdaConstant d Ccg *
            (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
    intro omega hmem n v hn hv
    exact sigmaBar_mul_inv_unitCubeLambda_two_gamma_le_of_mem_eventG0 M hCcg
      (hSall m) hn (by omega) hmem.1 hv
  -- the `(J3)` symmetry: the good event is invariant under whole-sequence negation
  have hmemN : ∀ omega ∈ Support.eventG0 M Ccg m ∩
      Support.eventG1 M m (s : ℝ)
        (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
      Cutoff.negateCutoffSample omega ∈ Support.eventG0 M Ccg m ∩
        Support.eventG1 M m (s : ℝ)
          (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by
    intro omega hmem
    exact ⟨(mem_eventG0_negateCutoffSample_iff M Ccg m omega).2 hmem.1,
      (mem_eventG1_negateCutoffSample_iff M m (s : ℝ) _ omega).2 hmem.2⟩
  have hbound : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ Support.eventG0 M Ccg m ∩
          Support.eventG1 M m (s : ℝ)
            (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) →
        clauseOneTermOne M m s omega ≠ ⊤ → ∀ L : ℤ, m ≤ L →
        IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
          (annDouble m (fun j n =>
            (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
              * annularErrorLatticeMax M s omega j n))
          (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
          (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
            * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
          (s : ℝ) (Disorder.cstar M) M.gamma
          (clauseOneOutConstant C₁ C 2 Cshom) := by
    filter_upwards [annularErrorAtomMax_ae_le_annularErrorLatticeMax M s] with
      omega hae hmem hfin L hL
    have hpretN := hpref (Cutoff.negateCutoffSample omega) (hmemN omega hmem) L hL
    rw [jLegField_negateCutoffSample_funext M L m omega] at hpretN
    refine clauseOne_bound_final M L m s omega hs1 hsg hcstar4 hlog hmem.2
      (summable_annFam_error_of_clauseOneTermOne_ne_top M m s omega hfin)
      hC6 hshom hC₁.le hC0.le
      (fun j n => annularResponseMax_nonneg M L m (Cutoff.negateCutoffSample omega) j n)
      (hpref omega hmem L hL) hpretN ?_ ?_
    · -- the field leg
      intro j n hjm hnj
      refine isUglyJEstimate_mono_E2 hC0.le (Real.rpow_nonneg (by norm_num) _)
        (hae j n hnj) ?_
      exact hugly M m L m E omega (s : ℝ) (annularLambdaConstant d Ccg) C
        (hSall m) le_rfl hL s.2 hs14 hsg hmem.2 hCl (hlam omega hmem) hsignlow
        hCconst j n hjm hnj
    · -- the transposed leg: the field leg at the negated sample
      intro j n hjm hnj
      have hraw := hugly M m L m E (Cutoff.negateCutoffSample omega) (s : ℝ)
        (annularLambdaConstant d Ccg) C (hSall m) le_rfl hL s.2 hs14 hsg
        (hmemN omega hmem).2 hCl
        (hlam (Cutoff.negateCutoffSample omega) (hmemN omega hmem)) hsignlow
        hCconst j n hjm hnj
      rw [annularErrorAtomMax_negateCutoffSample,
        annularL2Block_negateCutoffSample, annularGradBlock_negateCutoffSample,
        gradTailSq_negateCutoffSample] at hraw
      exact isUglyJEstimate_mono_E2 hC0.le (Real.rpow_nonneg (by norm_num) _)
        (hae j n hnj) hraw
  have hdisplay := clauseOne_representative_display_dichotomy M m s
    (Support.eventG0 M Ccg m ∩
      Support.eventG1 M m (s : ℝ)
        (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (C := clauseOneOutConstant C₁ C 2 Cshom)
    (clauseOneOutConstant_pos hC₁ hC0 (by norm_num) hC6) hbound
  filter_upwards [hdisplay] with omega hom
  rwa [clauseOneDisplayRhs_eq] at hom

end

end Algsuperdiff.Section4.Provider.Annular
