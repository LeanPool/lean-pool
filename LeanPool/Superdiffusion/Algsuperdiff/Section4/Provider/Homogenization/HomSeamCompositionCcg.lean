/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamSupClauseCcgFree
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamComposition

/-!
# HomSeamCompositionCcg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The composition target, at a MODEL-DEPENDENT clause constant

## What this file does

The composition of `HomSeamComposition` reduced the frozen root to ONE object, but at the lane's NUMERAL clause
constant `recutPinnedCcgFlux d p` — which the producing route cannot meet
(`CA ≍ |log γ|^{1-1/(4d)}`).  This file re-states the reduction at
a model-dependent constant `CcgF: ABKModel d → ℝ`, subject to exactly the two
things the lane actually needs of it:

```text
  C(p,d) ≤ ofReal (CcgF M)                             -- the duality-leg pin
  CcgF M · GEOM(M) ≤ C_bud · |log γ|                    -- the budget
```

The second is exactly the shape of the two-factor budget
`HomSeamBudgetArith.recut_geomBudget_le_absLog`
(`GEOM · (1 + (s·p')⁻¹)^{1/p'} ≤ 2|log γ|`), so a producer whose constant is
`≲ (1 + (s·p')⁻¹)^{1/p'}` — which is what the unconditional sup-form multiscale
clause of `HomSpineDepthBandInput` delivers at `x₀ = s·p'` — meets it.

The re-thread is a genuine widening: the pinned producer still drives the
composition (its constant is model-free, and `GEOM ≤ 2|log γ|` is available), so
it only enlarges the class of admissible producers.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. The provider at a model-dependent clause constant -/

/-- **THE FROZEN `generator_renormalization` BODY FROM A BUDGETED CLAUSE.**

The provider at the sup-form clause, with the numeral `Ccg` pin freed.  The hypothesis list is `{0 < cstar, 0 <
gamma0, 0 < Cgap, 0 ≤ Cbud}` plus the three properties of `CcgF` and the clause
supply — and NOTHING else.  `C_en⁰`, `C_top` and the geometric factor are still
closed terms pinned inside; `K_abs` is now the closed term `seamKabsAt d hd1
C_gap (CcgF M) (C_en⁰(M))`. -/
theorem generator_renormalization_provider_final_of_supClauseAt (d : ℕ) (cstar : ℝ)
    (hcstar : 0 < cstar) {gamma0 Cgap Cbud : ℝ} {CcgF : ABKModel d → ℝ}
    (hg0 : 0 < gamma0) (hCgap : 0 < Cgap) (hCbud : 0 ≤ Cbud)
    (hCcg0 : ∀ M : ABKModel d, 0 ≤ CcgF M)
    (hCcgDom : ∀ hd : 2 ≤ d, ∀ M : ABKModel d,
      cgDualBoundConstFlux d (recutExponent d (le_trans (by norm_num) hd)) ≤
        ENNReal.ofReal (CcgF M))
    (hbud : ∀ hd : 2 ≤ d, ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
      CcgF M * coarseGrainingGeomFactor
          ((recutExponent d (le_trans (by norm_num) hd)).exponent.toReal) (homS M / 4) ≤
        Cbud * |Real.log M.gamma|)
    (hclause : ∀ (hd : 2 ≤ d) (inst : NeZero d),
      @SeamMultiscaleSupClauseSupplyAt d inst (le_trans (by norm_num) hd) cstar gamma0
        CcgF) :
    GeneratorRenormalizationShape d cstar := by
  by_cases hd : 2 ≤ d
  · have inst : NeZero d := ⟨by omega⟩
    have hd1 : 1 ≤ d := le_trans (by norm_num) hd
    obtain ⟨g1, Ctop, hg1, hCtop, hsupply⟩ :=
      seamSupplyFluxAtSupGradBudget_of_supClauseAt d hd1 cstar hcstar hg0 (hclause hd inst)
    have hppos : (0 : ℝ) < (recutExponent d hd1).exponent.toReal := by
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      rw [recutExponent_toReal]; linarith only [hdR]
    have hgeom1 : ∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
        (1 : ℝ) ≤ coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal)
          (homS M / 4) := by
      intro M hlog
      have hs : 0 < homS M := homS_pos (by linarith only [hlog])
      exact one_le_coarseGrainingGeomFactor hppos (by linarith only [hs])
    have hU : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
    have hd2 : (0 : ℝ) ≤ 288 * (d : ℝ) ^ (2 : ℕ) := by
      have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
      linarith only [hsq]
    have ha : (0 : ℝ) ≤ seamCwCen0Slope d hd1 := seamCwCen0Slope_nonneg d hd1
    have hb : (0 : ℝ) ≤ recutCwHalfEnvelope d hd1 1 Cgap 0 :=
      recutCwHalfEnvelope_nonneg d hd1 zero_le_one hCgap le_rfl
    exact generator_renormalization_provider_of_supBundleBudget d hd cstar hcstar
      (CabsF := fun Creg => (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) *
        (Creg * 729 * seamCwCen0Slope d hd1 + recutCwHalfEnvelope d hd1 1 Cgap 0) * Cbud)
      (KabsF := fun Creg M => seamKabsAt d hd1 Cgap (CcgF M)
        (Creg * 729 *
          coarseGrainingGeomFactor ((recutExponent d hd1).exponent.toReal) (homS M / 4)))
      (lt_min hg1 (by norm_num)) hCgap.le
      (fun Creg hCreg => by
        have hA0 : (0 : ℝ) ≤ Creg * 729 * seamCwCen0Slope d hd1 :=
          mul_nonneg (by linarith only [hCreg]) ha
        exact mul_nonneg (mul_nonneg (by linarith only [hU, hd2])
          (by linarith only [hA0, hb])) hCbud)
      (fun Creg hCreg M hlog =>
        seamKabsAt_nonneg d hd1 (hCcg0 M) hCgap
          (mul_nonneg (by linarith only [hCreg])
            (by linarith only [hgeom1 M hlog])))
      (fun Creg hCreg M hlog =>
        seamKabsAt_le_budget d hd1 hCgap hCreg (hCcg0 M) (hgeom1 M hlog)
          (hbud hd M hlog))
      hCtop
      (fun Creg hCreg =>
        seamBundleOfRegularityHalfSupGradBudget_of_supplyAt d hd hCgap
          (fun M hlog =>
            mul_nonneg (by linarith only [hCreg]) (by linarith only [hgeom1 M hlog]))
          hCcg0 (hCcgDom hd) (hsupply Creg hCreg))
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma _m
    exact absurd M.shellPrefix.dimension hd

/-! ## 2. THE ONE REMAINING INPUT, at a budgeted constant -/

/-- **THE ONE REMAINING INPUT, RE-CUT.**

An a.e. producer of the sup-form multiscale clause at SOME positive `γ₀` and at
SOME model-dependent constant meeting the duality pin and the budget.  This
is the composition's one remaining input with the `Ccg` slot freed. -/
def SupClauseProducerAtBudgeted (d : ℕ) (cstar : ℝ) : Prop :=
  ∃ gamma0 : ℝ, 0 < gamma0 ∧
    ∀ (hd : 2 ≤ d) (inst : NeZero d), ∃ (CcgF : ABKModel d → ℝ) (Cbud : ℝ),
      0 ≤ Cbud ∧ (∀ M : ABKModel d, 0 ≤ CcgF M) ∧
      (∀ M : ABKModel d,
        cgDualBoundConstFlux d (recutExponent d (le_trans (by norm_num) hd)) ≤
          ENNReal.ofReal (CcgF M)) ∧
      (∀ M : ABKModel d, 4 ≤ |Real.log M.gamma| →
        CcgF M * coarseGrainingGeomFactor
            ((recutExponent d (le_trans (by norm_num) hd)).exponent.toReal)
            (homS M / 4) ≤
          Cbud * |Real.log M.gamma|) ∧
      @SeamMultiscaleSupClauseSupplyAt d inst (le_trans (by norm_num) hd) cstar gamma0
        CcgF

/-! ## 3. THE COMPOSITION -/

/-- **THE COMPOSITION, AT A BUDGETED CLAUSE CONSTANT.**

The frozen conclusion, at every dimension and every `cstar > 0`, from the
budgeted sup-form clause producer ALONE.  `C_gap` is pinned to the numeral `1`;
`C_en⁰`, `C_top` and the geometric factor are closed terms pinned inside;
`K_abs` is `seamKabsAt d hd1 1 (CcgF M) (C_en⁰(M))`. -/
theorem generatorRenormalizationShape_of_supClauseProducerAtBudgeted (d : ℕ)
    (cstar : ℝ) (hcstar : 0 < cstar) (h : SupClauseProducerAtBudgeted d cstar) :
    GeneratorRenormalizationShape d cstar := by
  obtain ⟨gamma0, hg0, hprod⟩ := h
  by_cases hd : 2 ≤ d
  · have inst : NeZero d := ⟨by omega⟩
    obtain ⟨CcgF, Cbud, hCbud, hCcg0, hCcgDom, hbud, hcl⟩ := hprod hd inst
    refine generator_renormalization_provider_final_of_supClauseAt d cstar hcstar
      hg0 one_pos hCbud hCcg0 (fun hd' M => ?_) (fun hd' M hlog => ?_)
      (fun hd' inst' => ?_)
    · exact hCcgDom M
    · exact hbud M hlog
    · exact hcl
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro M _hcs _hgamma _m
    exact absurd M.shellPrefix.dimension hd

end

end Algsuperdiff.Section4.Provider.Homogenization
