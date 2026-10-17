/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.LambdaDischarge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.CgEllipLowerConstant

/-!
# SealPackaging

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The annular decomposition packaged at ONE slot

`LambdaDischarge.exists_clauseOne_final_one` is the clause-(i) endpoint with a
single mathematical slot left, `hpref` (the Step-1 leg).  This module
*packages* it: one theorem whose conclusion is the target shape -- one
constant, both clauses conjoined inside one `∀ᵐ`, on the printed ranges --
carrying `hpref` as its one hypothesis.

## What packaging costs

1. **The two clauses share one `∀ᵐ`.**  The chain delivers clause (i) as an
   `∀ᵐ` statement and clause (ii) as a *consumer* of that display at a fixed
   `ε`.  A naïve `∀ ε, ∀ᵐ ω` → `∀ᵐ ω, ∀ ε` swap is false in general
   (uncountably many `ε`), so `clauseTwo_pointwise_of_display` below repeats
   the proved clause-(ii) route **pointwise at a single sample**: every
   ingredient of that route
   (`goodEventBase_subset_annularEvent`,
   `ClauseTwo.clauseOneDisplayRhs_le_of_goodEventBase`,
   `ClauseTwo.indicator_observableSup_le_of_sqSup`,
   `ClauseTwo.sqrt_four_mul_sq`) is already sample-wise, so the null set comes
   only from the `ε`-free clause-(i) display and the `ε`-quantifier goes
   *inside* it.
2. **One constant for both clauses and both regime gates.**  The endpoint
   produces the clause-(i) display at `C_out = clauseOneOutConstant C₁ C_b 2
   C_shom`, clause (ii) at `2√C_out`, and gates the regime at `C_shom^10`; the
   carried `hpref` gates its own regime at `C_reg`.  The packaged constant is
   `C_fin = max C_out (max (2√C_out) (max (C_shom^10) C_reg))`; clause (i) rises
   to it by `ClauseTwo.clauseOneDisplayRhs_mono`, clause (ii) by monotonicity of
   `ε ↦ Cε`, and the regime hypothesis at the *larger* `C_fin` is *stronger*
   than either gate, so it implies both (`inv_anti₀`).
3. **Three ranges the target does not carry are discharged, not assumed**:
   `c⋆⁴ ≤ 6` from `Section3.Provider.Disorder.cstar_le_three_halves`
   ((3/2)⁴ = 81/16 ≤ 6); `1 ≤ |log γ|` from the standing
   `M.shellPrefix.gamma_le_quarter` and `gamma_pos`; and `0 ≤ C_cg` from
   `Support.cgEllipLowerConstant_pos`.  The `ε`-side range `sε ≤ 1` needed by the
   event containment is `s ≤ 1/4`, `ε ≤ 1/2`.
4. **Dimension.**  The endpoint needs `2 ≤ d`; the target quantifies over all
   `d`.  For `d ≤ 1` the statement is vacuous, because `ABKModel d` bundles
   `M.shellPrefix.dimension : 2 ≤ d` -- the same split the Section 3
   asymptotics anchor uses.  The whole split stays *inside* this theorem:
   `hpref` is itself carried under `2 ≤ d`, so a producer that needs the
   dimension (every producer on these carriers does) discharges the hypothesis
   directly and the low-dimensional branch never asks for it.

## Why `hpref` is carried *gated*

The Step-1 leg is a statement about the manuscript's own regime: it is claimed
for `s ∈ [8γ, 1/4]`, under a smallness gate on `γ`, on `𝒢₀ ∩ 𝒢₁`, for `L ≥ m`.
Carrying it range-free would be carrying a *stronger* proposition than the
manuscript asserts -- an obligation that may well be false as stated and could
then never be discharged.  So the hypothesis below quantifies its own regime
constant `C_reg` and takes the two printed range clauses; every one of those
gates is available at the point of use, so nothing is lost, and a range-free
`hpref` (if one is ever proved) discharges this one by dropping the gates.
Note the two facts `c⋆⁴ ≤ 6` and `1 ≤ |log γ|` are *not* gates of `hpref`: they
are standing consequences of `c⋆ ≤ 3/2` and `γ ≤ 1/4`, discharged in Part A.

## The frozen event at `y = 0`

Clause (ii) is stated on the frozen `goodEventAt M C_cg m 0 s ε`, which is by
definition `Cutoff.translateCutoffSample 0 ⁻¹' Support.goodEventBase …`; the
proved `GoodEvents.Api.goodEventAt_eq_preimage` and
`ClauseTwo.goodEventBase_eq_translateZero_preimage` identify it with
`Support.goodEventBase M C_cg m s ε`, which is the event the chain carries.
Only the frozen *definition* module `Frozen.Section4.GoodEvents` enters
(through the proved `Provider.GoodEvents.Api`, exactly as
`Proportion.ProportionFinal` does); no frozen *theorem* module is imported.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the three discharged ranges -/

/-- `1 ≤ |log γ|` for `0 < γ ≤ 1/4`: the standing scale bound
`M.shellPrefix.gamma_le_quarter` is stronger than the `1/3` the logarithm
needs. -/
private theorem one_le_abs_log_of_le_quarter {g : ℝ} (hg0 : 0 < g)
    (hg4 : g ≤ 1 / 4) : 1 ≤ |Real.log g| := by
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
  have hg3 : g ≤ 1 / 3 := by linarith only [hg4]
  have hmono : Real.log g ≤ Real.log (1 / 3 : ℝ) := Real.log_le_log hg0 hg3
  have h13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have hle : Real.log g ≤ -1 := by
    rw [h13] at hmono
    linarith only [hmono, hlog3]
  rw [abs_of_nonpos (by linarith only [hle])]
  linarith only [hle]

/-- `c⋆⁴ ≤ 6` from the proved `c⋆ ≤ 3/2`: `(3/2)⁴ = 81/16 ≤ 6`. -/
private theorem pow_four_le_six_of_le_three_halves {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ 3 / 2) : c ^ 4 ≤ 6 := by
  have h := pow_le_pow_left₀ hc0 hc 4
  have hval : (3 / 2 : ℝ) ^ 4 = 81 / 16 := by norm_num
  rw [hval] at h
  linarith only [h]

/-- `sε ≤ 1` on the printed ranges `s ≤ 1/4`, `ε ≤ 1/2`. -/
private theorem mul_le_one_of_quarter_of_half {s ep : ℝ} (hep0 : 0 < ep)
    (hs4 : s ≤ 1 / 4) (hep : ep ≤ 1 / 2) : s * ep ≤ 1 := by
  have h1 : s * ep ≤ 1 / 4 * ep := mul_le_mul_of_nonneg_right hs4 hep0.le
  have h2 : (1 / 4 : ℝ) * ep ≤ 1 / 4 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hep (by norm_num)
  linarith only [h1, h2]

/-! ## Part B -- clause (ii) at a single sample -/

/-- **The proved clause-(ii) route, pointwise.**

The clause-(ii) route with the `∀ᵐ` peeled off both sides:
every step of it is sample-wise, so a *single* sample satisfying the `ε`-free
clause-(i) display satisfies the clause-(ii) bound for **every** admissible `ε`.
That is what lets the target's `∀ ε` sit inside its `∀ᵐ`. -/
private theorem clauseTwo_pointwise_of_display (M : ABKModel d) (Ccg : ℝ)
    (m : ℤ) (s : {s : ℝ // 0 < s}) {ep C : ℝ} (hC0 : 0 ≤ C)
    (hep : ep ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hsep : (s : ℝ) * ep ≤ 1)
    (hsmall : M.gamma * |Real.log M.gamma| ^ 2
      ≤ (s : ℝ) ^ (3 / 2 : ℝ) * Disorder.cstar M ^ 2 * ep)
    {omega : Cutoff.CutoffSample d}
    (hom : Set.indicator (Support.eventG0 M Ccg m ∩
        Support.eventG1 M m (s : ℝ)
          (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
        (Support.fluxCorrectedErrorObservableSqSup M m s) omega
      ≤ clauseOneDisplayRhs M m s C omega) :
    Set.indicator (Support.goodEventBase M Ccg m s ep)
        (Support.fluxCorrectedErrorObservableSup M m s) omega
      ≤ ENNReal.ofReal (2 * Real.sqrt C * ep) := by
  classical
  by_cases hmem : omega ∈ Support.goodEventBase M Ccg m s ep
  · have hsub : Set.indicator (Support.goodEventBase M Ccg m s ep)
        (Support.fluxCorrectedErrorObservableSqSup M m s) omega
        ≤ Set.indicator (Support.eventG0 M Ccg m ∩
            Support.eventG1 M m (s : ℝ)
              (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
            (Support.fluxCorrectedErrorObservableSqSup M m s) omega :=
      Set.indicator_le_indicator_of_subset
        (goodEventBase_subset_annularEvent M Ccg m s hep.1.le hsep)
        (fun _a => (zero_le : (0 : ℝ≥0∞) ≤ _)) omega
    have hstep : Set.indicator (Support.goodEventBase M Ccg m s ep)
        (Support.fluxCorrectedErrorObservableSqSup M m s) omega
        ≤ ENNReal.ofReal (4 * C * ep ^ 2) :=
      le_trans (le_trans hsub hom)
        (clauseOneDisplayRhs_le_of_goodEventBase M Ccg m s hC0 hep.1.le hsmall hmem)
    have hB0 : (0 : ℝ) ≤ 4 * C * ep ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hC0) (sq_nonneg _)
    have hfin := indicator_observableSup_le_of_sqSup M m s hB0 hstep
    rwa [sqrt_four_mul_sq hC0 hep.1.le] at hfin
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le

/-! ## Part C -- the packaged statement -/

/-- **The annular decomposition, packaged at ONE slot.**

The single hypothesis is `hpref` -- the Step-1 leg, at one constant `C₁ > 0`
uniform in `(M, m, s, ω, L)`, at the coarse-ellipticity constant the target
itself names, under `2 ≤ d`, and gated exactly as the manuscript gates it: its
own regime constant `C_reg`, the printed ranges `s ≤ 1/4` and `8γ ≤ s`, the
event `𝒢₀ ∩ 𝒢₁`, and `L ≥ m`.  It is an explicitly documented conditional A
obligation, not a source premise.  The three further facts the endpoint carries
(`c⋆⁴ ≤ 6`, `1 ≤ |log γ|`, `0 ≤ C_cg`) are **discharged** here from standing
facts, and nothing else is assumed.

Disclosure: a proved local `Provider` helper. -/
theorem annular_decomposition_of_hpref
    (d : ℕ)
    (hpref : 2 ≤ d → ∃ C₁ Creg : ℝ, 0 < C₁ ∧ 0 < Creg ∧
      ∀ M : ABKModel d, M.gamma ≤ Creg⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ (m : ℤ) (s : {s : ℝ // 0 < s}),
          (s : ℝ) ≤ 1 / 4 → 8 * M.gamma ≤ (s : ℝ) →
        ∀ omega ∈ Support.eventG0 M (Support.cgEllipLowerConstant d) m ∩
            Support.eventG1 M m (s : ℝ)
              (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹),
          ∀ L : ℤ, m ≤ L →
            IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega)
              (annularResponseMax M L m omega) C₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ s : ℝ, s ∈ Set.Icc (8 * M.gamma) (1 / 4) → ∀ hs : 0 < s, ∀ m : ℤ,
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            (Set.indicator
                (Algsuperdiff.Section4.Support.eventG0 M
                    (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) m ∩
                  Algsuperdiff.Section4.Support.eventG1 M m s
                    (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
                (fun omega' =>
                  Algsuperdiff.Section4.Support.fluxCorrectedErrorObservableSqSup M m
                    ⟨s, hs⟩ omega')
                omega ≤
              ENNReal.ofReal (C * s) *
                  (∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
                    ENNReal.ofReal
                        (Real.rpow (3 : ℝ) (-s * ((m - n.1 : ℤ) : ℝ))) *
                      ⨆ v : ↥(Algsuperdiff.Section4.Support.latticeAnnulusSet d n.1 j.1
                          (j.1 - 1)),
                        ENNReal.ofReal
                          (Algsuperdiff.Section4.Support.annularErrorObservable M n.1
                              ⟨s, hs⟩
                              (Cutoff.translateCutoffSample
                                (Algsuperdiff.Section4.Support.triadicLatticePoint n.1 v.1)
                                omega) ^ 2)) +
                ENNReal.ofReal
                  (C * (s⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)) *
                    M.gamma ^ (2 : ℕ) * |Real.log M.gamma| ^ (4 : ℕ)) +
                ENNReal.ofReal (C * (s⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) *
                  (∑' k : {k : ℤ // m ≤ k},
                    ENNReal.ofReal
                      (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
                        Algsuperdiff.Section4.Support.shellW1InfGradNorm m
                          (omega.1 k.1))) ^ (2 : ℕ) +
                ENNReal.ofReal (C * (s⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) *
                  (∑' n : {n : ℤ // n ≤ m},
                    ENNReal.ofReal
                        (Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
                      ∑ k ∈ Finset.Icc (n.1 - 1) m,
                        (ENNReal.ofReal
                              (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                            ⨆ v : ↥(Algsuperdiff.Section4.Support.latticeCubeSet d k m),
                              ENNReal.ofReal
                                (Algsuperdiff.Section4.Support.shellW2InfNormAt
                                  (Algsuperdiff.Section4.Support.triadicLatticePoint k v.1)
                                  k (omega.1 k))) ^ (2 : ℕ))) ∧
              ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 2) →
                M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                  Real.rpow s (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * ep →
                Set.indicator
                    (Algsuperdiff.Frozen.Section4.goodEventAt M
                      (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) m 0 ⟨s, hs⟩ ep)
                    (fun omega' =>
                      Algsuperdiff.Section4.Support.fluxCorrectedErrorObservableSup M m
                        ⟨s, hs⟩ omega')
                    omega ≤
                  ENNReal.ofReal (C * ep)
    := by
  by_cases hd : 2 ≤ d
  · have : NeZero d := ⟨by omega⟩
    obtain ⟨C₁, Creg, hC₁, hCreg, hpre⟩ := hpref hd
    obtain ⟨Cs, Cshom, hCs, hC6, hmain⟩ := exists_clauseOne_final_one d hd
    -- the λ-budget constant at the target's own coarse-ellipticity constant
    obtain ⟨Cl, hCldef⟩ : ∃ x : ℝ,
        x = annularLambdaConstant d (Support.cgEllipLowerConstant d) := ⟨_, rfl⟩
    have hCcg : (0 : ℝ) ≤ Support.cgEllipLowerConstant d :=
      (Support.cgEllipLowerConstant_pos d).le
    have hCl0 : (0 : ℝ) ≤ Cl := by
      rw [hCldef]
      exact annularLambdaConstant_nonneg d hCcg
    -- the endpoint's constant inequality, at equality
    obtain ⟨Cb, hCbdef⟩ : ∃ x : ℝ,
        x = Cs * (1 + 196 * Cl) ^ 2 * 4 * (1 + Cl)
            + 16 * Cs * (1 + 196 * Cl) ^ 2 * Cl * (1 + centeringConst d ^ 2)
            + 4 * Cs * (1 + 4 * Cl ^ 2) := ⟨_, rfl⟩
    have hCb0 : 0 < Cb := by
      have hp1 : (0 : ℝ) < 1 + 196 * Cl := by linarith only [hCl0]
      have hp2 : (0 : ℝ) < 1 + Cl := by linarith only [hCl0]
      have ht1 : (0 : ℝ) < Cs * (1 + 196 * Cl) ^ 2 * 4 * (1 + Cl) :=
        mul_pos (mul_pos (mul_pos hCs (pow_pos hp1 2)) (by norm_num)) hp2
      have ht2 : (0 : ℝ) ≤ 16 * Cs * (1 + 196 * Cl) ^ 2 * Cl
          * (1 + centeringConst d ^ 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num) hCs.le) (sq_nonneg _)) hCl0) (by positivity)
      have ht3 : (0 : ℝ) ≤ 4 * Cs * (1 + 4 * Cl ^ 2) :=
        mul_nonneg (mul_nonneg (by norm_num) hCs.le) (by positivity)
      rw [hCbdef]
      linarith only [ht1, ht2, ht3]
    have hCout0 : 0 < clauseOneOutConstant C₁ Cb 2 Cshom :=
      clauseOneOutConstant_pos hC₁ hCb0 (by norm_num) hC6
    -- the single packaged constant: it dominates the clause-(i) output constant,
    -- the clause-(ii) square root, and the endpoint's regime gate
    obtain ⟨Cfin, hCfindef⟩ : ∃ x : ℝ,
        x = max (clauseOneOutConstant C₁ Cb 2 Cshom)
          (max (2 * Real.sqrt (clauseOneOutConstant C₁ Cb 2 Cshom))
            (max (Cshom ^ (10 : ℕ)) Creg)) := ⟨_, rfl⟩
    have hCoutle : clauseOneOutConstant C₁ Cb 2 Cshom ≤ Cfin := by
      rw [hCfindef]; exact le_max_left _ _
    have hCsqle : 2 * Real.sqrt (clauseOneOutConstant C₁ Cb 2 Cshom) ≤ Cfin := by
      rw [hCfindef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hCshomle : Cshom ^ (10 : ℕ) ≤ Cfin := by
      rw [hCfindef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hCregle : Creg ≤ Cfin := by
      rw [hCfindef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    refine ⟨Cfin, lt_of_lt_of_le hCout0 hCoutle, ?_⟩
    intro M hreg s hsmem hs m
    have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
    have hcstar4 : Disorder.cstar M ^ 4 ≤ 6 :=
      pow_four_le_six_of_le_three_halves hcs0.le
        (Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M)
    have hlog : 1 ≤ |Real.log M.gamma| :=
      one_le_abs_log_of_le_quarter M.shellPrefix.gamma_pos
        M.shellPrefix.gamma_le_quarter
    -- the regime at the endpoint's gate: `C_fin ≥ C_shom^10` makes the target's
    -- hypothesis the stronger one
    have hregShom : M.gamma ≤ (Cshom ^ (10 : ℕ))⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
      refine hreg.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hcs0.le 10))
      exact inv_anti₀ (pow_pos (by linarith only [hC6]) 10) hCshomle
    have hdisp := hmain M hregShom (Support.cgEllipLowerConstant d) hCcg m ⟨s, hs⟩
      hsmem.2 hsmem.1 hcstar4 hlog C₁ Cb hC₁ hCb0
      (by rw [hCbdef, hCldef])
      (hpre M (hreg.trans (mul_le_mul_of_nonneg_right
        (inv_anti₀ hCreg hCregle) (pow_nonneg hcs0.le 10))) m ⟨s, hs⟩
        hsmem.2 hsmem.1)
    filter_upwards [hdisp] with omega hom
    have homD : Set.indicator (Support.eventG0 M (Support.cgEllipLowerConstant d) m ∩
          Support.eventG1 M m s
            (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
          (Support.fluxCorrectedErrorObservableSqSup M m ⟨s, hs⟩) omega
        ≤ clauseOneDisplayRhs M m ⟨s, hs⟩
            (clauseOneOutConstant C₁ Cb 2 Cshom) omega := hom
    refine ⟨le_trans homD (clauseOneDisplayRhs_mono M m ⟨s, hs⟩ omega hCoutle), ?_⟩
    intro ep hep hsmall
    have hev := (Algsuperdiff.Section4.Provider.GoodEvents.goodEventAt_eq_preimage M
        (Support.cgEllipLowerConstant d) m 0 ⟨s, hs⟩ ep).trans
      (goodEventBase_eq_translateZero_preimage M
        (Support.cgEllipLowerConstant d) m ⟨s, hs⟩ ep)
    rw [hev]
    refine le_trans (clauseTwo_pointwise_of_display M
      (Support.cgEllipLowerConstant d) m ⟨s, hs⟩ hCout0.le hep
      (mul_le_one_of_quarter_of_half hep.1 hsmem.2 hep.2) hsmall homD)
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hCsqle hep.1.le
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd⟩

end

end Algsuperdiff.Section4.Provider.Annular
