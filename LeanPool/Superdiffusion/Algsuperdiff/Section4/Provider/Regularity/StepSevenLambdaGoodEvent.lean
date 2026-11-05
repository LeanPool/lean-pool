/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaStability
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeBadSet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepOneParameters
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.GoodEventCaps
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorPrefactor

/-!
# StepSevenLambdaGoodEvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7b, clause (B): the good-event ellipticity caps at `s* = 1/16`

## The target

```text
  λ_{1/16,q}^{-1}(z+□_{k'}; 𝐚_{L,k'}) · 1_{𝒢(k',z; s/8, sδ^{1/2}/8)} ≤ C(d) σ_{k'}^{-1} ,
  Λ_{1/16,q}(z+□_{k'}; 𝐚_{L,k'}) · 1_{𝒢(k',z; s/8, sδ^{1/2}/8)}      ≤ C(d) σ_{k'} .
```

## The good-event derivation: clause (B) is unconditional

`ae_stepSevenLambdaCaps` below derives all four legs, a.e. on the §4.4 good
event itself, from the proved cap `ExcessDecay.ae_boundLambdasByEs`, whose
own source is the frozen theorem
`Algsuperdiff.Frozen.Section4.annular_decomposition` (clause (ii)).  Three
alignments make it work, and each is exact rather than approximate:

1. Taking `m:= k'`, `t:= ⟨s/8⟩` and `ep:= (s/8)δ^{1/2}` is a literal match — no
   `ε`-monotonicity step and no slot comparison is needed.
2. **The index.**  The cap proves at the good-event slot `s/8 = 1/32` and at `q
   = 2`.  The `q = 2` legs at `s*` come from index monotonicity
   (`Ch02.LambdaSq_antitone`, `Ch02.lambdaSq_mono`), which runs the right way:
   `1/32 < 1/16`, and a cap at a smaller index is stronger.

## The residual conditions, and why none of them is a new obligation

`ae_stepSevenLambdaCaps` carries exactly the proved cap's own binders: the
annular standing regime `γ ≤ C⁻¹c⋆^{10}`, the slot floor `8γ ≤ s/8`, the
`δ`-range `δ ∈ (0,1/2]` (which produces the cap's `ep ∈ (0,1/2]` through
`stepOneEp_mem_Ioc`), and the smallness `γ|log γ|² ≤ (s/8)^{3/2} c⋆² ·
(s/8)δ^{1/2}`.  These are the §4.4 parameter regime, present verbatim in every
proved cap of the development; nothing mathematical is supplied by the caller.

## References

* ABK26, `e.lambda.stability.applied`; `e.bound.Lambdas.by.Es.v2`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. Clause (B) as a named record -/

/-- **Clause (B)**: the good-event ellipticity caps at
the single index `s* = 1/16`, both `q ∈ {1, 2}`, against one comparator `sigma`
(`= σ_{k'}`) and one constant (`= C(d)`). -/
structure StepSevenLambdaCaps (Q : TriadicCube d) (a : CoeffFamily d)
    (sigma CB : ℝ) : Prop where
  /-- `λ_{s*,2}^{-1}(Q; a) ≤ · sigma⁻¹`. -/
  lambdaInv_two :
    (Ch02.lambdaSq Q stepSevenStabilityIndex (.finite 2) a)⁻¹ ≤ CB * sigma⁻¹
  /-- `Λ_{s*,2}(Q; a) ≤ · sigma`. -/
  Lambda_two :
    Ch02.LambdaSq Q stepSevenStabilityIndex (.finite 2) a ≤ CB * sigma
  /-- `λ_{s*,1}^{-1}(Q; a) ≤ · sigma⁻¹`. -/
  lambdaInv_one :
    (Ch02.lambdaSq Q stepSevenStabilityIndex (.finite 1) a)⁻¹ ≤ CB * sigma⁻¹
  /-- `Λ_{s*,1}(Q; a) ≤ · sigma`. -/
  Lambda_one :
    Ch02.LambdaSq Q stepSevenStabilityIndex (.finite 1) a ≤ CB * sigma

/-! ## 2. The index arithmetic of the re-specification -/

/-- **The ruled index is exactly twice the good-event slot**: `s*/2 = s/8`.  This
is what makes CoarseGraining's `q = 1 ← q = 2` bridge land on the cap without
loss. -/
theorem stepSevenStabilityIndex_div_two :
    stepSevenStabilityIndex / 2 = stepOneSEighth := by
  rw [stepSevenStabilityIndex_eq, stepOneSEighth_eq]; norm_num

/-- `s/8 < s*`: the good-event slot sits strictly below the ruled index, so index
monotonicity carries the `q = 2` cap upward for free. -/
theorem stepOneSEighth_lt_stepSevenStabilityIndex :
    stepOneSEighth < stepSevenStabilityIndex := by
  rw [stepSevenStabilityIndex_eq, stepOneSEighth_eq]; norm_num

/-! ## 3. The comparator algebra -/

/-- `sigma⁻¹ · x ≤ K → x ≤ K · sigma`. -/
private theorem le_mul_of_inv_mul_le {sigma x K : ℝ} (hsigma : 0 < sigma)
    (h : sigma⁻¹ * x ≤ K) : x ≤ K * sigma := by
  have hmul := mul_le_mul_of_nonneg_right h hsigma.le
  rwa [inv_mul_eq_div, div_mul_cancel₀ _ hsigma.ne'] at hmul

/-- `sigma · x ≤ K → x ≤ K · sigma⁻¹`. -/
private theorem le_mul_inv_of_mul_le {sigma x K : ℝ} (hsigma : 0 < sigma)
    (h : sigma * x ≤ K) : x ≤ K * sigma⁻¹ := by
  have hmul := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hsigma.le)
  rwa [mul_comm sigma, mul_assoc, mul_inv_cancel₀ hsigma.ne', mul_one] at hmul

/-! ## 4. Clause (B) from a `q = 2` ratio cap at the good-event slot -/

/-- **The deterministic core of the Unit-C derivation.**  A `q = 2` ratio cap
at the good-event slot `s/8 = s*/2` yields clause (B) at `s*` for BOTH `q`:

* `q = 2` by index monotonicity (`1/32 < 1/16`, and `λ^{-1}`, `Λ` are
  nonincreasing in the index);
* `q = 1` by CoarseGraining's `q = 1 ← q = 2` bridge at NO constant, which
  needs the `q = 2` datum at exactly half the index — which is exactly the
  slot. -/
theorem stepSevenLambdaCaps_of_ratio_cap [NeZero d] (Q : TriadicCube d)
    (a : CoeffFamily d) {sigma K : ℝ} (hsigma : 0 < sigma)
    (hup : sigma⁻¹ * Ch02.LambdaSq Q stepOneSEighth (.finite 2) a ≤ K)
    (hlo : sigma * (Ch02.lambdaSq Q stepOneSEighth (.finite 2) a)⁻¹ ≤ K) :
    StepSevenLambdaCaps Q a sigma K := by
  have hslot : (0 : ℝ) < stepOneSEighth := stepOneSEighth_pos
  have hstar : (0 : ℝ) < stepSevenStabilityIndex := stepSevenStabilityIndex_pos
  have hlt : stepOneSEighth < stepSevenStabilityIndex :=
    stepOneSEighth_lt_stepSevenStabilityIndex
  have hhalf : Ch02.LambdaSq Q (stepSevenStabilityIndex / 2) (.finite 2) a =
      Ch02.LambdaSq Q stepOneSEighth (.finite 2) a := by
    rw [stepSevenStabilityIndex_div_two]
  have hhalf' : Ch02.lambdaSq Q (stepSevenStabilityIndex / 2) (.finite 2) a =
      Ch02.lambdaSq Q stepOneSEighth (.finite 2) a := by
    rw [stepSevenStabilityIndex_div_two]
  -- the two `q = 2` legs at `s*`
  have hUpTwo : Ch02.LambdaSq Q stepSevenStabilityIndex (.finite 2) a ≤ K * sigma := by
    refine le_mul_of_inv_mul_le hsigma (le_trans ?_ hup)
    exact mul_le_mul_of_nonneg_left
      (Ch02.LambdaSq_antitone Q a hslot hlt (by norm_num))
      (inv_nonneg.mpr hsigma.le)
  have hLoTwo :
      (Ch02.lambdaSq Q stepSevenStabilityIndex (.finite 2) a)⁻¹ ≤ K * sigma⁻¹ := by
    refine le_mul_inv_of_mul_le hsigma (le_trans ?_ hlo)
    exact mul_le_mul_of_nonneg_left
      (lambdaSq_inv_le_of_index_le Q a hslot hlt (by norm_num)) hsigma.le
  -- the two `q = 1` legs at `s*`, through the bridge at half the index
  have hUpOne : Ch02.LambdaSq Q stepSevenStabilityIndex (.finite 1) a ≤ K * sigma := by
    have hcap : sigma⁻¹ *
        Ch02.LambdaSq Q (stepSevenStabilityIndex / 2) (.finite 2) a ≤ K := by
      rw [hhalf]; exact hup
    have h := ExcessDecay.LambdaS_le_of_ratio_cap Q a hstar hsigma hcap
    rwa [Ch02.LambdaS] at h
  have hLoOne :
      (Ch02.lambdaSq Q stepSevenStabilityIndex (.finite 1) a)⁻¹ ≤ K * sigma⁻¹ := by
    have hcap : sigma *
        (Ch02.lambdaSq Q (stepSevenStabilityIndex / 2) (.finite 2) a)⁻¹ ≤ K := by
      rw [hhalf']; exact hlo
    have h := ExcessDecay.lambdaS_inv_le_of_ratio_cap Q a hstar hsigma hcap
    rwa [Ch02.lambdaS] at h
  exact ⟨hLoTwo, hUpTwo, hLoOne, hUpOne⟩

/-- Almost surely, on the §4.4 Step-3/Step-7 good event
`𝒢(k, z; s/8, (s/8)δ^{1/2})` and for every `L ≥ k`, the coarse-grained
ellipticity constants of the flux-corrected field on `□_k` satisfy the
clause-(B) caps at the index `s* = 1/16` and both `q ∈ {1,2}`, against
`σ_k` and the pure dimensional constant `2d((C·(s/8)δ^{1/2})² + 1)`. -/
theorem ae_stepSevenLambdaCaps (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          8 * M.gamma ≤ stepOneSEighth →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ (k : ℤ) (z : Vec d),
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ stepThreeGoodEvent M delta k z →
                  ∀ L : ℤ, k ≤ L →
                    StepSevenLambdaCaps (originCube d k)
                      (Support.fluxCorrectedCoeffFamily M L k (originCube d k)
                        (Cutoff.translateCutoffSample z omega))
                      ((Annealed.sigmaBar M k : ℝ))
                      (2 * (d : ℝ) * ((C * stepOneEp delta) ^ 2 + 1)) := by
  obtain ⟨C, hCpos, hC⟩ := ExcessDecay.ae_boundLambdasByEs d
  refine ⟨C, hCpos, ?_⟩
  intro M hregime delta hdelta hfloor hsmall k z
  have hslot :
      ((⟨stepOneSEighth, stepOneSEighth_pos⟩ : {t : ℝ // 0 < t}) : ℝ) ∈
        Set.Icc (8 * M.gamma) (1 / 4 : ℝ) := by
    refine ⟨hfloor, ?_⟩
    change stepOneSEighth ≤ (1 : ℝ) / 4
    rw [stepOneSEighth_eq]; norm_num
  filter_upwards [hC M hregime ⟨stepOneSEighth, stepOneSEighth_pos⟩ hslot
    (stepOneEp delta) (stepOneEp_mem_Ioc hdelta) hsmall k z] with omega homega
  intro hmem L hL
  have hmax := homega hmem L hL
  rw [ExcessDecay.fluxCorrectedEllipticityRatioMax_def, max_le_iff] at hmax
  exact stepSevenLambdaCaps_of_ratio_cap _ _ (Annealed.sigmaBar M k).2 hmax.1 hmax.2

end

end Algsuperdiff.Section4.Provider.Regularity
