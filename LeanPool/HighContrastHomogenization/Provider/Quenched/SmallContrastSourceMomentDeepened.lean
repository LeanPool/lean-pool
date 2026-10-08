/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMoment

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSourceMomentDeepened

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Deepened source-scale moments: the corrected split

The crude uniform moments `𝔪_N(K)` of the normalized source scale are replaced
by their deepened values.  When the
normalization scale sits `Δ` levels above the growth witness, the moment
splits as

  `𝔼[(max 1 (S·3^{-(s_K+Δ)}))^N] ≤ 1 + 3^{-MΔ}·𝔪_{N+M}(K)`,

for every reserve order `M`: a scale-free unit floor plus a `K`-carrying
excess that decays absolutely in the depth `Δ`.  Downstream this is the
three-channel source model — the unit floor feeds the lag channel with a
`K`-free coefficient, the excess feeds the absolute channels whose
`K`-burn-in is paid once.  The proof is an event split: below the tail
event the deepened variable collapses to `1`; on the tail event the decayed
tail-moment estimate applies.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The deepening identity.**  Normalizing `Δ ≥ 0` levels deeper is the
same as rescaling the normalized variable and re-flooring at `1`. -/
theorem normalizedSourceScale_shift (S : CoeffSpace d → ℝ) (sK : ℤ)
    {Delta : ℤ} (hDelta : 0 ≤ Delta) (a : CoeffSpace d) :
    normalizedSourceScale S (sK + Delta) a =
      max 1 (normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) := by
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-Delta) := by positivity
  have hc1 : (3 : ℝ) ^ (-Delta) ≤ 1 := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      (by omega : -Delta ≤ 0)
    simpa using h
  rw [normalizedSourceScale, normalizedSourceScale]
  rw [max_mul_of_nonneg _ _ hc0, one_mul]
  rw [← max_assoc, max_eq_left hc1]
  congr 1
  rw [neg_add, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), ← mul_assoc]

/-- **The deepened moment.**  `Δ` levels above the growth witness, the
`N`-th moment of the normalized source scale is the unit floor plus a
`3^{-MΔ}`-decayed `growthBar` excess, for every reserve order `M`. -/
theorem lintegral_normalizedSourceScale_pow_deepened
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (N M : ℕ) (hNM : 1 ≤ N + M) {Delta : ℤ} (hDelta : 0 ≤ Delta) :
    ∫⁻ a, ENNReal.ofReal
        (normalizedSourceScale S (sK + Delta) a ^ (N : ℝ)) ∂P ≤
      ENNReal.ofReal
        (1 + (3 : ℝ) ^ (-((M : ℝ) * (Delta : ℝ))) *
          (1 + 2 * ((N + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
            growthBar K ^ IndependentSums.natTriangular (N + M))) := by
  classical
  have hbar2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hlog0 : 0 ≤ Real.log (growthBar K) :=
    Real.log_nonneg (by linarith only [hbar2])
  have hcrude0 : (0 : ℝ) ≤
      1 + 2 * ((N + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular (N + M) := by
    have hpow : (0 : ℝ) ≤
        growthBar K ^ IndependentSums.natTriangular (N + M) :=
      pow_nonneg (by linarith only [hbar2]) _
    positivity
  have hdec0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((M : ℝ) * (Delta : ℝ))) := by
    positivity
  have hmeasA : MeasurableSet
      {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a} := by
    refine measurableSet_lt measurable_const ?_
    exact Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  have h3D : (0 : ℝ) < (3 : ℝ) ^ Delta := by positivity
  -- split the integral at the tail event
  rw [← lintegral_add_compl
    (fun a => ENNReal.ofReal
      (normalizedSourceScale S (sK + Delta) a ^ (N : ℝ))) hmeasA]
  -- on the tail event: the decayed tail moment
  have htail : ∫⁻ a in {a | (3 : ℝ) ^ Delta <
        normalizedSourceScale S sK a},
      ENNReal.ofReal
        (normalizedSourceScale S (sK + Delta) a ^ (N : ℝ)) ∂P ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-((M : ℝ) * (Delta : ℝ)))) *
        ENNReal.ofReal
          (1 + 2 * ((N + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
            growthBar K ^ IndependentSums.natTriangular (N + M)) := by
    refine le_trans (lintegral_mono_ae ?_)
      (setLintegral_normalizedSourceScale_pow_le hdag hsK N M hNM hDelta)
    rw [ae_restrict_iff' hmeasA]
    refine _root_.Filter.Eventually.of_forall fun a ha => ?_
    have hgt : (1 : ℝ) < normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta) := by
      have h := Set.mem_ofPred_eq ▸ ha
      calc
        (1 : ℝ) = (3 : ℝ) ^ Delta * (3 : ℝ) ^ (-Delta) := by
          rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp
        _ < normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta) := by
          refine mul_lt_mul_of_pos_right h ?_
          positivity
    rw [normalizedSourceScale_shift S sK hDelta a, max_eq_right hgt.le]
  -- off the tail event: the deepened variable collapses to the unit floor
  have hfloor : ∫⁻ a in {a | (3 : ℝ) ^ Delta <
        normalizedSourceScale S sK a}ᶜ,
      ENNReal.ofReal
        (normalizedSourceScale S (sK + Delta) a ^ (N : ℝ)) ∂P ≤ 1 := by
    have hone : ∫⁻ a in {a | (3 : ℝ) ^ Delta <
          normalizedSourceScale S sK a}ᶜ,
        ENNReal.ofReal
          (normalizedSourceScale S (sK + Delta) a ^ (N : ℝ)) ∂P ≤
        ∫⁻ _ in {a | (3 : ℝ) ^ Delta <
          normalizedSourceScale S sK a}ᶜ, 1 ∂P := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' hmeasA.compl]
      refine _root_.Filter.Eventually.of_forall fun a ha => ?_
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at ha
      have hle : normalizedSourceScale S sK a ≤ (3 : ℝ) ^ Delta :=
        not_lt.mp ha
      have hcol : normalizedSourceScale S (sK + Delta) a = 1 := by
        rw [normalizedSourceScale_shift S sK hDelta a]
        refine max_eq_left ?_
        calc
          normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta) ≤
              (3 : ℝ) ^ Delta * (3 : ℝ) ^ (-Delta) := by
            refine mul_le_mul_of_nonneg_right hle ?_
            positivity
          _ = 1 := by
            rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
            simp
      rw [hcol, Real.one_rpow, ENNReal.ofReal_one]
    refine hone.trans ?_
    rw [setLIntegral_one]
    exact prob_le_one
  -- assemble
  have hsum := add_le_add htail hfloor
  refine hsum.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hdec0 hcrude0),
    ENNReal.ofReal_one, ENNReal.ofReal_mul hdec0]
  ring

/-- **The deepened first moment**, in Bochner form: the unit floor plus the
decayed excess, ready for the mean-envelope step. -/
theorem integral_normalizedSourceScale_deepened
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (M : ℕ) {Delta : ℤ} (hDelta : 0 ≤ Delta) :
    ∫ a, normalizedSourceScale S (sK + Delta) a ∂P ≤
      1 + (3 : ℝ) ^ (-((M : ℝ) * (Delta : ℝ))) *
        (1 + 2 * ((1 + M : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
          growthBar K ^ IndependentSums.natTriangular (1 + M)) := by
  have hmeas : Measurable (normalizedSourceScale S (sK + Delta)) :=
    Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  have h0 : ∀ a, 0 ≤ normalizedSourceScale S (sK + Delta) a := fun a =>
    le_trans zero_le_one (one_le_normalizedSourceScale S _ a)
  have hlint := lintegral_normalizedSourceScale_pow_deepened hdag hsK 1 M
    (by omega) hDelta
  have hone : ∀ a, normalizedSourceScale S (sK + Delta) a ^ ((1 : ℕ) : ℝ) =
      normalizedSourceScale S (sK + Delta) a := fun a => by
    norm_num
  rw [lintegral_congr fun a => congrArg ENNReal.ofReal (hone a)] at hlint
  rw [integral_eq_lintegral_of_nonneg_ae
    (_root_.Filter.Eventually.of_forall h0) hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal
    (by
      have hbar2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
      have hlog0 : 0 ≤ Real.log (growthBar K) :=
        Real.log_nonneg (by linarith only [hbar2])
      have hpow : (0 : ℝ) ≤
          growthBar K ^ IndependentSums.natTriangular (1 + M) :=
        pow_nonneg (by linarith only [hbar2]) _
      positivity) hlint

end

end HCPolySupport.HighContrast.Quenched
