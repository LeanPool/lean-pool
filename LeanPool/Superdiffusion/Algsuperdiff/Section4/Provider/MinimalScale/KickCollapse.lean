/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickTails
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroEngine

/-!
# KickCollapse

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-1 collapse and `e.Xj.expectation.upinthere`

ABK26, §4.2, Step 1 of `l.minimal.scale.sep`.  After the two-leg split,
collapses the pair into a single variable

```
X_j := X_j^{(1)} + (C s^{−9/2} X_j^{(2)})^{1/4} ,
```

asserts `X_j ≤ 𝒪_{Γ₂}(C c⋆^{−1}s^{−5/2}√γ)` "by `e.powerofGammasigma`, `s ≥ 8γ`
and `γ ≤ C^{−1}c⋆⁵`" (the endpoint below uses the lemma's own stronger regime
`γ ≤ C^{−10}c⋆^{10}` instead), and reads off

```
E[X_j] ≤ C c⋆^{−1} s^{−5/2} √γ                              (e.Xj.expectation.upinthere).
```

Both are proved here.  The `min{a,b} ≤ a^{1/4}b^{3/4}` step is what motivates
the shape and is not needed as an input: what the collapse consumes is the
*fourth root of the `Γ_{1/2}` leg*, and the two facts that make it work are

* the collapse absorption `KickArith.exp_neg_eighth_le_sqrt`, which is where
  `s ≥ 8γ` and the regime enter: it says that the fourth root of the
  exponentially small amplitude is already below `C c⋆^{−1}√γ`, so the `Γ_{1/2}`
  leg contributes nothing to the printed exponent.

The `s^{−9/8}` produced by the fourth root of `s^{−9/2}` is below the printed
`s^{−5/2}` because `s ≤ 1`; this is the only place the collapse's own `s`-power is
used, and it is slack.

## `E[X_j]`, and why it is a corollary and not a new estimate

A `Γ₂` tail at scale `A` gives `E[X] ≤ gammaMomentConst 2 · A`
(`Algsuperdiff.Probability.integral_le_of_isBigO_gammaSigma`), so the printed
first-moment constant is the tail constant times a dimensional factor.  The
endpoint below therefore proves the tail at an intermediate constant and states
BOTH conclusions at the single larger constant `C`, which is exactly the
manuscript's convention.

## Main definitions and results

* `kickCollapsed` — the collapsed variable `X_j`, with `K` the printed
  coefficient `C s^{−9/2}` supplied by the caller.
* `measurable_kickCollapsed`, `kickCollapsed_nonneg`, `rDependent_kickCollapsed`
  — the engine's `hmeas` slot, positivity, and the `r`-dependence, the last of
  these free because `X_j` is a measurable function of `annularKick_j`.
* `exists_kickCollapse` — the endpoint: the `Γ₂` tail AND
  `e.Xj.expectation.upinthere`, uniformly in `j`.

## References

* ABK26, `l.minimal.scale.sep`, (the lemma's hypotheses), Step 1;
  `e.powerofGammasigma` (ff).
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion

noncomputable section

variable {d : ℕ}

/-! ## 1. Two elementary devices -/

/-- `√√x ≤ y` from `x ≤ y⁴`: the comparison that turns a fourth-power estimate
into an estimate on the nested square root, with no `rpow` in sight. -/
theorem sqrt_sqrt_le_of_le_pow_four {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 4) :
    Real.sqrt (Real.sqrt x) ≤ y := by
  have h1 : Real.sqrt x ≤ y ^ 2 := by
    have h2 : Real.sqrt x ≤ Real.sqrt ((y ^ 2) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      calc x ≤ y ^ 4 := h
        _ = (y ^ 2) ^ 2 := by ring
    rwa [Real.sqrt_sq (by positivity)] at h2
  have h3 : Real.sqrt (Real.sqrt x) ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq hy] at h3

/-- **`e.powerofGammasigma` at the fourth root.**  A `Γ_{1/2}` tail at scale `A`
for a nonnegative variable gives a `Γ₂` tail at scale `√√A` for `√√X`: the
proved power rule `isBigOWith_gammaSigma_rpow` applied twice at `p = 1/2`,
since `(1/2)/(1/2) = 1` and `1/(1/2) = 2`. -/
theorem isBigOWith_sqrt_sqrt {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hX0 : ∀ omega, 0 ≤ X omega)
    (hX : IsBigOWith mu (gammaSigma (1 / 2)) X A) :
    IsBigOWith mu (gammaSigma 2) (fun omega => Real.sqrt (Real.sqrt (X omega)))
      (Real.sqrt (Real.sqrt A)) := by
  have h1 := isBigOWith_gammaSigma_rpow (μ := mu) (p := 1 / 2) (by norm_num) hA hX0 hX
  rw [show (1 : ℝ) / 2 / (1 / 2) = 1 from by norm_num] at h1
  have hfun1 : (fun omega => X omega ^ ((1 : ℝ) / 2))
      = fun omega => Real.sqrt (X omega) :=
    funext fun omega => (Real.sqrt_eq_rpow (X omega)).symm
  have hAeq1 : A ^ ((1 : ℝ) / 2) = Real.sqrt A := (Real.sqrt_eq_rpow A).symm
  rw [hfun1, hAeq1] at h1
  have h2 := isBigOWith_gammaSigma_rpow (μ := mu) (p := 1 / 2) (by norm_num)
    (Real.sqrt_nonneg A) (fun omega => Real.sqrt_nonneg _) h1
  rw [show (1 : ℝ) / (1 / 2) = 2 from by norm_num] at h2
  have hfun2 : (fun omega => Real.sqrt (X omega) ^ ((1 : ℝ) / 2))
      = fun omega => Real.sqrt (Real.sqrt (X omega)) :=
    funext fun omega => (Real.sqrt_eq_rpow (Real.sqrt (X omega))).symm
  have hAeq2 : Real.sqrt A ^ ((1 : ℝ) / 2) = Real.sqrt (Real.sqrt A) :=
    (Real.sqrt_eq_rpow (Real.sqrt A)).symm
  rw [hfun2, hAeq2] at h2
  exact h2

/-! ## 2. The collapsed variable -/

/-- **The collapsed Step-1 variable** `X_j = X_j^{(1)} + (K·X_j^{(2)})^{1/4}`, with
the printed coefficient `K = C s^{−9/2}` supplied by the caller and the fourth
root written as a nested square root. -/
def kickCollapsed (M : ABKModel d) (s : {s : ℝ // 0 < s}) (lam K : ℝ) (j : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  kickLegLow M s lam j omega +
    Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega))

theorem kickCollapsed_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) {lam : ℝ}
    (hlam : 0 ≤ lam) (K : ℝ) (j : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ kickCollapsed M s lam K j omega := by
  have h1 : 0 ≤ kickLegLow M s lam j omega := kickLegLow_nonneg M s hlam j omega
  have h2 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (K * kickLegHigh M s lam j omega)) :=
    Real.sqrt_nonneg _
  rw [kickCollapsed]
  linarith only [h1, h2]

theorem measurable_kickCollapsed (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (lam K : ℝ) (j : ℤ) : Measurable (kickCollapsed M s lam K j) := by
  refine (measurable_kickLegLow M s lam j).add ?_
  exact Real.continuous_sqrt.measurable.comp
    (Real.continuous_sqrt.measurable.comp
      ((measurable_kickLegHigh M s lam j).const_mul K))

/-- **The collapsed family is `r`-dependent** whenever the inner-scale sum is:
`X_j` is a measurable function of `annularKick_j` alone. -/
theorem rDependent_kickCollapsed (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (lam K : ℝ) {r : ℕ}
    (h : Algsuperdiff.Probability.RDependent (Cutoff.cutoffSampleLaw M).toMeasure
      (fun j => annularKick M s j) r) :
    Algsuperdiff.Probability.RDependent (Cutoff.cutoffSampleLaw M).toMeasure
      (fun j => kickCollapsed M s lam K j) r :=
  h.comp (fun _ x => min x lam + Real.sqrt (Real.sqrt (K * (x - min x lam))))
    fun _ => (measurable_id.min measurable_const).add
      (Real.continuous_sqrt.measurable.comp
        (Real.continuous_sqrt.measurable.comp
          ((measurable_id.sub (measurable_id.min measurable_const)).const_mul K)))

/-! ## 3. The two numerical facts of the assembly -/

/-- `(1 + log 2)^{1/2} ≤ 2`: the two-term `Γ₂` triangle constant is at most `2`,
which is all the assembly needs from it. -/
theorem triangleConstTwo_le : (1 + Real.log 2) ^ ((2 : ℝ))⁻¹ ≤ 2 := by
  have hl := log_two_le_one
  have h0 : (0 : ℝ) ≤ 1 + Real.log 2 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith only [h]
  have heq : (1 + Real.log 2) ^ ((2 : ℝ))⁻¹ = Real.sqrt (1 + Real.log 2) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq]
  have h2 := Real.sqrt_le_sqrt (show 1 + Real.log 2 ≤ (4 : ℝ) from by linarith only [hl])
  rwa [h4] at h2

/-! ## 4. The endpoint -/

/-- **TH AND `e.Xj.expectation.upinthere`, UN.**

There is a dimensional constant `C` such that for every model in the regime
`γ ≤ C^{−10}c⋆^{10}` and every window parameter `s ∈ [8γ, 1/2]` there is a
threshold `lam` for which, **uniformly in the annulus index `j`**, the two legs
add up to the Step-1 inner sum and the collapsed variable

```
X_j = X_j^{(1)} + (C s^{−9/2} X_j^{(2)})^{1/4}
```

obeys `X_j ≤ 𝒪_{Γ₂}(C c⋆^{−1}s^{−5/2}√γ)` and `E[X_j] ≤ C c⋆^{−1}s^{−5/2}√γ`.

`s^{−5/2}` is `((√s)⁵)⁻¹` and `s^{−9/2}` is `((√s)⁹)⁻¹`, so no `rpow` appears.

**Hypotheses.**  Exactly the premises of `l.minimal.scale.sep` as printed: `γ ≤
C^{−10}c⋆^{10}` and `s ∈ [8γ, 1/2]`.  The positivity of `s` is the typing datum
of the observable's index and is implied by the window. -/
theorem exists_kickCollapse (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, 8 * M.gamma ≤ (s : ℝ) → (s : ℝ) ≤ 1 / 2 →
          ∃ lam : ℝ, 0 ≤ lam ∧
            (∀ (j : ℤ) (omega : Cutoff.CutoffSample d),
              kickLegLow M s lam j omega + kickLegHigh M s lam j omega
                = annularKick M s j omega) ∧
            (∀ j : ℤ,
              IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
                (kickCollapsed M s lam (C * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹) j)
                (C * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
                  Real.sqrt M.gamma)) ∧
            (∀ j : ℤ,
              ∫ omega, kickCollapsed M s lam (C * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹) j omega
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure
                ≤ C * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
                  Real.sqrt M.gamma) := by
  obtain ⟨C2, hC2, htails⟩ := exists_kickFamily_tails d
  have hG : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hQ40 : (0 : ℝ) ≤ (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 2 := sq_nonneg _
  have hMc1 : (1 : ℝ) ≤ 1 + 4 * C2 +
      256 * (1 + gammaMomentConst 2) * C2 * (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 2 := by
    have h1 : (0 : ℝ) ≤ 4 * C2 := by linarith only [hC2]
    have h2 : (0 : ℝ) ≤ 256 * (1 + gammaMomentConst 2) * C2 :=
      mul_nonneg (by linarith only [hG]) hC2.le
    have h3 : (0 : ℝ) ≤ 256 * (1 + gammaMomentConst 2) * C2 *
        (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 2 := mul_nonneg h2 hQ40
    linarith only [h1, h3]
  refine ⟨(1 + 4 * C2 + 256 * (1 + gammaMomentConst 2) * C2 *
      (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 2) +
    gammaMomentConst 2 * (1 + 4 * C2 + 256 * (1 + gammaMomentConst 2) * C2 *
      (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 2), ?_, ?_⟩
  · have h := mul_nonneg hG.le (by linarith only [hMc1] :
      (0 : ℝ) ≤ 1 + 4 * C2 + 256 * (1 + gammaMomentConst 2) * C2 *
        (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 2)
    linarith only [hMc1, h]
  intro M hreg s hs8 hs2
  set Q4 : ℝ := (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 2 with hQ4def
  set Mc : ℝ := 1 + 4 * C2 + 256 * (1 + gammaMomentConst 2) * C2 * Q4 with hMcdef
  set C : ℝ := Mc + gammaMomentConst 2 * Mc with hCdef
  -- Make the three constants opaque: every use below goes through the defining
  -- equations `hQ4def`/`hMcdef`/`hCdef`, so keeping the bodies as `let` values
  -- only forces `whnf` to re-expand a large arithmetic tree at every
  -- unification step.
  clear_value C Mc Q4
  -- the numerical facts about the constants
  have hMcpos : (0 : ℝ) < Mc := lt_of_lt_of_le zero_lt_one hMc1
  have hMcC : Mc ≤ C := by
    have h := mul_nonneg hG.le hMcpos.le
    rw [hCdef]
    linarith only [h]
  have hGMcC : gammaMomentConst 2 * Mc ≤ C := by
    rw [hCdef]
    linarith only [hMcpos]
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le hMcpos hMcC
  have h4C2 : 4 * C2 ≤ Mc := by
    have h3 : (0 : ℝ) ≤ 256 * (1 + gammaMomentConst 2) * C2 * Q4 :=
      mul_nonneg (mul_nonneg (by linarith only [hG]) hC2.le) hQ40
    rw [hMcdef]
    linarith only [h3]
  have hC2Mc : C2 ≤ Mc := by linarith only [h4C2, hC2]
  have hC2C : C2 ≤ C := hC2Mc.trans hMcC
  have habsMc : 256 * (1 + gammaMomentConst 2) * C2 * Q4 ≤ Mc := by
    have h1 : (0 : ℝ) ≤ 4 * C2 := by linarith only [hC2]
    rw [hMcdef]
    linarith only [h1]
  -- the standing quantities
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  have hsq1 : Real.sqrt (s : ℝ) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show (s : ℝ) ≤ 1 from by linarith only [hs2])
    rwa [Real.sqrt_one] at h
  have hgsq : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 hgam
  -- the regime at the tails constant
  have hregC2 : M.gamma ≤ C2⁻¹ ^ 10 * (Disorder.cstar M) ^ 10 := by
    have h1 : C⁻¹ ≤ C2⁻¹ := inv_anti₀ hC2 hC2C
    have h2 : C⁻¹ ^ 10 ≤ C2⁻¹ ^ 10 :=
      pow_le_pow_left₀ (le_of_lt (inv_pos.2 hCpos)) h1 10
    exact hreg.trans (mul_le_mul_of_nonneg_right h2 (pow_nonneg hcs.le 10))
  obtain ⟨lam, hlam0, hlow, hhigh⟩ := htails M hregC2 s hs8 hs2
  -- the common amplitude factor `F = c⋆^{−1}s^{−5/2}√γ`
  set F : ℝ := (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
    Real.sqrt M.gamma with hFdef
  have hF0 : (0 : ℝ) < F := by
    rw [hFdef]
    exact mul_pos (mul_pos (inv_pos.2 hcs) (inv_pos.2 (pow_pos hsq0 5))) hgsq
  have hCF : C * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
      Real.sqrt M.gamma = C * F := by
    rw [hFdef]; ring
  have hC2F : C2 * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
      Real.sqrt M.gamma = C2 * F := by
    rw [hFdef]; ring
  -- the fourth power of `F`
  have hs20 : (((Real.sqrt (s : ℝ)) ^ 5)⁻¹) ^ 4 = ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ := by
    rw [inv_pow, ← pow_mul]
  have hF4 : F ^ 4 = (Disorder.cstar M)⁻¹ ^ 4 * ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ *
      M.gamma ^ 2 := by
    have hg4 : Real.sqrt M.gamma ^ 4 = M.gamma ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul, Real.sq_sqrt hgam.le]
    rw [hFdef, mul_pow, mul_pow, hs20, hg4]
  -- the collapse coefficient
  set Kc : ℝ := C * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ with hKcdef
  have hKc0 : (0 : ℝ) < Kc := by
    rw [hKcdef]
    exact mul_pos hCpos (inv_pos.2 (pow_pos hsq0 9))
  -- the high-leg amplitude, and the fourth-power estimate that tames it
  set bb : ℝ := C2⁻¹ * (Disorder.cstar M) ^ 3 * M.gamma⁻¹ with hbbdef
  have hbb0 : (0 : ℝ) < bb := by
    rw [hbbdef]
    exact mul_pos (mul_pos (inv_pos.2 hC2) (pow_pos hcs 3)) (inv_pos.2 hgam)
  have hexp4 : Real.exp (-bb) ≤ Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2) := by
    have habs := exp_neg_eighth_le_sqrt hC2 hcs hgam hregC2
    rw [← hbbdef] at habs
    have h4 : Real.exp (-(bb / 8)) ^ 4
        ≤ (Real.sqrt (4 * C2 + 64 * C2⁻¹ ^ 8) *
            ((Disorder.cstar M)⁻¹ * Real.sqrt M.gamma)) ^ 4 :=
      pow_le_pow_left₀ (Real.exp_pos _).le habs 4
    have hL : Real.exp (-(bb / 8)) ^ 4 = Real.exp (-(bb / 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hR : (Real.sqrt (4 * C2 + 64 * C2⁻¹ ^ 8) *
          ((Disorder.cstar M)⁻¹ * Real.sqrt M.gamma)) ^ 4
        = Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2) := by
      have hQ : Real.sqrt (4 * C2 + 64 * C2⁻¹ ^ 8) ^ 4 = Q4 := by
        rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul,
          Real.sq_sqrt (by positivity), hQ4def]
      have hg4 : Real.sqrt M.gamma ^ 4 = M.gamma ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul, Real.sq_sqrt hgam.le]
      rw [mul_pow, mul_pow, hQ, hg4]
    rw [hL, hR] at h4
    refine le_trans (Real.exp_le_exp.2 ?_) h4
    linarith only [hbb0]
  have hs9 : ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ ≤ ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ := by
    refine inv_anti₀ (pow_pos hsq0 20) ?_
    exact pow_le_pow_of_le_one hsq0.le hsq1 (by norm_num)
  have hkey : Kc * (C2 * Real.exp (-bb)) ≤ (Mc / 4 * F) ^ 4 := by
    have hstep1 : Kc * (C2 * Real.exp (-bb))
        ≤ C * ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ *
          (C2 * (Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2))) := by
      have h1 : C2 * Real.exp (-bb)
          ≤ C2 * (Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp4 hC2.le
      have h2 : (0 : ℝ) ≤ C2 * (Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2)) :=
        mul_nonneg hC2.le (mul_nonneg hQ40 (by positivity))
      have h3 : Kc ≤ C * ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ := by
        rw [hKcdef]
        exact mul_le_mul_of_nonneg_left hs9 hCpos.le
      calc Kc * (C2 * Real.exp (-bb))
          ≤ Kc * (C2 * (Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2))) :=
            mul_le_mul_of_nonneg_left h1 hKc0.le
        _ ≤ C * ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ *
              (C2 * (Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2))) :=
            mul_le_mul_of_nonneg_right h3 h2
    have hconst : C * C2 * Q4 ≤ (Mc / 4) ^ 4 := by
      have hcube : Mc ≤ Mc ^ 3 := by
        have h1 : Mc * 1 ≤ Mc * Mc ^ 2 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hMc1) hMcpos.le
        calc Mc = Mc * 1 := by ring
          _ ≤ Mc * Mc ^ 2 := h1
          _ = Mc ^ 3 := by ring
      have hCval : C = (1 + gammaMomentConst 2) * Mc := by rw [hCdef]; ring
      have hstep : 256 * (C * C2 * Q4) ≤ Mc * Mc ^ 3 := by
        have h1 : 256 * (C * C2 * Q4)
            = Mc * (256 * (1 + gammaMomentConst 2) * C2 * Q4) := by
          rw [hCval]; ring
        have h2 : Mc * (256 * (1 + gammaMomentConst 2) * C2 * Q4) ≤ Mc * Mc :=
          mul_le_mul_of_nonneg_left habsMc hMcpos.le
        have h3 : Mc * Mc ≤ Mc * Mc ^ 3 := mul_le_mul_of_nonneg_left hcube hMcpos.le
        rw [h1]
        exact h2.trans h3
      have hval : (Mc / 4) ^ 4 = Mc * Mc ^ 3 / 256 := by ring
      rw [hval]
      linarith only [hstep]
    have hfac0 : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ ^ 4 *
        ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ * M.gamma ^ 2 := by
      have h1 : (0 : ℝ) < ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ := inv_pos.2 (pow_pos hsq0 20)
      exact mul_nonneg (mul_nonneg (by positivity) h1.le) (by positivity)
    refine hstep1.trans ?_
    have hRw : (Mc / 4 * F) ^ 4 = (Mc / 4) ^ 4 * ((Disorder.cstar M)⁻¹ ^ 4 *
        ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ * M.gamma ^ 2) := by
      rw [mul_pow, hF4]
    rw [hRw]
    have hLw : C * ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ *
        (C2 * (Q4 * ((Disorder.cstar M)⁻¹ ^ 4 * M.gamma ^ 2)))
        = (C * C2 * Q4) * ((Disorder.cstar M)⁻¹ ^ 4 *
          ((Real.sqrt (s : ℝ)) ^ 20)⁻¹ * M.gamma ^ 2) := by ring
    rw [hLw]
    exact mul_le_mul_of_nonneg_right hconst hfac0
  -- the per-index assembly
  have hmain : ∀ j : ℤ,
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (kickCollapsed M s lam Kc j) (Mc * F) := by
    intro j
    have hlowj := hlow j
    rw [hC2F] at hlowj
    have hhighj := hhigh j
    have hKmul : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 2))
        (fun omega => Kc * kickLegHigh M s lam j omega)
        (Kc * (C2 * Real.exp (-bb))) := by
      have h := IsBigOWith.const_mul (c := Kc) hKc0.le hhighj
      rw [hbbdef]
      exact h
    have hroot := isBigOWith_sqrt_sqrt
      (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
      (by exact mul_nonneg hKc0.le (mul_nonneg hC2.le (Real.exp_pos _).le))
      (fun omega => mul_nonneg hKc0.le (kickLegHigh_nonneg M s lam j omega)) hKmul
    have hroot' : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (fun omega => Real.sqrt (Real.sqrt (Kc * kickLegHigh M s lam j omega)))
        (Mc / 4 * F) :=
      hroot.mono_scale (sqrt_sqrt_le_of_le_pow_four
        (by
          have h1 : (0 : ℝ) < Mc / 4 := by linarith only [hMcpos]
          exact le_of_lt (mul_pos h1 hF0)) hkey)
    -- add the two `Γ₂` legs
    have hlowO : IsBigO
        (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (kickLegLow M s lam j) (C2 * F) := by
      exact Algsuperdiff.Probability.isBigO_of_isBigOWith_of_nonneg
        (fun omega => kickLegLow_nonneg M s hlam0 j omega) hlowj
    have hrootO : IsBigO
        (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (fun omega => Real.sqrt (Real.sqrt (Kc * kickLegHigh M s lam j omega)))
        (Mc / 4 * F) :=
      Algsuperdiff.Probability.isBigO_of_isBigOWith_of_nonneg
        (fun omega => Real.sqrt_nonneg _) hroot'
    have hsum := Algsuperdiff.Probability.isBigO_gammaSigma_add2'
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (by norm_num : (0 : ℝ) < 2)
      (mul_nonneg hC2.le hF0.le)
      (mul_nonneg (by linarith only [hMcpos] : (0 : ℝ) ≤ Mc / 4) hF0.le)
      hlowO hrootO
    have hsumW : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (kickCollapsed M s lam Kc j)
        ((1 + Real.log 2) ^ ((2 : ℝ))⁻¹ * (C2 * F + Mc / 4 * F)) := by
      refine Algsuperdiff.Probability.isBigOWith_of_isBigO_of_nonneg
        (fun omega => kickCollapsed_nonneg M s hlam0 Kc j omega) ?_
      exact hsum
    refine hsumW.mono_scale ?_
    have hT := triangleConstTwo_le
    have hpos : (0 : ℝ) ≤ C2 * F + Mc / 4 * F :=
      add_nonneg (mul_nonneg hC2.le hF0.le)
        (mul_nonneg (by linarith only [hMcpos]) hF0.le)
    have hstep1 : (1 + Real.log 2) ^ ((2 : ℝ))⁻¹ * (C2 * F + Mc / 4 * F)
        ≤ 2 * (C2 * F + Mc / 4 * F) := mul_le_mul_of_nonneg_right hT hpos
    have hstep2 : 2 * (C2 * F + Mc / 4 * F) ≤ Mc * F := by
      have h1 : 2 * C2 ≤ Mc / 2 := by linarith only [h4C2]
      have h2 : (2 * C2) * F ≤ (Mc / 2) * F := mul_le_mul_of_nonneg_right h1 hF0.le
      calc 2 * (C2 * F + Mc / 4 * F) = (2 * C2) * F + (Mc / 2) * F := by ring
        _ ≤ (Mc / 2) * F + (Mc / 2) * F := by linarith only [h2]
        _ = Mc * F := by ring
    exact hstep1.trans hstep2
  refine ⟨lam, hlam0, fun j omega => kickLegLow_add_kickLegHigh M s lam j omega, ?_, ?_⟩
  · intro j
    rw [hCF]
    exact (hmain j).mono_scale (mul_le_mul_of_nonneg_right hMcC hF0.le)
  · intro j
    have hO : IsBigO
        (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (kickCollapsed M s lam Kc j) (Mc * F) :=
      Algsuperdiff.Probability.isBigO_of_isBigOWith_of_nonneg
        (fun omega => kickCollapsed_nonneg M s hlam0 Kc j omega) (hmain j)
    have hint := Algsuperdiff.Probability.integral_le_of_isBigO_gammaSigma
      (P := (Cutoff.cutoffSampleLaw M).toMeasure) (by norm_num : (0 : ℝ) < 2)
      (mul_pos hMcpos hF0)
      (measurable_kickCollapsed M s lam Kc j).aemeasurable hO
    rw [hCF]
    refine hint.trans ?_
    have hstep : gammaMomentConst 2 * (Mc * F) = (gammaMomentConst 2 * Mc) * F := by ring
    rw [hstep]
    exact mul_le_mul_of_nonneg_right hGMcC hF0.le

end

end Algsuperdiff.Section4.Provider.MinimalScale
