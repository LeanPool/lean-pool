/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.StepOneAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.StepThreeRearrange
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GammaSigmaFiniteTriangle

/-!
# KickingLemma

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `l.minimal.scale.sep`: the kicking lemma `e.good.scale.kicking`

ABK26, §4.2.  This module assembles the three Steps of
`l.minimal.scale.sep` into the lemma itself: for every window `[n, m]` with
`n < m`,

```
avsum_{k=n}^m sup_{L ≥ k} 𝓔_{s,∞,2}(□_k; a_L − (k_L − k_k)_{□_k}, σ_k) 1_{𝒢(k;s,1)}
  ≤ C c⋆^{−1}s^{−7/2}√γ + 𝒪_{Γ₂}( C c⋆^{−1}s^{−9/2}√γ (m−n)^{−1/2} ) .
```

The four inputs are already proved and are consumed by name:

* `exists_dDecomposition_absorbed` — the `√`-split of the annular anchor's
  clause (i) with the deterministic remainder already absorbed into the
  envelope;
* `exists_stepOne_d1_bound` — the `D₁` half of `e.kick.Dees.Dees`;
* `exists_D2k_kicked` — `e.D2k.kicked` at a free prefactor;
* `exists_D3k_kicked` with `stepThree_det_closed` / `stepThree_fluc_closed` —
  `e.D3k.kicked` and its two closed `s`-powers.

## The two coordination bridges

Steps 2 and 3 are stated against their own inner objects `gradInnerE` /
`hessInnerE`, the `D`-decomposition against `dTwo` / `dThree`.  The bridges are:

* `dTwo_eq_ofReal_mul_gradInnerE` — an **identity** (`rfl`): the two spellings of
  the `∇𝐣` group agree termwise, prefactor included.
* `dThree_le_ofReal_mul_hessInnerE` — the `𝐣`-Hessian group needs the
  `iSup → fmax` step (`inner_le_scoreG1b`, re-derived here because the
  `Proportion` original is `private`) and the weight-spelling identity
  `3^{−¼s(k−n)} = stepThreeWt (s/4) (k−n)`.  The `ℓ² → ℓ¹` halving is NOT owed
  here: `dThree` is already the `ℓ¹` object at the quarter exponent.

The prefactor `c⋆^{−1/2}s^{−1}γ^{1/2}` of the two `𝐣` groups is compared with
the lemma's envelope by `sqrt_cstar_inv_le` (the standing `c⋆ ≤ 3/2`, never `c⋆
≤ 1`) — the `√(C X²) = √C X` bookkeeping.

## The exponent

The fluctuation slot is `s^{−9/2}`, **not** the printed `s^{−7/2}`: Step 3's
below-window channel forces it (`stepThree_fluc_closed`) and the printed
amplitude is sharp.  The deterministic slot is the printed `s^{−7/2}`.

## Finiteness

The three groups are read in `ℝ` through `toReal`, so the assembly needs them
finite: `D₁` is finite at **every** sample (`dOne_ne_top`), and `D₂`, `D₃` are
finite almost surely at every scale of the window — from the proved
first-moment arguments `ae_gradSeries_finite` and `ae_hessHeadSeries_finite`,
never assumed.

## References

* ABK26, `l.minimal.scale.sep`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open Algsuperdiff.Probability
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Numerical facts -/

/-- `log 3 ≤ 2`, from `log x ≤ x − 1`. -/
private theorem log_three_le_two' : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  linarith only [h]

/-- The three-term `Γ₂` triangle constant is at most `2`. -/
theorem triangleConstThree_le : (1 + Real.log 3) ^ ((2 : ℝ))⁻¹ ≤ 2 := by
  have hl := log_three_le_two'
  have heq : (1 + Real.log 3) ^ ((2 : ℝ))⁻¹ = Real.sqrt (1 + Real.log 3) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq]
  have h2 := Real.sqrt_le_sqrt (show 1 + Real.log 3 ≤ (4 : ℝ) from by linarith only [hl])
  rw [h4] at h2
  exact h2

/-- The Step-3 deterministic constant is positive. -/
theorem stepThreeDetConst_pos (d : ℕ) : 0 < stepThreeDetConst d := by
  have h1 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : 0 < hessAmp d := hessAmp_pos d
  have h3 : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  simp only [stepThreeDetConst]
  positivity

/-- The Step-3 fluctuation constant is positive. -/
theorem stepThreeFlucConst_pos (d : ℕ) : 0 < stepThreeFlucConst d := by
  have h1 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : 0 < hessAmp d := hessAmp_pos d
  have h3 : 0 < cesaroTailEngineConst := cesaroTailEngineConst_pos
  simp only [stepThreeFlucConst]
  positivity

/-! ## 2. The prefactor arithmetic of the two `𝐣` groups -/

/-- **The `√c⋆` bookkeeping.**  The `𝐣` groups carry
`c⋆^{−1/2}`, the lemma's envelope carries `c⋆^{−1}`; the standing `c⋆ ≤ 3/2`
(never `c⋆ ≤ 1`) converts one into the other at the absolute cost `2`. -/
theorem sqrt_cstar_inv_le (M : ABKModel d) :
    (Real.sqrt (Disorder.cstar M))⁻¹ ≤ 2 * (Disorder.cstar M)⁻¹ := by
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hsq0 : (0 : ℝ) < Real.sqrt (Disorder.cstar M) := Real.sqrt_pos.2 hcs
  have hmul : Real.sqrt (Disorder.cstar M) * Real.sqrt (Disorder.cstar M) =
      Disorder.cstar M := Real.mul_self_sqrt hcs.le
  have hsqle : Real.sqrt (Disorder.cstar M) ≤ 2 := by
    have h := Real.sqrt_le_sqrt (show Disorder.cstar M ≤ (4 : ℝ) from by linarith only [hcs32])
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h4] at h
    exact h
  refine le_of_mul_le_mul_right ?_ hcs
  have h1 : (Real.sqrt (Disorder.cstar M))⁻¹ * Disorder.cstar M =
      Real.sqrt (Disorder.cstar M) := by
    rw [inv_mul_eq_div, div_eq_iff (ne_of_gt hsq0)]
    exact hmul.symm
  have h2 : 2 * (Disorder.cstar M)⁻¹ * Disorder.cstar M = 2 := by
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hcs), mul_one]
  rw [h1, h2]
  exact hsqle

/-- The two reciprocal square-root facts of the window. -/
private theorem sqrt_window_facts {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 < Real.sqrt x ∧ Real.sqrt x ≤ 1 ∧ x⁻¹ = ((Real.sqrt x) ^ (2 : ℕ))⁻¹ := by
  have hsq0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq1 : Real.sqrt x ≤ 1 := by
    have h := Real.sqrt_le_sqrt hx1
    rwa [Real.sqrt_one] at h
  refine ⟨hsq0, hsq1, ?_⟩
  rw [Real.sq_sqrt hx0.le]

/-- Monotonicity of the reciprocal powers of `√s` on the window. -/
private theorem inv_pow_sqrt_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {p q : ℕ} (hpq : p ≤ q) :
    ((Real.sqrt x) ^ p)⁻¹ ≤ ((Real.sqrt x) ^ q)⁻¹ := by
  obtain ⟨hsq0, hsq1, -⟩ := sqrt_window_facts hx0 hx1
  exact inv_anti₀ (pow_pos hsq0 q) (pow_le_pow_of_le_one hsq0.le hsq1 hpq)

/-- **The `D₂` deterministic prefactor against the lemma's envelope.** -/
theorem pref_le_two_mul_envSeven (M : ABKModel d) (s : {s : ℝ // 0 < s})
    (hs1 : (s : ℝ) ≤ 1) :
    (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma ≤
      2 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
  obtain ⟨hsq0, -, hinv2⟩ := sqrt_window_facts s.2 hs1
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have h27 : ((Real.sqrt (s : ℝ)) ^ (2 : ℕ))⁻¹ ≤ ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ :=
    inv_pow_sqrt_le s.2 hs1 (by norm_num)
  calc (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma
      = (Real.sqrt (Disorder.cstar M))⁻¹ * ((Real.sqrt (s : ℝ)) ^ (2 : ℕ))⁻¹ *
          Real.sqrt M.gamma := by rw [hinv2]
    _ ≤ 2 * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul (sqrt_cstar_inv_le M) h27 (by positivity) (by positivity))
          (Real.sqrt_nonneg _)
    _ = 2 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
          Real.sqrt M.gamma) := by ring

/-- The exact `s`-power identity behind the two `𝐣` slots: `s^{-1}(√s)^{-p} =
(√s)^{-(p+2)}`. -/
private theorem inv_mul_inv_pow_sqrt {x : ℝ} (hx0 : 0 < x) (p : ℕ) :
    x⁻¹ * ((Real.sqrt x) ^ p)⁻¹ = ((Real.sqrt x) ^ (p + 2))⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [pow_add, Real.sq_sqrt hx0.le]
  ring

/-- **The `D₃` deterministic prefactor against the lemma's envelope.** -/
theorem pref_mul_inv_five_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) (hs1 : (s : ℝ) ≤ 1) :
    (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
        ((Real.sqrt (s : ℝ)) ^ (5 : ℕ))⁻¹ ≤
      2 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
  have hid := inv_mul_inv_pow_sqrt s.2 5
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  obtain ⟨hsq0, -, -⟩ := sqrt_window_facts s.2 hs1
  have hstep : (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
      ((Real.sqrt (s : ℝ)) ^ (5 : ℕ))⁻¹
      = (Real.sqrt (Disorder.cstar M))⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
          Real.sqrt M.gamma := by
    rw [show (7 : ℕ) = 5 + 2 from by norm_num, ← hid]
    ring
  rw [hstep]
  calc (Real.sqrt (Disorder.cstar M))⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
        Real.sqrt M.gamma
      ≤ 2 * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (sqrt_cstar_inv_le M) (by positivity))
          (Real.sqrt_nonneg _)
    _ = 2 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
          Real.sqrt M.gamma) := by ring

/-- **The `D₃` fluctuation prefactor against the-corrected envelope.** -/
theorem pref_mul_inv_seven_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) (hs1 : (s : ℝ) ≤ 1) :
    (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
        ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ ≤
      2 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) := by
  have hid := inv_mul_inv_pow_sqrt s.2 7
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  obtain ⟨hsq0, -, -⟩ := sqrt_window_facts s.2 hs1
  have hstep : (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
      ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹
      = (Real.sqrt (Disorder.cstar M))⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ *
          Real.sqrt M.gamma := by
    rw [show (9 : ℕ) = 7 + 2 from by norm_num, ← hid]
    ring
  rw [hstep]
  calc (Real.sqrt (Disorder.cstar M))⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ *
        Real.sqrt M.gamma
      ≤ 2 * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (sqrt_cstar_inv_le M) (by positivity))
          (Real.sqrt_nonneg _)
    _ = 2 * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ *
          Real.sqrt M.gamma) := by ring

/-- The printed envelope is below the-corrected one. -/
theorem envSeven_le_envNine (M : ABKModel d) (s : {s : ℝ // 0 < s}) (hs1 : (s : ℝ) ≤ 1) :
    (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma ≤
      (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma := by
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have h79 : ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ ≤ ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ :=
    inv_pow_sqrt_le s.2 hs1 (by norm_num)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h79 ?_) (Real.sqrt_nonneg _)
  exact inv_nonneg.2 hcs.le

/-- Positivity of the-corrected envelope. -/
theorem envNine_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) :
    0 ≤ (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma := by
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 s.2
  positivity

/-- Positivity of the printed envelope. -/
theorem envSeven_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) :
    0 ≤ (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ * Real.sqrt M.gamma := by
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 s.2
  positivity

/-! ## 3. The two coordination bridges -/

/-- **The `D₂` bridge: an identity.**  `D₂(k)` is the `D-s23` inner sum times the
printed prefactor, on the nose. -/
theorem dTwo_eq_ofReal_mul_gradInnerE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    dTwo M s k omega =
      ENNReal.ofReal
          ((Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma) *
        gradInnerE M k omega := rfl

/-- **The `iSup → fmax` step** (re-derived: `Proportion`'s `inner_le_score` is
`private`).  The anchor's inner block at one scale is below the `𝒢₁b` score
field. -/
theorem inner_le_scoreG1b (M : ABKModel d) {i k : ℤ} (hik : i ≤ k)
    (omega : Cutoff.CutoffSample d) :
    ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (i : ℝ))) *
        ⨆ v : ↥(latticeCubeSet d i k),
          ENNReal.ofReal (shellW2InfNormAt (triadicLatticePoint i v.1) i (omega.1 i)) ≤
      ENNReal.ofReal (Proportion.scoreG1b M k i omega) := by
  rw [ENNReal.mul_iSup]
  refine iSup_le fun v => ?_
  rw [← ENNReal.ofReal_mul (Proportion.rpow_nonneg_three _)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact Proportion.le_fmax
    (f := fun v => Proportion.atomG1b M i (triadicLatticePoint i v) omega)
    ((Proportion.mem_latticeCubeFinset_iff hik).2 v.2)

/-- The weight-spelling identity of the `D₃` bridge. -/
theorem three_rpow_quarter_eq_stepThreeWt (a : ℝ) (t : ℤ) :
    Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * a * ((t : ℤ) : ℝ)) = stepThreeWt (a / 4) t := by
  rw [stepThreeWt]
  congr 1
  ring

/-- **The `D₃` bridge.**  `D₃(k)` is below the printed prefactor times `D-s23`'s
`ℓ¹` inner object at `α = s/4`.  The two steps are the weight spelling and the
`iSup → fmax` domination; no `ℓ² → ℓ¹` halving is needed (`D-s1`'s `dThree` is
already the `ℓ¹` object). -/
theorem dThree_le_ofReal_mul_hessInnerE (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    dThree M s k omega ≤
      ENNReal.ofReal
          ((Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma) *
        hessInnerE M ((s : ℝ) / 4) k omega := by
  rw [dThree, hessInnerE]
  refine mul_le_mul_right (ENNReal.tsum_le_tsum fun n => ?_) _
  rw [three_rpow_quarter_eq_stepThreeWt (s : ℝ) (k - n.1)]
  refine mul_le_mul_right (Finset.sum_le_sum fun i hi => ?_) _
  have hik : i ≤ k := (Finset.mem_Icc.1 hi).2
  exact inner_le_scoreG1b M hik omega

/-! ## 4. Finiteness of the three groups -/

/-- `D₂(k)` is finite wherever the Step-2 majorant series converges — almost
surely, at every scale (`ae_gradSeries_finite`). -/
theorem dTwo_ne_top (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    {omega : Cutoff.CutoffSample d}
    (hfin : wsumE (fun p => Proportion.atomG1a M (k + (p : ℤ))) (gradWeight M) omega
      ≠ (⊤ : ℝ≥0∞)) :
    dTwo M s k omega ≠ (⊤ : ℝ≥0∞) := by
  rw [dTwo_eq_ofReal_mul_gradInnerE]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top hfin (gradInnerE_le_wsumE M k omega))

/-- The Step-3 inner object is finite at every scale of the window wherever the
below-window channel converges — almost surely (`ae_hessHeadSeries_finite`). -/
theorem hessInnerE_ne_top (M : ABKModel d) {alpha : ℝ} (halpha : 0 < alpha) {n m : ℤ}
    {omega : Cutoff.CutoffSample d}
    (hfin : wsumE (fun r => hessHead M alpha n m r)
      (fun r => stepThreeWeight alpha (r + 1)) omega ≠ (⊤ : ℝ≥0∞))
    {k : ℤ} (hk : k ∈ Finset.Icc n m) :
    hessInnerE M alpha k omega ≠ (⊤ : ℝ≥0∞) := by
  set A : ℝ≥0∞ := ∑ i ∈ Finset.Icc n m,
    ENNReal.ofReal (hessWindow M alpha n m i omega) with hAdef
  have hAne : A ≠ (⊤ : ℝ≥0∞) := by
    rw [hAdef]
    refine (ENNReal.sum_lt_top.2 fun i _ => ?_).ne
    exact ENNReal.ofReal_lt_top
  have hRne : ENNReal.ofReal ((3 : ℝ) ^ alpha * geomTailConst alpha) *
      (A + wsumE (fun r => hessHead M alpha n m r)
        (fun r => stepThreeWeight alpha (r + 1)) omega) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hAne, hfin⟩)
  have hle := sum_hessInnerE_le M halpha n m omega
  rw [← hAdef] at hle
  refine ne_top_of_le_ne_top hRne (le_trans ?_ hle)
  exact Finset.single_le_sum (f := fun k => hessInnerE M alpha k omega)
    (fun j _ => (zero_le : (0 : ℝ≥0∞) ≤ hessInnerE M alpha j omega)) hk

/-- `D₃(k)` is finite at every scale of the window wherever the Step-3
below-window channel converges — almost surely (`ae_hessHeadSeries_finite`). -/
theorem dThree_ne_top (M : ABKModel d) (s : {s : ℝ // 0 < s}) {n m : ℤ}
    {omega : Cutoff.CutoffSample d}
    (hfin : wsumE (fun r => hessHead M ((s : ℝ) / 4) n m r)
      (fun r => stepThreeWeight ((s : ℝ) / 4) (r + 1)) omega ≠ (⊤ : ℝ≥0∞))
    {k : ℤ} (hk : k ∈ Finset.Icc n m) :
    dThree M s k omega ≠ (⊤ : ℝ≥0∞) := by
  have halpha : (0 : ℝ) < (s : ℝ) / 4 := by
    have := s.2
    linarith only [this]
  refine ne_top_of_le_ne_top ?_ (dThree_le_ofReal_mul_hessInnerE M s k omega)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hessInnerE_ne_top M halpha hfin hk)

/-! ### The two real readings -/

/-- The `D₂` prefactor is nonnegative. -/
theorem jPref_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s}) :
    0 ≤ (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  positivity

/-- The real reading of `D₂(k)`: the printed prefactor times `D-s23`'s inner sum. -/
theorem dTwo_toReal_eq (M : ABKModel d) (s : {s : ℝ // 0 < s}) (k : ℤ)
    (omega : Cutoff.CutoffSample d) :
    (dTwo M s k omega).toReal =
      (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
        gradInner M k omega := by
  rw [dTwo_eq_ofReal_mul_gradInnerE, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (jPref_nonneg M s)]
  rfl

/-- The real reading of `D₃(k)`, at the scales of a window where the Step-3
below-window channel converges. -/
theorem dThree_toReal_le (M : ABKModel d) (s : {s : ℝ // 0 < s}) {n m : ℤ}
    {omega : Cutoff.CutoffSample d}
    (hfin : wsumE (fun r => hessHead M ((s : ℝ) / 4) n m r)
      (fun r => stepThreeWeight ((s : ℝ) / 4) (r + 1)) omega ≠ (⊤ : ℝ≥0∞))
    {k : ℤ} (hk : k ∈ Finset.Icc n m) :
    (dThree M s k omega).toReal ≤
      (Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma *
        hessInner M ((s : ℝ) / 4) k omega := by
  have halpha : (0 : ℝ) < (s : ℝ) / 4 := by
    have := s.2
    linarith only [this]
  have hne : ENNReal.ofReal
      ((Real.sqrt (Disorder.cstar M))⁻¹ * ((s : ℝ))⁻¹ * Real.sqrt M.gamma) *
      hessInnerE M ((s : ℝ) / 4) k omega ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hessInnerE_ne_top M halpha hfin hk)
  have h := ENNReal.toReal_mono hne (dThree_le_ofReal_mul_hessInnerE M s k omega)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (jPref_nonneg M s)] at h

/-! ## 5. The `ℝ≥0∞` window average, converted to the real Cesàro averages -/

/-- **The conversion step.**  Given the `D`-decomposition at every scale of the
window and the finiteness of the three groups there, the frozen `ℝ≥0∞` window
average of the gated observable is below the `ofReal` of the real Cesàro sum.
The window normaliser `(((m−n).toNat : ℝ≥0∞) + 1)⁻¹` is exactly `ofReal` of
`cesaroAvg`'s own `1/(m−n+1)`. -/
theorem window_avg_le_ofReal_cesaro (M : ABKModel d) (Ccg : ℝ) (s : {s : ℝ // 0 < s})
    {n m : ℤ} (hnm : n ≤ m) {CD E : ℝ} (hCD : 0 ≤ CD) (hE : 0 ≤ E)
    {omega : Cutoff.CutoffSample d}
    (hdec : ∀ k ∈ Finset.Icc n m,
      Set.indicator (goodEventBase M Ccg k s 1)
          (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega ≤
        ENNReal.ofReal CD *
          (dOne M Ccg s k omega + dTwo M s k omega + dThree M s k omega +
            ENNReal.ofReal E))
    (h1 : ∀ k ∈ Finset.Icc n m, dOne M Ccg s k omega ≠ (⊤ : ℝ≥0∞))
    (h2 : ∀ k ∈ Finset.Icc n m, dTwo M s k omega ≠ (⊤ : ℝ≥0∞))
    (h3 : ∀ k ∈ Finset.Icc n m, dThree M s k omega ≠ (⊤ : ℝ≥0∞)) :
    (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
        ∑ k ∈ Finset.Icc n m,
          Set.indicator (goodEventBase M Ccg k s 1)
            (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega ≤
      ENNReal.ofReal
        (CD * (cesaroAvg (fun k => (dOne M Ccg s k omega).toReal) n m +
          cesaroAvg (fun k => (dTwo M s k omega).toReal) n m +
          cesaroAvg (fun k => (dThree M s k omega).toReal) n m + E)) := by
  set f : ℤ → ℝ := fun k =>
    CD * ((dOne M Ccg s k omega).toReal + (dTwo M s k omega).toReal +
      (dThree M s k omega).toReal + E) with hfdef
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    refine mul_nonneg hCD ?_
    have := ENNReal.toReal_nonneg (a := dOne M Ccg s k omega)
    have := ENNReal.toReal_nonneg (a := dTwo M s k omega)
    have := ENNReal.toReal_nonneg (a := dThree M s k omega)
    positivity
  -- the per-scale conversion
  have hterm : ∀ k ∈ Finset.Icc n m,
      Set.indicator (goodEventBase M Ccg k s 1)
          (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega ≤
        ENNReal.ofReal (f k) := by
    intro k hk
    refine (hdec k hk).trans (le_of_eq ?_)
    rw [hfdef, ENNReal.ofReal_mul hCD]
    refine congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal CD * t) ?_
    rw [ENNReal.ofReal_add
        (by positivity : (0 : ℝ) ≤ (dOne M Ccg s k omega).toReal +
          (dTwo M s k omega).toReal + (dThree M s k omega).toReal) hE,
      ENNReal.ofReal_add
        (by positivity : (0 : ℝ) ≤ (dOne M Ccg s k omega).toReal +
          (dTwo M s k omega).toReal) ENNReal.toReal_nonneg,
      ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (h1 k hk), ENNReal.ofReal_toReal (h2 k hk),
      ENNReal.ofReal_toReal (h3 k hk)]
  -- the normaliser
  have hpos : (0 : ℝ) < (((m - n).toNat : ℕ) : ℝ) + 1 := by positivity
  have hcast : (((m - n).toNat : ℕ) : ℝ) + 1 = ((m - n + 1 : ℤ) : ℝ) := by
    have h : (((m - n).toNat : ℕ) : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
    have h2' : ((((m - n).toNat : ℕ) : ℤ) : ℝ) = ((m - n : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h2' ⊢
    linarith only [h2']
  have hW : (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ = ENNReal.ofReal (1 / ((m - n + 1 : ℤ) : ℝ)) := by
    rw [show (((m - n).toNat : ℝ≥0∞)) = ENNReal.ofReal (((m - n).toNat : ℕ) : ℝ) from
        (ENNReal.ofReal_natCast _).symm,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_add (by positivity) zero_le_one, one_div,
      ← ENNReal.ofReal_inv_of_pos hpos, hcast]
  have hw0 : (0 : ℝ) ≤ 1 / ((m - n + 1 : ℤ) : ℝ) := by
    have := cesaroAvg_denom_pos hnm
    positivity
  calc (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
        ∑ k ∈ Finset.Icc n m,
          Set.indicator (goodEventBase M Ccg k s 1)
            (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega
      ≤ (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ * ∑ k ∈ Finset.Icc n m, ENNReal.ofReal (f k) :=
        mul_le_mul_right (Finset.sum_le_sum hterm) _
    _ = ENNReal.ofReal (1 / ((m - n + 1 : ℤ) : ℝ)) *
          ENNReal.ofReal (∑ k ∈ Finset.Icc n m, f k) := by
        rw [hW, ENNReal.ofReal_sum_of_nonneg fun k _ => hf0 k]
    _ = ENNReal.ofReal ((1 / ((m - n + 1 : ℤ) : ℝ)) * ∑ k ∈ Finset.Icc n m, f k) :=
        (ENNReal.ofReal_mul hw0).symm
    _ = ENNReal.ofReal
          (CD * (cesaroAvg (fun k => (dOne M Ccg s k omega).toReal) n m +
            cesaroAvg (fun k => (dTwo M s k omega).toReal) n m +
            cesaroAvg (fun k => (dThree M s k omega).toReal) n m + E)) := by
        refine congrArg ENNReal.ofReal ?_
        have hcesaro : (1 / ((m - n + 1 : ℤ) : ℝ)) * ∑ k ∈ Finset.Icc n m, f k
            = cesaroAvg f n m := rfl
        rw [hcesaro, hfdef, cesaroAvg_const_mul, cesaroAvg_add4 hnm]

end

end Algsuperdiff.Section4.Provider.MinimalScale
