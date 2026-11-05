/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.StepFourMoments

/-!
# SigmaBarLandmark

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's landmark: the continuity binders discharged, and the `σ` index shift

## What this module does

Three bookkeeping items that Step 5 of `l.bounds.mathcal.E.aL` needs before its
Hölder assembly can be written down.

1. **Bullet (B2) without the continuity binders.**  Bullet (B2) of Step 4
   (`StepFourSigmaBar.exists_sigmaBar_ratio_sub_one_sq_le`) carries
   `l.shom.continuity`'s own binders: the landmark gate `m** < m₀`, the
   induction state at `m₀ − 1`, and the two `E`-window gates, whereas §4.5
   quotes the continuity lemma hypothesis-free.  They are removable at Step 5's
   own landmark: `m₀ := max m (m** + 1)` satisfies BOTH `m ≤ m₀` and `m** < m₀`
   unconditionally, and `GoodEvents.exists_allScalesInductionState_ge` supplies
   the induction state at every scale together with the budget identity
   `E = C c⋆^{-1}` and the regime `γ ≤ E^{-10}`.  The result is (B2) in the
   printed regime alone (plus `γ ≤ 1/8`, which Step 3's display already
   carries), with the `E`-free display of the `_gammaAbsorbed` corollary.

2. **The `σ` index reconciliation.**  The (B5) bullet is delivered at the gauge
   `σ_{j−1}` while Step 3's display and the remaining Step-4 bullets are read
   at `σ_{j−2}`.  The two are interchangeable at the constant `4`, binder-free
   in the printed regime, by the same `hratio` slot that produces (B1).

3. **The dimension binder-order.**  A statement of the shape
   `∃ C, 0 < C ∧ ∀ M : ABKModel d, …` may be proved under `2 ≤ d` and then
   stated without it, because an `ABKModel d` carries `2 ≤ d` itself; the
   `d < 2` branch is vacuous.  This is the exact move the anchor's own binder
   order (`∃ C` before `∀ M`) requires.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 4 bullets (B1)/(B2)/(B5);
  `l.shom.continuity`; `e.shom.h.bounds`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The dimension binder order -/

/-- **The `2 ≤ d` binder, removed from the statement.**

This is the move that lets a provider match the anchor's binder order, where `∃
C` precedes `∀ M`. -/
theorem exists_pos_forall_model_of_two_le_dimension {d : ℕ}
    {Q : ℝ → ABKModel d → Prop}
    (h : 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ M : ABKModel d, Q C M) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ABKModel d, Q C M := by
  by_cases hd : 2 ≤ d
  · exact h hd
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd⟩

/-! ## 2. The `σ` index reconciliation `σ_{j−1} ↔ σ_{j−2}` -/

/-- **The (B5) gauge, moved to the (B1)/(B2)/(B3) index.**

`σ_{j−1}^{-1} ≤ 4 σ_{j−2}^{-1}` for every `j`, in the printed regime alone:
`Annular.SigmaBarBudget.sigmaBar_ratio_le_four` at the index pair
`(m, n) := (j−1, j)`, whose induction-state binder is discharged internally at
the landmark `m₀ := j − 1` by the all-scales state.

This is the conversion Step 5 needs in order to read `LambdaSlotConsumer`'s
(B5) majorant (stated at `σ_{R.scale−1}`) against (B3)'s gauge slot (stated at
`σ_{R.scale−2}`). -/
theorem exists_inv_sigmaBar_sub_one_le_four_mul_inv_sigmaBar_sub_two (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ j : ℤ,
          ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ ≤
            4 * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := GoodEvents.exists_allScalesInductionState d
  refine ⟨C, hC0, ?_⟩
  intro M hreg j
  obtain ⟨E, -, hall⟩ := hC M hreg
  have hratio := sigmaBar_ratio_le_four M (E := E) (hall (j - 1)) (m := j - 1)
    (n := j) (by omega) le_rfl
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M (j - 2) : ℝ) :=
    (Annealed.sigmaBar M (j - 2)).2
  have hinv0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ := (inv_pos.mpr hpos).le
  have hstep := mul_le_mul_of_nonneg_right hratio hinv0
  have hcancel : ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
      (Annealed.sigmaBar M (j - 2) : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ =
      ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
  rw [hcancel] at hstep
  exact hstep

/-- **The printed regime is monotone in the constant.**  Enlarging `C` in `γ ≤
C^{-10} c⋆^{10}` strengthens the hypothesis, so a bullet proved at `C` is
available at any larger constant.  This is what lets one constant serve a
composition of several proved bullets. -/
theorem gamma_regime_mono {C C' cst gam : ℝ} (hC : 0 < C) (hCC : C ≤ C') (hcst : 0 ≤ cst)
    (h : gam ≤ (C'⁻¹) ^ 10 * cst ^ 10) : gam ≤ (C⁻¹) ^ 10 * cst ^ 10 := by
  have hC'0 : (0 : ℝ) < C' := lt_of_lt_of_le hC hCC
  have hinv : C'⁻¹ ≤ C⁻¹ := inv_anti₀ hC hCC
  have hpow : (C'⁻¹) ^ 10 ≤ (C⁻¹) ^ 10 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hC'0.le) hinv 10
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hcst 10)
  linarith only [h, hmul]

/-- **(B3) at the (B5) index.**

`3^{γ j} σ_{j−1}^{-1} ≤ 16 c⋆^{-1/2} γ^{1/2}`: the gauge slot of Step 4, read
at the index `j − 1` that bullet (B5) delivers, through the index
reconciliation `σ_{j−1}^{-1} ≤ 4 σ_{j−2}^{-1}`.  The constant `16` is the
printed `4` of (B3) times the reconciliation's `4`.

This is the factor that makes Step 5's bracket `O(√γ)`: it is the ONLY place
where the product `‖∇(k_L−k_{j−2})‖ · λ^{-1}` of the two Step-4 bullets is
converted into a `γ`-power. -/
theorem exists_rpow_gamma_mul_inv_sigmaBar_sub_one_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ j : ℤ,
          (3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ ≤
            16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) := by
  obtain ⟨C1, hC1, hB3⟩ := exists_rpow_gamma_mul_inv_sigmaBar_sub_two_le d
  obtain ⟨C2, hC2, hidx⟩ := exists_inv_sigmaBar_sub_one_le_four_mul_inv_sigmaBar_sub_two d
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left _ _), ?_⟩
  intro M hreg j
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hb3 := hB3 M (gamma_regime_mono hC1 (le_max_left C1 C2) hcs0.le hreg) j
  have hix := hidx M (gamma_regime_mono hC2 (le_max_right C1 C2) hcs0.le hreg) j
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc (3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹
      ≤ (3 : ℝ) ^ (M.gamma * (j : ℝ)) * (4 * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hix h3
    _ = 4 * ((3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹) := by
        ring
    _ ≤ 4 * (4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) :=
        mul_le_mul_of_nonneg_left hb3 (by norm_num)
    _ = 16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) := by ring

/-! ## 3. Bullet (B2) without the continuity binders -/

/-- **(B2), unconditional in the printed regime.**

The squared `l.shom.continuity` display at the anchor's index pair, with ALL of
the continuity lemma's binders discharged:

```
(σ_m σ_{j−2}^{-1} − 1)²
    ≤ C (min{1, γ(m−j+2) + γ^{3/5}|log γ|²})² 3^{2γ(m−j)} ,      j − 2 ≤ m .
```

The landmark is Step 5's own: `m₀ := max m (m** + 1)` meets the gate `m** < m₀`
and the range binder `m ≤ m₀` at once, and the induction state at `m₀ − 1`
(with the budget identity `E = C c⋆^{-1}` and the regime `γ ≤ E^{-10}`) is
`GoodEvents.exists_allScalesInductionState_ge`, i.e. the manuscript's own
discharge.

The only binder beyond the printed regime is `γ ≤ 1/8`, which Step 3's display
already carries. -/
theorem exists_sigmaBar_ratio_sub_one_sq_le_unconditional (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        M.gamma ≤ 1 / 8 →
        ∀ m j : ℤ, j - 2 ≤ m →
          ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ - 1) ^ 2 ≤
            C * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
                  M.gamma ^ ((3 : ℝ) / 5) * |Real.log M.gamma| ^ 2)) ^ 2 *
              (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) := by
  obtain ⟨C1, hC1, hbase⟩ := exists_sigmaBar_ratio_sub_one_sq_le_gammaAbsorbed d
  obtain ⟨C, hC6, hC1le, hall⟩ := GoodEvents.exists_allScalesInductionState_ge d C1
  refine ⟨C, lt_of_lt_of_le (by norm_num) hC6, ?_⟩
  intro M hreg hgam m j hjm
  obtain ⟨E, hEval, hEreg, hstate⟩ := hall M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hm : m ≤ max m (mStarStar M + 1) := le_max_left _ _
  have hlm : mStarStar M < max m (mStarStar M + 1) :=
    lt_of_lt_of_le (by omega) (le_max_right m (mStarStar M + 1))
  have hCE : C1 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    rw [hEval]
    exact mul_le_mul_of_nonneg_right hC1le (inv_pos.mpr hcs0).le
  have hkey := hbase M (max m (mStarStar M + 1)) E hlm
    (hstate (max m (mStarStar M + 1) - 1)) hCE hEreg hgam m j hjm hm
  refine le_trans hkey ?_
  have hbase0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC1le (sq_nonneg _)) hbase0

end

end Algsuperdiff.Section4.Provider.BoundsEaL
