/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ShomContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SigmaBarBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.InductionState

/-!
# StepFourSigmaBar

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 4's `σ`-arithmetic at the anchor's index pair `(m, j−2)`

## What Step 4 needs, and what is proved here

Step 4 of the proof of `l.bounds.mathcal.E.aL` (ff.) reads Step 3's display at
the index pair `(m, j−2)` -- the recentering scale `m` against the `𝒢₂`-cutoff
scale `j−2` of the cube `□_j`.  Three scalar inputs of that reading are
`σ`-arithmetic and are proved here:

* **(B1)** `σ_m^{-1} σ_{j−2} ≤ 4` -- the ratio slot, at every pair `j − 2 ≤ m`;
* **(B3)** `3^{γ j} σ_{j−2}^{-1} ≤ 4 c⋆^{-1/2} γ^{1/2}` -- the gauge slot,
  i.e. the lower branch of the `e.shom.h.bounds` rearranged, with the index
  shift `3^{2γ} ≤ 2` already paid;
* **(B2)** the square of `l.shom.continuity`'s fifth conclusion at the shifted
  pair, which is the shape in which `(σ_m σ_{j−2}^{-1} − 1)^2` occurs in Step
  3's display, with the shift factor `3^{4γ} ≤ 2` absorbed into the constant.

(B1) and (B3) are stated in the **printed regime only**: their induction-state
binder is discharged internally by `GoodEvents.exists_allScalesInductionState`
(the manuscript's own discharge), so nothing is left for a caller beyond `γ ≤
C^{-10} c⋆^{10}`.

(B2) cannot be made binder-free: `l.shom.continuity` carries the landmark gate
`m** < m₀`, the induction state at `m₀ − 1` and the two `E`-window gates, and
its right-hand side mentions `E`.  Those binders are carried honestly below.
The `E`-free corollary `..._gammaAbsorbed` replaces `E² γ |log γ|²` by `γ^{3/5}
|log γ|²` using only the printed regime `γ ≤ E^{-10}` and `1 ≤ E` (through the
proved `E ≤ γ^{-1/5}` window), so a consumer that does not want to carry `E` in
the display still keeps the two structural binders.

## Constants

Every constant below is explicit: `4` in (B1), `4 c⋆^{-1/2}` in (B3), and
`max C (2C²)` in (B2), where `C` is `l.shom.continuity`'s own constant.  The
`max` is what lets one constant serve both as the budget gate `C c⋆^{-1} ≤ E`
and as the display constant.

## References

* ABK26, `l.bounds.mathcal.E.aL`, ff.  (Step 4); `l.shom.continuity`, (its
  fifth conclusion ff.); `e.shom.h.bounds`; `p.induction.bounds` proof.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## B1: the ratio slot -/

/-- **(B1) The `σ` ratio at the anchor's index pair.**

`σ_m^{-1} σ_{j−2} ≤ 4` for every pair with `j − 2 ≤ m`, in the printed regime
alone: the induction-state binder of
`Annular.SigmaBarBudget.sigmaBar_ratio_le_four` is discharged by the all-scales
state, at `m₀ := m`. -/
theorem exists_inv_sigmaBar_mul_sigmaBar_sub_two_le_four (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ m j : ℤ, j - 2 ≤ m →
          ((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M (j - 2) : ℝ) ≤ 4 := by
  obtain ⟨C, hC0, hC⟩ := GoodEvents.exists_allScalesInductionState d
  refine ⟨C, hC0, ?_⟩
  intro M hreg m j hjm
  obtain ⟨E, -, hall⟩ := hC M hreg
  exact sigmaBar_ratio_le_four M (E := E) (hall m) hjm le_rfl

/-! ## B3: the gauge slot -/

/-- The amplitude inversion `(√c⋆ (√γ)^{-1})^{-1} = (√c⋆)^{-1} √γ`. -/
private theorem inv_amplitude_eq {c g : ℝ} :
    (Real.sqrt c * (Real.sqrt g)⁻¹)⁻¹ = (Real.sqrt c)⁻¹ * Real.sqrt g := by
  rw [mul_inv, inv_inv]

/-- **(B3) The gauge slot.**

`3^{γ j} σ_{j−2}^{-1} ≤ 4 c⋆^{-1/2} γ^{1/2}`: the lower branch of the
`e.shom.h.bounds`, read at the shifted index `j − 2` (where the proved
`Annular.SigmaBarBudget.inv_sigmaBar_sub_two_le_of_inductionState` has already
paid the index shift `3^{2γ} ≤ 2`, at the honest constant `4`), multiplied by
the gauge weight `3^{γ j}`.

The `γ^{1/2}` on the right is what Step 4's moment pass converts into the
anchor's `√γ`; the `c⋆^{-1/2}` is the subsection's constant convention. -/
theorem exists_rpow_gamma_mul_inv_sigmaBar_sub_two_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ j : ℤ,
          (3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ ≤
            4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) := by
  obtain ⟨C, hC0, hC⟩ := GoodEvents.exists_allScalesInductionState d
  refine ⟨C, hC0, ?_⟩
  intro M hreg j
  obtain ⟨E, -, hall⟩ := hC M hreg
  have hbase := inv_sigmaBar_sub_two_le_of_inductionState M (E := E) (hall (j - 2))
    (n := j) le_rfl
  have hP : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_left hbase hP.le
  refine le_trans hstep (le_of_eq ?_)
  rw [inv_amplitude_eq]
  have hcancel : (3 : ℝ) ^ (M.gamma * (j : ℝ)) * (3 : ℝ) ^ (-(M.gamma * (j : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), add_neg_cancel, Real.rpow_zero]
  calc (3 : ℝ) ^ (M.gamma * (j : ℝ)) *
        (4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma *
          (3 : ℝ) ^ (-(M.gamma * (j : ℝ)))))
      = 4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) *
          ((3 : ℝ) ^ (M.gamma * (j : ℝ)) * (3 : ℝ) ^ (-(M.gamma * (j : ℝ)))) := by ring
    _ = 4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) := by
        rw [hcancel, mul_one]

/-! ## B2: the squared continuity display at the shifted pair -/

/-- `3^{4γ} ≤ 2` at `γ ≤ 1/8`: the cost of moving the continuity display's
index shift `m − (j−2)` back to `m − j`. -/
private theorem three_rpow_four_gamma_le_two {gam : ℝ} (hgam : gam ≤ 1 / 8) :
    (3 : ℝ) ^ (4 * gam) ≤ 2 := by
  have hmono : (3 : ℝ) ^ (4 * gam) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgam])
  have hhalf : (3 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
    have hsq : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 3 := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [hsq]
    norm_num
  exact le_trans hmono hhalf

/-- The square of a `3`-power, in the `Real.rpow` spelling the display uses. -/
private theorem rpow_sq (x : ℝ) : ((3 : ℝ) ^ x) ^ (2 : ℕ) = (3 : ℝ) ^ (2 * x) := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ x) 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- The `Real.rpow` bookkeeping of the index shift: `3^{2γ(m−j+2)}` is
`3^{4γ} · 3^{2γ(m−j)}`. -/
private theorem rpow_two_gamma_shift (gam x : ℝ) :
    (3 : ℝ) ^ (2 * (gam * (x + 2))) = (3 : ℝ) ^ (4 * gam) * (3 : ℝ) ^ (2 * (gam * x)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- **(B2) The squared continuity display at the shifted pair.**

`l.shom.continuity`'s fifth conclusion at `(n, m) := (j−2, m)`, squared:

```
(σ_m σ_{j−2}^{-1} − 1)^2 ≤ C · (min 1 (γ(m−j+2) + E² γ |log γ|²))^2 · 3^{2γ(m−j)} .
```

The second summand of the printed left-hand side (`|σ_{j−2} σ_m^{-1} − 1|`) is
dropped by nonnegativity; the index shift is paid by `3^{4γ} ≤ 2`, absorbed into
the constant. -/
theorem exists_sigmaBar_ratio_sub_one_sq_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        M.gamma ≤ 1 / 8 →
        ∀ m j : ℤ, j - 2 ≤ m → m ≤ m0 →
          ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ - 1) ^ 2 ≤
            C * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
                  (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
              (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) := by
  obtain ⟨C, hC0, hcont⟩ :=
    Algsuperdiff.Section3.Provider.Localization.shom_continuity d
  refine ⟨max C (2 * C ^ 2), lt_of_lt_of_le hC0 (le_max_left _ _), ?_⟩
  intro M m0 E hm0 hstate hCE hreg hgam m j hjm hm
  have hCle : C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left C (2 * C ^ 2))
      (inv_pos.mpr hcs0).le) hCE
  obtain ⟨-, -, -, -, hfive⟩ := hcont M m0 E hm0 hstate hCle hreg m (j - 2) hjm hm
  -- the printed display at the shifted pair, with the second summand dropped
  have hshift : ((m : ℝ) - (((j - 2 : ℤ)) : ℝ)) = ((m : ℝ) - (j : ℝ)) + 2 := by
    push_cast
    ring
  rw [hshift] at hfive
  have habs : |(Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ - 1| ≤
      C * min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
            (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) *
        (3 : ℝ) ^ (M.gamma * (((m : ℝ) - (j : ℝ)) + 2)) := by
    have hnn := abs_nonneg ((Annealed.sigmaBar M (j - 2) : ℝ) *
      ((Annealed.sigmaBar M m : ℝ))⁻¹ - 1)
    linarith only [hfive, hnn]
  -- square the display
  set A : ℝ := C * min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
      (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) *
    (3 : ℝ) ^ (M.gamma * (((m : ℝ) - (j : ℝ)) + 2)) with hA
  have hsq : ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ - 1) ^ 2 ≤
      A ^ 2 := by
    rw [← sq_abs ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ - 1)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hAsq : A ^ 2 =
      C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
          (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
        (3 : ℝ) ^ (2 * (M.gamma * (((m : ℝ) - (j : ℝ)) + 2))) := by
    rw [hA, mul_pow, mul_pow, rpow_sq]
  refine le_trans hsq ?_
  rw [hAsq]
  -- the index shift and the constant
  have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  have hexp : (3 : ℝ) ^ (2 * (M.gamma * (((m : ℝ) - (j : ℝ)) + 2))) =
      (3 : ℝ) ^ (4 * M.gamma) * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) :=
    rpow_two_gamma_shift M.gamma ((m : ℝ) - (j : ℝ))
  have hpow : (3 : ℝ) ^ (2 * (M.gamma * (((m : ℝ) - (j : ℝ)) + 2))) ≤
      2 * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) := by
    rw [hexp]
    exact mul_le_mul_of_nonneg_right (three_rpow_four_gamma_le_two hgam) hbase
  have hK : (0 : ℝ) ≤ C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
      (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 :=
    mul_nonneg (sq_nonneg C) (sq_nonneg _)
  have hstep : C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
      (3 : ℝ) ^ (2 * (M.gamma * (((m : ℝ) - (j : ℝ)) + 2))) ≤
      C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
      (2 * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ))))) :=
    mul_le_mul_of_nonneg_left hpow hK
  have hCmax : 2 * C ^ 2 ≤ max C (2 * C ^ 2) := le_max_right _ _
  have hfinal : 2 * C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) ≤
      max C (2 * C ^ 2) * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCmax (sq_nonneg _)) hbase
  calc C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
          (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
        (3 : ℝ) ^ (2 * (M.gamma * (((m : ℝ) - (j : ℝ)) + 2)))
      ≤ C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
          (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
          (2 * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ))))) := hstep
    _ = 2 * C ^ 2 * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
          (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) := by ring
    _ ≤ max C (2 * C ^ 2) * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
          (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) := hfinal

/-! ## B2 with `E` absorbed into a power of `γ` -/

/-- **`E² γ ≤ γ^{3/5}`**, from the printed regime `γ ≤ E^{-10}` and `1 ≤ E` alone,
through the proved `E`-window `E ≤ γ^{-1/5}`. -/
private theorem esq_mul_gamma_le_rpow (M : ABKModel d) {E : {E : ℝ // 1 ≤ E}}
    (hreg : M.gamma ≤ (((E : ℝ))⁻¹) ^ 10) :
    (E : ℝ) ^ 2 * M.gamma ≤ M.gamma ^ ((3 : ℝ) / 5) := by
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hE0 : (0 : ℝ) ≤ (E : ℝ) := le_trans zero_le_one E.2
  have hE := GoodEvents.le_rpow_neg_fifth_of_regime M hreg
  have h1 : (E : ℝ) ^ 2 ≤ (M.gamma ^ (-(1 / 5 : ℝ))) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have h2 : (M.gamma ^ (-(1 / 5 : ℝ))) ^ (2 : ℕ) = M.gamma ^ (-(2 / 5 : ℝ)) := by
    rw [← Real.rpow_natCast (M.gamma ^ (-(1 / 5 : ℝ))) 2, ← Real.rpow_mul hg0.le]
    congr 1
    push_cast
    ring
  have h3 : M.gamma ^ (-(2 / 5 : ℝ)) * M.gamma = M.gamma ^ ((3 : ℝ) / 5) := by
    nth_rewrite 2 [← Real.rpow_one M.gamma]
    rw [← Real.rpow_add hg0]
    congr 1
    norm_num
  calc (E : ℝ) ^ 2 * M.gamma ≤ M.gamma ^ (-(2 / 5 : ℝ)) * M.gamma := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_right h1 hg0.le
    _ = M.gamma ^ ((3 : ℝ) / 5) := h3

/-- **(B2), `E`-free.**  The squared continuity display at the shifted pair with
the budget `E` absorbed: `E² γ |log γ|² ≤ γ^{3/5} |log γ|²`.

The two structural binders (the landmark gate and the induction state) remain,
because `l.shom.continuity` genuinely needs them; only the `E` occurring in the
display is removed. -/
theorem exists_sigmaBar_ratio_sub_one_sq_le_gammaAbsorbed (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        M.gamma ≤ 1 / 8 →
        ∀ m j : ℤ, j - 2 ≤ m → m ≤ m0 →
          ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (j - 2) : ℝ))⁻¹ - 1) ^ 2 ≤
            C * (min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
                  M.gamma ^ ((3 : ℝ) / 5) * |Real.log M.gamma| ^ 2)) ^ 2 *
              (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) := by
  obtain ⟨C, hC0, hbase⟩ := exists_sigmaBar_ratio_sub_one_sq_le d
  refine ⟨C, hC0, ?_⟩
  intro M m0 E hm0 hstate hCE hreg hgam m j hjm hm
  refine le_trans (hbase M m0 E hm0 hstate hCE hreg hgam m j hjm hm) ?_
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have habs : (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) ≤
      M.gamma ^ ((3 : ℝ) / 5) * |Real.log M.gamma| ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_right (esq_mul_gamma_le_rpow M hreg)
      (sq_nonneg |Real.log M.gamma|)
    calc (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)
        = (E : ℝ) ^ 2 * M.gamma * |Real.log M.gamma| ^ 2 := by ring
      _ ≤ M.gamma ^ ((3 : ℝ) / 5) * |Real.log M.gamma| ^ 2 := hstep
  have hmin0 : (0 : ℝ) ≤ min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
      (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) := by
    have hjm' : (0 : ℝ) ≤ ((m : ℝ) - (j : ℝ)) + 2 := by
      have hcast : ((j : ℝ) - 2) ≤ (m : ℝ) := by exact_mod_cast hjm
      linarith only [hcast]
    refine le_min (by norm_num) ?_
    have h1 : (0 : ℝ) ≤ M.gamma * (((m : ℝ) - (j : ℝ)) + 2) := mul_nonneg hg0.le hjm'
    have h2 : (0 : ℝ) ≤ (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg hg0.le (sq_nonneg _))
    linarith only [h1, h2]
  have hmin : min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
        (E : ℝ) ^ 2 * (M.gamma * |Real.log M.gamma| ^ 2)) ≤
      min 1 (M.gamma * (((m : ℝ) - (j : ℝ)) + 2) +
        M.gamma ^ ((3 : ℝ) / 5) * |Real.log M.gamma| ^ 2) :=
    min_le_min le_rfl (by linarith only [habs])
  have hbasepow : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (j : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmin0 hmin 2) hC0.le) hbasepow

end

end Algsuperdiff.Section4.Provider.BoundsEaL
