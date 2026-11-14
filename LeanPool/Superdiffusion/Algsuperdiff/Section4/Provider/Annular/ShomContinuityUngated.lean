/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ShomContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.InductionState

/-!
# ShomContinuityUngated

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `σ`-continuity *difference* in the shape §4.1 consumes it

ABK26, the display `e.shom.m.vs.shom.n` (the conclusion of `l.shom.continuity`)
and its §4.1 consumption inside `p.mathcalE.annular.decomp`, Step 3:

```
  sum_{n <= m} 3^{-s(m-n)} |σ_m σ_{n-2}^{-1} - 1|^2
    <= C sum_{n <= m} 3^{-s(m-n)}
         min{ γ(m-n) + c⋆^{-2} γ |log γ|^2 , 1 }^2 3^{2γ(m-n)} .
```

The per-`n` inequality behind that first step is the `hshom` slot of
`Provider.Annular.ClauseOne.clauseOne_bound`, and this module supplies it
*without* the Section 3 gate list.

## The four gates, and how each is discharged

The proved Section 3 statement
`Algsuperdiff.Section3.Provider.Localization.shom_continuity` delivers, as its
fifth conjunct, the **symmetrized** display

```
  |σ_m σ_n^{-1} - 1| + |σ_n σ_m^{-1} - 1|
      <= C min{1, γ(m-n) + E^2 γ |log γ|^2} 3^{γ(m-n)}
```

for `n <= m <= m₀`, behind four gates: the landmark `m** < m₀`, the induction
state `𝒮(m₀-1,E)`, the budget `C c⋆^{-1} <= E`, and the regime `γ <= E^{-10}`.
Here:

* **the landmark and the scale gate are free.**  `m₀` occurs in the statement
  only through `m <= m₀` and `m** < m₀`, and the conclusion does not mention
  `m₀` at all; so for the pair `(m,n)` at hand one takes
  `m₀ := max m (m** + 1)` (`exists_landmark_scale`).  No case split at the
  landmark, and no below-landmark σ fact, is needed: the choice is available
  for *every* `m`, including `m <= m**`.
* Its `C₀`-floor is what lets the budget constant of `l.shom.continuity` be
  requested by name.
* **the budget gate** `C_shc c⋆^{-1} <= E` is `mul_cstarInv_le_of_budget` at
  the floor `C₀ := C_shc`.
* **the regime** `γ <= E^{-10}` is returned with the state at the budget
  identity `E = C c⋆^{-1}`; the surviving hypothesis is the printed
  `γ <= C^{-10} c⋆^{10}`, which is the regime `p.induction.bounds` is stated
  under.

## `E^2` versus `c⋆^{-2}`, and the index orientation

The manuscript's Step-3 display is the Section 3 display "at `E ≍ c⋆^{-1}`".
That is a *two-sided* reading of the budget, and only the lower half
(`E >= C c⋆^{-1}`) is a hypothesis of `l.shom.continuity`; the upper half is
available here because the state is produced at the *identity*
`E = C c⋆^{-1}`, so `E^2 = C^2 (c⋆^2)^{-1}` exactly.  Since
`min{1, x + K z} <= K min{1, x + z}` for `K >= 1` and `x,z >= 0`
(`min_one_add_mul_le`), the printed `c⋆^{-2}`-bracket follows at the cost of
one further constant factor, and the `min` is preserved rather than discarded.

The Section 3 conjunct is symmetric in the two ratio defects, so no
orientation is lost: with `n <= m` it bounds `|σ_m σ_n^{-1} - 1|` and
`|σ_n σ_m^{-1} - 1|` simultaneously.  §4.1 needs the first, at the shifted
lower index `n-2` (the `σ_{n-2}` of the per-cube ugly estimate); `n <= m-1`
gives `n-2 <= m`, and `γ(m-(n-2)) = γ(m-n) + 2γ` is exactly the `+2γ` printed
inside the slot's bracket.  The leftover `3^{2γ}` from the same shift is
absorbed into the constant using `γ <= 1`.

## What is delivered

* `exists_sigmaBar_defect_ge` — the symmetrized display at every pair
  `n <= m`, under the printed regime alone, with the `min` intact and the
  bracket in `c⋆^{-2}` form.
* `exists_shomSlot_ge` — the squared, index-shifted, `min`-free form that is
  literally the `hshom` slot of `clauseOne_bound`.

## References

* ABK26, `l.shom.continuity` / `e.shom.m.vs.shom.n`; the §4.1 consumption.
* `p.induction.bounds`, (the terminal budget).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. Abstract-real arithmetic

Five one-purpose facts on opaque reals: no `Real.rpow`, `log` or `exp` atom is
ever exposed to a numeric tactic here. -/

/-- **The min survives a rescaling of its second entry.**
`min{1, x + K z} ≤ K · min{1, x + z}` for `x ≥ 0` and `K ≥ 1`.

This is what converts the printed `E^2`-bracket into the `c⋆^{-2}`-bracket
without throwing the `min` away. -/
private theorem min_one_add_mul_le {x z K : ℝ} (hx : 0 ≤ x) (hK : 1 ≤ K) :
    min 1 (x + K * z) ≤ K * min 1 (x + z) := by
  rcases le_total 1 (x + z) with h | h
  · have h1 : min (1 : ℝ) (x + z) = 1 := min_eq_left h
    have h2 : min (1 : ℝ) (x + K * z) ≤ 1 := min_le_left _ _
    rw [h1, mul_one]
    linarith only [h2, hK]
  · have h1 : min (1 : ℝ) (x + z) = x + z := min_eq_right h
    have h2 : min (1 : ℝ) (x + K * z) ≤ x + K * z := min_le_right _ _
    have h3 : 1 * x ≤ K * x := mul_le_mul_of_nonneg_right hK hx
    rw [h1]
    linarith only [h2, h3]

/-- **The constant transfer.**  A bound `S ≤ C_shc · min{1, x + y} · w` with
`y = K z` and `K ≥ 1` becomes `S ≤ C · min{1, x + z} · w` as soon as
`C_shc K ≤ C`. -/
private theorem defect_transfer {S x y z w Csh K C : ℝ} (hx : 0 ≤ x)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hCsh0 : 0 ≤ Csh) (hK1 : 1 ≤ K) (hy : y = K * z)
    (hC : Csh * K ≤ C) (hS : S ≤ Csh * min 1 (x + y) * w) :
    S ≤ C * min 1 (x + z) * w := by
  have h1 : min (1 : ℝ) (x + y) ≤ K * min 1 (x + z) := by
    rw [hy]
    exact min_one_add_mul_le hx hK1
  have hmin0 : (0 : ℝ) ≤ min 1 (x + z) :=
    le_min zero_le_one (by linarith only [hx, hz])
  have h2 : Csh * min 1 (x + y) ≤ Csh * (K * min 1 (x + z)) :=
    mul_le_mul_of_nonneg_left h1 hCsh0
  have h3 : Csh * K * min 1 (x + z) ≤ C * min 1 (x + z) :=
    mul_le_mul_of_nonneg_right hC hmin0
  have h4 : Csh * min 1 (x + y) ≤ C * min 1 (x + z) := by
    linarith only [h2, h3]
  calc S ≤ Csh * min 1 (x + y) * w := hS
    _ ≤ C * min 1 (x + z) * w := mul_le_mul_of_nonneg_right h4 hw

/-- **The index shift, squared.**  From `D ≤ C · min{1, g(q+2) + Z} · v` and
`v ≤ 9u`, with everything nonnegative, one gets the `min`-free squared bound in
exactly the shape of the `hshom` slot. -/
private theorem slot_square {D C g q Z u v : ℝ} (hC0 : 0 ≤ C) (hq : 0 ≤ q)
    (hg : 0 ≤ g) (hZ : 0 ≤ Z) (hv0 : 0 ≤ v) (hD0 : 0 ≤ D) (hv : v ≤ 9 * u)
    (hD : D ≤ C * min 1 (g * (q + 2) + Z) * v) :
    D ^ 2 ≤ (9 * C * g * q + 9 * C * (2 * g + Z)) ^ 2 * u ^ 2 := by
  have hgq : 0 ≤ g * q := mul_nonneg hg hq
  have hbr0 : 0 ≤ g * (q + 2) + Z := by
    have hsplit : g * (q + 2) = g * q + 2 * g := by ring
    linarith only [hsplit, hgq, hg, hZ]
  have hmin : min (1 : ℝ) (g * (q + 2) + Z) ≤ g * (q + 2) + Z := min_le_right _ _
  have hcoef0 : 0 ≤ C * (g * (q + 2) + Z) := mul_nonneg hC0 hbr0
  have s1 : C * min 1 (g * (q + 2) + Z) ≤ C * (g * (q + 2) + Z) :=
    mul_le_mul_of_nonneg_left hmin hC0
  have s2 : C * min 1 (g * (q + 2) + Z) * v ≤ C * (g * (q + 2) + Z) * v :=
    mul_le_mul_of_nonneg_right s1 hv0
  have s3 : C * (g * (q + 2) + Z) * v ≤ C * (g * (q + 2) + Z) * (9 * u) :=
    mul_le_mul_of_nonneg_left hv hcoef0
  have hDu : D ≤ (9 * C * g * q + 9 * C * (2 * g + Z)) * u := by
    linarith only [hD, s2, s3]
  have hsq := pow_le_pow_left₀ hD0 hDu 2
  rwa [mul_pow] at hsq

/-- **`3^(2γ) ≤ 9`** for `γ ≤ 1`. -/
private theorem three_rpow_two_mul_le_nine {g : ℝ} (hg1 : g ≤ 1) :
    (3 : ℝ) ^ (2 * g) ≤ 9 := by
  have hstep := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
    (show 2 * g ≤ 2 by linarith only [hg1])
  have h9 : (3 : ℝ) ^ (2 : ℝ) = 9 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  linarith only [hstep, h9]

/-- **Enlarging the regime constant strengthens the regime.** -/
private theorem regime_mono {g Ca Cb cs : ℝ} (hCa0 : 0 < Ca) (hab : Ca ≤ Cb)
    (hcs0 : 0 ≤ cs) (h : g ≤ (Cb⁻¹) ^ 10 * cs ^ 10) :
    g ≤ (Ca⁻¹) ^ 10 * cs ^ 10 := by
  refine h.trans ?_
  have hinv : Cb⁻¹ ≤ Ca⁻¹ := inv_anti₀ hCa0 hab
  have h10 : (Cb⁻¹) ^ 10 ≤ (Ca⁻¹) ^ 10 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (le_trans hCa0.le hab)) hinv 10
  exact mul_le_mul_of_nonneg_right h10 (pow_nonneg hcs0 10)

/-- **The printed regime forces `γ ≤ 1`**, given the proved `c⋆ ≤ 3/2` and a regime
constant above `6`. -/
private theorem gamma_le_one_of_regime {g C cs : ℝ} (hC : 6 ≤ C) (hcs0 : 0 ≤ cs)
    (hcs : cs ≤ 3 / 2) (h : g ≤ (C⁻¹) ^ 10 * cs ^ 10) : g ≤ 1 := by
  refine h.trans ?_
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hCinv0 : (0 : ℝ) ≤ C⁻¹ := (inv_nonneg.mpr hC0.le)
  rw [← mul_pow]
  refine pow_le_one₀ (mul_nonneg hCinv0 hcs0) ?_
  have h1 : cs ≤ C := by linarith only [hC, hcs]
  have h2 := mul_le_mul_of_nonneg_left h1 hCinv0
  rwa [inv_mul_cancel₀ (ne_of_gt hC0)] at h2

/-! ## 2. The landmark gate -/

/-- **The landmark and the scale gate cost nothing.**

`l.shom.continuity` quantifies over an auxiliary top scale `m₀` subject to
`m** < m₀` and `m ≤ m₀`, and its conclusion does not mention `m₀`.  Both
constraints are met at once by `m₀ := max m (m** + 1)`, for every `m` — in
particular below the landmark, where no separate base-plateau σ fact is
needed. -/
theorem exists_landmark_scale (M : ABKModel d) (m : ℤ) :
    ∃ m0 : ℤ, mStarStar M < m0 ∧ m ≤ m0 :=
  ⟨max m (mStarStar M + 1),
    lt_of_lt_of_le (by omega) (le_max_right m (mStarStar M + 1)),
    le_max_left _ _⟩

/-! ## 3. The de-gated defect display -/

/-- **`e.shom.m.vs.shom.n`, de-gated, with a caller-prescribed constant floor.**

For every requested threshold `C₀` there is a `C ≥ max 6 C₀`, depending only on
the dimension and on `C₀`, such that every model in the printed regime
`γ ≤ C^{-10} c⋆^{10}` satisfies, at *every* pair of integer scales `n ≤ m`,

```
  |σ_m σ_n^{-1} - 1| + |σ_n σ_m^{-1} - 1|
      ≤ C min{1, γ(m-n) + c⋆^{-2} γ|log γ|^2} 3^{γ(m-n)} .
```

No landmark, no scale gate, no induction-state premise, no budget parameter:
the bracket is the manuscript's Step-3 bracket, i.e. the printed `E^2` read at
`E ≍ c⋆^{-1}`, which is legitimate because the state is produced at the budget
*identity*. -/
theorem exists_sigmaBar_defect_ge (d : ℕ) (C₀ : ℝ) :
    ∃ C : ℝ, 6 ≤ C ∧ C₀ ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ m n : ℤ, n ≤ m →
          |(Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ - 1| +
              |(Annealed.sigmaBar M n : ℝ) *
                ((Annealed.sigmaBar M m : ℝ))⁻¹ - 1| ≤
            C * min 1 (M.gamma * ((m : ℝ) - (n : ℝ)) +
                (Disorder.cstar M ^ 2)⁻¹ *
                  (M.gamma * |Real.log M.gamma| ^ 2)) *
              (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
  obtain ⟨Csh, hCsh0, hcont⟩ :=
    Algsuperdiff.Section3.Provider.Localization.shom_continuity d
  obtain ⟨Cb, hCb6, hCbCsh, hall⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d Csh
  have hCb0 : (0 : ℝ) < Cb := lt_of_lt_of_le (by norm_num) hCb6
  have hCb1 : (1 : ℝ) ≤ Cb := by linarith only [hCb6]
  have hK1 : (1 : ℝ) ≤ Cb ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hCb1 2
    rwa [one_pow] at h
  refine ⟨max (max 6 C₀) (max Cb (Csh * Cb ^ 2)), ?_, ?_, ?_⟩
  · exact le_trans (le_max_left 6 C₀) (le_max_left _ _)
  · exact le_trans (le_max_right 6 C₀) (le_max_left _ _)
  intro M hreg m n hnm
  have hCbC : Cb ≤ max (max 6 C₀) (max Cb (Csh * Cb ^ 2)) :=
    le_trans (le_max_left Cb (Csh * Cb ^ 2)) (le_max_right _ _)
  have hCshCb : Csh * Cb ^ 2 ≤ max (max 6 C₀) (max Cb (Csh * Cb ^ 2)) :=
    le_trans (le_max_right Cb (Csh * Cb ^ 2)) (le_max_right _ _)
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hregP0 : M.gamma ≤ (Cb⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 :=
    regime_mono hCb0 hCbC hcs0.le hreg
  obtain ⟨E, hEval, hEreg, hstate⟩ := hall M hregP0
  obtain ⟨m0, hm0, hmm0⟩ := exists_landmark_scale M m
  have hCE : Csh * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    Algsuperdiff.Section4.Provider.GoodEvents.mul_cstarInv_le_of_budget M hEval
      hCbCsh
  obtain ⟨-, -, -, -, h5⟩ :=
    hcont M m0 E hm0 (hstate (m0 - 1)) hCE hEreg m n hnm hmm0
  have hE2 : ((E : ℝ)) ^ 2 = Cb ^ 2 * (Disorder.cstar M ^ 2)⁻¹ := by
    rw [hEval, mul_pow, inv_pow]
  have hx : (0 : ℝ) ≤ M.gamma * ((m : ℝ) - (n : ℝ)) := by
    have hmn : ((n : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast hnm
    have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    exact mul_nonneg hgam0.le (by linarith only [hmn])
  have hz : (0 : ℝ) ≤ (Disorder.cstar M ^ 2)⁻¹ *
      (M.gamma * |Real.log M.gamma| ^ 2) := by
    have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have h1 : (0 : ℝ) ≤ (Disorder.cstar M ^ 2)⁻¹ :=
      inv_nonneg.mpr (pow_nonneg hcs0.le 2)
    exact mul_nonneg h1 (mul_nonneg hgam0.le (sq_nonneg _))
  refine defect_transfer (K := Cb ^ 2) hx hz
    (Real.rpow_nonneg (by norm_num) _) hCsh0.le hK1 ?_ hCshCb h5
  rw [hE2]
  ring

/-! ## 4. The `hshom` slot -/

/-- **The `hshom` slot of `clauseOne_bound`, unconditional in the printed
regime, with a caller-prescribed constant floor.**

For every requested threshold `C₀` there is a `Cshom ≥ max 6 C₀`, depending
only on the dimension and on `C₀`, such that every model with
`γ ≤ Cshom^{-10} c⋆^{10}` satisfies, for all integer scales `n ≤ m - 1`,

```
  |σ_m σ_{n-2}^{-1} - 1|^2
    ≤ ( Cshom γ (m-n) + Cshom (2γ + c⋆^{-2} γ|log γ|^2) )^2 3^{2γ(m-n)} .
```

The `2γ` inside the bracket and the constant factor `9` inside `Cshom` are the
two halves of the index shift `n ↦ n-2`: `γ(m-(n-2)) = γ(m-n) + 2γ` in the
bracket, and `3^{2γ} ≤ 9` in the growth factor. -/
theorem exists_shomSlot_ge (d : ℕ) (C₀ : ℝ) :
    ∃ Cshom : ℝ, 6 ≤ Cshom ∧ C₀ ≤ Cshom ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (Cshom⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∀ m n : ℤ, n ≤ m - 1 →
          ((Annealed.sigmaBar M m : ℝ) *
              ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2 ≤
            (Cshom * M.gamma * ((m - n : ℤ) : ℝ) +
                Cshom * (2 * M.gamma +
                  (Disorder.cstar M ^ 2)⁻¹ *
                    (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2 *
              (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)) := by
  obtain ⟨C, hC6, hCC₀, hgen⟩ := exists_sigmaBar_defect_ge d C₀
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC6
  refine ⟨9 * C, by linarith only [hC6], by linarith only [hCC₀, hC6], ?_⟩
  intro M hreg m n hn
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hregGen : M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 :=
    regime_mono hC0 (by linarith only [hC6]) hcs0.le hreg
  have hgam1 : M.gamma ≤ 1 :=
    gamma_le_one_of_regime hC6 hcs0.le
      (Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M) hregGen
  -- the general display at the shifted lower index `n - 2`
  have hbase := hgen M hregGen m (n - 2) (by omega)
  have hcast : ((m : ℝ) - ((n - 2 : ℤ) : ℝ)) = ((m - n : ℤ) : ℝ) + 2 := by
    push_cast
    ring
  rw [hcast] at hbase
  -- keep the first summand only
  have habs :
      |(Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1| ≤
        C * min 1 (M.gamma * (((m - n : ℤ) : ℝ) + 2) +
            (Disorder.cstar M ^ 2)⁻¹ *
              (M.gamma * |Real.log M.gamma| ^ 2)) *
          (3 : ℝ) ^ (M.gamma * (((m - n : ℤ) : ℝ) + 2)) :=
    le_trans (le_add_of_nonneg_right (abs_nonneg _)) hbase
  -- the growth factor of the shift
  have hq0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast this
  have hu0 : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hv : (3 : ℝ) ^ (M.gamma * (((m - n : ℤ) : ℝ) + 2)) ≤
      9 * (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) := by
    have hsplit : (3 : ℝ) ^ (M.gamma * (((m - n : ℤ) : ℝ) + 2)) =
        (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) * (3 : ℝ) ^ (2 * M.gamma) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    calc (3 : ℝ) ^ (M.gamma * (((m - n : ℤ) : ℝ) + 2))
        = (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) * (3 : ℝ) ^ (2 * M.gamma) :=
          hsplit
      _ ≤ (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) * 9 :=
          mul_le_mul_of_nonneg_left (three_rpow_two_mul_le_nine hgam1) hu0
      _ = 9 * (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) := by ring
  have hZ0 : (0 : ℝ) ≤ (Disorder.cstar M ^ 2)⁻¹ *
      (M.gamma * |Real.log M.gamma| ^ 2) :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hcs0.le 2))
      (mul_nonneg hgam0.le (sq_nonneg _))
  have hfin := slot_square (C := C) (g := M.gamma) (q := ((m - n : ℤ) : ℝ))
    (Z := (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2))
    (u := (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)))
    hC0.le hq0 hgam0.le hZ0
    (Real.rpow_nonneg (by norm_num) _) (abs_nonneg _) hv habs
  have hu2 : ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  rw [hu2, sq_abs] at hfin
  exact hfin

end

end Algsuperdiff.Section4.Provider.Annular
