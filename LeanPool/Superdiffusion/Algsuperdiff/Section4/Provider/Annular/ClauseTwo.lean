/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ClauseOneConditional
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Translate

/-!
# ClauseTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `In particular` bridge: clause (ii) of the annular decomposition

The Section 4.1 proposition ends with an `In particular` clause that the
manuscript never derives: on the good event `𝒢(m; s, ε)` and under a smallness
condition on `γ|log γ|²`, the *unsquared* flux-corrected error is at most `Cε`.

> `𝒢₂` bounds the first right-hand term of (i) by `Cε²`, `𝒢₁`'s two conditions
> bound the third and fourth by `C s^{−2} c⋆^{−1} γ · (s ε c⋆^{1/2} γ^{−1/2})²
> = Cε²`, and the smallness condition handles the second.

## The four term budgets

* `ofReal_mul_clauseOneTermOne_le_of_eventG2` — `𝒢₂`'s bracket carries the
  weight `3^{−(s/4)(m−n)}`, the display carries `3^{−s(m−n)}`, so the display
  term is *below* the event's own sum and `s · (term one) ≤ ε²` with no loss.
* With the printed `ℓ²` third term this step would still work, but clause (i)
  itself would not; see the graph's `[G-7]` note.
* `clauseOneTermFour_le_of_eventG1` — the display weight `3^{−(s/2)(m−n)}` is
  below `𝒢₁`'s `3^{−(s/4)(m−n)}` slot by slot.
* The printed hypothesis `γ|log γ|² ≤ s c⋆² ε` gives only `s² c⋆⁴ ε²` and does
  **not** suffice.

## Wrinkle (b): the silent square root

Clause (i) bounds the *squared* supremum over `L ≥ m`; clause (ii) is unsquared.
`indicator_observableSup_le_of_sqSup` takes the square root sample by sample:
a bound `B` on `⨆_L ofReal(𝓔_L²)` gives the bound `√B` on `⨆_L ofReal(𝓔_L)`,
because each representative is nonnegative.  Since the total budget is
`4 C ε²`, the clause-(ii) constant is `2√C`.

## The event

Clause (ii) is stated on `Frozen.Section4.goodEventAt M Ccg m 0 s ε`, which is
by definition `Cutoff.translateCutoffSample 0 ⁻¹' Support.goodEventBase …`;
`goodEventBase_eq_translateZero_preimage` records that this is
`Support.goodEventBase M Ccg m s ε` itself, so the event carried below is the
frozen one at `y = 0`.  (The frozen module is never imported.)
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the clause-(i) right-hand side as a named object -/

/-- The four-term right-hand side of the clause-(i) representative display, at
the output constant `C`.  This is *definitionally* the right-hand side of
`DisplaySlots.clauseOne_representative_display_latticeMax`; it is a naming
convenience inside this provider module and closes no node. -/
def clauseOneDisplayRhs (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s}) (C : ℝ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ENNReal.ofReal (C * (s : ℝ)) * clauseOneTermOne M m s omega
    + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
        * M.gamma ^ 2 * |Real.log M.gamma| ^ 4)
    + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
      * clauseOneTermThree M m omega
    + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
      * clauseOneTermFour M m s omega

theorem clauseOneDisplayRhs_eq (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (C : ℝ) (omega : Cutoff.CutoffSample d) :
    clauseOneDisplayRhs M m s C omega
      = ENNReal.ofReal (C * (s : ℝ)) * clauseOneTermOne M m s omega
        + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
            * M.gamma ^ 2 * |Real.log M.gamma| ^ 4)
        + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
          * clauseOneTermThree M m omega
        + ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
          * clauseOneTermFour M m s omega :=
  rfl

/-- The display is monotone in its output constant. -/
theorem clauseOneDisplayRhs_mono (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) {C C' : ℝ} (hCC : C ≤ C') :
    clauseOneDisplayRhs M m s C omega ≤ clauseOneDisplayRhs M m s C' omega := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hc0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsinv : (0 : ℝ) ≤ (s : ℝ)⁻¹ := (inv_pos.2 hs0).le
  have hcinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.2 hc0).le
  have h1 : C * (s : ℝ) ≤ C' * (s : ℝ) := mul_le_mul_of_nonneg_right hCC hs0.le
  have hA2 : (0 : ℝ) ≤ ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
      * M.gamma ^ 2 * |Real.log M.gamma| ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hsinv 3) (pow_nonneg hcinv 4))
      (sq_nonneg _)) (pow_nonneg (abs_nonneg _) 4)
  have hA3 : (0 : ℝ) ≤ ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma :=
    mul_nonneg (mul_nonneg (pow_nonneg hsinv 2) hcinv) hg0.le
  have h2 : C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
        * M.gamma ^ 2 * |Real.log M.gamma| ^ 4
      ≤ C' * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
        * M.gamma ^ 2 * |Real.log M.gamma| ^ 4 := by
    have hL : C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
        * M.gamma ^ 2 * |Real.log M.gamma| ^ 4
        = C * (((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
          * M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := by ring
    have hR : C' * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
        * M.gamma ^ 2 * |Real.log M.gamma| ^ 4
        = C' * (((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
          * M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hCC hA2
  have h3 : C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma
      ≤ C' * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma := by
    have hL : C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma
        = C * (((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) := by ring
    have hR : C' * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma
        = C' * (((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma) := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hCC hA3
  unfold clauseOneDisplayRhs
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h1) _
  · exact ENNReal.ofReal_le_ofReal h2
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h3) _
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h3) _

/-! ## Part B -- the three event budgets -/

/-- **The first term, from `𝒢₂`.**  The display weight `3^{−s(m−n)}` sits below
the event weight `3^{−(s/4)(m−n)}` on the annular region `n ≤ j − 1 ≤ m − 1`, so
`s ·` (term one) is bounded by the event's own threshold `ε²`. -/
theorem ofReal_mul_clauseOneTermOne_le_of_eventG2 (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {ep : ℝ} {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG2 M m s ep) :
    ENNReal.ofReal (s : ℝ) * clauseOneTermOne M m s omega
      ≤ ENNReal.ofReal (ep ^ 2) := by
  refine le_trans (mul_le_mul_right ?_ _)
    ((Support.mem_eventG2_iff M m s ep omega).mp homega)
  refine ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun n => ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hq : (0 : ℝ) ≤ ((m - n.1 : ℤ) : ℝ) := by
    have hz : (0 : ℤ) ≤ m - n.1 := by
      have hj := j.2
      have hn := n.2
      omega
    exact_mod_cast hz
  have hpos : (0 : ℝ) ≤ (3 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) s.2.le) hq
  have hid : -(s : ℝ) * ((m - n.1 : ℤ) : ℝ)
      = -(1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ)
        - (3 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ) := by ring
  linarith only [hid, hpos]

theorem clauseOneTermThree_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    (hT : 0 ≤ T) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) :
    clauseOneTermThree M m omega ≤ ENNReal.ofReal (T ^ 2) := by
  rw [ENNReal.ofReal_pow hT]
  exact ENNReal.pow_le_pow_left homega.1

/-- **The fourth term, from `𝒢₁`'s second condition.**  The display weight
`3^{−(s/2)(m−n)}` sits below the event weight `3^{−(s/4)(m−n)}` slot by slot;
the inner `k`-blocks are literally the same. -/
theorem clauseOneTermFour_le_of_eventG1 (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {T : ℝ} {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m (s : ℝ) T) :
    clauseOneTermFour M m s omega ≤ ENNReal.ofReal (T ^ 2) := by
  refine le_trans ?_ homega.2
  refine ENNReal.tsum_le_tsum fun n => ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hq : (0 : ℝ) ≤ ((m - n.1 : ℤ) : ℝ) := by
    have hz : (0 : ℤ) ≤ m - n.1 := by
      have hn := n.2
      omega
    exact_mod_cast hz
  have hpos : (0 : ℝ) ≤ (1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) s.2.le) hq
  have hid : -(1 / 2 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ)
      = -(1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ)
        - (1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ) := by ring
  linarith only [hid, hpos]

/-! ## Part C -- the total budget on the good event -/

/-- **The clause-(i) right-hand side on the good event is at most `4 C ε²`.**

The printed hypothesis `γ|log γ|² ≤ s c⋆² ε` would give only `γ²|log γ|⁴ ≤ s²
c⋆⁴ ε²`, one power of `s` short of the corrected `s^{−3}`. -/
theorem clauseOneDisplayRhs_le_of_goodEventBase (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {ep C : ℝ} (hC0 : 0 ≤ C) (hep0 : 0 ≤ ep)
    (hsmall : M.gamma * |Real.log M.gamma| ^ 2
      ≤ (s : ℝ) ^ (3 / 2 : ℝ) * Disorder.cstar M ^ 2 * ep)
    {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Support.goodEventBase M Ccg m s ep) :
    clauseOneDisplayRhs M m s C omega ≤ ENNReal.ofReal (4 * C * ep ^ 2) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hc0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs0
  have hcne : Disorder.cstar M ≠ 0 := ne_of_gt hc0
  have hgne : M.gamma ≠ 0 := ne_of_gt hg0
  have hsinv : (0 : ℝ) ≤ (s : ℝ)⁻¹ := (inv_pos.2 hs0).le
  have hcinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.2 hc0).le
  have hG1 := Support.goodEventBase_subset_eventG1 M Ccg m s ep hmem
  have hG2 := Support.goodEventBase_subset_eventG2 M Ccg m s ep hmem
  have hT0 : (0 : ℝ) ≤ (s : ℝ) * ep * Real.sqrt (Disorder.cstar M)
      * (Real.sqrt M.gamma)⁻¹ := goodEventAmplitude_nonneg M s hep0
  have hCep : (0 : ℝ) ≤ C * ep ^ 2 := mul_nonneg hC0 (sq_nonneg _)
  -- term one
  have h1 : ENNReal.ofReal (C * (s : ℝ)) * clauseOneTermOne M m s omega
      ≤ ENNReal.ofReal (C * ep ^ 2) := by
    calc ENNReal.ofReal (C * (s : ℝ)) * clauseOneTermOne M m s omega
        = ENNReal.ofReal C * (ENNReal.ofReal (s : ℝ) * clauseOneTermOne M m s omega) := by
          rw [ENNReal.ofReal_mul hC0, mul_assoc]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ep ^ 2) :=
          mul_le_mul_right (ofReal_mul_clauseOneTermOne_le_of_eventG2 M m s hG2) _
      _ = ENNReal.ofReal (C * ep ^ 2) := (ENNReal.ofReal_mul hC0).symm
  have h2 : ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
        * M.gamma ^ 2 * |Real.log M.gamma| ^ 4)
      ≤ ENNReal.ofReal (C * ep ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hlhs0 : (0 : ℝ) ≤ M.gamma * |Real.log M.gamma| ^ 2 :=
      mul_nonneg hg0.le (sq_nonneg _)
    have hsq := pow_le_pow_left₀ hlhs0 hsmall 2
    have hpow : ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = (s : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast ((s : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hs0.le,
        show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hlsq : (M.gamma * |Real.log M.gamma| ^ 2) ^ 2
        = M.gamma ^ 2 * |Real.log M.gamma| ^ 4 := by ring
    have hrsq : ((s : ℝ) ^ (3 / 2 : ℝ) * Disorder.cstar M ^ 2 * ep) ^ 2
        = (s : ℝ) ^ (3 : ℕ) * Disorder.cstar M ^ (4 : ℕ) * ep ^ 2 := by
      calc ((s : ℝ) ^ (3 / 2 : ℝ) * Disorder.cstar M ^ 2 * ep) ^ 2
          = ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) * Disorder.cstar M ^ (4 : ℕ)
              * ep ^ 2 := by ring
        _ = (s : ℝ) ^ (3 : ℕ) * Disorder.cstar M ^ (4 : ℕ) * ep ^ 2 := by rw [hpow]
    rw [hlsq, hrsq] at hsq
    have hk0 : (0 : ℝ) ≤ C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)) :=
      mul_nonneg (mul_nonneg hC0 (pow_nonneg hsinv 3)) (pow_nonneg hcinv 4)
    calc C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ))
            * M.gamma ^ 2 * |Real.log M.gamma| ^ 4
        = (C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)))
            * (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) := by ring
      _ ≤ (C * ((s : ℝ)⁻¹ ^ (3 : ℕ)) * ((Disorder.cstar M)⁻¹ ^ (4 : ℕ)))
            * ((s : ℝ) ^ (3 : ℕ) * Disorder.cstar M ^ (4 : ℕ) * ep ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hk0
      _ = C * ep ^ 2 := by field_simp
  -- the shared coefficient of terms three and four
  have hK0 : (0 : ℝ) ≤ C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (pow_nonneg hsinv 2)) hcinv) hg0.le
  have hKT : (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
      * ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ^ 2
      = C * ep ^ 2 := by
    rw [goodEventAmplitude_sq M s ep]
    field_simp
  -- term three
  have h3 : ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
        * clauseOneTermThree M m omega
      ≤ ENNReal.ofReal (C * ep ^ 2) := by
    calc ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
            * clauseOneTermThree M m omega
        ≤ ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
            * ENNReal.ofReal (((s : ℝ) * ep * Real.sqrt (Disorder.cstar M)
              * (Real.sqrt M.gamma)⁻¹) ^ 2) :=
          mul_le_mul_right (clauseOneTermThree_le_of_eventG1 M m hT0 hG1) _
      _ = ENNReal.ofReal ((C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
            * ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M)
              * (Real.sqrt M.gamma)⁻¹) ^ 2) := (ENNReal.ofReal_mul hK0).symm
      _ = ENNReal.ofReal (C * ep ^ 2) := by rw [hKT]
  -- term four
  have h4 : ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
        * clauseOneTermFour M m s omega
      ≤ ENNReal.ofReal (C * ep ^ 2) := by
    calc ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
            * clauseOneTermFour M m s omega
        ≤ ENNReal.ofReal (C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
            * ENNReal.ofReal (((s : ℝ) * ep * Real.sqrt (Disorder.cstar M)
              * (Real.sqrt M.gamma)⁻¹) ^ 2) :=
          mul_le_mul_right (clauseOneTermFour_le_of_eventG1 M m s hG1) _
      _ = ENNReal.ofReal ((C * ((s : ℝ)⁻¹ ^ (2 : ℕ)) * (Disorder.cstar M)⁻¹ * M.gamma)
            * ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M)
              * (Real.sqrt M.gamma)⁻¹) ^ 2) := (ENNReal.ofReal_mul hK0).symm
      _ = ENNReal.ofReal (C * ep ^ 2) := by rw [hKT]
  have hfour : ENNReal.ofReal (C * ep ^ 2) + ENNReal.ofReal (C * ep ^ 2)
      + ENNReal.ofReal (C * ep ^ 2) + ENNReal.ofReal (C * ep ^ 2)
      = ENNReal.ofReal (4 * C * ep ^ 2) := by
    rw [← ENNReal.ofReal_add hCep hCep,
      ← ENNReal.ofReal_add (by linarith only [hCep]) hCep,
      ← ENNReal.ofReal_add (by linarith only [hCep]) hCep]
    congr 1
    ring
  unfold clauseOneDisplayRhs
  exact le_trans (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) (le_of_eq hfour)

/-! ## Part D -- wrinkle (b): the silent square root -/

/-- `√(4 C ε²) = 2 √C ε`. -/
theorem sqrt_four_mul_sq {C ep : ℝ} (hC0 : 0 ≤ C) (hep0 : 0 ≤ ep) :
    Real.sqrt (4 * C * ep ^ 2) = 2 * Real.sqrt C * ep := by
  have hs : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC0
  have h : (2 * Real.sqrt C * ep) ^ 2 = 4 * C * ep ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  rw [← h, Real.sqrt_sq (mul_nonneg (by positivity) hep0)]

/-- **Wrinkle (b), made honest.**  A bound on the indicator of the *squared*
supremum gives the square root bound on the indicator of the plain supremum,
sample by sample, because each flux-corrected representative is nonnegative. -/
theorem indicator_observableSup_le_of_sqSup (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {Event : Set (Cutoff.CutoffSample d)}
    {omega : Cutoff.CutoffSample d} {B : ℝ} (hB : 0 ≤ B)
    (h : Set.indicator Event (Support.fluxCorrectedErrorObservableSqSup M m s) omega
      ≤ ENNReal.ofReal B) :
    Set.indicator Event (Support.fluxCorrectedErrorObservableSup M m s) omega
      ≤ ENNReal.ofReal (Real.sqrt B) := by
  classical
  by_cases hmem : omega ∈ Event
  · rw [Set.indicator_of_mem hmem] at h ⊢
    refine Support.fluxCorrectedErrorObservableSup_le M m s omega ?_
    intro L hL
    have hLle : ENNReal.ofReal
        (Support.fluxCorrectedErrorRepresentative M L m s omega ^ 2)
        ≤ ENNReal.ofReal B := by
      refine le_trans ?_ h
      exact le_iSup (fun L : {L : ℤ // m ≤ L} => ENNReal.ofReal
        (Support.fluxCorrectedErrorRepresentative M L.1 m s omega ^ 2)) ⟨L, hL⟩
    have hreal : Support.fluxCorrectedErrorRepresentative M L m s omega ^ 2 ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hB).mp hLle
    refine ENNReal.ofReal_le_ofReal ?_
    calc Support.fluxCorrectedErrorRepresentative M L m s omega
        = Real.sqrt (Support.fluxCorrectedErrorRepresentative M L m s omega ^ 2) :=
          (Real.sqrt_sq
            (Support.fluxCorrectedErrorRepresentative_nonneg M L m s omega)).symm
      _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hreal
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le

/-! ## Part E -- the `In particular` bridge -/

/-- The frozen clause-(ii) event `goodEventAt M Ccg m 0 s ε` unfolds to
`Support.goodEventBase M Ccg m s ε`: translating by `0` is the identity.  The
frozen module is not imported; this records the identification at the level of
its definitional body. -/
theorem goodEventBase_eq_translateZero_preimage (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Cutoff.translateCutoffSample (0 : Vec d) ⁻¹'
        Support.goodEventBase M Ccg m s ep
      = Support.goodEventBase M Ccg m s ep :=
  Algsuperdiff.Section4.Provider.GoodEvents.preimage_translateCutoffSample_zero _

end

end Algsuperdiff.Section4.Provider.Annular
