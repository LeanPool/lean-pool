/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorClause
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReplacementDatumHarmonic

/-!
# InteriorGlue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior clause's glue: the frame containment, the `s`-envelope of the
# correction, and the correction leg in the anchor's own carriers

Three of the four glue items the interior-clause assembly was priced with.

* **the frame containment** (`translateSet_cubeSet_subset_of_anchorGeometry`) —
  the frozen theorem's geometry binder gives the *half-open* containment `(x−z)
  + □_n ⊆ □_{n+2}` that the proved off-grid stability cap
  (`ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot`) consumes.
  The open containment is `CaccioppoliInteriorGeometry`'s; the half-open one is
  proved here directly from the two coordinate windows — the arithmetic slack
  is a factor `9/4` per coordinate, so no boundary case arises.
* **, the `s`-envelope of the correction factor**
  (`negativeToL2Factor_le_rpow_neg_half`) — `(1 − 3^{−s})^{−1/2} ≤
  √(3/2)·s^{−1/2}` on `(0,1]`, through the chord bound `1 − 3^{−s} ≥ 2s/3`
  (convexity of `exp`, no `nlinarith`, no numerical `rpow` evaluation).
* **+ composed** (`correctionLeg_le_anchorGagliardo`) — the correction summand
  of the harmonic replacement's coarse-graining slot, written in
  the frozen theorem's own Gagliardo carrier on the translated window `w +
  □_n`, at the explicit `d`-only constant `interiorCorrectionConst d` and the
  honest `s`-power `s^{−1/2}`.

## The `s`-power of the correction leg, against the anchor's display

Dividing the harmonic display by its own prefactor `σ·3^{−n}` turns the bound
below into

```text
  σ^{-1} · interiorCorrectionConst d · s^{-1/2} · 3^{(1+s)n} · [g]_{H^s(w+□_n)} ,
```

which is exactly the *shape* of the frozen statement's second interior summand
`C s^{-7} σ_n^{-1} 3^{(1+s)n} [g]_{H^s(W)}`, with the `s`-power `−1/2` in place
of the printed `−7`: **stronger than printed**, and dominated by it on `(0,1]`.
Nothing is claimed at the printed power here; the weakening is the assembly's
arithmetic step.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the geometry binder and the
  interior clause); the forcing correction.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The frame containment, in the half-open realization -/

/-- **The anchor's geometry binder gives the half-open child-in-parent
containment.**

The proved off-grid stability cap is stated with `translateSet w (cubeSet P) ⊆
cubeSet K` — the *half-open* realizations, because the flux-corrected
ellipticity envelope of the parent is available pointwise there.  The frozen
theorem supplies the *open* containment `x + □_n ⊆ (z + □_{n+1}) ∩ □_m`; the
half-open one at the two-scale gap follows with room to spare (`2·3^n` against
the available `(9/2)·3^n`). -/
theorem translateSet_cubeSet_subset_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hsub : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    translateSet (x - z) (cubeSet (originCube d n)) ⊆
      cubeSet (originCube d (n + 2)) := by
  have hw : x - z ∈ openCubeSet (originCube d (n + 1)) :=
    sub_mem_openCubeSet_succ_of_anchorGeometry hsub
  rw [mem_openCubeSet_originCube_iff] at hw
  have h1 : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have h2 : (3 : ℝ) ^ (n + 2) = 3 ^ n * 9 := by
    have hn : n + 2 = n + 1 + 1 := by ring
    rw [hn, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), h1]
    ring
  have hpos : (0 : ℝ) < 3 ^ n := zpow_pos (by norm_num) n
  rintro p ⟨y, hy, rfl⟩
  rw [mem_cubeSet_originCube_iff] at hy ⊢
  intro i
  have hyi := hy i
  have hwi := hw i
  rw [h1] at hwi
  rw [h2]
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply] <;>
    linarith only [hyi.1, hyi.2, hwi.1, hwi.2, hpos]

/-! ## 2.: the honest `s`-envelope of the correction factor -/

/-- **The chord bound for `3^{−s}`.**

On `[0,1]`, `1 − 3^{−s} ≥ (2/3)s`: the convexity of `exp` against the chord
through `(0,1)` and `(1,1/3)`.  Equality holds at both endpoints. -/
theorem two_mul_div_three_le_one_sub_three_rpow_neg {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 2 * s / 3 ≤ 1 - Real.rpow (3 : ℝ) (-s) := by
  have hlog : Real.rpow (3 : ℝ) (-s) = Real.exp (Real.log 3 * (-s)) :=
    Real.rpow_def_of_pos (by norm_num) (-s)
  have hexpneg : Real.exp (-Real.log 3) = (3 : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (-Real.log 3)) (by linarith only [hs1] : (0 : ℝ) ≤ 1 - s) hs0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  rw [hexpneg] at hconv
  have harg : s * -Real.log 3 = Real.log 3 * -s := by ring
  rw [harg] at hconv
  rw [hlog]
  linarith only [hconv]

/-- **.**  The closed-form correction factor `(1 − 3^{−s})^{−1/2}` carried by
`ReplacementDatumHarmonic.negativeToL2Factor` obeys the honest envelope `√(3/2)
· s^{−1/2}` on `(0,1]`. -/
theorem negativeToL2Factor_le_rpow_neg_half {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    negativeToL2Factor s ≤ Real.sqrt (3 / 2) * Real.rpow s (-(1 / 2 : ℝ)) := by
  have hchord := two_mul_div_three_le_one_sub_three_rpow_neg hs.le hs1
  have hrw : geometricDiscount (s / 2) 2 = 1 - Real.rpow (3 : ℝ) (-s) := by
    rw [geometricDiscount]
    congr 2
    ring
  have hden : 0 < 2 * s / 3 := by linarith only [hs]
  have hinv : (geometricDiscount (s / 2) 2)⁻¹ ≤ (2 * s / 3)⁻¹ := by
    have h1 := one_div_le_one_div_of_le hden hchord
    rw [one_div, one_div] at h1
    rw [hrw]
    exact h1
  have hstep : negativeToL2Factor s ≤ Real.sqrt ((2 * s / 3)⁻¹) :=
    Real.sqrt_le_sqrt hinv
  refine hstep.trans (le_of_eq ?_)
  have hfac : (2 * s / 3)⁻¹ = (3 / 2 : ℝ) * s⁻¹ := by
    field_simp
  have hrpow : Real.rpow s (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_neg hs.le (1 / 2 : ℝ)
  rw [hfac, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2), Real.sqrt_inv, hrpow]

/-! ## 3. +: the correction leg in the anchor's Gagliardo carrier -/

/-- The `d`-only constant of the composed correction leg:
`2 C_neg(d) √(3/2) √d · C_BG(d)`. -/
def interiorCorrectionConst (d : ℕ) [NeZero d] : ℝ :=
  2 * negNormBaseConst d * Real.sqrt (3 / 2) *
    Real.sqrt (Fintype.card (Fin d) : ℝ) * besovGagliardoConstant d

theorem interiorCorrectionConst_pos (d : ℕ) [NeZero d] :
    0 < interiorCorrectionConst d := by
  have hneg : 0 < negNormBaseConst d := negNormBaseConst_pos d
  have hcard : (0 : ℝ) < (Fintype.card (Fin d) : ℝ) := by
    have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    rw [Fintype.card_fin]
    exact_mod_cast hd
  have hsq : 0 < Real.sqrt (Fintype.card (Fin d) : ℝ) := Real.sqrt_pos.mpr hcard
  have hbg : 0 < besovGagliardoConstant d := by
    rw [besovGagliardoConstant]
    have h1 : (0 : ℝ) < Real.rpow (3 : ℝ) ((d : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < Ch01.Legacy.wspVsBsppConstant d :=
      Ch01.Legacy.wspVsBsppConstant_pos d
    have h3 : (0 : ℝ) < (d : ℝ) := by
      have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
      exact_mod_cast hd
    positivity
  have h32 : (0 : ℝ) < Real.sqrt (3 / 2) := Real.sqrt_pos.mpr (by norm_num)
  rw [interiorCorrectionConst]
  positivity

/-- **The composed correction leg +.**

The correction summand of the harmonic display, read at the translated window
`w + □_n`, is bounded by

```text
  interiorCorrectionConst d · s^{-1/2} · 3^{s n} · [g]_{H^s(w+□_n)} ,
```

the frozen theorem's own Gagliardo object on the right.  The `s`-power is the
honest `−1/2`; the scale weight `3^{sn}` is the manuscript's own; the constant
is `d`-only and explicit.  Both hypotheses are the anchor's clause-(iv) data,
restricted to the window the leg is read at. -/
theorem correctionLeg_le_anchorGagliardo [NeZero d] (n : ℤ) {w : Vec d} {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) {g : Vec d → Vec d}
    (hL2 : MemLp g 2 (Support.normalizedVolumeMeasureOn
      ((fun y => w + y) '' openCubeSet (originCube d n))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => w + y) '' openCubeSet (originCube d n)))) :
    2 * negNormBaseConst d * negativeToL2Factor s *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
            (fun y => -g (y + w))) ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
        Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => w + y) '' openCubeSet (originCube d n)) s g).toReal := by
  have hbes := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (originCube d n) hs hs1 hL2 hW
  rw [cubeBesovScaleWeight_neg_originCube (d := d) n s] at hbes
  have hcard : (0 : ℝ) ≤ Real.sqrt (Fintype.card (Fin d) : ℝ) := Real.sqrt_nonneg _
  have hneg : (0 : ℝ) ≤ 2 * negNormBaseConst d := by
    have := negNormBaseConst_pos d
    linarith only [this]
  have hfac : (0 : ℝ) ≤ 2 * negNormBaseConst d * negativeToL2Factor s :=
    mul_nonneg hneg (negativeToL2Factor_nonneg s)
  have hgag : (0 : ℝ) ≤ (Support.normalizedGagliardoESeminormOn
      ((fun y => w + y) '' openCubeSet (originCube d n)) s g).toReal :=
    ENNReal.toReal_nonneg
  have hpow : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep1 : 2 * negNormBaseConst d * negativeToL2Factor s *
      (Real.sqrt (Fintype.card (Fin d) : ℝ) *
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
          (fun y => -g (y + w))) ≤
      2 * negNormBaseConst d * negativeToL2Factor s *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            (Support.normalizedGagliardoESeminormOn
              ((fun y => w + y) '' openCubeSet (originCube d n)) s g).toReal)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbes hcard) hfac
  refine hstep1.trans ?_
  have henv := negativeToL2Factor_le_rpow_neg_half hs hs1
  have hrest : (0 : ℝ) ≤ Real.sqrt (Fintype.card (Fin d) : ℝ) *
      (besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => w + y) '' openCubeSet (originCube d n)) s g).toReal) :=
    mul_nonneg hcard (mul_nonneg (mul_nonneg (besovGagliardoConstant_nonneg d) hpow) hgag)
  have hstep2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left henv hneg) hrest
  refine hstep2.trans (le_of_eq ?_)
  rw [interiorCorrectionConst]
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
