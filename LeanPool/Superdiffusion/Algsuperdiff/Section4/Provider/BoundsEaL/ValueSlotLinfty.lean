/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.ValueSlotMoment

/-!
# ValueSlotLinfty

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# B6, second half: the `L∞` leg of the `L`-free value slot

## What this module does

`ShellSlotBounds.lFreeValueSlot` has two summands.

```
‖k_m − k_{j−2}‖_{L∞(3^j v + □_j)}
    =  Cutoff.localCubeControl j (translate (3^j v) (shellIncrement ω (j−2) m)) .
```

It is settled here by ONE application of the proved covering-plus-maximum
machinery of `Stream/LargeCubeLinfty.lean` (ABK26's `e.km.kn.Linfty`), read at
the index triple `(n, m, l) = (j−2, m, j)` and at the translated centre `3^j
v`: the cube `3^j v + □_j` is covered by `(2·3^{3} + 1)^d` translates of cubes
of scale `j − 2`, on each of which the proved small-cube bound
`Stream.translatedIncrementSupBound` applies at the SAME amplitude as at the
origin (one-shell stationarity, `TranslatedTransport.lean`).  Because `l − n =
2`, the maximum lemma's `(log N)^{1/2}` factor is a pure `d`-constant.

The covering family, the rounding argument and the count are the proved
`subcubeShifts`/`exists_subcubeShift_mem`/`three_mul_max_one_log_card_subcubeShifts_le`;
only the base point is new, and it is a silent parameter throughout
(`translatedLargeCubeSupBound` below is the proved `largeCubeSupBound` with
each covering centre shifted by `z`).

## The honest display, and how it differs from the printed one

The proved amplitude at `(n, m) = (j−2, m)` carries `min{γ^{-1/2}, (m − j +
2)^{1/2}}`, NOT the printed `min{γ^{-1/2}, (m−j)^{1/2}}`.  The two differ only
by a constant when `j ≤ m − 1`, but at the endpoint `j = m` the printed minimum
is `0` while the left-hand side contains the nondegenerate block `k_m −
k_{m−2}`.  The display proved here is therefore

```
‖k_m − k_{j−2}‖_{L∞(3^j v + □_j)}
    = 𝒪_{Γ₂}( C(d) ( 1 + min{γ^{-1/2}, (m−j)^{1/2}} ) 3^{γ m} ) ,
```

with the additive `1` that the endpoint forces.

## References

* ABK26, (`e.km.kn.Linfty`), (`e.km.kn.Linfty.smallcube`),
  (`e.k.ell.upscales.infty`), (bullet (B6), second half).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## 1. The covering maximum at a translated centre -/

/-- The proved covering maximum of `Stream/LargeCubeLinfty.lean` with every
covering centre shifted by `z`: the single random variable dominating `‖k_m −
k_n‖_{L∞(z + □_l)}`. -/
def translatedLargeCubeSupBound (z : Vec d) (l n m : ℤ) (omega : Cutoff.ShellSeq d) : ℝ :=
  (subcubeShifts d n l).sup' (subcubeShifts_nonempty d n l)
    fun p => translatedIncrementSupBound (subcubeCenter n p + z) n m omega

theorem translatedLargeCubeSupBound_nonneg (z : Vec d) (l n m : ℤ)
    (omega : Cutoff.ShellSeq d) : 0 ≤ translatedLargeCubeSupBound z l n m omega := by
  obtain ⟨p, hp⟩ := subcubeShifts_nonempty d n l
  refine le_trans (translatedIncrementSupBound_nonneg (subcubeCenter n p + z) n m omega) ?_
  exact Finset.le_sup' (fun q : Fin d → ℤ =>
    translatedIncrementSupBound (subcubeCenter n q + z) n m omega) hp

/-- **The deterministic half at a translated centre.**  At every point of
`z + □_l` the finite stream increment is dominated by the covering maximum. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_translatedLargeCubeSupBound
    (z : Vec d) (omega : Cutoff.ShellSeq d) (l n m : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d l)) :
    matrixOperatorNorm (Cutoff.finiteShellIncrement omega n m (x + z)) ≤
      translatedLargeCubeSupBound z l n m omega := by
  obtain ⟨p, hp, hmem⟩ := exists_subcubeShift_mem (d := d) n l hx
  rw [mem_translateSet_iff_sub_mem] at hmem
  have hvec : x + z - (subcubeCenter n p + z) = x - subcubeCenter n p := by
    funext i
    show x i + z i - (subcubeCenter n p i + z i) = x i - subcubeCenter n p i
    ring
  have hmem' : x + z ∈
      translateSet (subcubeCenter n p + z) (openCubeSet (originCube d n)) := by
    rw [mem_translateSet_iff_sub_mem, hvec]
    exact hmem
  refine le_trans
    (matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
      (subcubeCenter n p + z) omega n m hmem') ?_
  exact Finset.le_sup' (fun q : Fin d → ℤ =>
    translatedIncrementSupBound (subcubeCenter n q + z) n m omega) hp

/-- **The probabilistic half at a translated centre**, at the amplitude of the
proved centred display: each member of the shifted cover is itself a translated
small cube, so `isBigOWith_gammaSigma_translatedIncrementSupBound` prices it. -/
theorem isBigOWith_gammaSigma_translatedLargeCubeSupBound (M : ABKModel d) {l n m : ℤ}
    (hnm : n < m) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (translatedLargeCubeSupBound z l n m)
      ((3 * max 1 (Real.log (((subcubeShifts d n l).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        (streamLinftyConst d *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hmin_nonneg : (0 : ℝ) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hA : (0 : ℝ) ≤ streamLinftyConst d *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    mul_nonneg (mul_nonneg (streamLinftyConst_pos hd).le hmin_nonneg)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  exact Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (subcubeShifts d n l) (subcubeShifts_nonempty d n l) (by norm_num) hA
    fun p _ => isBigOWith_gammaSigma_translatedIncrementSupBound M hnm
      (subcubeCenter n p + z)

/-! ## 2. The deterministic bridge to the value gauge of the slot -/

/-- The translated increment shell field evaluates to the finite stream
increment at the translated point. -/
theorem translate_shellIncrement_apply (z : Vec d) (omega : Cutoff.ShellSeq d)
    (n m : ℤ) (x : Vec d) :
    (ShellField.translate z (shellIncrement omega n m)) x =
      Cutoff.finiteShellIncrement omega n m (x + z) := by
  rw [ShellField.translate_apply, shellIncrement_apply]

/-- **The value gauge of the translated increment is dominated by the covering
maximum.**  This is `e.km.kn.Linfty`'s deterministic half in the exact carrier
shape used by `ShellSlotBounds.lFreeValueSlot`. -/
theorem localCubeControl_translate_shellIncrement_le (z : Vec d)
    (omega : Cutoff.ShellSeq d) (l n m : ℤ) :
    Cutoff.localCubeControl l (ShellField.translate z (shellIncrement omega n m)) ≤
      translatedLargeCubeSupBound z l n m omega := by
  refine localCubeControl_le_of_forall l _
    (translatedLargeCubeSupBound_nonneg z l n m omega) fun x hx => ?_
  rw [translate_shellIncrement_apply]
  exact matrixOperatorNorm_finiteShellIncrement_le_translatedLargeCubeSupBound
    z omega l n m hx

/-! ## 3. The amplitude arithmetic -/

/-- Local re-derivation of a `private` helper of
`Stream/LargeCubeW1Inf.lean`. -/
theorem rpow_inv_two_eq_sqrt (x : ℝ) : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, one_div]

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- **The endpoint-safe comparison of the two minima.**  The covering route
reads the increment from the scale `n = j − 2`, so its `(m − n)^{1/2}` leg is
`(t + 2)^{1/2}` where `t = m − j`.  On the integer range `t ∈ {0} ∪ [1, ∞)` this
is at most twice `1 + min{a, t^{1/2}}` -- the additive `1` is exactly what the
endpoint `t = 0` forces. -/
theorem min_sqrt_add_two_le (a t : ℝ) (ha : 0 ≤ a) (ht : t = 0 ∨ 1 ≤ t) :
    min a (Real.sqrt (t + 2)) ≤ 2 * (1 + min a (Real.sqrt t)) := by
  have hmin_nonneg : (0 : ℝ) ≤ min a (Real.sqrt t) :=
    le_min ha (Real.sqrt_nonneg t)
  rcases ht with h0 | h1
  · subst h0
    have h2 : Real.sqrt (0 + 2) ≤ 2 := by
      have hle : Real.sqrt ((0 : ℝ) + 2) ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt (by norm_num)
      rwa [sqrt_four] at hle
    have h3 : min a (Real.sqrt ((0 : ℝ) + 2)) ≤ Real.sqrt ((0 : ℝ) + 2) :=
      min_le_right _ _
    linarith only [h2, h3, hmin_nonneg]
  · have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have hs : Real.sqrt (t + 2) ≤ 2 * Real.sqrt t := by
      have h4 : Real.sqrt (t + 2) ≤ Real.sqrt (4 * t) :=
        Real.sqrt_le_sqrt (by linarith only [h1])
      rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) t, sqrt_four] at h4
    rcases le_total a (Real.sqrt t) with hle | hle
    · have hlft : min a (Real.sqrt (t + 2)) ≤ a := min_le_left _ _
      rw [min_eq_left hle]
      linarith only [hlft, ha]
    · have hlft : min a (Real.sqrt (t + 2)) ≤ Real.sqrt (t + 2) := min_le_right _ _
      rw [min_eq_right hle]
      linarith only [hlft, hs, hst]

/-- The explicit dimensional constant of the `L∞` leg. -/
def valueLinftyConst (d : ℕ) : ℝ :=
  2 * Real.sqrt (largeCubeLogConst * (d : ℝ) * 2) * streamLinftyConst d

theorem valueLinftyConst_nonneg (d : ℕ) : 0 ≤ valueLinftyConst d := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · subst h0
    rw [valueLinftyConst, streamLinftyConst]
    have hgeo : (0 : ℝ) ≤ geometricConcentrationConst :=
      geometricConcentrationConst_pos.le
    have hsq : (0 : ℝ) ≤ Real.sqrt ((0 : ℕ) : ℝ) := Real.sqrt_nonneg _
    positivity
  · exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (streamLinftyConst_pos hpos).le

/-! ## 4. The `Γ₂` display of the `L∞` leg -/

/-- `‖k_m − k_{j−2}‖_{L∞(3^j v + □_j)} = 𝒪_{Γ₂}(C(d)(1 + min{γ^{-1/2},(m−j)^{1/2}})3^{γm})`.

The additive `1` is forced at `j = m`, where the printed minimum vanishes while
the left-hand side contains the nondegenerate block `k_m − k_{m−2}`; for `j ≤ m
− 1` the minimum is at least `1` and the display is the printed one up to the
constant. -/
theorem isBigOWith_gammaSigma_valueSlotLinfty (M : ABKModel d) {m : ℤ}
    (R : TriadicCube d) (hjm : R.scale ≤ m) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Cutoff.localCubeControl R.scale
          (ShellField.translate (Support.triadicLatticePoint R.scale R.index)
            (shellIncrement omega.1 (R.scale - 2) m)))
      (valueLinftyConst d *
        (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ)))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
  have hd1 : (1 : ℕ) ≤ d := le_trans (by norm_num) M.shellPrefix.dimension
  have hd : 0 < d := hd1
  have hnm : R.scale - 2 < m := by omega
  have hnl : R.scale - 2 < R.scale := by omega
  have hbase := isBigOWith_gammaSigma_translatedLargeCubeSupBound M
    (l := R.scale) (n := R.scale - 2) (m := m) hnm
    (Support.triadicLatticePoint R.scale R.index)
  have hcut := isBigOWith_cutoffSampleLaw_comp_val (M := M) hbase
  refine (hcut.of_le fun omega : Cutoff.CutoffSample d =>
    localCubeControl_translate_shellIncrement_le
      (Support.triadicLatticePoint R.scale R.index) omega.1 R.scale
      (R.scale - 2) m).mono_scale ?_
  -- the amplitude arithmetic: a `d`-only log factor and the endpoint-safe minimum
  have hlogpos : (0 : ℝ) ≤
      3 * max 1 (Real.log (((subcubeShifts d (R.scale - 2) R.scale).card : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤
        max 1 (Real.log (((subcubeShifts d (R.scale - 2) R.scale).card : ℕ) : ℝ)) :=
      le_max_left _ _
    linarith only [h1]
  have hlog := three_mul_max_one_log_card_subcubeShifts_le d
    (n := R.scale - 2) (l := R.scale) hd1 hnl
  have hlen : (R.scale : ℝ) - (((R.scale - 2 : ℤ)) : ℝ) = 2 := by push_cast; ring
  rw [hlen] at hlog
  have hsqrtlog :
      (3 * max 1 (Real.log (((subcubeShifts d (R.scale - 2) R.scale).card : ℕ) : ℝ)))
          ^ ((2 : ℝ)⁻¹) ≤ Real.sqrt (largeCubeLogConst * (d : ℝ) * 2) := by
    rw [rpow_inv_two_eq_sqrt]
    exact Real.sqrt_le_sqrt hlog
  have hshift : (m : ℝ) - (((R.scale - 2 : ℤ)) : ℝ) = ((m : ℝ) - (R.scale : ℝ)) + 2 := by
    push_cast; ring
  have hcase : (m : ℝ) - (R.scale : ℝ) = 0 ∨ 1 ≤ (m : ℝ) - (R.scale : ℝ) := by
    rcases eq_or_lt_of_le hjm with heq | hlt
    · exact Or.inl (by rw [heq]; ring)
    · refine Or.inr ?_
      have : (R.scale : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
      linarith only [this]
  have hmincmp :
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (((R.scale - 2 : ℤ)) : ℝ))) ≤
        2 * (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ)))) := by
    rw [hshift]
    exact min_sqrt_add_two_le _ _ (Real.sqrt_nonneg _) hcase
  have hKm : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hCpos : (0 : ℝ) < streamLinftyConst d := streamLinftyConst_pos hd
  have hSpos : (0 : ℝ) ≤ Real.sqrt (largeCubeLogConst * (d : ℝ) * 2) :=
    Real.sqrt_nonneg _
  have hminold : (0 : ℝ) ≤
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (((R.scale - 2 : ℤ)) : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hrest : (0 : ℝ) ≤ streamLinftyConst d *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (((R.scale - 2 : ℤ)) : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    mul_nonneg (mul_nonneg hCpos.le hminold) hKm.le
  calc (3 * max 1 (Real.log (((subcubeShifts d (R.scale - 2) R.scale).card : ℕ) : ℝ)))
          ^ ((2 : ℝ)⁻¹) *
        (streamLinftyConst d *
          min (Real.sqrt M.gamma⁻¹)
            (Real.sqrt ((m : ℝ) - (((R.scale - 2 : ℤ)) : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)))
      ≤ Real.sqrt (largeCubeLogConst * (d : ℝ) * 2) *
          (streamLinftyConst d *
            min (Real.sqrt M.gamma⁻¹)
              (Real.sqrt ((m : ℝ) - (((R.scale - 2 : ℤ)) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hsqrtlog hrest
    _ ≤ Real.sqrt (largeCubeLogConst * (d : ℝ) * 2) *
          (streamLinftyConst d *
            (2 * (1 + min (Real.sqrt M.gamma⁻¹)
              (Real.sqrt ((m : ℝ) - (R.scale : ℝ))))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hSpos
        refine mul_le_mul_of_nonneg_right ?_ hKm.le
        exact mul_le_mul_of_nonneg_left hmincmp hCpos.le
    _ = valueLinftyConst d *
          (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (R.scale : ℝ)))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
        rw [valueLinftyConst]
        ring

end

end Algsuperdiff.Section4.Provider.BoundsEaL
