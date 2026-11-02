/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootPayloadDataM
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootPayloadPrefix
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveShomComparison

/-!
# RootClauseBCloseArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The interior window's volume at an arbitrary scale -/

/-- `(3^a)^{d}` as a real power of `3`. -/
theorem three_zpow_pow_eq_rpow (a : ℤ) (e : ℕ) :
    ((3 : ℝ) ^ a) ^ e = Real.rpow (3 : ℝ) ((a : ℝ) * (e : ℝ)) := by
  have h1 : Real.rpow (3 : ℝ) ((a : ℝ) * (e : ℝ)) =
      Real.rpow (Real.rpow (3 : ℝ) (a : ℝ)) (e : ℝ) :=
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
  have h2 : Real.rpow (3 : ℝ) (a : ℝ) = (3 : ℝ) ^ a := Real.rpow_intCast (3 : ℝ) a
  have h3 : Real.rpow ((3 : ℝ) ^ a) (e : ℝ) = ((3 : ℝ) ^ a) ^ e :=
    Real.rpow_natCast ((3 : ℝ) ^ a) e
  rw [h1, h2, h3]

/-- On the interior branch the window `(z+□_j) ∩ □_m` IS the translate `z + □_j`
for every `j ≤ m-1`, so its volume is exactly `3^{dj}`. -/
theorem volume_toReal_truncatedWindow_inner_gen (d : ℕ) {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1) :
    (volume (truncatedWindow z m j)).toReal = ((3 : ℝ) ^ j) ^ d := by
  rw [truncatedWindow_eq_translateSet_of_mem_inner hz hj,
    ← image_add_eq_translateSet, volume_image_add,
    volume_toReal_openCubeSet_originCube]

/-- The volume ratio of the interior window at scale `j` inside `□_m`. -/
theorem volumeRatio_inner_gen (d : ℕ) (m j : ℤ) :
    ((3 : ℝ) ^ m) ^ d / ((3 : ℝ) ^ j) ^ d = ((3 : ℝ) ^ (m - j)) ^ d := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [← div_pow, ← zpow_sub₀ h3]

/-! ## 2. The window-to-cube step of `hgradE`, at an arbitrary interior scale -/

/-- **The `K_g` slot of the chain, at a general coarse scale.**

```text
  ν^{1/2}‖∇u‖_{L²((z+□_j) ∩ □_m)}  ≤  3^{(m-j)d/2} · ν^{1/2}‖∇u‖_{L²(□_m)} .
```

The case `j = m-1` is the one the close chain consumes.
Not an estimate on `u`: integral monotonicity on nested sets plus the exact
volume computation of §1. -/
theorem stepSevenNuGradNorm_window_le_cube (d : ℕ) {m j : ℤ} {z : Vec d} {nu : ℝ}
    (hnu : 0 ≤ nu) (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1)
    (u : H1Function (openCubeSet (originCube d m))) :
    stepSevenNuGradNorm nu (truncatedWindow z m j) u.grad ≤
      Real.sqrt (((3 : ℝ) ^ (m - j)) ^ d) *
        stepSevenNuGradNorm nu (openCubeSet (originCube d m)) u.grad := by
  have hmono := stepSevenGradMass_mono hnu u (truncatedWindow_subset_domain z m j)
    (Set.Subset.refl (openCubeSet (originCube d m)))
  have hvolS : (0 : ℝ) < (volume (truncatedWindow z m j)).toReal := by
    rw [volume_toReal_truncatedWindow_inner_gen d hz hj]
    exact pow_pos (zpow_pos (by norm_num) _) d
  have hvolT : (0 : ℝ) < (volume (openCubeSet (originCube d m))).toReal := by
    rw [volume_toReal_openCubeSet_originCube]
    exact pow_pos (zpow_pos (by norm_num) _) d
  have hratio : Real.sqrt ((volume (openCubeSet (originCube d m))).toReal /
      (volume (truncatedWindow z m j)).toReal) =
      Real.sqrt (((3 : ℝ) ^ (m - j)) ^ d) := by
    rw [volume_toReal_truncatedWindow_inner_gen d hz hj,
      volume_toReal_openCubeSet_originCube, volumeRatio_inner_gen d m j]
  have hmain := normalizedSqrt_le_volumeRatio_mul hvolS hvolT hmono
  rw [hratio] at hmain
  rw [stepSevenNuGradNorm_eq_sqrt_div, stepSevenNuGradNorm_eq_sqrt_div]
  exact hmain

/-! ## 3. The three re-cut constants -/

/-- **The `K_g` slot** at the chain's coarse scale `k`: the exact volume ratio
`3^{(m-k)d/2}`. -/
def rootClauseBTopKg (d : ℕ) (m k : ℤ) : ℝ := Real.sqrt (((3 : ℝ) ^ (m - k)) ^ d)

/-- `K_g` in exponential form. -/
theorem rootClauseBTopKg_eq (d : ℕ) (m k : ℤ) :
    rootClauseBTopKg d m k =
      Real.rpow (3 : ℝ) (((m : ℝ) - (k : ℝ)) * (d : ℝ) / 2) := by
  have hcast : (((m - k : ℤ)) : ℝ) = (m : ℝ) - (k : ℝ) := by push_cast; ring
  rw [rootClauseBTopKg, three_zpow_pow_eq_rpow, hcast, sqrt_rpow_three]

/-- **The `K_s` slot**: the `σ` index gap `4·3^{γ(m-k⋆)}` between the coarse
record's own `σ_{k⋆}` and the display's `σ_m`. -/
def rootClauseBTopKs (gamma : ℝ) (m ks : ℤ) : ℝ :=
  4 * Real.rpow (3 : ℝ) (gamma * ((m : ℝ) - (ks : ℝ)))

theorem rootClauseBTopKs_nonneg (gamma : ℝ) (m ks : ℤ) :
    0 ≤ rootClauseBTopKs gamma m ks := by
  have h : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (gamma * ((m : ℝ) - (ks : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  rw [rootClauseBTopKs]
  linarith only [h]

/-- **The `C_tr` slot of the re-cut**: `max(2·3^{d+1/2}, 4·3^{3/4}K_d)`.  A pure
`(d, K_d)` constant — no sample, no scale, no `α`, no `γ`. -/
def rootClauseBTopCtr (d : ℕ) (Kd : ℝ) : ℝ :=
  max (2 * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 2)) (4 * Real.rpow (3 : ℝ) (3 / 4) * Kd)

theorem rootClauseBTopCtr_nonneg (d : ℕ) (Kd : ℝ) : 0 ≤ rootClauseBTopCtr d Kd := by
  have h : (0 : ℝ) < Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine le_max_of_le_left ?_
  linarith only [h]

/-! ## 4. The `δ`-linear exponent budget -/

/-- **The gap absorbs.**

For any coefficient `c ≥ 0` with `4c ≤ 2d+2` (both `1/4 + d/2` and `1/2`
qualify), the Step-7c scalar budget forces

```text
  c·G  ≤  (1/4)·(1-α)T  +  (1/4 + c)          whenever  G ≤ |𝓑| + 1 .
```

The remainder `1/4 + c` is free of `m`, `n`, `α`, `δ` and the sample: this is
the whole content of the print's absorption of the bad-scale count into the
display's exponent. -/
theorem rootClauseBExpBudget {dd c alpha delta C1 T Bb G : ℝ} (hdd : 0 ≤ dd)
    (hc0 : 0 ≤ c) (hcC1 : 4 * c ≤ 2 * dd + 2) (hC1 : 2 * dd + 2 ≤ C1)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hdelta : delta ≤ C1⁻¹ * (1 - alpha)) (hT0 : 0 ≤ T)
    (hbud : Bb ≤ delta * (T + 1)) (hGB : G ≤ Bb + 1) :
    c * G ≤ 1 / 4 * ((1 - alpha) * T) + (1 / 4 + c) := by
  have hC1pos : (0 : ℝ) < C1 := by linarith only [hdd, hC1]
  have hC1ne : C1 ≠ 0 := ne_of_gt hC1pos
  have hT1 : (0 : ℝ) ≤ T + 1 := by linarith only [hT0]
  have ha1 : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha1]
  -- `c·C₁⁻¹ ≤ 1/4`
  have h4c : 4 * c ≤ C1 := le_trans hcC1 hC1
  have hquarter : c * C1⁻¹ ≤ 1 / 4 := by
    have hinv0 : (0 : ℝ) ≤ C1⁻¹ := le_of_lt (inv_pos.mpr hC1pos)
    have hstep : c * C1⁻¹ ≤ (C1 / 4) * C1⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith only [h4c]) hinv0
    have heq : (C1 / 4) * C1⁻¹ = 1 / 4 := by field_simp
    rwa [heq] at hstep
  -- the chain of dominations
  have hA : c * G ≤ c * (Bb + 1) := mul_le_mul_of_nonneg_left hGB hc0
  have hA' : c * (Bb + 1) = c * Bb + c := by ring
  have hB : c * Bb ≤ c * (delta * (T + 1)) := mul_le_mul_of_nonneg_left hbud hc0
  have hC : delta * (T + 1) ≤ C1⁻¹ * (1 - alpha) * (T + 1) :=
    mul_le_mul_of_nonneg_right hdelta hT1
  have hD : c * (delta * (T + 1)) ≤ c * (C1⁻¹ * (1 - alpha) * (T + 1)) :=
    mul_le_mul_of_nonneg_left hC hc0
  have hD' : c * (C1⁻¹ * (1 - alpha) * (T + 1)) =
      (c * C1⁻¹) * ((1 - alpha) * (T + 1)) := by ring
  have hE : (c * C1⁻¹) * ((1 - alpha) * (T + 1)) ≤
      1 / 4 * ((1 - alpha) * (T + 1)) :=
    mul_le_mul_of_nonneg_right hquarter (mul_nonneg ha1 hT1)
  have hF : 1 / 4 * ((1 - alpha) * (T + 1)) =
      1 / 4 * ((1 - alpha) * T) + 1 / 4 * (1 - alpha) := by ring
  have hG4 : 1 / 4 * (1 - alpha) ≤ 1 / 4 := by linarith only [halpha0]
  linarith only [hA, hA'.le, hA'.ge, hB, hD, hD'.le, hD'.ge, hE, hF.le, hF.ge, hG4]

/-! ## 5. The two `K_tr` dominations at the re-cut -/

/-- **The `hKgb` slot at the re-cut coarse scale.**

`√K_s·K_g = 2·3^{d/2}·3^{(γ/2 + d/2)(m-k⋆)}` and §4 at `c = 1/4 + d/2` puts the
exponent under `d + 1/2 + (1/4)(1-α)(m-n)`. -/
theorem rootClauseBTop_hKgb (d : ℕ) {gamma alpha delta C1 Kd : ℝ} {n m k : ℤ}
    {Bb : ℕ} (hgamma : gamma < 1 / 2)
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hbud : (Bb : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1))
    (hks : k + 1 ≤ m) (hgap : m - (k + 1) ≤ (Bb : ℤ) + 1) :
    Real.sqrt (rootClauseBTopKs gamma m (k + 1)) * rootClauseBTopKg d m k ≤
      rootClauseBTopCtr d Kd *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
  have hT : (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := toNat_sub_cast_real hnm
  have hT0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [h]
  set G : ℝ := (m : ℝ) - ((k + 1 : ℤ) : ℝ) with hGdef
  have hG0 : (0 : ℝ) ≤ G := by
    have h : (((k + 1 : ℤ)) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hks
    rw [hGdef]; linarith only [h]
  have hGB : G ≤ (Bb : ℝ) + 1 := by
    have h : (((m - (k + 1) : ℤ)) : ℝ) ≤ (((Bb : ℤ) + 1 : ℤ) : ℝ) := by
      exact_mod_cast hgap
    have hc1 : (((m - (k + 1) : ℤ)) : ℝ) = (m : ℝ) - ((k + 1 : ℤ) : ℝ) := by
      push_cast; ring
    have hc2 : (((Bb : ℤ) + 1 : ℤ) : ℝ) = (Bb : ℝ) + 1 := by push_cast; ring
    rw [hc1, hc2] at h
    rw [hGdef]; exact h
  -- the budget at `c = 1/4 + d/2`
  have hbudget := rootClauseBExpBudget (dd := (d : ℝ)) (c := 1 / 4 + (d : ℝ) / 2)
    (alpha := alpha) (delta := delta) (C1 := C1) (T := (m : ℝ) - (n : ℝ))
    (Bb := (Bb : ℝ)) (G := G) (Nat.cast_nonneg d)
    (by linarith only [Nat.cast_nonneg (α := ℝ) d]) (by linarith only []) hC1
    halpha0 halpha1 hdelta hT0 (by rw [hT] at hbud; exact hbud) hGB
  -- the exponent identity
  have hKs : Real.sqrt (rootClauseBTopKs gamma m (k + 1)) =
      2 * Real.rpow (3 : ℝ) (gamma * G / 2) := by
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [rootClauseBTopKs, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4,
      sqrt_rpow_three, hGdef]
  have hKg : rootClauseBTopKg d m k =
      Real.rpow (3 : ℝ) ((G + 1) * (d : ℝ) / 2) := by
    have hcast : (m : ℝ) - (k : ℝ) = G + 1 := by rw [hGdef]; push_cast; ring
    rw [rootClauseBTopKg_eq, hcast]
  have hmulexp : Real.rpow (3 : ℝ) (gamma * G / 2) *
      Real.rpow (3 : ℝ) ((G + 1) * (d : ℝ) / 2) =
      Real.rpow (3 : ℝ) (gamma * G / 2 + (G + 1) * (d : ℝ) / 2) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
  -- the exponent comparison
  have hcoef : gamma * G / 2 + (G + 1) * (d : ℝ) / 2 ≤
      ((d : ℝ) + 1 / 2) + 1 / 4 * stepSixExponent alpha n m := by
    have hgle : gamma / 2 + (d : ℝ) / 2 ≤ 1 / 4 + (d : ℝ) / 2 := by
      linarith only [hgamma]
    have hprod : (gamma / 2 + (d : ℝ) / 2) * G ≤ (1 / 4 + (d : ℝ) / 2) * G :=
      mul_le_mul_of_nonneg_right hgle hG0
    have hid : gamma * G / 2 + (G + 1) * (d : ℝ) / 2 =
        (gamma / 2 + (d : ℝ) / 2) * G + (d : ℝ) / 2 := by ring
    have hE : stepSixExponent alpha n m = (1 - alpha) * ((m : ℝ) - (n : ℝ)) := rfl
    rw [hid, hE]
    linarith only [hprod, hbudget]
  have hexp : Real.rpow (3 : ℝ) (gamma * G / 2 + (G + 1) * (d : ℝ) / 2) ≤
      Real.rpow (3 : ℝ) (((d : ℝ) + 1 / 2) + 1 / 4 * stepSixExponent alpha n m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hcoef
  have hsplit : Real.rpow (3 : ℝ) (((d : ℝ) + 1 / 2) +
        1 / 4 * stepSixExponent alpha n m) =
      Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 2) *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
  have hCtr : 2 * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 2) ≤ rootClauseBTopCtr d Kd :=
    le_max_left _ _
  have hR : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    Real.rpow_nonneg (by norm_num) _
  calc Real.sqrt (rootClauseBTopKs gamma m (k + 1)) * rootClauseBTopKg d m k
      = 2 * Real.rpow (3 : ℝ) (gamma * G / 2 + (G + 1) * (d : ℝ) / 2) := by
        rw [hKs, hKg, mul_assoc, hmulexp]
    _ ≤ 2 * Real.rpow (3 : ℝ)
          (((d : ℝ) + 1 / 2) + 1 / 4 * stepSixExponent alpha n m) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = (2 * Real.rpow (3 : ℝ) ((d : ℝ) + 1 / 2)) *
          Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
        rw [hsplit, mul_assoc]
    _ ≤ rootClauseBTopCtr d Kd *
          Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
        mul_le_mul_of_nonneg_right hCtr hR

/-- **The `hKdb` slot at the re-cut coarse scale.**

`K_s·K_d = 4·3^{γ(m-k⋆)}·K_d` and §4 at `c = 1/2` puts the exponent under `3/4
+ (1/4)(1-α)(m-n)`. -/
theorem rootClauseBTop_hKdb (d : ℕ) {gamma alpha delta C1 Kd : ℝ} {n m k : ℤ}
    {Bb : ℕ} (hgamma : gamma < 1 / 2) (hKd : 0 ≤ Kd)
    (hC1 : 2 * (d : ℝ) + 2 ≤ C1) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hnm : n ≤ m) (hdelta : delta ≤ C1⁻¹ * (1 - alpha))
    (hbud : (Bb : ℝ) ≤ delta * (((m - n).toNat : ℝ) + 1))
    (hks : k + 1 ≤ m) (hgap : m - (k + 1) ≤ (Bb : ℤ) + 1) :
    rootClauseBTopKs gamma m (k + 1) * Kd ≤
      rootClauseBTopCtr d Kd *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
  have hT : (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := toNat_sub_cast_real hnm
  have hT0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [h]
  set G : ℝ := (m : ℝ) - ((k + 1 : ℤ) : ℝ) with hGdef
  have hG0 : (0 : ℝ) ≤ G := by
    have h : (((k + 1 : ℤ)) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hks
    rw [hGdef]; linarith only [h]
  have hGB : G ≤ (Bb : ℝ) + 1 := by
    have h : (((m - (k + 1) : ℤ)) : ℝ) ≤ (((Bb : ℤ) + 1 : ℤ) : ℝ) := by
      exact_mod_cast hgap
    have hc1 : (((m - (k + 1) : ℤ)) : ℝ) = (m : ℝ) - ((k + 1 : ℤ) : ℝ) := by
      push_cast; ring
    have hc2 : (((Bb : ℤ) + 1 : ℤ) : ℝ) = (Bb : ℝ) + 1 := by push_cast; ring
    rw [hc1, hc2] at h
    rw [hGdef]; exact h
  have hbudget := rootClauseBExpBudget (dd := (d : ℝ)) (c := 1 / 2)
    (alpha := alpha) (delta := delta) (C1 := C1) (T := (m : ℝ) - (n : ℝ))
    (Bb := (Bb : ℝ)) (G := G) (Nat.cast_nonneg d) (by norm_num)
    (by linarith only [Nat.cast_nonneg (α := ℝ) d]) hC1 halpha0 halpha1 hdelta hT0
    (by rw [hT] at hbud; exact hbud) hGB
  have hcoef : gamma * G ≤ (3 / 4 : ℝ) + 1 / 4 * stepSixExponent alpha n m := by
    have hprod : gamma * G ≤ 1 / 2 * G :=
      mul_le_mul_of_nonneg_right (by linarith only [hgamma]) hG0
    have hE : stepSixExponent alpha n m = (1 - alpha) * ((m : ℝ) - (n : ℝ)) := rfl
    rw [hE]
    linarith only [hprod, hbudget]
  have hexp : Real.rpow (3 : ℝ) (gamma * G) ≤
      Real.rpow (3 : ℝ) ((3 / 4 : ℝ) + 1 / 4 * stepSixExponent alpha n m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hcoef
  have hsplit : Real.rpow (3 : ℝ) ((3 / 4 : ℝ) + 1 / 4 * stepSixExponent alpha n m) =
      Real.rpow (3 : ℝ) (3 / 4 : ℝ) *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
  have hCtr : 4 * Real.rpow (3 : ℝ) (3 / 4 : ℝ) * Kd ≤ rootClauseBTopCtr d Kd :=
    le_max_right _ _
  have hR : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep1 : rootClauseBTopKs gamma m (k + 1) * Kd ≤
      (4 * Real.rpow (3 : ℝ) ((3 / 4 : ℝ) +
        1 / 4 * stepSixExponent alpha n m)) * Kd := by
    have hbase : rootClauseBTopKs gamma m (k + 1) ≤
        4 * Real.rpow (3 : ℝ) ((3 / 4 : ℝ) +
          1 / 4 * stepSixExponent alpha n m) := by
      rw [rootClauseBTopKs, ← hGdef]
      exact mul_le_mul_of_nonneg_left hexp (by norm_num)
    exact mul_le_mul_of_nonneg_right hbase hKd
  have hstep2 : (4 * Real.rpow (3 : ℝ) ((3 / 4 : ℝ) +
        1 / 4 * stepSixExponent alpha n m)) * Kd =
      (4 * Real.rpow (3 : ℝ) (3 / 4 : ℝ) * Kd) *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) := by
    rw [hsplit]; ring
  have hstep3 : (4 * Real.rpow (3 : ℝ) (3 / 4 : ℝ) * Kd) *
      Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) ≤
      rootClauseBTopCtr d Kd *
        Real.rpow (3 : ℝ) (1 / 4 * stepSixExponent alpha n m) :=
    mul_le_mul_of_nonneg_right hCtr hR
  linarith only [hstep1, hstep2.le, hstep2.ge, hstep3]

/-! ## 6. The `htrShom` slot: the `σ` index gap, inverted -/

/-- **The `htrShom` slot at the re-cut coarse scale.**

The proved growth cap `σ_m ≤ 4·3^{γ(m-k⋆)}σ_{k⋆}` inverted:

```text
  σ_{k⋆}^{-1}  ≤  K_s · σ_m^{-1} ,      K_s = 4·3^{γ(m-k⋆)} .
```

's `K_s = 1` is the case `k⋆ = m`, where the cap is vacuous. -/
theorem rootClauseBTop_htrShom {M : ABKModel d} {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {ks m : ℤ}
    (hks : ks ≤ m) (hm : m ≤ m0) :
    ((Annealed.sigmaBar M ks : ℝ))⁻¹ ≤
      rootClauseBTopKs M.gamma m ks * ((Annealed.sigmaBar M m : ℝ))⁻¹ := by
  have hgrowth := sigmaBar_le_rpow_mul_sigmaBar_of_inductionState hS hks hm
  have hrw : (4 : ℝ) * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (ks : ℝ))) =
      rootClauseBTopKs M.gamma m ks := rfl
  rw [hrw] at hgrowth
  exact inv_le_mul_inv_of_le_mul (Annealed.sigmaBar M ks).2 (Annealed.sigmaBar M m).2
    hgrowth

end

end Algsuperdiff.Section4.Provider.Regularity
