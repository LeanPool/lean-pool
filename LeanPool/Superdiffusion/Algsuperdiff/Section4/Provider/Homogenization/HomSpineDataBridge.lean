/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineTopScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepThreeData

/-!
# HomSpineDataBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `StepTwoDataBridge` PRODUCED: the correction discharged

## What this file discharges

`HomSpineTopScale.StepTwoDataBridge` — the ONE data-leg input of
`htop_of_stepTwoA_enlargedY` — is the passage from the printed `p = ∞`
normalization of the manuscript,

```text
  [g]_{C^{0,1/2}(□_m)} ≤ K_g,   [∇h]_{C^{0,1/2}(□_m)} ≤ K_h,
  ‖∇h‖_{L^∞(□_m)} ≤ K_h^∞,
```

to the `q = 2`-in-scale Besov data quantities that `CoarseGraining`'s
coarse-graining right-hand side carries,

```text
  3^{sm}[g]_{B^s_{2,2}(□_m)} ≤ C_data · 3^{m/2} K_g,
  3^{sm}‖∇h‖_{B^s_{2,2}(□_m)} ≤ C_data · (K_h^∞ + 3^{m/2} K_h).
```

The correction records this as a named input, together with the two findings it
verified: the passage is **exponent-critical** (`s < 1/2` STRICTLY — at `s =
1/2` the depth-`j` contribution `3^{m/2}3^{(s-1/2)j}[g]` does not decay and the
`ℓ²`-in-scale sum diverges), and nothing in `CoarseGraining` or Mathlib proves
it.

**It is proved here, from material already available in this repository.**  The
route is the *Gagliardo* one, not the direct depth sum:

* `HomStepThreeData.memWsp_of_holderHalf` — a `C^{0,1/2}` field on the cube
  lies in `W^{s,2}(□_m)` for `s < 1/2` (the radial kernel integrates near the
  diagonal exactly in that range);
* `StepFourSeminormComparisons.three_rpow_mul_normalizedGagliardoESeminormOn_cube_le`
  — `3^{ms}[f]_{H^s(□_m)} ≤ K·C_{S4.4}(d,s)·3^{m/2}`, whose constant
  `C_{S4.4}(d,s) ≤ (2^{d+1}3^d/(1-2s))^{1/2}` carries the correction's endpoint
  blow-up (here in the Gagliardo form `(1-2s)^{-1/2}`; the correction states it in
  the depth-sum form `(1-3^{2s-1})^{-1/2}` — the same divergence at `s ↑ 1/2`,
  from the same geometric series);
* `ExcessDecay.scaleNormalizedPositiveBesovVectorSeminormTwo_le_gagliardo` —
  the `H^s → B^s_{2,2}` bridge at `besovGagliardoConstant d`;
* `HomStepThreeData.sqrt_vecNormSq_cubeAverageVec_le` — the MEAN term of the
  `∇h` NORM, priced by the root's own `K_h^∞` binder at `√d` (a Hölder
  seminorm alone cannot price it; the root already carries the sup datum).

## No hypothesis is added

`stepTwoDataBridge_of_holder` takes exactly the frozen root's own data binders
(`generator_renormalization`, the `Kg`/`Kh`/`KhInf` block) plus the standing
`0 < t`, and the correction's own strict `t < 1/2`.  There is no new
mathematical proposition in any binder.

## The constant

```text
  stepTwoDataConst d t = max ( √d, C_besov(d) · C_{S4.4}(d,t) )
```

— the `√d` prices the mean term (the ambient sup-versus-Euclidean conversion,
the standing convention) and the product prices both seminorm legs.
`stepTwoDataConstPinned d` is its `t ≤ 1/4` specialization at the `γ`-free
`homDataConst d`.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.Regularity
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The Gagliardo data embedding at the FULL corrected range `s < 1/2`

`HomStepThreeData` states the embedding at the gate `s ≤ 1/4`, where the
`s`-dependence of the constant is absorbed into the `γ`-free `homDataConst d`.
The correction asks for the whole open range, with the endpoint blow-up
displayed.  These are the same proofs at `stepFourGagliardoConst d s`. -/

/-- **The data embedding in `toReal` form, at `0 < s < 1/2`**:
`3^{ms}[f]_{H^s(□_m)} ≤ K · C_{S4.4}(d,s) · 3^{m/2}`, with the correction's
endpoint factor kept visible inside `C_{S4.4}(d,s)`. -/
theorem three_rpow_mul_cubeGagliardoSeminorm_le_of_lt_half {m : ℤ} {K s : ℝ} {f : Vec d → E}
    (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    (3 : ℝ) ^ ((m : ℝ) * s) *
        (Gagliardo.cubeGagliardoESeminorm (originCube d m) s 2 f).toReal ≤
      K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) / 2) := by
  have hid := normalizedGagliardoESeminormOn_openCubeSet (originCube d m) s f
  have hbase := three_rpow_mul_normalizedGagliardoESeminormOn_cube_le (E := E) hd hs0 hs hK hf
  have hnn : (0 : ℝ) ≤ K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) / 2) :=
    mul_nonneg (mul_nonneg hK (stepFourGagliardoConst_nonneg d s))
      (Real.rpow_nonneg (by norm_num) _)
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) * s) := Real.rpow_nonneg (by norm_num) _
  have hreal := ENNReal.toReal_le_of_le_ofReal hnn (hid ▸ hbase)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw] at hreal

/-- **`B_g ≤ C 3^{m/2} K` at `0 < s < 1/2`.**  The `q = 2`-in-scale Besov data
leg of the coarse-graining right-hand side, priced by the printed Hölder normalization on the whole
range the correction names. -/
theorem besovSeminormTwo_le_of_holderHalf_of_lt_half [NeZero d] {m : ℤ} {K s : ℝ}
    {g : Vec d → Vec d} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d m) s g ≤
      besovGagliardoConstant d * (K * stepFourGagliardoConst d s) *
        (3 : ℝ) ^ ((m : ℝ) / 2) := by
  have hbridge := scaleNormalizedPositiveBesovVectorSeminormTwo_le_gagliardo
    (originCube d m) g hs0 (by linarith only [hs])
    (memLp_two_normalizedCubeMeasure_of_holderHalf hK hg)
    (memWsp_of_holderHalf hd hs0 hs hK hg)
  have hweight : cubeBesovScaleWeight (-s) (originCube d m) = (3 : ℝ) ^ ((m : ℝ) * s) := by
    rw [cubeBesovScaleWeight, cubeScaleFactor, neg_neg]
    change ((3 : ℝ) ^ (m : ℤ)) ^ s = (3 : ℝ) ^ ((m : ℝ) * s)
    rw [← Real.rpow_intCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hstep := three_rpow_mul_cubeGagliardoSeminorm_le_of_lt_half (E := Vec d) hd hs0 hs hK hg
  refine hbridge.trans ?_
  have hCnn : (0 : ℝ) ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
  calc besovGagliardoConstant d * cubeBesovScaleWeight (-s) (originCube d m) *
        (Gagliardo.cubeGagliardoESeminorm (originCube d m) s 2 g).toReal
      = besovGagliardoConstant d *
          ((3 : ℝ) ^ ((m : ℝ) * s) *
            (Gagliardo.cubeGagliardoESeminorm (originCube d m) s 2 g).toReal) := by
        rw [hweight]; ring
    _ ≤ besovGagliardoConstant d * (K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((m : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hstep hCnn
    _ = besovGagliardoConstant d * (K * stepFourGagliardoConst d s) *
          (3 : ℝ) ^ ((m : ℝ) / 2) := by ring

/-- **The `∇h` NORM leg at `0 < s < 1/2`.**  `HomStepThreeData`'s `M3` display
on the whole corrected range: the mean half priced by the root's sup binder at
`√d`, the seminorm half by the embedding. -/
theorem besovVectorNormTwo_le_of_holderHalf_of_sup_of_lt_half [NeZero d] {m : ℤ}
    {K KInf s : ℝ} {F : Vec d → Vec d} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2)
    (hK : 0 ≤ K) (hKInf : 0 ≤ KInf)
    (hF : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K F)
    (hFsup : ∀ x ∈ openCubeSet (originCube d m), ‖F x‖ ≤ KInf) :
    scaleNormalizedPositiveBesovVectorNormTwo (originCube d m) s F ≤
      Real.sqrt (d : ℝ) * KInf +
        besovGagliardoConstant d * (K * stepFourGagliardoConst d s) *
          (3 : ℝ) ^ ((m : ℝ) / 2) := by
  have hmean := sqrt_vecNormSq_cubeAverageVec_le (Q := originCube d m) hKInf hFsup
  have hsem := besovSeminormTwo_le_of_holderHalf_of_lt_half hd hs0 hs hK hF
  rw [scaleNormalizedPositiveBesovVectorNormTwo]
  exact add_le_add hmean hsem

/-! ## 2. The bridge constant -/

/-- The constant of the correction in this repository's carriers:
`max(√d, C_besov(d)·C_{S4.4}(d,t))`.  The first entry prices the MEAN term of
the `∇h` norm against the root's `K_h^∞` binder, the second prices both
seminorm legs; the endpoint blow-up as `t ↑ 1/2` sits in
`stepFourGagliardoConst`. -/
def stepTwoDataConst (d : ℕ) (t : ℝ) : ℝ :=
  max (Real.sqrt (d : ℝ)) (besovGagliardoConstant d * stepFourGagliardoConst d t)

/-- The pinned form of the bridge constant (`t ≤ 1/4`, `γ`-free). -/
def stepTwoDataConstPinned (d : ℕ) : ℝ :=
  max (Real.sqrt (d : ℝ)) (besovGagliardoConstant d * homDataConst d)

theorem stepTwoDataConstPinned_nonneg (d : ℕ) : 0 ≤ stepTwoDataConstPinned d :=
  le_trans (Real.sqrt_nonneg _) (le_max_left _ _)

theorem stepTwoDataConst_le_pinned {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 4) :
    stepTwoDataConst d t ≤ stepTwoDataConstPinned d := by
  refine max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
  exact mul_le_mul_of_nonneg_left (stepFourGagliardoConst_le_homDataConst ht0 ht)
    (besovGagliardoConstant_nonneg d)

/-! ## 3. The bridge is monotone in its constant -/

/-- Enlarging `C_data` weakens the bridge: the two right-hand sides are
nonnegative multiples of `C_data`. -/
theorem StepTwoDataBridge.mono_const {m : ℤ} {t Cdata Cdata' Kg KhInf Kh : ℝ}
    {g gradh : Vec d → Vec d} (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) (hKhInf : 0 ≤ KhInf)
    (hbridge : StepTwoDataBridge m t g gradh Cdata Kg KhInf Kh)
    (hCC : Cdata ≤ Cdata') :
    StepTwoDataBridge m t g gradh Cdata' Kg KhInf Kh := by
  obtain ⟨h1, h2⟩ := hbridge
  have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hCC (mul_nonneg hpow hKg)
  · exact mul_le_mul_of_nonneg_right hCC
      (by linarith only [hKhInf, mul_nonneg hpow hKh])

/-! ## 4. The bridge, proved -/

/-- **The Hölder-embedding correction, discharged.**

`HomSpineTopScale.StepTwoDataBridge` at the constant `stepTwoDataConst d t`,
from exactly the frozen root's own data binders:

```text
  [g]_{C^{0,1/2}(□_m)} ≤ K_g,  [∇h]_{C^{0,1/2}(□_m)} ≤ K_h,
  ‖∇h‖_{L^∞(□_m)} ≤ K_h^∞,        0 < t < 1/2.
```

The `g` leg is the embedding applied to `-g` (the forcing sign,
`holderSeminormBoundOn_neg`, at constant `1`); the `∇h` leg is the NORM, whose
mean half is the root's `K_h^∞` binder at `√d` and whose seminorm half is the
embedding again.  `t < 1/2` is STRICT and load-bearing: it is what makes the
Gagliardo kernel of a `C^{0,1/2}` field integrable at the diagonal, i.e. the
correction's `ℓ²`-in-scale convergence. -/
theorem stepTwoDataBridge_of_holder [NeZero d] {m : ℤ} {t Kg Kh KhInf : ℝ}
    {g gradh : Vec d → Vec d} (ht0 : 0 < t) (ht : t < 1 / 2)
    (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) (hKhInf : 0 ≤ KhInf)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hh : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh gradh)
    (hhsup : ∀ x ∈ openCubeSet (originCube d m), ‖gradh x‖ ≤ KhInf) :
    StepTwoDataBridge m t g gradh (stepTwoDataConst d t) Kg KhInf Kh := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hprod : besovGagliardoConstant d * stepFourGagliardoConst d t ≤ stepTwoDataConst d t :=
    le_max_right _ _
  have hsqrt : Real.sqrt (d : ℝ) ≤ stepTwoDataConst d t := le_max_left _ _
  constructor
  · /- the `g` leg, at the negated forci -/
    have hgneg := besovSeminormTwo_le_of_holderHalf_of_lt_half (m := m) (K := Kg) (s := t)
      (g := fun x => -g x) hd ht0 ht hKg (holderSeminormBoundOn_neg hg)
    refine hgneg.trans ?_
    have hstep := mul_le_mul_of_nonneg_right hprod (mul_nonneg hpow hKg)
    calc besovGagliardoConstant d * (Kg * stepFourGagliardoConst d t) *
          (3 : ℝ) ^ ((m : ℝ) / 2)
        = (besovGagliardoConstant d * stepFourGagliardoConst d t) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) * Kg) := by ring
      _ ≤ stepTwoDataConst d t * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kg) := hstep
      _ = stepTwoDataConst d t * (Real.rpow 3 ((m : ℝ) / 2) * Kg) := by
          rw [show Real.rpow 3 ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) from rfl]
  · /- the `∇h` leg: mean plus semino -/
    have hnorm := besovVectorNormTwo_le_of_holderHalf_of_sup_of_lt_half
      (m := m) (K := Kh) (KInf := KhInf) (s := t) (F := gradh) hd ht0 ht hKh hKhInf hh hhsup
    refine hnorm.trans ?_
    have hmean : Real.sqrt (d : ℝ) * KhInf ≤ stepTwoDataConst d t * KhInf :=
      mul_le_mul_of_nonneg_right hsqrt hKhInf
    have hsem : besovGagliardoConstant d * (Kh * stepFourGagliardoConst d t) *
        (3 : ℝ) ^ ((m : ℝ) / 2) ≤
        stepTwoDataConst d t * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) := by
      have h := mul_le_mul_of_nonneg_right hprod (mul_nonneg hpow hKh)
      calc besovGagliardoConstant d * (Kh * stepFourGagliardoConst d t) *
            (3 : ℝ) ^ ((m : ℝ) / 2)
          = (besovGagliardoConstant d * stepFourGagliardoConst d t) *
            ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) := by ring
        _ ≤ stepTwoDataConst d t * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) := h
    have hsplit : stepTwoDataConst d t *
        (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh) =
        stepTwoDataConst d t * KhInf +
          stepTwoDataConst d t * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) := by
      rw [show Real.rpow 3 ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) from rfl]; ring
    rw [hsplit]
    exact add_le_add hmean hsem

/-- The pinned corollary: at `0 < t ≤ 1/4` the bridge runs at the
`γ`-free constant `stepTwoDataConstPinned d`. -/
theorem stepTwoDataBridge_of_holder_pinned [NeZero d] {m : ℤ} {t Kg Kh KhInf : ℝ}
    {g gradh : Vec d → Vec d} (ht0 : 0 < t) (ht : t ≤ 1 / 4)
    (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) (hKhInf : 0 ≤ KhInf)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hh : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh gradh)
    (hhsup : ∀ x ∈ openCubeSet (originCube d m), ‖gradh x‖ ≤ KhInf) :
    StepTwoDataBridge m t g gradh (stepTwoDataConstPinned d) Kg KhInf Kh :=
  StepTwoDataBridge.mono_const hKg hKh hKhInf
    (stepTwoDataBridge_of_holder ht0 (by linarith only [ht]) hKg hKh hKhInf hg hh hhsup)
    (stepTwoDataConst_le_pinned ht0 ht)

end

end Algsuperdiff.Section4.Provider.Homogenization
