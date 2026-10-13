/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerApp

/-!
# OneStepOddClassCornerFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The corner pricing `(★★)`, assembled

's residue (2): at a window meeting two upper faces the odd affine class
collapses to `{0}` (`affineLift_eq_zero_of_two_met`), and this module prices
the resulting degenerate defect:

* `exists_normalizedL2On_le_affineExcessRaw_corner` — **`(★★)`**: for `V`
  classically harmonic on the doubled window and odd under every met-face
  reflection, `‖V‖_{L²(U₂)} ≤ C(d)·E_raw(U₂,V)`.
* `exists_oddClassDefect_le_affineExcessRaw_corner` — the consumer shape:
  `oddClassDefect x m n V 0 0 ≤ C(d)·E_raw(U₂,V)` at the corner datum
  `(0,0)`, the only member of the collapsed class.

## The absorption

With `ℓ*` a minimizer, `f = V − ℓ*`, `E = ‖f‖_{L²(U₂)}`, `P = ‖ℓ*‖_{L²(U₂)}`
and the split `ℓ* = evenᵢ + evenⱼ − e_{ij}`, the three applications of
`OneStepOddClassCornerApp` give

```text
  ‖evenᵢ‖, ‖evenⱼ‖ ≤ 3·Caff·Vr·E + Λt·(E+P) ,
  ‖e_{ij}‖ ≤ 3·Caff·Vr·E + Λt·(E+P) + 2·Λt·(P + ‖evenᵢ‖) ,
```

with `Λ = Λ(d)` collecting the Hessian, fold and ramp coefficients and the
depth fraction `t = min(1/16, 1/(8Λ))` making `Λt ≤ 1/8`.  The linear
program closes at `P ≤ (104/11)·3·Caff·Vr·E + (13/11)·E`, whence
`‖V‖ ≤ E + P ≤ C(d)·E` with `C(d) = (104/11)·3·Caff·Vr + 24/11` explicit in
`d` (through `Caff`, `Vr` and the transplanted interior Hessian constant).

## Scope (disclosed)

Upper-upper met pairs, matching every proved one-face convention; the met set
is otherwise arbitrary.  Lower/mixed corners need the mechanical lower-face
twins or a negation transport (not built here).  The oddness binders are the
global pointwise identities, as in the proved `(★)`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **`(★★)`: the corner competitor's window seminorm is priced by the
excess.**  See the module docstring. -/
theorem exists_normalizedL2On_le_affineExcessRaw_corner (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i j : Fin d) (V : Vec d → ℝ)
      (c : ℝ) (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m → i ≠ j →
      MeetsUpperFace x m (n - 2) i → MeetsUpperFace x m (n - 2) j →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      normalizedL2On (truncatedWindow x m (n - 2)) V
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  classical
  obtain ⟨CH, hCH0, hCH⟩ := exists_hessian_normalizedL2On_bound d
  set CHc : ℝ := CH * 256 * Real.sqrt ((32 : ℝ) ^ d) with hCHcdef
  have hCHc0 : 0 ≤ CHc := by
    rw [hCHcdef]
    exact mul_nonneg (mul_nonneg hCH0 (by norm_num)) (Real.sqrt_nonneg _)
  set Caff : ℝ := Real.sqrt ((24 * (d : ℝ) + 1) * 4 ^ 2 + 2) with hCaffdef
  have hCaff0 : 0 ≤ Caff := Real.sqrt_nonneg _
  set Crefl : ℝ := Real.sqrt ((24 * (d : ℝ) + 1) * 2 ^ 2 + 2) with hCrefldef
  have hCrefl0 : 0 ≤ Crefl := Real.sqrt_nonneg _
  set CFold : ℝ := 2 ^ d + Crefl with hCFolddef
  have hCFold0 : 0 ≤ CFold := by
    rw [hCFolddef]
    have h2 : (0 : ℝ) ≤ 2 ^ d := by positivity
    linarith only [h2, hCrefl0]
  set Lam : ℝ := 3 * Caff * CHc * CFold + 21 * Caff + 3 * Caff * CHc * Crefl + 1
    with hLamdef
  have hpart1 : (0 : ℝ) ≤ 3 * Caff * CHc * CFold :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCaff0) hCHc0) hCFold0
  have hpart2 : (0 : ℝ) ≤ 21 * Caff := by linarith only [hCaff0]
  have hpart3 : (0 : ℝ) ≤ 3 * Caff * CHc * Crefl :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCaff0) hCHc0) hCrefl0
  have hLam1 : 1 ≤ Lam := by
    rw [hLamdef]
    linarith only [hpart1, hpart2, hpart3]
  have hLam0 : (0 : ℝ) < Lam := lt_of_lt_of_le (by norm_num) hLam1
  set tt : ℝ := min (1 / 16) (1 / (8 * Lam)) with httdef
  have htt0 : 0 < tt := by
    rw [httdef]
    exact lt_min (by norm_num) (by positivity)
  have htt16 : tt ≤ 1 / 16 := min_le_left _ _
  have htt1 : tt ≤ 1 := le_trans htt16 (by norm_num)
  have heps8 : Lam * tt ≤ 1 / 8 := by
    have h := min_le_right (1 / 16 : ℝ) (1 / (8 * Lam))
    rw [← httdef] at h
    have h8 : (0 : ℝ) < 8 * Lam := by positivity
    calc Lam * tt ≤ Lam * (1 / (8 * Lam)) := mul_le_mul_of_nonneg_left h hLam0.le
      _ = 1 / 8 := by field_simp
  set Vr : ℝ := Real.sqrt ((1 / tt) ^ d) with hVrdef
  have hVr0 : 0 ≤ Vr := Real.sqrt_nonneg _
  have hCtot0 : 0 ≤ (104 / 11) * (3 * Caff * Vr) + 24 / 11 := by
    have h1 : 0 ≤ Caff * Vr := mul_nonneg hCaff0 hVr0
    linarith only [h1]
  refine ⟨(104 / 11) * (3 * Caff * Vr) + 24 / 11, hCtot0, ?_⟩
  intro m n x i j V c A hx hmn hij hupi hupj hupV hlowV hharm hVR hmin
  have hji : j ≠ i := fun h => hij h.symm
  set delta : ℝ := tt * (3 : ℝ) ^ (n - 2) with hdeltadef
  -- the third-application affine pair
  set A3 : Vec d := evenAffineSlope i A with hA3def
  set c3 : ℝ := evenAffineIntercept x m i c A + vecDot A3 x with hc3def
  have hc3sub : c3 - vecDot A3 x = evenAffineIntercept x m i c A := by
    rw [hc3def]; ring
  have he3 : ∀ y, affineEval (c3 - vecDot A3 x) A3 y
      = evenAffinePart x m i c A y := by
    intro y
    rw [hc3sub, evenAffinePart, hA3def]
  have hA3i : A3 i = 0 := by
    rw [hA3def]
    exact evenAffineSlope_apply_self i A
  have hA3j : A3 j = A j := by
    rw [hA3def]
    show (A - oddAffineSlope i A) j = A j
    rw [Pi.sub_apply, oddAffineSlope, ite_eq_right hji, sub_zero]
  have hgij_i : evenAffineSlope j A3 i = 0 := by
    show (A3 - oddAffineSlope j A3) i = 0
    rw [Pi.sub_apply, oddAffineSlope, ite_eq_right hij, hA3i, sub_zero]
  have hLsplit : ∀ y, affineEval (c - vecDot A x) A y
      = evenAffinePart x m i c A y + evenAffinePart x m j c A y
        - evenAffinePart x m j c3 A3 y := by
    intro y
    have h1 := affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y
    have h2 := affineEval_eq_oddAffinePart_add_evenAffinePart x m j c A y
    have h3 := affineEval_eq_oddAffinePart_add_evenAffinePart x m j c3 A3 y
    have h4 := he3 y
    have h5 : oddAffinePart x m j A3 y = oddAffinePart x m j A y := by
      rw [oddAffinePart_apply, oddAffinePart_apply, hA3j]
    linarith only [h1, h2, h3, h4, h5]
  have hf3split : ∀ y, V y - affineEval (c3 - vecDot A3 x) A3 y
      = (V y - affineEval (c - vecDot A x) A y) + oddAffinePart x m i A y := by
    intro y
    have h1 := affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y
    have h4 := he3 y
    linarith only [h1, h4]
  -- `L²` data on the window
  have hUR := truncatedWindow_subset_reflectedWindow x m (n - 2)
  have hfR : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (reflectedWindow x m (n - 2))) :=
    hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hfU : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (truncatedWindow x m (n - 2))) :=
    hfR.mono_measure (Measure.restrict_mono hUR le_rfl)
  have hlU : MemLp (affineEval (c - vecDot A x) A) 2
      (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have heiU : MemLp (evenAffinePart x m i c A) 2
      (volume.restrict (truncatedWindow x m (n - 2))) := by
    rw [evenAffinePart]
    exact memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have hejU : MemLp (evenAffinePart x m j c A) 2
      (volume.restrict (truncatedWindow x m (n - 2))) := by
    rw [evenAffinePart]
    exact memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have heijU : MemLp (evenAffinePart x m j c3 A3) 2
      (volume.restrict (truncatedWindow x m (n - 2))) := by
    rw [evenAffinePart]
    exact memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have hoddRmem : MemLp (oddAffinePart x m i A) 2
      (volume.restrict (reflectedWindow x m (n - 2))) := by
    rw [oddAffinePart]
    exact memLp_affineEval_reflectedWindow x m (n - 2) _ _
  have hE0 : 0 ≤ normalizedL2On (truncatedWindow x m (n - 2))
      (fun y => V y - affineEval (c - vecDot A x) A y) := normalizedL2On_nonneg _ _
  have hP0 : 0 ≤ normalizedL2On (truncatedWindow x m (n - 2))
      (affineEval (c - vecDot A x) A) := normalizedL2On_nonneg _ _
  have hNi0 : 0 ≤ normalizedL2On (truncatedWindow x m (n - 2))
      (evenAffinePart x m i c A) := normalizedL2On_nonneg _ _
  -- the three applications
  have h_i := corner_faceApp_le (face := i) (c := c) (A := A) hx hmn hupi
    (hupV i hupi) hharm hVR htt0 htt16 hdeltadef hCH0 hCH
  have h_j := corner_faceApp_le (face := j) (c := c) (A := A) hx hmn hupj
    (hupV j hupj) hharm hVR htt0 htt16 hdeltadef hCH0 hCH
  have h_3 := corner_pairApp_le (c' := c3) (A' := A3) hx hmn hij hupi hupj
    (hupV j hupj) hharm hVR htt0 htt16 hdeltadef hf3split hgij_i hCH0 hCH
  rw [← hCaffdef, ← hVrdef, ← hCHcdef] at h_i h_j h_3
  -- the fold and the shifted fold
  have hFRle := normalizedL2On_reflected_residual_le (c := c) (A := A) hx hmn
    hupV hlowV hVR
  rw [← hCrefldef, ← hCFolddef] at hFRle
  have hoddRle : normalizedL2On (reflectedWindow x m (n - 2))
      (oddAffinePart x m i A)
      ≤ Crefl * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A) := by
    have h := normalizedL2On_reflectedWindow_affineEval_le hx (by omega : n - 2 < m)
      (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)
      (oddAffineSlope i A)
    rw [← hCrefldef] at h
    rw [oddAffinePart]
    exact h
  have hoddU_le : normalizedL2On (truncatedWindow x m (n - 2))
      (oddAffinePart x m i A)
      ≤ normalizedL2On (truncatedWindow x m (n - 2)) (affineEval (c - vecDot A x) A)
        + normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A) := by
    have hcongr : normalizedL2On (truncatedWindow x m (n - 2))
        (oddAffinePart x m i A)
        = normalizedL2On (truncatedWindow x m (n - 2))
          (fun y => affineEval (c - vecDot A x) A y - evenAffinePart x m i c A y) := by
      congr 1
      funext y
      have h1 := affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y
      linarith only [h1]
    rw [hcongr]
    exact normalizedL2On_sub_le hlU heiU
  have hF3split : normalizedL2On (reflectedWindow x m (n - 2))
      (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y)
      ≤ normalizedL2On (reflectedWindow x m (n - 2))
          (fun y => V y - affineEval (c - vecDot A x) A y)
        + normalizedL2On (reflectedWindow x m (n - 2)) (oddAffinePart x m i A) := by
    have hcongr : normalizedL2On (reflectedWindow x m (n - 2))
        (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y)
        = normalizedL2On (reflectedWindow x m (n - 2))
          (fun y => (V y - affineEval (c - vecDot A x) A y)
            + oddAffinePart x m i A y) := by
      congr 1
      funext y
      exact hf3split y
    rw [hcongr]
    exact normalizedL2On_add_le hfR hoddRmem
  have hF3R : normalizedL2On (reflectedWindow x m (n - 2))
      (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y)
      ≤ CFold * (normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A))
        + Crefl * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A)) := by
    have h1 : Crefl * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A)
        ≤ Crefl * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A)) :=
      mul_le_mul_of_nonneg_left hoddU_le hCrefl0
    linarith only [hF3split, hoddRle, h1, hFRle]
  -- the ramp against the minimizer pieces
  have hAiq : |A i| * delta
      ≤ 7 * tt * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A) :=
    abs_slope_mul_delta_le hx hmn htt0 hdeltadef
  have hq2 : |A i| * delta
      ≤ 7 * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A)) := by
    have h := mul_le_mul_of_nonneg_left hoddU_le
      (by positivity : (0 : ℝ) ≤ 7 * tt)
    linarith only [hAiq, h]
  -- the split of the minimizer
  have hPsum : normalizedL2On (truncatedWindow x m (n - 2))
      (affineEval (c - vecDot A x) A)
      ≤ normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A)
        + normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m j c A)
        + normalizedL2On (truncatedWindow x m (n - 2))
            (evenAffinePart x m j c3 A3) := by
    have hcongr : normalizedL2On (truncatedWindow x m (n - 2))
        (affineEval (c - vecDot A x) A)
        = normalizedL2On (truncatedWindow x m (n - 2))
          (fun y => (evenAffinePart x m i c A y + evenAffinePart x m j c A y)
            - evenAffinePart x m j c3 A3 y) := by
      congr 1
      funext y
      rw [hLsplit y]
    rw [hcongr]
    have hsum : MemLp (fun y => evenAffinePart x m i c A y
        + evenAffinePart x m j c A y) 2
        (volume.restrict (truncatedWindow x m (n - 2))) := heiU.add hejU
    have h1 := normalizedL2On_sub_le hsum heijU
    have h2 := normalizedL2On_add_le heiU hejU
    linarith only [h1, h2]
  have hVsplit : normalizedL2On (truncatedWindow x m (n - 2)) V
      ≤ normalizedL2On (truncatedWindow x m (n - 2))
          (fun y => V y - affineEval (c - vecDot A x) A y)
        + normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A) := by
    have hcongr : normalizedL2On (truncatedWindow x m (n - 2)) V
        = normalizedL2On (truncatedWindow x m (n - 2))
          (fun y => (V y - affineEval (c - vecDot A x) A y)
            + affineEval (c - vecDot A x) A y) := by
      congr 1
      funext y
      ring
    rw [hcongr]
    exact normalizedL2On_add_le hfU hlU
  -- coefficient smallness
  have hco1 : 3 * Caff * CHc * CFold * tt ^ 2 ≤ Lam * tt := by
    have ha : 3 * Caff * CHc * CFold ≤ Lam := by
      rw [hLamdef]
      linarith only [hpart2, hpart3]
    have hb : 3 * Caff * CHc * CFold * tt ≤ Lam := by
      have h1 : 3 * Caff * CHc * CFold * tt ≤ 3 * Caff * CHc * CFold * 1 :=
        mul_le_mul_of_nonneg_left htt1 hpart1
      rw [mul_one] at h1
      linarith only [h1, ha]
    calc 3 * Caff * CHc * CFold * tt ^ 2
        = (3 * Caff * CHc * CFold * tt) * tt := by ring
      _ ≤ Lam * tt := mul_le_mul_of_nonneg_right hb htt0.le
  have hco3 : 3 * Caff * CHc * Crefl * tt ^ 2 ≤ Lam * tt := by
    have ha : 3 * Caff * CHc * Crefl ≤ Lam := by
      rw [hLamdef]
      linarith only [hpart1, hpart2]
    have hb : 3 * Caff * CHc * Crefl * tt ≤ Lam := by
      have h1 : 3 * Caff * CHc * Crefl * tt ≤ 3 * Caff * CHc * Crefl * 1 :=
        mul_le_mul_of_nonneg_left htt1 hpart3
      rw [mul_one] at h1
      linarith only [h1, ha]
    calc 3 * Caff * CHc * Crefl * tt ^ 2
        = (3 * Caff * CHc * Crefl * tt) * tt := by ring
      _ ≤ Lam * tt := mul_le_mul_of_nonneg_right hb htt0.le
  have h21 : 21 * Caff ≤ Lam := by
    rw [hLamdef]
    linarith only [hpart1, hpart3]
  -- the absorbed application bounds
  have hEP0 : 0 ≤ normalizedL2On (truncatedWindow x m (n - 2))
        (fun y => V y - affineEval (c - vecDot A x) A y)
      + normalizedL2On (truncatedWindow x m (n - 2))
          (affineEval (c - vecDot A x) A) := add_nonneg hE0 hP0
  have hPNi0 : 0 ≤ normalizedL2On (truncatedWindow x m (n - 2))
        (affineEval (c - vecDot A x) A)
      + normalizedL2On (truncatedWindow x m (n - 2))
          (evenAffinePart x m i c A) := add_nonneg hP0 hNi0
  have p1 : Caff * (3 * (CHc * tt ^ 2
        * normalizedL2On (reflectedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)))
      ≤ Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A)) := by
    have hstep : Caff * (3 * (CHc * tt ^ 2
          * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)))
        ≤ Caff * (3 * (CHc * tt ^ 2
          * (CFold * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A))))) := by
      refine mul_le_mul_of_nonneg_left ?_ hCaff0
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left hFRle
        (mul_nonneg hCHc0 (sq_nonneg tt))
    have heq : Caff * (3 * (CHc * tt ^ 2
          * (CFold * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)))))
        = (3 * Caff * CHc * CFold * tt ^ 2)
          * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)) := by ring
    have hfin := mul_le_mul_of_nonneg_right hco1 hEP0
    calc Caff * (3 * (CHc * tt ^ 2
          * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)))
        ≤ (3 * Caff * CHc * CFold * tt ^ 2)
          * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)) := by
          rw [← heq]
          exact hstep
      _ ≤ Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A)) := hfin
  have p2 : Caff * (3 * (|A i| * delta))
      ≤ Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A)) := by
    have hstep : Caff * (3 * (|A i| * delta))
        ≤ Caff * (3 * (7 * tt * (normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (evenAffinePart x m i c A)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hCaff0
      refine mul_le_mul_of_nonneg_left hq2 (by norm_num)
    have heq : Caff * (3 * (7 * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A))))
        = (21 * Caff) * (tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A))) := by ring
    have httPNi : 0 ≤ tt * (normalizedL2On (truncatedWindow x m (n - 2))
          (affineEval (c - vecDot A x) A)
        + normalizedL2On (truncatedWindow x m (n - 2))
            (evenAffinePart x m i c A)) := mul_nonneg htt0.le hPNi0
    have hfin := mul_le_mul_of_nonneg_right h21 httPNi
    calc Caff * (3 * (|A i| * delta))
        ≤ (21 * Caff) * (tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A))) := by
          rw [← heq]
          exact hstep
      _ ≤ Lam * (tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A))) := hfin
      _ = Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A)) := by ring
  have p3 : Caff * (3 * (CHc * tt ^ 2
        * normalizedL2On (reflectedWindow x m (n - 2))
            (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y)))
      ≤ Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A))
        + Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (evenAffinePart x m i c A)) := by
    have hstep : Caff * (3 * (CHc * tt ^ 2
          * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y)))
        ≤ Caff * (3 * (CHc * tt ^ 2
          * (CFold * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A))
            + Crefl * (normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)
              + normalizedL2On (truncatedWindow x m (n - 2))
                  (evenAffinePart x m i c A))))) := by
      refine mul_le_mul_of_nonneg_left ?_ hCaff0
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left hF3R (mul_nonneg hCHc0 (sq_nonneg tt))
    have heq : Caff * (3 * (CHc * tt ^ 2
          * (CFold * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A))
            + Crefl * (normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)
              + normalizedL2On (truncatedWindow x m (n - 2))
                  (evenAffinePart x m i c A)))))
        = (3 * Caff * CHc * CFold * tt ^ 2)
            * (normalizedL2On (truncatedWindow x m (n - 2))
                (fun y => V y - affineEval (c - vecDot A x) A y)
              + normalizedL2On (truncatedWindow x m (n - 2))
                  (affineEval (c - vecDot A x) A))
          + (3 * Caff * CHc * Crefl * tt ^ 2)
            * (normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)
              + normalizedL2On (truncatedWindow x m (n - 2))
                  (evenAffinePart x m i c A)) := by ring
    have hfin1 := mul_le_mul_of_nonneg_right hco1 hEP0
    have hfin3 := mul_le_mul_of_nonneg_right hco3 hPNi0
    calc Caff * (3 * (CHc * tt ^ 2
          * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y)))
        ≤ (3 * Caff * CHc * CFold * tt ^ 2)
            * (normalizedL2On (truncatedWindow x m (n - 2))
                (fun y => V y - affineEval (c - vecDot A x) A y)
              + normalizedL2On (truncatedWindow x m (n - 2))
                  (affineEval (c - vecDot A x) A))
          + (3 * Caff * CHc * Crefl * tt ^ 2)
            * (normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)
              + normalizedL2On (truncatedWindow x m (n - 2))
                  (evenAffinePart x m i c A)) := by
          rw [← heq]
          exact hstep
      _ ≤ Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A))
          + Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (evenAffinePart x m i c A)) := add_le_add hfin1 hfin3
  -- the absorbed bounds
  have hNi2 : normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A)
      ≤ 3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
        + Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)) := by
    have hsplit : Caff * (3 * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
          + 3 * (CHc * tt ^ 2 * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)))
        = 3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
          + Caff * (3 * (CHc * tt ^ 2
            * normalizedL2On (reflectedWindow x m (n - 2))
                (fun y => V y - affineEval (c - vecDot A x) A y))) := by ring
    linarith only [h_i, hsplit, p1]
  have hNj2 : normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m j c A)
      ≤ 3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
        + Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)) := by
    have hsplit : Caff * (3 * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
          + 3 * (CHc * tt ^ 2 * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)))
        = 3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
          + Caff * (3 * (CHc * tt ^ 2
            * normalizedL2On (reflectedWindow x m (n - 2))
                (fun y => V y - affineEval (c - vecDot A x) A y))) := by ring
    linarith only [h_j, hsplit, p1]
  have hG2 : normalizedL2On (truncatedWindow x m (n - 2))
      (evenAffinePart x m j c3 A3)
      ≤ 3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
        + Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A))
        + 2 * (Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (evenAffinePart x m i c A))) := by
    have hsplit : Caff * (3 * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
          + 3 * (|A i| * delta)
          + 3 * (CHc * tt ^ 2 * normalizedL2On (reflectedWindow x m (n - 2))
              (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y)))
        = 3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y))
          + Caff * (3 * (|A i| * delta))
          + Caff * (3 * (CHc * tt ^ 2
            * normalizedL2On (reflectedWindow x m (n - 2))
                (fun y => V y - affineEval (c3 - vecDot A3 x) A3 y))) := by ring
    linarith only [h_3, hsplit, p2, p3]
  -- the linear program
  have hX : Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
        (fun y => V y - affineEval (c - vecDot A x) A y)
      + normalizedL2On (truncatedWindow x m (n - 2))
          (affineEval (c - vecDot A x) A))
      ≤ 1 / 8 * (normalizedL2On (truncatedWindow x m (n - 2))
          (fun y => V y - affineEval (c - vecDot A x) A y)
        + normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)) :=
    mul_le_mul_of_nonneg_right heps8 hEP0
  have hY : Lam * tt * (normalizedL2On (truncatedWindow x m (n - 2))
        (affineEval (c - vecDot A x) A)
      + normalizedL2On (truncatedWindow x m (n - 2))
          (evenAffinePart x m i c A))
      ≤ 1 / 8 * (normalizedL2On (truncatedWindow x m (n - 2))
          (affineEval (c - vecDot A x) A)
        + normalizedL2On (truncatedWindow x m (n - 2))
            (evenAffinePart x m i c A)) :=
    mul_le_mul_of_nonneg_right heps8 hPNi0
  have hPfin : normalizedL2On (truncatedWindow x m (n - 2))
      (affineEval (c - vecDot A x) A)
      ≤ (104 / 11) * (3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)))
        + (13 / 11) * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y) := by
    linarith only [hPsum, hNi2, hNj2, hG2, hX, hY, hE0, hP0, hNi0]
  -- conclusion
  have hEeq : normalizedL2On (truncatedWindow x m (n - 2))
      (fun y => V y - affineEval (c - vecDot A x) A y)
      = affineExcessRaw (truncatedWindow x m (n - 2)) V := hmin
  rw [← hEeq]
  have hexp : ((104 / 11) * (3 * Caff * Vr) + 24 / 11)
        * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
      = (104 / 11) * (3 * Caff * (Vr * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)))
        + (24 / 11) * normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y) := by ring
  linarith only [hVsplit, hPfin, hexp]

/-- **The corner defect pricing** —'s residue (2), the consumer shape.  At the
corner datum `(0,0)` (the only member of the collapsed odd class), the
odd-class defect is priced by the excess itself. -/
theorem exists_oddClassDefect_le_affineExcessRaw_corner (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m n : ℤ) (x : Vec d) (i j : Fin d) (V : Vec d → ℝ)
      (c : ℝ) (A : Vec d),
      x ∈ openCubeSet (originCube d m) → n - 2 < m → i ≠ j →
      MeetsUpperFace x m (n - 2) i → MeetsUpperFace x m (n - 2) j →
      (∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      (∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z) →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) →
      MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) →
      IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A →
      oddClassDefect x m n V 0 0
        ≤ C * affineExcessRaw (truncatedWindow x m (n - 2)) V := by
  obtain ⟨C, hC0, hC⟩ := exists_normalizedL2On_le_affineExcessRaw_corner d
  refine ⟨C, hC0, ?_⟩
  intro m n x i j V c A hx hmn hij hupi hupj hupV hlowV hharm hVR hmin
  have hmain := hC m n x i j V c A hx hmn hij hupi hupj hupV hlowV hharm hVR hmin
  have hzero : ∀ y : Vec d, affineEval (0 - vecDot (0 : Vec d) x) (0 : Vec d) y
      = 0 := by
    intro y
    have hv0 : ∀ z : Vec d, vecDot (0 : Vec d) z = 0 := by
      intro z
      show ∑ l, (0 : Vec d) l * z l = 0
      refine Finset.sum_eq_zero fun l _ => ?_
      show (0 : ℝ) * z l = 0
      ring
    rw [affineEval, hv0, hv0]
    ring
  have hdist : affineDistOn (truncatedWindow x m (n - 2)) V
      (0 - vecDot (0 : Vec d) x) (0 : Vec d)
      = normalizedL2On (truncatedWindow x m (n - 2)) V := by
    rw [affineDistOn]
    congr 1
    funext y
    rw [hzero y, sub_zero]
  have hEnn : 0 ≤ affineExcessRaw (truncatedWindow x m (n - 2)) V :=
    affineExcessRaw_nonneg _ _
  rw [oddClassDefect, hdist]
  linarith only [hmain, hEnn]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
