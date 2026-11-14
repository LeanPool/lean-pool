/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBound

/-!
# MeanFinalPointwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `(A)`, step 1: the near-face elimination for a face-odd harmonic function

```text
  |⨍_K w| ≤ C(d) · ‖w − (w)_K‖_{L²(K)}
```

for `w` `Δ`-harmonic on the boundary-flush cube `K` and vanishing on the face
`K` shares with the frontier.  This module carries its **pointwise** half.

## The mechanism ('s, at a general face level)

Write `ρ` for the reflection in the face hyperplane `{yᵢ = a}` and let
`G = W − β` where `W` is odd about the face — so that `G` satisfies the
*reflection identity* `G ∘ ρ + G = −2β`, an identity carrying no information by
itself.  Harmonicity enters through a **second-order Taylor comparison** along
the normal, applied twice:

* to the pair `(y, ρ y)`, whose displacement is `2s·eᵢ` with `s = a − yᵢ`;
* to the pair `(y, y − w·eᵢ)`, whose displacement is `−w·eᵢ`.

The first, combined with the reflection identity, gives
`|β + G y + s·γ| ≤ 2 M w²` where `γ` is the (unknown) normal derivative of `G`
at `y`; the second gives `|G(y − w·eᵢ) − G y + w·γ| ≤ M w²` and therefore pins
`γ` down to `O(M w)`.  Eliminating `γ` — legitimate because `t = s/w ∈ (0,1]`,
which is exactly why the comparison point is taken at the **fixed** signed depth
`w` rather than at a depth proportional to `s` — leaves

```text
  |β| ≤ 2 |G y| + |G (y − w·eᵢ)| + 3 M w² .
```

* the "even part" is a **constant** `β` (the mean), not the even part of an
  affine competitor, so the reflection identity is taken as a hypothesis at the
  single point `y` rather than derived from a global affine splitting;
* the depth `w` is **signed**, so the same statement serves an upper face
  (`w > 0`) and a lower face (`w < 0`) with no case split — only the ratio
  `t = s/w ∈ (0,1]` is constrained;
* the Taylor set `T` is an arbitrary **convex** set, not the `x`-window's
  `taylorLo/taylorHi` box, so the estimate is available at the flush cube of
  `MeanControlWindowCube`, whose centre is `z` and whose face may be either.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2;
  `l.excess.decay.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The signed depth ratio -/

/-- If `0 < s/w ≤ 1` then `s` and `w` have the same sign and `s² ≤ w²`. -/
theorem sq_le_sq_of_div_mem {s w : ℝ} (h0 : 0 < s / w) (h1 : s / w ≤ 1) :
    s ^ 2 ≤ w ^ 2 := by
  have hw : w ≠ 0 := by
    intro hw
    rw [hw, div_zero] at h0
    exact lt_irrefl (0 : ℝ) h0
  have hsw : (s / w) * w = s := div_mul_cancel₀ s hw
  have hle : (s / w) ^ 2 ≤ 1 := by
    have hmul := mul_le_mul h1 h1 h0.le (by norm_num : (0 : ℝ) ≤ 1)
    calc (s / w) ^ 2 = (s / w) * (s / w) := by ring
      _ ≤ 1 * 1 := hmul
      _ = 1 := by norm_num
  have hw2 : (0 : ℝ) ≤ w ^ 2 := sq_nonneg w
  calc s ^ 2 = ((s / w) * w) ^ 2 := by rw [hsw]
    _ = (s / w) ^ 2 * w ^ 2 := by ring
    _ ≤ 1 * w ^ 2 := mul_le_mul_of_nonneg_right hle hw2
    _ = w ^ 2 := by ring

/-! ## 2. The two-point Taylor elimination -/

/-- **The near-face elimination, at a general face level and a signed depth.**

Let `G` be classically harmonic on a convex set `T` with Hessian bounded by `M`
there, and let `y ∈ T` satisfy the *reflection identity*
`G (ρ y) + G y = −2β` for the reflection `ρ` in `{yᵢ = a}`.  If both the
reflected point `ρ y` and the pushed point `y − w·eᵢ` lie in `T`, and the signed
depth ratio `(a − yᵢ)/w` lies in `(0, 1]`, then the constant `β` is priced
pointwise by the two values of `G` and a quadratic Hessian remainder:

```text
  |β| ≤ 2 |G y| + |G (y − w·eᵢ)| + 3 M w² .
```

No continuity of `G` at the face and no membership hypothesis beyond the three
listed points is used. -/
theorem abs_le_pointwise_of_reflectionIdentity {i : Fin d} {a : ℝ} {T : Set (Vec d)}
    (hT : Convex ℝ T) {G : Vec d → ℝ} {beta M w : ℝ}
    (hharm : ∀ z ∈ T, HarmonicAt (G ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      (toEuc z))
    (hMb : ∀ z ∈ T, ‖fderiv ℝ (fderiv ℝ (G ∘
      (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M)
    {y : Vec d} (hyT : y ∈ T) (hrT : coordFaceReflection a i y ∈ T)
    (hpT : y - w • (basisVec i : Vec d) ∈ T)
    (hrefl : G (coordFaceReflection a i y) + G y = -2 * beta)
    (h0 : 0 < (a - y i) / w) (h1 : (a - y i) / w ≤ 1) :
    |beta| ≤ 2 * |G y| + |G (y - w • (basisVec i : Vec d))| + 3 * M * w ^ 2 := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg
    (fderiv ℝ (fderiv ℝ (G ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)))
      (toEuc y))).trans (hMb y hyT)
  have hw : w ≠ 0 := by
    intro hw0
    rw [hw0, div_zero] at h0
    exact lt_irrefl (0 : ℝ) h0
  have hssq0 : (a - y i) ^ 2 ≤ w ^ 2 := sq_le_sq_of_div_mem h0 h1
  set s : ℝ := a - y i with hsdef
  set t : ℝ := s / w with htdef
  have hsw : t * w = s := by rw [htdef]; exact div_mul_cancel₀ s hw
  have hssq : s ^ 2 ≤ w ^ 2 := hssq0
  set gamma : ℝ :=
    fderiv ℝ (G ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc y)
      (EuclideanSpace.single i (1 : ℝ)) with hgammadef
  -- Taylor towards the reflected point
  have htay1 := abs_sub_fderiv_apply_le_of_hessian_bound_vec (V := G) (S := T)
    hT hharm hMb hyT hrT
  have hdisp1 : (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) (coordFaceReflection a i y)
      - toEuc y = toEuc ((2 * s) • (basisVec i : Vec d)) := by
    rw [← map_sub, coordFaceReflection_sub_self, hsdef]
  have hnorm1 : ‖(toEuc : Vec d → EuclideanSpace ℝ (Fin d)) (coordFaceReflection a i y)
      - toEuc y‖ = |2 * s| := by
    rw [hdisp1, norm_toEuc_smul_basisVec]
  have happ1 : fderiv ℝ (G ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc y)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) (coordFaceReflection a i y) - toEuc y)
      = 2 * s * gamma := by
    rw [hdisp1, toEuc_smul_basisVec, map_smul, hgammadef, smul_eq_mul]
  rw [hnorm1, happ1] at htay1
  -- Taylor towards the pushed point
  have htay2 := abs_sub_fderiv_apply_le_of_hessian_bound_vec (V := G) (S := T)
    hT hharm hMb hyT hpT
  have hdisp2 : (toEuc : Vec d → EuclideanSpace ℝ (Fin d))
        (y - w • (basisVec i : Vec d)) - toEuc y
      = toEuc ((-w) • (basisVec i : Vec d)) := by
    rw [← map_sub, sub_smul_basisVec_sub_self]
  have hnorm2 : ‖(toEuc : Vec d → EuclideanSpace ℝ (Fin d))
      (y - w • (basisVec i : Vec d)) - toEuc y‖ = |w| := by
    rw [hdisp2, norm_toEuc_smul_basisVec, abs_neg]
  have happ2 : fderiv ℝ (G ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc y)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) (y - w • (basisVec i : Vec d)) - toEuc y)
      = -w * gamma := by
    rw [hdisp2, toEuc_smul_basisVec, map_smul, hgammadef, smul_eq_mul]
  rw [hnorm2, happ2] at htay2
  -- the two scalar bounds
  have hB1 : |beta + G y + s * gamma| ≤ 2 * (M * w ^ 2) := by
    have hsq : M * |2 * s| ^ 2 ≤ 4 * (M * w ^ 2) := by
      have habs : |2 * s| ^ 2 = 4 * s ^ 2 := by
        rw [sq_abs]; ring
      have h4 := mul_le_mul_of_nonneg_left hssq hM0
      rw [habs]
      linarith only [h4]
    have hrw : G (coordFaceReflection a i y) - G y - 2 * s * gamma
        = -2 * (beta + G y + s * gamma) := by
      linarith only [hrefl]
    rw [hrw, abs_mul] at htay1
    have habs2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [habs2] at htay1
    linarith only [htay1, hsq]
  have hB2 : |G (y - w • (basisVec i : Vec d)) - G y + w * gamma| ≤ M * w ^ 2 := by
    have hsq : M * |w| ^ 2 = M * w ^ 2 := by rw [sq_abs]
    rw [show G (y - w • (basisVec i : Vec d)) - G y - -w * gamma
        = G (y - w • (basisVec i : Vec d)) - G y + w * gamma by ring] at htay2
    rw [hsq] at htay2
    exact htay2
  -- eliminating the unknown normal derivative
  set P : ℝ := G y with hPdef
  set Q : ℝ := G (y - w • (basisVec i : Vec d)) with hQdef
  set u1 : ℝ := beta + P + s * gamma with hu1def
  set u2 : ℝ := t * (Q - P + w * gamma) with hu2def
  have hid : beta = u1 - P - u2 + t * Q + -(t * P) := by
    rw [hu1def, hu2def, ← hsw]
    ring
  have hu2b : |u2| ≤ M * w ^ 2 := by
    rw [hu2def, abs_mul, abs_of_pos h0]
    have hstep : t * |Q - P + w * gamma| ≤ 1 * |Q - P + w * gamma| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    linarith only [hstep, hB2]
  have hMw : 0 ≤ M * w ^ 2 := mul_nonneg hM0 (sq_nonneg w)
  have hQ1 : t * Q ≤ |Q| := by
    have hA : t * Q ≤ t * |Q| := mul_le_mul_of_nonneg_left (le_abs_self Q) h0.le
    have hB : t * |Q| ≤ 1 * |Q| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    linarith only [hA, hB]
  have hQ2 : -|Q| ≤ t * Q := by
    have hA : t * (-|Q|) ≤ t * Q := mul_le_mul_of_nonneg_left (neg_abs_le Q) h0.le
    have hB : t * |Q| ≤ 1 * |Q| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    linarith only [hA, hB]
  have hP1 : t * P ≤ |P| := by
    have hA : t * P ≤ t * |P| := mul_le_mul_of_nonneg_left (le_abs_self P) h0.le
    have hB : t * |P| ≤ 1 * |P| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    linarith only [hA, hB]
  have hP2 : -|P| ≤ t * P := by
    have hA : t * (-|P|) ≤ t * P := mul_le_mul_of_nonneg_left (neg_abs_le P) h0.le
    have hB : t * |P| ≤ 1 * |P| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    linarith only [hA, hB]
  obtain ⟨h1l, h1r⟩ := abs_le.1 hB1
  obtain ⟨h2l, h2r⟩ := abs_le.1 hu2b
  have hPl : -|P| ≤ P := neg_abs_le P
  have hPr : P ≤ |P| := le_abs_self P
  refine abs_le.2 ⟨?_, ?_⟩ <;> rw [hid] <;>
    linarith only [h1l, h1r, h2l, h2r, hQ1, hQ2, hP1, hP2, hPl, hPr, hMw]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
