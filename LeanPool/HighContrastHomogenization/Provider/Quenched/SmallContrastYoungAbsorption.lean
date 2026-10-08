/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastYoungAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Young absorption for the small-contrast response bound

The pre-Young response estimate contains mixed square-root products.  At small
terminal energy, a tunable Young inequality absorbs the energy contribution
back into the response and leaves a linear bound in the defect, row, and weak
terms.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

private theorem sqrt_mul_sqrt_le_div_add_mul
    {x y eta : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (heta : 0 < eta) :
    Real.sqrt x * Real.sqrt y ≤ x / (4 * eta) + eta * y := by
  have hsquare :
      0 ≤ (Real.sqrt x - 2 * eta * Real.sqrt y) ^ (2 : ℕ) :=
    sq_nonneg _
  have hxSq : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx
  have hySq : Real.sqrt y ^ (2 : ℕ) = y := Real.sq_sqrt hy
  have hdenPos : 0 < 4 * eta := by positivity
  have hscaled :
      (Real.sqrt x * Real.sqrt y) * (4 * eta) ≤
        x + 4 * eta ^ (2 : ℕ) * y := by
    nlinarith only [hsquare, hxSq, hySq]
  have hquotient :
      x / (4 * eta) + eta * y =
        (x + 4 * eta ^ (2 : ℕ) * y) / (4 * eta) := by
    field_simp
  rw [hquotient]
  exact (le_div_iff₀ hdenPos).2 hscaled

private theorem sqrt_mul_sqrt_le_half_add
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
  have hsquare : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ (2 : ℕ) :=
    sq_nonneg _
  have hxSq : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx
  have hySq : Real.sqrt y ^ (2 : ℕ) = y := Real.sq_sqrt hy
  nlinarith only [hsquare, hxSq, hySq]

/-- A mixed pre-Young response estimate becomes linear after absorbing an
energy bounded by the response plus a nonnegative center error. -/
theorem response_le_linear_of_preYoung
    {response energy defect row weak center C expo eta : ℝ}
    (hresponse : 0 ≤ response) (henergy : 0 ≤ energy)
    (hdefect : 0 ≤ defect) (hrow : 0 ≤ row)
    (hcenter : 0 ≤ center) (hC : 0 ≤ C) (hexpo : 0 ≤ expo)
    (hexpoOne : expo ≤ 1)
    (heta : 0 < eta)
    (henergyResponse : energy ≤ response + center)
    (hpreYoung :
      response ≤
        C * Real.sqrt defect *
            (Real.sqrt defect + Real.sqrt energy + Real.sqrt row) +
          C * expo * Real.sqrt energy *
            (Real.sqrt energy + Real.sqrt row) + C * weak)
    (habsorb : C * eta + (3 / 2 : ℝ) * C * expo ≤ 1 / 2) :
    response ≤
      2 * C * ((3 / 2 + 1 / (4 * eta)) * defect + row + weak) +
        center := by
  have hde : Real.sqrt defect * Real.sqrt energy ≤
      defect / (4 * eta) + eta * energy :=
    sqrt_mul_sqrt_le_div_add_mul hdefect henergy heta
  have hdr : Real.sqrt defect * Real.sqrt row ≤
      (defect + row) / 2 :=
    sqrt_mul_sqrt_le_half_add hdefect hrow
  have her : Real.sqrt energy * Real.sqrt row ≤
      (energy + row) / 2 :=
    sqrt_mul_sqrt_le_half_add henergy hrow
  have hdefectSq : Real.sqrt defect ^ (2 : ℕ) = defect :=
    Real.sq_sqrt hdefect
  have henergySq : Real.sqrt energy ^ (2 : ℕ) = energy :=
    Real.sq_sqrt henergy
  have hCde := mul_le_mul_of_nonneg_left hde hC
  have hCdr := mul_le_mul_of_nonneg_left hdr hC
  have hCE0 : 0 ≤ C * expo := mul_nonneg hC hexpo
  have hCexpo : C * expo ≤ C := by
    calc
      C * expo ≤ C * 1 := mul_le_mul_of_nonneg_left hexpoOne hC
      _ = C := mul_one C
  have hCer := mul_le_mul_of_nonneg_left her hCE0
  let a : ℝ := C * eta + (3 / 2 : ℝ) * C * expo
  let B : ℝ :=
    C * ((3 / 2 + 1 / (4 * eta)) * defect + row + weak)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have haHalf : a ≤ 1 / 2 := by
    simpa only [a] using habsorb
  have hlinear : response ≤ B + a * energy := by
    calc
      response ≤
          C * defect + C * (Real.sqrt defect * Real.sqrt energy) +
              C * (Real.sqrt defect * Real.sqrt row) +
            C * expo * energy +
              C * expo * (Real.sqrt energy * Real.sqrt row) + C * weak := by
        calc
          response ≤
              C * Real.sqrt defect *
                  (Real.sqrt defect + Real.sqrt energy + Real.sqrt row) +
                C * expo * Real.sqrt energy *
                  (Real.sqrt energy + Real.sqrt row) + C * weak := hpreYoung
          _ = C * Real.sqrt defect ^ (2 : ℕ) +
                C * (Real.sqrt defect * Real.sqrt energy) +
                C * (Real.sqrt defect * Real.sqrt row) +
              C * expo * Real.sqrt energy ^ (2 : ℕ) +
                C * expo * (Real.sqrt energy * Real.sqrt row) + C * weak := by
            ring
          _ = _ := by rw [hdefectSq, henergySq]
      _ ≤ C * defect + C * (defect / (4 * eta) + eta * energy) +
              C * ((defect + row) / 2) +
            C * expo * energy + C * expo * ((energy + row) / 2) +
              C * weak := by
        gcongr
      _ = C * defect + C * (defect / (4 * eta) + eta * energy) +
              C * ((defect + row) / 2) +
            C * expo * energy + C * expo * (energy / 2) +
              C * expo * (row / 2) + C * weak := by
        ring
      _ ≤ C * defect + C * (defect / (4 * eta) + eta * energy) +
              C * ((defect + row) / 2) +
            C * expo * energy + C * expo * (energy / 2) +
              C * (row / 2) + C * weak := by
        gcongr
      _ = B + a * energy := by
        dsimp only [B, a]
        ring
  have henergyScaled : a * energy ≤ a * (response + center) :=
    mul_le_mul_of_nonneg_left henergyResponse ha0
  have hchain : response ≤ B + a * (response + center) :=
    hlinear.trans (add_le_add le_rfl henergyScaled)
  have hfinal : response ≤ 2 * B + center := by
    nlinarith only [hchain, haHalf, ha0, hresponse, hcenter]
  simpa only [B, mul_assoc] using hfinal

end

end HCPolySupport.HighContrast.Quenched
