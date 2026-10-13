/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutClose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCloseRecut

/-!
# HomSpineInstallArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The §4.5 level arithmetic of the re-cut bundle, reduced to its residues

## What this file supplies

The re-cut bundle carries two arithmetic conditions, `hlevel`
and `hlevelDual`, on the printed right-hand side `coarseGrainingFinitePRHS`.
This file EXPANDS both at the display's own data and reduces them to the
smallest set of residues, proving every model-side piece outright:

* the `σ`-bookkeeping `σ · dataBracket = 3^{m/2}K_g + σ(K_h^∞ + 3^{m/2}K_h)`
  and `√σ · energyBracket = σ · dataBracket`;
* the `3`-power split `3^{s₂n} · 3^{(1/2-s₂)m} = 3^{s₂(n-m)} · 3^{m/2}`
  (the printed display's `3^{\frac12(n-m)} 3^{\frac12 m}`, at general `s₂`);
* **the dual-order cancellation**: `K_test(□_m, s, s′, p′) · 3^{s′m} =
  d(1 + C_rad^{1/p′}) · 3^{sm}` — the `3^{sm}` on the two sides of `hlevelDual`
  cancel EXACTLY, so the dual condition is the SAME arithmetic read at `s′`
  with one extra dimensional constant.

## The residues that survive

`coarseGrainingFinitePRHS_le_of_energyBound` is the reduction.  Its three
content-bearing hypotheses are:

1. `hSbound: S ≤ C_en · energyBracket σ 3^{m/2} K_g K_h^∞ K_h` — **the
   Theorem-C residue**: the Step-2 energy-density datum (
   the mesoscale energy bound), whose `C_en` carries `3^{(1-α)X_m(α)}`;
2. `hDgbound: D_g ≤ C_data · K_g · 3^{(1/2-s₂)m}` — the data slot; PROVED for
   the pinned carrier in `HomSpineInstallData`;
3. `hA`, `hB` — **the `E_B` pairing**: the two summands of the printed constant
   against the two summands of `EthmB(m)` ("comparing to the
   definition of `EthmB(m)`").

Everything else in the two conditions is discharged here.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The `σ` bookkeeping of the printed level -/

/-- **The printed level, expanded.**  `σ · D = 3^{m/2}K_g + σ(K_h^∞ +
3^{m/2}K_h)`: the `σ^{-1}` of the introduction's homogenization estimate's bracket is
cancelled by the `σ` weight of the coarse-graining display's right-hand side.
No inequality is spent. -/
theorem sigma_mul_dataBracket (sigma pow Kg KhInf Kh : ℝ) (hsig : 0 < sigma) :
    sigma * dataBracket sigma pow Kg KhInf Kh =
      pow * Kg + sigma * (KhInf + pow * Kh) := by
  have hne : sigma ≠ 0 := ne_of_gt hsig
  rw [dataBracket]
  field_simp

/-- The expanded level is nonnegative on the printed data. -/
theorem sigma_mul_dataBracket_nonneg {sigma pow Kg KhInf Kh : ℝ} (hsig : 0 < sigma)
    (hpow : 0 ≤ pow) (hKg : 0 ≤ Kg) (hKhInf : 0 ≤ KhInf) (hKh : 0 ≤ Kh) :
    0 ≤ sigma * dataBracket sigma pow Kg KhInf Kh := by
  have h1 : (0 : ℝ) ≤ pow * Kg := mul_nonneg hpow hKg
  have h2 : (0 : ℝ) ≤ sigma * (KhInf + pow * Kh) :=
    mul_nonneg hsig.le (by
      have h := mul_nonneg hpow hKh
      linarith only [hKhInf, h])
  rw [sigma_mul_dataBracket sigma pow Kg KhInf Kh hsig]
  linarith only [h1, h2]

/-- The data leg alone is below the expanded level. -/
theorem dataLeg_le_sigma_mul_dataBracket {sigma pow Kg KhInf Kh : ℝ} (hsig : 0 < sigma)
    (hpow : 0 ≤ pow) (hKhInf : 0 ≤ KhInf) (hKh : 0 ≤ Kh) :
    pow * Kg ≤ sigma * dataBracket sigma pow Kg KhInf Kh := by
  have h2 : (0 : ℝ) ≤ sigma * (KhInf + pow * Kh) :=
    mul_nonneg hsig.le (by
      have h := mul_nonneg hpow hKh
      linarith only [hKhInf, h])
  rw [sigma_mul_dataBracket sigma pow Kg KhInf Kh hsig]
  linarith only [h2]

/-- **The `√σ` half of the same bookkeeping**: the display's `σ^{1/2}` weight
turns the Step-2 the introduction's energy display bracket into the printed level. -/
theorem sqrt_mul_energyBracket (sigma pow Kg KhInf Kh : ℝ) (hsig : 0 < sigma) :
    Real.sqrt sigma * energyBracket sigma pow Kg KhInf Kh =
      sigma * dataBracket sigma pow Kg KhInf Kh := by
  have hkey : Real.sqrt sigma * dataBracket sigma pow Kg KhInf Kh =
      energyBracket sigma pow Kg KhInf Kh :=
    sqrt_mul_dataBracket sigma pow Kg KhInf Kh hsig
  have hsq : Real.sqrt sigma * Real.sqrt sigma = sigma :=
    Real.mul_self_sqrt (le_of_lt hsig)
  rw [← hkey, ← mul_assoc, hsq]

/-! ## 2. The `3`-power split of the forcing leg -/

/-- **The mesoscale `3`-power split at general `s₂`**:
`3^{s₂n} · 3^{(1/2-s₂)m} = 3^{s₂(n-m)} · 3^{m/2}`.  Exact. -/
theorem three_rpow_mesoscale_split (s2 : ℝ) (m n : ℤ) :
    (3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * (3 : ℝ) ^ ((1 / 2 - s2) * (m : ℝ)) =
      (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) * (3 : ℝ) ^ ((m : ℝ) / 2) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-! ## 3. THE REDUCTION -/

/-- **The printed right-hand side, reduced to its three residues.**

Every model-side piece of the §4.5 level arithmetic is discharged; what remains
on the right is the single product `(A + B) · (σ · dataBracket)`, i.e. the
printed level with the two constants left abstract.

* `hSbound` is the Theorem-C residue (the Step-2 energy-density datum);
* `hDgbound` is the data slot (proved for the pinned carrier elsewhere);
* `hA`, `hB` are the two `EthmB(m)` pairings. -/
theorem coarseGrainingFinitePRHS_le_of_energyBound {Ccg s s2 sigma E1 E2 Dg S : ℝ}
    {Cen Cdata Kg KhInf Kh A B : ℝ} {m n : ℤ}
    (hsig : 0 < sigma) (hs0 : 0 < s) (hss2 : s < s2)
    (hCcg0 : 0 ≤ Ccg) (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2)
    (hKg0 : 0 ≤ Kg) (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh)
    (hCen0 : 0 ≤ Cen) (hCdata0 : 0 ≤ Cdata)
    (hSbound : S ≤ Cen * energyBracket sigma ((3 : ℝ) ^ ((m : ℝ) / 2)) Kg KhInf Kh)
    (hDgbound : Dg ≤ Cdata * Kg * (3 : ℝ) ^ ((1 / 2 - s2) * (m : ℝ)))
    (hA : Ccg * s⁻¹ * E1 * Cen ≤ A)
    (hB : Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
        (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) ≤ B) :
    coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n ≤
      (A + B) * (sigma * dataBracket sigma ((3 : ℝ) ^ ((m : ℝ) / 2)) Kg KhInf Kh) := by
  set pow : ℝ := (3 : ℝ) ^ ((m : ℝ) / 2) with hpowdef
  have hpow0 : (0 : ℝ) ≤ pow := Real.rpow_nonneg (by norm_num) _
  set D : ℝ := dataBracket sigma pow Kg KhInf Kh with hDdef
  have hsD0 : (0 : ℝ) ≤ sigma * D :=
    sigma_mul_dataBracket_nonneg hsig hpow0 hKg0 hKhInf0 hKh0
  have hleg : pow * Kg ≤ sigma * D :=
    dataLeg_le_sigma_mul_dataBracket hsig hpow0 hKhInf0 hKh0
  /- the first te -/
  have hcoef1 : (0 : ℝ) ≤ Ccg * s⁻¹ * E1 :=
    mul_nonneg (mul_nonneg hCcg0 (inv_nonneg.mpr hs0.le)) hE10
  have hA0 : (0 : ℝ) ≤ A := le_trans (mul_nonneg hcoef1 hCen0) hA
  have hT1 : Ccg * s⁻¹ * Real.sqrt sigma * E1 * S ≤ A * (sigma * D) := by
    have hstep : Real.sqrt sigma * S ≤ Cen * (sigma * D) := by
      have h := mul_le_mul_of_nonneg_left hSbound (Real.sqrt_nonneg sigma)
      calc Real.sqrt sigma * S
          ≤ Real.sqrt sigma * (Cen * energyBracket sigma pow Kg KhInf Kh) := h
        _ = Cen * (Real.sqrt sigma * energyBracket sigma pow Kg KhInf Kh) := by ring
        _ = Cen * (sigma * D) := by rw [sqrt_mul_energyBracket sigma pow Kg KhInf Kh hsig]
    calc Ccg * s⁻¹ * Real.sqrt sigma * E1 * S
        = (Ccg * s⁻¹ * E1) * (Real.sqrt sigma * S) := by ring
      _ ≤ (Ccg * s⁻¹ * E1) * (Cen * (sigma * D)) :=
          mul_le_mul_of_nonneg_left hstep hcoef1
      _ = (Ccg * s⁻¹ * E1 * Cen) * (sigma * D) := by ring
      _ ≤ A * (sigma * D) := mul_le_mul_of_nonneg_right hA hsD0
  /- the second te -/
  have hdiff : (0 : ℝ) < s2 - s := by linarith only [hss2]
  have hspow : (0 : ℝ) ≤ s ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
  have hE2sq : (0 : ℝ) ≤ 1 + E2 ^ (2 : ℕ) := by
    have h : (0 : ℝ) ≤ E2 ^ (2 : ℕ) := pow_nonneg hE20 2
    linarith only [h]
  have hcoef2 : (0 : ℝ) ≤ Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCcg0 hspow) (inv_nonneg.mpr hdiff.le)) hE2sq
  have hgap0 : (0 : ℝ) ≤ (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hB0 : (0 : ℝ) ≤ B :=
    le_trans (mul_nonneg (mul_nonneg hcoef2 hCdata0) hgap0) hB
  have hmeso0 : (0 : ℝ) ≤ (3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hT2 : Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
      ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) ≤ B * (sigma * D) := by
    have hinner : (3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg ≤
        (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) * Cdata * (pow * Kg) := by
      calc (3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg
          ≤ (3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) *
              (Cdata * Kg * (3 : ℝ) ^ ((1 / 2 - s2) * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hDgbound hmeso0
        _ = ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * (3 : ℝ) ^ ((1 / 2 - s2) * (m : ℝ))) *
              (Cdata * Kg) := by ring
        _ = ((3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) * pow) * (Cdata * Kg) := by
            rw [three_rpow_mesoscale_split s2 m n]
        _ = (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) * Cdata * (pow * Kg) := by ring
      /- the `Cdata` factor is carried into `B` -/
    calc Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)
        ≤ Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
            ((3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) * Cdata * (pow * Kg)) :=
          mul_le_mul_of_nonneg_left hinner hcoef2
      _ = (Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
            (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ)))) * (pow * Kg) := by ring
      _ ≤ B * (pow * Kg) := mul_le_mul_of_nonneg_right hB (mul_nonneg hpow0 hKg0)
      _ ≤ B * (sigma * D) := mul_le_mul_of_nonneg_left hleg hB0
  rw [coarseGrainingFinitePRHS_def]
  have hsum : Ccg * s⁻¹ * Real.sqrt sigma * E1 * S +
      Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
        ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) ≤ A * (sigma * D) + B * (sigma * D) :=
    add_le_add hT1 hT2
  calc Ccg * s⁻¹ * Real.sqrt sigma * E1 * S +
        Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)
      ≤ A * (sigma * D) + B * (sigma * D) := hsum
    _ = (A + B) * (sigma * D) := by ring

/-! ## 4. `hlevel`, from the residues -/

/-- **THE BUNDLE'S `hlevel`, from the named residues alone.**

The conclusion is byte-identical to the `hlevel` conjunct of the re-cut
bundle. -/
theorem hlevel_of_energyBound {Ccg s s2 sigma E1 E2 Dg S : ℝ}
    {Cen Cdata Cw EB Kg KhInf Kh A B : ℝ} {m n : ℤ}
    (hsig : 0 < sigma) (hs0 : 0 < s) (hss2 : s < s2)
    (hCcg0 : 0 ≤ Ccg) (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2)
    (hKg0 : 0 ≤ Kg) (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh)
    (hCen0 : 0 ≤ Cen) (hCdata0 : 0 ≤ Cdata)
    (hSbound : S ≤ Cen * energyBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hDgbound : Dg ≤ Cdata * Kg * (3 : ℝ) ^ ((1 / 2 - s2) * (m : ℝ)))
    (hA : Ccg * s⁻¹ * E1 * Cen ≤ A)
    (hB : Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
        (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))) ≤ B)
    (hsplit : A + B ≤ Cw * EB) :
    coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n ≤
      sigma * (Cw * EB * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
  have hpow0 : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hsD0 : (0 : ℝ) ≤ sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    sigma_mul_dataBracket_nonneg hsig hpow0 hKg0 hKhInf0 hKh0
  have hbase := coarseGrainingFinitePRHS_le_of_energyBound (Ccg := Ccg) (s := s) (s2 := s2)
    (sigma := sigma) (E1 := E1) (E2 := E2) (Dg := Dg) (S := S) (Cen := Cen)
    (Cdata := Cdata) (Kg := Kg) (KhInf := KhInf) (Kh := Kh) (A := A) (B := B)
    (m := m) (n := n) hsig hs0 hss2 hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0 hCen0 hCdata0
    hSbound hDgbound hA hB
  refine hbase.trans ?_
  calc (A + B) * (sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
      ≤ (Cw * EB) *
          (sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) :=
        mul_le_mul_of_nonneg_right hsplit hsD0
    _ = sigma * (Cw * EB * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
        ring

/-! ## 5. The dual-order cancellation, and `hlevelDual` -/

/-- **The scale-free half of the test-class constant**, `d(1 + C_rad^{1/t})`.
`cgTestConst` is this times the single scale power `L^{α-s′}`. -/
def cgTestConstBase (d : ℕ) (alpha s' t : ℝ) : ℝ :=
  (d : ℝ) * (1 + Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹)

theorem cgTestConstBase_nonneg (d : ℕ) {alpha s' t : ℝ} (hlo : 0 < (alpha - s') * t) :
    0 ≤ cgTestConstBase d alpha s' t := by
  have hblt : cgGagliardoBeta d alpha s' t < (d : ℝ) := cgGagliardoBeta_lt hlo
  have hCc : (0 : ℝ) ≤
      Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹ :=
    Real.rpow_nonneg (Regularity.radialKernelConst_pos hblt).le _
  rw [cgTestConstBase]
  exact mul_nonneg (Nat.cast_nonneg d) (by linarith only [hCc])

/-- **THE DUAL-ORDER CANCELLATION.**

`K_test(□_m, α, s′, t) · 3^{s′m} = d(1 + C_rad^{1/t}) · 3^{αm}`.  The single
scale power the order-losing test-class comparison carries is EXACTLY the one
that turns the display's own `3^{s′m}` into the consumption site's `3^{αm}`, so
the `3^{αm}` factors on the two sides of `hlevelDual` cancel and the dual
condition is the plain level condition read at the dual order. -/
theorem cgTestConst_mul_rpow_originCube (d : ℕ) (m : ℤ) (alpha s' t : ℝ) :
    cgTestConst d (originCube d m) alpha s' t * Real.rpow 3 (s' * (m : ℝ)) =
      cgTestConstBase d alpha s' t * Real.rpow 3 (alpha * (m : ℝ)) := by
  change cgTestConst d (originCube d m) alpha s' t * (3 : ℝ) ^ (s' * (m : ℝ)) =
      cgTestConstBase d alpha s' t * (3 : ℝ) ^ (alpha * (m : ℝ))
  have hscale : cubeScaleFactor (originCube d m) = (3 : ℝ) ^ ((m : ℝ)) := by
    change ((3 : ℝ) ^ (m : ℤ)) = (3 : ℝ) ^ ((m : ℝ))
    exact (Real.rpow_intCast (3 : ℝ) m).symm
  have hpow : (cubeScaleFactor (originCube d m)) ^ (alpha - s') =
      (3 : ℝ) ^ ((m : ℝ) * (alpha - s')) := by
    rw [hscale, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hmul : (3 : ℝ) ^ ((m : ℝ) * (alpha - s')) * (3 : ℝ) ^ (s' * (m : ℝ)) =
      (3 : ℝ) ^ (alpha * (m : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [cgTestConst_def, cgTestConstBase, hpow]
  calc (d : ℝ) * (3 : ℝ) ^ ((m : ℝ) * (alpha - s')) *
        (1 + Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹) *
        (3 : ℝ) ^ (s' * (m : ℝ))
      = (d : ℝ) *
          (1 + Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹) *
          ((3 : ℝ) ^ ((m : ℝ) * (alpha - s')) * (3 : ℝ) ^ (s' * (m : ℝ))) := by
        ring
    _ = (d : ℝ) *
          (1 + Regularity.radialKernelConst d (cgGagliardoBeta d alpha s' t) ^ t⁻¹) *
          (3 : ℝ) ^ (alpha * (m : ℝ)) := by rw [hmul]

/-- **THE BUNDLE'S `hlevelDual`, from the named residues alone.**

The conclusion is byte-identical to the `hlevelDual` conjunct of the re-cut
bundle.  The residues are the SAME three as `hlevel`'s,
read at the dual order `s′` and carrying the one extra factor
`cgTestConstBase d s s′ p′`. -/
theorem hlevelDual_of_energyBound {Ccg s s' s2 sigma E1 E2 Dg S : ℝ}
    {Cen Cdata Cw EB Kg KhInf Kh A B t : ℝ} {m n : ℤ}
    (hsig : 0 < sigma) (hs'0 : 0 < s') (hs's2 : s' < s2) (hlo : 0 < (s - s') * t)
    (hCcg0 : 0 ≤ Ccg) (hE10 : 0 ≤ E1) (hE20 : 0 ≤ E2)
    (hKg0 : 0 ≤ Kg) (hKhInf0 : 0 ≤ KhInf) (hKh0 : 0 ≤ Kh)
    (hCen0 : 0 ≤ Cen) (hCdata0 : 0 ≤ Cdata)
    (hSbound : S ≤ Cen * energyBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hDgbound : Dg ≤ Cdata * Kg * (3 : ℝ) ^ ((1 / 2 - s2) * (m : ℝ)))
    (hA : cgTestConstBase d s s' t * (Ccg * s'⁻¹ * E1 * Cen) ≤ A)
    (hB : cgTestConstBase d s s' t *
        (Ccg * s' ^ (-(9 / 2) : ℝ) * (s2 - s')⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
          (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ)))) ≤ B)
    (hsplit : A + B ≤ Cw * EB) :
    cgTestConst d (originCube d m) s s' t *
        (Real.rpow 3 (s' * (m : ℝ)) *
          coarseGrainingFinitePRHS Ccg s' s2 sigma E1 E2 Dg S n) ≤
      Real.rpow 3 (s * (m : ℝ)) *
        (sigma * (Cw * EB * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) := by
  set K : ℝ := cgTestConstBase d s s' t with hKdef
  have hK0 : (0 : ℝ) ≤ K := cgTestConstBase_nonneg d hlo
  have hpow0 : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hsD0 : (0 : ℝ) ≤ sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh :=
    sigma_mul_dataBracket_nonneg hsig hpow0 hKg0 hKhInf0 hKh0
  have hthree0 : (0 : ℝ) ≤ Real.rpow 3 (s * (m : ℝ)) := Real.rpow_nonneg (by norm_num) _
  /- the reduction at the dual ord -/
  have hbase := coarseGrainingFinitePRHS_le_of_energyBound (Ccg := Ccg) (s := s') (s2 := s2)
    (sigma := sigma) (E1 := E1) (E2 := E2) (Dg := Dg) (S := S) (Cen := Cen)
    (Cdata := Cdata) (Kg := Kg) (KhInf := KhInf) (Kh := Kh)
    (A := Ccg * s'⁻¹ * E1 * Cen)
    (B := Ccg * s' ^ (-(9 / 2) : ℝ) * (s2 - s')⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
      (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))))
    (m := m) (n := n) hsig hs'0 hs's2 hCcg0 hE10 hE20 hKg0 hKhInf0 hKh0 hCen0 hCdata0
    hSbound hDgbound le_rfl le_rfl
  /- carry the test constant throu -/
  have hscaled : K * coarseGrainingFinitePRHS Ccg s' s2 sigma E1 E2 Dg S n ≤
      (Cw * EB) * (sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
    have hstep := mul_le_mul_of_nonneg_left hbase hK0
    refine hstep.trans ?_
    have hKAB : K * (Ccg * s'⁻¹ * E1 * Cen +
        Ccg * s' ^ (-(9 / 2) : ℝ) * (s2 - s')⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
          (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ)))) ≤ Cw * EB := by
      have hexp : K * (Ccg * s'⁻¹ * E1 * Cen +
          Ccg * s' ^ (-(9 / 2) : ℝ) * (s2 - s')⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
            (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ)))) =
          K * (Ccg * s'⁻¹ * E1 * Cen) +
            K * (Ccg * s' ^ (-(9 / 2) : ℝ) * (s2 - s')⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
              (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ)))) := by ring
      rw [hexp]
      linarith only [hA, hB, hsplit]
    calc K * ((Ccg * s'⁻¹ * E1 * Cen +
            Ccg * s' ^ (-(9 / 2) : ℝ) * (s2 - s')⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
              (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ)))) *
          (sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
        = (K * (Ccg * s'⁻¹ * E1 * Cen +
            Ccg * s' ^ (-(9 / 2) : ℝ) * (s2 - s')⁻¹ * (1 + E2 ^ (2 : ℕ)) * Cdata *
              (3 : ℝ) ^ (s2 * ((n : ℝ) - (m : ℝ))))) *
            (sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) := by
          ring
      _ ≤ (Cw * EB) *
            (sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) :=
          mul_le_mul_of_nonneg_right hKAB hsD0
  /- the cancellati -/
  calc cgTestConst d (originCube d m) s s' t *
        (Real.rpow 3 (s' * (m : ℝ)) *
          coarseGrainingFinitePRHS Ccg s' s2 sigma E1 E2 Dg S n)
      = (cgTestConst d (originCube d m) s s' t * Real.rpow 3 (s' * (m : ℝ))) *
          coarseGrainingFinitePRHS Ccg s' s2 sigma E1 E2 Dg S n := by ring
    _ = (K * Real.rpow 3 (s * (m : ℝ))) *
          coarseGrainingFinitePRHS Ccg s' s2 sigma E1 E2 Dg S n := by
        rw [cgTestConst_mul_rpow_originCube d m s s' t]
    _ = Real.rpow 3 (s * (m : ℝ)) *
          (K * coarseGrainingFinitePRHS Ccg s' s2 sigma E1 E2 Dg S n) := by ring
    _ ≤ Real.rpow 3 (s * (m : ℝ)) *
          ((Cw * EB) *
            (sigma * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) :=
        mul_le_mul_of_nonneg_left hscaled hthree0
    _ = Real.rpow 3 (s * (m : ℝ)) *
          (sigma *
            (Cw * EB * dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)) := by
        ring

end

end Algsuperdiff.Section4.Provider.Homogenization
