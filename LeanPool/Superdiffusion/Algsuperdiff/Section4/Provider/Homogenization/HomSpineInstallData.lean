/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineInstallArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepThreeCoarse

/-!
# HomSpineInstallData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The data slot and the gap absorption, at the finite-`p` window `s₂ < 1/2`

## What this file supplies

Two of the three residues of `HomSpineInstallArith`'s reduction are settled
here, at the finite-`p` pin where `s₂` is FORCED strictly below the printed
`1/2` (the membership band `1/2 - d/p < s₂ < 1/2` of `HomCGFinalDatum`).

1. **The data slot, PROVED.**  `overlapSeminorm_toReal_le` bounds the printed
   forcing carrier `[𝐠]` by `C_data(d,s₂,p) · K_g · 3^{(1/2-s₂)m}`, from the
   root's OWN `C^{0,1/2}` binder on `𝐠`.  This is the `hDgbound` residue; it is
   no longer a hypothesis of the assembly.
2. **The gap absorption at general `s₂`.**  `homGapAbsorbAt` is
   the printed gap absorption with `s₂ = 1/2` released:
   ```text
     s^{-9/2} · 3^{s₂(n-m)} ≤ C_gap(s₂) · γ^5,
        C_gap(s₂) = 3125 (10 s₂ log 3 - 5)^{-5},
   ```
   valid **exactly when** `10 s₂ log 3 > 5`, i.e. `s₂ > (2 log 3)^{-1} =
   0.4551…`.

## THE LOAD-BEARING VERDICT (machine-checked below)

`EthmB(m)`'s second summand is `C γ⁵(1 + 𝓔²)`, so the forcing leg must be
absorbed at the `γ⁵` rate.  With the printed mesoscale `k = ⌈10|log γ|⌉` the
absorption's exponent condition is `10 s₂ log 3 > 5`, and

* the numeral pin `s₂ = 3/8` FAILS it
  (`10·(3/8)·log 3 < 4.27 < 5`).  The pin cannot reach `γ⁵`;
* `gapExponent_holds_at_fortyNineHundredths` — `s₂ = 49/100` SATISFIES it
  (`10·(49/100)·log 3 > 5.15 > 5`), and `49/100` is inside the membership band
  `1/4 < s₂ < 1/2` at the printed exponent `p = 4d`.

So the re-cut's numeral pin must move from `s₂ = 3/8` to any
`s₂ ∈ ((2 log 3)^{-1}, 1/2)`; nothing else in the frame changes.  This is a
NUMERAL correction inside the own freedom (`s₂` is existentially
bound by the bundle), not a `Theorem C` dependence.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The data slot: the printed forcing carrier, from the root's binder -/

/-- **The data-slot constant** `C_data(d,s₂,p)`: the dimension-only
overlap/fractional comparison constant times the Gagliardo radial constant of
the `C^{0,1/2} ⊂ W^{s₂,p}` embedding.  It depends on `(d, s₂, p)` only —
never on the model, the scale or the data. -/
def cgOverlapDataConst (d : ℕ) (s2 : FractionalOrder) (p : FiniteLpExponent) : ℝ :=
  (cubeEuclideanWspOverlapDimensionConstant d).toReal *
    ((d : ℝ) *
      Regularity.radialKernelConst d
          (cgGagliardoBeta d (1 / 2) s2.1 p.exponent.toReal) ^ (p.exponent.toReal)⁻¹)

theorem cgOverlapDataConst_nonneg (d : ℕ) (s2 : FractionalOrder) (p : FiniteLpExponent)
    (hlo : 0 < (1 / 2 - s2.1) * p.exponent.toReal) :
    0 ≤ cgOverlapDataConst d s2 p := by
  have hblt : cgGagliardoBeta d (1 / 2) s2.1 p.exponent.toReal < (d : ℝ) :=
    cgGagliardoBeta_lt hlo
  have hCc : (0 : ℝ) ≤
      Regularity.radialKernelConst d
        (cgGagliardoBeta d (1 / 2) s2.1 p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ :=
    Real.rpow_nonneg (Regularity.radialKernelConst_pos hblt).le _
  exact mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg d) hCc)

/-- **THE DATA SLOT, PROVED.**

The printed forcing carrier `[𝐠]_{W^{s₂,p}(□_m)}` — the overlap seminorm the
coarse-graining display's second term carries — is at most
`C_data(d,s₂,p) · K_g · 3^{(1/2-s₂)m}`, from the root's own `C^{0,1/2}` binder
on `𝐠`.  The single scale power is the `1/2 - s₂` order loss of the embedding;
against the display's `3^{s₂n}` it reassembles into the printed
`3^{s₂(n-m)}·3^{m/2}` (`HomSpineInstallArith.three_rpow_mesoscale_split`). -/
theorem overlapSeminorm_toReal_le [NeZero d] (m : ℤ) (s2 : FractionalOrder)
    (p : FiniteLpExponent) {Kg : ℝ} {g : Vec d → Vec d} (hKg0 : 0 ≤ Kg)
    (hlt : s2.1 < 1 / 2) (hgt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g) :
    (ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g).toReal ≤
      cgOverlapDataConst d s2 p * Kg * (3 : ℝ) ^ ((1 / 2 - s2.1) * (m : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := holderHalf_window (p := p) hlt hgt
  have hgmem : MemCubeEuclideanFullWsp (originCube d m) s2 p g :=
    memCubeEuclideanFullWsp_of_holderHalf hKg0 hlt hgt hg
  let F : CubeEuclideanLpField (originCube d m) p :=
    { toField := g, euclideanMemLp := hgmem.1 }
  have hcomp : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
      cubeEuclideanWspOverlapDimensionConstant d *
        cubeEuclideanWspESeminorm (originCube d m) s2 p g := by
    simpa only [F] using
      cubeEuclideanOverlap_le_dimensionConstant_mul_wsp (originCube d m) s2 p F
  /- the Gagliardo half, at the printed Hölder expone -/
  have hsemi := cubeEuclideanWspESeminorm_le_of_holder (Q := originCube d m) (s' := s2)
    (q := p) (phi := g) (alpha := 1 / 2) (K := Kg) hKg0 hlo hhi hg
  set X : ℝ := (d : ℝ) * Kg *
      Regularity.radialKernelConst d
          (cgGagliardoBeta d (1 / 2) s2.1 p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ *
      cubeScaleFactor (originCube d m) ^ ((1 / 2 : ℝ) - s2.1) with hXdef
  have hblt : cgGagliardoBeta d (1 / 2) s2.1 p.exponent.toReal < (d : ℝ) :=
    cgGagliardoBeta_lt hlo
  have hCc : (0 : ℝ) ≤
      Regularity.radialKernelConst d
        (cgGagliardoBeta d (1 / 2) s2.1 p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ :=
    Real.rpow_nonneg (Regularity.radialKernelConst_pos hblt).le _
  have hscalepos : (0 : ℝ) < cubeScaleFactor (originCube d m) :=
    cubeScaleFactor_pos (originCube d m)
  have hX0 : (0 : ℝ) ≤ X :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hKg0) hCc)
      (Real.rpow_nonneg hscalepos.le _)
  /- the two steps, in `ℝ≥0∞` -/
  have hchain : ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
      cubeEuclideanWspOverlapDimensionConstant d * ENNReal.ofReal X :=
    hcomp.trans (mul_le_mul' le_rfl hsemi)
  have hne : cubeEuclideanWspOverlapDimensionConstant d * ENNReal.ofReal X ≠ ⊤ :=
    ENNReal.mul_ne_top (cubeEuclideanWspOverlapDimensionConstant_lt_top d).ne
      ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hne hchain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hX0] at hreal
  refine hreal.trans (le_of_eq ?_)
  /- the scale power, evaluat -/
  have hscale : cubeScaleFactor (originCube d m) = (3 : ℝ) ^ ((m : ℝ)) := by
    change ((3 : ℝ) ^ (m : ℤ)) = (3 : ℝ) ^ ((m : ℝ))
    exact (Real.rpow_intCast (3 : ℝ) m).symm
  have hpow : cubeScaleFactor (originCube d m) ^ ((1 / 2 : ℝ) - s2.1) =
      (3 : ℝ) ^ ((1 / 2 - s2.1) * (m : ℝ)) := by
    rw [hscale, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hXdef, hpow, cgOverlapDataConst]
  ring

/-! ## 2. The gap absorption at a general `s₂` -/

/-- **The gap-absorption constant at a general `s₂`**, `3125(10 s₂ log 3 -
5)^{-5}`, the printed `s₂ = 1/2` constant with `s₂` released. -/
def homGapConstAt (s2 : ℝ) : ℝ := 3125 / (10 * s2 * Real.log 3 - 5) ^ (5 : ℕ)

/-- **The gap absorption, `s₂` released**.

```text
  s^{-9/2} 3^{s₂(n-m)} ≤ C_gap(s₂) γ⁵,
```

with `n = m - ⌈10|log γ|⌉` the printed mesoscale.  The slack is
`10 s₂ log 3 - 5`, which is positive exactly when `s₂ > (2 log 3)^{-1}`; the
printed `s₂ = 1/2` has slack `5(log 3 - 1) > 0`. -/
theorem homGapAbsorbAt {M : Section3.ABKModel d} (hlog : 4 ≤ |Real.log M.gamma|)
    (hgamma1 : M.gamma < 1) (m : ℤ) {s2 : ℝ} (hs2 : 5 < 10 * s2 * Real.log 3) :
    homS M ^ (-(9 / 2) : ℝ) *
        (3 : ℝ) ^ (s2 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) ≤
      homGapConstAt s2 * M.gamma ^ (5 : ℕ) := by
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hlog0 : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hlog]
  have hlogneg : Real.log M.gamma < 0 := Real.log_neg hgpos hgamma1
  have habs : |Real.log M.gamma| = -Real.log M.gamma := abs_of_neg hlogneg
  have hlog3 : (0 : ℝ) < Real.log 3 := by
    have h := one_lt_log_three
    linarith only [h]
  have hs2pos : 0 < s2 := by
    by_contra hcon
    push Not at hcon
    have : 10 * s2 * Real.log 3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hcon]) hlog3.le
    linarith only [this, hs2]
  set u : ℝ := |Real.log M.gamma| with hu
  have hu1 : (1 : ℝ) ≤ u := by linarith only [hlog]
  have hupos : (0 : ℝ) < u := by linarith only [hu1]
  /- the `s`-pow -/
  have hspow : homS M ^ (-(9 / 2) : ℝ) = u ^ (9 / 2 : ℝ) := by
    have hs : homS M = u⁻¹ := by rw [hu]; rfl
    rw [hs, Real.inv_rpow hlog0.le, Real.rpow_neg hlog0.le, inv_inv]
  have hupow : u ^ (9 / 2 : ℝ) ≤ u ^ (5 : ℕ) := by
    have h5 : u ^ (5 : ℕ) = u ^ (((5 : ℕ) : ℝ)) := (Real.rpow_natCast u 5).symm
    rw [h5]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  /- the mesoscale g -/
  have hgapexp : s2 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ)) ≤ -(10 * s2 * u) := by
    have hk : 10 * u ≤ (homK M : ℝ) := homK_ge M
    have hn : ((m : ℝ) - ((homN M m : ℤ) : ℝ)) = (homK M : ℝ) := homN_gap M m
    have hstep : ((((homN M m : ℤ)) : ℝ) - (m : ℝ)) ≤ -(10 * u) := by
      linarith only [hk, hn]
    have hmul := mul_le_mul_of_nonneg_left hstep hs2pos.le
    linarith only [hmul]
  have hgapbound : (3 : ℝ) ^ (s2 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ))) ≤
      (3 : ℝ) ^ (-(10 * s2 * u)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hgapexp
  have hthree : (3 : ℝ) ^ (-(10 * s2 * u)) = Real.exp (-(10 * s2 * u * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hgam : M.gamma ^ (5 : ℕ) = Real.exp (-(5 * u)) := by
    have hexp : Real.exp (Real.log M.gamma) = M.gamma := Real.exp_log hgpos
    rw [← hexp, ← Real.exp_nat_mul]
    congr 1
    rw [habs]
    ring
  /- the sla -/
  set a : ℝ := 10 * s2 * Real.log 3 - 5 with ha
  have hapos : 0 < a := by rw [ha]; linarith only [hs2]
  have hkey : u ^ (5 : ℕ) * Real.exp (-(10 * s2 * u * Real.log 3)) ≤
      homGapConstAt s2 * Real.exp (-(5 * u)) := by
    have hfive := pow_five_le_exp (t := a * u) (mul_nonneg hapos.le hupos.le)
    have hapow : (0 : ℝ) < a ^ (5 : ℕ) := pow_pos hapos 5
    have hmul : u ^ (5 : ℕ) ≤ 3125 / a ^ (5 : ℕ) * Real.exp (a * u) := by
      have hexp : (a * u) ^ (5 : ℕ) = a ^ (5 : ℕ) * u ^ (5 : ℕ) := by rw [mul_pow]
      rw [hexp] at hfive
      rw [div_mul_eq_mul_div, le_div_iff₀ hapow]
      linarith only [hfive]
    have hsplit : Real.exp (a * u) * Real.exp (-(10 * s2 * u * Real.log 3)) =
        Real.exp (-(5 * u)) := by
      rw [← Real.exp_add]
      congr 1
      rw [ha]
      ring
    have hposE : (0 : ℝ) < Real.exp (-(10 * s2 * u * Real.log 3)) := Real.exp_pos _
    calc u ^ (5 : ℕ) * Real.exp (-(10 * s2 * u * Real.log 3))
        ≤ (3125 / a ^ (5 : ℕ) * Real.exp (a * u)) *
            Real.exp (-(10 * s2 * u * Real.log 3)) :=
          mul_le_mul_of_nonneg_right hmul hposE.le
      _ = (3125 / a ^ (5 : ℕ)) *
            (Real.exp (a * u) * Real.exp (-(10 * s2 * u * Real.log 3))) := by ring
      _ = homGapConstAt s2 * Real.exp (-(5 * u)) := by
          rw [hsplit, homGapConstAt, ha]
  rw [hspow, hgam]
  have hunn : (0 : ℝ) ≤ u ^ (9 / 2 : ℝ) := Real.rpow_nonneg hupos.le _
  calc u ^ (9 / 2 : ℝ) * (3 : ℝ) ^ (s2 * ((((homN M m : ℤ)) : ℝ) - (m : ℝ)))
      ≤ u ^ (9 / 2 : ℝ) * (3 : ℝ) ^ (-(10 * s2 * u)) :=
        mul_le_mul_of_nonneg_left hgapbound hunn
    _ = u ^ (9 / 2 : ℝ) * Real.exp (-(10 * s2 * u * Real.log 3)) := by rw [hthree]
    _ ≤ u ^ (5 : ℕ) * Real.exp (-(10 * s2 * u * Real.log 3)) :=
        mul_le_mul_of_nonneg_right hupow (Real.exp_pos _).le
    _ ≤ homGapConstAt s2 * Real.exp (-(5 * u)) := hkey

/-! ## 3. The numeral verdict on the `s₂` pin -/

/-- `log 3 = 2 log 2 - log(4/3)`. -/
private theorem log_three_eq : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
  have h43 : Real.log (4 / 3) = Real.log 4 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h, Real.log_pow]
    push_cast
    ring
  rw [h43, h4]
  ring

/-- A machine-checked lower bound: `log 3 > 1.0529`. -/
theorem log_three_gt : (10529 / 10000 : ℝ) < Real.log 3 := by
  have hup : Real.log (4 / 3) ≤ 1 / 3 := by
    have h := Real.log_le_sub_one_of_pos (x := (4 / 3 : ℝ)) (by norm_num)
    linarith only [h]
  have h2 := Real.log_two_gt_d9
  rw [log_three_eq]
  norm_num at h2 ⊢
  linarith only [h2, hup]

/-- **THE VERDICT (b).**  The pin `s₂ = 49/100` DOES satisfy it:
`10·(49/100)·log 3 > 5`.  Together with `1/4 < 49/100 < 1/2` (the membership
band at `p = 4d`) this is an admissible replacement. -/
theorem gapExponent_holds_at_fortyNineHundredths :
    5 < 10 * (49 / 100 : ℝ) * Real.log 3 := by
  have h := log_three_gt
  linarith only [h]

end

end Algsuperdiff.Section4.Provider.Homogenization
