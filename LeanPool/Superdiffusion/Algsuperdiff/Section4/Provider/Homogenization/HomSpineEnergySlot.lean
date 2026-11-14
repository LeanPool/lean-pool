/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineEnergyDensity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueLevel

/-!
# HomSpineEnergySlot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The §4.5 supplier's energy slot, produced from Theorem C

## What this file supplies

The supplier asks, per `ω` and per elliptic pair, for a real `S` with

```text
  0 ≤ S,     ∀ N, coarseGrainingEnergyPartial □_m p (s - s/4) j_n N Gen ≤ S,
  S ≤ C_en · recutEnergyFactor · energyBracket σ_m 3^{m/2} K_g K_h^∞ K_h
```

at `Gen:= printedLocalEnergy` (the cutoff field's own per-cell energy).  This
is the **Theorem-C item** of the §4.5 spine.  `energySlot_of_regularityDisplay`
produces all three from

1. `HomSpineEnergyDensity.RegularityEnergyDisplay` — Theorem C's
   first conjunct, sliced (deep range only; the shallow range is recovered
   inside `printedLocalEnergy_le_of_display` by the sub-cube average step);
2. the printed order identification `1 - α = s/2` (the §4.5 web's own pin,
   which is what makes the `s₁ = s/4` weight gap positive — see
   `coarseGrainingEnergyPartial_le_at_quarterPin`);
3. `htop` — **the top-scale datum**, the ONE remaining input: the minimal-scale
   factor times Theorem C's own three-term bracket is below the printed Step-2
   random factor `3^{(1-α)X_m(α)}(1 + 𝓔_{1/4})` times the printed data bracket.
   That is exactly the printed display's constant shape; the `Y` slot of
   `recutEnergyFactor` carries `3^{(1-α)X_m(α)}` and the `(1 + 𝓔_{1/4})` factor
   absorbs the bracket's own top-scale energy `√ν‖∇u‖_{L²(□_m)}` against the
   `BoundsMathcalEaL` datum.  It is stated explicitly, not assumed away.

## The constant

`recutEnergySlotConst` is the deterministic half of `C_en`: the Theorem-C
constant, the mesoscale depth factor `3^{(1-α)j_n}` at the `j_n = homK M` pin,
and the finite-`p` geometric factor `(1 - 3^{-(s/4)p})^{-1/p}` the `ℓ^p` slot
pays over the `p = ∞` sup.  No randomness, no `ν`, no `σ`.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. One piece of bookkeeping -/

/-- The finite-`p` geometric factor is nonnegative on the printed window. -/
theorem coarseGrainingGeomFactor_nonneg {p w : ℝ} (hp : 0 < p) (hw : 0 < w) :
    0 ≤ coarseGrainingGeomFactor p w := by
  have hr : (3 : ℝ) ^ (-(w * p)) < 1 := three_rpow_neg_lt_one (mul_pos hw hp)
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(w * p)) := by linarith only [hr]
  rw [coarseGrainingGeomFactor_def]
  exact Real.rpow_nonneg (inv_nonneg.mpr hden.le) _

/-! ## 2. The deterministic half of the Step-2 constant -/

/-- **The deterministic Step-2 constant of the energy slot.**

The Theorem-C constant `C`, the mesoscale depth factor `3^{(1-α)j_n}`, and the
finite-`p` geometric factor.  Model-independent: no `ω`, no `ν`, no `σ`. -/
def recutEnergySlotConst (Creg alpha p s : ℝ) (jn : ℕ) : ℝ :=
  Creg * (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) * coarseGrainingGeomFactor p (s / 4)

/-! ## 3. The Step-2b family bound at the `s₁ = s/4` pin -/

/-- **The printed family bound.**

At depth `j_n + i` below `□_m` the per-cube energy grows at most like
`3^{(s/2)i}` — the §4.5 web's `1 - α = s/2` — off the depth-`j_n` value.  This
is the exact hypothesis `coarseGrainingEnergyPartial_le_at_quarterPin`
consumes. -/
theorem printedLocalEnergy_le_family {M : ABKModel d} {m : ℤ} {X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {Creg alpha : ℝ} {T : ℝ≥0∞}
    (hdisp : RegularityEnergyDisplay M m X u Creg alpha T) (hT : T ≠ ⊤)
    (halpha1 : alpha ≤ 1) (hCreg : 0 ≤ Creg) {s : ℝ} (halpha : 1 - alpha = s / 2)
    (L : ℤ) (omega : Cutoff.CutoffSample d) (jn : ℕ) (i : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d m) (jn + i)) :
    printedLocalEnergy (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u R ≤
      (Creg * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
          (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) * T.toReal) *
        (3 : ℝ) ^ (s / 2 * (i : ℝ)) := by
  have hsplit : (3 : ℝ) ^ ((1 - alpha) * ((jn + i : ℕ) : ℝ)) =
      (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) * (3 : ℝ) ^ ((1 - alpha) * (i : ℝ)) := by
    have hc : (1 - alpha) * ((jn + i : ℕ) : ℝ) =
        (1 - alpha) * (jn : ℝ) + (1 - alpha) * (i : ℝ) := by push_cast; ring
    rw [hc, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hc0 : (0 : ℝ) ≤ Creg * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
      (3 : ℝ) ^ ((1 - alpha) * ((jn + i : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg hCreg (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  have hmain := le_toReal_of_ofReal_le hc0 hT
    (printedLocalEnergy_le_of_display hdisp halpha1 hCreg L omega (jn + i) hR)
  rw [hsplit] at hmain
  calc printedLocalEnergy (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u R
      ≤ Creg * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
          ((3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) *
            (3 : ℝ) ^ ((1 - alpha) * (i : ℝ))) * T.toReal := hmain
    _ = (Creg * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
          (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) * T.toReal) *
        (3 : ℝ) ^ ((1 - alpha) * (i : ℝ)) := by ring
    _ = (Creg * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
          (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) * T.toReal) *
        (3 : ℝ) ^ (s / 2 * (i : ℝ)) := by rw [halpha]

/-! ## 4. THE ENERGY SLOT -/

/-- **`hS0`, `hS` and `hSbound`, produced.**

The three energy conjuncts of the supplier from the Theorem-C display, the
printed order identification `1 - α = s/2`, and the disclosed top-scale datum.
The majorant is the printed one: the deterministic Step-2 constant times
`3^{(1-α)X_m(α)}(1 + 𝓔_{1/4})` times the data bracket. -/
theorem energySlot_of_regularityDisplay {M : ABKModel d} {m : ℤ} {X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {Creg alpha : ℝ} {T : ℝ≥0∞}
    {Y : Cutoff.CutoffSample d → ℝ≥0∞} {sigmaBarM pow Kg KhInf Kh : ℝ} {p s : ℝ}
    (hdisp : RegularityEnergyDisplay M m X u Creg alpha T) (hT : T ≠ ⊤)
    (halpha1 : alpha ≤ 1) (hCreg : 0 ≤ Creg) (halpha : 1 - alpha = s / 2)
    (hp : 0 < p) (hs : 0 < s) (L : ℤ) (omega : Cutoff.CutoffSample d) (jn : ℕ)
    (htop : (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) * T.toReal ≤
      recutEnergyFactor M Y m omega * energyBracket sigmaBarM pow Kg KhInf Kh) :
    ∃ S : ℝ,
      0 ≤ S ∧
      (∀ N : ℕ,
        coarseGrainingEnergyPartial (originCube d m) p (s - s / 4) jn N
            (printedLocalEnergy
              (Cutoff.coefficientCutoffCoeffOn M L omega (originCube d m)) u) ≤ S) ∧
      S ≤ recutEnergySlotConst Creg alpha p s jn * recutEnergyFactor M Y m omega *
        energyBracket sigmaBarM pow Kg KhInf Kh := by
  classical
  have hgeom : (0 : ℝ) ≤ coarseGrainingGeomFactor p (s / 4) :=
    coarseGrainingGeomFactor_nonneg hp (by linarith only [hs])
  have hXpow : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hjnpow : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  set S0 : ℝ := Creg * (3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) *
    (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) * T.toReal with hS0def
  have hS0 : 0 ≤ S0 := by
    rw [hS0def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCreg hXpow) hjnpow) ENNReal.toReal_nonneg
  refine ⟨S0 * coarseGrainingGeomFactor p (s / 4), mul_nonneg hS0 hgeom, ?_, ?_⟩
  · intro N
    exact coarseGrainingEnergyPartial_le_at_quarterPin (Q := originCube d m) (p := p)
      (s := s) (S := S0) (jn := jn) (N := N) hp hs hS0
      (fun i R hR => printedLocalEnergy_le_family hdisp hT halpha1 hCreg halpha L omega jn i hR)
      (printedLocalEnergy_nonneg _ u)
  · have hstep : S0 ≤ Creg * Real.rpow 3 ((1 - alpha) * (jn : ℝ)) *
        (recutEnergyFactor M Y m omega * energyBracket sigmaBarM pow Kg KhInf Kh) := by
      have hbase : (0 : ℝ) ≤ Creg * (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) :=
        mul_nonneg hCreg hjnpow
      have hmul := mul_le_mul_of_nonneg_left htop hbase
      calc S0 = Creg * (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) *
            ((3 : ℝ) ^ ((1 - alpha) * (X : ℝ)) * T.toReal) := by rw [hS0def]; ring
        _ ≤ Creg * (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) *
            (recutEnergyFactor M Y m omega *
              energyBracket sigmaBarM pow Kg KhInf Kh) := hmul
    calc S0 * coarseGrainingGeomFactor p (s / 4)
        ≤ Creg * (3 : ℝ) ^ ((1 - alpha) * (jn : ℝ)) *
            (recutEnergyFactor M Y m omega *
              energyBracket sigmaBarM pow Kg KhInf Kh) *
            coarseGrainingGeomFactor p (s / 4) :=
          mul_le_mul_of_nonneg_right hstep hgeom
      _ = recutEnergySlotConst Creg alpha p s jn * recutEnergyFactor M Y m omega *
            energyBracket sigmaBarM pow Kg KhInf Kh := by
          rw [recutEnergySlotConst]; ring

end

end Algsuperdiff.Section4.Provider.Homogenization
