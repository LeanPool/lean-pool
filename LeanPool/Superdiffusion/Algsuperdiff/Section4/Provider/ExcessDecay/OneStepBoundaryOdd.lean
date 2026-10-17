/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundaryEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionSobolevL2

/-!
# OneStepBoundaryOdd

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary datum leg through the odd class

The split Schauder bound prices the boundary branch against the
*far-side* seminorm `boundaryDatumLeg`, an object with no direct manuscript
counterpart.  This module replaces it by the sharper and much more meaningful
**odd-class defect**, using the repository's own odd-extension calculus
(`OddReflectionMap`, `OddReflectionSobolevL2`).

## The mechanism

Two proved facts do all the work.

* `OddReflectionMap.oddExtend_affineLift` — an affine function of the **odd
  class** `𝕃_odd(V)` (`IsOddAffineData`: it vanishes on every hyperplane
  carrying a met face of `∂□_m`) is its own partial odd extension.  This is the
  paper's own free parameter `ℓ` in `e.v0.hessian`, i.e. the "affine shift
  freedom" of the excess, restricted to the class that survives the reflection.
* `OddReflectionSobolevL2.eLpNorm_oddExtend_le` — the partial odd extension costs
  at most `2^d` in `L²`, by the cellwise change of variables.

Together with `oddExtend_sub`: if the competitor `V` is **odd** about the met
faces (`oddExtend x m (n-2) V = V`, which is exactly what the odd extension of a
window competitor delivers) and `ℓ ∈ 𝕃_odd`, then `V − ℓ` is again odd, so

```text
  E_raw(V, reflectedWindow) ≤ ‖V − ℓ‖_{L²(reflectedWindow)}
                            ≤ 2^d ‖V − ℓ‖_{L²(U_2)} = 2^d · affineDistOn U_2 V ℓ .
```

## The residue, isolated to one scalar

```text
  Csch = boundaryOddSchauderConst d = 2^d · boundarySchauderConst d ,
  K_h  = boundaryOddSchauderConst d · (3^{-n})^{1/2} · (3^{-(n-2)} · oddClassDefect) .
```

`oddClassDefect x m n V c A` is the amount by which restricting the affine
competitor to the odd class `𝕃_odd(V)` degrades the excess minimum on `U_2`.  It
is `≥ 0` always, and it is `0` on the interior branch, where
`isOddAffineData_of_no_met_face` makes the odd class the full affine class (so a
minimizer may be chosen inside it).

```text
  oddClassDefect x m n V c A  ≤  C(d) · (3^{n-2})^{3/2} · [∇h]_{C^{0,1/2}(U_2)} ,
```

whose units are exactly right: multiplied by the display's prefactor
`boundaryOddSchauderConst d · (3^{-n})^{1/2} · 3^{-(n-2)}` it yields
`C(d)·[∇h]_{C^{0,1/2}(U_2)}`, the manuscript's second leg, including its
indicator, which is carried here by the vanishing of the defect in the unmet
case.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot axisCube openCubeSet originCube)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two affine parametrizations -/

/-- `affineLift x c A` is the `affineEval` competitor with intercept
`c − A·x`. -/
theorem affineEval_eq_affineLift (x : Vec d) (c : ℝ) (A : Vec d) :
    affineEval (c - vecDot A x) A = affineLift x c A := by
  funext y
  rw [affineEval, affineLift, vecDot_sub_right]
  ring

/-! ## 2. Affine competitors are square integrable on both windows -/

theorem memLp_affineEval_reflectedWindow (x : Vec d) (m k : ℤ) (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict (reflectedWindow x m k)) := by
  refine memLp_affineEval_of_sandwich (zout := fun _ => -(1 / 2) * (3 : ℝ) ^ (m + 2))
    (Lout := (3 : ℝ) ^ (m + 2)) (zpow_pos (by norm_num) (m + 2))
    (measurableSet_reflectedWindow x m k) ?_ c g
  refine subset_trans (reflectedWindow_subset_openCubeSet x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube]

theorem memLp_affineEval_truncatedWindow (x : Vec d) (m k : ℤ) (c : ℝ) (g : Vec d) :
    MemLp (affineEval c g) 2 (volume.restrict (truncatedWindow x m k)) := by
  refine memLp_affineEval_of_sandwich (zout := x + fun _ => -(1 / 2) * (3 : ℝ) ^ k)
    (Lout := (3 : ℝ) ^ k) (zpow_pos (by norm_num) k)
    (measurableSet_truncatedWindow x m k) ?_ c g
  refine subset_trans (truncatedWindow_subset_translate x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube, image_add_axisCube]

/-! ## 3. The `L²` cost of the odd extension, normalized -/

/-- **The odd extension costs at most `2^d` in the normalized seminorm.**  The
unnormalized `L²` cost is `OddReflectionSobolevL2.eLpNorm_oddExtend_le`; the
normalizers only help, because `|U_2| ≤ |reflectedWindow|`. -/
theorem normalizedL2On_oddExtend_le (x : Vec d) {m k : ℤ} (hkm : k < m) (f : Vec d → ℝ)
    (hRpos : 0 < (volume (reflectedWindow x m k)).toReal)
    (hUpos : 0 < (volume (truncatedWindow x m k)).toReal)
    (hfR : MemLp (oddExtend x m k f) 2 (volume.restrict (reflectedWindow x m k)))
    (hfU : MemLp f 2 (volume.restrict (truncatedWindow x m k))) :
    normalizedL2On (reflectedWindow x m k) (oddExtend x m k f)
      ≤ 2 ^ d * normalizedL2On (truncatedWindow x m k) f := by
  have hUle : (volume (truncatedWindow x m k)).toReal
      ≤ (volume (reflectedWindow x m k)).toReal :=
    ENNReal.toReal_mono (volume_reflectedWindow_ne_top x m k)
      (volume_truncatedWindow_le_volume_reflectedWindow x m k)
  have hc : ((2 : ℝ≥0∞) ^ d).toReal = (2 : ℝ) ^ d := by
    rw [ENNReal.toReal_pow]
    norm_num
  have hfin : (2 : ℝ≥0∞) ^ d * eLpNorm f 2 (volume.restrict (truncatedWindow x m k)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hfU.eLpNorm_ne_top
  have htoReal := ENNReal.toReal_mono hfin (eLpNorm_oddExtend_le x hkm f)
  rw [ENNReal.toReal_mul, hc,
    toReal_eLpNorm_eq_sqrt_volume_mul_normalizedL2On hUpos hfU] at htoReal
  set N : ℝ := normalizedL2On (truncatedWindow x m k) f with hNdef
  have hNnn : 0 ≤ N := normalizedL2On_nonneg _ _
  have hsqR : 0 < Real.sqrt ((volume (reflectedWindow x m k)).toReal) := Real.sqrt_pos.2 hRpos
  have hsq : Real.sqrt ((volume (truncatedWindow x m k)).toReal)
      ≤ Real.sqrt ((volume (reflectedWindow x m k)).toReal) := Real.sqrt_le_sqrt hUle
  have hfacnn : (0 : ℝ) ≤ 2 ^ d * N := mul_nonneg (by positivity) hNnn
  rw [normalizedL2On_eq_toReal_eLpNorm_div hfR, div_le_iff₀ hsqR]
  calc (eLpNorm (oddExtend x m k f) 2 (volume.restrict (reflectedWindow x m k))).toReal
      ≤ 2 ^ d * (Real.sqrt ((volume (truncatedWindow x m k)).toReal) * N) := htoReal
    _ = 2 ^ d * N * Real.sqrt ((volume (truncatedWindow x m k)).toReal) := by ring
    _ ≤ 2 ^ d * N * Real.sqrt ((volume (reflectedWindow x m k)).toReal) :=
        mul_le_mul_of_nonneg_left hsq hfacnn

/-! ## 5. The odd-class defect -/

/-- **The odd-class defect.**  The amount by which restricting the affine
competitor to the odd class `𝕃_odd(V)` degrades the excess minimum on
`U_2 = (x + □_{n-2}) ∩ □_m`.  It is the Lean surface's boundary datum leg. -/
def oddClassDefect (x : Vec d) (m n : ℤ) (V : Vec d → ℝ) (c : ℝ) (A : Vec d) : ℝ :=
  affineDistOn (truncatedWindow x m (n - 2)) V (c - vecDot A x) A
    - affineExcessRaw (truncatedWindow x m (n - 2)) V

/-- **The defect vanishes for a minimizer of the odd class when no face is
met.**  In the interior regime the odd class is the whole affine class
(`isOddAffineData_of_no_met_face`), so an unrestricted minimizer is admissible
and the defect is `0`. -/
theorem oddClassDefect_of_isAffineMinimizer {x : Vec d} {m n : ℤ} {V : Vec d → ℝ}
    {c : ℝ} {A : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow x m (n - 2)) V (c - vecDot A x) A) :
    oddClassDefect x m n V c A = 0 := by
  rw [oddClassDefect, hmin, sub_self]

/-! ## 6. The constant and the producer -/

/-- The Schauder constant of the boundary branch through the odd class:
`2^d · boundarySchauderConst d`. -/
def boundaryOddSchauderConst (d : ℕ) [NeZero d] : ℝ := 2 ^ d * boundarySchauderConst d

theorem boundaryOddSchauderConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ boundaryOddSchauderConst d :=
  mul_nonneg (by positivity) (boundarySchauderConst_nonneg d)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

end

end Algsuperdiff.Section4.Provider.ExcessDecay
