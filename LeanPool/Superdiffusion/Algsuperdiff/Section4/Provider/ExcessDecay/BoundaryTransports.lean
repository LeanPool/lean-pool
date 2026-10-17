/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BesovBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryPoincareWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorWindowMove

/-!
# BoundaryTransports

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary lane's data transports onto the anchor window

The boundary Caccioppoli's *data* legs — the force `[g]` and the boundary
gradient `[∇h]` — are Gagliardo seminorms, not `L²` norms, and this module
supplies the same move for them:

```text
  [f]_{H^s(c+□_{n+2})} ≤ 3^d · [f]_{H^s(W')} ,
```

together with the composition that the boundary Caccioppoli's right-hand side
actually reads: CoarseGraining's cube Besov seminorm of the *transported*
force, in the covering cube's own frame, priced by the anchor's own window
seminorm.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The Gagliardo window move -/

/-- Gagliardo transport assuming containment of the covering cube in the window. -/
theorem normalizedGagliardoESeminormOn_coveringCube_atWindow {n m : ℤ}
    {x z : Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))) s f ≤
      ENNReal.ofReal (gagliardoWindowConst d) *
        Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s f := by
  have hbase := normalizedGagliardoESeminormOn_le_of_volume_le
    (K := ENNReal.ofReal ((9 : ℝ) ^ d))
    hcov (by simp) (by simp)
    (volume_anchorWindow_le_coveringCube n m z (wellPlacedCentre x m (n + 2))) s f
  have hhalf : (ENNReal.ofReal ((9 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (gagliardoWindowConst d) := by
    have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ (2 : ℕ) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (9 : ℝ) ^ d), h9,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity), gagliardoWindowConst]
  rwa [hhalf] at hbase

/-- **The Gagliardo seminorm transport onto the anchor's window.** -/
theorem normalizedGagliardoESeminormOn_coveringCube_le_anchorWindow {n m : ℤ}
    {x z : Vec d} (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))) s f ≤
      ENNReal.ofReal (gagliardoWindowConst d) *
        Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s f := by
  exact normalizedGagliardoESeminormOn_coveringCube_atWindow
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom) s f

/-- Real-valued Gagliardo transport under the same containment and finiteness hypotheses. -/
theorem normalizedGagliardoESeminormOn_coveringCube_toReal_le_atWindow {n m : ℤ}
    {x z : Vec d} {s : ℝ}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (f : Vec d → E)
    (hfin : MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    (Support.normalizedGagliardoESeminormOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))) s f).toReal ≤
      gagliardoWindowConst d *
        (Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s f).toReal := by
  have hbase := normalizedGagliardoESeminormOn_coveringCube_atWindow hcov s f
  have hne : Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s f ≠ ⊤ := hfin.eLpNorm_ne_top
  have hRHSne : ENNReal.ofReal (gagliardoWindowConst d) *
      Support.normalizedGagliardoESeminormOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) s f ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne
  have hstep := ENNReal.toReal_mono hRHSne hbase
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (gagliardoWindowConst_pos d).le] at hstep

/-- **The Gagliardo window move, in the real-valued form the boundary assembly
consumes.**  The finiteness hypothesis is the anchor's own clause (iv), read on
the anchor's window. -/
theorem normalizedGagliardoESeminormOn_coveringCube_toReal_le {n m : ℤ}
    {x z : Vec d} {s : ℝ} (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (f : Vec d → E)
    (hfin : MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    (Support.normalizedGagliardoESeminormOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))) s f).toReal ≤
      gagliardoWindowConst d *
        (Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s f).toReal := by
  exact normalizedGagliardoESeminormOn_coveringCube_toReal_le_atWindow
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom) f hfin

/-! ## 2. The force leg of the boundary Caccioppoli, onto the anchor's window -/

/-- The transported force Besov budget under covering-cube containment. -/
theorem besovVectorSeminormTwo_coveringCube_atWindow [NeZero d] {n m : ℤ}
    {x z : Vec d} {s : ℝ} {g : Vec d → Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hWcov : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => -g (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s g).toReal) := by
  have hbes := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (z := wellPlacedCentre x m (n + 2)) (originCube d (n + 2)) hs hs1 hL2 hWcov
  rw [cubeBesovScaleWeight_neg_originCube (d := d) (n + 2) s] at hbes
  refine hbes.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · exact normalizedGagliardoESeminormOn_coveringCube_toReal_le_atWindow hcov g hW
  · exact mul_nonneg (besovGagliardoConstant_nonneg d)
      (Real.rpow_nonneg (by norm_num) _)

/-- **The transported force's cube Besov seminorm, priced on the anchor's window.**

`BoundaryOuterAssembly` reads its force leg as CoarseGraining's cube Besov
seminorm of `y ↦ −g(y + c)` on the covering cube `□_{n+2}` in that cube's own
frame.  This is the composition of `BesovBridge`'s Besov--Gagliardo comparison
at the covering cube with the window move of section 1: the whole leg is priced
by the anchor's own `[g]_{H^s(W')}` at the scale weight `3^{s(n+2)}` and the
coefficient-free constant `besovGagliardoConstant d · 3^d`. -/
theorem besovVectorSeminormTwo_coveringCube_le_anchorWindow [NeZero d] {n m : ℤ}
    {x z : Vec d} {s : ℝ} {g : Vec d → Vec d} (hnm : n + 2 ≤ m)
    (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hWcov : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => -g (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s g).toReal) := by
  exact besovVectorSeminormTwo_coveringCube_atWindow
    (image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom) hs hs1 hL2 hWcov hW

/-! ## 3. The covering cube's own clause-(iv) data -/

omit [NormedSpace ℝ E] in
/-- The anchor's `L²` datum, restricted to the boundary covering cube. -/
theorem memLp_two_coveringCube_of_clause_iv {n m : ℤ} {x : Vec d} {f : Vec d → E}
    (hnm : n + 2 ≤ m)
    (hf : MemLp f 2 (Support.normalizedVolumeMeasureOn
      (openCubeSet (originCube d m)))) :
    MemLp f 2 (Support.normalizedVolumeMeasureOn
      ((fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)))) :=
  memLp_normalizedVolumeMeasureOn_subset
    (image_add_wellPlacedCentre_subset_openCubeSet x hnm)
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero (wellPlacedCentre x m (n + 2))
      (originCube d (n + 2))) hf

/-- The anchor's Gagliardo datum, restricted to the boundary covering cube. -/
theorem memLp_two_gagliardo_coveringCube_of_clause_iv {n m : ℤ} {x : Vec d} {s : ℝ}
    {f : Vec d → E} (hnm : n + 2 ≤ m)
    (hf : MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))) :=
  memLp_normalizedGagliardoMeasureOn_subset
    (image_add_wellPlacedCentre_subset_openCubeSet x hnm)
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero (wellPlacedCentre x m (n + 2))
      (originCube d (n + 2))) hf

end

end Algsuperdiff.Section4.Provider.ExcessDecay
