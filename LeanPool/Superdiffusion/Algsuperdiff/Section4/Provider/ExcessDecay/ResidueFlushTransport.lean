/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealScalarBase
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorWindowMove
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapGeometry

/-!
# ResidueFlushTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The one-step window transport `K' → W'`

Nothing here imports the frozen file, and nothing here claims the anchor or any
source node.

## What is proved

The proved boundary composition transports the child cube's Gagliardo seminorm
to the frozen window `W' = (z+□_{n+3}) ∩ □_m` in **two** hops, the
anchor's child window `x + □_n ⊆ (z+□_{n+2}) ∩ □_m` and then the window
move onto `W'`, at the constants `gagliardoWindowConst d = 3^d` and `windowMoveConst d =
9^d`.  The flush sub-cube `K' = flushSubCentre z m n i σ + □_n` is *not* inside
`(z+□_{n+2}) ∩ □_m` (that is `ResidueAbsorption`'s block), so the two-hop
route is unavailable.

It is not needed: `K' ⊆ W'` is proved
(`SealCaccioppoliGeometry.flushSubCube_subset_anchorWindow`) and the volume
ratio `|W'| ≤ 27^d |K'|` is proved
(`SealScalarBase.volume_anchorWindow_le_scaleN_cube`), so
`InteriorWindowMove.normalizedGagliardo` gives the **one-hop** transport at
`√(27^d)` — the same constant `ResidueInterface` already uses for the `L²`
transport at `K'`.  Note `√(27^d) ≤ 3^d·9^d = 27^d`, so the one-hop constant is
no worse than the proved two-hop product.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The one-hop window constant `√(27^d)`, the same factor
`ResidueInterface` uses for the `L²` transport at the flush sub-cube. -/
def flushWindowConst (d : ℕ) : ℝ := Real.sqrt ((27 : ℝ) ^ d)

theorem flushWindowConst_pos (d : ℕ) : 0 < flushWindowConst d := by
  rw [flushWindowConst]
  exact Real.sqrt_pos.mpr (by positivity)

theorem flushWindowConst_nonneg (d : ℕ) : 0 ≤ flushWindowConst d :=
  (flushWindowConst_pos d).le

private theorem ofReal_twentySeven_pow_rpow_half (d : ℕ) :
    (ENNReal.ofReal ((27 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (flushWindowConst d) := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (27 : ℝ) ^ d),
    flushWindowConst, Real.sqrt_eq_rpow]

/-! ## 1. The Gagliardo seminorm, transported in one hop -/

/-- **The one-hop Gagliardo transport at the flush sub-cube.**

`[f]_{H^s(K')} ≤ √(27^d) · [f]_{H^s(W')}`, from `K' ⊆ W'` and `|W'| ≤ 27^d |K'|`.
Both sides are `ℝ≥0∞`, so no finiteness hypothesis is needed. -/
theorem normalizedGagliardoESeminormOn_flushSubCube_le_anchorWindow {n m : ℤ}
    (hnm : n + 2 ≤ m) {z : Vec d} (hz : z ∈ openCubeSet (originCube d m))
    (i : Fin d) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn
        ((fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n)) s f ≤
      ENNReal.ofReal (flushWindowConst d) *
        Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s f := by
  have hbase := normalizedGagliardoESeminormOn_le_of_volume_le
    (K := ENNReal.ofReal ((27 : ℝ) ^ d))
    (flushSubCube_subset_anchorWindow hnm hz i hσ)
    (by simp) (by simp)
    (volume_anchorWindow_le_scaleN_cube n m z (flushSubCentre z m n i σ)) s f
  rwa [ofReal_twentySeven_pow_rpow_half d] at hbase

/-- **The one-hop Gagliardo transport, in the real-valued spelling the
composition consumes.** -/
theorem normalizedGagliardoESeminormOn_flushSubCube_toReal_le {n m : ℤ}
    (hnm : n + 2 ≤ m) {z : Vec d} (hz : z ∈ openCubeSet (originCube d m))
    (i : Fin d) {σ s : ℝ} (hσ : σ = 1 ∨ σ = -1) (f : Vec d → E)
    (hfin : MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    (Support.normalizedGagliardoESeminormOn
        ((fun y => flushSubCentre z m n i σ + y) ''
          openCubeSet (originCube d n)) s f).toReal ≤
      flushWindowConst d *
        (Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s f).toReal := by
  have hbase := normalizedGagliardoESeminormOn_flushSubCube_le_anchorWindow
    hnm hz i hσ s f
  have hne : Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s f ≠ ⊤ := hfin.eLpNorm_ne_top
  have hRHSne : ENNReal.ofReal (flushWindowConst d) *
      Support.normalizedGagliardoESeminormOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) s f ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne
  have hstep := ENNReal.toReal_mono hRHSne hbase
  rwa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (flushWindowConst_nonneg d)] at hstep

/-! ## 2. The window's volume is nonzero, from the flush sub-cube -/

/-- **`W'` carries positive volume**, because the flush sub-cube does and sits
inside it.  The proved derivation goes through the `(n+2)` window and the
anchor's geometry binder; at `K'` this is the direct route. -/
theorem volume_anchorWindow_ne_zero_of_flushSubCube {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} (hz : z ∈ openCubeSet (originCube d m)) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≠ 0 := by
  intro hzero
  have hle := measure_mono (μ := (volume : Measure (Vec d)))
    (flushSubCube_subset_anchorWindow hnm hz i hσ)
  rw [hzero] at hle
  have hzeroK : volume ((fun y => flushSubCentre z m n i σ + y) ''
      openCubeSet (originCube d n)) = 0 := le_antisymm hle zero_le
  have hpos := volume_toReal_image_add_openCubeSet_pos
    (flushSubCentre z m n i σ) n
  rw [hzeroK] at hpos
  simp only [ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

end

end Algsuperdiff.Section4.Provider.ExcessDecay
