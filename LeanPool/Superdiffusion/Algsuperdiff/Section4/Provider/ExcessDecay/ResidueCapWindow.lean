/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryGradH
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowNormalized

/-!
# ResidueCapWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary covering-cube transports, re-cut at the window hinge

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

The proved boundary transports are all stated at the anchor's **geometry
binder**

```text
  hgeom : x + □_n ⊆ (z + □_{n+1}) ∩ □_m ,
```

and every one of them consumes that binder for exactly one thing: the
containment of the boundary covering cube inside the anchor's window,

```text
  (W)   c + □_{n+2} ⊆ (z + □_{n+3}) ∩ □_m ,   c = wellPlacedCentre x m (n+2) ,
```

produced by `image_add_wellPlacedCentre_subset_anchorWindow`.  This module
restates the transports with the containment `(W)` — here the binder `hcov` —
supplied directly, and reproves them by supplying the hinge instead of deriving
it.  The re-cuts are strict generalizations: each proved statement is recovered
by feeding `image_add_wellPlacedCentre_subset_anchorWindow hnm hx hgeom` for
`hcov`.  Their conclusions are byte-identical to the proved ones.

The seven declarations are, in dependency order:

* `eLpNorm_coveringCube_atWindow` — the `L²` transport onto the window at the
  factor `3^d`;
* `normalizedGagliardo and its real-valued companion `normalizedGagliardo — the
  Gagliardo seminorm transport at the factor `gagliardoWindowConst d`;
* `besovVectorSeminormTwo_coveringCube_atWindow` — the force leg of the
  boundary Caccioppoli, priced on the window;
* `besovVectorSeminormTwo_datumGrad_coveringCube_atWindow` and
  `sqrt_vecNormSq_cubeAverageVec_coveringCube_atWindow` — the seminorm half and
  the average half of the `∇h` leg;
* `eLpNorm_coveringCube_sub_le_boundaryWindowPoincare_atWindow` — the boundary
  Poincaré read on the covering cube.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
* The proved originals: `BoundaryPoincareWindow.lean`,
  `BoundaryTransports.lean`, `BoundaryGradH.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The `L²` transport, at the hinge -/

omit [NormedSpace ℝ E] in
/-- **The `L²` transport onto the anchor's window, at the hinge.**

The re-cut of `eLpNorm_coveringCube_le_anchorWindow`: a normalized `L²` norm
over the boundary covering cube is at most `3^d` times the one over the
anchor's window `W' = (z+□_{n+3}) ∩ □_m`, given only the containment `(W)`. -/
theorem eLpNorm_coveringCube_atWindow {n m : ℤ} {x z : Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (f : Vec d → E) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ d) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) := by
  have hbase := eLpNorm_le_of_volume_le (K := ENNReal.ofReal ((9 : ℝ) ^ d))
    hcov (by simp) (by simp)
    (volume_anchorWindow_le_coveringCube n m z (wellPlacedCentre x m (n + 2))) f
  have hhalf : (ENNReal.ofReal ((9 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((3 : ℝ) ^ d) := by
    have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ (2 : ℕ) := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (9 : ℝ) ^ d), h9,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rwa [hhalf] at hbase

/-! ## 2. The Gagliardo window move, at the hinge -/

/-- **The Gagliardo seminorm transport onto the anchor's window, at the
hinge.**

The re-cut of `normalizedGagliardoESeminormOn_coveringCube_le_anchorWindow`: the
containment `(W)` together with the volume ratio `9^d`, read through the general engine
`normalizedGagliardoESeminormOn_le_of_volume_le`. -/
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

/-- **The Gagliardo window move at the hinge, in the real-valued form the
boundary assembly consumes.**

The re-cut of `normalizedGagliardoESeminormOn_coveringCube_atWindow`.  The finiteness
hypothesis is the anchor's own clause (iv), read on the window. -/
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

/-! ## 3. The force leg of the boundary Caccioppoli, at the hinge -/

/-- **The transported force's cube Besov seminorm, priced on the window, at the
hinge.**

The re-cut of `besovVectorSeminormTwo_coveringCube_le_anchorWindow`: the
composition of `BesovBridge`'s Besov--Gagliardo comparison at the covering cube
with the window move of section 2. -/
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

/-! ## 4. The two halves of the `∇h` leg, at the hinge -/

/-- **The transported boundary gradient's cube Besov seminorm, priced on the
window, at the hinge.**

The re-cut of
`besovVectorSeminormTwo_datumGrad_coveringCube_le_anchorWindow`: section 3's
move read at `g := −∇h`. -/
theorem besovVectorSeminormTwo_datumGrad_coveringCube_atWindow [NeZero d]
    {n m : ℤ} {x z : Vec d} {s : ℝ} {H : Vec d → Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hWcov : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2)))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s
        (fun y => H (y + wellPlacedCentre x m (n + 2))) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * ((n + 2 : ℤ) : ℝ)) *
        (gagliardoWindowConst d *
          (Support.normalizedGagliardoESeminormOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) s H).toReal) := by
  have hbase := besovVectorSeminormTwo_coveringCube_atWindow
    (g := fun y => -H y) hcov hs hs1 hL2.neg
    (memLp_gagliardoKernel_neg _ s hWcov) (memLp_gagliardoKernel_neg _ s hW)
  rw [normalizedGagliardoESeminormOn_neg] at hbase
  simpa only [neg_neg] using hbase

/-- **The transported boundary gradient's cube average, priced on the window,
at the hinge.**

The re-cut of
`sqrt_vecNormSq_cubeAverageVec_coveringCube_le_anchorWindow`: the vector
Jensen inequality on the covering cube composed with section 1's `L²` window
transport, at the coefficient-free constant `√d · 3^d`. -/
theorem sqrt_vecNormSq_cubeAverageVec_coveringCube_atWindow {n m : ℤ}
    {x z : Vec d} {H : Vec d → Vec d}
    (hcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))
    (hL2W : MemLp H 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))) :
    Real.sqrt (vecNormSq (cubeAverageVec (originCube d (n + 2))
        (fun y => H (y + wellPlacedCentre x m (n + 2))))) ≤
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
        (eLpNorm H 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))))).toReal := by
  classical
  -- the hinge, and section 1's transport, taken before the abbreviations
  have hsubcov : (fun y => wellPlacedCentre x m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) := hcov
  have hmove : (eLpNorm H 2 (Support.normalizedVolumeMeasureOn
        ((fun y => wellPlacedCentre x m (n + 2) + y) ''
          openCubeSet (originCube d (n + 2))))).toReal ≤
      (3 : ℝ) ^ d * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal := by
    have hbase := eLpNorm_coveringCube_atWindow hcov H
    have hne : eLpNorm H 2 (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m)))) ≠ ⊤ := hL2W.eLpNorm_ne_top
    have hRHSne : ENNReal.ofReal ((3 : ℝ) ^ d) *
        eLpNorm H 2 (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m)))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne
    have hstep := ENNReal.toReal_mono hRHSne hbase
    rwa [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)] at hstep
  set c : Vec d := wellPlacedCentre x m (n + 2) with hc
  set cov : Set (Vec d) :=
    (fun y => c + y) '' openCubeSet (originCube d (n + 2)) with hcovDef
  set W : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hWDef
  have hcovne : volume cov ≠ 0 :=
    volume_image_add_openCubeSet_ne_zero c (originCube d (n + 2))
  have hWne : volume W ≠ 0 := by
    intro h0
    exact hcovne (le_antisymm (h0 ▸ measure_mono hsubcov) zero_le)
  have hWtop : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_openCubeSet_ne_top (originCube d m))
      (measure_mono Set.inter_subset_right)
  have hL2cov : MemLp H 2 (Support.normalizedVolumeMeasureOn cov) :=
    memLp_normalizedVolumeMeasureOn_subset hsubcov hWne hWtop hcovne hL2W
  have hL2cube : MemLp (fun y => H (y + c)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) := by
    have h := memLp_normalizedVolumeMeasureOn_image_add (p := 2) (by norm_num)
      (by norm_num) hL2cov
    rwa [normalizedVolumeMeasureOn_openCubeSet] at h
  -- the vector Jensen step on the covering cube
  have hjen : ‖cubeAverageVec (originCube d (n + 2)) (fun y => H (y + c))‖ ≤
      (eLpNorm (fun y => H (y + c)) 2
        (normalizedCubeMeasure (originCube d (n + 2)))).toReal :=
    norm_cubeAverageVec_le_cubeLpNorm_two (originCube d (n + 2)) _ hL2cube
  -- the frame move
  have hframe : eLpNorm (fun y => H (y + c)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) =
      eLpNorm H 2 (Support.normalizedVolumeMeasureOn cov) := by
    rw [hcovDef, eLpNorm_normalizedVolumeMeasureOn_image_add c
      (openCubeSet (originCube d (n + 2))) (by norm_num) (by norm_num),
      normalizedVolumeMeasureOn_openCubeSet]
  have hsqrtd : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  calc Real.sqrt (vecNormSq (cubeAverageVec (originCube d (n + 2))
        (fun y => H (y + c))))
      ≤ Real.sqrt (d : ℝ) *
          ‖cubeAverageVec (originCube d (n + 2)) (fun y => H (y + c))‖ :=
        sqrt_vecNormSq_le_sqrt_dim_mul_norm _
    _ ≤ Real.sqrt (d : ℝ) *
          (eLpNorm (fun y => H (y + c)) 2
            (normalizedCubeMeasure (originCube d (n + 2)))).toReal :=
        mul_le_mul_of_nonneg_left hjen hsqrtd
    _ = Real.sqrt (d : ℝ) * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn cov)).toReal := by
        rw [hframe]
    _ ≤ Real.sqrt (d : ℝ) *
          ((3 : ℝ) ^ d * (eLpNorm H 2 (Support.normalizedVolumeMeasureOn W)).toReal) :=
        mul_le_mul_of_nonneg_left hmove hsqrtd
    _ = Real.sqrt (d : ℝ) * (3 : ℝ) ^ d *
          (eLpNorm H 2 (Support.normalizedVolumeMeasureOn W)).toReal := by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
