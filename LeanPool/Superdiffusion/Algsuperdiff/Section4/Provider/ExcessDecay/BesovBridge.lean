/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ForceTransport
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.SobolevPublic

/-!
# BesovBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Gagliardo-versus-Besov bridge for the force leg

This module supplies the comparison in the direction the chain needs, `Besov ≤
C(d) · scale · Gagliardo`, which is the direction CoarseGraining's
`Sobolev/Fractional/BesovLeGagliardo.lean` proves.

## What is assumed and what is derived

The hypothesis is the manuscript's own premise `g ∈ H^s(□;ℝ^d)`, in its exact
`ℝ^d`-valued form: `g` is `L²` for the normalized cube measure and its
difference-quotient kernel is `L²` for the Gagliardo product measure
(`Gagliardo.MemWsp Q s 2 g`, CoarseGraining's definition instantiated at `E:=
Vec d`).  Everything else is derived:

* the **componentwise** package `Ch03.Legacy.ForceSobolevRegularity` that
  CoarseGraining's comparison consumes — each coordinate is the image of the
  vector datum under the (continuous linear) coordinate projection, both for
  the function and for its kernel, because the Gagliardo kernel commutes with
  the projection (the kernel exponent `s + d/p` does not see the target space);
* finiteness of the vector Gagliardo seminorm (`MemWsp.eSeminorm_lt_top`),
  which is what makes the real-valued comparison non-vacuous.

## The constant

```text
  besovGagliardoConstant d = 3^{d/2} · (2³·3^{3d+2}) · d ,
```

The scale factor `cubeBesovScaleWeight (-s) Q = (3^{Q.scale})^{s}` is the
manuscript's own normalization difference: the Besov object is note-normalized
(`3^{sm}[·]_{B^s}`), the Gagliardo object is not.

## References

* ABK26, (`[·]_{W^{s,p}}`), (`l.coarse.grained.Caccioppoli.RHS`).
* CoarseGraining, `Homogenization/Sobolev/Fractional/BesovLeGagliardo.lean`,
  `Homogenization/Book/Ch01/Theorems/FractionalSobolevVsBesov.lean`,
  `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The coordinate projections of the force datum -/

/-- The Gagliardo kernel commutes with the coordinate projection: the kernel of
a coordinate is the coordinate of the kernel.  (The kernel exponent depends only
on `d`, `s`, `p`, never on the target space.) -/
theorem gagliardoKernel_coord (s : ℝ) (g : Vec d → Vec d) (i : Fin d) :
    Gagliardo.gagliardoKernel s 2 (fun x => g x i) =
      fun w : Vec d × Vec d => Gagliardo.gagliardoKernel s 2 g w i :=
  rfl

/-- **The componentwise force package, derived from the vector one.**  This is the
input format of CoarseGraining's Besov-versus-Gagliardo comparison. -/
theorem forceSobolevRegularity_of_memWsp (Q : TriadicCube d) (s : ℝ)
    (g : Vec d → Vec d) (hL2 : MemLp g 2 (normalizedCubeMeasure Q))
    (hW : Gagliardo.MemWsp Q s 2 g) :
    Ch03.Legacy.ForceSobolevRegularity Q s g := by
  intro i
  refine ⟨?_, ?_⟩
  · exact (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hL2
  · show MemLp (Gagliardo.gagliardoKernel s 2 (fun x => g x i)) 2
      (Gagliardo.gagliardoCubeMeasure Q)
    rw [gagliardoKernel_coord s g i]
    exact (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hW

theorem forceBesovRegularity_of_memWsp [NeZero d] (Q : TriadicCube d) {s : ℝ}
    (g : Vec d → Vec d) (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp g 2 (normalizedCubeMeasure Q))
    (hW : Gagliardo.MemWsp Q s 2 g) :
    ForceBesovRegularity Q s g :=
  (forceSobolevRegularity_of_memWsp Q s g hL2 hW).toForceBesovRegularity hs hs1

/-! ## 2. Coordinate seminorms versus the vector seminorm -/

/-- Each coordinate's Gagliardo seminorm is dominated by the vector one: the
ambient norm of `Vec d` is the supremum norm, so the coordinate kernel is
pointwise dominated by the vector kernel. -/
theorem cubeGagliardoESeminorm_coord_le (Q : TriadicCube d) (s : ℝ)
    (g : Vec d → Vec d) (i : Fin d) :
    Gagliardo.cubeGagliardoESeminorm Q s 2 (fun x => g x i) ≤
      Gagliardo.cubeGagliardoESeminorm Q s 2 g := by
  rw [Gagliardo.Internal.cubeGagliardoESeminorm_def,
    Gagliardo.Internal.cubeGagliardoESeminorm_def, gagliardoKernel_coord s g i]
  by_cases hK : AEStronglyMeasurable (Gagliardo.gagliardoKernel s 2 g)
      (Gagliardo.gagliardoCubeMeasure Q)
  · exact eLpNorm_mono ((continuous_apply i).comp_aestronglyMeasurable hK)
      fun w => norm_le_pi_norm (Gagliardo.gagliardoKernel s 2 g w) i
  · rw [eLpNorm_of_not_aestronglyMeasurable hK]
    exact le_top

/-- The sum of the `d` coordinate seminorms is at most `d` times the vector
seminorm.  Finiteness of the vector seminorm is what makes the `toReal`
comparison valid, and it is supplied by the manuscript's `g ∈ H^s`. -/
theorem sum_cubeGagliardoSeminorm_coord_le (Q : TriadicCube d) (s : ℝ)
    (g : Vec d → Vec d) (hfin : Gagliardo.cubeGagliardoESeminorm Q s 2 g ≠ ∞) :
    ∑ i : Fin d, Gagliardo.cubeGagliardoSeminorm Q s 2 (fun x => g x i) ≤
      (d : ℝ) * (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal := by
  have hle : ∀ i : Fin d,
      Gagliardo.cubeGagliardoSeminorm Q s 2 (fun x => g x i) ≤
        (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal := fun i =>
    ENNReal.toReal_mono hfin (cubeGagliardoESeminorm_coord_le Q s g i)
  calc ∑ i : Fin d, Gagliardo.cubeGagliardoSeminorm Q s 2 (fun x => g x i)
      ≤ ∑ _i : Fin d, (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal :=
        Finset.sum_le_sum fun i _ => hle i
    _ = (d : ℝ) * (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 3. The bridge -/

/-- The dimensional constant of the Gagliardo-versus-Besov force bridge. -/
def besovGagliardoConstant (d : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d * (d : ℝ)

theorem besovGagliardoConstant_nonneg (d : ℕ) : 0 ≤ besovGagliardoConstant d := by
  unfold besovGagliardoConstant
  have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ Ch01.Legacy.wspVsBsppConstant d :=
    (Ch01.Legacy.wspVsBsppConstant_pos d).le
  positivity

/-- **`Besov ≤ C(d) · 3^{s·scale} · Gagliardo` for the force.** -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_le_gagliardo [NeZero d]
    (Q : TriadicCube d) {s : ℝ} (g : Vec d → Vec d) (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp g 2 (normalizedCubeMeasure Q)) (hW : Gagliardo.MemWsp Q s 2 g) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s g ≤
      besovGagliardoConstant d * cubeBesovScaleWeight (-s) Q *
        (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal := by
  have hbase := Ch03.Legacy.scaleNormalizedPositiveBesovVectorSeminormTwo_le_const_mul_sobolev
    Q g hs hs1 (forceSobolevRegularity_of_memWsp Q s g hL2 hW)
  have hsum := sum_cubeGagliardoSeminorm_coord_le Q s g hW.eSeminorm_lt_top.ne
  have hWnn : 0 ≤ cubeBesovScaleWeight (-s) Q := cubeBesovScaleWeight_nonneg (-s) Q
  have hcnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Ch01.Legacy.wspVsBsppConstant_pos d).le
  have hstep : Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo Q s g ≤
      cubeBesovScaleWeight (-s) Q *
        ((d : ℝ) * (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal) := by
    unfold Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
    exact mul_le_mul_of_nonneg_left hsum hWnn
  calc scaleNormalizedPositiveBesovVectorSeminormTwo Q s g
      ≤ Real.rpow (3 : ℝ) ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d *
          Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo Q s g := hbase
    _ ≤ Real.rpow (3 : ℝ) ((d : ℝ) / 2) * Ch01.Legacy.wspVsBsppConstant d *
          (cubeBesovScaleWeight (-s) Q *
            ((d : ℝ) * (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal)) :=
        mul_le_mul_of_nonneg_left hstep hcnn
    _ = besovGagliardoConstant d * cubeBesovScaleWeight (-s) Q *
          (Gagliardo.cubeGagliardoESeminorm Q s 2 g).toReal := by
        unfold besovGagliardoConstant
        ring

/-! ## 4. The bridge at the frozen theorem's window -/

theorem forceBesovRegularity_translated_neg [NeZero d] {z : Vec d}
    (Q : TriadicCube d) {s : ℝ} {g : Vec d → Vec d} (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn ((fun y => z + y) '' openCubeSet Q)))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn ((fun y => z + y) '' openCubeSet Q))) :
    ForceBesovRegularity Q s (fun x => -g (x + z)) := by
  have hL2' : MemLp (fun x => g (x + z)) 2 (normalizedCubeMeasure Q) := by
    have h := memLp_normalizedVolumeMeasureOn_image_add (p := 2) (by norm_num)
      (by norm_num) hL2
    rwa [normalizedVolumeMeasureOn_openCubeSet] at h
  have hW' : Gagliardo.MemWsp Q s 2 (fun x => g (x + z)) := by
    have h := memLp_gagliardoKernel_image_add hW
    rwa [normalizedGagliardoMeasureOn_openCubeSet] at h
  exact forceBesovRegularity_of_memWsp Q _ hs hs1 hL2'.neg hW'.neg

theorem besovVectorSeminormTwo_translated_neg_le_gagliardo_window [NeZero d]
    {z : Vec d} (Q : TriadicCube d) {s : ℝ} {g : Vec d → Vec d} (hs : 0 < s)
    (hs1 : s ≤ 1)
    (hL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn ((fun y => z + y) '' openCubeSet Q)))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn ((fun y => z + y) '' openCubeSet Q))) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s (fun x => -g (x + z)) ≤
      besovGagliardoConstant d * cubeBesovScaleWeight (-s) Q *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => z + y) '' openCubeSet Q) s g).toReal := by
  have hL2' : MemLp (fun x => g (x + z)) 2 (normalizedCubeMeasure Q) := by
    have h := memLp_normalizedVolumeMeasureOn_image_add (p := 2) (by norm_num)
      (by norm_num) hL2
    rwa [normalizedVolumeMeasureOn_openCubeSet] at h
  have hW' : Gagliardo.MemWsp Q s 2 (fun x => g (x + z)) := by
    have h := memLp_gagliardoKernel_image_add hW
    rwa [normalizedGagliardoMeasureOn_openCubeSet] at h
  have hmain := scaleNormalizedPositiveBesovVectorSeminormTwo_le_gagliardo Q
    (fun x => -g (x + z)) hs hs1 hL2'.neg hW'.neg
  have hneg : Gagliardo.cubeGagliardoESeminorm Q s 2 (fun x => -g (x + z)) =
      Gagliardo.cubeGagliardoESeminorm Q s 2 (fun x => g (x + z)) := by
    have hfun : (fun x => -g (x + z)) = -(fun x : Vec d => g (x + z)) := rfl
    rw [hfun, Gagliardo.cubeGagliardoESeminorm_neg]
  rwa [hneg, ← normalizedGagliardoESeminormOn_image_add_openCubeSet z Q s g] at hmain

end

end Algsuperdiff.Section4.Provider.ExcessDecay
