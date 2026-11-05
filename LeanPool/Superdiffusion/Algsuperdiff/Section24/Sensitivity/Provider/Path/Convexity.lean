/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Bounds

/-!
# Convexity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform convexity of the doubled energy on the admissible class

The doubled `mu` problem minimizes a quadratic functional over an affine class
that does *not* depend on the coefficient.  Consequently the exact
parallelogram identity

`E(X) + E(Y) - 2 E((X+Y)/2) = ½ E(X - Y)`

together with admissibility of the midpoint turns minimality of `X` into the
quantitative energy gap `½ E(X - Y) ≤ E(Y) - E(X)`.  This is the only place
where the algebraic structure of the admissible class is used, so the two
Chapter 1 field classes are shown here to be closed under sums and scalar
multiples.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Algebra of the Chapter 1 field classes -/

/-- Zero-trace potential fields are closed under sums. -/
theorem potentialZeroTraceFieldOn_add {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : Book.Ch01.PotentialZeroTraceFieldOn U f)
    (hg : Book.Ch01.PotentialZeroTraceFieldOn U g) :
    Book.Ch01.PotentialZeroTraceFieldOn U (fun x => f x + g x) := by
  obtain ⟨hfm, u, hu⟩ := hf
  obtain ⟨hgm, v, hv⟩ := hg
  refine ⟨?_, ⟨u + v, ?_⟩⟩
  · exact hfm.add hgm
  · filter_upwards [hu, hv] with x hx hy
    show f x + g x = (u + v).toH1Function.grad x
    rw [hx, hy]
    rfl

/-- Zero-trace potential fields are closed under scalar multiples. -/
theorem potentialZeroTraceFieldOn_smul {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) (c : ℝ) :
    Book.Ch01.PotentialZeroTraceFieldOn U (fun x => c • f x) := by
  obtain ⟨hfm, u, hu⟩ := hf
  refine ⟨?_, ⟨c • u, ?_⟩⟩
  · exact hfm.const_smul c
  · filter_upwards [hu] with x hx
    show c • f x = (c • u).toH1Function.grad x
    rw [hx]
    rfl

/-- Zero-normal-trace solenoidal fields are closed under sums. -/
theorem solenoidalZeroNormalTraceFieldOn_add {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hf : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U f)
    (hg : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  exact isSolenoidalZeroNormalTraceOn_add_of_memVectorL2 hf.1 hg.1 hf.2 hg.2

/-- Zero-normal-trace solenoidal fields are closed under scalar multiples. -/
theorem solenoidalZeroNormalTraceFieldOn_smul {U : Set (Vec d)}
    {g : Vec d → Vec d}
    (hg : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g) (c : ℝ) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (fun x => c • g x) := by
  refine ⟨hg.1.const_smul c, ?_⟩
  exact isSolenoidalZeroNormalTraceOn_smul hg.2 c

/-! ## Midpoint admissibility -/

/-- The admissible class of the doubled `mu` problem is convex: the midpoint of
two admissible fields is admissible. -/
theorem isDoubledMuAdmissible_midpoint {U : Domain d} {P : BlockVec d}
    {X Y : DoubledField d} (hX : IsDoubledMuAdmissible U P X)
    (hY : IsDoubledMuAdmissible U P Y) :
    IsDoubledMuAdmissible U P ((1 / 2 : ℝ) • (X + Y)) := by
  constructor
  · have hsum := potentialZeroTraceFieldOn_add hX.1 hY.1
    have hsmul := potentialZeroTraceFieldOn_smul hsum (1 / 2 : ℝ)
    have hfun :
        (fun x => ((1 / 2 : ℝ) • (X + Y)).potential x - P.1) =
          fun x => (1 / 2 : ℝ) •
            ((X.potential x - P.1) + (Y.potential x - P.1)) := by
      funext x
      funext i
      change (1 / 2 : ℝ) * (X.potential x i + Y.potential x i) - P.1 i =
        (1 / 2 : ℝ) * ((X.potential x i - P.1 i) + (Y.potential x i - P.1 i))
      ring
    rw [hfun]
    exact hsmul
  · have hsum := solenoidalZeroNormalTraceFieldOn_add hX.2 hY.2
    have hsmul := solenoidalZeroNormalTraceFieldOn_smul hsum (1 / 2 : ℝ)
    have hfun :
        (fun x => ((1 / 2 : ℝ) • (X + Y)).flux x - P.2) =
          fun x => (1 / 2 : ℝ) •
            ((X.flux x - P.2) + (Y.flux x - P.2)) := by
      funext x
      funext i
      change (1 / 2 : ℝ) * (X.flux x i + Y.flux x i) - P.2 i =
        (1 / 2 : ℝ) * ((X.flux x i - P.2 i) + (Y.flux x i - P.2 i))
      ring
    rw [hfun]
    exact hsmul

/-! ## The exact parallelogram identity -/

theorem blockMatVecMul_sub (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ Y, blockMatVecMul_add, blockMatVecMul_smul,
    neg_one_smul, ← sub_eq_add_neg]

theorem blockVecDot_sub_left (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ Y, blockVecDot_add_left,
    blockVecDot_smul_left]
  ring

/-- **Parallelogram identity for the doubled quadratic form.**  The form is the
diagonal of a symmetric bilinear pairing, so the midpoint defect is exactly a
quarter of the form of the difference. -/
theorem blockQuadForm_parallelogram (A : Mat d) (Z W : BlockVec d) :
    blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z)
        + blockVecDot W (blockMatVecMul (blockMatrixOfCoeff A) W)
        - 2 * blockVecDot ((1 / 2 : ℝ) • (Z + W))
            (blockMatVecMul (blockMatrixOfCoeff A) ((1 / 2 : ℝ) • (Z + W)))
      = (1 / 2 : ℝ) *
          blockVecDot (Z - W) (blockMatVecMul (blockMatrixOfCoeff A) (Z - W)) := by
  have hc := blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm A Z W
  have emid :
      blockVecDot ((1 / 2 : ℝ) • (Z + W))
          (blockMatVecMul (blockMatrixOfCoeff A) ((1 / 2 : ℝ) • (Z + W))) =
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) *
          (blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z)
            + blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) W)
            + (blockVecDot W (blockMatVecMul (blockMatrixOfCoeff A) Z)
              + blockVecDot W (blockMatVecMul (blockMatrixOfCoeff A) W)))) := by
    rw [blockMatVecMul_smul, blockVecDot_smul_left, blockVecDot_smul_right,
      blockMatVecMul_add, blockVecDot_add_left, blockVecDot_add_right,
      blockVecDot_add_right]
  have esub :
      blockVecDot (Z - W) (blockMatVecMul (blockMatrixOfCoeff A) (Z - W)) =
        blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) Z)
          - blockVecDot Z (blockMatVecMul (blockMatrixOfCoeff A) W)
          - (blockVecDot W (blockMatVecMul (blockMatrixOfCoeff A) Z)
            - blockVecDot W (blockMatVecMul (blockMatrixOfCoeff A) W)) := by
    rw [blockMatVecMul_sub, blockVecDot_sub_left, blockVecDot_sub_right,
      blockVecDot_sub_right]
  rw [emid, esub]
  ring

/-- Parallelogram identity for the doubled energy density. -/
theorem blockEnergyDensityAt_parallelogram {U : Domain d} (a : CoeffOn U)
    (Z W : BlockVec d) (x : Vec d) :
    blockEnergyDensityAt a Z x + blockEnergyDensityAt a W x
        - 2 * blockEnergyDensityAt a ((1 / 2 : ℝ) • (Z + W)) x
      = (1 / 2 : ℝ) * blockEnergyDensityAt a (Z - W) x := by
  have h := blockQuadForm_parallelogram (a.toCoeffField x) Z W
  unfold blockEnergyDensityAt
  simp only [blockMatrixField_eq_blockMatrixOfCoeff]
  linarith

/-! ## The averaged parallelogram identity and the energy gap -/

/-- Parallelogram identity for the doubled energy value. -/
theorem doubledMuValue_parallelogram {U : Domain d} (a : CoeffOn U)
    {X Y : DoubledField d}
    (hXpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hXflux : MemVectorL2 (U : Set (Vec d)) X.flux)
    (hYpot : MemVectorL2 (U : Set (Vec d)) Y.potential)
    (hYflux : MemVectorL2 (U : Set (Vec d)) Y.flux) :
    doubledMuValue U a X + doubledMuValue U a Y
        - 2 * doubledMuValue U a ((1 / 2 : ℝ) • (X + Y))
      = (1 / 2 : ℝ) * doubledMuValue U a (X - Y) := by
  have hmidpot : MemVectorL2 (U : Set (Vec d))
      (((1 / 2 : ℝ) • (X + Y)).potential) := (hXpot.add hYpot).const_smul _
  have hmidflux : MemVectorL2 (U : Set (Vec d))
      (((1 / 2 : ℝ) • (X + Y)).flux) := (hXflux.add hYflux).const_smul _
  have hsubpot : MemVectorL2 (U : Set (Vec d)) ((X - Y).potential) :=
    hXpot.sub hYpot
  have hsubflux : MemVectorL2 (U : Set (Vec d)) ((X - Y).flux) :=
    hXflux.sub hYflux
  have hIX := integrableOn_blockEnergyDensity a hXpot hXflux
  have hIY := integrableOn_blockEnergyDensity a hYpot hYflux
  have hIM := integrableOn_blockEnergyDensity a hmidpot hmidflux
  have hIS := integrableOn_blockEnergyDensity a hsubpot hsubflux
  have hfun :
      ((fun x => blockEnergyDensityAt a (X.eval x) x)
          + (fun x => blockEnergyDensityAt a (Y.eval x) x))
        - (2 : ℝ) • (fun x => blockEnergyDensityAt a
            (((1 / 2 : ℝ) • (X + Y)).eval x) x)
      = (1 / 2 : ℝ) • fun x => blockEnergyDensityAt a ((X - Y).eval x) x := by
    funext x
    have h := blockEnergyDensityAt_parallelogram a (X.eval x) (Y.eval x) x
    change blockEnergyDensityAt a (X.eval x) x + blockEnergyDensityAt a (Y.eval x) x
        - 2 * blockEnergyDensityAt a (((1 / 2 : ℝ) • (X + Y)).eval x) x
      = (1 / 2 : ℝ) * blockEnergyDensityAt a ((X - Y).eval x) x
    rw [show ((1 / 2 : ℝ) • (X + Y)).eval x = (1 / 2 : ℝ) • (X.eval x + Y.eval x) from rfl,
      show (X - Y).eval x = X.eval x - Y.eval x from rfl]
    exact h
  change volumeAverage (U : Set (Vec d))
      (fun x => blockEnergyDensityAt a (X.eval x) x)
    + volumeAverage (U : Set (Vec d))
      (fun x => blockEnergyDensityAt a (Y.eval x) x)
    - 2 * volumeAverage (U : Set (Vec d))
      (fun x => blockEnergyDensityAt a (((1 / 2 : ℝ) • (X + Y)).eval x) x)
    = (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d))
      (fun x => blockEnergyDensityAt a ((X - Y).eval x) x)
  rw [← volumeAverage_smul (U : Set (Vec d)) (1 / 2 : ℝ), ← hfun,
    volumeAverage_sub (hIX.add hIY) (hIM.smul (2 : ℝ)),
    volumeAverage_add hIX hIY, volumeAverage_smul]

/-- **Uniform convexity of the doubled energy.**  A minimizer beats the
midpoint against any admissible competitor, so the energy gap dominates the
energy of the difference. -/
theorem half_doubledMuValue_sub_le_of_isDoubledMuMinimizer {U : Domain d}
    (a : CoeffOn U) {P : BlockVec d} {X Y : DoubledField d}
    (hX : IsDoubledMuMinimizer U a P X) (hY : IsDoubledMuAdmissible U P Y) :
    (1 / 2 : ℝ) * doubledMuValue U a (X - Y)
      ≤ doubledMuValue U a Y - doubledMuValue U a X := by
  have hXpot := memVectorL2_potential_of_isDoubledMuAdmissible hX.1
  have hXflux := memVectorL2_flux_of_isDoubledMuAdmissible hX.1
  have hYpot := memVectorL2_potential_of_isDoubledMuAdmissible hY
  have hYflux := memVectorL2_flux_of_isDoubledMuAdmissible hY
  have hpar := doubledMuValue_parallelogram a hXpot hXflux hYpot hYflux
  have hmid := hX.2 ((1 / 2 : ℝ) • (X + Y))
    (isDoubledMuAdmissible_midpoint hX.1 hY)
  linarith

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
