/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.UnitCubeWeakIBP
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# EnergyBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Energy bridge: `solutionEnergyNorm` versus the response functional

Source: ABK26 (`e.Jenergyv.nosymm` as used in the proof of `l.Dh.bound`):
  `‖σ^{1/2} ∇w‖²_{L²(□₀)} = 2 J(□₀, p, q; a)`,  `w = ½ v(·, □₀, p, q; a)`.

In the CoarseGraining vocabulary the left-hand side of that display, for the
*unscaled* maximizer `v`, is `Ch03.solutionEnergyNorm Q a v ^ 2`, i.e. the
square root of `Ch02.variationEnergyValue`.  The public maximizer-energy
identity `responseJ_eq_energy_of_isResponseMaximizer` gives `J = ½ · energy`,
hence `energy = 2 J`.

Every statement here is proved at a general Chapter 2 `Domain d`; the triadic
cube form (the vocabulary consumed by the coarse Poincaré inequality) is a
specialization stated for an *arbitrary* triadic cube `Q`, not only the origin
cube, as required by the descendant-cube consumers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **Energy bridge at a general domain.**  The variational energy of a
response maximizer is twice the response functional. -/
theorem variationEnergyValue_eq_two_mul_responseJ {U : Domain d} {a : CoeffOn U}
    {p q : Vec d} {v : Solution U a} (hv : IsResponseMaximizer U a p q v) :
    variationEnergyValue U a v = 2 * responseJ U a p q := by
  rw [responseJ_eq_energy_of_isResponseMaximizer hv]; ring

/-- **Energy bridge in the Chapter 3 cube vocabulary, at an arbitrary triadic
cube.**  The Chapter 3 solution energy norm of a response maximizer on
`cubeDomain Q` is `√(2 J)`. -/
theorem solutionEnergyNorm_eq_sqrt_two_mul_responseJ (Q : TriadicCube d)
    (F : Ch03.CoeffFamily d) {p q : Vec d} {v : Ch03.CubeSolution Q F}
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p q v) :
    Ch03.solutionEnergyNorm Q F v =
      Real.sqrt (2 * responseJ (cubeDomain Q) (F.coeffOn Q) p q) := by
  unfold Ch03.solutionEnergyNorm
  rw [variationEnergyValue_eq_two_mul_responseJ hv]

/-- The energy bridge in the form used by the assembly: the Chapter 3 energy
norm of a maximizer is `√2 · √J`. -/
theorem solutionEnergyNorm_eq_sqrt_two_mul_sqrt_responseJ (Q : TriadicCube d)
    (F : Ch03.CoeffFamily d) {p q : Vec d} {v : Ch03.CubeSolution Q F}
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p q v) :
    Ch03.solutionEnergyNorm Q F v =
      Real.sqrt 2 * Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q) := by
  rw [solutionEnergyNorm_eq_sqrt_two_mul_responseJ Q F hv,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Chapter 3 energy norm of a maximizer is bounded by `2 √J`; this is the
form fed to the assembly, where all constants are absorbed. -/
theorem solutionEnergyNorm_le_two_mul_sqrt_responseJ (Q : TriadicCube d)
    (F : Ch03.CoeffFamily d) {p q : Vec d} {v : Ch03.CubeSolution Q F}
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p q v) :
    Ch03.solutionEnergyNorm Q F v ≤
      2 * Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q) := by
  rw [solutionEnergyNorm_eq_sqrt_two_mul_sqrt_responseJ Q F hv]
  have h2 : Real.sqrt 2 ≤ 2 := by
    have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at this
    exact this
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
