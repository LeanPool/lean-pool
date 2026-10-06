/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletCorrectedWeakFluxAveraged

/-!
# Coarse-graining support: Support.Book.Ch03.Theorems.CoarseFluxResponseRHS

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch03

/-!
# Section 3.2.4: Coarse-grained flux-response estimate with right-hand side

This file assembles the public theorem package for
`l.coarse.grained.flux.response.RHS.deterministic.theory`.  The left-hand side
uses the genuine dual negative Besov norm, not the concrete negative seminorm
from Section 3.1.

## Audit tag

Claim: expose the single public coarse flux-response-with-RHS package using
the genuine dual negative Besov norm.

Downstream target: `InhomogeneousEquationsTheory` and the Ch3.3 coarse-graining
handoff.  This file should not introduce additional RHS package variants.
-/

noncomputable section

open ZeroTraceDirichletCorrectorData

/-- Public theorem package for the coarse-grained flux-response estimate with
right-hand side. -/
structure CoarseFluxResponseRHSTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (a0 : ConstantCoeffMatrix d)
        (u : ForcedCubeSolution Q a g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          scaleNormalizedDualNegativeBesovVectorNormTwo Q s
              (forcedSolutionFluxDefectField Q a a0 u) ≤
            coarseFluxResponseWithRHSRHS C Q a a0 s g u

/-- Fully proved coarse-grained flux-response estimate with right-hand side. -/
theorem coarseFluxResponseRHS_negativeDual_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (a0 : ConstantCoeffMatrix d)
    (u : ForcedCubeSolution Q a g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    scaleNormalizedDualNegativeBesovVectorNormTwo Q s
        (forcedSolutionFluxDefectField Q a a0 u) ≤
      coarseFluxResponseWithRHSRHS
        ((d : ℝ) ^ 2 *
          max 1
            (((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
              (2 * zeroTraceFluxApexConstant d 1)))
        Q a a0 s g u := by
  let A : CoeffField d := publicCoeffField Q a
  let B : ℝ := _root_.HCPolySupport.coarseFluxResponseRHSBound Q A
    a0.matrix s (forcedSolutionGradientField u) g
  let K : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s)
  let K₁ : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)
  let M : ℝ := zeroTraceFluxApexConstant d s
  let M₁ : ℝ := zeroTraceFluxApexConstant d 1
  let C₀ : ℝ := max 1 (K₁ * (2 * M₁))
  let C : ℝ := (d : ℝ) ^ 2 * C₀
  have hs_le : s ≤ 1 := hs_lt.le
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hK₁_nonneg : 0 ≤ K₁ := by
    dsimp [K₁]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hK_le : K ≤ K₁ := by
    dsimp [K, K₁]
    have hpow :
        Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith)
    exact mul_le_mul_of_nonneg_left hpow (by exact_mod_cast Nat.zero_le d)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact zeroTraceFluxApexConstant_nonneg d s
  have hM_le : M ≤ M₁ := by
    dsimp [M, M₁]
    have hdisplay :
        zeroTraceFluxApexDisplayScale d s ≤
          zeroTraceFluxApexDisplayScale d 1 := by
      unfold zeroTraceFluxApexDisplayScale
      have hpow :
          (3 : ℝ) ^ ((d : ℝ) + s) ≤
            (3 : ℝ) ^ ((d : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (by linarith)
      have hinner :
          (3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2 ≤
            (3 : ℝ) ^ ((d : ℝ) + 1) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg 2)
      exact mul_le_mul_of_nonneg_left hinner (by exact_mod_cast Nat.zero_le d)
    unfold zeroTraceFluxApexConstant
    nlinarith
  have hKM_le_C₀ : K * (2 * M) ≤ C₀ := by
    have htwoM_nonneg : 0 ≤ 2 * M := by nlinarith
    have htwoM_le : 2 * M ≤ 2 * M₁ := by nlinarith [hM_le]
    have hprod : K * (2 * M) ≤ K₁ * (2 * M₁) :=
      mul_le_mul hK_le htwoM_le htwoM_nonneg hK₁_nonneg
    exact hprod.trans (le_max_right 1 (K₁ * (2 * M₁)))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, A]
    exact coarseFluxResponseRHSBound_nonneg_of_bddAbove
      Q (publicCoeffField Q a) a0.matrix
      (forcedSolutionGradientField u) g hs hg.partialSeminorms_bddAbove
  have hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ))
            MultiscaleExponent.infinity A a0.matrix) := by
    dsimp [A]
    exact homogenizationErrorOnCube_publicCoeffField_infinity_one_terms_summable
      a Q a0.matrix hs
  have hdet :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fluxDefect A a0.matrix (forcedSolutionGradientField u)) ≤
        2 * M * B := by
    have hraw :=
      ZeroTraceDirichletCorrectorData.besovFluxDefect_le_constant_mul_bound
        (Q := Q) (a := A) (a0 := a0.matrix) (s := s) (g := g)
        (v := publicH1ToCubeSet u.toH1)
        (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
        (lam0 := a0.lam) (Lam0 := a0.Lam)
        hs hs_le (by simpa [A] using publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        a0.elliptic a0.isSymm
        (by
          simpa [A] using
            isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
              (Q := Q) (a := a) (u := u.toH1) (g := g) u.weakSolution)
        hg hresponseSum
    simpa [A, B, M, forcedSolutionGradientField, publicH1ToCubeSet_grad] using hraw
  have hdual :
      scaleNormalizedDualNegativeBesovVectorNormTwo Q s
          (forcedSolutionFluxDefectField Q a a0 u) ≤
        K * cubeBesovNegativeVectorSeminormTwo Q s
          (fluxDefect A a0.matrix (forcedSolutionGradientField u)) := by
    simpa [K, A] using
      forcedSolutionFluxDefect_dualNorm_le_constant_mul_negativeBesovSeminormTwo
        (Q := Q) (a := a) (a0 := a0) (s := s) u hs
  have hbounded :
      scaleNormalizedDualNegativeBesovVectorNormTwo Q s
          (forcedSolutionFluxDefectField Q a a0 u) ≤ C₀ * B := by
    calc
      scaleNormalizedDualNegativeBesovVectorNormTwo Q s
          (forcedSolutionFluxDefectField Q a a0 u)
          ≤ K * cubeBesovNegativeVectorSeminormTwo Q s
              (fluxDefect A a0.matrix (forcedSolutionGradientField u)) := hdual
      _ ≤ K * (2 * M * B) := mul_le_mul_of_nonneg_left hdet hK_nonneg
      _ = (K * (2 * M)) * B := by ring
      _ ≤ C₀ * B := mul_le_mul_of_nonneg_right hKM_le_C₀ hB_nonneg
  have herror :
      HomogenizationErrorOnCube Q s MultiscaleExponent.infinity
          (MultiscaleExponent.finite 1) (publicCoeffField Q a) a0.matrix =
        Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
          (Ch02.MultiscaleExponent.finite 1) a a0.matrix :=
    homogenizationErrorOnCube_publicCoeffField_infinity_one_eq_ch02
      a Q s a0.matrix
  have hC₀_nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    exact le_trans zero_le_one (le_max_left 1 (K₁ * (2 * M₁)))
  have hBsemi_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g
      hg.partialSeminorms_bddAbove
  have hH_nonneg :
      0 ≤ Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
        (Ch02.MultiscaleExponent.finite 1) a a0.matrix :=
    Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q a a0.matrix hs
  have hrhs_le :
      C₀ * B ≤ coarseFluxResponseWithRHSRHS C Q a a0 s g u := by
    dsimp [B, A, C]
    exact
      coarseFluxResponseBound_le_dimSquared_publicRHS
        C₀ Q a a0 u hC₀_nonneg hs hBsemi_nonneg hH_nonneg herror
  simpa [C] using! hbounded.trans hrhs_le

/-- Fully proved public coarse-grained flux-response theorem package with RHS. -/
theorem coarseFluxResponseRHSTheory {d : ℕ} [NeZero d] :
    CoarseFluxResponseRHSTheory d := by
  refine ⟨?_⟩
  refine ⟨(d : ℝ) ^ 2 * max 1
    (((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
      (2 * zeroTraceFluxApexConstant d 1)), ?_, ?_⟩
  · have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos (sq_pos_of_pos hd_pos)
      (lt_of_lt_of_le zero_lt_one
        (le_max_left 1
          (((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
            (2 * zeroTraceFluxApexConstant d 1))))
  · intro Q a s g a0 u hs hs_lt hg
    exact coarseFluxResponseRHS_negativeDual_le
      (Q := Q) (a := a) (a0 := a0) (u := u) hs hs_lt hg

end

end Ch03
end Book
end HCPolySupport
