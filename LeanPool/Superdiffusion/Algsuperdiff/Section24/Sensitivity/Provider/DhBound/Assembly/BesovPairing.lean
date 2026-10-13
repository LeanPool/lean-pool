/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly.GaugeBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.HarmonicRemainder
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

/-!
# BesovPairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Besov pairing against a response gradient

Source: ABK26 (`e.sensitivity.basic.split1` and `e.split.besov.stuff.begin`).
Both terms of the `D_h` split are estimated by the *same* mechanism:

  `|⨍_Q F · H| ≤ C ‖H‖_{B^{3/8}_{2,2}(Q)} ‖F‖_{B^{-3/8}_{2,2}(Q)}`,

applied with `F = ∇v` and then combined with the coarse Poincaré inequality
`‖∇v‖_{B^{-3/8}_{2,2}} ≤ C λ_{3/8,2}^{-1/2} J^{1/2}`.

This module packages that combination once and for all: given any second factor
`H` with a positive-Besov budget `B`, the averaged pairing against the gradient
of a response maximizer is bounded by `C(d) · B · λ^{-1/2} · J^{1/2}`.

Term A of the source proof is this lemma with `H x = hᵀ(x) p`; Term BC is this
lemma with `H x = (w + w* + ℓ_p)(x) (∇·h)(x)`.

Everything is stated at an arbitrary triadic cube `Q` and an arbitrary
CoarseGraining coefficient family `F`, as required by the descendant-cube
consumers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Average bridges -/

/-- The Chapter 2 average over `cubeDomain Q` is the Chapter 3 cube average. -/
theorem average_cubeDomain_eq_cubeAverage (Q : TriadicCube d) (f : Vec d → ℝ) :
    Book.Ch02.average (cubeDomain Q) f = cubeAverage Q f := by
  rw [HCPolySupport.Internal.Ch02.book_average_eq_volumeAverage]
  rw [Ch02.cubeDomain_coe]
  rw [← ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube]
  exact volumeAverage_cubeSet_eq_cubeAverage Q f

/-! ## Transporting the coarse Poincaré bound to the duality hypothesis -/

/-- The gradient of a public `H¹` function on `cubeDomain Q` is square
integrable on the closed cube. -/
theorem memVectorL2_cubeSet_grad [NeZero d] {Q : TriadicCube d}
    (u : H1Function ((cubeDomain Q : Domain d) : Set (Vec d))) :
    MemVectorL2 (cubeSet Q) u.grad := by
  simpa [Ch03.publicH1ToCubeSet_grad] using
    (Ch03.publicH1ToCubeSet u).grad_memVectorL2

/-- Every partial negative Besov seminorm of a field is dominated by the frozen
concrete negative Besov norm at exponent `q = 2`. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_le_scaleNormalizedNegativeBesovVectorNorm
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (G : Vec d → Vec d)
    (hG : MemVectorL2 (cubeSet Q) G) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N G ≤
      Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) G := by
  have hbdd := cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs G
    (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hG)
  rw [Ch03.scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm]
  exact le_csSup hbdd ⟨N, rfl⟩

/-! ## The pairing estimate -/

/-- **Besov pairing against a response gradient.**

For every field `H` with positive Besov budget `B` at smoothness `3/8`,

  `|⨍_Q ∇v · H| ≤ (1 + d 3^{d+1}) · (2 c_{3/8,2}^{-1/2}) · B · λ_{3/8,2}^{-1/2} · J^{1/2}`,

where `v` is any response maximizer for `(a, p, q)` on `Q`.

This is the common engine of `e.sensitivity.basic.split1` (Term A) and
`e.split.besov.stuff.begin` (Term BC).  The positive Besov budget `B` is the
only input not proved here. -/
theorem abs_cubeAverage_vecDot_grad_le_of_positiveBesov_bound
    [NeZero d] (Q : TriadicCube d) (F : Ch03.CoeffFamily d) {p q : Vec d}
    {v : Ch03.CubeSolution Q F}
    (hv : IsResponseMaximizer (cubeDomain Q) (F.coeffOn Q) p q v)
    (H : Vec d → Vec d) {B : ℝ}
    (hH : Ch03.ForceBesovRegularity Q (3 / 8) H)
    (hHnorm : Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q (3 / 8) H ≤ B) :
    |cubeAverage Q (fun x => vecDot (v.toH1.grad x) (H x))| ≤
      (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
          (2 * Ch03.poincareDiscountFactor (3 / 8) (.finite 2)) * B *
        (Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
          Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q)) := by
  classical
  have hgradL2 : MemVectorL2 (cubeSet Q) v.toH1.grad := memVectorL2_cubeSet_grad v.toH1
  -- the coarse Poincaré budget for the gradient
  set Bflux : ℝ :=
    Ch03.poincareDiscountFactor (3 / 8) (.finite 2) *
      Real.sqrt ((Ch02.lambdaSq Q (3 / 8) (.finite 2) F)⁻¹) *
      (2 * Real.sqrt (responseJ (cubeDomain Q) (F.coeffOn Q) p q)) with hBflux
  have hpoincare :
      Ch03.scaleNormalizedNegativeBesovVectorNorm Q (3 / 8) (.finite 2)
        v.toH1.grad ≤ Bflux :=
    scaleNormalizedNegativeBesovVectorNorm_solutionGradient_le Q F hv
  have hBflux_nonneg : 0 ≤ Bflux := by
    refine mul_nonneg (mul_nonneg poincareDiscountFactor_sensitivity_pos.le
      (Real.sqrt_nonneg _)) ?_
    positivity
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminormTwo Q (3 / 8) N v.toH1.grad ≤ Bflux :=
    fun N =>
      (cubeBesovNegativeVectorPartialSeminormTwo_le_scaleNormalizedNegativeBesovVectorNorm
        Q (by norm_num) v.toH1.grad hgradL2 N).trans hpoincare
  -- the Besov duality estimate
  have hdual :=
    Ch03.abs_cubeAverage_vecDot_le_public_negative_positive_besov_duality_of_partial_flux_bound
      (Q := Q) (s := (3 / 8 : ℝ)) (Bflux := Bflux) (F := v.toH1.grad) (H := H)
      (by norm_num) (by norm_num)
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hgradL2)
      hH hBflux_nonneg hneg
  have hPnonneg : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q (3 / 8) H := by
    have hsemi :=
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := (3 / 8 : ℝ)) (g := H) hH
    have := Real.sqrt_nonneg (vecNormSq (cubeAverageVec Q H))
    simpa [Ch03.scaleNormalizedPositiveBesovVectorNormTwo] using
      add_nonneg this hsemi
  have hCnonneg : (0 : ℝ) ≤ 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    have : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    positivity
  refine hdual.trans ?_
  have hstep :
      (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) * Bflux *
          Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q (3 / 8) H ≤
        (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) * Bflux * B :=
    mul_le_mul_of_nonneg_left hHnorm (mul_nonneg hCnonneg hBflux_nonneg)
  refine hstep.trans (le_of_eq ?_)
  rw [hBflux]
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
