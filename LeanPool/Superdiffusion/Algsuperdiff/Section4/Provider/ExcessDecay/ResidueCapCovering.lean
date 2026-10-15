/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryPrefactor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseIndexBridges

/-!
# ResidueCapCovering

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The covering-cube cap family, re-cut at the geometric hinge

Nothing here claims the anchor or any
source node.  The only two imports are the proved covering-cube modules
`BoundaryPrefactor` and `CoarseIndexBridges`.

## What is proved

The proved covering-cube cap family is stated at the *anchor geometry binder*

```text
  hgeom : (fun y => x + y) '' □°_n ⊆ ((fun y => z + y) '' □°_{n+1}) ∩ □°_m .
```

Measurement of the five proved theorems shows that `hgeom` (together with `n +
2 ≤ m` and `x ∈ □°_m`) is consumed for **exactly one** thing: the half-open
containment

```text
  HINGE :  translateSet (wellPlacedCentre x m (n+2) - z) □_{n+2} ⊆ □_{n+3}
```

produced by
`BoundaryCoveringSlot.translateSet_cubeSet_coveringCube_subset_anchorParent`.
This module restates the same five theorems with `HINGE` itself as the inner
binder, in place of `hgeom` and of the two premises that only fed it.  Every
conclusion, constant, index and outer regime/smallness preamble is
byte-identical to the proved original; each proof is the proved proof with the
hinge *supplied* rather than *derived*.

* `ae_coveringCubeError_le_representative_gapThree` — the off-grid coarse-graining
  error transport at depth one (`≡ ae_coveringCubeError_le_representative`);
* `ae_coveringCubeCaps_le_gapThree` — the `q = 2` ratio pair at the slot `s/6`
  and the three `q = 1` ingredients (`≡ ae_coveringCubeCaps_le`);
* `ae_coveringCubeCapsPair_le_gapThree` — the `q = 1` ingredients at the boundary
  Caccioppoli pair `(1/2, s/3)` (`≡ ae_coveringCubeCapsPair_le`);
* `ae_coveringCubePrefactor_le_gapThree` — the capped prefactor and lower constant
  (`≡ ae_coveringCubePrefactor_le`);
* `ae_coveringCubeRatioCap_le_gapThree` — the parametric `q = 2` ratio cap at a
  free index `t` (`≡ ae_coveringCubeRatioCap_le`).

The final record `translateSet_cubeSet_coveringCube_gapThree_of_anchorGeometry`
is the one-line statement that the proved binder *implies* the hinge, so every
proved statement is recovered by feeding it: this file is a **strict
generalization**, never a weakening.

## References

* ABK26, `e.mathcalE.stability.applied`; the boundary application of
  `l.coarse.grained.Caccioppoli.RHS` (for the prefactor).
* `Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryCoveringSlot.lean`,
  `BoundaryPrefactor.lean`, `CoarseIndexBridges.lean` — the proved
  originals.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

private theorem isotropicComparator_eq_scalarMatrix_gapThree (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) := rfl

/-! ## 1. The off-grid error transport, at the hinge -/

/-! ## 2. The slot caps and the three `q = 1` ingredients, at the hinge -/

/-! ## 3. The boundary Caccioppoli pair's ingredients, at the hinge -/

/-- **The covering cube's `q = 1` ingredients at the boundary Caccioppoli pair
`(1/2, s/3)`, at the hinge.**

`ae_coveringCubeCapsPair_le` with the half-open containment supplied as a
binder in place of `x ∈ □°_m` and the anchor geometry binder. -/
theorem ae_coveringCubeCapsPair_le_gapThree (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ x : Vec d,
                translateSet (wellPlacedCentre x m (n + 2) - z)
                    (cubeSet (originCube d (n + 2))) ⊆
                  cubeSet (originCube d (n + 3)) →
                Ch02.LambdaS (originCube d (n + 2)) (1 / 2)
                      (parentRebasedFamily M L (n + 3)
                        (wellPlacedCentre x m (n + 2)) z omega) ≤
                    K * (Annealed.sigmaBar M (n + 3) : ℝ) ∧
                  (Ch02.lambdaS (originCube d (n + 2)) (s / 3)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤
                      K * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ∧
                  Ch02.lambdaS (originCube d (n + 2)) (s / 3)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) ≤
                      K * (Annealed.sigmaBar M (n + 3) : ℝ) ∧
                  Ch02.ThetaRatio (originCube d (n + 2)) (1 / 2) (s / 3)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) ≤ K * K := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  refine ⟨C, 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1), hCpos, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (kappa * (C * (1 / 2))) ^ 2 + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  intro M s hsrange hregime hsmall hs L m n hmL hnm z
  have hs1 : s ≤ 1 := hsrange.2
  have hs6 : (0 : ℝ) < s / 6 := by linarith only [hs]
  have hs3 : (0 : ℝ) < s / 3 := by linarith only [hs]
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) := (Annealed.sigmaBar M (n + 3)).2
  filter_upwards [hC M s hsrange hregime hsmall hs n z,
    ae_coveringCubeError_le_representative_gapThree M L n m z hs
      (by linarith only [hs] : s / 8 < s / 6) (by linarith only [hs1] : s / 6 ≤ 1 / 2),
    ae_coveringCubeError_le_representative_gapThree M L n m z hs
      (by linarith only [hs1] : s / 8 < 1 / 4) (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2)]
    with omega hcap herr6 herr4
  intro hmem x hhinge
  have hErep0 : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hErepCap := hcap hmem L (le_trans hnm hmL)
  have h3s8 : ((3 : ℝ) ^ (s / 8)) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith only [hs1] : s / 8 ≤ (1 : ℝ))
    rwa [Real.rpow_one] at h
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 8) *
      fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
        (Cutoff.translateCutoffSample z omega) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
  have h3 : (3 : ℝ) ^ (s / 8) *
      fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
        (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
    have hstepa := mul_le_mul_of_nonneg_right h3s8 hErep0
    have hstepb : (3 : ℝ) *
        fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
      linarith only [hErepCap]
    linarith only [hstepa, hstepb]
  -- the two coarse-graining errors, at the two ratio indices
  have hE6 : Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) (s / 6) .infinity
      (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
      kappa * (C * (1 / 2)) := by
    refine (herr6 x hhinge).trans ?_
    have h1 : Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) ≤
        Real.sqrt (192 * (d : ℝ)) :=
      Real.sqrt_le_sqrt (offGridStabilityConst_slot_le hs hs1)
    calc Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
          ((3 : ℝ) ^ (s / 8) *
            fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega))
        ≤ Real.sqrt (192 * (d : ℝ)) * (3 * (C * (1 / 2))) :=
          mul_le_mul h1 h3 h3nn (Real.sqrt_nonneg _)
      _ = kappa * (C * (1 / 2)) := by rw [hkappadef]; ring
  have hE4 : Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) (1 / 4) .infinity
      (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
      kappa * (C * (1 / 2)) := by
    refine (herr4 x hhinge).trans ?_
    have h1 : Real.sqrt (offGridStabilityConst d (1 / 4) (s / 8)) ≤
        Real.sqrt (192 * (d : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      have h96 := offGridStabilityConst_quarter_le d hs hs1
      have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [h96, hdnn]
    calc Real.sqrt (offGridStabilityConst d (1 / 4) (s / 8)) *
          ((3 : ℝ) ^ (s / 8) *
            fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega))
        ≤ Real.sqrt (192 * (d : ℝ)) * (3 * (C * (1 / 2))) :=
          mul_le_mul h1 h3 h3nn (Real.sqrt_nonneg _)
      _ = kappa * (C * (1 / 2)) := by rw [hkappadef]; ring
  -- the ratio caps at the two indices
  have hE6nn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) (s / 6)
      .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hs6
  have hE4nn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) (1 / 4)
      .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) (by norm_num)
  have hratio6 := max_ellipticityRatio_le_homogenizationError (d := d)
    (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) hs6
    (Annealed.sigmaBar M (n + 3)).2
  have hratio4 := max_ellipticityRatio_le_homogenizationError (d := d)
    (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
    (by norm_num : (0 : ℝ) < 1 / 4) (Annealed.sigmaBar M (n + 3)).2
  rw [← isotropicComparator_eq_scalarMatrix_gapThree] at hratio6 hratio4
  have hmax6 := hratio6.trans (two_mul_dim_mul_sq_add_one_le_of_le hE6nn hE6)
  have hmax4 := hratio4.trans (two_mul_dim_mul_sq_add_one_le_of_le hE4nn hE4)
  have hU4 := le_trans (le_max_left _ _) hmax4
  have hL6 := le_trans (le_max_right _ _) hmax6
  -- the `q = 1` ingredients
  have hB1 : Ch02.LambdaS (originCube d (n + 2)) (1 / 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) := by
    refine LambdaS_le_of_ratio_cap (originCube d (n + 2)) _ (by norm_num) hsig ?_
    rwa [show (1 : ℝ) / 2 / 2 = 1 / 4 by norm_num]
  have hB2 : (Ch02.lambdaS (originCube d (n + 2)) (s / 3)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ := by
    refine lambdaS_inv_le_of_ratio_cap (originCube d (n + 2)) _ hs3 hsig ?_
    rwa [show s / 3 / 2 = s / 6 by ring]
  have hB3 : Ch02.lambdaS (originCube d (n + 2)) (s / 3)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) ≤
      2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) :=
    le_trans (lambdaS_le_LambdaS (originCube d (n + 2)) _ (by norm_num) hs3) hB1
  refine ⟨hB1, hB2, hB3, ?_⟩
  refine (thetaRatio_le_of_caps (originCube d (n + 2)) _ (by norm_num) hs3 hB1 hB2).trans
    (le_of_eq ?_)
  have hsne : ((Annealed.sigmaBar M (n + 3) : ℝ)) ≠ 0 := ne_of_gt hsig
  calc 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
        (Annealed.sigmaBar M (n + 3) : ℝ) *
        (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹)
      = 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1)) *
          ((Annealed.sigmaBar M (n + 3) : ℝ) *
            ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹) := by ring
    _ = 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1) *
          (2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1)) := by
        rw [mul_inv_cancel₀ hsne, mul_one]

/-! ## 4. The prefactor on the covering cube, at the hinge -/

/-- **The boundary Caccioppoli's two coarse-grained factors, capped, at the
hinge.**

`ae_coveringCubePrefactor_le` with the half-open containment supplied as a
binder; the proof is the proved one, consuming
`ae_coveringCubeCapsPair_le_gapThree` in place of
`ae_coveringCubeCapsPair_le`.  **No `s`-power is spent.** -/
theorem ae_coveringCubePrefactor_le_gapThree (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ x : Vec d,
                translateSet (wellPlacedCentre x m (n + 2) - z)
                    (cubeSet (originCube d (n + 2))) ⊆
                  cubeSet (originCube d (n + 3)) →
                ∀ C₁ : ℝ, 0 < C₁ →
                  caccioppoliWithRHSPrefactor C₁ (originCube d (n + 2))
                      (parentRebasedFamily M L (n + 3)
                        (wellPlacedCentre x m (n + 2)) z omega) (1 / 2) (s / 3) ≤
                    (6 * max 1 C₁) ^ (14 : ℕ) * 64 * (K * K) ^ (6 : ℕ) ∧
                  Ch02.lambdaS (originCube d (n + 2)) (s / 3)
                      (parentRebasedFamily M L (n + 3)
                        (wellPlacedCentre x m (n + 2)) z omega) ≤
                    K * (Annealed.sigmaBar M (n + 3) : ℝ) := by
  obtain ⟨C, K, hCpos, hKpos, hcaps⟩ := ae_coveringCubeCapsPair_le_gapThree d
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z
  have hs1 : s ≤ 1 := hsrange.2
  filter_upwards [hcaps M s hsrange hregime hsmall hs L m n hmL hnm z] with omega hall
  intro hmem x hhinge C₁ hC₁
  obtain ⟨_, _, hlam, hTheta⟩ := hall hmem x hhinge
  exact ⟨caccioppoliWithRHSPrefactor_boundaryPair_le hC₁ hs hs1 hTheta, hlam⟩

/-! ## 5. The parametric ratio cap, at the hinge -/


end

end Algsuperdiff.Section4.Provider.ExcessDecay
