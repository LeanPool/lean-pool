/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringSlot

/-!
# BoundaryPrefactor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary Caccioppoli prefactor at the slot `n+3`, on the covering cube

The boundary lane's Caccioppoli inequality runs on the covering cube `c +
□_{n+2}`, `c = wellPlacedCentre x m (n+2)`, and its right-hand side carries two
coarse-grained factors: CoarseGraining's `caccioppoliWith a s_c t` and the
lower constant `λ_t(Q; a)`.  `BoundaryCoveringSlot` capped the covering
cube's `q = 2` ratio pair at the *coarse-graining slot* `s/6`; this module
reads the caps at the **pair of indices the boundary Caccioppoli actually
consumes** and turns them into a `d`-only bound on the prefactor.

## The parameter pair

The proved interior chain runs the Caccioppoli at `(s_c, t) = (1/4, s/4)`.
That pair is **not available off-grid**: its lower ingredient needs the `q = 2`
ratio at `(s/4)/2 = s/8`, and the off-grid transport of
`BoundaryCoveringSlot` (`ae_coveringCubeError_le_representative`) requires
an index *strictly* above the good-event slot `s/8`.  The boundary lane
therefore runs at

```text
  (s_c, t) = (1/2, s/3) ,
```

whose two ratio indices are `1/4` and `s/6`, both strictly above `s/8` for
every `s ∈ (0,1]`, and which satisfies CoarseGraining's own range conditions `0
< s_c < 1`, `0 < t < 1/2`, `s_c + t < 1`.  **The pair costs no `s`-power**: the
prefactor's middle factor is `s_c^{-2s_c/σ}` at the *first* parameter `s_c =
1/2`, a pure number.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; the boundary application.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

private theorem isotropicComparator_eq_scalarMatrix_boundaryPair
    (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) :=
  rfl

/-! ## 1. The off-grid constant at the upper index -/

/-- **The off-grid stability constant at the pair `(1/4, s/8)`.**

`36 d (1/4) / ((1/4 − s/8)(1 − s/4)) ≤ 96 d` for every `s ∈ (0,1]`; the
extremal configuration is `s = 1`, where the denominator is `3/32`.  (The
proved slot bound is `offGridStabilityConst_slot_le` at `(s/6, s/8)`; this is
its sibling at the upper index, and `96 d ≤ 192 d`, so both are absorbed by the
same `κ`.) -/
theorem offGridStabilityConst_quarter_le (d : ℕ) {s : ℝ} (_hs0 : 0 < s)
    (hs1 : s ≤ 1) :
    offGridStabilityConst d (1 / 4) (s / 8) ≤ 96 * (d : ℝ) := by
  have hden : (0 : ℝ) < (1 / 4 - s / 8) * (1 - 2 * (s / 8)) := by
    refine mul_pos (by linarith only [hs1]) ?_
    linarith only [hs1]
  rw [offGridStabilityConst, div_le_iff₀ hden]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hkey : (0 : ℝ) ≤ (d : ℝ) * (1 - s) * (5 - s) :=
    mul_nonneg (mul_nonneg hdnn (by linarith only [hs1])) (by linarith only [hs1])
  nlinarith only [hkey]

/-! ## 2. The coarse-grained caps at the boundary pair -/

/-- Covering-cube caps under explicit half-open parent containment. -/
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
  rw [← isotropicComparator_eq_scalarMatrix_boundaryPair] at hratio6 hratio4
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

/-- **The covering cube's `q = 1` ingredients at the boundary Caccioppoli
pair.**

On the frozen general clause's own good event `𝒢(n+3, z; s/8, 1/2)`, the
coarse-grained ellipticity data of the `(n+3)` re-based family on the covering
cube — the upper constant at `1/2`, the lower constant at `s/3`, and their
contrast — are all controlled by one `d`-only constant `K` against `σ_{n+3}`. -/
theorem ae_coveringCubeCapsPair_le (d : ℕ) [NeZero d] :
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
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                    ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                      openCubeSet (originCube d m) →
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
  obtain ⟨C, K, hCpos, hKpos, hcaps⟩ := ae_coveringCubeCapsPair_le_gapThree d
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z
  filter_upwards [hcaps M s hsrange hregime hsmall hs L m n hmL hnm z] with omega hall
  intro hmem x hx hgeom
  exact hall hmem x (translateSet_cubeSet_coveringCube_subset_anchorParent (by omega) hx hgeom)

/-! ## 3. The prefactor at the boundary pair -/

/-- **The prefactor at `(s_c, t) = (1/2, s/3)` is a constant.**

For every `s ∈ (0,1]`, every `C > 0` and every cap `Θ ≤ Θ₀`,

```text
  (C/σ)^{2+4·(1/2)/σ} · (1/2)^{-2·(1/2)/σ} · Θ^{(1−s/3)/σ}
      ≤ (6C)^{14} · 64 · Θ₀^6 ,     σ = 1 − 1/2 − s/3 ∈ [1/6, 1/2) .
```

Every step is a rational comparison of `rpow` exponents; no transcendental
estimate and no `s`-power is used. -/
theorem caccioppoliWithRHSPrefactor_boundaryPair_le [NeZero d] {Q : TriadicCube d}
    {a : CoeffFamily d} {C s Theta0 : ℝ} (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hTheta : Ch02.ThetaRatio Q (1 / 2) (s / 3) a ≤ Theta0) :
    caccioppoliWithRHSPrefactor C Q a (1 / 2) (s / 3) ≤
      (6 * max 1 C) ^ (14 : ℕ) * 64 * Theta0 ^ (6 : ℕ) := by
  have hCm : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hCle : C ≤ max 1 C := le_max_right _ _
  have hTh1 : 1 ≤ Ch02.ThetaRatio Q (1 / 2) (s / 3) a :=
    Ch02.one_le_ThetaRatio_of_pos Q a (by norm_num) (by linarith only [hs])
  have hsg_lo : (1 : ℝ) / 6 ≤ 1 - 1 / 2 - s / 3 := by linarith only [hs1]
  have hsg_pos : (0 : ℝ) < 1 - 1 / 2 - s / 3 := by linarith only [hsg_lo]
  have hinv : (1 - 1 / 2 - s / 3)⁻¹ ≤ 6 := by
    have h := inv_anti₀ (show (0 : ℝ) < 1 / 6 by norm_num) hsg_lo
    rw [show ((1 : ℝ) / 6)⁻¹ = 6 by norm_num] at h
    exact h
  have hCmpos : (0 : ℝ) < max 1 C := lt_of_lt_of_le zero_lt_one hCm
  -- the first factor
  have hbase0 : (0 : ℝ) ≤ C / (1 - 1 / 2 - s / 3) := div_nonneg hC.le hsg_pos.le
  have hbase2 : C / (1 - 1 / 2 - s / 3) ≤ 6 * max 1 C := by
    rw [div_le_iff₀ hsg_pos]
    have hstep : 6 * max 1 C * (1 / 6) ≤ 6 * max 1 C * (1 - 1 / 2 - s / 3) :=
      mul_le_mul_of_nonneg_left hsg_lo (by linarith only [hCmpos])
    linarith only [hstep, hCle]
  have he1 : (4 : ℝ) * (1 / 2) / (1 - 1 / 2 - s / 3) ≤ 12 := by
    rw [show (4 : ℝ) * (1 / 2) = 2 by norm_num]
    have h : (2 : ℝ) * (1 - 1 / 2 - s / 3)⁻¹ ≤ 2 * 6 :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    rw [div_eq_mul_inv]
    linarith only [h]
  have he1nn : (0 : ℝ) ≤ 2 + 4 * (1 / 2) / (1 - 1 / 2 - s / 3) := by
    have h : (0 : ℝ) ≤ 4 * (1 / 2) / (1 - 1 / 2 - s / 3) := by positivity
    linarith only [h]
  have hT1 : Real.rpow (C / (1 - 1 / 2 - s / 3))
      (2 + 4 * (1 / 2) / (1 - 1 / 2 - s / 3)) ≤ (6 * max 1 C) ^ (14 : ℕ) := by
    calc Real.rpow (C / (1 - 1 / 2 - s / 3))
          (2 + 4 * (1 / 2) / (1 - 1 / 2 - s / 3))
        ≤ Real.rpow (6 * max 1 C) (2 + 4 * (1 / 2) / (1 - 1 / 2 - s / 3)) :=
          Real.rpow_le_rpow hbase0 hbase2 he1nn
      _ ≤ Real.rpow (6 * max 1 C) (14 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith only [hCm])
            (by linarith only [he1])
      _ = (6 * max 1 C) ^ (14 : ℕ) := by
          rw [Real.rpow_eq_pow, show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
  -- the second factor
  have he2 : (-6 : ℝ) ≤ -(2 * (1 / 2) / (1 - 1 / 2 - s / 3)) := by
    have hone : (2 : ℝ) * (1 / 2) / (1 - 1 / 2 - s / 3) ≤ 6 := by
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_div]
      exact hinv
    linarith only [hone]
  have hT2 : Real.rpow (1 / 2 : ℝ) (-(2 * (1 / 2) / (1 - 1 / 2 - s / 3))) ≤ 64 := by
    calc Real.rpow (1 / 2 : ℝ) (-(2 * (1 / 2) / (1 - 1 / 2 - s / 3)))
        ≤ Real.rpow (1 / 2 : ℝ) (-6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) he2
      _ = 64 := by
          rw [Real.rpow_eq_pow, show (-6 : ℝ) = ((-6 : ℤ) : ℝ) by norm_num,
            Real.rpow_intCast]
          norm_num
  -- the third factor
  have he3 : (1 - s / 3) / (1 - 1 / 2 - s / 3) ≤ 6 := by
    rw [div_le_iff₀ hsg_pos]
    linarith only [hs1]
  have hT3 : Real.rpow (Ch02.ThetaRatio Q (1 / 2) (s / 3) a)
      ((1 - s / 3) / (1 - 1 / 2 - s / 3)) ≤ Theta0 ^ (6 : ℕ) := by
    calc Real.rpow (Ch02.ThetaRatio Q (1 / 2) (s / 3) a)
          ((1 - s / 3) / (1 - 1 / 2 - s / 3))
        ≤ Real.rpow (Ch02.ThetaRatio Q (1 / 2) (s / 3) a) (6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hTh1 he3
      _ ≤ Real.rpow Theta0 (6 : ℝ) :=
          Real.rpow_le_rpow (le_trans zero_le_one hTh1) hTheta (by norm_num)
      _ = Theta0 ^ (6 : ℕ) := by
          rw [Real.rpow_eq_pow, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
  -- assemble
  have hT2nn : (0 : ℝ) ≤ Real.rpow (1 / 2 : ℝ)
      (-(2 * (1 / 2) / (1 - 1 / 2 - s / 3))) := Real.rpow_nonneg (by norm_num) _
  have hT3nn : (0 : ℝ) ≤ Real.rpow (Ch02.ThetaRatio Q (1 / 2) (s / 3) a)
      ((1 - s / 3) / (1 - 1 / 2 - s / 3)) :=
    Real.rpow_nonneg (le_trans zero_le_one hTh1) _
  have hprod1 : (0 : ℝ) ≤ (6 * max 1 C) ^ (14 : ℕ) * 64 := by positivity
  rw [caccioppoliWithRHSPrefactor]
  exact mul_le_mul (mul_le_mul hT1 hT2 hT2nn (by positivity)) hT3 hT3nn hprod1

/-! ## 4. The coarse-grained prefactor on the covering cube -/

/-- The boundary prefactor under explicit half-open parent containment. -/
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

/-- **The boundary Caccioppoli's two coarse-grained factors, capped.**

On the frozen good event, the boundary Caccioppoli's prefactor at the pair
`(1/2, s/3)` and its lower constant `λ_{s/3}` — both read on the covering cube
at the `(n+3)` re-based family, with no `Λ`/`λ` converted by invariance — are
controlled by one constant depending on `d` and CoarseGraining's own
Caccioppoli constant, times `σ_{n+3}` for the lower constant.  **No `s`-power
is spent.** -/
theorem ae_coveringCubePrefactor_le (d : ℕ) [NeZero d] :
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
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                    ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                      openCubeSet (originCube d m) →
                ∀ C₁ : ℝ, 0 < C₁ →
                  caccioppoliWithRHSPrefactor C₁ (originCube d (n + 2))
                      (parentRebasedFamily M L (n + 3)
                        (wellPlacedCentre x m (n + 2)) z omega) (1 / 2) (s / 3) ≤
                    (6 * max 1 C₁) ^ (14 : ℕ) * 64 * (K * K) ^ (6 : ℕ) ∧
                  Ch02.lambdaS (originCube d (n + 2)) (s / 3)
                      (parentRebasedFamily M L (n + 3)
                        (wellPlacedCentre x m (n + 2)) z omega) ≤
                    K * (Annealed.sigmaBar M (n + 3) : ℝ) := by
  obtain ⟨C, K, hCpos, hKpos, hpref⟩ := ae_coveringCubePrefactor_le_gapThree d
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z
  filter_upwards [hpref M s hsrange hregime hsmall hs L m n hmL hnm z] with omega hall
  intro hmem x hx hgeom C₁ hC₁
  exact hall hmem x (translateSet_cubeSet_coveringCube_subset_anchorParent (by omega) hx hgeom)
    C₁ hC₁

end

end Algsuperdiff.Section4.Provider.ExcessDecay
