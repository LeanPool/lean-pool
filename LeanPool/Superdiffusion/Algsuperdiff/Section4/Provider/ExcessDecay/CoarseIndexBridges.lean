/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringSlot
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryTransports

/-!
# CoarseIndexBridges

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `G-small-1`, `G-small-2`, `G-M2`: the `r = s/2` pin's small bridges

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## The three gaps this module closes

Three small bridges are then needed.

* **`G-small-1`** (§1): the two coarse caps the Dirichlet energy estimate reads
  at that pin — `Λ_{s/2,2}` and `λ_{s/4,2}^{-1}` at the `(n+3)` re-based family
  on the covering cube — capped against `σ_{n+3}` on the frozen good event
  `𝒢(n+3, z; s/8, 1/2)`.  Both indices lie in `(s/8, 1/2]` for every
  `s ∈ (0,1]`, which is exactly why `s/2` is the pin: at the earlier `r = s`
  the index `Λ_{s,2}` leaves the good-event window for `s ∈ (1/2, 1]`.
  The proof is one parametric instance of `BoundaryCoveringSlot`'s own
  two-lemma pattern (off-grid error transport + ratio cap).
* **`G-small-2`** (§2): the index conversion `[·]_{s/2} → [·]_s` on the
  scale-normalized positive Besov carrier.  **Finding: this costs nothing.**
  CoarseGraining already proves the exact monotonicity
  (`cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove`): the
  depth weights are `3^{u j}` with `j ≥ 0`, increasing in `u`.  No `3`-power
  and no constant appear — strictly better than the plan's budgeted
  `3^{(s/2)(n+3)}`-type factor.  Recorded as an improvement.
* **`G-M2`** (§3): the `ForceBesovRegularity` binders that
  `BoundaryEnergyRebase.exists_boundaryWindowEnergy_rebased_le_dirichletDatumRHS`
  asks of its caller, at the pin `r = s/2`, for the transported force `y ↦ −g(y
  + c)` and the transported boundary gradient `y ↦ ∇h(y + c)`, from the
  anchor's clause-(iv) `MemLp` data on `□_m`.

## References

* CoarseGraining: `Deterministic/WeakNormInterfacesPositiveQTwo.lean`,
  `Deterministic/CoarsePoincare/Regularity.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. `G-small-1`: the `q = 2` ratio caps at the pin's two indices -/

/-- The off-grid stability constant at the pin's two indices is below the same `192
d` the proved `s/6` slot uses. -/
theorem offGridStabilityConst_pinHalf_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    offGridStabilityConst d (s / 2) (s / 8) ≤ 192 * (d : ℝ) := by
  have hden : (0 : ℝ) < (s / 2 - s / 8) * (1 - 2 * (s / 8)) := by
    refine mul_pos (by linarith only [hs0]) ?_
    linarith only [hs1]
  rw [offGridStabilityConst, div_le_iff₀ hden]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hkey : (0 : ℝ) ≤ (d : ℝ) * s * (1 - s) :=
    mul_nonneg (mul_nonneg hdnn hs0.le) (by linarith only [hs1])
  nlinarith only [hkey, hdnn, hs0, hs1]

/-- The off-grid stability constant at the pin's lower index. -/
theorem offGridStabilityConst_pinQuarter_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    offGridStabilityConst d (s / 4) (s / 8) ≤ 192 * (d : ℝ) := by
  have hden : (0 : ℝ) < (s / 4 - s / 8) * (1 - 2 * (s / 8)) := by
    refine mul_pos (by linarith only [hs0]) ?_
    linarith only [hs1]
  rw [offGridStabilityConst, div_le_iff₀ hden]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hkey : (0 : ℝ) ≤ (d : ℝ) * s * (1 - s) :=
    mul_nonneg (mul_nonneg hdnn hs0.le) (by linarith only [hs1])
  nlinarith only [hkey, hdnn, hs0, hs1]

/-- **`G-small-1`, parametric form.**  On the frozen good event, at any
index `t ∈ (s/8, 1/2]` whose off-grid stability constant is below `192 d`, the
covering cube's `q = 2` ellipticity ratios at the `(n+3)` re-based family are
bounded by an absolute `K(d)` against `σ_{n+3}`.

The `s/6` instance is `BoundaryCoveringSlot.ae_coveringCubeCaps_le`; this
is the same two-step pattern with the index left free, so the Dirichlet-energy
indices `s/2` and `s/4` of the `r = s/2` pin are covered. -/
theorem ae_coveringCubeRatioCap_le (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
        ∀ t : ℝ, s / 8 < t → t ≤ 1 / 2 →
          offGridStabilityConst d t (s / 8) ≤ 192 * (d : ℝ) →
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ x : Vec d, x ∈ openCubeSet (originCube d m) →
                (fun y => x + y) '' openCubeSet (originCube d n) ⊆
                    ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                      openCubeSet (originCube d m) →
                ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                      Ch02.LambdaSq (originCube d (n + 2)) t (.finite 2)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega) ≤ K ∧
                  (Annealed.sigmaBar M (n + 3) : ℝ) *
                      (Ch02.lambdaSq (originCube d (n + 2)) t (.finite 2)
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre x m (n + 2)) z omega))⁻¹ ≤ K := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  have hkappa : 0 ≤ kappa := by positivity
  refine ⟨C, 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1), hCpos, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (kappa * (C * (1 / 2))) ^ 2 + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  intro M s hsrange hregime hsmall hs L m n hmL hnm z t hst ht hstab
  have hs1 : s ≤ 1 := hsrange.2
  have ht0 : (0 : ℝ) < t := by linarith only [hs, hst]
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) := (Annealed.sigmaBar M (n + 3)).2
  filter_upwards [hC M s hsrange hregime hsmall hs n z,
    ae_coveringCubeError_le_representative M L n m z hs hst ht]
    with omega hcap herr
  intro hmem x hx hgeom
  have hErep0 : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
    fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hErepCap := hcap hmem L (le_trans hnm hmL)
  have hE : Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) t .infinity
      (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
      kappa * (C * (1 / 2)) := by
    refine (herr x (by omega) hx hgeom).trans ?_
    have h1 : Real.sqrt (offGridStabilityConst d t (s / 8)) ≤
        Real.sqrt (192 * (d : ℝ)) := Real.sqrt_le_sqrt hstab
    have h2 : ((3 : ℝ) ^ (s / 8)) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith only [hs1] : s / 8 ≤ (1 : ℝ))
      rwa [Real.rpow_one] at h
    have h3 : (3 : ℝ) ^ (s / 8) *
        fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
      have hstepa : (3 : ℝ) ^ (s / 8) *
          fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) ≤
          3 * fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) :=
        mul_le_mul_of_nonneg_right h2 hErep0
      have hstepb : (3 : ℝ) *
          fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
            (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
        linarith only [hErepCap]
      linarith only [hstepa, hstepb]
    have h4 : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 8) *
        fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
    calc Real.sqrt (offGridStabilityConst d t (s / 8)) *
          ((3 : ℝ) ^ (s / 8) *
            fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega))
        ≤ Real.sqrt (192 * (d : ℝ)) * (3 * (C * (1 / 2))) :=
          mul_le_mul h1 h3 h4 (Real.sqrt_nonneg _)
      _ = kappa * (C * (1 / 2)) := by rw [hkappadef]; ring
  have hEnn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) t .infinity
      (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ht0
  have hratio := max_ellipticityRatio_le_homogenizationError (d := d)
    (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega) ht0
    (Annealed.sigmaBar M (n + 3)).2
  rw [show isotropicComparatorMatrix (d := d) (Annealed.sigmaBar M (n + 3)) =
    scalarMatrix (d := d) ((Annealed.sigmaBar M (n + 3) : ℝ)) from rfl] at hE hEnn
  have hmax := hratio.trans (two_mul_dim_mul_sq_add_one_le_of_le hEnn hE)
  exact ⟨le_trans (le_max_left _ _) hmax, le_trans (le_max_right _ _) hmax⟩

/-! ## 2. `G-small-2`: the positive-Besov index conversion, at no cost -/

/-- **`G-small-2`.**  The scale-normalized positive Besov seminorm is monotone
in the index: the pin's `[·]_{s/2}` is bounded by the frozen clause's `[·]_s`
with **no constant and no scale factor**.

This is CoarseGraining's own
`cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove` read on the
public alias; the plan budgeted a `3^{(s/2)(n+3)}`-type factor for this step,
which turns out to be unnecessary. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_le_of_exponent_le
    (Q : TriadicCube d) {u t : ℝ} (F : Vec d → Vec d) (hut : u ≤ t)
    (hF : ForceBesovRegularity Q t F) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q u F ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo Q t F :=
  cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove Q F hut
    hF.partialSeminorms_bddAbove

/-- The clause-(iv) regularity descends to any lower index — CoarseGraining's
`CubeVectorBesovHRegularity.of_exponent_le`, named for the pin. -/
theorem forceBesovRegularity_of_exponent_le {Q : TriadicCube d} {u t : ℝ}
    {F : Vec d → Vec d} (hF : ForceBesovRegularity Q t F) (hut : u ≤ t) :
    ForceBesovRegularity Q u F :=
  hF.of_exponent_le hut

/-! ## 3. `G-M2`: the covering cube's `ForceBesovRegularity` binders -/

/-- **`G-M2`, the force half.**  The transported, negated force
`y ↦ −g(y + c)` is `ForceBesovRegularity` on the covering cube at every index
`u ≤ s`, from the anchor's clause-(iv) data on `□_m`. -/
theorem forceBesovRegularity_coveringCube_neg_of_clause_iv [NeZero d]
    {n m : ℤ} {x : Vec d} {s u : ℝ} {g : Vec d → Vec d}
    (hnm : n + 2 ≤ m) (hs : 0 < s) (hs1 : s ≤ 1) (hu : u ≤ s)
    (hL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    ForceBesovRegularity (originCube d (n + 2)) u
      (fun y => -g (y + wellPlacedCentre x m (n + 2))) :=
  forceBesovRegularity_of_exponent_le
    (forceBesovRegularity_translated_neg (z := wellPlacedCentre x m (n + 2))
      (originCube d (n + 2)) hs hs1
      (memLp_two_coveringCube_of_clause_iv (x := x) hnm hL2)
      (memLp_two_gagliardo_coveringCube_of_clause_iv (x := x) hnm hW)) hu

/-- **`G-M2`, the datum half.**  The transported boundary gradient
`y ↦ ∇h(y + c)` is `ForceBesovRegularity` on the covering cube at every index
`u ≤ s`, from the anchor's clause-(iv) data on `□_m`. -/
theorem forceBesovRegularity_coveringCube_datumGrad_of_clause_iv [NeZero d]
    {n m : ℤ} {x : Vec d} {s u : ℝ} {H : Vec d → Vec d}
    (hnm : n + 2 ≤ m) (hs : 0 < s) (hs1 : s ≤ 1) (hu : u ≤ s)
    (hL2 : MemLp H 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 H) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    ForceBesovRegularity (originCube d (n + 2)) u
      (fun y => H (y + wellPlacedCentre x m (n + 2))) := by
  have hneg := forceBesovRegularity_coveringCube_neg_of_clause_iv
    (x := x) (g := fun y => -H y) (u := u) hnm hs hs1 hu hL2.neg
    (by
      have h : Gagliardo.gagliardoKernel s 2 (fun y => -H y) =
          -(Gagliardo.gagliardoKernel s 2 H) := by
        funext p
        simp only [Gagliardo.gagliardoKernel, Pi.neg_apply, smul_sub, smul_neg,
          neg_sub]
        abel
      rw [h]
      exact hW.neg)
  simpa only [neg_neg] using hneg

end

end Algsuperdiff.Section4.Provider.ExcessDecay
