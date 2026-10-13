/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueCap
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SigmaBarIndex
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlotTransportChildCube

/-!
# ReindexSlot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The slot ingredients: the caps, the off-grid cap and the `σ` gap, at `n+3`

The frozen statement reads the **general** clause's good-event slot and its
flux-corrected error index at `n+3` rather than `n+2`, and carries the binder
`n + 3 ≤ m` rather than `n + 2 ≤ m`.  Everything the proved interior chain reads at
the slot therefore has to be re-instantiated one scale up.  This module
collects the four re-instantiations, all mechanical:

1. **the caps** — `GoodEventCaps.ae_errorRepresentative_le_of_mem_goodEventAt`
   and `ae_boundLambdasByEs` are `m`-generic, so the `(n+3)` slot is a plain
   re-instantiation, at *no* cost;
2. **the centre-child transport** — the chain's own cube is `□_{n+2}`, which is
   the **centre child** of `□_{n+3}`, i.e. its triadic descendant at depth `1`;
   `SlotTransportChildCube`'s descendant transport then reads the `(n+3)` caps
   on `□_{n+2}` at the explicit factor `3^{(s/8)·1} ≤ 3^{1/8} < 1.15`;
3. **the off-grid cap at one extra depth** — the proved root transport
   (`OffGridErrorFluxCorrected`) is generic in the root cube, so the anchor's
   child window `x+□_n` is capped against the `(n+3)` representative at the
   depth factor `3^{3·(s/8)} = 3^{3s/8} ≤ 3^{3/8} < 1.53` (the proved `(n+2)`
   value is `3^{2·(s/8)} = 3^{s/4}`, so the re-index costs exactly one more
   `3^{s/8}`);
4. **the `σ` gap-3 conversion** —
   `Annular.SigmaBarBudget.sigmaBar_ratio_le_four` is gap-generic (its
   hypothesis is `n - 2 ≤ m`, not `n - 2 = m`), so `σ_{n+3}^{-1} ≤ 4
   σ_n^{-1}` at the **same** constant `4` as the proved two-scale conversion;
   the induction-state binder is discharged internally exactly as in
   `SigmaBarIndex`.

## References

* ABK26, `e.good.set.giveth.v2`, `e.bound.Lambdas.by.Es.v2`;
  `e.mathcalE.stability.applied`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## 1. The centre child, and the two geometric consequences -/

/-- **The centre child.**  The centred cube of scale `k - 1` is the middle child of
the centred cube of scale `k`. -/
theorem centreChild_mem_childCubes (d : ℕ) (k : ℤ) :
    originCube d (k - 1) ∈ childCubes (originCube d k) := by
  refine Finset.mem_image.mpr ⟨fun _ => (1 : Fin 3), Finset.mem_univ _, ?_⟩
  have hindex : (fun i : Fin d => 3 * (originCube d k).index i + ((1 : Fin 3) : ℤ) - 1) =
      (originCube d (k - 1)).index := by
    funext i
    show 3 * (0 : ℤ) + ((1 : Fin 3) : ℤ) - 1 = 0
    norm_num
  exact congrArg (fun idx => (⟨k - 1, idx⟩ : TriadicCube d)) hindex

/-- The centre child is the depth-`1` triadic descendant. -/
theorem centreChild_mem_descendantsAtScale (d : ℕ) (k : ℤ) :
    originCube d (k - 1) ∈ descendantsAtScale (originCube d k) (k - 1) := by
  have hk : k - 1 ≤ (originCube d k).scale := by
    show k - 1 ≤ k
    omega
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d k) hk]
  have hdepth : Int.toNat ((originCube d k).scale - (k - 1)) = 1 := by
    show Int.toNat (k - (k - 1)) = 1
    omega
  rw [hdepth, descendantsAtDepth_one]
  exact centreChild_mem_childCubes d k

/-- `□_{n+2}` is the centre child of `□_{n+3}`: the `n+3` re-index's own
depth-`1` descent. -/
theorem originCube_add_two_mem_descendantsAtScale (d : ℕ) (n : ℤ) :
    originCube d (n + 2) ∈ descendantsAtScale (originCube d (n + 3)) (n + 2) := by
  have h := centreChild_mem_descendantsAtScale d (n + 3)
  have he : n + 3 - 1 = n + 2 := by ring
  rwa [he] at h

/-- The half-open realizations nest: `□_{n+2} ⊆ □_{n+3}`. -/
theorem cubeSet_originCube_add_two_subset (d : ℕ) (n : ℤ) :
    cubeSet (originCube d (n + 2)) ⊆ cubeSet (originCube d (n + 3)) := by
  have hk : n + 2 ≤ (originCube d (n + 3)).scale := by
    show n + 2 ≤ n + 3
    omega
  exact cubeSet_subset_of_mem_descendantsAtScale hk
    (originCube_add_two_mem_descendantsAtScale d n)

/-! ## 2. The caps at the slot `n+3` -/

/-- **The caps step at the `n+3` slot.**  `GoodEventCaps`'s `m`-generic caps read
at `m := n+3`: on the good event `𝒢(n+3, z; s/8, 1/2)` and for every `L ≥ n+3`,
the flux-corrected `(∞,2)` representative at index `n+3` is `≤ C/2`. -/
theorem ae_errorRepresentative_le_harmonicSlot_addThree (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 3 ≤ L →
                Support.fluxCorrectedErrorRepresentative M L (n + 3)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega) ≤ C * (1 / 2) := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  refine ⟨C, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs n z
  exact hC M hregime ⟨s / 8, by linarith only [hs]⟩
    (annularSlot_mem_Icc M.gamma s hsrange) (1 / 2) half_mem_Ioc hsmall (n + 3) z

/-- **The `q = 2` cap read on the chain's own cube.**

The `(n+3)` caps, transported to the centre child `□_{n+2}` by the proved
descendant transport: the cost is the explicit depth-`1` factor `3^{s/8}`, at
most `3^{1/8}`. -/
theorem ae_errorOn_centreChild_le_harmonicSlot (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 3 ≤ L → ∀ u : ℝ, s / 8 ≤ u →
                fluxCorrectedErrorOn M L (n + 3) (originCube d (n + 2)) u
                    (Cutoff.translateCutoffSample z omega) ≤
                  Real.rpow (3 : ℝ) (1 / 8 : ℝ) * (C * (1 / 2)) := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_harmonicSlot_addThree d
  refine ⟨C, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs n z
  have hs1 : s ≤ 1 := hsrange.2
  have hs8 : 0 < s / 8 := by linarith only [hs]
  have htr := (GoodEvents.measurePreserving_translateCutoffSample M
    z).quasiMeasurePreserving.ae
    (Support.ae_forall_fluxCorrectedError_eq_representative M (n + 3) ⟨s / 8, hs8⟩)
  filter_upwards [hC M s hsrange hregime hsmall hs n z, htr] with omega hcap heq
  intro hmem L hL u hu
  have hparent : fluxCorrectedErrorOn M L (n + 3) (originCube d (n + 3)) (s / 8)
      (Cutoff.translateCutoffSample z omega) ≤ C * (1 / 2) := by
    have h1 : Support.fluxCorrectedError M L (n + 3) (s / 8)
        (Cutoff.translateCutoffSample z omega) =
        Support.fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, hs8⟩
          (Cutoff.translateCutoffSample z omega) := heq ⟨L, hL⟩
    rw [fluxCorrectedErrorOn_originCube, h1]
    exact hcap hmem L hL
  have hdesc := homogenizationErrorOnCube_infinity_two_descendant_index_le
    (Q := originCube d (n + 3)) (R := originCube d (n + 2)) (k := n + 2)
    (Support.fluxCorrectedCoeffFamily M L (n + 3) (originCube d (n + 3))
      (Cutoff.translateCutoffSample z omega))
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hs8 hu
    (originCube_add_two_mem_descendantsAtScale d n)
  have hdepth : Int.toNat ((originCube d (n + 3)).scale - (n + 2)) = 1 := by
    show Int.toNat (n + 3 - (n + 2)) = 1
    omega
  rw [hdepth] at hdesc
  have hfac : Real.rpow (3 : ℝ) (s / 8 * ((1 : ℕ) : ℝ)) ≤ Real.rpow (3 : ℝ) (1 / 8 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    push_cast
    linarith only [hs1]
  have hfac0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s / 8 * ((1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hpar0 : (0 : ℝ) ≤ C * (1 / 2) := by positivity
  refine hdesc.trans (le_trans (mul_le_mul_of_nonneg_left hparent hfac0) ?_)
  exact mul_le_mul_of_nonneg_right hfac hpar0

/-- **`e.bound.Lambdas.by.Es.v2` at the `n+3` slot, read on the chain's own
cube.**

On the good event `𝒢(n+3, z; s/8, 1/2)`, for every `L ≥ n+3` and every index
`u ≥ s/8`, the coarse-grained ellipticity ratios of the `(n+3)` flux-corrected
field on `□_{n+2}`, against the comparator `σ_{n+3}`, are bounded by the
constant `K = 2d((3^{1/8} C/2)² + 1)`. -/
theorem ae_boundLambdasByEs_centreChild (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 3 ≤ L → ∀ u : ℝ, s / 8 ≤ u →
                fluxCorrectedEllipticityRatioMaxOn M L (n + 3) (originCube d (n + 2)) u
                    (Cutoff.translateCutoffSample z omega) ≤ K := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorOn_centreChild_le_harmonicSlot d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨C, 2 * (d : ℝ) * ((Real.rpow (3 : ℝ) (1 / 8 : ℝ) * (C * (1 / 2))) ^ 2 + 1),
    hCpos, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (Real.rpow (3 : ℝ) (1 / 8 : ℝ) * (C * (1 / 2))) ^ 2 + 1 := by
      positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  intro M s hsrange hregime hsmall hs n z
  have hs8 : 0 < s / 8 := by linarith only [hs]
  filter_upwards [hC M s hsrange hregime hsmall hs n z] with omega hcap
  intro hmem L hL u hu
  have hu0 : 0 < u := by linarith only [hs8, hu]
  have hratio := max_ellipticityRatio_le_homogenizationError (d := d) (originCube d (n + 2))
    (Support.fluxCorrectedCoeffFamily M L (n + 3) (originCube d (n + 3))
      (Cutoff.translateCutoffSample z omega)) hu0 (Annealed.sigmaBar M (n + 3)).2
  have hnonneg : 0 ≤ fluxCorrectedErrorOn M L (n + 3) (originCube d (n + 2)) u
      (Cutoff.translateCutoffSample z omega) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (Support.fluxCorrectedCoeffFamily M L (n + 3) (originCube d (n + 3))
        (Cutoff.translateCutoffSample z omega))
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hu0
  exact le_trans hratio
    (two_mul_dim_mul_sq_add_one_le_of_le hnonneg (hcap hmem L hL u hu))

/-! ## 3. The off-grid cap at one extra depth -/

/-- The scale gap of the `(n+3)`/`n` parent/child pair, as a natural number. -/
private theorem originCube_scale_gap_three (n : ℤ) :
    ((originCube d (n + 3)).scale - (originCube d n).scale).toNat = 3 := by
  have h : (originCube d (n + 3)).scale - (originCube d n).scale = 3 := by
    simp only [originCube]
    ring
  rw [h]
  rfl

/-- **The off-grid child error against the `(n+3)` representative.**

The proved root transport is generic in the root cube, so the anchor's own
child window `x+□_n`, read in the parent's `z`-frame at the translate `w = x −
z`, is bounded by the `n+3` slot's own representative
`fluxCorrectedErrorRepresentative M L (n+3) ⟨s/8⟩`, with the depth factor
`3^{3s/8}` (at most `3^{3/8} < 1.53`) — exactly one more `3^{s/8}` than the
proved `(n+2)` value `3^{s/4}`. -/
theorem ae_offGridChildError_le_representative_harmonicSlot_addThree [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        offGridErrorFunctional (x - z) (originCube d n) (s / 6)
            (Support.fluxCorrectedRegField M L (n + 3) (originCube d (n + 3))
              (Cutoff.translateCutoffSample z omega)).toFun
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (3 * (s / 8)) *
              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  have hbase := (GoodEvents.measurePreserving_translateCutoffSample M
      z).quasiMeasurePreserving.ae
    (ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot
      M L (n + 3) (originCube d (n + 3))
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))
      (by linarith only [hs] : (0 : ℝ) < s / 8)
      (by linarith only [hs] : s / 8 < s / 6)
      (by linarith only [hs1] : s / 6 ≤ 1 / 2))
  filter_upwards [hbase] with omega hall
  intro x m hgeom
  have hcontain : translateSet (x - z) (cubeSet (originCube d n)) ⊆
      cubeSet (originCube d (n + 3)) :=
    fun p hp => cubeSet_originCube_add_two_subset d n
      (translateSet_cubeSet_subset_of_anchorGeometry hgeom hp)
  have hstep := hall (x - z) (originCube d n) (originCube d (n + 3)) hcontain
  rw [originCube_scale_gap_three (d := d) n,
    fluxCorrectedErrorFunctionalAtRoot_eq_representative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩] at hstep
  have hexp : (s / 8 * ((3 : ℕ) : ℝ)) = 3 * (s / 8) := by
    push_cast
    ring
  rwa [hexp] at hstep

/-! ## 4. The `σ` gap-3 conversion, binder-free -/

/-- The regime bridge. -/
private theorem regime_bridge {C0 gam c : ℝ} (h : gam ≤ (C0 ^ (10 : ℕ))⁻¹ * c) :
    gam ≤ (C0⁻¹) ^ (10 : ℕ) * c := by
  rwa [inv_pow]

/-- **`σ` is almost increasing across a three-scale gap, at the same `4`.**
`Annular.SigmaBarBudget.sigmaBar_ratio_le_four` asks only `n - 2 ≤ m`, so the
gap is free: `σ_{n+3}^{-1} ≤ 4 σ_n^{-1}`. -/
theorem inv_sigmaBar_add_three_le_of_inductionState (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n + 3 ≤ m0) :
    ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ≤ 4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  have hidx : (n + 2 : ℤ) - 2 = n := by ring
  have hbase := Annular.sigmaBar_ratio_le_four M hS (m := n + 3) (n := n + 2)
    (by omega) hn
  rw [hidx] at hbase
  have hB : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hstep := mul_le_mul_of_nonneg_right hbase (inv_nonneg.2 hB.le)
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hB), mul_one] at hstep
  exact hstep

/-- **The force leg's `σ` index conversion, binder-free**:
`σ_{n+3}^{-1} ≤ 4 σ_n^{-1}` inside the anchor's own regime. -/
theorem exists_inv_sigmaBar_add_three_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ n : ℤ, ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ ≤
          4 * ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  obtain ⟨C0, hC0, hC⟩ := GoodEvents.exists_allScalesInductionState d
  refine ⟨C0 ^ (10 : ℕ), by positivity, ?_⟩
  intro M hreg n
  obtain ⟨E, -, hall⟩ := hC M (regime_bridge hreg)
  exact inv_sigmaBar_add_three_le_of_inductionState M (E := E) (hall (n + 3)) le_rfl

end

end Algsuperdiff.Section4.Provider.ExcessDecay
