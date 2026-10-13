/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.OscillationFamily

/-!
# OscillationGrid

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The truncated-window oscillation family at a scale-indexed grid of centres

The oscillation family of `OscillationFamily.lean` is stated at a centre of the
triadic lattice of the bottom scale.  A Campanato characterisation of Hölder
spaces instead reads a *scale-indexed* family of centres: at window scale `j`
the admissible centres are the points of the lattice of spacing `3 ^ (j-1)`, one
triadic scale finer than the window, which is what makes the family fine enough
to reach every point of the cube.

This module supplies the two dictionaries that connect the two readings and then
restates the family in the grid form.

* the truncated window `(z + □_j) ∩ □_m` is the intersection of the sup-ball of
  radius `3 ^ j / 2` about `z` with the sup-ball of radius `3 ^ m / 2` about the
  origin — the shape a Campanato telescope on a cube consumes;
* a point of the lattice of spacing `3 ^ (j-1)` lies on the lattice of spacing
  `3 ^ n` for every `n ≤ j - 1`, so a single grid centre serves every admissible
  bottom scale at or below its own.

## Main definitions

* `latticeDescent` — the index of a lattice point read at a coarser scale.

## Main results

* `truncatedWindow_eq_ball_inter_ball` — the window dictionary.
* `triadicLatticePoint_latticeDescent` — the lattice dictionary.
* `oscillationHolderBound_zeroDatum_grid` — the family at a grid centre, with the
  bottom scale free below the centre's own lattice scale.

## References

* [ABK], `ss.proof.regularity` Step 3 and display `e.oscillation.Holder.bound`.
-/

namespace Algsuperdiff.Section4.Provider.Holder

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Regularity
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The window dictionary -/

/-- The open cube of scale `k` about `x` is the sup-ball of radius `3 ^ k / 2`. -/
theorem openCubeAtScale_eq_ball [NeZero d] (x : Vec d) (k : ℤ) :
    openCubeAtScale x k = Metric.ball x ((3 : ℝ) ^ k / 2) := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ k / 2 := by
    have := zpow_pos (by norm_num : (0 : ℝ) < 3) k
    linarith only [this]
  have hrpow : Real.rpow (3 : ℝ) ((k : ℤ) : ℝ) = (3 : ℝ) ^ k :=
    Real.rpow_intCast (3 : ℝ) k
  ext y
  simp only [openCubeAtScale, Set.mem_ofPred_eq, Metric.mem_ball, hrpow]
  rw [dist_pi_lt_iff hr]
  exact ⟨fun h i => by simpa [Real.dist_eq] using h i,
    fun h i => by simpa [Real.dist_eq] using h i⟩

/-- The cube `□_m` is the sup-ball of radius `3 ^ m / 2` about the origin. -/
theorem openCubeSet_originCube_eq_ball_zero [NeZero d] (m : ℤ) :
    openCubeSet (originCube d m) = Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) := by
  rw [← openCubeAtScale_zero_eq_openCubeSet_originCube, openCubeAtScale_eq_ball]

/-- **The window dictionary.**  The truncated window `(z + □_k) ∩ □_m` is the
intersection of the sup-ball of radius `3 ^ k / 2` about `z` with the sup-ball of
radius `3 ^ m / 2` about the origin. -/
theorem truncatedWindow_eq_ball_inter_ball [NeZero d] (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k =
      Metric.ball x ((3 : ℝ) ^ k / 2) ∩ Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) := by
  rw [truncatedWindow_eq_inter_openCubeAtScale, openCubeAtScale_eq_ball,
    openCubeSet_originCube_eq_ball_zero]

/-! ## 2. The lattice dictionary -/

/-- **The index of a lattice point read at a coarser scale.**  A point of
`3 ^ n₀ ℤ^d` is a point of `3 ^ n ℤ^d` for every `n ≤ n₀`, with index scaled by
`3 ^ (n₀ - n)`. -/
def latticeDescent (n n₀ : ℤ) (v : Fin d → ℤ) : Fin d → ℤ :=
  fun i => (3 : ℤ) ^ (n₀ - n).toNat * v i

/-- The descended index names the same point. -/
theorem triadicLatticePoint_latticeDescent {n n₀ : ℤ} (hn : n ≤ n₀) (v : Fin d → ℤ) :
    triadicLatticePoint n (latticeDescent n n₀ v) = triadicLatticePoint n₀ v := by
  funext i
  have hcast : ((3 : ℝ)) ^ ((n₀ - n).toNat : ℕ) = (3 : ℝ) ^ (n₀ - n) := by
    rw [← zpow_natCast (3 : ℝ) ((n₀ - n).toNat), Int.toNat_of_nonneg (by omega)]
  have hsum : (3 : ℝ) ^ n * (3 : ℝ) ^ (n₀ - n) = (3 : ℝ) ^ n₀ := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  simp only [triadicLatticePoint, latticeDescent, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat]
  rw [← mul_assoc, hcast, hsum]

/-- The descended index is admissible for the ambient cube. -/
theorem latticeDescent_mem_latticeCubeSet {n n₀ m : ℤ} (hn : n ≤ n₀) {v : Fin d → ℤ}
    (hv : triadicLatticePoint n₀ v ∈ openCubeSet (originCube d m)) :
    latticeDescent n n₀ v ∈ latticeCubeSet d n m := by
  have h : triadicLatticePoint n (latticeDescent n n₀ v) ∈
      openCubeSet (originCube d m) := by
    rw [triadicLatticePoint_latticeDescent hn]
    exact hv
  exact h

/-! ## 3. The family at a grid centre -/

/-- **[ABK] `e.oscillation.Holder.bound` at a scale-indexed grid centre.**

The oscillation family of `oscillationHolderBound_zeroDatum`, read at a centre
`z` of the triadic lattice of spacing `3 ^ (j-1)` -- one scale finer than the
window of scale `j` it carries -- with the bottom scale `n` left free below that
lattice scale.  This is the reading a Campanato characterisation on the cube
consumes: the centres available at window scale `j` form a lattice fine enough
to approximate every point of the cube, and one and the same centre serves every
admissible bottom scale at or below `j - 1`.

The seed is the oscillation on the truncated window `(z + □_{m'}) ∩ □_m` at the
caller's own upper scale `m'`. -/
theorem oscillationHolderBound_zeroDatum_grid (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C Cosc Cdata : ℝ, 0 < gamma0 ∧ 0 < C ∧ 0 ≤ Cosc ∧ 0 ≤ Cdata ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Cutoff.CutoffSample d → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ L : ℤ, m ≤ L →
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d) (Kg : ℝ), 0 ≤ Kg →
                  IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u 0 g →
                  HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
                  ∀ n j m' : ℤ, n ≤ j - 1 → j ≤ m' → m' ≤ m →
                    X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                    ∀ z : Vec d, z ∈ openCubeSet (originCube d m) →
                      (∃ v : Fin d → ℤ, z = triadicLatticePoint (j - 1) v) →
                        (3 : ℝ) ^ (-j) *
                            normalizedL2On (truncatedWindow z m j)
                              (fun y => u.toFun y -
                                volumeAverage (truncatedWindow z m j) u.toFun) ≤
                          Cosc *
                              Real.rpow (3 : ℝ)
                                (1 / 2 * ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                            ((3 : ℝ) ^ (-m') *
                                normalizedL2On (truncatedWindow z m m')
                                  (fun y => u.toFun y -
                                    volumeAverage (truncatedWindow z m m') u.toFun) +
                              Cdata *
                                (((Annealed.sigmaBar M m : ℝ))⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)) := by
  classical
  obtain ⟨gamma0, C, Cosc, Cdata, hgamma0, hC, hCosc, hCdata, hmain⟩ :=
    oscillationHolderBound_zeroDatum d hd cstar hcstar
  refine ⟨gamma0, C, Cosc, Cdata, hgamma0, hC, hCosc, hCdata, ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  obtain ⟨X, hXmeas, hXtail, hXae⟩ := hmain M hcs hgamma alpha halpha0 halpha m
  refine ⟨X, hXmeas, hXtail, ?_⟩
  filter_upwards [hXae] with omega hom
  intro L hmL u g Kg hKg hsol hgHol n j m' hnj hjm' hm'm hgate z hz hlat
  obtain ⟨v, hzv⟩ := hlat
  subst hzv
  have hnm : n ≤ m := by omega
  have hv : latticeDescent n (j - 1) v ∈ latticeCubeSet d n m :=
    latticeDescent_mem_latticeCubeSet hnj hz
  have hbase := hom L n hmL hnm hgate (latticeDescent n (j - 1) v) hv u g Kg hKg
    hsol hgHol j m' (by omega) hjm' hm'm
  rwa [triadicLatticePoint_latticeDescent hnj] at hbase

end

end Algsuperdiff.Section4.Provider.Holder
