/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Iteration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Numerics

/-!
# TranslatedCrossing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The crossing event at an arbitrary base site

The maximal-diameter bound `measure_crossingEvent₂_le_exp` (ABK26,
`l.percolation.bound.general`, conclusion (3), `e.diameter.bound`) is stated for
the *origin-centred* annulus `□_{k+1} \ □_k`.  The consumers of that bound in
Section 3.3 need it at an arbitrary base site `w ∈ ℤ^d`.

Nothing new is proved here: the abstract percolation layer is covariant under
lattice translations, because `latDist` and `cubeAt` are.  This module makes
the covariance explicit by *reindexing* the family of bad events,

`shiftFamily B w l y = B l (y + w)`.

The two hypotheses of `measure_crossingEvent₂_le_exp` — finite-range
independence of the `siteSigma` σ-algebras and the uniform tail bound on the
bad events — are transported to the reindexed family with no change of
constants, since
`siteSigma (shiftFamily B w) S l = siteSigma B ((· + w) '' S) l` and
`latDist (u + w) (v + w) = latDist u v`.

## Main definitions

* `Algsuperdiff.Section3.Provider.Percolation.shiftFamily`: the reindexed
  family of bad events.

## Main results

* `siteSigma_shiftFamily`: the reindexing identity for the localised
  σ-algebras.
* `indep_siteSigma_shiftFamily`: finite-range independence transports to the
  reindexed family with the same range.
* `measure_shiftFamily_le`: a uniform tail bound transports to the reindexed
  family verbatim.

## References

* ABK26, `l.percolation.bound.general`, `e.diameter.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {Ω : Type*}

/-! ### Translation invariance of the lattice geometry -/

/-- The sup distance is invariant under a common lattice translation. -/
theorem latDist_add_right (x y w : Fin d → ℤ) :
    latDist (x + w) (y + w) = latDist x y := by
  refine Finset.sup_congr rfl fun j _ => ?_
  have h : (x + w) j - (y + w) j = x j - y j := by
    simp only [Pi.add_apply]
    ring
  rw [h]

/-- The sup distance is invariant under a common lattice translation, in
subtracted form. -/
theorem latDist_sub_right (x y w : Fin d → ℤ) :
    latDist (x - w) (y - w) = latDist x y := by
  refine Finset.sup_congr rfl fun j _ => ?_
  have h : (x - w) j - (y - w) j = x j - y j := by
    simp only [Pi.sub_apply]
    ring
  rw [h]

/-- The sup distance from the origin to a difference. -/
theorem latDist_zero_sub (z w : Fin d → ℤ) :
    latDist (0 : Fin d → ℤ) (z - w) = latDist w z := by
  refine Finset.sup_congr rfl fun j _ => ?_
  have h : (0 : Fin d → ℤ) j - (z - w) j = -(z j - w j) := by
    simp only [Pi.zero_apply, Pi.sub_apply]
    ring
  have h' : w j - z j = -(z j - w j) := by ring
  rw [h, h']

/-- Recentring a triadic cube at the origin. -/
theorem mem_cubeAt_sub_zero {k : ℕ} {z w : Fin d → ℤ} :
    z - w ∈ cubeAt k (0 : Fin d → ℤ) ↔ z ∈ cubeAt k w := by
  rw [mem_cubeAt_iff, mem_cubeAt_iff, latDist_zero_sub]

/-! ### The reindexed family -/

/-- The family of bad events reindexed by the lattice translation `y ↦ y + w`. -/
def shiftFamily (B : ℕ → (Fin d → ℤ) → Set Ω) (w : Fin d → ℤ) :
    ℕ → (Fin d → ℤ) → Set Ω :=
  fun l y => B l (y + w)


/-! ### Transport of the two hypotheses -/

/-- The localised σ-algebras of the reindexed family are the localised
σ-algebras of the original family at the translated set of sites. -/
theorem siteSigma_shiftFamily (B : ℕ → (Fin d → ℤ) → Set Ω) (w : Fin d → ℤ)
    (S : Set (Fin d → ℤ)) (k : ℕ) :
    siteSigma (shiftFamily B w) S k = siteSigma B ((fun u => u + w) '' S) k := by
  unfold siteSigma
  congr 1
  ext A
  constructor
  · rintro ⟨L, hL, y, hy, rfl⟩
    exact ⟨L, hL, y + w, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨L, hL, u, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨L, hL, y, hy, rfl⟩

/-- Finite-range independence transports to the reindexed family with the same
range. -/
theorem indep_siteSigma_shiftFamily [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℕ → (Fin d → ℤ) → Set Ω}
    (hindep : ∀ (l : ℕ) (S S' : Set (Fin d → ℤ)),
      (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
        Indep (siteSigma B S l) (siteSigma B S' l) μ)
    (w : Fin d → ℤ) (l : ℕ) (S S' : Set (Fin d → ℤ))
    (hsep : ∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) :
    Indep (siteSigma (shiftFamily B w) S l) (siteSigma (shiftFamily B w) S' l) μ := by
  rw [siteSigma_shiftFamily, siteSigma_shiftFamily]
  refine hindep l _ _ ?_
  rintro u ⟨p, hp, rfl⟩ v ⟨q, hq, rfl⟩
  rw [latDist_add_right]
  exact hsep p hp q hq

/-- A uniform tail bound transports to the reindexed family verbatim. -/
theorem measure_shiftFamily_le [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℕ → (Fin d → ℤ) → Set Ω} {c : ℕ → ENNReal}
    (hB : ∀ (L : ℕ) (y : Fin d → ℤ), μ (B L y) ≤ c L)
    (w : Fin d → ℤ) (L : ℕ) (y : Fin d → ℤ) :
    μ (shiftFamily B w L y) ≤ c L :=
  hB L (y + w)

/-! ### The diameter bound at an arbitrary base site -/


end Algsuperdiff.Section3.Provider.Percolation
