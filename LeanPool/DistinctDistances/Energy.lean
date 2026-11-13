/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import LeanPool.DistinctDistances.PlanarGeneralPosition
public import LeanPool.DistinctDistances.Foundation

/-!
# Distance energy and the fixed-linear-distance target.

`NumDistances p` is the count of distinct pairwise distances over the
image-finset `Config.toFinset p`, via the canonical FCM
`EuclideanGeometry.distinctDistances`.

Ordered-pair distance multiplicities (`OrderedMultiplicity`) and the
sum-of-squares `DistanceEnergy` follow the ordered formulation of the prose
proof. `FixedLinearDistanceEnergyGapStatement` is the active Problem 98 target:
for each fixed `A > 0`, configurations with at most `A n` distances have an
energy-density gap below the ordered Cauchy threshold `1 / A`.

`GeneralPositionEqualDistanceEnergySavingStatement` retains the former
universal `o(n³)` target as a named stronger statement. Both propositions
quantify over indexed configurations using the FCM `InGeneralPosition`
predicate transported through `Config.toFinset` (do not use the pre-refactor
`Esgk.Point` or `Esgk.GeneralPosition` names).
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

/-- Range of pairwise distances over ordered pairs with `i ≠ j`. -/
noncomputable def OrderedDistanceValues {n : ℕ} (p : Config n) : Finset ℝ :=
  Finset.image (fun ij : Fin n × Fin n ↦ dist (p ij.1) (p ij.2))
    ((Finset.univ.product Finset.univ).filter (fun ij : Fin n × Fin n ↦ ij.1 ≠ ij.2))

/-- Ordered multiplicity of distance value `r` in configuration `p` (counts `(i,j)` with `i ≠ j`).
-/
noncomputable def OrderedMultiplicity {n : ℕ} (p : Config n) (r : ℝ) : ℕ :=
  (((Finset.univ.product Finset.univ).filter
    (fun ij : Fin n × Fin n ↦ ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r))).card

/-- Distance energy: `Σ_r m_r^2` over ordered-pair multiplicities. Excludes the diagonal `r = 0` via
the `i ≠ j` predicate inside `OrderedDistanceValues` / `OrderedMultiplicity`. -/
noncomputable def DistanceEnergy {n : ℕ} (p : Config n) : ℕ :=
  ∑ r ∈ OrderedDistanceValues p, (OrderedMultiplicity p r)^2

/-- Indexed distinct-distance count via the image-finset. Equals the canonical FCM
`EuclideanGeometry.distinctDistances` applied to `Config.toFinset p`; inherits diagonal exclusion
from `Finset.offDiag.image`. -/
noncomputable def NumDistances {n : ℕ} (p : Config n) : ℕ := distinctDistances (Config.toFinset p)

/-- Ordered-pair distance-value count: matches the Cauchy multiplicity proof. Equals `NumDistances
p` under `Function.Injective p`; can be strictly larger when `p` has collisions (the dist=0 bucket
appears here but is absent from `NumDistances`). -/
noncomputable def NumDistancesOrdered {n : ℕ} (p : Config n) : ℕ := (OrderedDistanceValues p).card

/-- The image-finset distance count is bounded above by the ordered-pair distance count: every
distance value arising from a distinct-image pair also arises from an ordered i≠j pair. -/
theorem numDistances_le_numDistancesOrdered {n : ℕ} (p : Config n) :
    NumDistances p ≤ NumDistancesOrdered p := by
  unfold NumDistances NumDistancesOrdered OrderedDistanceValues distinctDistances Config.toFinset
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨pair, hpair_mem, hpair_dist⟩ := hr
  rw [Finset.mem_offDiag] at hpair_mem
  obtain ⟨hx_mem, hy_mem, hxy_ne⟩ := hpair_mem
  rw [Finset.mem_image] at hx_mem hy_mem
  obtain ⟨i, _, hpi⟩ := hx_mem
  obtain ⟨j, _, hpj⟩ := hy_mem
  rw [Finset.mem_image]
  refine ⟨(i, j), ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    intro (hij : i = j)
    apply hxy_ne
    rw [← hpi, ← hpj, hij]
  · simp only
    rw [hpi, hpj]
    exact hpair_dist


/-- Under injectivity the two counts agree: `i ≠ j ↔ p i ≠ p j` makes the ordered-pair distance set
and the image-finset offDiag distance set equal. -/
theorem numDistances_eq_numDistancesOrdered_of_injective {n : ℕ} {p : Config n}
    (hp : Function.Injective p) :
    NumDistances p = NumDistancesOrdered p := by
  unfold NumDistances NumDistancesOrdered OrderedDistanceValues distinctDistances Config.toFinset
  congr 1
  apply Finset.Subset.antisymm
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨pair, hpair_mem, hpair_dist⟩ := hr
    rw [Finset.mem_offDiag] at hpair_mem
    obtain ⟨hx_mem, hy_mem, hxy_ne⟩ := hpair_mem
    rw [Finset.mem_image] at hx_mem hy_mem
    obtain ⟨i, _, hpi⟩ := hx_mem
    obtain ⟨j, _, hpj⟩ := hy_mem
    rw [Finset.mem_image]
    refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      intro (hij : i = j)
      apply hxy_ne
      rw [← hpi, ← hpj, hij]
    · simp only
      rw [hpi, hpj]
      exact hpair_dist
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨ij, hij_mem, hij_dist⟩ := hr
    rw [Finset.mem_filter] at hij_mem
    obtain ⟨_, hij_ne⟩ := hij_mem
    rw [Finset.mem_image]
    refine ⟨(p ij.1, p ij.2), ?_, hij_dist⟩
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mem_image]; exact ⟨ij.1, Finset.mem_univ _, rfl⟩
    · rw [Finset.mem_image]; exact ⟨ij.2, Finset.mem_univ _, rfl⟩
    · intro h; exact hij_ne (hp h)


/-- Active counterexample-local target for Problem 98, in ordered normalization.
For every fixed linear distinct-distance constant `A > 0`, there is a fixed
energy gap `δ > 0` below the ordered Cauchy threshold `1 / A` on all sufficiently
large general-position configurations satisfying `NumDistances p ≤ A n`.

For unordered distance energy this says
`E(P) ≤ (1 / (4A) - δ / 4) n³`, because injective configurations satisfy
`DistanceEnergy p = 4 E(P)`. This is sufficient for eventual exclusion of
`D(P) ≤ A n`; see
`fixedLinearDistanceEnergyGap_implies_eventually_numDistances_gt_linear`.
The converse is vacuous, so
`fixedLinearDistanceEnergyGap_iff_superlinearDistances` identifies this as a
reformulation of the fixed-`A` conclusion rather than a reduction. -/
def FixedLinearDistanceEnergyGapStatement : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          (NumDistances p : ℝ) ≤ A * (n : ℝ) →
          (DistanceEnergy p : ℝ) ≤ (A⁻¹ - δ) * (n : ℝ) ^ 3

/-- Direct fixed-`A` formulation of the Problem 98 target: every positive linear
distance bound is eventually beaten by every general-position configuration. -/
def GeneralPositionDistinctDistancesSuperlinearStatement : Prop :=
  ∀ A : ℝ, 0 < A →
    ∀ᶠ n in Filter.atTop,
      ∀ p : Config n,
        Function.Injective p →
        InGeneralPosition (Config.toFinset p) →
        A * (n : ℝ) < (NumDistances p : ℝ)

/-- Former universal target: every indexed general-position configuration has
`o(n³)` ordered-pair distance energy. This remains a useful stronger statement,
but the active Problem 98 target is the counterexample-local
`FixedLinearDistanceEnergyGapStatement`. -/
def GeneralPositionEqualDistanceEnergySavingStatement : Prop := ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in Filter.atTop,
      ∀ p : Config n,
        Function.Injective p →
        InGeneralPosition (Config.toFinset p) →
          (DistanceEnergy p : ℝ) ≤ ε * (n : ℝ)^3

end Esgk
