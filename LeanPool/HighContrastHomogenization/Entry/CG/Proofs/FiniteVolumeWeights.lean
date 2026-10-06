/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientField
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Definitions
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
public import LeanPool.HighContrastHomogenization.Support.PDE.Harmonic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# High-contrast homogenization: Entry.CG.Proofs.FiniteVolumeWeights

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite Volume Weights

For a finite-measure set `W` and measurable subsets `U i ⊆ W`, the relative volumes
`volume (U i) / volume W` have finite partial sums at most one and form a summable family, and
every finite disjoint subfamily splits `volume W` into the volumes of its pieces together with
the volume of the uncovered remainder, normalized to total mass one. These are the volume
weights that the countable subadditivity of the response quadratic is summed against, in the
proofs of `p.response.transfer` and `p.successful.short.bridge`.
-/

section
/-!
## Volume weights for CG response sums

Self-contained CG/Mathlib support for the relative-volume weights appearing in the
countable response summability statement.
-/

namespace HCPolySupport.HighContrast.CG

open MeasureTheory BigOperators

theorem volume_piece_ne_top_of_subset {d : ℕ} {W V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)] (hsub : V ⊆ W) :
    volume V ≠ ⊤ := by
  have hW : volume W ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_ne_top (volumeMeasureOn W) Set.univ)
  exact MeasureTheory.measure_ne_top_of_subset hsub hW

private theorem pairwiseDisjoint_subtype_finset {d : ℕ} {ι : Type*} {s : Set ι}
    {U : ι → Set (Vec d)} (hdisj : s.PairwiseDisjoint U) (F : Finset s) :
    (F : Set s).PairwiseDisjoint fun i : s => U i.1 := by
  intro i _hi j _hj hij
  exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))

theorem sum_volumeRatio_le_one {d : ℕ} {ι : Type*} {s : Set ι}
    {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hmeas : ∀ i ∈ s, MeasurableSet (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (F : Finset s) :
    ∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal ≤ 1 := by
  classical
  have hWfin : volume W ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_ne_top (volumeMeasureOn W) Set.univ)
  by_cases hWzero : (volume W).toReal = 0
  · have hWnull : volume W = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (volume W)).mp hWzero with h | h
      · exact h
      · exact (hWfin h).elim
    have hterm_zero :
        ∀ i : s, (volume (U i)).toReal / (volume W).toReal = 0 := by
      intro i
      have hUi_null : volume (U i.1) = 0 :=
        MeasureTheory.measure_mono_null (hsub i.1 i.2) hWnull
      simp [hWzero, hUi_null]
    simp [hterm_zero]
  · have hWpos : 0 < (volume W).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hWzero)
    have hfinite :
        ∀ i ∈ F, volume (U i.1) ≠ ⊤ := by
      intro i _hi
      exact volume_piece_ne_top_of_subset (W := W) (V := U i.1) (hsub i.1 i.2)
    have hmeasF :
        ∀ i ∈ F, MeasurableSet (U i.1) := by
      intro i _hi
      exact hmeas i.1 i.2
    have hsum_eq :
        volume.real (⋃ i ∈ F, U i.1) =
          ∑ i ∈ F, volume.real (U i.1) :=
      MeasureTheory.measureReal_biUnion_finset
        (pairwiseDisjoint_subtype_finset hdisj F) hmeasF hfinite
    have hUnionSub : (⋃ i ∈ F, U i.1) ⊆ W := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hiF, hxUi⟩
      exact hsub i.1 i.2 hxUi
    have hsum_le :
        ∑ i ∈ F, (volume (U i.1)).toReal ≤ (volume W).toReal := by
      calc
        ∑ i ∈ F, (volume (U i.1)).toReal
            = volume.real (⋃ i ∈ F, U i.1) := by
              simpa [Measure.real] using hsum_eq.symm
        _ ≤ volume.real W :=
              MeasureTheory.measureReal_mono hUnionSub hWfin
        _ = (volume W).toReal := rfl
    rw [← Finset.sum_div]
    exact (div_le_iff₀ hWpos).mpr (by simpa using hsum_le)

theorem summable_volumeRatio {d : ℕ} {ι : Type*} {s : Set ι}
    {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hmeas : ∀ i ∈ s, MeasurableSet (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) :
    Summable (fun i : s => (volume (U i)).toReal / (volume W).toReal) := by
  refine summable_of_sum_le (c := 1) ?_ ?_
  · intro i
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · intro F
    simpa using sum_volumeRatio_le_one hmeas hsub hdisj F

end HCPolySupport.HighContrast.CG
end

section
/-!
## Finite splitting for CG response defects

Self-contained CG/Mathlib support for finite volume and integral decompositions.  The
same finite-volume facts are proved again in the response-weight file; this module repeats the
short measure-theory layer
instead of importing any `HCPoly.Entry.*` module.
-/

namespace HCPolySupport.HighContrast.CG

open MeasureTheory
open scoped BigOperators

private theorem measurable_iUnion_finset {d : ℕ} {ι : Type*}
    (F : Finset ι) {U : ι → Set (Vec d)}
    (hmeas : ∀ i ∈ F, MeasurableSet (U i)) :
    MeasurableSet (⋃ i ∈ F, U i) := by
  exact Finset.measurableSet_biUnion F hmeas

private theorem iUnion_finset_subset {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    (hsub : ∀ i ∈ F, U i ⊆ W) :
    (⋃ i ∈ F, U i) ⊆ W := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hiF, hxU⟩
  exact hsub i hiF hxU

theorem volume_eq_sum_add_remainder {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hmeas : ∀ i ∈ F, MeasurableSet (U i))
    (hsub : ∀ i ∈ F, U i ⊆ W) (hdisj : (F : Set ι).PairwiseDisjoint U) :
    (volume W).toReal = (∑ i ∈ F, (volume (U i)).toReal) +
      (volume (W \ ⋃ i ∈ F, U i)).toReal := by
  classical
  let S : Set (Vec d) := ⋃ i ∈ F, U i
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact measurable_iUnion_finset F hmeas
  have hSsub : S ⊆ W := by
    dsimp [S]
    exact iUnion_finset_subset F hsub
  have hWfin : volume W ≠ ⊤ :=
    volume_piece_ne_top_of_subset (W := W) (V := W) (fun _ hx => hx)
  have hSfin : volume S ≠ ⊤ :=
    volume_piece_ne_top_of_subset (W := W) (V := S) hSsub
  have hpieces_fin : ∀ i ∈ F, volume (U i) ≠ ⊤ := by
    intro i hi
    exact volume_piece_ne_top_of_subset (W := W) (V := U i) (hsub i hi)
  have hsum :
      volume.real S = ∑ i ∈ F, volume.real (U i) := by
    dsimp [S]
    exact MeasureTheory.measureReal_biUnion_finset hdisj hmeas hpieces_fin
  have hsplit :
      volume.real S + volume.real (W \ S) = volume.real W := by
    have hUnion : S ∪ W = W := Set.union_eq_self_of_subset_left hSsub
    simpa [S, hUnion] using
      MeasureTheory.measureReal_add_sdiff (μ := volume) hSmeas hSfin hWfin
  calc
    (volume W).toReal = volume.real S + volume.real (W \ S) := by
      simpa [Measure.real] using hsplit.symm
    _ = (∑ i ∈ F, (volume (U i)).toReal) +
        (volume (W \ ⋃ i ∈ F, U i)).toReal := by
      rw [hsum]
      rfl

theorem sum_volumeRatio_add_remainder_eq_one {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWvol : (volume W).toReal ≠ 0)
    (hmeas : ∀ i ∈ F, MeasurableSet (U i)) (hsub : ∀ i ∈ F, U i ⊆ W)
    (hdisj : (F : Set ι).PairwiseDisjoint U) :
    (∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal) +
      (volume (W \ ⋃ i ∈ F, U i)).toReal / (volume W).toReal = 1 := by
  classical
  have hsplit :=
    volume_eq_sum_add_remainder (F := F) (W := W) (U := U) hmeas hsub hdisj
  rw [← Finset.sum_div]
  field_simp [hWvol]
  linarith only [hsplit]

end HCPolySupport.HighContrast.CG
end
