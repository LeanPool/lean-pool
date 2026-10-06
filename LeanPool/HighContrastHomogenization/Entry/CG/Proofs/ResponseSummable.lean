/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Definitions
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientField
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# High-contrast homogenization: Entry.CG.Proofs.ResponseSummable

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Summability of weighted CG responses

For a countable family of pairwise disjoint open pieces inside a locally elliptic container,
the relative-volume-weighted scalar coarse responses `ResponseJ` are summable. Each response
is nonnegative and bounded by the container's plain ellipticity bound `λ⁻¹ (Λ² |p|² + |q|²)`,
so the weighted series is dominated by the relative volumes of the pieces, which sum to at
most one. This is the summability input to the countable response subadditivity used by
`p.successful.short.bridge`.
-/

namespace HCPolySupport.HighContrast.CG

open MeasureTheory BigOperators

private theorem volume_piece_ne_top_of_subset_local {d : ℕ} {W V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)] (hsub : V ⊆ W) :
    volume V ≠ ⊤ := by
  have hW : volume W ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_ne_top (volumeMeasureOn W) Set.univ)
  exact MeasureTheory.measure_ne_top_of_subset hsub hW

private theorem pairwiseDisjoint_subtype_finset_local {d : ℕ} {ι : Type*} {s : Set ι}
    {U : ι → Set (Vec d)} (hdisj : s.PairwiseDisjoint U) (F : Finset s) :
    (F : Set s).PairwiseDisjoint fun i : s => U i.1 := by
  intro i _hi j _hj hij
  exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))

private theorem sum_volumeRatio_le_one_local {d : ℕ} {ι : Type*} {s : Set ι}
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
      exact volume_piece_ne_top_of_subset_local (W := W) (V := U i.1) (hsub i.1 i.2)
    have hmeasF :
        ∀ i ∈ F, MeasurableSet (U i.1) := by
      intro i _hi
      exact hmeas i.1 i.2
    have hsum_eq :
        volume.real (⋃ i ∈ F, U i.1) =
          ∑ i ∈ F, volume.real (U i.1) :=
      MeasureTheory.measureReal_biUnion_finset
        (pairwiseDisjoint_subtype_finset_local hdisj F) hmeasF hfinite
    have hUnionSub : (⋃ i ∈ F, U i.1) ⊆ W := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨_hiF, hxUi⟩
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

private theorem responseJ_le_plainUpperBound_of_isEllipticFieldOn_local {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q : Vec d) :
    ResponseJ U p q a ≤ lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q) := by
  unfold ResponseJ
  refine csSup_le (responseJValueSet_nonempty U p q a) ?_
  rintro m ⟨u, rfl⟩
  refine volumeAverage_le_of_le_on (measurableSet_of_isEllipticFieldOn hEll)
    (scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u) hvol ?_
  exact scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn hEll p q u

theorem responseJ_piece_bounds {d : ℕ} {ι : Type*} {s : Set ι}
    {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a)
    (p q : Vec d) {i : ι} (hi : i ∈ s) (hvol : (volume (U i)).toReal ≠ 0) :
    0 ≤ ResponseJ (U i) p q a ∧
      ResponseJ (U i) p q a ≤ lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q) := by
  have hfinite : volume (U i) ≠ ⊤ :=
    volume_piece_ne_top_of_subset_local (W := W) (V := U i) (hsub i hi)
  let : IsFiniteMeasure (volumeMeasureOn (U i)) :=
    ⟨by simpa [volumeMeasureOn] using (lt_top_iff_ne_top.mpr hfinite)⟩
  have hEllPiece : IsEllipticFieldOn lam Lam (U i) a :=
    hEll.mono (hopen i hi).measurableSet (hsub i hi)
  exact
    ⟨responseJ_nonneg (U i) p q a,
      responseJ_le_plainUpperBound_of_isEllipticFieldOn_local hEllPiece hvol p q⟩

private theorem summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn_aux {d : ℕ}
    {ι : Type*} {s : Set ι} {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a)
    (p q : Vec d) :
    Summable (fun i : s =>
      (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a) := by
  classical
  let C : ℝ := lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)
  refine summable_of_sum_le (c := max C 0) ?_ ?_
  · intro i
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (responseJ_nonneg (U i.1) p q a)
  · intro F
    have hmeas : ∀ i ∈ s, MeasurableSet (U i) := fun i hi => (hopen i hi).measurableSet
    have hweights := sum_volumeRatio_le_one_local hmeas hsub hdisj F
    have hCmax_nonneg : 0 ≤ max C 0 := le_max_right C 0
    have hterm_le :
        ∀ i ∈ F,
          (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a ≤
            (volume (U i)).toReal / (volume W).toReal * max C 0 := by
      intro i _hiF
      by_cases hvol : (volume (U i.1)).toReal = 0
      · simp [hvol]
      · have hbound :=
          (responseJ_piece_bounds hopen hsub hEll p q i.2 hvol).2
        exact mul_le_mul_of_nonneg_left (hbound.trans (le_max_left C 0))
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    calc
      ∑ i ∈ F,
          (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a
          ≤ ∑ i ∈ F,
              (volume (U i)).toReal / (volume W).toReal * max C 0 :=
            Finset.sum_le_sum hterm_le
      _ = (∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal) * max C 0 := by
            rw [Finset.sum_mul]
      _ ≤ 1 * max C 0 :=
            mul_le_mul_of_nonneg_right hweights hCmax_nonneg
      _ = max C 0 := one_mul _

theorem summable_volumeWeightedResponseJ {d : ℕ}
    {ι : Type*} {s : Set ι} (_hs : s.Countable) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a) (p q : Vec d) :
    Summable (fun i : s => (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a) := by
  exact summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn_aux
    hopen hsub hdisj hEll p q

end HCPolySupport.HighContrast.CG
