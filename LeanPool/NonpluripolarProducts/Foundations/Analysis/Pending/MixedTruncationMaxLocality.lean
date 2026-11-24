/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxObstacle

/-!
# Plurifine locality of the maximum for mixed truncation limits

For PSH tuples `u` and `w` on `Ω`, the mixed non-pluripolar measure of the
slotwise maximum `max (u i) (w i)` agrees with that of `u` on the set where every
obstacle lies strictly below its slot, `{z ∈ Ω | ∀ i, w i z < u i z}`.

The set is only plurifine open. It is exhausted by the pieces
`{∀ i, w i < q i} ∩ {∀ i, q i < u i}` for rational vectors `q`: the first factor
is ordinary open by upper semicontinuity, and on it both tuples, truncated at a
level below every `q i`, become `max (u i) (q i)` after a further maximum with the
constant obstacle `q i`. Bounded max-obstacle locality then applies twice.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.MixedNonPluripolar
open MixedMongeAmpere

variable {n : ℕ}

theorem max_toReal_coe {a : EReal} (ha : a ≠ ⊤) (hb : a ≠ ⊥) (c : ℝ) :
    max a.toReal c = (max a (c : EReal)).toReal := by
  lift a to ℝ using ⟨ha, hb⟩
  rw [EReal.toReal_coe]
  rcases le_total a c with h | h
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h), EReal.toReal_coe]
  · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h), EReal.toReal_coe]

theorem max_max_max_eq {a b c d : EReal} (hb : b ≤ d) :
    max (max (max a b) c) d = max (max a d) c :=
  le_antisymm
    (max_le (max_le (max_le ((le_max_left a d).trans (le_max_left _ c))
      (hb.trans ((le_max_right a d).trans (le_max_left _ c))))
      (le_max_right _ c)) ((le_max_right a d).trans (le_max_left _ c)))
    (max_le (max_le ((le_max_left a b).trans ((le_max_left _ c).trans (le_max_left _ d)))
      (le_max_right _ d)) ((le_max_right (max a b) c).trans (le_max_left _ d)))

theorem max_max_eq {a c d : EReal} (hc : c ≤ d) : max (max a c) d = max (max a d) c :=
  le_antisymm
    (max_le (max_le ((le_max_left a d).trans (le_max_left _ c)) (le_max_right _ c))
      ((le_max_right a d).trans (le_max_left _ c)))
    (max_le (max_le ((le_max_left a c).trans (le_max_left _ d)) (le_max_right _ d))
      (hc.trans (le_max_right _ d)))

/-- On an open set where every obstacle lies below a real constant `q i`, the
maximum does not change the measure where every slot exceeds its constant. -/
theorem mixedTruncationLimitMeasure_restrict_max_of_lt_const {Ω : Opens (ComplexModel n)}
    {u w : Fin n → ComplexModel n → EReal} (q : Fin n → ℝ)
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hmax : ∀ i, PlurisubharmonicOn (fun z => max (u i z) (w i z)) Ω)
    (hwq : ∀ i, ∀ z ∈ Ω, w i z < (q i : EReal)) :
    (mixedTruncationLimitMeasure Ω (fun i z => max (u i z) (w i z)) hmax).restrict
        {z | z ∈ Ω ∧ ∀ i, (q i : EReal) < u i z} =
      (mixedTruncationLimitMeasure Ω u hu).restrict
        {z | z ∈ Ω ∧ ∀ i, (q i : EReal) < u i z} := by
  set Y : Fin n → ComplexModel n → EReal := fun i z => max (u i z) (w i z) with hY
  set S := {z | z ∈ Ω ∧ ∀ i, (q i : EReal) < u i z} with hS
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ i, -(k : ℝ) < q i := by
    obtain ⟨k, hk⟩ := exists_nat_gt (∑ i, |q i|)
    refine ⟨k, fun i => ?_⟩
    have h1 : |q i| ≤ ∑ j, |q j| :=
      Finset.single_le_sum (f := fun j => |q j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [neg_abs_le (q i)]
  have hkE (i : Fin n) : ((-(k : ℝ) : ℝ) : EReal) < (q i : EReal) :=
    EReal.coe_lt_coe_iff.mpr (hk i)
  have hSu : S ⊆ commonStrictLocus Ω u k := fun z hz =>
    ⟨hz.1, fun i => (hkE i).trans (hz.2 i)⟩
  have hSY : S ⊆ commonStrictLocus Ω Y k := fun z hz =>
    ⟨hz.1, fun i => ((hkE i).trans (hz.2 i)).trans_le (le_max_left _ _)⟩
  have eL : (mixedTruncationLimitMeasure Ω Y hmax).restrict S =
      (mixedTruncationMeasure Ω Y hmax k).restrict S := by
    rw [← Measure.restrict_restrict_of_subset hSY,
      mixedTruncationLimitMeasure_restrict_commonStrictLocus]
  have eR : (mixedTruncationLimitMeasure Ω u hu).restrict S =
      (mixedTruncationMeasure Ω u hu k).restrict S := by
    rw [← Measure.restrict_restrict_of_subset hSu,
      mixedTruncationLimitMeasure_restrict_commonStrictLocus]
  rw [eL, eR]
  unfold mixedTruncationMeasure
  rw [Measure.restrict_restrict_of_subset hSu, Measure.restrict_restrict_of_subset hSY]
  set Z : Fin n → ComplexModel n → EReal := fun i z => max (u i z) (q i : EReal) with hZ
  have hZpsh : ∀ i, PlurisubharmonicOn (Z i) Ω := fun i =>
    (hu i).max (fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) z)
  have hg : ∀ i, BedfordTaylor.IsSmoothPsdOn Ω (fun _ => q i) := fun i =>
    ⟨contDiffOn_const, fun z _ => by
      have hc : complexHessian (fun _ : ComplexModel n => q i) z = 0 := by
        ext j l; simp [complexHessian]
      rw [hc]; exact Matrix.PosSemidef.zero⟩
  have hkey (v : Fin n → ComplexModel n → EReal) (hv : ∀ i, PlurisubharmonicOn (v i) Ω)
      (hvZ : ∀ i, ∀ z ∈ Ω, max (max (v i z) ((-(k : ℝ) : ℝ) : EReal)) (q i : EReal) =
        max (Z i z) ((-(k : ℝ) : ℝ) : EReal)) :
      ∀ i, EqOn (mixedTruncationReal Z k i)
        (fun z => max (mixedTruncationReal v k i z) (q i)) Ω := by
    intro i z hz
    change (truncation (Z i) k z).toReal = max (truncation (v i) k z).toReal (q i)
    rw [max_toReal_coe (truncation_ne_top (hv i) k hz) (truncation_ne_bot _ k z)]
    exact congrArg EReal.toReal (hvZ i z hz).symm
  have hYZ := hkey Y hmax (fun i z hz => max_max_max_eq (hwq i z hz).le)
  have huZ := hkey u hu (fun i z hz => max_max_eq (hkE i).le)
  have hspec (v : Fin n → ComplexModel n → EReal) (hv : ∀ i, PlurisubharmonicOn (v i) Ω) :=
    canonicalMixedBedfordTaylorMeasure_spec Ω _ (mixedTruncationReal_isLocallyBounded hv k)
  have h1 := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.restrict_max_obstacle
    (hspec Y hmax) (hspec Z hZpsh) hg hYZ
  have h2 := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.restrict_max_obstacle
    (hspec u hu) (hspec Z hZpsh) hg huZ
  have hsub (v : Fin n → ComplexModel n → EReal) (hv : ∀ i, PlurisubharmonicOn (v i) Ω)
      (hSv : ∀ z ∈ S, ∀ i, (q i : EReal) < v i z) :
      S ⊆ {z | z ∈ Ω ∧ ∀ i, q i < mixedTruncationReal v k i z} := by
    intro z hz
    refine ⟨hz.1, fun i => ?_⟩
    change q i < (truncation (v i) k z).toReal
    have hlt : (q i : EReal) < truncation (v i) k z := (hSv z hz i).trans_le (le_max_left _ _)
    rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal (truncation_ne_top (hv i) k hz.1)
      (truncation_ne_bot _ k z)]
    exact hlt
  have hS1 := hsub Y hmax (fun z hz i => (hz.2 i).trans_le (le_max_left _ _))
  have hS2 := hsub u hu (fun z hz i => hz.2 i)
  rw [← Measure.restrict_restrict_of_subset hS1, ← h1, Measure.restrict_restrict_of_subset hS1]
  conv_rhs => rw [← Measure.restrict_restrict_of_subset hS2, ← h2,
    Measure.restrict_restrict_of_subset hS2]

/-- **Plurifine locality of the maximum.** The mixed truncation-limit measure of
the slotwise maximum `max (u i) (w i)` agrees with that of `u` on the set where
every obstacle lies strictly below its slot. No finiteness is assumed. -/
theorem mixedTruncationLimitMeasure_restrict_max_eq {Ω : Opens (ComplexModel n)}
    {u w : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (hw : ∀ i, PlurisubharmonicOn (w i) Ω)
    (hmax : ∀ i, PlurisubharmonicOn (fun z => max (u i z) (w i z)) Ω) :
    (mixedTruncationLimitMeasure Ω (fun i z => max (u i z) (w i z)) hmax).restrict
        {z | z ∈ Ω ∧ ∀ i, w i z < u i z} =
      (mixedTruncationLimitMeasure Ω u hu).restrict {z | z ∈ Ω ∧ ∀ i, w i z < u i z} := by
  have hopen (q : Fin n → ℚ) :
      IsOpen {z | z ∈ Ω ∧ ∀ i, w i z < ((q i : ℝ) : EReal)} := by
    have hi (i : Fin n) : IsOpen {z | z ∈ Ω ∧ w i z < ((q i : ℝ) : EReal)} := by
      obtain ⟨O, hO, hOeq⟩ := upperSemicontinuousOn_iff_preimage_Iio.mp
        (hw i).upperSemicontinuousOn ((q i : ℝ) : EReal)
      have : {z | z ∈ Ω ∧ w i z < ((q i : ℝ) : EReal)} =
          (Ω : Set (ComplexModel n)) ∩ O := by
        rw [← hOeq]; rfl
      rw [this]
      exact Ω.isOpen.inter hO
    have : {z | z ∈ Ω ∧ ∀ i, w i z < ((q i : ℝ) : EReal)} =
        (Ω : Set (ComplexModel n)) ∩
          ⋂ i, {z | z ∈ Ω ∧ w i z < ((q i : ℝ) : EReal)} := by
      ext z
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
      exact ⟨fun h => ⟨h.1, fun i => ⟨h.1, h.2 i⟩⟩,
        fun h => ⟨h.1, fun i => (h.2 i).2⟩⟩
    rw [this]
    exact Ω.isOpen.inter (isOpen_iInter_of_finite hi)
  let V (q : Fin n → ℚ) : Opens (ComplexModel n) := ⟨_, hopen q⟩
  have hVΩ (q : Fin n → ℚ) : V q ≤ Ω := fun z hz => hz.1
  have hunion : {z | z ∈ Ω ∧ ∀ i, w i z < u i z} =
      ⋃ q : Fin n → ℚ, {z | z ∈ V q ∧ ∀ i, ((q i : ℝ) : EReal) < u i z} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hz, hwu⟩
      choose q hq using fun i => EReal.exists_rat_btwn_of_lt (hwu i)
      exact ⟨q, ⟨hz, fun i => (hq i).1⟩, fun i => (hq i).2⟩
    · rintro ⟨q, ⟨hz, hwq⟩, hqu⟩
      exact ⟨hz, fun i => (hwq i).trans (hqu i)⟩
  rw [hunion, Measure.restrict_iUnion_congr]
  intro q
  have hsub :
      {z | z ∈ V q ∧ ∀ i, ((q i : ℝ) : EReal) < u i z} ⊆ (V q : Set (ComplexModel n)) :=
    fun z hz => hz.1
  have eL : (mixedTruncationLimitMeasure Ω (fun i z => max (u i z) (w i z)) hmax).restrict
      {z | z ∈ V q ∧ ∀ i, ((q i : ℝ) : EReal) < u i z} =
      (mixedTruncationLimitMeasure (V q) (fun i z => max (u i z) (w i z))
        (fun i => (hmax i).mono (hVΩ q))).restrict
        {z | z ∈ V q ∧ ∀ i, ((q i : ℝ) : EReal) < u i z} := by
    rw [← Measure.restrict_restrict_of_subset hsub,
      mixedTruncationLimitMeasure_restrict_open (hVΩ q) hmax]
  have eR : (mixedTruncationLimitMeasure Ω u hu).restrict
      {z | z ∈ V q ∧ ∀ i, ((q i : ℝ) : EReal) < u i z} =
      (mixedTruncationLimitMeasure (V q) u (fun i => (hu i).mono (hVΩ q))).restrict
        {z | z ∈ V q ∧ ∀ i, ((q i : ℝ) : EReal) < u i z} := by
    rw [← Measure.restrict_restrict_of_subset hsub,
      mixedTruncationLimitMeasure_restrict_open (hVΩ q) hu]
  rw [eL, eR]
  exact mixedTruncationLimitMeasure_restrict_max_of_lt_const (fun i => (q i : ℝ))
    (fun i => (hu i).mono (hVΩ q)) (fun i => (hmax i).mono (hVΩ q))
    (fun i z hz => hz.2 i)

end SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
