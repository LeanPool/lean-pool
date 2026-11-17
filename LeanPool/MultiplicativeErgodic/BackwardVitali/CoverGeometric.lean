/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BackwardVitali.CoverThird

/-!
# Vitali covering across geometrically separated scales
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The union of symmetric orbit-windows `(fun t => zIter σ t ω) '' Icc (-(r ω)) (r ω)` over a
*measurable* centre set `A`, with a measurable radius function `r`, is measurable — even though
the indexing set `A` may be uncountable. Reorganize the union over centres into a **countable**
union over the integer shift `t : ℤ`: a point lies in the union iff it equals `zIter σ t ω` for
some centre `ω ∈ A` with `t ∈ Icc (-(r ω)) (r ω)`, i.e. it lies in
`zIter σ t '' {ω ∈ A | t ∈ Icc (-(r ω)) (r ω)}`. Each such set is the image of a measurable set
(`A ∩ r ⁻¹' {n | t ∈ Icc (-n) n}`) under the measurable bijection `zIter σ t`
(`measurableSet_zIter_image`). This is what makes the covered region of `vitali_cover_geometric`
measurable, so `vitali_cover_third` may be applied to its (measurable) complement. -/
lemma measurableSet_iUnion_win (σ : Ω ≃ᵐ Ω) {A : Set Ω} (hA : MeasurableSet A)
    (r : Ω → ℕ) (hr : Measurable r) :
    MeasurableSet (⋃ ω ∈ A, (fun t => zIter σ t ω) '' Set.Icc (-(r ω : ℤ)) (r ω)) := by
  have hrw : (⋃ ω ∈ A, (fun t => zIter σ t ω) '' Set.Icc (-(r ω : ℤ)) (r ω))
      = ⋃ t : ℤ, zIter σ t '' {ω | ω ∈ A ∧ t ∈ Set.Icc (-(r ω : ℤ)) (r ω)} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨ω, hωA, t, ht, hxt⟩
      exact ⟨t, ω, ⟨hωA, ht⟩, hxt⟩
    · rintro ⟨t, ω, ⟨hωA, ht⟩, hxt⟩
      exact ⟨ω, hωA, t, ht, hxt⟩
  rw [hrw]
  refine MeasurableSet.iUnion (fun t => ?_)
  apply measurableSet_zIter_image σ t
  have hcond : {ω | ω ∈ A ∧ t ∈ Set.Icc (-(r ω : ℤ)) (r ω)}
      = A ∩ r ⁻¹' {n : ℕ | t ∈ Set.Icc (-(n : ℤ)) (n : ℤ)} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [hcond]
  exact hA.inter (hr (Set.to_countable _).measurableSet)

/-- Any function `ℕ → ℕ` is measurable: `ℕ`'s `MeasurableSpace` makes every (countable, i.e.
every) subset measurable, so preimages are automatically measurable regardless of the function. -/
private lemma measurable_nat_to_nat (g : ℕ → ℕ) : Measurable g :=
  fun S _ => (Set.to_countable (g ⁻¹' S)).measurableSet

/-- **The key `ℕ`-arithmetic fact behind the growth-factor fix.** If a "true" radius `r` is
enlarged by a `1/G` buffer (`r + r / G`, `Nat` division), the ratio of true-to-enlarged window
counts is at least `G / (G + 1)`, *uniformly in `r`* — this is what replaces the previous
(unachievable) fixed-ratio-3 approach: the loss shrinks as `G` grows, for every `r` at once.
Proof: `(r / G) * G ≤ r` (`Nat.div_mul_le_self`), so `G * (2 * (r + r/G) + 1)
= 2 * r * G + 2 * (r/G) * G + G ≤ 2 * r * G + 2 * r + G < (2 * r + 1) * (G + 1)
= 2 * r * G + 2 * r + G + 1`. -/
private lemma enlarge_ratio_le (r G : ℕ) :
    G * (2 * (r + r / G) + 1) ≤ (G + 1) * (2 * r + 1) := by
  have hdiv : (r / G) * G ≤ r := Nat.div_mul_le_self r G
  nlinarith [hdiv]

/-- A `1/G` enlargement of disjoint orbit windows costs at most the factor `(G+1)/G`. -/
private theorem measure_variable_window_enlargement [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ) (Bnd G : ℕ) :
    ∀ (S : Set Ω), MeasurableSet S → ∀ (r0 : Ω → ℕ), Measurable r0 →
      (∀ ω, r0 ω ≤ Bnd) →
      S.PairwiseDisjoint (fun ω => (fun t => zIter σ t ω) ''
        Set.Icc (-(r0 ω : ℤ)) (r0 ω : ℤ)) →
      G * μ (⋃ ω ∈ S, (fun t => zIter σ t ω) ''
        Set.Icc (-((r0 ω + r0 ω / G : ℕ) : ℤ)) ((r0 ω + r0 ω / G : ℕ) : ℤ))
        ≤ (G + 1) * μ (⋃ ω ∈ S, (fun t => zIter σ t ω) ''
          Set.Icc (-(r0 ω : ℤ)) (r0 ω : ℤ)) := by
  classical
  set win : ℕ → Ω → Set Ω := fun r ω =>
    (fun t => zIter σ t ω) '' Set.Icc (-(r : ℤ)) (r : ℤ) with hwindef
  -- The union-over-shifts form of a window union, matching `measure_iUnion_zIter_window_le/_eq`'s
  -- statement shape (union over `t ∈ Icc`, not over `ω ∈ S`) to the `win`-indexed form used here.
  have hWU_eq : ∀ (r : ℕ) (S : Set Ω),
      (⋃ t ∈ Set.Icc (-(r : ℤ)) r, zIter σ t '' S) = ⋃ ω ∈ S, win r ω := by
    intro r S
    ext z
    simp only [hwindef, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨t, ht, ω, hω, hz⟩; exact ⟨ω, hω, t, ht, hz⟩
    · rintro ⟨ω, hω, t, ht, hz⟩; exact ⟨t, ht, ω, hω, hz⟩
  -- `zIter` at a natural-number index matches plain iteration.
  have hznat : ∀ (n : ℕ) (x : Ω), zIter σ (n : ℤ) x = (⇑σ)^[n] x := by
    intro n x
    rw [zIter_eq_zpow, zpow_natCast, Equiv.Perm.coe_pow]
    rfl
  -- **Non-periodicity up to a bounded period, as a null set.** Needed to upgrade
  -- "pairwise disjoint windows over distinct points" (all `vitali_cover_third` exposes) to the
  -- *stronger* shifted-set disjointness `measure_iUnion_zIter_window_eq` needs: the only way the
  -- weaker fact can fail to give the stronger one is if some *single* point's own window has an
  -- internal self-collision, i.e. the point is periodic with period `≤ 2r`. That is null.
  have hPerBad_null : ∀ r : ℕ,
      μ (⋃ N ∈ Finset.Icc 1 (2 * r), {x : Ω | zIter σ (N : ℤ) x = x}) = 0 := by
    intro r
    have hterm0 : ∀ N ∈ Finset.Icc 1 (2 * r), μ {x : Ω | zIter σ (N : ℤ) x = x} = 0 := by
      intro N hN
      have hN1 : 1 ≤ N := (Finset.mem_Icc.mp hN).1
      have heq : {x : Ω | zIter σ (N : ℤ) x = x} = {x : Ω | (⇑σ)^[N] x = x} := by
        ext x; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hznat]
      rw [heq]
      exact periodic_null μ σ hσ hN1
    have hle : μ (⋃ N ∈ Finset.Icc 1 (2 * r), {x : Ω | zIter σ (N : ℤ) x = x}) ≤ 0 :=
      calc μ (⋃ N ∈ Finset.Icc 1 (2 * r), {x : Ω | zIter σ (N : ℤ) x = x})
          ≤ ∑ N ∈ Finset.Icc 1 (2 * r), μ {x : Ω | zIter σ (N : ℤ) x = x} :=
            measure_biUnion_finset_le _ _
        _ = 0 := Finset.sum_eq_zero hterm0
    exact le_antisymm hle bot_le
  -- A point's own single-window self-collision at two distinct indices forces it to be periodic
  -- with a bounded period.
  have hperiodic_of_eq : ∀ (d : ℤ) (x : Ω), zIter σ d x = x → zIter σ (d.natAbs : ℤ) x = x := by
    intro d x hd
    by_cases hd0 : 0 ≤ d
    · rwa [Int.natAbs_of_nonneg hd0]
    · push Not at hd0
      have hnegd : zIter σ (-d) x = x := by
        calc zIter σ (-d) x = zIter σ (-d) (zIter σ d x) := by rw [hd]
          _ = zIter σ (-d + d) x := by rw [← zIter_add]
          _ = zIter σ 0 x := by norm_num
          _ = x := zIter_zero_apply σ x
      rwa [show (d.natAbs : ℤ) = -d from by omega]
  intro S hSmeas r0 hr0meas hr0B hdisj
  set level : ℕ → Set Ω := fun r => S ∩ r0 ⁻¹' {r} with hleveldef
  have hlevelmeas : ∀ r, MeasurableSet (level r) :=
    fun r => hSmeas.inter (hr0meas (measurableSet_singleton r))
  have hlevelsub : ∀ r, level r ⊆ S := fun _ => Set.inter_subset_left
  have hlevel_r0 : ∀ r ω, ω ∈ level r → r0 ω = r := fun r ω hω => hω.2
  set Bad : ℕ → Set Ω :=
    fun r => ⋃ N ∈ Finset.Icc 1 (2 * r), {x : Ω | zIter σ (N : ℤ) x = x} with hBaddef
  have hBadmeas : ∀ r, MeasurableSet (Bad r) := fun r =>
    Finset.measurableSet_biUnion _
      (fun N _ => measurableSet_eq_fun (measurable_zIter σ (N : ℤ)) measurable_id)
  have hBadnull : ∀ r, μ (Bad r) = 0 := hPerBad_null
  have hSeq : S = ⋃ r ∈ Finset.range (Bnd + 1), level r := by
    ext ω
    simp only [hleveldef, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hωS; exact ⟨r0 ω, Nat.lt_succ_of_le (hr0B ω), hωS, rfl⟩
    · rintro ⟨r, _, hωS, _⟩; exact hωS
  have hlevelWU_disj : ∀ r r' : ℕ, r ≠ r' →
      Disjoint (⋃ ω ∈ level r, win (r0 ω) ω) (⋃ ω ∈ level r', win (r0 ω) ω) := by
    intro r r' hrr'
    rw [Set.disjoint_iUnion₂_left]
    intro ω hω
    rw [Set.disjoint_iUnion₂_right]
    intro ω' hω'
    have hne : ω ≠ ω' := by
      intro heq
      apply hrr'
      have h1 := hlevel_r0 r ω hω
      have h2 := hlevel_r0 r' ω' hω'
      rw [← h1, heq, h2]
    exact hdisj (hlevelsub r hω) (hlevelsub r' hω') hne
  have hTrueEq : μ (⋃ ω ∈ S, win (r0 ω) ω)
      = ∑ r ∈ Finset.range (Bnd + 1), μ (⋃ ω ∈ level r, win (r0 ω) ω) := by
    conv_lhs => rw [hSeq]
    rw [show (⋃ ω ∈ ⋃ r ∈ Finset.range (Bnd + 1), level r, win (r0 ω) ω)
        = ⋃ r ∈ Finset.range (Bnd + 1), ⋃ ω ∈ level r, win (r0 ω) ω from by
      ext z; simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨ω, ⟨r, hr, hωr⟩, hz⟩; exact ⟨r, hr, ω, hωr, hz⟩
      · rintro ⟨r, hr, ω, hωr, hz⟩; exact ⟨ω, ⟨r, hr, hωr⟩, hz⟩]
    exact measure_biUnion_finset (fun r _ r' _ hrr' => hlevelWU_disj r r' hrr')
      (fun r _ => measurableSet_iUnion_win σ (hlevelmeas r) r0 hr0meas)
  -- Per-level exact equality, via the null bounded-period correction.
  have hTrueLevel : ∀ r, μ (⋃ ω ∈ level r, win (r0 ω) ω) = (2 * r + 1) * μ (level r) := by
    intro r
    have heq0 : (⋃ ω ∈ level r, win (r0 ω) ω) = ⋃ ω ∈ level r, win r ω :=
      Set.iUnion₂_congr (fun ω hω => by rw [hlevel_r0 r ω hω])
    rw [heq0]
    have hcorrect : μ (⋃ ω ∈ level r, win r ω) = μ (⋃ ω ∈ level r \ Bad r, win r ω) := by
      refine le_antisymm ?_ (measure_mono (Set.biUnion_subset_biUnion_left Set.sdiff_subset))
      have hsub : (⋃ ω ∈ level r, win r ω)
          ⊆ (⋃ ω ∈ level r \ Bad r, win r ω) ∪ (⋃ ω ∈ Bad r, win r ω) := by
        intro z hz
        simp only [Set.mem_iUnion] at hz
        obtain ⟨ω, hω, hz⟩ := hz
        by_cases hb : ω ∈ Bad r
        · exact Or.inr (Set.mem_biUnion hb hz)
        · exact Or.inl (Set.mem_biUnion ⟨hω, hb⟩ hz)
      have hBadWU0 : μ (⋃ ω ∈ Bad r, win r ω) = 0 := by
        rw [← hWU_eq r (Bad r)]
        have hle := measure_iUnion_zIter_window_le σ hσ.toMeasurePreserving r (hBadmeas r)
        rw [hBadnull r, mul_zero] at hle
        exact le_antisymm hle bot_le
      calc μ (⋃ ω ∈ level r, win r ω)
          ≤ μ ((⋃ ω ∈ level r \ Bad r, win r ω) ∪ (⋃ ω ∈ Bad r, win r ω)) := measure_mono hsub
        _ ≤ μ (⋃ ω ∈ level r \ Bad r, win r ω) + μ (⋃ ω ∈ Bad r, win r ω) := measure_union_le _ _
        _ = μ (⋃ ω ∈ level r \ Bad r, win r ω) := by rw [hBadWU0, add_zero]
    rw [hcorrect]
    have hdisjTrim : ∀ i ∈ Set.Icc (-(r : ℤ)) r, ∀ k ∈ Set.Icc (-(r : ℤ)) r, i ≠ k →
        Disjoint (zIter σ i '' (level r \ Bad r)) (zIter σ k '' (level r \ Bad r)) := by
      intro i hi k hk hik
      rw [Set.disjoint_left]
      rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
      by_cases hxy : x = y
      · subst hxy
        apply hx.2
        have heqx : zIter σ i x = zIter σ k x := hxz.trans hyz.symm
        have hzik : zIter σ (i - k) x = x := by
          have step1 : zIter σ (-k) (zIter σ i x) = zIter σ (-k) (zIter σ k x) := by rw [heqx]
          rw [← zIter_add, ← zIter_add, show (-k + k : ℤ) = 0 from by ring,
            zIter_zero_apply] at step1
          rwa [show (-k + i : ℤ) = i - k from by ring] at step1
        have hxbad : zIter σ ((i - k).natAbs : ℤ) x = x := hperiodic_of_eq (i - k) x hzik
        simp only [hBaddef, Set.mem_iUnion]
        refine ⟨(i - k).natAbs, ?_, hxbad⟩
        simp only [Finset.mem_Icc] at *
        simp only [Set.mem_Icc] at hi hk
        omega
      · have hd : Disjoint (win (r0 x) x) (win (r0 y) y) :=
          hdisj (hlevelsub r hx.1) (hlevelsub r hy.1) hxy
        rw [hlevel_r0 r x hx.1, hlevel_r0 r y hy.1] at hd
        exact Set.disjoint_left.mp hd ⟨i, hi, hxz⟩ ⟨k, hk, hyz⟩
    rw [← hWU_eq r (level r \ Bad r)]
    rw [measure_iUnion_zIter_window_eq σ hσ.toMeasurePreserving r ((hlevelmeas r).diff
      (hBadmeas r)) hdisjTrim]
    congr 1
    exact measure_sdiff_null (hBadnull r)
  -- Enlarged bound: subadditive over levels (no disjointness needed).
  have hEnlLe : μ (⋃ ω ∈ S, win (r0 ω + r0 ω / G) ω)
      ≤ ∑ r ∈ Finset.range (Bnd + 1), μ (⋃ ω ∈ level r, win (r + r / G) ω) := by
    have hEnlEq : (⋃ ω ∈ S, win (r0 ω + r0 ω / G) ω)
        = ⋃ r ∈ Finset.range (Bnd + 1), ⋃ ω ∈ level r, win (r0 ω + r0 ω / G) ω := by
      conv_lhs => rw [hSeq]
      ext z; simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨ω, ⟨r, hr, hωr⟩, hz⟩; exact ⟨r, hr, ω, hωr, hz⟩
      · rintro ⟨r, hr, ω, hωr, hz⟩; exact ⟨ω, ⟨r, hr, hωr⟩, hz⟩
    rw [hEnlEq]
    calc μ (⋃ r ∈ Finset.range (Bnd + 1), ⋃ ω ∈ level r, win (r0 ω + r0 ω / G) ω)
        ≤ ∑ r ∈ Finset.range (Bnd + 1), μ (⋃ ω ∈ level r, win (r0 ω + r0 ω / G) ω) :=
          measure_biUnion_finset_le _ _
      _ = ∑ r ∈ Finset.range (Bnd + 1), μ (⋃ ω ∈ level r, win (r + r / G) ω) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          congr 1
          exact Set.iUnion₂_congr (fun ω hω => by rw [hlevel_r0 r ω hω])
  have hEnlLevel : ∀ r, μ (⋃ ω ∈ level r, win (r + r / G) ω)
      ≤ (2 * ((r + r / G : ℕ) : ℝ≥0∞) + 1) * μ (level r) := by
    intro r
    rw [← hWU_eq (r + r / G) (level r)]
    exact measure_iUnion_zIter_window_le σ hσ.toMeasurePreserving (r + r / G) (hlevelmeas r)
  -- Combine level-by-level via `enlarge_ratio_le`, then sum.
  have hlevelRatio : ∀ r, (G : ℝ≥0∞) * μ (⋃ ω ∈ level r, win (r + r / G) ω)
      ≤ ((G : ℝ≥0∞) + 1) * μ (⋃ ω ∈ level r, win (r0 ω) ω) := by
    intro r
    have hcast : ((G * (2 * (r + r / G) + 1) : ℕ) : ℝ≥0∞)
        ≤ (((G + 1) * (2 * r + 1) : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr (enlarge_ratio_le r G)
    calc (G : ℝ≥0∞) * μ (⋃ ω ∈ level r, win (r + r / G) ω)
        ≤ (G : ℝ≥0∞) * ((2 * ((r + r / G : ℕ) : ℝ≥0∞) + 1) * μ (level r)) := by
          gcongr; exact hEnlLevel r
      _ = ((G * (2 * (r + r / G) + 1) : ℕ) : ℝ≥0∞) * μ (level r) := by
          push_cast; ring
      _ ≤ (((G + 1) * (2 * r + 1) : ℕ) : ℝ≥0∞) * μ (level r) := by
          gcongr
      _ = ((G : ℝ≥0∞) + 1) * μ (⋃ ω ∈ level r, win (r0 ω) ω) := by
          rw [hTrueLevel r]; push_cast; ring
  calc (G : ℝ≥0∞) * μ (⋃ ω ∈ S, win (r0 ω + r0 ω / G) ω)
      ≤ (G : ℝ≥0∞) * ∑ r ∈ Finset.range (Bnd + 1), μ (⋃ ω ∈ level r, win (r + r / G) ω) := by
        gcongr
    _ = ∑ r ∈ Finset.range (Bnd + 1), (G : ℝ≥0∞) * μ (⋃ ω ∈ level r, win (r + r / G) ω) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ Finset.range (Bnd + 1), ((G : ℝ≥0∞) + 1) * μ (⋃ ω ∈ level r, win (r0 ω) ω) :=
        Finset.sum_le_sum (fun r _ => hlevelRatio r)
    _ = ((G : ℝ≥0∞) + 1) * ∑ r ∈ Finset.range (Bnd + 1), μ (⋃ ω ∈ level r, win (r0 ω) ω) := by
        rw [Finset.mul_sum]
    _ = ((G : ℝ≥0∞) + 1) * μ (⋃ ω ∈ S, win (r0 ω) ω) := by rw [hTrueEq]

/-- Finite disjoint true covers control both the final remainder and enlargement collars. -/
private theorem measure_finite_selection_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A₀ U : Set Ω) (R TrueWin EnlargedWin : ℕ → Set Ω)
    (m G : ℕ) (hm : 1 ≤ m) (hG1' : 0 < G)
    (hR0 : R 0 = A₀) (hRsucc' : ∀ k, R (k + 1) = R k \ EnlargedWin k)
    (hRanti : Antitone R)
    (hTrueMeas : ∀ k, MeasurableSet (TrueWin k))
    (hEnlargedMeas : ∀ k, MeasurableSet (EnlargedWin k))
    (hNested : ∀ k, TrueWin k ⊆ EnlargedWin k)
    (hRatioK : ∀ k, (G : ℝ≥0∞) * μ (EnlargedWin k) ≤ (G + 1) * μ (TrueWin k))
    (hRk_le3 : ∀ k, μ (R k) ≤ 3 * μ (EnlargedWin k))
    (hTrueWindowCrossDisjoint : ∀ k k', k < m → k' < m → k ≠ k' →
      Disjoint (TrueWin k) (TrueWin k'))
    (hTrueWindowUnion_eq : U = ⋃ k ∈ Finset.range m, TrueWin k) :
    μ (A₀ \ U) ≤ ENNReal.ofReal (3 * ((G : ℝ) + 1) / (G * m) + 1 / G) := by
  classical
  have hPerLevel : ∀ k, (G : ℝ≥0∞) * μ (R k)
      ≤ 3 * (G + 1) * μ (TrueWin k) := by
    intro k
    have h1 := hRk_le3 k
    have h2 := hRatioK k
    calc (G : ℝ≥0∞) * μ (R k)
        ≤ (G : ℝ≥0∞) * (3 * μ (EnlargedWin k)) := by
          gcongr
      _ = 3 * ((G : ℝ≥0∞) * μ (EnlargedWin k)) := by ring
      _ ≤ 3 * (((G : ℝ≥0∞) + 1) * μ (TrueWin k)) := by
          gcongr
      _ = 3 * ((G : ℝ≥0∞) + 1) * μ (TrueWin k) := by ring
  -- Cross-level true-window disjointness (set-level), needed for the
  -- finite-sum-equals-measure step.
  have hSumTrue_le1 : ∑ k ∈ Finset.range m, μ (TrueWin k) ≤ 1 := by
    rw [← measure_biUnion_finset (fun k hk k' hk' hkk' => hTrueWindowCrossDisjoint k k'
        (Finset.mem_range.mp hk) (Finset.mem_range.mp hk') hkk')
      (fun k _ => hTrueMeas k)]
    calc μ (⋃ k ∈ Finset.range m, TrueWin k)
        ≤ μ (Set.univ : Set Ω) := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hRk_ge_Rm : ∀ k, k < m → μ (R m) ≤ μ (R k) := fun k hk => measure_mono (hRanti hk.le)
  have hSumR_ge : (m : ℝ≥0∞) * μ (R m) ≤ ∑ k ∈ Finset.range m, μ (R k) := by
    calc (m : ℝ≥0∞) * μ (R m) = ∑ _k ∈ Finset.range m, μ (R m) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range m, μ (R k) :=
          Finset.sum_le_sum (fun k hk => hRk_ge_Rm k (Finset.mem_range.mp hk))
  have hFinalRm : (G : ℝ≥0∞) * m * μ (R m) ≤ 3 * ((G : ℝ≥0∞) + 1) := by
    calc (G : ℝ≥0∞) * m * μ (R m) = (G : ℝ≥0∞) * (m * μ (R m)) := by ring
      _ ≤ (G : ℝ≥0∞) * ∑ k ∈ Finset.range m, μ (R k) := by gcongr
      _ = ∑ k ∈ Finset.range m, (G : ℝ≥0∞) * μ (R k) := by rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range m, 3 * ((G : ℝ≥0∞) + 1) * μ (TrueWin k) :=
          Finset.sum_le_sum (fun k _ => hPerLevel k)
      _ = 3 * ((G : ℝ≥0∞) + 1) * ∑ k ∈ Finset.range m, μ (TrueWin k) := by
          rw [Finset.mul_sum]
      _ ≤ 3 * ((G : ℝ≥0∞) + 1) * 1 := by gcongr
      _ = 3 * ((G : ℝ≥0∞) + 1) := mul_one _
  -- Convert to a real-number bound on `μ (R m)`.
  have hRmtop : μ (R m) ≠ ⊤ := measure_ne_top μ _
  have hRmReal : (G : ℝ) * m * (μ (R m)).toReal ≤ 3 * ((G : ℝ) + 1) := by
    have heq1 : ((G : ℝ≥0∞) * m * μ (R m)).toReal = (G : ℝ) * m * (μ (R m)).toReal := by
      simp [ENNReal.toReal_mul]
    have heq2 : ((3 * ((G : ℝ≥0∞) + 1))).toReal = 3 * ((G : ℝ) + 1) := by
      simp [ENNReal.toReal_mul, ENNReal.toReal_add]
    have hGp1top : (3 * ((G : ℝ≥0∞) + 1)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top G, ENNReal.one_ne_top⟩)
    calc (G : ℝ) * m * (μ (R m)).toReal = ((G : ℝ≥0∞) * m * μ (R m)).toReal := heq1.symm
      _ ≤ (3 * ((G : ℝ≥0∞) + 1)).toReal :=
          ENNReal.toReal_mono hGp1top hFinalRm
      _ = 3 * ((G : ℝ) + 1) := heq2
  have hGmpos : (0 : ℝ) < (G : ℝ) * m := by
    have : (0:ℝ) < G := by exact_mod_cast hG1'
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm
    positivity
  have hRmBoundReal : (μ (R m)).toReal ≤ 3 * ((G : ℝ) + 1) / (G * m) := by
    rw [le_div_iff₀ hGmpos]
    nlinarith [hRmReal]
  have hRmBound : μ (R m) ≤ ENNReal.ofReal (3 * ((G : ℝ) + 1) / (G * m)) := by
    rw [← ENNReal.ofReal_toReal hRmtop]
    exact ENNReal.ofReal_le_ofReal hRmBoundReal
  -- Telescoping: `R k = A₀ \ (union of the first `k` enlarged selections)`.
  have hRexpand : ∀ k, R k = A₀ \ ⋃ j ∈ Finset.range k, EnlargedWin j := by
    intro k
    induction k with
    | zero => simp [hR0]
    | succ k ih =>
      rw [hRsucc' k, ih]
      ext x
      simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨⟨hxA0, hxnotin⟩, hxnotk⟩
        refine ⟨hxA0, ?_⟩
        rintro ⟨j, hjk1, hxj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjk1 with hjk | hjk
        · exact hxnotin ⟨j, hjk, hxj⟩
        · rw [hjk] at hxj; exact hxnotk hxj
      · rintro ⟨hxA0, hxnot⟩
        exact ⟨⟨hxA0, fun ⟨j, hjk, hxj⟩ => hxnot ⟨j, by omega, hxj⟩⟩,
          fun hxk => hxnot ⟨k, by omega, hxk⟩⟩
  have hUncoveredSubset : A₀ \ U ⊆
      R m ∪ ⋃ k ∈ Finset.range m,
        (EnlargedWin k \ TrueWin k) := by
    intro x hx
    by_cases hxRm : x ∈ R m
    · exact Or.inl hxRm
    · have hxA0 : x ∈ A₀ := hx.1
      have hxnotTrue : x ∉ U := hx.2
      have hxEnl : x ∈ ⋃ k ∈ Finset.range m, EnlargedWin k := by
        by_contra hcon
        exact hxRm (by rw [hRexpand m]; exact ⟨hxA0, hcon⟩)
      obtain ⟨k, hkm, hxk⟩ := Set.mem_iUnion₂.mp hxEnl
      refine Or.inr (Set.mem_biUnion hkm ⟨hxk, fun hxTrue => hxnotTrue ?_⟩)
      rw [hTrueWindowUnion_eq]; exact Set.mem_biUnion hkm hxTrue
  have hGapBound : ∀ k, (G : ℝ≥0∞) *
      μ (EnlargedWin k \ TrueWin k)
      ≤ μ (TrueWin k) := by
    intro k
    set EnlK := EnlargedWin k with hEnlKdef
    set TrueK := TrueWin k with hTrueKdef
    have hsub : TrueK ⊆ EnlK := by
      exact hNested k
    have hdisjUT : Disjoint TrueK (EnlK \ TrueK) :=
      Set.disjoint_left.mpr (fun x hx1 hx2 => hx2.2 hx1)
    have hmeasTrueK : MeasurableSet TrueK :=
      hTrueMeas k
    have hmeasEnlDiff : MeasurableSet (EnlK \ TrueK) :=
      (hEnlargedMeas k).diff hmeasTrueK
    have hmeasEnl : μ EnlK = μ TrueK + μ (EnlK \ TrueK) := by
      conv_lhs => rw [← Set.union_sdiff_cancel hsub]
      exact measure_union hdisjUT hmeasEnlDiff
    have hR := hRatioK k
    rw [show EnlargedWin k = EnlK from rfl,
      show TrueWin k = TrueK from rfl, hmeasEnl] at hR
    have hRexp : (G : ℝ≥0∞) * μ TrueK + (G : ℝ≥0∞) * μ (EnlK \ TrueK)
        ≤ (G : ℝ≥0∞) * μ TrueK + μ TrueK := by
      calc (G : ℝ≥0∞) * μ TrueK + (G : ℝ≥0∞) * μ (EnlK \ TrueK)
          = (G : ℝ≥0∞) * (μ TrueK + μ (EnlK \ TrueK)) := by ring
        _ ≤ ((G : ℝ≥0∞) + 1) * μ TrueK := hR
        _ = (G : ℝ≥0∞) * μ TrueK + μ TrueK := by ring
    have hGTop : (G : ℝ≥0∞) * μ TrueK ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top G) (measure_ne_top μ TrueK)
    exact (ENNReal.add_le_add_iff_left hGTop).mp hRexp
  have hSumGap_le : (G : ℝ≥0∞) * ∑ k ∈ Finset.range m,
      μ (EnlargedWin k \ TrueWin k)
      ≤ 1 := by
    calc (G : ℝ≥0∞) * ∑ k ∈ Finset.range m,
        μ (EnlargedWin k \ TrueWin k)
        = ∑ k ∈ Finset.range m, (G : ℝ≥0∞) *
          μ (EnlargedWin k \ TrueWin k) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range m, μ (TrueWin k) :=
          Finset.sum_le_sum (fun k _ => hGapBound k)
      _ ≤ 1 := hSumTrue_le1
  have hSumGapReal_le : ∑ k ∈ Finset.range m,
      (μ (EnlargedWin k \ TrueWin k)).toReal
      ≤ 1 / G := by
    have hGpos : (0 : ℝ) < G := by exact_mod_cast hG1'
    have hmeasne : ∀ k ∈ Finset.range m,
        μ (EnlargedWin k \ TrueWin k) ≠ ⊤ :=
      fun k _ => measure_ne_top μ _
    have hcast : ((G : ℝ≥0∞) * ∑ k ∈ Finset.range m,
        μ (EnlargedWin k \ TrueWin k)).toReal
        ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by norm_num) hSumGap_le
    rw [ENNReal.toReal_mul, ENNReal.toReal_one, ENNReal.toReal_sum hmeasne] at hcast
    rw [le_div_iff₀ hGpos]
    calc (∑ k ∈ Finset.range m,
          (μ (EnlargedWin k \ TrueWin k)).toReal) * G
        = (G : ℝ) * ∑ k ∈ Finset.range m,
          (μ (EnlargedWin k \ TrueWin k)).toReal := by
          ring
      _ ≤ 1 := hcast
  have hFinalUncovered : μ (A₀ \ U) ≤
      μ (R m) + ∑ k ∈ Finset.range m,
        μ (EnlargedWin k \ TrueWin k) := by
    calc μ (A₀ \ U)
        ≤ μ (R m ∪ ⋃ k ∈ Finset.range m,
            (EnlargedWin k \ TrueWin k)) :=
          measure_mono hUncoveredSubset
      _ ≤ μ (R m) + μ (⋃ k ∈ Finset.range m,
            (EnlargedWin k \ TrueWin k)) :=
          measure_union_le _ _
      _ ≤ μ (R m) + ∑ k ∈ Finset.range m,
            μ (EnlargedWin k \ TrueWin k) := by
          gcongr; exact measure_biUnion_finset_le _ _
  have hFinalReal : (μ (A₀ \ U)).toReal
      ≤ 3 * ((G : ℝ) + 1) / (G * m) + 1 / G := by
    have hsumne : (∑ k ∈ Finset.range m,
        μ (EnlargedWin k \ TrueWin k)) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun k _ => measure_ne_top μ _)
    have htop2 : μ (R m) + ∑ k ∈ Finset.range m,
        μ (EnlargedWin k \ TrueWin k) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hRmtop, hsumne⟩
    calc (μ (A₀ \ U)).toReal
        ≤ (μ (R m) + ∑ k ∈ Finset.range m,
            μ (EnlargedWin k \ TrueWin k)).toReal :=
          ENNReal.toReal_mono htop2 hFinalUncovered
      _ = (μ (R m)).toReal + (∑ k ∈ Finset.range m,
            μ (EnlargedWin k \ TrueWin k)).toReal := by
          rw [ENNReal.toReal_add hRmtop hsumne]
      _ = (μ (R m)).toReal + ∑ k ∈ Finset.range m,
            (μ (EnlargedWin k \ TrueWin k)).toReal := by
          rw [ENNReal.toReal_sum (fun k _ => measure_ne_top μ _)]
      _ ≤ 3 * ((G : ℝ) + 1) / (G * m) + 1 / G := by
          have h1 : (μ (R m)).toReal ≤ 3 * ((G : ℝ) + 1) / (G * m) := hRmBoundReal
          have h2 := hSumGapReal_le
          linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (A₀ \ U))]
  exact ENNReal.ofReal_le_ofReal hFinalReal

/-- Descending removal with measurable, bounded orbit windows and a one-third selection. -/
private theorem exists_orbit_window_ladder [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    (A₀ : Set Ω) (hA₀ : MeasurableSet A₀) (r : ℕ → Ω → ℕ)
    (hr : ∀ k, Measurable (r k)) (Bnd : ℕ) (hrB : ∀ k ω, r k ω ≤ Bnd) :
    ∃ R Piece : ℕ → Set Ω,
      R 0 = A₀ ∧
      (∀ k, R (k + 1) = R k \ ⋃ ω ∈ Piece k,
        (fun t => zIter σ t ω) '' Set.Icc (-(r k ω : ℤ)) (r k ω : ℤ)) ∧
      (∀ k, MeasurableSet (R k) ∧ MeasurableSet (Piece k)) ∧
      ∀ k, Piece k ⊆ R k ∧
        (Piece k).PairwiseDisjoint (fun ω => (fun t => zIter σ t ω) ''
          Set.Icc (-(r k ω : ℤ)) (r k ω : ℤ)) ∧
        μ (⋃ ω ∈ R k, (fun t => zIter σ t ω) '' Set.Icc (-(r k ω : ℤ)) (r k ω : ℤ))
          ≤ 3 * μ (⋃ ω ∈ Piece k, (fun t => zIter σ t ω) ''
            Set.Icc (-(r k ω : ℤ)) (r k ω : ℤ)) := by
  classical
  let win : ℕ → Ω → Set Ω := fun r ω =>
    (fun t => zIter σ t ω) '' Set.Icc (-(r : ℤ)) (r : ℤ)
  set pieceOf : ℕ → Set Ω → Set Ω := fun k Rk =>
    if h : MeasurableSet Rk then
      (vitali_cover_third μ σ hσ h (r k) (hr k)
        Bnd (hrB k)).choose
    else ∅ with hpieceOfdef
  set R : ℕ → Set Ω := fun k =>
    Nat.rec A₀ (fun k ih => ih \ (⋃ ω ∈ pieceOf k ih, win (r k ω) ω)) k with hRdef
  set Piece : ℕ → Set Ω := fun k => pieceOf k (R k) with hPiecedef
  have hR0 : R 0 = A₀ := rfl
  have hRsucc : ∀ k, R (k + 1) = R k \ (⋃ ω ∈ pieceOf k (R k), win (r k ω) ω) :=
    fun _ => rfl
  have hPiecek : ∀ k, Piece k = pieceOf k (R k) := fun _ => rfl
  have hRsucc' : ∀ k, R (k + 1) = R k \ (⋃ ω ∈ Piece k, win (r k ω) ω) := by
    intro k; rw [hPiecek k]
  -- Measurability of `R`, `Piece`, by simultaneous induction.
  have hMeas : ∀ k, MeasurableSet (R k) ∧ MeasurableSet (Piece k) := by
    intro k
    induction k with
    | zero =>
      have hR0meas : MeasurableSet (R 0) := by rw [hR0]; exact hA₀
      refine ⟨hR0meas, ?_⟩
      rw [hPiecek 0, hpieceOfdef]
      simp only [dite_eq_left hR0meas]
      exact (vitali_cover_third μ σ hσ hR0meas (r 0) (hr 0)
        Bnd (hrB 0)).choose_spec.2.1
    | succ k ih =>
      obtain ⟨ihR, ihPiece⟩ := ih
      have hRk1meas : MeasurableSet (R (k + 1)) := by
        rw [hRsucc' k]
        exact ihR.diff (measurableSet_iUnion_win σ ihPiece (r k) (hr k))
      refine ⟨hRk1meas, ?_⟩
      rw [hPiecek (k + 1), hpieceOfdef]
      simp only [dite_eq_left hRk1meas]
      exact (vitali_cover_third μ σ hσ hRk1meas (r (k + 1)) (hr (k + 1))
        Bnd (hrB (k + 1))).choose_spec.2.1
  -- Full spec of `Piece k`: subset of `R k`, enlarged-windows pairwise disjoint, factor-`3` bound.
  have hPieceSpec : ∀ k, Piece k ⊆ R k ∧
      (Piece k).PairwiseDisjoint (fun ω => win (r k ω) ω) ∧
      μ (⋃ ω ∈ R k, win (r k ω) ω) ≤ 3 * μ (⋃ ω ∈ Piece k, win (r k ω) ω) := by
    intro k
    rw [hPiecek k, hpieceOfdef]
    simp only [dite_eq_left (hMeas k).1]
    have hspec := (vitali_cover_third μ σ hσ (hMeas k).1 (r k) (hr k)
      Bnd (hrB k)).choose_spec
    exact ⟨hspec.1, hspec.2.2⟩
  exact ⟨R, Piece, hR0, hRsucc', hMeas, hPieceSpec⟩

omit [MeasurableSpace Ω] in
/-- A uniform multiplicative separation between successive scales also separates earlier scales. -/
private theorem radius_le_div_of_earlier_scale (A₀ : Set Ω) (m G : ℕ) (hG1' : 0 < G)
    (w : ℕ → Ω → ℕ)
    (hgrow : ∀ s, s < m → ∀ ω ω', ω ∈ A₀ → ω' ∈ A₀ → G * w s ω ≤ w (s + 1) ω') :
    ∀ (t s : ℕ) (ω ω' : Ω), ω ∈ A₀ → ω' ∈ A₀ → t < s → s < m →
      w t ω ≤ w s ω' / G := by
  have hchain2 : ∀ (d s : ℕ) (ω ω' : Ω), ω ∈ A₀ → ω' ∈ A₀ → s + d < m →
      G * w s ω ≤ w (s + d + 1) ω' := by
    intro d
    induction d with
    | zero => intro s ω ω' hω hω' hlt; simpa using hgrow s (by omega) ω ω' hω hω'
    | succ d ihd =>
      intro s ω ω' hω hω' hlt
      have h1 : G * w s ω ≤ w (s + d + 1) ω' := ihd s ω ω' hω hω' (by omega)
      have h2 : G * w (s + d + 1) ω' ≤ w (s + d + 1 + 1) ω' :=
        hgrow (s + d + 1) (by omega) ω' ω' hω' hω'
      have h3 : w (s + d + 1) ω' ≤ G * w (s + d + 1) ω' := Nat.le_mul_of_pos_left _ hG1'
      have heq : s + d + 1 + 1 = s + (d + 1) + 1 := by omega
      calc G * w s ω ≤ w (s + d + 1) ω' := h1
        _ ≤ G * w (s + d + 1) ω' := h3
        _ ≤ w (s + d + 1 + 1) ω' := h2
        _ = w (s + (d + 1) + 1) ω' := by rw [heq]
  -- Consequence: any candidate's radius at a strictly earlier (finer) scale is at most the
  -- buffer amount `w s ω' / G` built into the claiming point's own enlargement. Needs `s < m`
  -- (the target scale itself must be within the domain where `hgrow` is assumed).
  have hfuture : ∀ (t s : ℕ) (ω ω' : Ω), ω ∈ A₀ → ω' ∈ A₀ → t < s → s < m →
      w t ω ≤ w s ω' / G := by
    intro t s ω ω' hω hω' hts hsm
    obtain ⟨d, hd⟩ : ∃ d, s = t + d + 1 := ⟨s - t - 1, by omega⟩
    have h := hchain2 d t ω ω' hω hω' (by omega)
    rw [← hd] at h
    rw [Nat.le_div_iff_mul_le hG1', mul_comm]
    exact h
  exact hfuture

/-- **Rudolph's geometric-scales covering lemma.** Select pairwise disjoint orbit windows
whose centres lie in `A₀`, leaving measure at most `3 (G+1)/(Gm) + 1/G` uncovered within `A₀`.

The proof combines the one-third covering lemma over `m` scales. At each scale the true windows
occupy at least the fraction `G/(G+1)` of their enlarged windows. Disjointness across scales
bounds the total selected true-window measure by one. A global counting argument then bounds
the final candidate remainder by `3 (G+1)/(Gm)`; the enlargement shells contribute at most `1/G`.
This uses monotonicity of the remainders, not a geometric decay estimate at each step.

The growth condition compares only points of `A₀`; radii outside it may be padded independently.
The upper radius bound is global in the point variable. Both scale conditions apply only for
`s < m`: imposing uniform upper bounds and geometric growth over all natural scales would be
inconsistent for `G ≥ 2` on a nonempty domain with a positive initial radius. Both `m` and `G`
can increase to make the error arbitrarily small. -/
theorem vitali_cover_geometric [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ)
    (A₀ : Set Ω) (hA₀ : MeasurableSet A₀)
    (m : ℕ) (hm : 1 ≤ m) (w : ℕ → Ω → ℕ) (hw : ∀ s, Measurable (w s))
    (Bnd : ℕ) (hwB : ∀ s, s < m → ∀ ω, w s ω ≤ Bnd)
    (G : ℕ) (hG1 : 1 ≤ G)
    (hgrow : ∀ s, s < m → ∀ ω ω', ω ∈ A₀ → ω' ∈ A₀ → G * w s ω ≤ w (s + 1) ω') :
    ∃ (A : Set Ω) (scale : Ω → ℕ), A ⊆ A₀ ∧ MeasurableSet A ∧ Measurable scale ∧
      (∀ ω ∈ A, scale ω < m) ∧
      (A.PairwiseDisjoint fun ω =>
          (fun t => zIter σ t ω) '' Set.Icc (-(w (scale ω) ω : ℤ)) (w (scale ω) ω)) ∧
      μ (A₀ \ ⋃ ω ∈ A, (fun t => zIter σ t ω) '' Set.Icc (-(w (scale ω) ω : ℤ)) (w (scale ω) ω))
        ≤ ENNReal.ofReal (3 * ((G : ℝ) + 1) / (G * m) + 1 / G) := by
  classical
  have hG1' : 0 < G := hG1
  -- Window of radius `r` centred at `ω`.
  set win : ℕ → Ω → Set Ω := fun r ω =>
    (fun t => zIter σ t ω) '' Set.Icc (-(r : ℤ)) (r : ℤ) with hwindef
  -- Enlarged radius: own radius plus a `1/G`-buffer (`Nat` division).
  set renl : ℕ → Ω → ℕ := fun s ω => w s ω + w s ω / G with hrenldef
  have hrenl_meas : ∀ s, Measurable (renl s) :=
    fun s => (measurable_nat_to_nat (fun n => n + n / G)).comp (hw s)
  have hrenlB : ∀ s, s < m → ∀ ω, renl s ω ≤ Bnd + Bnd / G := by
    intro s hs ω
    have h1 : w s ω ≤ Bnd := hwB s hs ω
    have h2 : w s ω / G ≤ Bnd / G := Nat.div_le_div_right h1
    simp only [hrenldef]; omega
  have hrenl_ge : ∀ s ω, w s ω ≤ renl s ω := fun s ω => Nat.le_add_right _ _
  -- Earlier scales have uniformly smaller radii, including for different points of `A₀`.
  have hfuture := radius_le_div_of_earlier_scale A₀ m G hG1' w hgrow
  -- **Meeting-implies-bounded-distance.** If two windows (radii `a`, `b`, centres `x`, `y`) meet,
  -- `y` lies within `a + b` steps of `x`.
  have hmeet_dist : ∀ (a b : ℕ) (x y : Ω), ¬ Disjoint (win a x) (win b y) →
      ∃ u : ℤ, u ∈ Set.Icc (-(a : ℤ) - b) ((a : ℤ) + b) ∧ y = zIter σ u x := by
    intro a b x y hnd
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨z, hz1, hz2⟩ := hnd
    simp only [hwindef, Set.mem_image] at hz1 hz2
    obtain ⟨t1, ht1, hzt1⟩ := hz1
    obtain ⟨t2, ht2, hzt2⟩ := hz2
    refine ⟨t1 - t2, ?_, ?_⟩
    · simp only [Set.mem_Icc] at ht1 ht2 ⊢; omega
    · have e1 : zIter σ (-t2) z = y := by
        rw [← hzt2, ← zIter_add, show (-t2 + t2 : ℤ) = 0 from by ring, zIter_zero_apply]
      have e2 : zIter σ (-t2) z = zIter σ (t1 - t2) x := by
        rw [← hzt1, ← zIter_add]
        congr 1; ring
      rw [← e1, e2]
  -- **Safety.** If a claimed point `x` (radius `w s x` at scale `s`) has enlarged its window to
  -- `renl s x` and a candidate `y` lies *outside* that enlarged window, then `y`'s true window at
  -- any strictly finer scale `t < s` cannot meet `x`'s true window.
  have hsafe : ∀ (s t : ℕ) (x y : Ω), x ∈ A₀ → y ∈ A₀ → t < s → s < m → y ∉ win (renl s x) x →
      Disjoint (win (w t y) y) (win (w s x) x) := by
    intro s t x y hx hy hts hsm hy'
    by_contra hnd
    rw [disjoint_comm] at hnd
    obtain ⟨u, hu, hyu⟩ := hmeet_dist (w s x) (w t y) x y hnd
    apply hy'
    simp only [hwindef, Set.mem_image]
    refine ⟨u, ?_, hyu.symm⟩
    simp only [Set.mem_Icc] at hu ⊢
    have hbound : w t y ≤ w s x / G := hfuture t s y x hy hx hts hsm
    simp only [hrenldef]
    omega
  have ratio_lemma : ∀ (S : Set Ω), MeasurableSet S → ∀ (r0 : Ω → ℕ), Measurable r0 →
      (∀ ω, r0 ω ≤ Bnd) → S.PairwiseDisjoint (fun ω => win (r0 ω) ω) →
      G * μ (⋃ ω ∈ S, win (r0 ω + r0 ω / G) ω) ≤ (G + 1) * μ (⋃ ω ∈ S, win (r0 ω) ω) :=
    measure_variable_window_enlargement μ σ hσ Bnd G
  -- A window is monotone in its radius (nested `Icc`).
  have hwin_mono : ∀ (r r' : ℕ) (ω : Ω), r ≤ r' → win r ω ⊆ win r' ω := by
    intro r r' ω hrr'
    apply Set.image_mono
    intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    omega
  -- Every point lies in its own (any-radius) window, via shift `0`.
  have hself : ∀ (r : ℕ) (ω : Ω), ω ∈ win r ω := fun r ω => ⟨0, by simp, zIter_zero_apply σ ω⟩
  -- **The `m`-step construction.** `scaleAt k` is the scale processed at step `k` (coarsest
  -- first: `k = 0` handles `s = m-1`). `R k` is the remainder after `k` steps (`R 0 = A₀`);
  -- `Piece k` is the selection `vitali_cover_third` returns at step `k`, using the *enlarged*
  -- radius `renl (scaleAt k)`. `R (k+1)` excludes the enlarged windows of `Piece k`.
  set scaleAt : ℕ → ℕ := fun k => m - 1 - k with hscaleAtdef
  -- `scaleAt k` is always `< m` (`ℕ`-subtraction truncates at `0` for `k ≥ m - 1`), for *every*
  -- `k : ℕ`, not just `k < m` — this is what lets every downstream use of the now `s < m`-guarded
  -- `hwB`/`hgrow` (via `hrenlB`/`hsafe`) go through uniformly, even inside the unbounded `∀ k`
  -- statements below (`hMeas`, `hPieceSpec`, …), since `hm : 1 ≤ m` forces `m - 1 < m`.
  have hscaleAt_lt : ∀ k, scaleAt k < m := fun k => by simp only [hscaleAtdef]; omega
  obtain ⟨R, Piece, hR0, hRsucc', hMeas, hPieceSpec⟩ :=
    exists_orbit_window_ladder μ σ hσ A₀ hA₀ (fun k => renl (scaleAt k))
      (fun k => hrenl_meas (scaleAt k)) (Bnd + Bnd / G)
      (fun k => hrenlB (scaleAt k) (hscaleAt_lt k))
  -- `R` is monotone decreasing, and stays inside `A₀`.
  have hRstep : ∀ k, R (k + 1) ⊆ R k := by intro k; rw [hRsucc' k]; exact Set.sdiff_subset
  have hRanti : Antitone R := antitone_nat_of_succ_le hRstep
  have hRsubA0 : ∀ k, R k ⊆ A₀ := by
    intro k
    induction k with
    | zero => rw [hR0]
    | succ k ih => exact (hRstep k).trans ih
  -- A claimed piece's own points are excluded from all later remainders.
  have hPieceExcluded : ∀ k k', k < k' → Piece k' ⊆ R (k + 1) :=
    fun k k' hkk' => (hPieceSpec k').1.trans (hRanti hkk')
  -- Piece sets are pairwise disjoint (as sets, not just their windows).
  have hPieceSetDisjointLt : ∀ k k', k < k' → Disjoint (Piece k) (Piece k') := by
    intro k k' hkk'
    rw [Set.disjoint_left]
    intro y hyk hyk'
    have hyR1 : y ∈ R (k + 1) := hPieceExcluded k k' hkk' hyk'
    rw [hRsucc' k] at hyR1
    exact hyR1.2 (Set.mem_biUnion hyk (hself _ y))
  have hPieceSetDisjoint : ∀ k k', k ≠ k' → Disjoint (Piece k) (Piece k') := by
    intro k k' hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact hPieceSetDisjointLt k k' h
    · exact (hPieceSetDisjointLt k' k h).symm
  -- True windows are pairwise disjoint within a level (via the enlarged-window guarantee, nested).
  have hPieceTrueDisjoint : ∀ k, (Piece k).PairwiseDisjoint (fun ω => win (w (scaleAt k) ω) ω) := by
    intro k x hx y hy hxy
    exact ((hPieceSpec k).2.1 hx hy hxy).mono
      (hwin_mono _ _ x (hrenl_ge (scaleAt k) x)) (hwin_mono _ _ y (hrenl_ge (scaleAt k) y))
  -- **Cross-scale safety.** A later (finer-scale), still-available point's true window cannot
  -- meet an earlier (coarser-scale) claimed point's true window.
  have hCrossDisjoint : ∀ k k', k < k' → k' < m → ∀ x ∈ Piece k, ∀ y ∈ Piece k',
      Disjoint (win (w (scaleAt k') y) y) (win (w (scaleAt k) x) x) := by
    intro k k' hkk' hk'm x hx y hy
    have hyR1 : y ∈ R (k + 1) := hPieceExcluded k k' hkk' hy
    rw [hRsucc' k] at hyR1
    have hynotin : y ∉ win (renl (scaleAt k) x) x := fun hmem => hyR1.2 (Set.mem_biUnion hx hmem)
    have hxA0 : x ∈ A₀ := hRsubA0 k ((hPieceSpec k).1 hx)
    have hyA0 : y ∈ A₀ := hRsubA0 k' ((hPieceSpec k').1 hy)
    have hlt : scaleAt k' < scaleAt k := by simp only [hscaleAtdef]; omega
    exact hsafe (scaleAt k) (scaleAt k') x y hxA0 hyA0 hlt (hscaleAt_lt k) hynotin
  -- Assemble the final selected set and its scale assignment.
  set A : Set Ω := ⋃ k ∈ Finset.range m, Piece k with hAdef
  set scaleFn : Ω → ℕ := fun ω => ∑ k ∈ Finset.range m, (if ω ∈ Piece k then scaleAt k else 0)
    with hscaleFndef
  have hscaleFn_meas : Measurable scaleFn := by
    have hgen : ∀ (s : Finset ℕ),
        Measurable (fun ω => ∑ k ∈ s, (if ω ∈ Piece k then scaleAt k else 0)) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (Measurable.ite (hMeas a).2 measurable_const measurable_const).add ih
    simpa [hscaleFndef] using hgen (Finset.range m)
  have hscaleFn_eq : ∀ j, j < m → ∀ ω ∈ Piece j, scaleFn ω = scaleAt j := by
    intro j hjm ω hω
    simp only [hscaleFndef]
    rw [Finset.sum_eq_single j]
    · simp [hω]
    · intro k _ hkj
      have hnotk : ω ∉ Piece k :=
        fun hωk => (Set.disjoint_left.mp (hPieceSetDisjoint k j hkj) hωk) hω
      simp [hnotk]
    · intro hjnotin
      exact absurd (Finset.mem_range.mpr hjm) hjnotin
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Finset.measurableSet_biUnion _ (fun k _ => (hMeas k).2)
  have hAsubA0 : A ⊆ A₀ := by
    rw [hAdef]
    refine Set.iUnion₂_subset (fun k _ x hx => ?_)
    exact hRsubA0 k ((hPieceSpec k).1 hx)
  have hAscaleLt : ∀ ω ∈ A, scaleFn ω < m := by
    intro ω hω
    simp only [hAdef, Set.mem_iUnion, Finset.mem_range] at hω
    obtain ⟨j, hjm, hωj⟩ := hω
    rw [hscaleFn_eq j hjm ω hωj]
    simp only [hscaleAtdef]; omega
  have hAdisjoint : A.PairwiseDisjoint fun ω => win (w (scaleFn ω) ω) ω := by
    intro x hx y hy hxy
    simp only [hAdef, Set.mem_iUnion, Finset.mem_range] at hx hy
    obtain ⟨j, hjm, hxj⟩ := hx
    obtain ⟨j', hj'm, hyj'⟩ := hy
    have hsx : scaleFn x = scaleAt j := hscaleFn_eq j hjm x hxj
    have hsy : scaleFn y = scaleAt j' := hscaleFn_eq j' hj'm y hyj'
    change Disjoint (win (w (scaleFn x) x) x) (win (w (scaleFn y) y) y)
    rw [hsx, hsy]
    rcases lt_trichotomy j j' with h | h | h
    · exact (hCrossDisjoint j j' h hj'm x hxj y hyj').symm
    · subst h; exact hPieceTrueDisjoint j hxj hyj' hxy
    · exact hCrossDisjoint j' j h hjm y hyj' x hxj
  -- **Measure bookkeeping.** Per-level ratio (`ratio_lemma`) and the `vitali_cover_third`
  -- covering bound combine to bound `μ (R k)` in terms of the true-window measure at level `k`.
  have hRatioK : ∀ k, G * μ (⋃ ω ∈ Piece k, win (renl (scaleAt k) ω) ω)
      ≤ (G + 1) * μ (⋃ ω ∈ Piece k, win (w (scaleAt k) ω) ω) := by
    intro k
    have h := ratio_lemma (Piece k) (hMeas k).2 (w (scaleAt k)) (hw (scaleAt k))
      (fun ω => hwB (scaleAt k) (hscaleAt_lt k) ω) (hPieceTrueDisjoint k)
    simpa [hrenldef] using h
  have hRsubWin : ∀ k, R k ⊆ ⋃ ω ∈ R k, win (renl (scaleAt k) ω) ω :=
    fun k ω hω => Set.mem_biUnion hω (hself _ ω)
  have hRk_le3 : ∀ k, μ (R k) ≤ 3 * μ (⋃ ω ∈ Piece k, win (renl (scaleAt k) ω) ω) :=
    fun k => (measure_mono (hRsubWin k)).trans (hPieceSpec k).2.2
  have hTrueWindowCrossDisjointLt : ∀ k k', k < k' → k' < m →
      Disjoint (⋃ ω ∈ Piece k, win (w (scaleAt k) ω) ω)
        (⋃ ω ∈ Piece k', win (w (scaleAt k') ω) ω) := by
    intro k k' hkk' hk'm
    rw [Set.disjoint_iUnion₂_left]
    intro x hx
    rw [Set.disjoint_iUnion₂_right]
    intro y hy
    exact (hCrossDisjoint k k' hkk' hk'm x hx y hy).symm
  have hTrueWindowCrossDisjoint : ∀ k k', k < m → k' < m → k ≠ k' →
      Disjoint (⋃ ω ∈ Piece k, win (w (scaleAt k) ω) ω)
        (⋃ ω ∈ Piece k', win (w (scaleAt k') ω) ω) := by
    intro k k' hkm hk'm hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact hTrueWindowCrossDisjointLt k k' h hk'm
    · exact (hTrueWindowCrossDisjointLt k' k h hkm).symm
  have hTrueWindowUnion_eq : (⋃ ω ∈ A, win (w (scaleFn ω) ω) ω)
      = ⋃ k ∈ Finset.range m, (⋃ ω ∈ Piece k, win (w (scaleAt k) ω) ω) := by
    rw [hAdef]
    ext z
    constructor
    · intro hz
      obtain ⟨ω, hωA, hz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨k, hkm, hωk⟩ := Set.mem_iUnion₂.mp hωA
      have hseq : scaleFn ω = scaleAt k := hscaleFn_eq k (Finset.mem_range.mp hkm) ω hωk
      exact Set.mem_biUnion hkm (Set.mem_biUnion hωk (by rwa [hseq] at hz))
    · intro hz
      obtain ⟨k, hkm, hz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨ω, hωk, hz⟩ := Set.mem_iUnion₂.mp hz
      have hseq : scaleFn ω = scaleAt k := hscaleFn_eq k (Finset.mem_range.mp hkm) ω hωk
      exact Set.mem_biUnion (Set.mem_biUnion hkm hωk) (by rwa [hseq])
  refine ⟨A, scaleFn, hAsubA0, hAmeas, hscaleFn_meas, hAscaleLt, hAdisjoint, ?_⟩
  exact measure_finite_selection_error μ A₀ _ R
    (fun k => ⋃ ω ∈ Piece k, win (w (scaleAt k) ω) ω)
    (fun k => ⋃ ω ∈ Piece k, win (renl (scaleAt k) ω) ω)
    m G hm hG1' hR0 hRsucc' hRanti
    (fun k => measurableSet_iUnion_win σ (hMeas k).2 (w (scaleAt k)) (hw (scaleAt k)))
    (fun k => measurableSet_iUnion_win σ (hMeas k).2 (renl (scaleAt k)) (hrenl_meas (scaleAt k)))
    (fun k => Set.biUnion_mono (subset_refl _)
      (fun ω _ => hwin_mono _ _ ω (hrenl_ge (scaleAt k) ω)))
    hRatioK hRk_le3 hTrueWindowCrossDisjoint hTrueWindowUnion_eq

end MultiplicativeErgodic
