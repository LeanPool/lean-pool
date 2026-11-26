/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4ThinPlaneDisc
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Transferring a thin disc through an arc chart

The empty discs in XII (4.3), page 250, follow from a thin disc
around a normal arc. In a strip chart, the arc is a real interval.
Rescale that interval to `[-1, 1]` and apply the plane construction.
The chart is injective, so it carries the resulting disc and its
two boundary ends back to the surface without new intersections.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric Complex

/-- A thin disc around an arc in strip coordinates, avoiding a
closed set except at the arc's two ends. -/
theorem exists_thin_disc_of_strip_arc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {O : Set ℂ} {K : ℂ → S} (hO : IsOpen O)
    (hKc : ContinuousOn K O) (hKi : InjOn K O)
    {a : unitInterval → S} (ha : IsArcMap a)
    {θ : unitInterval → ℝ} (hθc : Continuous θ) (hθm : StrictMono θ)
    (hθK : ∀ t, (θ t : ℂ) ∈ O ∧ K (θ t) = a t)
    {B : Set S} (hB : IsClosed B) (hleft : a 0 ∈ B) (hright : a 1 ∈ B)
    (hmeet : range a ∩ B ⊆ {a 0, a 1}) :
    ∃ D : Set S, IsClosedDisc D ∧ D ∩ B = {a 0, a 1} ∧
      ({a 0, a 1} : Set S) ⊆ discBd D ∧ range a ⊆ D := by
  let s : ℝ := (θ 1 - θ 0) / 2
  have hs : 0 < s := half_pos (sub_pos.mpr (hθm (show (0 : unitInterval) < 1 by norm_num)))
  let A : ℂ → ℂ := fun z => (θ 0 : ℂ) + (s : ℂ) * (z + 1)
  have hAc : Continuous A := by fun_prop
  have hAi : Function.Injective A := by
    intro z w h
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    exact add_right_cancel (mul_left_cancel₀ hs' (add_left_cancel h))
  have hAleft : A (-1) = (θ 0 : ℂ) := by simp [A]
  have hAright : A 1 = (θ 1 : ℂ) := by
    dsimp only [A, s]
    push_cast
    ring
  have hseg : ∀ z ∈ Complex.ofReal '' Icc (-1 : ℝ) 1,
      ∃ t : unitInterval, A z = (θ t : ℂ) := by
    rintro _ ⟨x, hx, rfl⟩
    have hn : θ 0 + s * (x + 1) ∈ Icc (θ 0) (θ 1) := by
      have hlo : 0 ≤ x + 1 := by linarith [hx.1]
      have hhi : x + 1 ≤ 2 := by linarith [hx.2]
      have heq : s * 2 = θ 1 - θ 0 := by dsimp only [s]; ring
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg hs.le hlo)
      · have hmul := mul_le_mul_of_nonneg_left hhi hs.le
        rw [heq] at hmul
        linarith
    have himage := hθc.image_Icc_of_strictMono (a := 0) (b := 1) hθm
    have hn' : θ 0 + s * (x + 1) ∈ θ '' Icc (0 : unitInterval) 1 := by
      rw [himage]
      exact hn
    obtain ⟨t, _, ht⟩ := hn'
    refine ⟨t, ?_⟩
    dsimp only [A]
    exact_mod_cast ht.symm
  let G : Set ℂ := O ∩ K ⁻¹' Bᶜ
  have hG : IsOpen G := hKc.isOpen_inter_preimage hO hB.isOpen_compl
  let O' : Set ℂ := A ⁻¹' O
  let B' : Set ℂ := (A ⁻¹' G)ᶜ
  have hO' : IsOpen O' := hO.preimage hAc
  have hB' : IsClosed B' := (hG.preimage hAc).isClosed_compl
  have hsegO : Complex.ofReal '' Icc (-1 : ℝ) 1 ⊆ O' := by
    intro z hz
    obtain ⟨t, ht⟩ := hseg z hz
    change A z ∈ O
    rw [ht]
    exact (hθK t).1
  have hB'seg : B' ∩ (Complex.ofReal '' Icc (-1 : ℝ) 1) ⊆ {-1, 1} := by
    rintro z ⟨hzB, hzseg⟩
    obtain ⟨t, ht⟩ := hseg z hzseg
    have hatB : a t ∈ B := by
      by_contra hn
      apply hzB
      exact ⟨ht ▸ (hθK t).1, by change K (A z) ∉ B; rw [ht, (hθK t).2]; exact hn⟩
    have hend := hmeet ⟨mem_range_self t, hatB⟩
    rcases hend with he | he
    · have ht0 : t = 0 := ha.2 he
      exact Or.inl (hAi (ht.trans (ht0 ▸ hAleft.symm)))
    · have ht1 : t = 1 := ha.2 (Set.mem_singleton_iff.mp he)
      exact Or.inr (Set.mem_singleton_iff.mpr (hAi (ht.trans (ht1 ▸ hAright.symm))))
  have hB'left : (-1 : ℂ) ∈ B' := by
    intro h
    exact h.2 (by rw [hAleft, (hθK 0).2]; exact hleft)
  have hB'right : (1 : ℂ) ∈ B' := by
    intro h
    exact h.2 (by rw [hAright, (hθK 1).2]; exact hright)
  obtain ⟨D, hD, hDO, hDB, hends, hsegD⟩ := exists_thin_plane_disc hO' hB' hsegO hB'seg hB'left
    hB'right
  let f : ℂ → S := fun z => K (A z)
  have hfc : ContinuousOn f O' := hKc.comp hAc.continuousOn (fun _ hx => hx)
  have hfi : InjOn f O' := by
    intro z hz w hw he
    exact hAi (hKi hz hw he)
  have himage := isClosedDisc_image_injOn hD hD.isCompact (hfc.mono hDO) (hfi.mono hDO)
  have hfleft : f (-1) = a 0 := by dsimp only [f]; rw [hAleft, (hθK 0).2]
  have hfright : f 1 = a 1 := by dsimp only [f]; rw [hAright, (hθK 1).2]
  have hmem : ∀ z ∈ D, f z ∈ B → z ∈ B' := by
    intro z _ hzB hzG
    exact hzG.2 hzB
  refine ⟨f '' D, himage.1, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro w ⟨⟨z, hzD, rfl⟩, hzB⟩
      have hzends : z ∈ ({-1, 1} : Set ℂ) := hDB.subset ⟨hzD, hmem z hzD hzB⟩
      rcases hzends with rfl | hzends
      · exact Or.inl hfleft
      · have hz1 := Set.mem_singleton_iff.mp hzends
        subst z
        exact Or.inr (Set.mem_singleton_iff.mpr hfright)
    · intro w hw
      rcases hw with rfl | hw
      · exact ⟨⟨-1, discBd_subset D (hends (by simp)), hfleft⟩, hleft⟩
      · have hw1 := Set.mem_singleton_iff.mp hw
        subst w
        exact ⟨⟨1, discBd_subset D (hends (by simp)), hfright⟩, hright⟩
  · rw [himage.2]
    intro w hw
    rcases hw with rfl | hw
    · exact ⟨-1, hends (by simp), hfleft⟩
    · have hw1 := Set.mem_singleton_iff.mp hw
      subst w
      exact ⟨1, hends (by simp), hfright⟩
  · rintro _ ⟨t, rfl⟩
    let x : ℝ := (θ t - θ 0) / s - 1
    have htlo : θ 0 ≤ θ t := hθm.monotone (unitInterval.nonneg t)
    have hthi : θ t ≤ θ 1 := hθm.monotone (unitInterval.le_one t)
    have hst : s * 2 = θ 1 - θ 0 := by dsimp only [s]; ring
    have hx : x ∈ Icc (-1 : ℝ) 1 := by
      dsimp only [x]
      constructor
      · have hdiv := div_nonneg (sub_nonneg.mpr htlo) hs.le
        linarith
      · have hdiv : (θ t - θ 0) / s ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
        linarith
    refine ⟨(x : ℂ), hsegD ⟨x, hx, rfl⟩, ?_⟩
    have hAx : A (x : ℂ) = (θ t : ℂ) := by
      have hreal : θ 0 + s * (x + 1) = θ t := by
        dsimp only [x]
        field_simp
        ring
      dsimp only [A]
      exact_mod_cast hreal
    exact (congrArg K hAx).trans (hθK t).2

end GraphMinor.GM12
