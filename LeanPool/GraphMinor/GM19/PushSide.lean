/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PushOff

/-!
# Pushing a closed set off a disc across its boundary

Here is a form of `GraphMinor.Surface.push_off` for a disc `D` and a line `L` in the boundary of
`D`, with
the same proof. A closed set that meets `L` only in its ends moves off `D`. The set `Z` that must
stay
fixed meets `D` only in `L`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

universe u

theorem push_off_side {S : Type u} [TopologicalSpace S] (hS : IsSurface S) {ι : Type} [Finite ι]
    {N Z : Set S} {D L : ι → Set S} (hN : N.Finite) (hZ : IsClosed Z) (hD : ∀ i, IsClosedDisc (D i))
    (hL : ∀ i, ∃ a b, IsLineWithEnds (L i) a b ∧ D i ∩ N = {a, b} ∧ L i ⊆ discBd (D i) ∧
      D i ∩ bd S ⊆ N)
    (hDD : ∀ i j, i ≠ j → D i ∩ D j ⊆ N) (hDZ : ∀ i, D i ∩ Z ⊆ L i)
    {F : Set S} (hF : IsOArc F) (hFZ : F ∩ Z ⊆ N) (hFL : ∀ i, F ∩ L i ⊆ N) :
    ∃ h : S ≃ₜ S, (∀ n ∈ N, h n = n) ∧ (h '' F) ∩ Z ⊆ N ∧ ∀ i, (h '' F) ∩ D i ⊆ N := by
  classical
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  obtain ⟨T, _, j, K, hT, hj, hK, hu, hi⟩ := exists_capAll S hS
  obtain ⟨hTc, hTt, hTi⟩ := id hT
  obtain ⟨φ⟩ := id hF
  have : Nonempty S := ⟨(φ 1).1⟩
  have := Fintype.ofFinite ι
  have hji := hj.injective
  obtain ⟨j', hjc, hjl⟩ := exists_inv_of_compactOn isCompact_univ hj.continuous.continuousOn
    hji.injOn
  have hdisc : ∀ {E : Set S}, IsClosedDisc E → IsClosedDisc (j '' E) ∧ discBd (j '' E)
    = j '' discBd E :=
    fun hE => hE.image hj.continuous.continuousOn (hjc.mono (image_mono (subset_univ _)))
      (hjl.mono (subset_univ _))
  let Z' : Set T := K ∪ (j '' N ∪ j '' Z)
  have hZ' : IsClosed Z' := hK.union ((hj.isClosedMap _ hN.isClosed).union (hj.isClosedMap _ hZ))
  have hFc : IsClosed (j '' F) := hj.isClosedMap _ hF.isCompact.isClosed
  have main : ∀ s : Finset ι, ∃ h : T ≃ₜ T, (∀ y ∈ Z', h y = y) ∧ (∀ k, k ∉ s → ∀ y ∈ j '' D k, h y
    = y) ∧
      ∀ k ∈ s, h '' (j '' F) ∩ j '' D k ⊆ j '' N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨Homeomorph.refl T, fun _ _ => rfl, fun _ _ _ _ => rfl, fun k hk => absurd hk (by simp)⟩
    | insert i s his ih =>
      obtain ⟨h, h1, h2, h3⟩ := ih
      obtain ⟨a, b, hLi, hDN, hLb, c2⟩ := hL i
      have hLD : L i ⊆ D i := hLb.trans (discBd_subset _)
      have haL : a ∈ L i := by
        obtain ⟨f, h4, -⟩ := hLi
        exact h4 ▸ (f 0).2
      have hbL : b ∈ L i := by
        obtain ⟨f, -, h4⟩ := hLi
        exact h4 ▸ (f 1).2
      have haN : a ∈ D i ∩ N := hDN ▸ Or.inl rfl
      have hbN : b ∈ D i ∩ N := hDN ▸ Or.inr rfl
      have hN' : D i ∩ N ⊆ L i := by
        rw [hDN]
        rintro _ (rfl | rfl)
        · exact haL
        · exact hbL
      let Y : Set T := Z' ∪ ⋃ k ∈ {k | k ≠ i}, j '' D k
      have hY : IsClosed Y := hZ'.union ((Set.toFinite _).isClosed_biUnion fun k _ =>
        hj.isClosedMap _ (hD k).isClosed)
      obtain ⟨d1, d2⟩ := hdisc (hD i)
      have hYN : ∀ x ∈ Y, ∀ y ∈ D i, x = j y → y ∈ L i ∨ y ∈ bd S := by
        rintro x (hx | hx) y hy rfl
        · rcases hx with hx | ⟨w, hw, he⟩ | ⟨w, hw, he⟩
          · obtain ⟨w, hw, he⟩ : j y ∈ j '' bd S := hi.1 ▸ ⟨⟨y, rfl⟩, hx⟩
            exact .inr (hji he ▸ hw)
          · exact .inl (hN' ⟨hy, hji he ▸ hw⟩)
          · exact .inl (hDZ i ⟨hy, hji he ▸ hw⟩)
        · obtain ⟨k, hk, w, hw, he⟩ := mem_iUnion₂.mp hx
          exact .inl (hN' ⟨hy, hDD i k hk.symm ⟨hy, hji he ▸ hw⟩⟩)
      have hline : IsLineWithEnds (j '' L i) (j a) (j b) := by
        obtain ⟨f, h4, h5⟩ := hLi
        refine ⟨f.trans (hj.isEmbedding.homeomorphImage (L i)), ?_, ?_⟩
        · exact congrArg j h4
        · exact congrArg j h5
      have hC : IsClosed (h '' (j '' F)) := h.isClosed_image.mpr hFc
      obtain ⟨h₂, g1, g2⟩ := push_disc (T := T) hTi (D := j '' D i) (L := j '' L i) (Y := Y)
        (C := h '' (j '' F)) d1 hline (image_mono hLD)
        (by
          left
          refine ⟨?_, ?_⟩
          · rw [d2]
            exact image_mono hLb
          · rintro x ⟨hx, y, hy, rfl⟩
            refine mem_image_of_mem j ?_
            rcases hYN _ hx y hy rfl with h4 | h4
            · exact h4
            · have h5 : y ∈ D i ∩ N := ⟨hy, c2 ⟨hy, h4⟩⟩
              rw [hDN] at h5
              rcases h5 with rfl | rfl
              · exact haL
              · exact hbL)
        (by rw [d2]; exact mem_image_of_mem j (hLb haL))
        (by rw [d2]; exact mem_image_of_mem j (hLb hbL))
        hY (.inl (.inr (.inl (mem_image_of_mem j haN.2)))) (.inl (.inr (.inl
          (mem_image_of_mem j hbN.2))))
        hC
        (by
          rintro _ ⟨⟨_, ⟨y, hy, rfl⟩, rfl⟩, w, hw, he⟩
          have h4 : h (j w) = j w := h2 i (by simpa using his) _ (mem_image_of_mem j (hLD hw))
          have h5 : j w = j y := h.injective (h4.trans he)
          have h6 : w = y := hji h5
          subst h6
          have h7 : w ∈ D i ∩ N := ⟨hLD hw, hFL i ⟨hy, hw⟩⟩
          rw [hDN] at h7
          rw [← he]
          rcases h7 with rfl | rfl
          · exact .inl rfl
          · exact .inr rfl)
      refine ⟨h.trans h₂, fun y hy => ?_, fun k hk y hy => ?_, fun k hk => ?_⟩
      · change h₂ (h y) = y
        rw [h1 y hy, g1 y (.inl hy)]
      · have hk1 : k ≠ i := fun he => hk (by simp [he])
        have hk2 : k ∉ s := fun he => hk (by simp [he])
        change h₂ (h y) = y
        rw [h2 k hk2 y hy, g1 y (.inr (mem_iUnion₂.mpr ⟨k, hk1, hy⟩))]
      · rintro _ ⟨⟨_, ⟨y, hy, rfl⟩, rfl⟩, hx⟩
        by_cases hki : k = i
        · subst hki
          have h4 : (h.trans h₂) (j y) ∈ h₂ '' (h '' (j '' F)) ∩ j '' D k :=
            ⟨⟨_, ⟨_, mem_image_of_mem j hy, rfl⟩, rfl⟩, hx⟩
          rcases g2 h4 with h5 | h5
          · rw [h5]
            exact mem_image_of_mem j haN.2
          · rw [h5]
            exact mem_image_of_mem j hbN.2
        · have hks : k ∈ s := by simpa [hki] using hk
          have h4 : h₂ (h₂ (h (j y))) = h₂ (h (j y)) := g1 _ (.inr (mem_iUnion₂.mpr ⟨k, hki, hx⟩))
          have h5 : h₂ (h (j y)) = h (j y) := h₂.injective h4
          change h₂ (h (j y)) ∈ _ at hx
          change h₂ (h (j y)) ∈ _
          rw [h5] at hx ⊢
          exact h3 k hks ⟨⟨_, mem_image_of_mem j hy, rfl⟩, hx⟩
  obtain ⟨H, f1, -, f3⟩ := main Finset.univ
  have hfixK : ∀ y ∈ K, H y = y := fun y hy => f1 y (.inl hy)
  have hran : ∀ x, x ∈ range j ↔ H x ∈ range j := by
    intro x
    constructor
    · intro hx
      by_contra hcon
      have h1 : H x ∈ K := (hu ▸ mem_univ (H x) : H x ∈ range j ∪ K).resolve_left hcon
      have h2 := H.injective (hfixK _ h1)
      exact hcon (by rw [h2]; exact hx)
    · intro hx
      by_contra hcon
      have h1 : x ∈ K := (hu ▸ mem_univ x : x ∈ range j ∪ K).resolve_left hcon
      exact hcon (hfixK x h1 ▸ hx)
  let e : S ≃ₜ range j := hj.isEmbedding.toHomeomorph
  let h : S ≃ₜ S := e.trans ((H.subtype hran).trans e.symm)
  have hjh : ∀ x, j (h x) = H (j x) := fun x => by
    have h1 : e (h x) = (H.subtype hran) (e x) := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hfixN : ∀ n ∈ N, h n = n := fun n hn =>
    hji ((hjh n).trans (f1 _ (.inr (.inl (mem_image_of_mem j hn)))))
  refine ⟨h, hfixN, ?_, fun i => ?_⟩
  · rintro _ ⟨⟨y, hy, rfl⟩, hz⟩
    have h1 : H (j (h y)) = j (h y) := f1 _ (.inr (.inr (mem_image_of_mem j hz)))
    rw [hjh] at h1
    have h2 : H (j y) = j y := H.injective h1
    have h3 : h y = y := hji ((hjh y).trans h2)
    rw [h3] at hz ⊢
    exact hFZ ⟨hy, hz⟩
  · rintro _ ⟨⟨y, hy, rfl⟩, hz⟩
    obtain ⟨w, hw, he⟩ := f3 i (Finset.mem_univ i)
      ⟨⟨j y, mem_image_of_mem j hy, (hjh y).symm⟩, mem_image_of_mem j hz⟩
    exact hji he ▸ hw

end GraphMinor.GM19
