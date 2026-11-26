/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CutConnected
public import LeanPool.GraphMinor.GM07.BdChart

/-!
# A chart around the part of a cut surface over a tree

Let `T` be a component of the forest along which `Σ` is cut, with a point on `bd(Σ)`. By
`isPreconnected_preimage_tree`, `φ⁻¹(T)` is a connected part of one cuff of `Σ'`. It is not the
whole cuff, because `bd(Σ)` has points near `T` that are not on `T`. So `φ⁻¹(T)` is an arc, and it
has a half rectangle around it (`exists_tree_chart`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Complex GraphMinor.Surface GraphMinor.GM11

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- Near a point `z` of `bd(Σ)` there are points of `bd(Σ)` outside any finite set. -/
theorem exists_bd_near (hS : IsSurface S) {z : S} (hz : z ∈ bd S) {W F : Set S} (hW : IsOpen W)
  (hzW : z ∈ W) (hF : F.Finite) : ∃ y ∈ W ∩ bd S, y ∉ F := by
  obtain ⟨f, hf, h0, hi, -, hb, -⟩ := exists_cuffMark hS hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hW.preimage hf) 0
    (by rw [mem_preimage, h0]; exact hzW)
  have hpi := Real.pi_pos
  let r := min ε Real.pi
  have hr : 0 < r := lt_min hε hpi
  have hsub : Ioo 0 r ⊆ Ioc (-Real.pi) Real.pi := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2, min_le_right ε Real.pi]⟩
  obtain ⟨y, ⟨t, ht, rfl⟩, hy⟩ := ((Ioo_infinite hr).image (hi.mono hsub)).exists_notMem_finite hF
  refine ⟨f t, ⟨hball ?_, hb t (Ioc_subset_Icc_self (hsub ht))⟩, hy⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
  exact lt_of_lt_of_le ht.2 (min_le_left _ _)

/-- A connected subset of `bd(Σ)` meeting a closed part `C` of `bd(Σ)` with closed complement lies
in `C`. -/
theorem subset_of_clopen_bd {A C : Set S} (hA : IsPreconnected A) (hAb : A ⊆ bd S)
  (hC : IsClosed C) (hrest : IsClosed (bd S \ C)) {a : S} (haA : a ∈ A) (haC : a ∈ C) : A ⊆ C := by
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA C (bd S \ C) hC hrest (fun x hx => by
      by_cases h : x ∈ C
      · exact .inl h
      · exact .inr ⟨hAb hx, h⟩) (by
      ext x
      simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]
      tauto) with h | h
  · exact h
  · exact absurd haC (h haA).2

/-- **A chart around `φ⁻¹(T)`.** -/
theorem exists_tree_chart (hS : IsSurface S) {L : Drawing S} {φ : S' → S}
  (hJ : IsCutAlongGraph L S' φ) (hNo : NoArcs L) {T : Set S} (hT : IsPreconnected T)
    (hTc : IsClosed T) (hrest : IsClosed (L.U \ T)) (hTU : T ⊆ L.U)
    {z : S} (hzT : z ∈ T) (hzb : z ∈ bd S) {N : Set S} (hN : IsOpen N) (hTN : T ⊆ N) :
    ∃ (χ : ℂ → S') (x₁ x₂ δ : ℝ), IsBdChart χ x₁ x₂ δ ∧ (∀ w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ, φ (χ w) ∈ N)
      ∧ ∀ a ∈ φ ⁻¹' T, ∃ x ∈ Ioo x₁ x₂, χ (x : ℂ) = a := by
  classical
  have hY := hJ.isSurface
  have : CompactSpace S' := hY.1
  have : T2Space S' := hY.2.1
  have : T2Space S := hS.2.1
  have hcont := hJ.quotientMap.continuous
  have hpi := Real.pi_pos
  set A : Set S' := φ ⁻¹' T with hAdef
  have hAb : A ⊆ bd S' := fun x hx => by
    rw [← hJ.preimage_bd_union_U]
    exact .inr (hTU hx)
  have hAc : IsClosed A := hTc.preimage hcont
  have hAp : IsPreconnected A := isPreconnected_preimage_tree hS hJ hNo hT hTc hrest
  obtain ⟨a₀, ha₀⟩ := hJ.quotientMap.surjective z
  have ha₀A : a₀ ∈ A := by rw [hAdef, mem_preimage, ha₀]; exact hzT
  obtain ⟨f₀, hf₀, h00, -, -, hb₀, hr₀⟩ := exists_cuffMark hY (hAb ha₀A)
  have hIcc : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
  have hC₀c : IsClosed (f₀ '' Icc (-Real.pi) Real.pi) := (isCompact_Icc.image hf₀).isClosed
  have ha₀C : a₀ ∈ f₀ '' Icc (-Real.pi) Real.pi := ⟨0, hIcc, h00⟩
  have hAC₀ := subset_of_clopen_bd hAp hAb hC₀c hr₀ ha₀A ha₀C
  -- The arc is not the whole cuff.
  obtain ⟨y₀, hy₀C, hy₀A⟩ : ∃ y₀ ∈ f₀ '' Icc (-Real.pi) Real.pi, y₀ ∉ A := by
    by_contra hn
    push Not at hn
    have hE : IsClosed (φ '' (bd S' \ f₀ '' Icc (-Real.pi) Real.pi)) := hcont.isClosedMap _ hr₀
    have hW : IsOpen (φ '' (bd S' \ f₀ '' Icc (-Real.pi) Real.pi))ᶜ := hE.isOpen_compl
    have hzW : z ∈ (φ '' (bd S' \ f₀ '' Icc (-Real.pi) Real.pi))ᶜ := by
      rintro ⟨x, hx, he⟩
      exact hx.2 (hAC₀ (by rw [hAdef, mem_preimage, he]; exact hzT))
    obtain ⟨y, ⟨hyW, hyb⟩, hyV⟩ := exists_bd_near hS hzb hW hzW L.finite_V
    have hyU : y ∉ L.U := fun h => hyV (hJ.isProper ⟨hyb, h⟩)
    obtain ⟨x, rfl⟩ := hJ.quotientMap.surjective y
    have hxb : x ∈ bd S' := by
      rw [← hJ.preimage_bd_union_U]
      exact .inl hyb
    have hxC : x ∈ f₀ '' Icc (-Real.pi) Real.pi := by
      by_contra h
      exact hyW ⟨x, ⟨hxb, h⟩, rfl⟩
    exact hyU (hTU (hn x hxC))
  have hy₀b : y₀ ∈ bd S' := by
    obtain ⟨t, ht, rfl⟩ := hy₀C
    exact hb₀ t ht
  obtain ⟨f, hf, hfπ, hfi, hfs, hfb, hfr⟩ := exists_cuffSeam hY hy₀b
  have hC₀b : f₀ '' Icc (-Real.pi) Real.pi ⊆ bd S' := by
    rintro _ ⟨t, ht, rfl⟩
    exact hb₀ t ht
  have hC₀p : IsPreconnected (f₀ '' Icc (-Real.pi) Real.pi) := isPreconnected_Icc.image f₀
    hf₀.continuousOn
  have hCc : IsClosed (f '' Icc (-Real.pi) Real.pi) := (isCompact_Icc.image hf).isClosed
  have hπ : Real.pi ∈ Icc (-Real.pi) Real.pi := ⟨by linarith, le_rfl⟩
  have hAC : A ⊆ f '' Icc (-Real.pi) Real.pi := hAC₀.trans (subset_of_clopen_bd hC₀p hC₀b hCc hfr
    hy₀C (show y₀ ∈ f '' Icc (-Real.pi) Real.pi from ⟨Real.pi, hπ, hfπ⟩))
  -- The parameters of the arc.
  let I : Set ℝ := Icc (-Real.pi) Real.pi ∩ f ⁻¹' A
  have hIc : IsCompact I := isCompact_Icc.inter_right (hAc.preimage hf)
  have hIo : I ⊆ Ioo (-Real.pi) Real.pi := fun t ht => by
    refine ⟨lt_of_le_of_ne ht.1.1 fun h => ?_, lt_of_le_of_ne ht.1.2 fun h => ?_⟩
    · have h2 : f t = y₀ := by rw [← h, hfs, hfπ]
      exact hy₀A (h2 ▸ ht.2)
    · have h2 : f t = y₀ := by rw [h, hfπ]
      exact hy₀A (h2 ▸ ht.2)
  have hIin : InjOn f I := hfi.mono (show I ⊆ Ioc (-Real.pi) Real.pi from fun t ht => ⟨(hIo ht).1,
    (hIo ht).2.le⟩)
  have hIp : IsPreconnected I := by
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv hsub hd
    have hUc : IsCompact (I ∩ u) := hIc.inter_right hu
    have hVc : IsCompact (I ∩ v) := hIc.inter_right hv
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hAp (f '' (I ∩ u)) (f '' (I ∩ v))
      (hUc.image hf).isClosed (hVc.image hf).isClosed (fun a ha => by
        obtain ⟨t, ht, rfl⟩ := hAC ha
        have htI : t ∈ I := ⟨ht, ha⟩
        rcases hsub htI with h | h
        · exact .inl ⟨t, ⟨htI, h⟩, rfl⟩
        · exact .inr ⟨t, ⟨htI, h⟩, rfl⟩) (by
        ext a
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
        have h1 : t' = t := hIin ht'.1 ht.1 he
        have : t ∈ I ∩ (u ∩ v) := ⟨ht.1, ht.2, h1 ▸ ht'.2⟩
        rw [hd] at this
        exact this) with h | h
    · refine .inl fun t ht => ?_
      obtain ⟨t', ht', he⟩ := h ht.2
      rw [← hIin ht'.1 ht he]
      exact ht'.2
    · refine .inr fun t ht => ?_
      obtain ⟨t', ht', he⟩ := h ht.2
      rw [← hIin ht'.1 ht he]
      exact ht'.2
  have hINe : I.Nonempty := by
    obtain ⟨t, ht, he⟩ := hAC ha₀A
    exact ⟨t, ht, by rw [mem_preimage, he]; exact ha₀A⟩
  obtain ⟨c₀, hc₀, hc₀l⟩ := hIc.exists_isLeast hINe
  obtain ⟨d₀, hd₀, hd₀l⟩ := hIc.exists_isGreatest hINe
  have hsegI : Icc c₀ d₀ ⊆ I := hIp.Icc_subset hc₀ hd₀
  have hG : IsOpen ((φ ∘ f) ⁻¹' N) := hN.preimage (hcont.comp hf)
  have hgN : ∀ t ∈ I, φ (f t) ∈ N := fun t ht => hTN ht.2
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp hG c₀ (hgN _ hc₀)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.mp hG d₀ (hgN _ hd₀)
  have hc₀π := hIo hc₀
  have hd₀π := hIo hd₀
  have hcd₀ : c₀ ≤ d₀ := hc₀l hd₀
  let c := max (c₀ - ε₁ / 2) ((c₀ - Real.pi) / 2)
  let d := min (d₀ + ε₂ / 2) ((d₀ + Real.pi) / 2)
  have hc1 : c < c₀ := max_lt (by linarith) (by linarith [hc₀π.1])
  have hc2 : c₀ - ε₁ / 2 ≤ c := le_max_left _ _
  have hc3 : (c₀ - Real.pi) / 2 ≤ c := le_max_right _ _
  have hd1 : d₀ < d := lt_min (by linarith) (by linarith [hd₀π.2])
  have hd2 : d ≤ d₀ + ε₂ / 2 := min_le_left _ _
  have hd3 : d ≤ (d₀ + Real.pi) / 2 := min_le_right _ _
  have hcd : c < d := by linarith
  let a := (c - Real.pi) / 2
  let b := (d + Real.pi) / 2
  have ha1 : -Real.pi < a := by simp only [a]; linarith [hc₀π.1]
  have ha2 : a < c := by simp only [a]; linarith [hc₀π.1]
  have hb1 : b < Real.pi := by simp only [b]; linarith [hd₀π.2]
  have hb2 : d < b := by simp only [b]; linarith [hd₀π.2]
  have hsub : Icc a b ⊆ Ioc (-Real.pi) Real.pi := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hrest' : IsClosed (bd S' \ f '' Ioo a b) := by
    have he : bd S' \ f '' Ioo a b = (bd S' \ f '' Icc (-Real.pi) Real.pi) ∪ f '' (Icc
      (-Real.pi) Real.pi \ Ioo a b) := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h3 : x ∈ f '' Icc (-Real.pi) Real.pi
        · obtain ⟨t, ht, rfl⟩ := h3
          exact .inr ⟨t, ⟨ht, fun h => h2 ⟨t, h, rfl⟩⟩, rfl⟩
        · exact .inl ⟨h1, h3⟩
      · rintro (h | ⟨t, ht, rfl⟩)
        · exact ⟨h.1, fun h' => h.2 (image_mono
            (Ioo_subset_Icc_self.trans (hsub.trans Ioc_subset_Icc_self)) h')⟩
        · refine ⟨hfb t ht.1, ?_⟩
          rintro ⟨t', ht', he⟩
          have ht'I : t' ∈ Ioc (-Real.pi) Real.pi := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
          by_cases h1 : t = -Real.pi
          · rw [h1, hfs] at he
            have := hfi ht'I ⟨by linarith, le_rfl⟩ he
            linarith [ht'.2]
          · have := hfi ht'I ⟨lt_of_le_of_ne ht.1.1 (Ne.symm h1), ht.1.2⟩ he
            exact ht.2 (this ▸ ht')
    rw [he]
    exact hfr.union (((isCompact_Icc.diff isOpen_Ioo).image hf).isClosed)
  have hZ : IsClosed (φ ⁻¹' Nᶜ) := hN.isClosed_compl.preimage hcont
  have hZg : ∀ u ∈ Icc c d, f u ∉ φ ⁻¹' Nᶜ := fun u hu h => by
    refine h ?_
    by_cases h1 : u < c₀
    · refine hb₁ ?_
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1]
    · by_cases h2 : d₀ < u
      · refine hb₂ ?_
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.2]
      · exact hgN u (hsegI ⟨not_lt.mp h1, not_lt.mp h2⟩)
  obtain ⟨χ, x₁, x₂, δ, hχ, hz', hA⟩ := exists_bd_chart hY hf (by linarith : a < c) hcd hb2
    (hfi.mono hsub) (fun u hu => hfb u ⟨(hsub hu).1.le, (hsub hu).2⟩) hrest' hZ hZg
  refine ⟨χ, x₁, x₂, δ, hχ, fun w hw => ?_, fun a' ha' => ?_⟩
  · by_contra h
    exact hz' w hw h
  · obtain ⟨t, ht, rfl⟩ := hAC ha'
    have htI : t ∈ I := ⟨ht, ha'⟩
    exact hA t ⟨by linarith [hc₀l htI], by linarith [hd₀l htI]⟩

end GraphMinor.GM07
