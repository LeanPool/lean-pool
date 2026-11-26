/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutArc
public import LeanPool.GraphMinor.Surface.PasteModel

/-!
# Two closed pieces of a surface that meet along an `O`-arc

Let a connected surface be the union of two closed sets `T` and `Z`, and let an `O`-arc `C` in its
interior be a component of `T ∩ Z`, with points of both `T` and `Z` outside the other piece
arbitrarily near each point of `C`.
We show that `T` is a surface near `C`, with `C` on its boundary (`side_manifold`).

The proof cuts the surface along `C`. Near a lifted point the cut surface is a half disc. The half
disc without its edge is connected, so it lies on one side, and so each lifted point belongs to one
side only. Each point of `C` has two lifts, one on each side. This shows that a neighbourhood of `C`
in `T` is an open set of the cut surface.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Near a point of a surface there is a connected open set of interior points that is dense in a
neighbourhood of the point. -/
theorem IsManifoldPoint.exists_half {x : S} (hx : IsManifoldPoint x) {N : Set S} (hN : IsOpen N)
  (hxN : x ∈ N) :
    ∃ V P : Set S, IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧ P ⊆ V ∧ IsPreconnected P ∧
      (∀ y ∈ P, IsInteriorPoint y) ∧ V ⊆ closure P := by
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hm, hm', hl, hr⟩ := hx.exists_chart
  have hA : U ∩ N ∈ 𝓝 (k (j x)) := by
    rw [hl hxU]
    exact (hU.inter hN).mem_nhds ⟨hxU, hxN⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hk _ (hm hxU) hA)
  obtain ⟨ρ', hρ', hball'⟩ := Metric.isOpen_iff.mp hO _ (hm hxU).1
  let r : ℝ := min ρ ρ'
  have hr0 : 0 < r := lt_min hρ hρ'
  have sub1 : Metric.ball (j x) r ⊆ Metric.ball (j x) ρ := Metric.ball_subset_ball (min_le_left _ _)
  have sub2 : Metric.ball (j x) r ⊆ O := (Metric.ball_subset_ball (min_le_right _ _)).trans hball'
  let B : Set ℂ := Metric.ball (j x) r ∩ {z | 0 < z.re}
  have hBO : B ⊆ O ∩ halfPlane := fun z hz => ⟨sub2 hz.1, le_of_lt (show (0 : ℝ) < z.re from hz.2)⟩
  have hBc : Convex ℝ B := (convex_ball _ _).inter (convex_halfSpace_gt Complex.reLm.isLinear 0)
  have hV : IsOpen (U ∩ j ⁻¹' Metric.ball (j x) r) := hj.isOpen_inter_preimage hU Metric.isOpen_ball
  have hint : ∀ z ∈ B, IsInteriorPoint (k z) := fun z hz => by
    have h1 : k z ∈ U := hm' (hBO hz)
    refine isInteriorPoint_of_chart hU hO hj hk hm hm' hl hr h1 ?_
    rw [hr (hBO hz)]
    exact hz.2
  refine ⟨_, k '' B, hV, ⟨hxU, Metric.mem_ball_self hr0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨h1, h2⟩
    have h3 := hball ⟨sub1 h2, hm h1⟩
    rw [mem_preimage, hl h1] at h3
    exact h3.2
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨hm' (hBO hz), ?_⟩
    rw [mem_preimage, hr (hBO hz)]
    exact hz.1
  · exact hBc.isPreconnected.image _ (hk.mono hBO)
  · rintro _ ⟨z, hz, rfl⟩
    exact hint z hz
  · rintro y ⟨h1, h2⟩
    have hz : j y ∈ O ∩ halfPlane := hm h1
    have h3 : j y ∈ closure B := by
      have ht : Filter.Tendsto (fun ε : ℝ => j y + (ε : ℂ)) (𝓝[>] 0) (𝓝 (j y)) := by
        have : Continuous fun ε : ℝ => j y + (ε : ℂ) := by fun_prop
        have h4 := this.tendsto 0
        simp only [Complex.ofReal_zero, add_zero] at h4
        exact h4.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht ?_
      have h5 := ht (Metric.isOpen_ball.mem_nhds h2)
      filter_upwards [h5, self_mem_nhdsWithin] with ε h6 h7
      refine ⟨h6, ?_⟩
      have h8 : 0 ≤ (j y).re := hz.2
      have h9 : 0 < ε := h7
      change 0 < (j y + (ε : ℂ)).re
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have h4 := (hk (j y) hz).mono hBO
    have := h4.mem_closure_image h3
    rwa [hl h1] at this

/-- Two closed pieces of a surface that meet along an `O`-arc `C`, and perhaps in a closed set `D`
away from `C`. Near `C`, the piece `T` is a surface with `C` on its boundary. -/
theorem side_manifold [ConnectedSpace S] (hS : IsSurface S) {T Z C D : Set S} (hT : IsClosed T)
  (hZ : IsClosed Z) (hu : T ∪ Z = univ)
    (hO : IsOArc C) (hb : Disjoint C (bd S)) (hCT : C ⊆ T) (hD : IsClosed D) (hm : T ∩ Z = C ∪ D)
      (hCD : Disjoint C D)
    (h1 : ∀ x ∈ C, x ∈ closure (T \ Z)) (h2 : ∀ x ∈ C, x ∈ closure (Z \ T)) {x : S} (hx : x ∈ C) :
    IsManifoldPoint (⟨x, hCT hx⟩ : T) ∧ (⟨x, hCT hx⟩ : T) ∈ bd T := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, -⟩ := exists_cut_loop hS hO hb
  have hcY : CompactSpace Y := hY.1
  have hcl : IsClosedMap ψ := hψ.1.isClosedMap
  have hsurj := hψ.2.1
  have hc := hψ.1
  have hbdC : ψ ⁻¹' C ⊆ bd Y := hψ.2.2.2.2
  have hTc : T \ Z = Zᶜ := by
    ext z
    have h3 : z ∈ T ∪ Z := hu ▸ mem_univ z
    exact ⟨fun h => h.2, fun h => ⟨h3.resolve_right h, h⟩⟩
  have hZc : Z \ T = Tᶜ := by
    ext z
    have h3 : z ∈ T ∪ Z := hu ▸ mem_univ z
    exact ⟨fun h => h.2, fun h => ⟨h3.resolve_left h, h⟩⟩
  set O₁ : Set Y := ψ ⁻¹' (T \ Z) with hO₁
  set O₂ : Set Y := ψ ⁻¹' (Z \ T) with hO₂
  have hO₁o : IsOpen O₁ := by
    rw [hO₁, hTc]
    exact hZ.isOpen_compl.preimage hc
  have hO₂o : IsOpen O₂ := by
    rw [hO₂, hZc]
    exact hT.isOpen_compl.preimage hc
  have hDc : IsClosed (ψ ⁻¹' D) := hD.preimage hc
  have hcover : ∀ y : Y, y ∈ O₁ ∨ y ∈ O₂ ∨ y ∈ ψ ⁻¹' C ∨ y ∈ ψ ⁻¹' D := fun y => by
    have h3 : ψ y ∈ T ∪ Z := hu ▸ mem_univ _
    by_cases h4 : ψ y ∈ T <;> by_cases h5 : ψ y ∈ Z
    · rcases (hm ▸ (⟨h4, h5⟩ : ψ y ∈ T ∩ Z) : ψ y ∈ C ∪ D) with h | h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    · exact .inl ⟨h4, h5⟩
    · exact .inr (.inl ⟨h5, h4⟩)
    · exact absurd h3 (by simp [h4, h5])
  have hdis12 : Disjoint O₁ O₂ := Set.disjoint_left.mpr fun y h3 h4 => h3.2 h4.1
  have hCDd : ∀ y, y ∈ ψ ⁻¹' C → y ∉ ψ ⁻¹' D := fun y h3 h4 => Set.disjoint_left.mp hCD h3 h4
  have hCO₁ : ∀ y, y ∈ ψ ⁻¹' C → y ∉ O₁ := fun y h3 h4 => h4.2 ((show ψ y ∈ T ∩ Z from hm ▸ .inl
    h3).2)
  have hCO₂ : ∀ y, y ∈ ψ ⁻¹' C → y ∉ O₂ := fun y h3 h4 => h4.2 ((show ψ y ∈ T ∩ Z from hm ▸ .inl
    h3).1)
  have hDO₁ : ∀ y, y ∈ ψ ⁻¹' D → y ∉ O₁ := fun y h3 h4 => h4.2 ((show ψ y ∈ T ∩ Z from hm ▸ .inr
    h3).2)
  have hDO₂ : ∀ y, y ∈ ψ ⁻¹' D → y ∉ O₂ := fun y h3 h4 => h4.2 ((show ψ y ∈ T ∩ Z from hm ▸ .inr
    h3).1)
  /- Each lifted point lies on one side at least. -/
  have key : ∀ y ∈ ψ ⁻¹' C, y ∉ closure O₁ ∨ y ∉ closure O₂ := by
    intro y hy
    obtain ⟨V, P, hV, hyV, hVD, hPV, hPc, hPi, hVc⟩ := (hY.2.2 y).exists_half hDc.isOpen_compl
      (hCDd y hy)
    have hsub : P ⊆ O₁ ∪ O₂ := fun z hz => by
      rcases hcover z with h | h | h | h
      · exact .inl h
      · exact .inr h
      · exact absurd (hPi z hz) (hbdC h)
      · exact absurd h (hVD (hPV hz))
    rcases hPc.subset_or_subset hO₁o hO₂o hdis12 hsub with h | h
    · right
      intro hcl2
      obtain ⟨z, ⟨hz1, hz2⟩⟩ := mem_closure_iff_nhds.mp hcl2 _ (hV.mem_nhds hyV) |>.imp fun _ h => h
      have h3 : z ∈ closure P := hVc hz1
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h3 _ hO₂o hz2
      exact Set.disjoint_left.mp hdis12 (h hw2) hw1
    · left
      intro hcl2
      obtain ⟨z, ⟨hz1, hz2⟩⟩ := mem_closure_iff_nhds.mp hcl2 _ (hV.mem_nhds hyV) |>.imp fun _ h => h
      have h3 : z ∈ closure P := hVc hz1
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h3 _ hO₁o hz2
      exact Set.disjoint_left.mp hdis12 hw1 (h hw2)
  /- The two open sets around the two sides. -/
  set N₁ : Set Y := (closure O₂ ∪ ψ ⁻¹' D)ᶜ with hN₁
  set N₂ : Set Y := (closure O₁ ∪ ψ ⁻¹' D)ᶜ with hN₂
  have hN₁o : IsOpen N₁ := (isClosed_closure.union hDc).isOpen_compl
  have hN₂o : IsOpen N₂ := (isClosed_closure.union hDc).isOpen_compl
  have hN₁s : ∀ y ∈ N₁, y ∈ O₁ ∨ y ∈ ψ ⁻¹' C := fun y hy => by
    rcases hcover y with h | h | h | h
    · exact .inl h
    · exact absurd (.inl (subset_closure h)) hy
    · exact .inr h
    · exact absurd (.inr h) hy
  have hN₂s : ∀ y ∈ N₂, y ∈ O₂ ∨ y ∈ ψ ⁻¹' C := fun y hy => by
    rcases hcover y with h | h | h | h
    · exact absurd (.inl (subset_closure h)) hy
    · exact .inl h
    · exact .inr h
    · exact absurd (.inr h) hy
  have hNd : ∀ y, y ∈ N₁ → y ∈ N₂ → False := by
    intro y h3 h4
    have hN : IsOpen (N₁ ∩ N₂) := hN₁o.inter hN₂o
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp (mem_closure_compl_bd (hY.2.2 y)) _ hN ⟨h3, h4⟩
    rcases hN₁s z hz.1 with h | h
    · exact hz.2 (.inl (subset_closure h))
    · exact hz' (hbdC h)
  have hkey2 : ∀ y ∈ ψ ⁻¹' C, y ∈ N₁ ∨ y ∈ N₂ := fun y hy => by
    rcases key y hy with h | h
    · refine .inr fun h' => ?_
      rcases h' with h' | h'
      · exact h h'
      · exact hCDd y hy h'
    · refine .inl fun h' => ?_
      rcases h' with h' | h'
      · exact h h'
      · exact hCDd y hy h'
  /- Over each point of `C` there is one lift on each side. -/
  have hex₁ : ∀ x ∈ C, ∃ y ∈ N₁, ψ y = x := fun x hx => by
    have h3 : ψ '' closure O₁ ⊇ T \ Z := fun z hz => by
      obtain ⟨y, rfl⟩ := hsurj z
      exact ⟨y, subset_closure hz, rfl⟩
    have h4 : x ∈ ψ '' closure O₁ := (hcl _ isClosed_closure).closure_subset_iff.mpr h3 (h1 x hx)
    obtain ⟨y, hy, rfl⟩ := h4
    rcases hkey2 y hx with h | h
    · exact ⟨y, h, rfl⟩
    · exact absurd (.inl hy) h
  have hex₂ : ∀ x ∈ C, ∃ y ∈ N₂, ψ y = x := fun x hx => by
    have h3 : ψ '' closure O₂ ⊇ Z \ T := fun z hz => by
      obtain ⟨y, rfl⟩ := hsurj z
      exact ⟨y, subset_closure hz, rfl⟩
    have h4 : x ∈ ψ '' closure O₂ := (hcl _ isClosed_closure).closure_subset_iff.mpr h3 (h2 x hx)
    obtain ⟨y, hy, rfl⟩ := h4
    rcases hkey2 y hx with h | h
    · exact absurd (.inl hy) h
    · exact ⟨y, h, rfl⟩
  have hinj : InjOn ψ N₁ := by
    intro y hy y' hy' he
    by_cases hC : ψ y ∈ C
    · obtain ⟨w, hw, hwe⟩ := hex₂ _ hC
      have hc2 := hψ.2.2.2.1 _ hC
      obtain ⟨p, q, hpq, hpq'⟩ := Set.ncard_eq_two.mp hc2
      have m1 : y ∈ ψ ⁻¹' {ψ y} := rfl
      have m2 : y' ∈ ψ ⁻¹' {ψ y} := he.symm
      have m3 : w ∈ ψ ⁻¹' {ψ y} := hwe
      rw [hpq'] at m1 m2 m3
      have hyw : y ≠ w := fun h => hNd y hy (h ▸ hw)
      have hyw' : y' ≠ w := fun h => hNd y' hy' (h ▸ hw)
      simp only [mem_insert_iff, mem_singleton_iff] at m1 m2 m3
      rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2 <;> rcases m3 with e3 | e3 <;>
        first
          | exact e1.trans e2.symm
          | exact absurd (e1.trans e3.symm) hyw
          | exact absurd (e2.trans e3.symm) hyw'
    · have hC' : ψ y' ∉ C := he ▸ hC
      exact hψ.2.2.1 hC hC' he
  set K : Set Y := (N₁ ∪ N₂)ᶜ with hK
  have hKc : IsClosed K := (hN₁o.union hN₂o).isClosed_compl
  set W : Set S := (ψ '' K)ᶜ with hWd
  have hWo : IsOpen W := (hcl _ hKc).isOpen_compl
  have hWN : ∀ y, ψ y ∈ W → y ∈ N₁ ∪ N₂ := fun y hy => by
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hCW : C ⊆ W := by
    rintro z hz ⟨y, hy, rfl⟩
    exact hy (by simpa using hkey2 y hz)
  have hTW : ∀ t ∈ T, t ∈ W → ∃ y ∈ N₁, ψ y = t := fun t ht htW => by
    obtain ⟨y, rfl⟩ := hsurj t
    rcases hWN y htW with h | h
    · exact ⟨y, h, rfl⟩
    · rcases hN₂s y h with h' | h'
      · exact absurd ht h'.2
      · exact hex₁ _ h'
  /- The open set `P` of the cut surface is an open set of `T`. -/
  let P : Set Y := N₁ ∩ ψ ⁻¹' W
  have hPo : IsOpen P := hN₁o.inter (hWo.preimage hc)
  have hPT : ∀ y ∈ P, ψ y ∈ T := fun y hy => by
    rcases hN₁s y hy.1 with h | h
    · exact h.1
    · exact hCT h
  let ρ : P → T := fun y => ⟨ψ y, hPT y y.2⟩
  have hρ : IsOpenEmbedding ρ := by
    have c1 : Continuous ρ := (hc.comp continuous_subtype_val).subtype_mk _
    have i1 : Function.Injective ρ := fun a b he =>
      Subtype.ext (hinj a.2.1 b.2.1 (congrArg Subtype.val he))
    refine (IsOpenEmbedding.of_continuous_injective_isOpenMap c1 i1 ?_)
    intro U hU
    obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.mp hU
    have hc' : IsClosed ((U' ∩ P) ∪ N₂)ᶜ := ((hU'.inter hPo).union hN₂o).isClosed_compl
    have : ρ '' (Subtype.val ⁻¹' U') = Subtype.val ⁻¹' (W ∩ (ψ '' ((U' ∩ P) ∪ N₂)ᶜ)ᶜ) := by
      ext t
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2.2, ?_⟩
        rintro ⟨y', hy', he⟩
        rcases hWN y' (he.symm ▸ y.2.2) with h | h
        · have : y' = y.1 := hinj h y.2.1 he
          exact hy' (.inl ⟨this ▸ hy, this ▸ y.2⟩)
        · exact hy' (.inr h)
      · rintro ⟨h3, h4⟩
        obtain ⟨y, hy, he⟩ := hTW t.1 t.2 h3
        have hyP : y ∈ P := ⟨hy, by rw [mem_preimage, he]; exact h3⟩
        by_cases hyU : y ∈ U'
        · exact ⟨⟨y, hyP⟩, hyU, Subtype.ext he⟩
        · exact absurd ⟨y, fun h => h.elim (fun h' => hyU h'.1) (fun h' => hNd y hy h'), he⟩ h4
    rw [this]
    exact (hWo.inter (hcl _ hc').isOpen_compl).preimage continuous_subtype_val
  obtain ⟨y, hy, rfl⟩ := hex₁ x hx
  have hyP : y ∈ P := ⟨hy, hCW hx⟩
  have hyC : y ∈ ψ ⁻¹' C := hx
  have m1 : IsManifoldPoint (⟨y, hyP⟩ : P) := isManifoldPoint_sub hPo (hY.2.2 y)
  have m2 : (⟨y, hyP⟩ : P) ∈ bd P := fun h => hbdC hyC ((isInteriorPoint_sub hPo).mp h)
  exact ⟨isManifoldPoint_of_isOpenEmbedding hρ m1, bd_of_isOpenEmbedding hρ m2⟩

end GraphMinor.Surface
