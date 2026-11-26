/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5c
public import LeanPool.GraphMinor.GM19.CutTwo

/-!
# Graph Minors XIX, (5.3): the frame and the fit

We finish the first three conditions of "fit" for `ψ⁻¹(Γ) ∩ Σ₁` and `ψ⁻¹(Φ) ∩ Σ₁`. A side of the new
frame maps
into a side of `Φ` or into an edge of `K`. In the second case it is short, and in the first case it
is short
only if the side of `Φ` is. Either way a short side has no vertex of `Γ₁` on it.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]


omit [T2Space S₁] in
/-- The mirror of `arcOf_eq_of_left`. -/
theorem arcOf_eq_of_right {Θ : Set S₁} (f : Circle ≃ₜ Θ) {N : Set S₁} {a b a' b' : ℝ} (hab : a < b)
  (hab' : a' < b')
    (hd : Disjoint (arcOf f a b) N) (hd' : Disjoint (arcOf f a' b') N)
    (ha : cuffPoint f a ∈ N) (ha' : cuffPoint f a' ∈ N) (h : cuffPoint f b = cuffPoint f b') :
    arcOf f a b = arcOf f a' b' := by
  obtain ⟨m, hm⟩ := cuffPoint_eq f h
  subst hm
  have hshift := arcOf_shift f (a - m * (2 * Real.pi)) b' m
  rw [sub_add_cancel] at hshift
  rw [hshift] at hd ⊢
  have hcp : cuffPoint f (a - m * (2 * Real.pi)) = cuffPoint f a := by
    have h := cuffPoint_shift f (a - m * (2 * Real.pi)) m
    rwa [sub_add_cancel, eq_comm] at h
  have hab₂ : a - m * (2 * Real.pi) < b' := by linarith
  rcases lt_trichotomy (a - m * (2 * Real.pi)) a' with h₁ | h₁ | h₁
  · exact absurd ha' (disjoint_left.mp hd ⟨_, ⟨h₁, hab'⟩, rfl⟩)
  · rw [h₁]
  · exact absurd (hcp ▸ ha) (disjoint_left.mp hd' ⟨_, ⟨h₁, hab₂⟩, rfl⟩)

/-- At a point of the boundary at most two arcs of `bd(Σ₁) \ N` end: one on each side. -/
theorem eq_or_eq_of_mem_tilde (hS : IsSurface S₁) {N : Set S₁} (hN : N.Finite)
    (h2 : ∀ C : cuffs S₁, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) {R₁ R₂ R₃ : Set S₁}
    (h₁ : R₁ ∈ arcComponentsIn (bd S₁ \ N)) (h₂ : R₂ ∈ arcComponentsIn (bd S₁ \ N))
    (h₃ : R₃ ∈ arcComponentsIn (bd S₁ \ N)) (hne : R₁ ≠ R₂) {p : S₁} (hp₁ : p ∈ tilde R₁)
      (hp₂ : p ∈ tilde R₂)
    (hp₃ : p ∈ tilde R₃) : R₃ = R₁ ∨ R₃ = R₂ := by
  have key : ∀ {R}, R ∈ arcComponentsIn (bd S₁ \ N) → p ∈ tilde R → ∃ (C : cuffs S₁)
    (a b : ℝ), a < b ∧
      R = arcOf (cuffPar hS C) a b ∧ Disjoint R N ∧ cuffPoint (cuffPar hS C) a ∈ N ∧
      cuffPoint (cuffPar hS C) b ∈ N ∧ (p = cuffPoint (cuffPar hS C) a ∨ p = cuffPoint
        (cuffPar hS C) b) := by
    intro R hR hp
    obtain ⟨C, a, b, hab, hub, rfl, hd, ha, hb⟩ := exists_arc_of_mem hS (cuffPar hS) hN h2 hR
    rw [tilde_arcOf _ hab hub] at hp
    exact ⟨C, a, b, hab, rfl, hd, ha, hb, hp⟩
  obtain ⟨C₁, a₁, b₁, hab₁, rfl, hd₁, ha₁, hb₁, hc₁⟩ := key h₁ hp₁
  obtain ⟨C₂, a₂, b₂, hab₂, rfl, hd₂, ha₂, hb₂, hc₂⟩ := key h₂ hp₂
  obtain ⟨C₃, a₃, b₃, hab₃, rfl, hd₃, ha₃, hb₃, hc₃⟩ := key h₃ hp₃
  have hm : ∀ {C : cuffs S₁} {t}, p = cuffPoint (cuffPar hS C) t → p ∈ C.1 := fun {C t} h ↦
    h ▸ cuffPoint_mem _ t
  have hC : ∀ {C C' : cuffs S₁}, p ∈ C.1 → p ∈ C'.1 → C = C' := fun {C C'} h h' ↦ by
    by_contra hne
    exact disjoint_left.mp (cuffs_disjoint' hne) h h'
  have h12 : C₁ = C₂ := hC (hc₁.elim hm hm) (hc₂.elim hm hm)
  have h13 : C₁ = C₃ := hC (hc₁.elim hm hm) (hc₃.elim hm hm)
  subst h12
  subst h13
  rcases hc₁ with hc₁ | hc₁ <;> rcases hc₂ with hc₂ | hc₂
  · exact absurd (arcOf_eq_of_left _ hab₁ hab₂ hd₁ hd₂ hb₁ hb₂ (hc₁.symm.trans hc₂)) hne
  · rcases hc₃ with hc₃ | hc₃
    · exact .inl (arcOf_eq_of_left _ hab₃ hab₁ hd₃ hd₁ hb₃ hb₁ (hc₃.symm.trans hc₁))
    · exact .inr (arcOf_eq_of_right _ hab₃ hab₂ hd₃ hd₂ ha₃ ha₂ (hc₃.symm.trans hc₂))
  · rcases hc₃ with hc₃ | hc₃
    · exact .inr (arcOf_eq_of_left _ hab₃ hab₂ hd₃ hd₂ hb₃ hb₂ (hc₃.symm.trans hc₂))
    · exact .inl (arcOf_eq_of_right _ hab₃ hab₁ hd₃ hd₁ ha₃ ha₁ (hc₃.symm.trans hc₁))
  · exact absurd (arcOf_eq_of_right _ hab₁ hab₂ hd₁ hd₂ ha₁ ha₂ (hc₁.symm.trans hc₂)) hne

omit [T2Space S] in
/-- A boundary point is a limit of interior points, and near it the interior is connected. -/
theorem isConnectedNear_compl_bd {x : S} (hx : IsManifoldPoint x) (hb : x ∈ bd S) :
    IsConnectedNear (bd S)ᶜ x ∧ x ∈ closure (bd S)ᶜ := by
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hm, hk', hl, hr⟩ := hx.exists_chart
  have hjx := hm hxU
  have hk0 : k (j x) = x := hl hxU
  have hH : ∀ {z : ℂ}, z ∈ {z : ℂ | 0 < z.re} → z ∈ halfPlane := fun {z} h ↦
    le_of_lt (show 0 < z.re from h)
  have hint : ∀ y ∈ U, IsInteriorPoint y ↔ 0 < (j y).re := fun y hy ↦ by
    constructor
    · intro hi
      exact lt_of_le_of_ne (hm hy).2 fun h ↦
        not_isInteriorPoint_of_chart hU hj hm hl.injOn hy h.symm hi
    · exact isInteriorPoint_of_chart hU hO hj hk hm hk' hl hr hy
  have hre : (j x).re = 0 := le_antisymm (not_lt.mp fun h ↦ hb ((hint x hxU).mpr h)) hjx.2
  have hkey : ∀ W ∈ 𝓝 x, ∃ ρ > 0, Metric.ball (j x) ρ ⊆ O ∧
      k '' (Metric.ball (j x) ρ ∩ {z | 0 < z.re}) ⊆ W := by
    intro W hW
    have hc : ContinuousWithinAt k (O ∩ halfPlane) (j x) := hk _ hjx
    have hpre : k ⁻¹' W ∈ 𝓝[O ∩ halfPlane] j x := hc.preimage_mem_nhdsWithin (by rwa [hk0])
    obtain ⟨ρ₁, h₁, hsub₁⟩ := Metric.mem_nhdsWithin_iff.mp hpre
    obtain ⟨ρ₂, h₂, hsub₂⟩ := Metric.isOpen_iff.mp hO _ hjx.1
    refine ⟨min ρ₁ ρ₂, lt_min h₁ h₂, (Metric.ball_subset_ball (min_le_right _ _)).trans hsub₂, ?_⟩
    rintro _ ⟨z, ⟨hz, hzr⟩, rfl⟩
    have hzO : z ∈ O := hsub₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact hsub₁ ⟨Metric.ball_subset_ball (min_le_left _ _) hz, hzO, hH hzr⟩
  have hkint : ∀ {ρ : ℝ}, Metric.ball (j x) ρ ⊆ O → ∀ {z}, z ∈ Metric.ball (j x) ρ ∩ {z | 0 < z.re}
    → k z ∉ bd S := by
    intro ρ hρ z hz hbz
    have hzH : z ∈ O ∩ halfPlane := ⟨hρ hz.1, hH hz.2⟩
    refine hbz ((hint _ (hk' hzH)).mpr ?_)
    rw [hr hzH]
    exact hz.2
  constructor
  · intro W hW
    obtain ⟨ρ, hρ, hsubO, hsubW⟩ := hkey W hW
    refine ⟨k '' (Metric.ball (j x) ρ ∩ {z | 0 < z.re}), ?_, ?_, U ∩ j ⁻¹' Metric.ball (j x) ρ,
      ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨hkint hsubO hz, hsubW (mem_image_of_mem k hz)⟩
    · have hconv : Convex ℝ (Metric.ball (j x) ρ ∩ {z | 0 < z.re}) :=
        (convex_ball _ _).inter (convex_halfSpace_re_gt 0)
      exact hconv.isPreconnected.image _ (hk.mono fun z hz ↦ ⟨hsubO hz.1, hH hz.2⟩)
    · exact (hj.isOpen_inter_preimage hU Metric.isOpen_ball).mem_nhds ⟨hxU, Metric.mem_ball_self hρ⟩
    · rintro y ⟨hyb, hyU, hyB⟩
      have hi : IsInteriorPoint y := not_not.mp hyb
      exact ⟨j y, ⟨hyB, (hint y hyU).mp hi⟩, hl hyU⟩
  · rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨ρ, hρ, hsubO, hsubW⟩ := hkey W hW
    have hz : j x + ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball (j x) ρ ∩ {z | 0 < z.re} := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hρ)]
        exact half_lt_self hρ
      · simp [hre, hρ]
    exact ⟨k _, hsubW (mem_image_of_mem k hz), hkint hsubO hz⟩

/-- Two connected parts of a line that come near one end of the line meet. -/
theorem nonempty_inter_of_end {L A B : Set S} {u v : S} (hL : IsLineWithEnds L u v)
  (hA : A ⊆ L \ {u})
    (hB : B ⊆ L \ {u}) (hAc : IsPreconnected A) (hBc : IsPreconnected B) (huA : u ∈ closure A)
    (huB : u ∈ closure B) (hAn : A.Nonempty) (hBn : B.Nonempty) : (A ∩ B).Nonempty := by
  obtain ⟨f, hf0, -⟩ := id hL
  let g : unitInterval → S := fun t ↦ (f t).1
  have hgc : Continuous g := continuous_subtype_val.comp f.continuous
  have hgi : Function.Injective g := fun a b he ↦ f.injective (Subtype.ext he)
  have hgr : range g = L := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hz
      exact ⟨f.symm ⟨z, hz⟩, by simp [g]⟩
  have hclosed : IsClosedMap g := hgc.isClosedMap
  have hemb : IsEmbedding g := (hgc.isClosedEmbedding hgi).isEmbedding
  have key : ∀ {X : Set S}, X ⊆ L \ {u} → IsPreconnected X → u ∈ closure X → X.Nonempty →
      ∃ X' : Set unitInterval, g '' X' = X ∧ X'.OrdConnected ∧ (∀ t ∈ X', t ≠ 0) ∧
        (∀ m, 0 < m → ∃ t ∈ X', t < m) ∧ X'.Nonempty := by
    intro X hX hXc hu hXn
    have hsubr : X ⊆ range g := fun z hz ↦ hgr ▸ (hX hz).1
    have him : g '' (g ⁻¹' X) = X := image_preimage_eq_of_subset hsubr
    have hpre : IsPreconnected (g ⁻¹' X) := by
      rw [← hemb.isInducing.isPreconnected_image, him]
      exact hXc
    have h0 : (0 : unitInterval) ∈ closure (g ⁻¹' X) := by
      have hu' : u ∈ g '' closure (g ⁻¹' X) := by
        rw [← hclosed.closure_image_eq_of_continuous hgc, him]
        exact hu
      obtain ⟨t, ht, hgt⟩ := hu'
      have : t = 0 := hgi (hgt.trans hf0.symm)
      exact this ▸ ht
    refine ⟨g ⁻¹' X, him, hpre.ordConnected, ?_, ?_, ?_⟩
    · rintro t ht rfl
      exact (hX ht).2 hf0
    · intro m hm
      obtain ⟨t, htm, ht⟩ := mem_closure_iff_nhds.mp h0 _ (Iio_mem_nhds hm)
      exact ⟨t, ht, htm⟩
    · obtain ⟨z, hz⟩ := hXn
      obtain ⟨t, rfl⟩ := hsubr hz
      exact ⟨t, hz⟩
  obtain ⟨A', rfl, hAo, hA0, hAl, a, ha⟩ := key hA hAc huA hAn
  obtain ⟨B', rfl, hBo, hB0, hBl, b, hb⟩ := key hB hBc huB hBn
  have hm0 : 0 < min a b := lt_min (unitInterval.pos_iff_ne_zero.mpr (hA0 a ha))
    (unitInterval.pos_iff_ne_zero.mpr (hB0 b hb))
  obtain ⟨a', ha', ha'm⟩ := hAl _ hm0
  obtain ⟨b', hb', hb'm⟩ := hBl _ hm0
  have h₁ : min a b ∈ A' := hAo.out ha' ha ⟨ha'm.le, min_le_left _ _⟩
  have h₂ : min a b ∈ B' := hBo.out hb' hb ⟨hb'm.le, min_le_right _ _⟩
  exact ⟨g (min a b), mem_image_of_mem g h₁, mem_image_of_mem g h₂⟩

namespace FrameData

variable {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S} (D : FrameData Φ Γ K ψ)
include D

omit [T2Space S] [T2Space S₁] in
/-- A side of the frame of the fragment maps into a side of `Φ` or into an edge of `K`. -/
theorem image_side {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) :
    (∃ s ∈ Φ.sides, ψ '' R ⊆ s) ∨ ∃ e ∈ arcComponentsIn (K.U \ K.V), ψ '' R ⊆ e := by
  have hc : Continuous ψ := D.pull.frag.continuous_ψ
  have hS : IsSurface S := D.pull.surface
  have hbd : IsClosed (bd S) := (cuff_statement S hS).1
  have hIc : IsPathConnected (ψ '' R) := hR.2.2.1.image hc
  have hoff : ∀ {x}, x ∈ R → ψ x ∉ Φ.V ∪ K.V := fun hx ↦ (hR.2.1 hx).2
  have hcov : ψ '' R ⊆ bd S ∪ K.U := by
    rintro _ ⟨x, hx, rfl⟩
    exact D.pull.frag.maps_bd (mem_image_of_mem ψ (hR.2.1 hx).1)
  by_cases hb : ψ '' R ⊆ bd S
  · refine Or.inl ?_
    obtain ⟨s, hs, hsub⟩ := exists_arcComp_superset hIc (F := bd S \ Φ.V) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hb (mem_image_of_mem ψ hx), fun hv ↦ hoff hx (Or.inl hv)⟩)
    exact ⟨s, hs, hsub⟩
  have hKsub : ψ '' R ⊆ K.U := by
    obtain ⟨_, ⟨u, hu, rfl⟩, hub⟩ := not_subset.mp hb
    by_contra hk
    obtain ⟨_, ⟨v, hv, rfl⟩, hvk⟩ := not_subset.mp hk
    obtain ⟨z, ⟨x, hx, rfl⟩, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp
      hIc.isConnected.isPreconnected
      (bd S) K.U hbd K.isClosed_U hcov
      ⟨ψ v, mem_image_of_mem ψ hv, (hcov (mem_image_of_mem ψ hv)).resolve_right hvk⟩
      ⟨ψ u, mem_image_of_mem ψ hu, (hcov (mem_image_of_mem ψ hu)).resolve_left hub⟩
    exact hoff hx (Or.inr (D.K_bd ⟨hz₂, hz₁⟩))
  refine Or.inr ?_
  obtain ⟨e, he, hsub⟩ := exists_arcComp_superset hIc (F := K.U \ K.V) (by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hKsub (mem_image_of_mem ψ hx), fun hv ↦ hoff hx (Or.inr hv)⟩)
  exact ⟨e, he, hsub⟩

omit [T2Space S] [T2Space S₁] in
/-- A short side of the frame of the fragment has no vertex of `Γ₁`: it maps into a short side of
`Φ`, which is
an edge of `Γ`, or into an edge of `K`, which meets `Γ` in no point. So it is a component of `bd(Σ₁)
\ V₁`. -/
theorem mem_arcComponents_of_short {R : Set S₁} (hR : R ∈ arcComponentsIn
  (bd S₁ \ pullFrameV Φ K ψ))
    (hshort : ¬ ∃ s ∈ Φ.longSides, ψ '' R ⊆ s) : R ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ) := by
  have hoffΓ : ∀ x ∈ R, ψ x ∉ Γ.V := by
    intro x hx hxV
    rcases D.image_side hR with ⟨s, hs, hsub⟩ | ⟨e, he, hsub⟩
    · have hsh : s ∈ Φ.shortSides := ⟨hs, fun hl ↦ hshort ⟨s, ⟨hs, hl⟩, hsub⟩⟩
      have hsE : s ∈ Γ.E := D.fits.short_sides hsh
      exact Γ.disjoint_V hsE (hsub (mem_image_of_mem ψ hx)) hxV
    · have hk := (he.2.1 (hsub (mem_image_of_mem ψ hx)))
      exact hk.2 (D.pull.inter ⟨Γ.V_subset hxV, hk.1⟩).2
  have hsub : R ⊆ bd S₁ \ pullV Γ K ψ := by
    intro x hx
    refine ⟨(hR.2.1 hx).1, ?_⟩
    rintro (hv | hv)
    · exact hoffΓ x hx hv
    · exact (hR.2.1 hx).2 (Or.inr hv)
  exact ⟨hR.1, hsub, hR.2.2.1, fun X hX hXc hRX ↦
    hR.2.2.2 X (hX.trans (sdiff_subset_sdiff_right D.pullFrameV_subset)) hXc hRX⟩

end FrameData

end GraphMinor.GM19
