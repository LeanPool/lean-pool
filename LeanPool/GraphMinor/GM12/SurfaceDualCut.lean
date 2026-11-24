/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialTwoCell
public import LeanPool.GraphMinor.GM11.GlueDiscs

/-!
# A cross-cut of an open disc

Let `p` be an open disc in a closed surface, and let `a` be a line or an `O`-arc with its ends off
`p`
and all of its other points in `p`. Collapse the complement of `p` to a point. This gives a sphere,
and `a`
becomes an `O`-arc. So the Jordan curve theorem cuts `p` along `a` into exactly two parts, and the
whole line is on the frontier of each. Each part is an open disc, by `isOpenDisc_of_bound`
(`exists_crosscut_sides`).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval OnePoint

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Two components of a set are equal or disjoint. -/
theorem disjoint_of_components {X : Type*} [TopologicalSpace X] {T A B : Set X}
    (hA : A ∈ componentsIn T) (hB : B ∈ componentsIn T) (hne : A ≠ B) : Disjoint A B := by
  obtain ⟨a, -, rfl⟩ := hA
  obtain ⟨b, -, rfl⟩ := hB
  refine disjoint_left.mpr fun x h₁ h₂ => hne ?_
  rw [connectedComponentIn_eq h₁, connectedComponentIn_eq h₂]

/-- A subset of `X` with frontier `F` that misses `F` is open. -/
theorem isOpen_of_frontier {X : Type*} [TopologicalSpace X] {A F : Set X} (h : frontier A = F)
    (hd : Disjoint A F) : IsOpen A := by
  rw [← interior_eq_iff_isOpen]
  refine interior_subset.antisymm fun x hx => ?_
  by_contra hn
  exact disjoint_left.mp hd hx (h ▸ ⟨subset_closure hx, hn⟩)

variable [ConnectedSpace S]

/-- See the module docstring. -/
theorem exists_crosscut_sides (hS : IsClosedSurface S) {p : Set S} (hp : IsOpenDisc p) {a : I → S}
    (ha : Continuous a) (hi : InjOn a (Ioo 0 1)) (h0 : a 0 ∉ p) (h1 : a 1 ∉ p)
    (hin : ∀ t, t ≠ 0 → t ≠ 1 → a t ∈ p) :
    ∃ s₁ s₂ : Set S, IsOpenDisc s₁ ∧ IsOpenDisc s₂ ∧ Disjoint s₁ s₂ ∧ p \ range a = s₁ ∪ s₂ ∧
      range a ⊆ closure s₁ ∧ range a ⊆ closure s₂ := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hsph : IsSphere (OnePoint p) := isSphere_onePoint hp
  have hT : T2Space (OnePoint p) := by
    obtain ⟨e⟩ := id hsph
    exact e.symm.t2Space
  have hpo : IsOpen p := hp.1
  have hmc : Continuous (collapse p ∘ a) := (continuous_collapse hpo).comp ha
  have hm0 : (collapse p ∘ a) 0 = ∞ := collapse_of_notMem h0
  have hm1 : (collapse p ∘ a) 1 = ∞ := collapse_of_notMem h1
  have hmin : ∀ t ∈ Ioo (0 : I) 1, a t ∈ p := fun t ht => hin t ht.1.ne' ht.2.ne
  have hF : IsOArc (range (collapse p ∘ a)) := by
    refine isOArc_of_loop hmc (hm0.trans hm1.symm) ?_ ?_
    · intro s hs t ht h
      simp only [Function.comp, collapse_of_mem (hmin s hs), collapse_of_mem (hmin t ht)] at h
      exact hi hs ht (congrArg Subtype.val (OnePoint.coe_injective h))
    · intro t ht
      rw [hm0]
      simp only [Function.comp, collapse_of_mem (hmin t ht)]
      exact OnePoint.coe_ne_infty _
  obtain ⟨A, B, hne, hcomp, hfA, hfB⟩ := jordan_sphere hsph hF
  set F := range (collapse p ∘ a) with hFdef
  have hinfF : (∞ : OnePoint p) ∈ F := ⟨0, hm0⟩
  have hmemA : A ∈ componentsIn (univ \ F) := hcomp ▸ Or.inl rfl
  have hmemB : B ∈ componentsIn (univ \ F) := hcomp ▸ Or.inr rfl
  have hsub : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) → Disjoint C F := by
    rintro _ ⟨x, hx, rfl⟩
    exact disjoint_left.mpr fun y hy hyF => (connectedComponentIn_subset _ _ hy).2 hyF
  have hpre : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) → IsPreconnected C := by
    rintro _ ⟨x, -, rfl⟩
    exact isPreconnected_connectedComponentIn
  have hnon : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) → C.Nonempty := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hoA : IsOpen A := isOpen_of_frontier hfA (hsub hmemA)
  have hoB : IsOpen B := isOpen_of_frontier hfB (hsub hmemB)
  have hdAB : Disjoint A B := disjoint_of_components hmemA hmemB hne
  -- The part of `p` for a side of the curve.
  let side : Set (OnePoint p) → Set S := fun C => collapse p ⁻¹' C
  obtain ⟨z⟩ : Nonempty S := inferInstance
  have hsub_p : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) → side C ⊆ p := by
    intro C hC x hx
    by_contra hn
    have : (∞ : OnePoint p) ∈ C := by
      have h : collapse p x ∈ C := hx
      rwa [collapse_of_notMem hn] at h
    exact disjoint_left.mp (hsub hC) this hinfF
  have hunc : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) →
      ContinuousOn (uncollapse z) C := by
    intro C hC y hy
    induction y using OnePoint.rec with
    | infty => exact absurd hinfF (disjoint_left.mp (hsub hC) hy)
    | coe y => exact (continuousAt_uncollapse z y).continuousWithinAt
  have himg : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) →
      side C = uncollapse z '' C := by
    intro C hC
    ext x
    constructor
    · intro hx
      have hxp := hsub_p hC hx
      refine ⟨collapse p x, hx, ?_⟩
      rw [collapse_of_mem hxp]
      rfl
    · rintro ⟨y, hy, rfl⟩
      induction y using OnePoint.rec with
      | infty => exact absurd hinfF (disjoint_left.mp (hsub hC) hy)
      | coe y =>
        change collapse p y.1 ∈ C
        rw [collapse_of_mem y.2]
        exact hy
  have hsconn : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) → IsPreconnected (side C)
    := by
    intro C hC
    rw [himg hC]
    exact (hpre hC).image _ (hunc hC)
  have hrange_off : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) →
      Disjoint (side C) (range a) := by
    intro C hC
    refine disjoint_left.mpr ?_
    rintro _ hx ⟨t, rfl⟩
    exact disjoint_left.mp (hsub hC) hx ⟨t, rfl⟩
  have hopen : ∀ {C : Set (OnePoint p)}, IsOpen C → IsOpen (side C) := fun h =>
    h.preimage (continuous_collapse hpo)
  have hnonempty : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) → (side C).Nonempty := by
    intro C hC
    rw [himg hC]
    exact (hnon hC).image _
  have hcover : p \ range a ⊆ side A ∪ side B := by
    rintro x ⟨hxp, hxa⟩
    have hxF : collapse p x ∉ F := by
      rintro ⟨t, ht⟩
      by_cases ht0 : t = 0
      · rw [ht0, hm0, collapse_of_mem hxp] at ht
        exact OnePoint.coe_ne_infty _ ht.symm
      by_cases ht1 : t = 1
      · rw [ht1, hm1, collapse_of_mem hxp] at ht
        exact OnePoint.coe_ne_infty _ ht.symm
      have hat := hin t ht0 ht1
      simp only [Function.comp, collapse_of_mem hat, collapse_of_mem hxp] at ht
      exact hxa ⟨t, congrArg Subtype.val (OnePoint.coe_injective ht)⟩
    have h : connectedComponentIn (univ \ F) (collapse p x) ∈ componentsIn (univ \ F) :=
      mem_image_of_mem _ ⟨mem_univ _, hxF⟩
    rw [hcomp] at h
    have hm := mem_connectedComponentIn (F := univ \ F) ⟨mem_univ _, hxF⟩
    rcases h with h | h
    · exact Or.inl (h ▸ hm)
    · exact Or.inr (h ▸ hm)
  have hdisc : ∀ {C D : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) →
      D ∈ componentsIn (univ \ F) → Disjoint C D → IsOpen C → IsOpen D →
      p \ range a ⊆ side C ∪ side D → IsOpenDisc (side C) := by
    intro C D hC hD hCD hoC hoD hcov
    refine isOpenDisc_of_bound hS (hopen hoC) ⟨hnonempty hC, hsconn hC⟩
      (fun h => hsub_p hC (h.symm ▸ mem_univ (a 0)) |> h0) ?_
    intro G hGC hG
    have hGp := hGC.trans (hsub_p hC)
    obtain ⟨Δ, hΔp, hΔ, hb⟩ := exists_disc_in_openDisc hp hG hGp
    have hconn : IsPreconnected (range a) := isPreconnected_range ha
    have hdb : Disjoint (range a) (discBd Δ) := by
      rw [hb]
      exact ((hrange_off hC).mono_left hGC).symm
    have hΔa : Disjoint (range a) Δ :=
      disjoint_disc_of_outside hman hΔ hconn hdb ⟨0, rfl⟩ fun h => h0 (hΔp h)
    refine ⟨Δ, ?_, hΔ, hb⟩
    obtain ⟨y, hy⟩ : G.Nonempty := by
      obtain ⟨φ⟩ := hG
      exact ⟨_, (φ 1).2⟩
    have hyΔ : y ∈ Δ := GraphMinor.Surface.discBd_subset Δ (hb.symm.subset hy)
    have hΔc : IsPreconnected Δ := by
      obtain ⟨h, g, c'⟩ := hΔ.exists_isChart
      rw [← c'.g_closedBall]
      exact (convex_closedBall _ _).isPreconnected.image _ c'.gc
    have hdis : Disjoint (side C) (side D) :=
      disjoint_left.mpr fun x h₁ h₂ => disjoint_left.mp hCD h₁ h₂
    exact hΔc.subset_left_of_subset_union (hopen hoC) (hopen hoD) hdis
      (fun x hx => hcov ⟨hΔp hx, fun h => disjoint_left.mp hΔa h hx⟩) ⟨y, hyΔ, hGC hy⟩
  have hclosure : ∀ {C : Set (OnePoint p)}, C ∈ componentsIn (univ \ F) → frontier C = F →
      range a ⊆ closure (side C) := by
    intro C hC hf
    have hIoo : a '' Ioo 0 1 ⊆ closure (side C) := by
      rintro _ ⟨t, ht, rfl⟩
      have hmem : (collapse p ∘ a) t ∈ closure C := by
        have : (collapse p ∘ a) t ∈ frontier C := hf ▸ ⟨t, rfl⟩
        exact frontier_subset_closure this
      have hat := hmin t ht
      simp only [Function.comp, collapse_of_mem hat] at hmem
      rw [himg hC]
      exact mem_closure_image (continuousAt_uncollapse z ⟨a t, hat⟩) hmem
    have hdense : (univ : Set I) ⊆ closure (Ioo (0 : I) 1) := by
      rw [closure_Ioo (by norm_num : (0 : I) ≠ 1)]
      exact fun t _ => ⟨t.2.1, t.2.2⟩
    rintro _ ⟨t, rfl⟩
    exact closure_minimal hIoo isClosed_closure (image_closure_subset_closure_image ha
      (mem_image_of_mem a (hdense (mem_univ t))))
  refine ⟨side A, side B, hdisc hmemA hmemB hdAB hoA hoB hcover,
    hdisc hmemB hmemA hdAB.symm hoB hoA ((union_comm _ _).subset.trans' hcover) ,
    disjoint_left.mpr fun x h₁ h₂ => disjoint_left.mp hdAB h₁ h₂, ?_, hclosure hmemA hfA,
    hclosure hmemB hfB⟩
  refine Subset.antisymm hcover (union_subset ?_ ?_)
  · exact fun x hx => ⟨hsub_p hmemA hx, disjoint_left.mp (hrange_off hmemA) hx⟩
  · exact fun x hx => ⟨hsub_p hmemB hx, disjoint_left.mp (hrange_off hmemB) hx⟩

end GraphMinor.GM12
