/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.ShrinkForest
public import LeanPool.GraphMinor.GM07.FlatMinimal
public import LeanPool.GraphMinor.GM07.Section11f
public import LeanPool.GraphMinor.Surface.TriLocal
public import LeanPool.GraphMinor.Surface.SurfacePull

/-!
# The part of a cut surface over a tree is connected

Let `T` be a component of a forest `L` with no `O`-arc and no `I`-arc, and let `φ` be the map of the
cut along `U(L)`. We show that `φ⁻¹(T)` is connected (`isPreconnected_preimage_tree`). This is what
lets us see `φ⁻¹(T)` as an arc of a cuff in (4.4) of Graph Minors VII.

The reason is that a forest does not separate an open set. A line with a free end does not separate,
because a path that crosses it can be moved off it by the slide `exists_line_slide`
(`isPreconnected_sdiff_line`). Lines are removed in the order of a growth
(`isPreconnected_sdiff_growth`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- **A line with an end outside `X` does not separate the open set `X`.** A path in `X` misses that
end, so it misses a piece of the line next to it. The slide of the rest of the line into a small set
off the path gives a path off the line. -/
theorem isPreconnected_sdiff_line (hS : IsSurface S) {X : Set S} (hXo : IsOpen X)
  (hXc : IsPreconnected X) {c : unitInterval → S} (hc : IsArcMap c) (h0 : c 0 ∉ X)
    (hin : ∀ s, s ≠ 0 → c s ∈ X) (hbd : ∀ s, s ≠ 0 → c s ∉ bd S) :
    IsPreconnected (X \ range c) := by
  classical
  have ht2 : T2Space S := hS.2.1
  rcases (X \ range c).eq_empty_or_nonempty with he | hne
  · rw [he]
    exact isPreconnected_empty
  refine (IsPathConnected.isConnected ?_).isPreconnected
  rw [isPathConnected_iff]
  refine ⟨hne, fun u hu v hv => ?_⟩
  have hXp : IsPathConnected X := isPathConnected_of_isOpen hS hXo ⟨⟨u, hu.1⟩, hXc⟩
  have hJ : JoinedIn X u v := hXp.joinedIn u hu.1 v hv.1
  let γ := hJ.somePath
  have hγ : ∀ t, γ t ∈ X := hJ.somePath_mem
  have hGc : IsClosed (range γ) := (isCompact_range γ.continuous).isClosed
  obtain ⟨t, ht0, ht1, htN⟩ := exists_initial hc.1 hGc.isOpen_compl (by
    rintro ⟨w, hw⟩
    exact h0 (hw ▸ hγ w))
  obtain ⟨A, hA, hA0, hAf, hfA, -⟩ := exists_tail hc ht0 ht1
  have hne0 : ∀ s', t < s' → s' ≠ 0 := fun s' h h0 => by
    rw [h0] at h
    exact absurd (show t.1 < 0 from h) (not_lt.mpr t.2.1)
  have ht00 : t ≠ 0 := fun h => by
    rw [h] at ht0
    simp at ht0
  let Y : Set S := c '' Iic t
  have hYc : IsClosed Y := (isClosed_Iic.isCompact.image hc.1).isClosed
  let Z : Set S := Xᶜ ∪ {u, v} ∪ Y
  have hZc : IsClosed Z := (hXo.isClosed_compl.union (toFinite _).isClosed).union hYc
  have hoff : ∀ s, A s ∉ bd S := fun s h => by
    by_cases hs : s = 0
    · rw [hs, hA0] at h
      exact hbd t ht00 h
    · obtain ⟨s', hs', he⟩ := hAf s hs
      exact hbd s' (hne0 s' hs') (he ▸ h)
  let N : Set S := X ∩ (range γ)ᶜ
  have hN : IsOpen N := hXo.inter hGc.isOpen_compl
  have hA0N : A 0 ∈ N := by
    rw [hA0]
    exact ⟨hin t ht00, htN t le_rfl⟩
  obtain ⟨α, -, hz, hA'⟩ := exists_line_slide hS hA hoff hZc (fun s hs h => by
      obtain ⟨s', hs', he⟩ := hAf s hs
      rw [he] at h
      rcases h with (h | h) | ⟨s'', hs'', he'⟩
      · exact h (hin s' (hne0 s' hs'))
      · rcases h with h | h
        · exact hu.2 ⟨s', h⟩
        · exact hv.2 ⟨s', h⟩
      · have := hc.2 he'
        exact absurd (show s'' ≤ t from hs'') (not_le.mpr (this ▸ hs'))) hN hA0N
  have huN : u ∉ N := fun h => h.2 ⟨0, γ.source⟩
  have hvN : v ∉ N := fun h => h.2 ⟨1, γ.target⟩
  have hαu : α u = u := by
    rcases hz u (.inl (.inr (.inl rfl))) with h | h
    · exact h
    · exact (huN h.1).elim
  have hαv : α v = v := by
    rcases hz v (.inl (.inr (.inr rfl))) with h | h
    · exact h
    · exact (hvN h.1).elim
  have hs1 : α.symm u = u := by rw [Homeomorph.symm_apply_eq, hαu]
  have hs2 : α.symm v = v := by rw [Homeomorph.symm_apply_eq, hαv]
  refine ⟨(γ.map α.symm.continuous).cast hs1.symm hs2.symm, fun s => ?_⟩
  change α.symm (γ s) ∈ X \ range c
  set w := α.symm (γ s) with hw
  have hαw : α w = γ s := by rw [hw, Homeomorph.apply_symm_apply]
  have hoffG : α w ∈ range γ := ⟨s, hαw.symm⟩
  constructor
  · by_contra hwX
    rcases hz w (.inl (.inl hwX)) with h' | h'
    · rw [hαw] at h'
      exact hwX (h' ▸ hγ s)
    · exact hwX h'.1.1
  · rintro ⟨s', hs'⟩
    by_cases hst : s' ≤ t
    · rcases hz w (.inr ⟨s', hst, hs'⟩) with h' | h'
      · rw [h'] at hoffG
        exact htN s' hst (hs' ▸ hoffG)
      · exact h'.2.2 hoffG
    · obtain ⟨s'', he⟩ := hfA s' (le_of_not_ge hst)
      have h1 := hA' s''
      rw [he, hs'] at h1
      exact h1.2 hoffG

/-- **A free line in `X` off the boundary does not separate `X`.** -/
theorem isPreconnected_sdiff_free (hS : IsSurface S) {X : Set S} (hXo : IsOpen X)
  (hXc : IsPreconnected X) (hXb : Disjoint X (bd S)) {c : unitInterval → S} (hc : IsArcMap c)
    (hin : ∀ s, c s ∈ X) :
    IsPreconnected (X \ range c) := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨T, tT, j, Kc, hT, hj, hKc, hu, hi', -⟩ := exists_capAll S hS
  have : T2Space T := hT.2.1
  obtain ⟨N', hN', hNe⟩ := hj.isInducing.isOpen_iff.mp hXo
  have himg : j '' X = N' ∩ Kcᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(hNe ▸ hx : x ∈ j ⁻¹' N'), fun hk => ?_⟩
      have : j x ∈ j '' bd S := by
        rw [← hi']
        exact ⟨mem_range_self _, hk⟩
      obtain ⟨x', hx', he⟩ := this
      exact disjoint_left.mp hXb hx (hj.injective he ▸ hx')
    · rintro ⟨h1, h2⟩
      rcases hu.symm ▸ mem_univ y with ⟨x, rfl⟩ | h
      · exact ⟨x, hNe ▸ (h1 : x ∈ j ⁻¹' N'), rfl⟩
      · exact (h2 h).elim
  have hp := IsPreconnected.diff_point hT (hXc.image j hj.continuous.continuousOn)
    (by rw [himg]; exact hN'.inter hKc.isOpen_compl) (j (c 0))
  have hX₁c : IsPreconnected (X \ {c 0}) := by
    rw [← hj.isInducing.isPreconnected_image, image_sdiff hj.injective, image_singleton]
    exact hp
  have h := isPreconnected_sdiff_line hS (hXo.sdiff isClosed_singleton) hX₁c hc (fun h => h.2 rfl)
    (fun s hs => ⟨hin s, fun h => hs (hc.2 h)⟩) fun s _ h => disjoint_left.mp hXb (hin s) h
  have he : (X \ {c 0}) \ range c = X \ range c := by
    ext z
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, fun hz => h.2 ⟨0, hz.symm⟩⟩, h.2⟩
  rwa [he] at h

/-- **A forest does not separate.** Remove the lines of a growth from an open connected set `X` one
at a time. Each line either misses `X` or lies in it, apart from its first end. -/
theorem isPreconnected_sdiff_growth (hS : IsSurface S) {B : Set S} {l : List (Set S)} {k : ℕ}
  (h : IsGrowth B l k) :
    ∀ X : Set S, bd S ⊆ B → IsOpen X → IsPreconnected X → Disjoint X B → (∀ A ∈ l, Disjoint A X
      ∨ A ⊆ X ∪ B) → IsPreconnected (X \ listUnion l) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hlines : ∀ {A X B : Set S} {l : List (Set S)}, IsClosed A → (∀ A' ∈ A :: l, Disjoint A' X
    ∨ A' ⊆ X ∪ B) → ∀ A' ∈ l, Disjoint A' (X \ A) ∨ A' ⊆ (X \ A) ∪ (B ∪ A)
      := fun {A X B l} _ h A' hA' => by
    rcases h A' (List.mem_cons_of_mem _ hA') with h1 | h1
    · exact .inl (h1.mono_right sdiff_subset)
    · refine .inr fun z hz => ?_
      by_cases hzA : z ∈ A
      · exact .inr (.inr hzA)
      · rcases h1 hz with h2 | h2
        · exact .inl ⟨h2, hzA⟩
        · exact .inr (.inl h2)
  have hlines' : ∀ {A X B : Set S} {l : List (Set S)}, (∀ A' ∈ A :: l, Disjoint A' X ∨ A' ⊆ X ∪ B)
    → ∀ A' ∈ l, Disjoint A' X ∨ A' ⊆ X ∪ (B ∪ A) := fun {A X B l} h A' hA' => by
    rcases h A' (List.mem_cons_of_mem _ hA') with h1 | h1
    · exact .inl h1
    · exact .inr fun z hz => (h1 hz).imp id .inl
  have hset : ∀ {A X : Set S} {l : List (Set S)}, X \ listUnion (A :: l) = (X \ A) \ listUnion l
    := fun {A X l} => by
    ext z
    simp only [listUnion_cons, mem_sdiff, mem_union]
    tauto
  have hset' : ∀ {A X : Set S} {l : List (Set S)}, Disjoint A X → X \ listUnion (A :: l)
    = X \ listUnion l := fun {A X l} hd => by
    ext z
    simp only [listUnion_cons, mem_sdiff, mem_union]
    constructor
    · exact fun h => ⟨h.1, fun h' => h.2 (.inr h')⟩
    · refine fun h => ⟨h.1, ?_⟩
      rintro (h' | h')
      · exact disjoint_left.mp hd h' h.1
      · exact h.2 h'
  induction h with
  | nil B =>
    intro X _ _ hc _ _
    simpa using hc
  | @free B A l k hA hd _ ih =>
    intro X hb hXo hXc hXB hl
    rcases hl A List.mem_cons_self with h1 | h1
    · rw [hset' h1]
      refine ih X (hb.trans subset_union_left) hXo hXc ?_ (hlines' hl)
      exact disjoint_union_right.mpr ⟨hXB, h1.symm⟩
    · obtain ⟨f⟩ := hA
      have hL : IsLineWithEnds A (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
      have hAc := hL.isCompact.isClosed
      have hc : IsArcMap fun t => (f t).1 := ⟨by fun_prop, fun x y h => f.injective (Subtype.ext h)⟩
      have hr : range (fun t => (f t).1) = A := by
        ext z
        exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩⟩
      have hAX : ∀ t, (f t).1 ∈ X := fun t => (h1 (f t).2).resolve_right fun h => by
        have : (f t).1 ∈ A ∩ B := ⟨(f t).2, h⟩
        rw [hd] at this
        exact this
      have h2 := isPreconnected_sdiff_free hS hXo hXc (hXB.mono_right hb) hc hAX
      rw [hr] at h2
      rw [hset]
      refine ih (X \ A) (hb.trans subset_union_left) (hXo.sdiff hAc) h2 ?_ (hlines hAc hl)
      exact disjoint_union_right.mpr ⟨hXB.mono_left sdiff_subset, disjoint_sdiff_left⟩
  | @attached B A l k p q hA hd _ ih =>
    intro X hb hXo hXc hXB hl
    rcases hl A List.mem_cons_self with h1 | h1
    · rw [hset' h1]
      refine ih X (hb.trans subset_union_left) hXo hXc ?_ (hlines' hl)
      exact disjoint_union_right.mpr ⟨hXB, h1.symm⟩
    · obtain ⟨f, h0, h2⟩ := hA
      have hL : IsLineWithEnds A p q := ⟨f, h0, h2⟩
      have hAc := hL.isCompact.isClosed
      have hc : IsArcMap fun t => (f t).1 := ⟨by fun_prop, fun x y h => f.injective (Subtype.ext h)⟩
      have hr : range (fun t => (f t).1) = A := by
        ext z
        exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩⟩
      have hoffB : ∀ s, s ≠ 0 → (f s).1 ∉ B := fun s hs h => by
        have h3 : (f s).1 ∈ A ∩ B := ⟨(f s).2, h⟩
        rw [hd] at h3
        have h4 : (f s).1 = (f 0).1 := h3.trans h0.symm
        exact hs (f.injective (Subtype.ext h4))
      have hpB : (f 0).1 ∈ B := by
        have : p ∈ A ∩ B := by rw [hd]; rfl
        rw [h0]
        exact this.2
      have h3 := isPreconnected_sdiff_line hS hXo hXc hc (fun h => disjoint_left.mp hXB h hpB)
        (fun s hs => (h1 (f s).2).resolve_right (hoffB s hs)) fun s hs h => hoffB s hs (hb h)
      rw [hr] at h3
      rw [hset]
      refine ih (X \ A) (hb.trans subset_union_left) (hXo.sdiff hAc) h3 ?_ (hlines hAc hl)
      exact disjoint_union_right.mpr ⟨hXB.mono_left sdiff_subset, disjoint_sdiff_left⟩

theorem IsGrowth.isLine {B : Set S} {l : List (Set S)} {k : ℕ} (h : IsGrowth B l k) : ∀ A ∈ l,
  IsLine A := by
  induction h with
  | nil B => simp
  | free hA _ _ ih =>
    intro A' h
    rcases List.mem_cons.mp h with rfl | h
    · exact hA
    · exact ih A' h
  | attached hA _ _ ih =>
    intro A' h
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨f, -, -⟩ := hA
      exact ⟨f⟩
    · exact ih A' h

theorem IsLine.isPreconnected {A : Set S} (h : IsLine A) : IsPreconnected A := by
  obtain ⟨f⟩ := h
  have hr : A = range fun t => (f t).1 := by
    ext z
    exact ⟨fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩, by rintro ⟨t, rfl⟩; exact (f t).2⟩
  rw [hr]
  exact isPreconnected_range (by fun_prop)

/-- **The part of a cut surface over a component of the forest is connected.** A small connected
open set `W` around `T` stays connected when the forest and `bd(Σ)` are removed. So its preimage off
`bd(Σ')` is connected, and `φ⁻¹(T)` lies in the closure of this preimage. -/
theorem isPreconnected_preimage_tree (hS : IsSurface S) {L : Drawing S} {φ : S' → S}
  (hJ : IsCutAlongGraph L S' φ) (hN : NoArcs L) {T : Set S} (hT : IsPreconnected T)
    (hTc : IsClosed T) (hrest : IsClosed (L.U \ T)) :
    IsPreconnected (φ ⁻¹' T) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hY := hJ.isSurface
  have : CompactSpace S' := hY.1
  have : T2Space S' := hY.2.1
  have hlc := hS.locallyConnected
  have hcont := hJ.quotientMap.continuous
  rcases T.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simpa using isPreconnected_empty
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsub huv
  have hAc : IsClosed (φ ⁻¹' T) := hTc.preimage hcont
  obtain ⟨U', V', hU', hV', huU, hvV, hd⟩ := normal_separation (hu.inter hAc) (hv.inter hAc)
    (disjoint_iff_inter_eq_empty.mpr (by
    ext z
    have := Set.ext_iff.mp huv z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false] at this ⊢
    tauto))
  let E : Set S' := (U' ∪ V')ᶜ
  have hEc : IsClosed E := (hU'.union hV').isClosed_compl
  have hφE : IsClosed (φ '' E) := hcont.isClosedMap _ hEc
  let P : Set S := (φ '' E ∪ (L.U \ T))ᶜ
  have hPo : IsOpen P := (hφE.union hrest).isOpen_compl
  have hTP : T ⊆ P := by
    rintro t ht (⟨e, he, rfl⟩ | h)
    · rcases hsub ht with h | h
      · exact he (.inl (huU ⟨h, ht⟩))
      · exact he (.inr (hvV ⟨h, ht⟩))
    · exact h.2 ht
  let W : Set S := connectedComponentIn P t₀
  have hWo : IsOpen W := hPo.connectedComponentIn
  have hTW : T ⊆ W := hT.subset_connectedComponentIn ht₀ hTP
  have hWP : W ⊆ P := connectedComponentIn_subset _ _
  obtain ⟨l, k, hg, hun, -⟩ := exists_growth _ L rfl hJ.isProper hN
  have hUl : listUnion l = L.U := by rw [hun, ← U_eq_biUnion_closure hJ.noIsolated]
  let X : Set S := W \ bd S
  have hXo : IsOpen X := hWo.sdiff (isClosed_bd S)
  have hXc : IsPreconnected X := isPreconnected_diff_bd hS hWo isPreconnected_connectedComponentIn
  have hl : ∀ A ∈ l, Disjoint A X ∨ A ⊆ X ∪ bd S := fun A hA => by
    have hAL : A ⊆ L.U := fun z hz => hUl ▸ (mem_sUnion_of_mem hz hA : z ∈ listUnion l)
    have hcov : A ⊆ T ∪ (L.U \ T) := fun z hz => by
      by_cases hzT : z ∈ T
      · exact .inl hzT
      · exact .inr ⟨hAL hz, hzT⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp (IsLine.isPreconnected
      (hg.isLine A hA))) _ _ hTc hrest hcov (by
      ext z
      simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]
      tauto) with h | h
    · refine .inr fun z hz => ?_
      by_cases hb : z ∈ bd S
      · exact .inr hb
      · exact .inl ⟨hTW (h hz), hb⟩
    · refine .inl (disjoint_left.mpr fun z hz hzX => ?_)
      exact hWP hzX.1 (.inr (h hz))
  have hX₀ := isPreconnected_sdiff_growth hS hg X subset_rfl hXo hXc disjoint_sdiff_left hl
  have hF : IsClosed (bd S ∪ L.U) := (isClosed_bd S).union L.isClosed_U
  have hm : GM19.IsCutMap φ (bd S ∪ L.U) := hJ.toSet.isCutMap
  have hsubF : X \ listUnion l ⊆ (bd S ∪ L.U)ᶜ := by
    rintro z ⟨hz, hzl⟩ (h | h)
    · exact hz.2 h
    · exact hzl (hUl ▸ h)
  have hC₀ := GM19.isPreconnected_preimage_of_isCutMap hm hF hsubF hX₀
  set C₀ : Set S' := φ ⁻¹' (X \ listUnion l) with hC₀def
  have hAcl : φ ⁻¹' T ⊆ closure C₀ := fun x hx => by
    have h1 := mem_closure_compl_bd (hY.2.2 x)
    have h2 := (hWo.preimage hcont).inter_closure ⟨hTW hx, h1⟩
    refine closure_mono (fun y hy => ?_) h2
    have hyF : φ y ∉ bd S ∪ L.U := fun h => hy.2 (by rw [← hJ.preimage_bd_union_U]; exact h)
    refine ⟨⟨hy.1, fun h => hyF (.inl h)⟩, fun h => hyF (.inr (hUl ▸ h))⟩
  have hC : IsPreconnected (C₀ ∪ φ ⁻¹' T) := hC₀.subset_closure subset_union_left
    (union_subset subset_closure hAcl)
  have hCsub : C₀ ∪ φ ⁻¹' T ⊆ U' ∪ V' := by
    have key : ∀ y, φ y ∈ P → y ∈ U' ∪ V' := fun y hy => by
      by_contra hn
      exact hy (.inl ⟨y, hn, rfl⟩)
    rintro y (hy | hy)
    · exact key y (hWP hy.1.1)
    · exact key y (hTP hy)
  rcases hC.subset_or_subset hU' hV' hd hCsub with h | h
  · refine .inl fun x hx => ?_
    rcases hsub hx with h1 | h1
    · exact h1
    · exact (disjoint_left.mp hd (h (.inr hx)) (hvV ⟨h1, hx⟩)).elim
  · refine .inr fun x hx => ?_
    rcases hsub hx with h1 | h1
    · exact (disjoint_left.mp hd (huU ⟨h1, hx⟩) (h (.inr hx))).elim
    · exact h1

end GraphMinor.GM07
