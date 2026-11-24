/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialAccess
public import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# Chords of a region of a radial drawing

A line `K` from a vertex `c = v_r` of a radial drawing `Γ'` to a vertex `x` of `Γ`, inside the
region
`r` of `Γ` and off `Γ'`, cannot be added to `Γ'`, because `Γ'` is maximal. Conditions (i)-(iii) hold
for `Γ' + K`, so condition (iv) fails. So `K` and an edge of `Γ'` bound a closed disc in `r ∪ {x}`
(`exists_parallel_spoke`). This is the only place where maximality is used.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The range of an injective path in a Hausdorff space is a line. -/
theorem isLine_range [T2Space S] {g : I → S} (hg : Continuous g) (hi : Function.Injective g) :
    IsLineWithEnds (range g) (g 0) (g 1) := by
  have hemb := hg.isClosedEmbedding hi
  let f : I ≃ₜ range g := hemb.isEmbedding.toHomeomorph
  exact ⟨f, rfl, rfl⟩

/-- A line through a path-connected set `p`, from `x` to `c`, that starts along `g₁`. -/
theorem exists_chord [T2Space S] {p : Set S} (hp : IsPathConnected p) {x c : S} (hxc : x ≠ c)
    (hxp : x ∉ p) {g₁ g₂ : I → S} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (h₁0 : g₁ 0 = x) (h₂0 : g₂ 0 = c) (h₁ : ∀ t, 0 < t → g₁ t ∈ p) (h₂ : ∀ t, 0 < t → g₂ t ∈ p) :
    ∃ e : I → S, Continuous e ∧ Function.Injective e ∧ e 0 = x ∧ e 1 = c ∧
      (∀ t, t ≠ 0 → t ≠ 1 → e t ∈ p) ∧
      ∃ O, IsOpen O ∧ x ∈ O ∧ ∀ t, e t ∈ O → e t ∈ range g₁ := by
  have h₁1 : g₁ 1 ∈ p := h₁ 1 one_pos
  have h₂1 : g₂ 1 ∈ p := h₂ 1 one_pos
  let a : Path x (g₁ 1) := ⟨⟨g₁, hg₁⟩, h₁0, rfl⟩
  let b : Path c (g₂ 1) := ⟨⟨g₂, hg₂⟩, h₂0, rfl⟩
  obtain ⟨m, hm⟩ := hp.joinedIn _ h₁1 _ h₂1
  let ℓ : Path x c := (a.trans m).trans b.symm
  have hr : range ℓ = range g₁ ∪ range m ∪ range g₂ := by
    simp only [ℓ, Path.trans_range, Path.symm_range]
    rfl
  obtain ⟨e, he, hi, he0, he1, hsub⟩ := exists_arc_of_path (γ := ℓ) ℓ.continuous
    (by simpa using hxc)
  have he0' : e 0 = x := by simpa using he0
  have he1' : e 1 = c := by simpa using he1
  have hsub' : ∀ t, e t ∈ range g₁ ∪ range m ∪ range g₂ := fun t => hr ▸ hsub ⟨t, rfl⟩
  have hgood : ∀ {g : I → S} {z : S}, (g 0 = z) → (∀ t, 0 < t → g t ∈ p) → ∀ y ∈ range g, y ≠ z →
      y ∈ p := by
    rintro g z h0 h _ ⟨t, rfl⟩ hy
    by_cases ht : t = 0
    · exact absurd (ht ▸ h0) hy
    · exact h t (unitInterval.pos_iff_ne_zero.mpr ht)
  refine ⟨e, he, hi, he0', he1', ?_, ?_⟩
  · intro t ht0 ht1
    have hne0 : e t ≠ x := fun h => ht0 (hi (h.trans he0'.symm))
    have hne1 : e t ≠ c := fun h => ht1 (hi (h.trans he1'.symm))
    rcases hsub' t with (h' | h') | h'
    · exact hgood h₁0 h₁ _ h' hne0
    · obtain ⟨s, hs⟩ := h'
      exact hs ▸ hm s
    · exact hgood h₂0 h₂ _ h' hne1
  · let B : Set S := range m ∪ range g₂
    have hB : IsClosed B := ((isCompact_range m.continuous).union (isCompact_range hg₂)).isClosed
    refine ⟨Bᶜ, hB.isOpen_compl, ?_, fun t ht => ?_⟩
    · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
      · exact hxp (hs ▸ hm s)
      · by_cases h0 : s = 0
        · exact hxc ((h0 ▸ hs).symm.trans h₂0)
        · exact hxp (hs ▸ h₂ s (unitInterval.pos_iff_ne_zero.mpr h0))
    · rcases hsub' t with (h' | h') | h'
      · exact h'
      · exact absurd (Or.inl h') ht
      · exact absurd (Or.inr h') ht

/-- A line from `x` to a point `c` of a path-connected set `p`, inside `p` after time `0`. -/
theorem exists_chord_to_point [T2Space S] {p : Set S} (hp : IsPathConnected p) {x c : S}
    (hxp : x ∉ p) (hcp : c ∈ p) {g₁ : I → S} (hg₁ : Continuous g₁) (h₁0 : g₁ 0 = x)
    (h₁ : ∀ t, 0 < t → g₁ t ∈ p) :
    ∃ e : I → S, Continuous e ∧ Function.Injective e ∧ e 0 = x ∧ e 1 = c ∧ (∀ t, t ≠ 0 → e t ∈ p) ∧
      ∃ O, IsOpen O ∧ x ∈ O ∧ ∀ t, e t ∈ O → e t ∈ range g₁ := by
  have h₁1 : g₁ 1 ∈ p := h₁ 1 one_pos
  have hxc : x ≠ c := fun h => hxp (h ▸ hcp)
  let a : Path x (g₁ 1) := ⟨⟨g₁, hg₁⟩, h₁0, rfl⟩
  obtain ⟨m, hm⟩ := hp.joinedIn _ h₁1 _ hcp
  let ℓ : Path x c := a.trans m
  have hr : range ℓ = range g₁ ∪ range m := by
    simp only [ℓ, Path.trans_range]
    rfl
  obtain ⟨e, he, hi, he0, he1, hsub⟩ := exists_arc_of_path (γ := ℓ) ℓ.continuous
    (by simpa using hxc)
  have he0' : e 0 = x := by simpa using he0
  have he1' : e 1 = c := by simpa using he1
  have hsub' : ∀ t, e t ∈ range g₁ ∪ range m := fun t => hr ▸ hsub ⟨t, rfl⟩
  refine ⟨e, he, hi, he0', he1', fun t ht => ?_, (range m)ᶜ,
    (isCompact_range m.continuous).isClosed.isOpen_compl, ?_, fun t ht => ?_⟩
  · have hne0 : e t ≠ x := fun h => ht (hi (h.trans he0'.symm))
    rcases hsub' t with ⟨s, hs⟩ | ⟨s, hs⟩
    · by_cases h0 : s = 0
      · exact absurd (hs.symm.trans (h0 ▸ h₁0)) hne0
      · exact hs ▸ h₁ s (unitInterval.pos_iff_ne_zero.mpr h0)
    · exact hs ▸ hm s
  · rintro ⟨s, hs⟩
    exact hxp (hs ▸ hm s)
  · exact (hsub' t).resolve_right ht

section LineDrawing

variable [T2Space S] {K : Set S} {c x : S}

omit [T2Space S] in
theorem exists_line_param (hK : IsLineWithEnds K c x) :
    ∃ g : I → S, Continuous g ∧ range g = K ∧ K \ {c, x} = g '' Ioo (0 : I) 1 := by
  obtain ⟨f, h0, h1⟩ := hK
  refine ⟨fun t => (f t).1, by fun_prop, ?_, ?_⟩
  · ext y
    exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hy => ⟨f.symm ⟨y, hy⟩, by simp⟩⟩
  ext y
  constructor
  · rintro ⟨hy, hn⟩
    refine ⟨f.symm ⟨y, hy⟩, ⟨?_, ?_⟩, by simp⟩
    · refine unitInterval.pos_iff_ne_zero.mpr fun h => hn (Or.inl ?_)
      have := congrArg f h
      simp only [Homeomorph.apply_symm_apply] at this
      exact (congrArg Subtype.val this).trans h0
    · refine lt_of_le_of_ne (unitInterval.le_one _) fun h => hn (Or.inr ?_)
      have := congrArg f h
      simp only [Homeomorph.apply_symm_apply] at this
      exact (congrArg Subtype.val this).trans h1
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨(f t).2, ?_⟩
    rintro (h | h)
    · exact ht0.ne' (f.injective (Subtype.ext (h.trans h0.symm)))
    · exact ht1.ne (f.injective (Subtype.ext (h.trans h1.symm)))

omit [T2Space S] in
theorem isPathConnected_sdiff_pair (hK : IsLineWithEnds K c x) : IsPathConnected (K \ {c, x}) := by
  obtain ⟨g, hg, -, hEq⟩ := exists_line_param hK
  rw [hEq]
  have hI : Ioo (0 : I) 1 = projIcc 0 1 zero_le_one '' Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · intro ht
      refine ⟨t, ⟨ht.1, ht.2⟩, ?_⟩
      exact projIcc_val _ t
    · rintro ⟨u, hu, rfl⟩
      rw [mem_Ioo, ← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe,
        projIcc_of_mem zero_le_one (Ioo_subset_Icc_self hu)]
      exact hu
  have hcon : IsPathConnected (Ioo (0 : I) 1) := by
    rw [hI]
    exact ((convex_Ioo (0 : ℝ) 1).isPathConnected (by norm_num)).image continuous_projIcc
  exact hcon.image hg

theorem closure_sdiff_pair (hK : IsLineWithEnds K c x) : closure (K \ {c, x}) = K := by
  obtain ⟨g, hg, hr, hEq⟩ := exists_line_param hK
  have hKc : IsClosed K := hr ▸ (isCompact_range hg).isClosed
  apply subset_antisymm (closure_minimal sdiff_subset hKc)
  rw [hEq, ← hr]
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ closure (Ioo (0 : I) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨t.2.1, t.2.2⟩
  exact map_mem_closure hg ht fun s hs => ⟨s, hs, rfl⟩

/-- A line, as a drawing with one edge. -/
noncomputable def lineDrawing (hK : IsLineWithEnds K c x) (hcx : c ≠ x) : Drawing S where
  U := K
  V := {c, x}
  V_subset_U := by
    obtain ⟨f, h0, h1⟩ := hK
    rintro y (rfl | rfl)
    · exact h0 ▸ (f 0).2
    · exact h1 ▸ (f 1).2
  isClosed_U := by
    rw [← closure_sdiff_pair hK]
    exact isClosed_closure
  finite_V := by simp
  finite_edges := by
    refine (finite_singleton (K \ {c, x})).subset ?_
    rintro C ⟨-, hsub, -, hmax⟩
    exact (hmax _ Subset.rfl (isPathConnected_sdiff_pair hK) hsub).symm ▸ rfl
  edge_cond := by
    rintro C ⟨-, hsub, -, hmax⟩
    have hC : C = K \ {c, x} := (hmax _ Subset.rfl (isPathConnected_sdiff_pair hK) hsub).symm
    subst hC
    rw [closure_sdiff_pair hK]
    refine Or.inl ⟨c, x, hcx, ?_, hK⟩
    apply inter_eq_right.mpr
    obtain ⟨f, h0, h1⟩ := hK
    rintro y (rfl | rfl)
    · exact h0 ▸ (f 0).2
    · exact h1 ▸ (f 1).2

theorem lineDrawing_E (hK : IsLineWithEnds K c x) (hcx : c ≠ x) :
    (lineDrawing hK hcx).E = {K \ {c, x}} := by
  apply subset_antisymm
  · rintro C ⟨-, hsub, -, hmax⟩
    exact (hmax _ Subset.rfl (isPathConnected_sdiff_pair hK) hsub).symm
  · rintro _ rfl
    refine ⟨(isPathConnected_sdiff_pair hK).nonempty, Subset.rfl,
      isPathConnected_sdiff_pair hK, fun D hD _ hsub => subset_antisymm hD hsub⟩

end LineDrawing

variable [T2Space S] {K : Set S} {c x : S}

/-- `Γ` is 2-cell and `Γ'` satisfies conditions (i)–(iv) of a radial drawing of it. -/
def PreRad (Γ : PaintingOrDrawing S) (Γ' : Drawing S) : Prop :=
  Γ.IsTwoCell ∧ Γ.IsPreRadialDrawing Γ'

/-- Condition (v) of a radial drawing: `Γ'` is maximal subject to (i)–(iv). -/
def RadMax (Γ : PaintingOrDrawing S) (Γ' : Drawing S) : Prop :=
  ∀ Γ'' : Drawing S, Γ.IsPreRadialDrawing Γ'' → Γ'.IsSubdrawing Γ'' → Γ''.IsSubdrawing Γ'

/-- **A chord has a parallel spoke.** Graph Minors XI, Section 3, uses the maximality in condition
(v) of a radial drawing in this form, without stating it. -/
theorem exists_parallel_spoke {Γ : PaintingOrDrawing S} {Γ' : Drawing S}
    (hpre : Γ.IsPreRadialDrawing Γ') (hmax : RadMax Γ Γ')
    {r : Set S} (hr : r ∈ Γ.R) (hcr : c ∈ r) (hc : c ∈ Γ'.V) (hx : x ∈ Γ.V)
    (hK : IsLineWithEnds K c x) (hcx : c ≠ x) (hKr : K \ {c, x} ⊆ r)
    (hKU : Disjoint (K \ {c, x}) Γ'.U) (hrU : Disjoint r Γ.U)
    (hrr : ∀ {r₁ r₂ : Set S}, r₁ ∈ Γ.R → r₂ ∈ Γ.R → ∀ {y : S}, y ∈ r₁ → y ∈ r₂ → r₁ = r₂) :
    ∃ h ∈ Γ'.E, closure h ∩ Γ'.V = {x, c} ∧ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {x} ∧
      subBd Δ = closure h ∪ K := by
  classical
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hpre
  have hxV : x ∈ Γ'.V := h₂ hx
  have hVsub : (lineDrawing hK hcx).V ⊆ Γ'.V := by
    rintro y (rfl | rfl)
    · exact hc
    · exact hxV
  have hmeet : Γ'.U ∩ (lineDrawing hK hcx).U ⊆ Γ'.V ∩ (lineDrawing hK hcx).V := by
    rintro y ⟨hy, hyK⟩
    have : y ∈ ({c, x} : Set S) := by
      by_contra hn
      exact disjoint_left.mp hKU ⟨hyK, hn⟩ hy
    exact ⟨hVsub this, this⟩
  let G : Drawing S := Γ'.glue (lineDrawing hK hcx) hmeet
  have hGV : G.V = Γ'.V := union_eq_left.mpr hVsub
  have hGE : G.E = Γ'.E ∪ {K \ {c, x}} := by
    change (Γ'.glue (lineDrawing hK hcx) hmeet).E = _
    rw [Drawing.glue_E, lineDrawing_E]
  have hKcl : closure (K \ {c, x}) = K := closure_sdiff_pair hK
  have hKV : K ∩ Γ'.V = {x, c} := by
    apply subset_antisymm
    · rintro y ⟨hyK, hyV⟩
      by_contra hn
      have hn' : y ∉ ({c, x} : Set S) := fun h => hn (by rw [pair_comm]; exact h)
      exact disjoint_left.mp hKU ⟨hyK, hn'⟩ (Γ'.V_subset_U hyV)
    · have hend : ({c, x} : Set S) ⊆ K := (lineDrawing hK hcx).V_subset_U
      rintro y (rfl | rfl)
      · exact ⟨hend (Or.inr rfl), hxV⟩
      · exact ⟨hend (Or.inl rfl), hc⟩
  have hVU : Γ.V ⊆ Γ.U := by
    rw [← h₁]
    exact inter_subset_left
  have hcnV : c ∉ Γ.V := fun h => disjoint_left.mp hrU hcr (hVU h)
  by_contra hno
  have hiv : ∀ e ∈ G.E, ∀ f ∈ G.E, e ≠ f → ∀ v ∈ Γ.V, ∀ r' ∈ Γ.R, ∀ w ∈ r' ∩ G.V,
      closure e ∩ G.V = {v, w} → closure f ∩ G.V = {v, w} →
      ¬ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r' ∪ {v} ∧ subBd Δ = closure e ∪ closure f := by
    -- The case of `K` and an old edge.
    have key : ∀ f ∈ Γ'.E, ∀ v ∈ Γ.V, ∀ r' ∈ Γ.R, ∀ w ∈ r' ∩ Γ'.V,
        K ∩ Γ'.V = {v, w} → closure f ∩ Γ'.V = {v, w} →
        ¬ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r' ∪ {v} ∧ subBd Δ = closure f ∪ K := by
      intro f hf v hv r' hr' w hw hKe hfe hΔ
      have hmx : x ∈ ({v, w} : Set S) := hKe ▸ (show x ∈ K ∩ Γ'.V by rw [hKV]; simp)
      have hmc : c ∈ ({v, w} : Set S) := hKe ▸ (show c ∈ K ∩ Γ'.V by rw [hKV]; simp)
      have hvc : c ≠ v := fun h => hcnV (h ▸ hv)
      have hcw : c = w := hmc.resolve_left hvc
      subst hcw
      have hr'r : r' = r := hrr hr' hr hw.1 hcr
      have hxv : x = v := by
        rcases hmx with h | h
        · exact h
        · exact absurd h.symm hcx
      subst hxv
      subst hr'r
      obtain ⟨Δ, hd, hsubΔ, hb⟩ := hΔ
      exact hno ⟨f, hf, hfe, Δ, hd, hsubΔ, hb⟩
    rw [hGE, hGV]
    rintro e (he | rfl) f (hf | rfl) hef v hv r' hr' w hw hee hfe hΔ
    · exact h₆ e he f hf hef v hv r' hr' w hw hee hfe hΔ
    · rw [hKcl] at hfe hΔ
      exact key e he v hv r' hr' w hw hfe hee hΔ
    · rw [hKcl] at hee hΔ
      obtain ⟨Δ, a, b, c'⟩ := hΔ
      exact key f hf v hv r' hr' w hw hee hfe ⟨Δ, a, b, by rw [c', union_comm]⟩
    · exact hef rfl
  have hpre' : Γ.IsPreRadialDrawing G := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hiv⟩
    · apply subset_antisymm
      · rintro y ⟨hyU, hyG | hyK⟩
        · rw [← h₁]
          exact ⟨hyU, hyG⟩
        · by_cases hym : y ∈ ({c, x} : Set S)
          · rcases hym with rfl | rfl
            · exact (disjoint_left.mp hrU hcr hyU).elim
            · exact hx
          · exact (disjoint_left.mp hrU (hKr ⟨hyK, hym⟩) hyU).elim
      · intro y hy
        rw [← h₁] at hy
        exact ⟨hy.1, Or.inl hy.2⟩
    · rw [hGV]
      exact h₂
    · rw [hGV]
      exact h₃
    · rw [hGV]
      exact h₄
    · intro e he
      rw [hGE] at he
      rw [hGV]
      rcases he with he | rfl
      · exact h₅ e he
      · exact ⟨x, hx, c, ⟨hc, hcnV⟩, by rw [hKcl]; exact hKV⟩
  have hsub : Γ'.IsSubdrawing G := ⟨by rw [hGV], by rw [hGE]; exact subset_union_left⟩
  have hback := hmax G hpre' hsub
  have hmem : K \ {c, x} ∈ Γ'.E := hback.2 (by rw [hGE]; exact Or.inr rfl)
  obtain ⟨y, hy⟩ := (isPathConnected_sdiff_pair hK).nonempty
  exact disjoint_left.mp hKU hy (Γ'.closure_subset_U hmem (subset_closure hy))

end GraphMinor.GM11
