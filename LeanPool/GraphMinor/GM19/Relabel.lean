/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Conditional
public import LeanPool.GraphMinor.GM19.Section4a
public import LeanPool.GraphMinor.GM19.Defs3
public import LeanPool.GraphMinor.GM11.PaintingCells

/-!
# Changing the labels of a colour scheme

Section 15 of Graph Minors XIX starts: "(by replacing the $\Omega_\chi(k)$'s and $\Omega_\chi(S)$'s
by isomorphic
well-quasi-orders) we may choose $\chi$ to be disjoint". A colour scheme here has one type of
labels, and
`S₂`, `S₃`, `S₄` compare schemes over that type. So we keep the type and move the labels inside it.
This needs a type `β` that holds a copy of `β × ℕ`, that is, an infinite one. The proof of (3.1) can
pick such a type, by first moving the labels of a bad scheme to `Option β × ℕ`.

`LabelMap χ χ'` is a map of labels. It sends a `χ`-coloured painting to a `χ'`-coloured painting
with
the same painting. A linear inflation of the new paintings is one of the old paintings, so a bad
sequence stays bad. We need linear inflations here, since these send internal edges to internal
edges, and only then do the labels of an edge and of its image come from the same quasi-order.

The main results are `IsBad.of_labelMap`, `IsOrientedlyBad.of_labelMap` and `exists_disjoint`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u w

variable {S : Type u} [TopologicalSpace S] {α α' : Type w}

namespace QuasiOrder

/-- The copy of `Ω` under an injection `i`. -/
def map (Ω : QuasiOrder α) (i : α → α') (hi : Injective i) : QuasiOrder α' where
  E := i '' Ω.E
  le a b := ∃ x y, a = i x ∧ b = i y ∧ Ω.le x y
  refl := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, x, rfl, rfl, Ω.refl x hx⟩
  trans := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ ⟨a, b, h₁, h₂, h⟩ ⟨c, d, h₃, h₄, h'⟩
    obtain rfl := hi h₁
    obtain rfl := hi h₂
    obtain rfl := hi h₃
    obtain rfl := hi h₄
    exact ⟨_, _, rfl, rfl, Ω.trans _ hx _ hy _ hz h h'⟩

/-- The pull-back of `Ω` along `i`. -/
def comap (Ω : QuasiOrder α') (i : α → α') : QuasiOrder α where
  E := i ⁻¹' Ω.E
  le x y := Ω.le (i x) (i y)
  refl _x hx := Ω.refl _ hx
  trans _x hx _y hy _z hz := Ω.trans _ hx _ hy _ hz

theorem map_isWQO {Ω : QuasiOrder α} {i : α → α'} (hi : Injective i) (h : Ω.IsWQO) :
    (Ω.map i hi).IsWQO := by
  intro f hf
  choose g hg hgf using hf
  obtain ⟨a, b, hab, hle⟩ := h g hg
  exact ⟨a, b, hab, g a, g b, (hgf a).symm, (hgf b).symm, hle⟩

theorem comap_isWQO {Ω : QuasiOrder α'} {i : α → α'} (h : Ω.IsWQO) : (Ω.comap i).IsWQO :=
  fun f hf ↦ h (i ∘ f) hf

theorem comap_map (Ω : QuasiOrder α) {i : α → α'} (hi : Injective i) :
    (Ω.map i hi).comap i = Ω := by
  have hE : ((Ω.map i hi).comap i).E = Ω.E := preimage_image_eq _ hi
  have hle : ((Ω.map i hi).comap i).le = Ω.le := by
    funext x y
    refine propext ⟨?_, fun h ↦ ⟨x, y, rfl, rfl, h⟩⟩
    rintro ⟨a, b, h₁, h₂, h⟩
    rw [hi h₁, hi h₂]
    exact h
  cases h : (Ω.map i hi).comap i
  cases Ω
  simp only [h, mk.injEq] at hE hle ⊢
  exact ⟨hE, hle⟩

theorem comap_subIdeal {Ω' : QuasiOrder α'} {Ω : QuasiOrder α} {i : α → α'} (hi : Injective i)
    (h : Ω'.IsSubIdeal (Ω.map i hi)) : (Ω'.comap i).IsSubIdeal Ω where
  E_subset x hx := by
    obtain ⟨y, hy, hxy⟩ := h.E_subset hx
    rwa [← hi hxy]
  downward_closed x' hx' x hx hle :=
    h.downward_closed _ hx' _ (mem_image_of_mem _ hx) ⟨x, x', rfl, rfl, hle⟩
  le_iff x₁ hx₁ x₂ hx₂ := by
    refine (h.le_iff _ hx₁ _ hx₂).trans ⟨?_, fun h' ↦ ⟨_, _, rfl, rfl, h'⟩⟩
    rintro ⟨a, b, h₁, h₂, h'⟩
    rw [hi h₁, hi h₂]
    exact h'

theorem comap_E_ne {Ω' : QuasiOrder α'} {Ω : QuasiOrder α} {i : α → α'} (hi : Injective i)
    (h : Ω'.IsSubIdeal (Ω.map i hi)) (hne : Ω'.E ≠ (Ω.map i hi).E) : (Ω'.comap i).E ≠ Ω.E := by
  intro hE
  refine hne (Subset.antisymm h.E_subset ?_)
  rintro _ ⟨x, hx, rfl⟩
  rw [← hE] at hx
  exact hx

end QuasiOrder

/-- A map of labels from `χ` to `χ'`, which have the same frame. It may depend on the kind of edge.
It
preserves the element sets and reflects the order. -/
structure LabelMap (χ : ColourScheme S α) (χ' : ColourScheme S α') where
  hΦ : χ'.Φ = χ.Φ
  /-- The relabeling for interior edges with two ends. -/
  f2 : α → α'
  /-- The relabeling for interior edges with three ends. -/
  f3 : α → α'
  /-- The relabeling for an edge on a specified side. -/
  fS : Set S → α → α'
  map_2 : ∀ x ∈ χ.Ω2.E, f2 x ∈ χ'.Ω2.E
  map_3 : ∀ x ∈ χ.Ω3.E, f3 x ∈ χ'.Ω3.E
  map_S : ∀ s ∈ χ.Φ.sides, ∀ x ∈ (χ.ΩS s).E, fS s x ∈ (χ'.ΩS s).E
  le_2 : ∀ x ∈ χ.Ω2.E, ∀ y ∈ χ.Ω2.E, χ'.Ω2.le (f2 x) (f2 y) → χ.Ω2.le x y
  le_3 : ∀ x ∈ χ.Ω3.E, ∀ y ∈ χ.Ω3.E, χ'.Ω3.le (f3 x) (f3 y) → χ.Ω3.le x y
  le_S : ∀ s ∈ χ.Φ.sides, ∀ x ∈ (χ.ΩS s).E, ∀ y ∈ (χ.ΩS s).E,
    (χ'.ΩS s).le (fS s x) (fS s y) → (χ.ΩS s).le x y

namespace LabelMap

variable {χ : ColourScheme S α} {χ' : ColourScheme S α'}

open Classical in
/-- The new label of an edge. -/
noncomputable def col (m : LabelMap χ χ') (P : ColouredPainting χ) (e : Set S) : α' :=
  if Painting.IsInternal e then
    (if (tilde e).ncard = 2 then m.f2 (P.φ e) else m.f3 (P.φ e))
  else if h : ∃ s ∈ χ.Φ.sides, BordersSide e s then m.fS h.choose (P.φ e) else m.f2 (P.φ e)

theorem col_two (m : LabelMap χ χ') (P : ColouredPainting χ) {e : Set S}
    (hi : Painting.IsInternal e) (h2 : (tilde e).ncard = 2) : m.col P e = m.f2 (P.φ e) := by
  simp [col, hi, h2]

theorem col_three (m : LabelMap χ χ') (P : ColouredPainting χ) {e : Set S}
    (hi : Painting.IsInternal e) (h3 : (tilde e).ncard = 3) : m.col P e = m.f3 (P.φ e) := by
  simp [col, hi, h3]

theorem not_internal {e s : Set S} (h : BordersSide e s) : ¬ Painting.IsInternal e := by
  obtain ⟨x, hx, hb⟩ := h.1
  exact fun hi ↦ disjoint_left.mp hi hx hb

theorem col_border (m : LabelMap χ χ') (P : ColouredPainting χ) {e s : Set S} (he : e ∈ P.Γ.E)
    (hs : s ∈ χ.Φ.sides) (hb : BordersSide e s) : m.col P e = m.fS s (P.φ e) := by
  classical
  have hex : ∃ s ∈ χ.Φ.sides, BordersSide e s := ⟨s, hs, hb⟩
  have hspec := hex.choose_spec
  obtain ⟨x, hx⟩ : e.Nonempty := he.2.2.1.nonempty
  have hsame : hex.choose = s := GM11.arcComponent_eq hspec.1 hs (hspec.2.2 hx) (hb.2 hx)
  rw [col, ite_eq_right (not_internal hb), dite_eq_left hex, hsame]

/-- The `χ'`-coloured painting with the same painting and the new labels. -/
noncomputable def map (m : LabelMap χ χ') (P : ColouredPainting χ) : ColouredPainting χ' where
  Γ := P.Γ
  φ := m.col P
  fits := by
    rw [m.hΦ]
    exact P.fits
  internal_2_mem e he hi h2 := by
    rw [m.col_two P hi h2]
    exact m.map_2 _ (P.internal_2_mem e he hi h2)
  internal_3_mem e he hi h3 := by
    rw [m.col_three P hi h3]
    exact m.map_3 _ (P.internal_3_mem e he hi h3)
  border_mem e he s hs hb := by
    rw [m.hΦ] at hs
    rw [m.col_border P he hs hb]
    exact m.map_S s hs _ (P.border_mem e he s hs hb)

theorem isInternal_of_linear {Γ Γ' : Painting S} {σv : S → Set S} {σe : Set S → Set S}
    (h : IsLinearInflation Γ Γ' σv σe) {e : Set S} (he : e ∈ Γ.E) (hi : Painting.IsInternal e) :
    Painting.IsInternal (σe e) := by
  rw [Painting.IsInternal, disjoint_left]
  intro x hx hb
  obtain ⟨Θ, hΘ, hxΘ⟩ : ∃ Θ ∈ cuffs S, x ∈ Θ := ⟨_, ⟨x, hb, rfl⟩, mem_connectedComponentIn hb⟩
  obtain ⟨y, hy, hyΘ⟩ := (h.borders_iff e he Θ hΘ).2 ⟨x, hx, hxΘ⟩
  obtain ⟨z, hz, rfl⟩ := hΘ
  exact disjoint_left.mp hi hy (connectedComponentIn_subset _ _ hyΘ)

/-- A linear inflation of the relabelled paintings is a linear inflation of the old ones. -/
theorem of_map (m : LabelMap χ χ') {P P' : ColouredPainting χ} {σv : S → Set S}
    {σe : Set S → Set S} (h : IsColouredLinearInflation χ' (m.map P) (m.map P') σv σe) :
    IsColouredLinearInflation χ P P' σv σe := by
  have hinf : IsInflation P.Γ P'.Γ σv σe := h.isInflation
  have hlin : IsLinearInflation P.Γ P'.Γ σv σe := h.isLinear
  have hresp : RespectsFrame χ.Φ P.Γ σe := by
    have := h.respects
    rwa [m.hΦ] at this
  refine ⟨⟨hinf, hresp, ?_, ?_, ?_⟩, hlin⟩
  · intro e he hi h2
    have hi' := isInternal_of_linear hlin he hi
    have h2' : (tilde (σe e)).ncard = 2 := (hinf.edge_size e he).trans h2
    have hm' := hinf.edge_mem e he
    have hle : χ'.Ω2.le (m.col P e) (m.col P' (σe e)) := h.le_internal_2 e he hi h2
    rw [m.col_two P hi h2, m.col_two P' hi' h2'] at hle
    exact m.le_2 _ (P.internal_2_mem e he hi h2) _ (P'.internal_2_mem _ hm' hi' h2') hle
  · intro e he hi h3
    have hi' := isInternal_of_linear hlin he hi
    have h3' : (tilde (σe e)).ncard = 3 := (hinf.edge_size e he).trans h3
    have hm' := hinf.edge_mem e he
    have hle : χ'.Ω3.le (m.col P e) (m.col P' (σe e)) := h.le_internal_3 e he hi h3
    rw [m.col_three P hi h3, m.col_three P' hi' h3'] at hle
    exact m.le_3 _ (P.internal_3_mem e he hi h3) _ (P'.internal_3_mem _ hm' hi' h3') hle
  · intro e he s hs hb
    have hm' := hinf.edge_mem e he
    obtain ⟨hb', hiff⟩ := hresp e he hb.1
    have hb₂ : BordersSide (σe e) s := ⟨hb', (hiff s hs).1 hb.2⟩
    have hle : (χ'.ΩS s).le (m.col P e) (m.col P' (σe e)) :=
      h.le_border e he s (by rw [m.hΦ]; exact hs) hb
    rw [m.col_border P he hs hb, m.col_border P' hm' hs hb₂] at hle
    exact m.le_S s hs _ (P.border_mem e he s hs hb) _ (P'.border_mem _ hm' s hs hb₂) hle

theorem isBadSequence (m : LabelMap χ χ') {P : ℕ → ColouredPainting χ} (h : IsBadSequence χ P) :
    IsBadSequence χ' fun i ↦ m.map (P i) :=
  fun i j hij ⟨σv, σe, hσ⟩ ↦ h i j hij ⟨σv, σe, m.of_map hσ⟩

theorem isBad (m : LabelMap χ χ') (h : χ.IsBad) : χ'.IsBad := by
  obtain ⟨P, hP⟩ := h
  exact ⟨_, m.isBadSequence hP⟩

theorem isOrientedlyBad (m : LabelMap χ χ') (h : χ.IsOrientedlyBad) : χ'.IsOrientedlyBad := by
  obtain ⟨P, hP, hsim⟩ := h
  exact ⟨_, m.isBadSequence hP, hsim⟩

end LabelMap

/-- The copy of `χ` over `Option α × ℕ`. -/
def ColourScheme.lift (χ : ColourScheme S α) : ColourScheme S (Option α × ℕ) where
  isSurface := χ.isSurface
  connected := χ.connected
  Φ := χ.Φ
  Ω2 := χ.Ω2.map (fun x ↦ (some x, 0)) fun _ _ h ↦ by simpa using h
  Ω3 := χ.Ω3.map (fun x ↦ (some x, 0)) fun _ _ h ↦ by simpa using h
  ΩS s := (χ.ΩS s).map (fun x ↦ (some x, 0)) fun _ _ h ↦ by simpa using h
  shortElem s := (some (χ.shortElem s), 0)
  isWQO_2 := QuasiOrder.map_isWQO _ χ.isWQO_2
  isWQO_3 := QuasiOrder.map_isWQO _ χ.isWQO_3
  isWQO_S s hs := QuasiOrder.map_isWQO _ (χ.isWQO_S s hs)
  short_singleton s hs := by
    change (fun x ↦ (some x, 0)) '' (χ.ΩS s).E = _
    rw [χ.short_singleton s hs, image_singleton]

/-- `χ` maps to its copy over `Option α × ℕ`. -/
def ColourScheme.liftMap (χ : ColourScheme S α) : LabelMap χ χ.lift where
  hΦ := rfl
  f2 x := (some x, 0)
  f3 x := (some x, 0)
  fS _ x := (some x, 0)
  map_2 _ hx := mem_image_of_mem _ hx
  map_3 _ hx := mem_image_of_mem _ hx
  map_S _ _ _ hx := mem_image_of_mem _ hx
  le_2 _ _ _ _ := by
    rintro ⟨a, b, h₁, h₂, h⟩
    simp only [Prod.mk.injEq, Option.some.injEq, and_true] at h₁ h₂
    rwa [h₁, h₂]
  le_3 _ _ _ _ := by
    rintro ⟨a, b, h₁, h₂, h⟩
    simp only [Prod.mk.injEq, Option.some.injEq, and_true] at h₁ h₂
    rwa [h₁, h₂]
  le_S _ _ _ _ _ _ := by
    rintro ⟨a, b, h₁, h₂, h⟩
    simp only [Prod.mk.injEq, Option.some.injEq, and_true] at h₁ h₂
    rwa [h₁, h₂]

section Disjoint

variable {β : Type w} (e : β × ℕ ≃ β)

/-- The copy of `β` with tag `n`. -/
def tagged (n : ℕ) (x : β) : β := e (x, n)

theorem tagged_injective (n : ℕ) : Injective (tagged e n) := fun _ _ h ↦ by
  simpa [tagged] using h

theorem tagged_ne {n m : ℕ} (hnm : n ≠ m) (x y : β) : tagged e n x ≠ tagged e m y := fun h ↦ by
  have := e.injective h
  simp only [Prod.mk.injEq] at this
  exact hnm this.2

/-- Undoes every `tagged e n`. -/
def untag (y : β) : β := (e.symm y).1

theorem untag_tagged (n : ℕ) (x : β) : untag e (tagged e n x) = x := by
  simp [untag, tagged]

theorem disjoint_map (Ω Ω' : QuasiOrder β) {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (Ω.map (tagged e n) (tagged_injective e n)).E
      (Ω'.map (tagged e m) (tagged_injective e m)).E := by
  rw [disjoint_left]
  rintro _ ⟨x, -, rfl⟩ ⟨y, -, h⟩
  exact tagged_ne e hnm x y h.symm

variable {S' : Type u} [TopologicalSpace S']

/-- The scheme `χ'` with its internal labels moved back by `tagged e 0`, `tagged e 1`, and with the
labels of each long side `R` moved back by `tagged e (t R)`. -/
noncomputable def ColourScheme.pull (χ' : ColourScheme S' β) (t : Set S' → ℕ) (L : Set S' → Prop) :
    ColourScheme S' β where
  isSurface := χ'.isSurface
  connected := χ'.connected
  Φ := χ'.Φ
  Ω2 := χ'.Ω2.comap (tagged e 0)
  Ω3 := χ'.Ω3.comap (tagged e 1)
  ΩS s := open Classical in if L s ∧ s ∈ χ'.Φ.longSides then (χ'.ΩS s).comap (tagged e
    (t s)) else χ'.ΩS s
  shortElem := χ'.shortElem
  isWQO_2 := QuasiOrder.comap_isWQO χ'.isWQO_2
  isWQO_3 := QuasiOrder.comap_isWQO χ'.isWQO_3
  isWQO_S s hs := by
    by_cases h : L s ∧ s ∈ χ'.Φ.longSides
    · simpa only [ite_eq_left h] using QuasiOrder.comap_isWQO (χ'.isWQO_S s hs)
    · simpa only [ite_eq_right h] using χ'.isWQO_S s hs
  short_singleton s hs := by
    have h : ¬ (L s ∧ s ∈ χ'.Φ.longSides) := fun h ↦ hs.2 h.2.2
    simpa only [ite_eq_right h] using χ'.short_singleton s hs

theorem tagged_untag {Ω : QuasiOrder β} {n : ℕ} {y : β}
    (hy : y ∈ (Ω.map (tagged e n) (tagged_injective e n)).E) : tagged e n (untag e y) = y := by
  obtain ⟨x, -, rfl⟩ := hy
  rw [untag_tagged]

/-- `χ'` maps to `χ'.pull` when its labels are tagged in the right way. -/
noncomputable def ColourScheme.pullMap (χ' : ColourScheme S' β) (t : Set S' → ℕ) (L : Set S' → Prop)
    (h2 : ∀ y ∈ χ'.Ω2.E, tagged e 0 (untag e y) = y)
    (h3 : ∀ y ∈ χ'.Ω3.E, tagged e 1 (untag e y) = y)
    (hS : ∀ s, L s → s ∈ χ'.Φ.longSides → ∀ y ∈ (χ'.ΩS s).E, tagged e (t s) (untag e y) = y) :
    open Classical in LabelMap χ' (χ'.pull e t L) where
  hΦ := rfl
  f2 := untag e
  f3 := untag e
  fS s := open Classical in if L s ∧ s ∈ χ'.Φ.longSides then untag e else id
  map_2 x hx := by
    change tagged e 0 (untag e x) ∈ χ'.Ω2.E
    rwa [h2 x hx]
  map_3 x hx := by
    change tagged e 1 (untag e x) ∈ χ'.Ω3.E
    rwa [h3 x hx]
  map_S s hs x hx := by
    by_cases h : L s ∧ s ∈ χ'.Φ.longSides
    · simp only [ColourScheme.pull, ite_eq_left h]
      change tagged e (t s) (untag e x) ∈ (χ'.ΩS s).E
      rwa [hS s h.1 h.2 x hx]
    · simp only [ColourScheme.pull, ite_eq_right h]
      exact hx
  le_2 x hx y hy hle := by
    change χ'.Ω2.le (tagged e 0 (untag e x)) (tagged e 0 (untag e y)) at hle
    rwa [h2 x hx, h2 y hy] at hle
  le_3 x hx y hy hle := by
    change χ'.Ω3.le (tagged e 1 (untag e x)) (tagged e 1 (untag e y)) at hle
    rwa [h3 x hx, h3 y hy] at hle
  le_S s hs x hx y hy hle := by
    by_cases h : L s ∧ s ∈ χ'.Φ.longSides
    · simp only [ColourScheme.pull, ite_eq_left h] at hle
      change (χ'.ΩS s).le (tagged e (t s) (untag e x)) (tagged e (t s) (untag e y)) at hle
      rwa [hS s h.1 h.2 x hx, hS s h.1 h.2 y hy] at hle
    · simp only [ColourScheme.pull, ite_eq_right h] at hle
      exact hle

variable {S₀ : Type u} [TopologicalSpace S₀]

/-- The copy of `χ` with tag `0` on `Ω(2)`, tag `1` on `Ω(3)`, and tag `2 + t s` on `Ω(s)`. When `t`
is
injective on the sides this copy is disjoint. -/
def ColourScheme.tag (χ : ColourScheme S₀ β) (t : Set S₀ → ℕ) : ColourScheme S₀ β where
  isSurface := χ.isSurface
  connected := χ.connected
  Φ := χ.Φ
  Ω2 := χ.Ω2.map (tagged e 0) (tagged_injective e 0)
  Ω3 := χ.Ω3.map (tagged e 1) (tagged_injective e 1)
  ΩS s := (χ.ΩS s).map (tagged e (2 + t s)) (tagged_injective e _)
  shortElem s := tagged e (2 + t s) (χ.shortElem s)
  isWQO_2 := QuasiOrder.map_isWQO _ χ.isWQO_2
  isWQO_3 := QuasiOrder.map_isWQO _ χ.isWQO_3
  isWQO_S s hs := QuasiOrder.map_isWQO _ (χ.isWQO_S s hs)
  short_singleton s hs := by
    change tagged e (2 + t s) '' (χ.ΩS s).E = _
    rw [χ.short_singleton s hs, image_singleton]

/-- `χ` maps to its tagged copy. -/
def ColourScheme.tagMap (χ : ColourScheme S₀ β) (t : Set S₀ → ℕ) : LabelMap χ (χ.tag e t) where
  hΦ := rfl
  f2 := tagged e 0
  f3 := tagged e 1
  fS s := tagged e (2 + t s)
  map_2 _ hx := mem_image_of_mem _ hx
  map_3 _ hx := mem_image_of_mem _ hx
  map_S _ _ _ hx := mem_image_of_mem _ hx
  le_2 _ _ _ _ := by
    rintro ⟨a, b, h₁, h₂, h⟩
    rwa [tagged_injective e 0 h₁, tagged_injective e 0 h₂]
  le_3 _ _ _ _ := by
    rintro ⟨a, b, h₁, h₂, h⟩
    rwa [tagged_injective e 1 h₁, tagged_injective e 1 h₂]
  le_S s _ _ _ _ _ := by
    rintro ⟨a, b, h₁, h₂, h⟩
    rwa [tagged_injective e (2 + t s) h₁, tagged_injective e (2 + t s) h₂]

theorem ColourScheme.tag_disjoint (χ : ColourScheme S₀ β) {t : Set S₀ → ℕ}
    (ht : InjOn t χ.Φ.sides) : (χ.tag e t).IsDisjoint where
  disj_2_3 := disjoint_map e _ _ (by omega)
  disj_2_S _ _ := disjoint_map e _ _ (by omega)
  disj_3_S _ _ := disjoint_map e _ _ (by omega)
  disj_S_S s₁ h₁ s₂ h₂ hne := disjoint_map e _ _ fun h ↦ hne (ht h₁ h₂ (by omega))

variable {Shat Shat₀ : Type u} [TopologicalSpace Shat] [TopologicalSpace Shat₀]

theorem ColourScheme.tag_S2 {χ : ColourScheme S₀ β} (t : Set S₀ → ℕ)
    {cap : IsCappedSurface S₀ Shat₀} (h : ConditionS2 χ cap) : ConditionS2 (χ.tag e t) cap := by
  classical
  rintro S' Shat' _ _ χ' hcap hhom h3 h2 hstrict hb
  have h3E : ∀ y ∈ χ'.Ω3.E, tagged e 1 (untag e y) = y := fun y hy ↦ tagged_untag e (h3.E_subset hy)
  have h2E : ∀ y ∈ χ'.Ω2.E, tagged e 0 (untag e y) = y := fun y hy ↦ tagged_untag e (h2.E_subset hy)
  refine h S' Shat' (χ'.pull e (fun _ ↦ 0) (fun _ ↦ False)) hcap hhom
    (QuasiOrder.comap_subIdeal (tagged_injective e 1) h3) (QuasiOrder.comap_subIdeal
      (tagged_injective e 0) h2) ?_
    ((χ'.pullMap e _ _ h2E h3E fun _ h ↦ h.elim).isOrientedlyBad hb)
  rcases hstrict with hs | hs
  · exact Or.inl ⟨QuasiOrder.comap_subIdeal (tagged_injective e 1) h3,
      QuasiOrder.comap_E_ne (tagged_injective e 1) h3 hs.2⟩
  · exact Or.inr ⟨QuasiOrder.comap_subIdeal (tagged_injective e 0) h2,
      QuasiOrder.comap_E_ne (tagged_injective e 0) h2 hs.2⟩

theorem ColourScheme.tag_S3 {χ : ColourScheme S₀ β} (t : Set S₀ → ℕ)
    {cap : IsCappedSurface S₀ Shat₀} (h : ConditionS3 χ cap) : ConditionS3 (χ.tag e t) cap := by
  classical
  rintro S' Shat' _ _ χ' hcap hhom h2 h3 hlt hb
  have h3E : ∀ y ∈ χ'.Ω3.E, tagged e 1 (untag e y) = y := fun y hy ↦ by
    rw [h3] at hy
    exact tagged_untag e hy
  have h2E : ∀ y ∈ χ'.Ω2.E, tagged e 0 (untag e y) = y := fun y hy ↦ by
    rw [h2] at hy
    exact tagged_untag e hy
  refine h S' Shat' (χ'.pull e (fun _ ↦ 0) (fun _ ↦ False)) hcap hhom ?_ ?_ hlt
    ((χ'.pullMap e _ _ h2E h3E fun _ h ↦ h.elim).isOrientedlyBad hb)
  · change χ'.Ω2.comap (tagged e 0) = _
    rw [h2]
    exact QuasiOrder.comap_map _ (tagged_injective e 0)
  · change χ'.Ω3.comap (tagged e 1) = _
    rw [h3]
    exact QuasiOrder.comap_map _ (tagged_injective e 1)

theorem ColourScheme.tag_S4 {χ : ColourScheme S₀ β} (t : Set S₀ → ℕ) (h : ConditionS4 χ) :
    ConditionS4 (χ.tag e t) := by
  classical
  rintro S' _ χ' ⟨hhom, h2, h3, f, hf, hsub, hstrict, hshort⟩ hb
  have h3E : ∀ y ∈ χ'.Ω3.E, tagged e 1 (untag e y) = y := fun y hy ↦ by
    rw [h3] at hy
    exact tagged_untag e hy
  have h2E : ∀ y ∈ χ'.Ω2.E, tagged e 0 (untag e y) = y := fun y hy ↦ by
    rw [h2] at hy
    exact tagged_untag e hy
  let t' : Set S' → ℕ := fun R ↦ 2 + t (f R)
  have hSE : ∀ R, True → R ∈ χ'.Φ.longSides → ∀ y ∈ (χ'.ΩS R).E, tagged e (t' R) (untag e y) = y :=
    fun R _ hR y hy ↦ tagged_untag e ((hsub R hR).E_subset hy)
  have hpull : ∀ R ∈ χ'.Φ.longSides, ((χ'.pull e t' fun _ ↦ True).ΩS R) =
      (χ'.ΩS R).comap (tagged e (t' R)) := fun R hR ↦ by
    simp only [ColourScheme.pull, true_and, ite_eq_left hR]
  refine h S' (χ'.pull e t' fun _ ↦ True) ⟨hhom, ?_, ?_, f, hf, ?_, ?_, ?_⟩
    ((χ'.pullMap e t' _ h2E h3E hSE).isOrientedlyBad hb)
  · change χ'.Ω2.comap (tagged e 0) = _
    rw [h2]
    exact QuasiOrder.comap_map _ (tagged_injective e 0)
  · change χ'.Ω3.comap (tagged e 1) = _
    rw [h3]
    exact QuasiOrder.comap_map _ (tagged_injective e 1)
  · intro R hR
    rw [hpull R hR]
    exact QuasiOrder.comap_subIdeal (tagged_injective e _) (hsub R hR)
  · intro R₁ h₁ R₂ h₂ hne hff
    rw [hpull R₁ h₁]
    exact ⟨QuasiOrder.comap_subIdeal (tagged_injective e _) (hsub R₁ h₁),
      QuasiOrder.comap_E_ne (tagged_injective e _) (hsub R₁ h₁) (hstrict R₁ h₁ R₂ h₂ hne hff).2⟩
  · intro hall
    refine hshort fun s hs ↦ ?_
    obtain ⟨R, hR, hfR, hE⟩ := hall s hs
    refine ⟨R, hR, hfR, ?_⟩
    rw [hpull R hR] at hE
    subst hfR
    by_contra hne
    exact QuasiOrder.comap_E_ne (tagged_injective e _) (hsub R hR) hne hE

/-- **Graph Minors XIX, Section 15**: "(by replacing the $\Omega_\chi(k)$'s and $\Omega_\chi(S)$'s
by isomorphic well-quasi-orders) we may choose $\chi$ to be disjoint". -/
theorem ColourScheme.exists_disjoint [Infinite β] (χ : ColourScheme S₀ β)
    (cap : IsCappedSurface S₀ Shat₀) (h2 : ConditionS2 χ cap) (h3 : ConditionS3 χ cap)
    (h4 : ConditionS4 χ) (hb : χ.IsOrientedlyBad) :
    ∃ χ' : ColourScheme S₀ β, χ'.IsDisjoint ∧ ConditionS2 χ' cap ∧ ConditionS3 χ' cap ∧
      ConditionS4 χ' ∧ χ'.IsOrientedlyBad := by
  obtain ⟨e⟩ : Nonempty (β × ℕ ≃ β) := by
    rw [← Cardinal.eq]
    simp [Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk β)]
  obtain ⟨t, ht⟩ := Set.countable_iff_exists_injOn.mp χ.Φ.finite_sides.countable
  exact ⟨χ.tag e t, χ.tag_disjoint e ht, ColourScheme.tag_S2 e t h2, ColourScheme.tag_S3 e t h3,
    ColourScheme.tag_S4 e t h4, (χ.tagMap e t).isOrientedlyBad hb⟩

end Disjoint

end GraphMinor.GM19
