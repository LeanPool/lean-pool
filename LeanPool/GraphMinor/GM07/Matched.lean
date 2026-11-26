/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section3

/-!
# Drawings that match under a map

For (7.5), page 241, we pass forests between `Σ` and the surface `Σ_e` cut along `ē`. We keep the
forests off the cut. Then `φ_e` is one to
one on them, so it carries walks, the curves tracing them, and homotopies from one surface to the
other. In `Σ_e` the forest has two more
vertices `a'` and `b'`, which are isolated.

`IsCarry` says that a map takes the part of a drawing on a set `P` of vertices to another drawing.
`IsMatched` says that a map is onto a drawing
apart from a set `B` of isolated vertices. A matching gives a carry in each direction.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface

universe u v

section Carry

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- `f` takes the part of `Γ` on `P` into `Γ'`. -/
structure IsCarry (Γ : Drawing X) (Γ' : Drawing Y) (f : X → Y) (P : Set X) : Prop where
  cont : ContinuousOn f Γ.U
  inj : InjOn f Γ.U
  mem : ∀ x ∈ P, x ∈ Γ.V ∧ f x ∈ Γ'.V
  step : ∀ e ∈ Γ.E, ∀ x y, closure e ∩ Γ.V = {x, y} → x ∈ P →
    y ∈ P ∧ f '' e ∈ Γ'.E ∧ closure (f '' e) ∩ Γ'.V = {f x, f y} ∧ f '' closure e ⊆ closure (f '' e)

theorem CurveTracesWalk.range_subset {Γ : Drawing X} {u v : X}
  (W : GraphWalk Γ.toGraph u v) :
    ∀ φ : Curve X, CurveTracesWalk Γ φ W → range φ ⊆ Γ.U := by
  induction W with
  | nil hv =>
    intro φ h
    cases h with
    | nil _ _ hconst =>
      rintro _ ⟨x, rfl⟩
      rw [hconst]
      exact Γ.V_subset_U hv
  | cons hlink rest ih =>
    intro φ h
    cases h with
    | cons _ φ₁ φ₂ _ _ hφ₂ hconcat =>
      obtain ⟨t₀, -, -, -, -, -, h1, h2⟩ := hconcat
      rintro _ ⟨x, rfl⟩
      rcases le_total x.1 t₀.1 with hx | hx
      · exact Γ.closure_subset_U hlink.1 (h1 x hx)
      · exact ih φ₂ hφ₂ (h2 x hx)

theorem IsCarry.walk {Γ : Drawing X} {Γ' : Drawing Y} {f : X → Y} {P : Set X}
  (h : IsCarry Γ Γ' f P) {u v : X}
    (W : GraphWalk Γ.toGraph u v) : u ∈ P → ∀ u' v', f u = u' → f v = v'
      → ∃ W' : GraphWalk Γ'.toGraph u' v',
      W'.support = W.support.map f ∧ W'.edges = W.edges.map (image f) ∧ (∀ x ∈ W.support, x ∈ P) ∧
        ∀ φ : Curve X, CurveTracesWalk Γ φ W → ∃ φ' : Curve Y, CurveTracesWalk Γ' φ' W' ∧ ∀ t, φ' t
          = f (φ t) := by
  induction W with
  | nil hv =>
    intro hu u' v' h1 h2
    subst h1
    subst h2
    refine ⟨.nil (h.mem _ hu).2, by simp [GraphWalk.support], by simp [GraphWalk.edges],
      by simpa [GraphWalk.support] using hu, fun φ hφ => ?_⟩
    cases hφ with
    | nil _ _ hconst =>
      refine ⟨ContinuousMap.const _ (f _), .nil _ _ fun _ => rfl, fun t => ?_⟩
      simp [hconst]
  | @cons a b c e hlink rest ih =>
    intro hu u' v' h1 h2
    subst h1
    subst h2
    obtain ⟨hb, he, hcap, hcl⟩ := h.step e hlink.1 _ _ hlink.2.2.2 hu
    obtain ⟨W', h1, h2, h3, h4⟩ := ih hb _ _ rfl rfl
    have hlink' : Γ'.toGraph.IsLink (f '' e) (f a) (f b) := ⟨he, (h.mem _ hu).2,
      (h.mem _ hb).2, hcap⟩
    refine ⟨.cons hlink' W', by simp [GraphWalk.support, h1], by simp [GraphWalk.edges, h2], ?_,
      fun φ hφ => ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hu
      · exact h3 x hx
    · have hr := CurveTracesWalk.range_subset _ φ hφ
      let φ' : Curve Y := ⟨fun t => f (φ t), h.cont.comp_continuous φ.continuous fun t
        => hr ⟨t, rfl⟩⟩
      refine ⟨φ', ?_, fun t => rfl⟩
      cases hφ with
      | cons _ φ₁ φ₂ _ hφ₁ hφ₂ hconcat =>
        obtain ⟨φ₂', hφ₂', hval⟩ := h4 φ₂ hφ₂
        have hr₁ : range φ₁ ⊆ Γ.U := hφ₁.2.2.trans (Γ.closure_subset_U hlink.1)
        let φ₁' : Curve Y := ⟨fun t => f (φ₁ t), h.cont.comp_continuous φ₁.continuous fun t
          => hr₁ ⟨t, rfl⟩⟩
        obtain ⟨t₀, h5, h6, h7, h8, h9, h10, h11⟩ := hconcat
        refine .cons hlink' φ₁' φ₂' φ' ⟨congrArg f hφ₁.1, congrArg f hφ₁.2.1, ?_⟩ hφ₂' ⟨t₀, h5,
          h6, congrArg f h7, congrArg f h8, congrArg f h9, ?_, ?_⟩
        · rintro _ ⟨t, rfl⟩
          exact hcl ⟨_, hφ₁.2.2 ⟨t, rfl⟩, rfl⟩
        · exact fun x hx => hcl ⟨_, h10 x hx, rfl⟩
        · intro x hx
          obtain ⟨y, hy⟩ := h11 x hx
          exact ⟨y, by rw [hval, hy]; rfl⟩

theorem GraphWalk.edges_mem_toGraph {Γ : Drawing X} {u v : X} (W : GraphWalk Γ.toGraph u v) : ∀ e ∈
  W.edges, e ∈ Γ.E := by
  induction W with
  | nil => simp [GraphWalk.edges]
  | cons hlink rest ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hlink.1
    · exact ih e he

/-- A carry that holds every edge of `Γ` takes forests back. -/
theorem IsCarry.isGraphForest {Γ : Drawing X} {Γ' : Drawing Y} {f : X → Y} {P : Set X}
  (h : IsCarry Γ Γ' f P)
    (hends : ∀ e ∈ Γ.E, ∀ x y, closure e ∩ Γ.V = {x, y} → x ∈ P) (hF : IsGraphForest Γ'.toGraph) :
      IsGraphForest Γ.toGraph := by
  intro u W hW
  cases W with
  | nil hv => rfl
  | @cons _ b _ e hlink rest =>
    have hu := hends e hlink.1 _ _ hlink.2.2.2
    obtain ⟨W', h1, h2, h3, -⟩ := h.walk (.cons hlink rest) hu _ _ rfl rfl
    have hsimple : W'.IsSimpleClosed := by
      constructor
      · rw [h1, ← List.map_tail]
        refine hW.1.map_on fun x hx y hy he => ?_
        exact h.inj (Γ.V_subset_U (h.mem _ (h3 x (List.mem_of_mem_tail hx))).1)
          (Γ.V_subset_U (h.mem _ (h3 y (List.mem_of_mem_tail hy))).1) he
      · rw [h2]
        refine hW.2.map_on fun x hx y hy he => ?_
        have hxE := GraphWalk.edges_mem_toGraph _ x hx
        have hyE := GraphWalk.edges_mem_toGraph _ y hy
        have hxU : x ⊆ Γ.U := subset_closure.trans (Γ.closure_subset_U hxE)
        have hyU : y ⊆ Γ.U := subset_closure.trans (Γ.closure_subset_U hyE)
        exact (h.inj.image_eq_image_iff hxU hyU).mp he
    have h0 := hF _ W' hsimple
    rw [GraphWalk.length, h2, List.length_map] at h0
    exact h0

end Carry

section Matched

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- `f` is one to one on `Γ` and takes it onto `Γ'`, apart from a set `B` of isolated vertices of
`Γ`. -/
structure IsMatched (Γ : Drawing X) (Γ' : Drawing Y) (f : X → Y) (B : Set X) : Prop where
  cont : Continuous f
  inj : InjOn f Γ.U
  sub : B ⊆ Γ.V
  off : ∀ e ∈ Γ.E, Disjoint (closure e) B
  image_U : f '' (Γ.U \ B) = Γ'.U
  image_V : f '' (Γ.V \ B) = Γ'.V
  image_E : Γ'.E = image f '' Γ.E

variable [CompactSpace X] [T2Space X] [T2Space Y] {Γ : Drawing X} {Γ' : Drawing Y} {f : X
  → Y} {B : Set X}

omit [T2Space X] in
theorem IsMatched.closure_image (h : IsMatched Γ Γ' f B) (e : Set X) : closure (f '' e)
  = f '' closure e :=
  (image_closure_subset_closure_image h.cont).antisymm' (closure_minimal (image_mono subset_closure)
    (isClosed_closure.isCompact.image h.cont).isClosed)

omit [T2Space X] in
theorem IsMatched.cap (h : IsMatched Γ Γ' f B) {e : Set X} (he : e ∈ Γ.E) : closure (f '' e) ∩ Γ'.V
  = f '' (closure e ∩ Γ.V) := by
  have hU := Γ.closure_subset_U he
  rw [h.closure_image]
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    rw [← h.image_V] at hz
    obtain ⟨w', hw', he'⟩ := hz
    rw [← h.inj (Γ.V_subset_U hw'.1) (hU hw) he']
    exact ⟨w', ⟨h.inj (Γ.V_subset_U hw'.1) (hU hw) he' ▸ hw, hw'.1⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwV⟩, rfl⟩
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rw [← h.image_V]
    exact ⟨w, ⟨hwV, disjoint_left.mp (h.off e he) hw⟩, rfl⟩

omit [T2Space X] in
theorem IsMatched.carry (h : IsMatched Γ Γ' f B) : IsCarry Γ Γ' f (Γ.V \ B) where
  cont := h.cont.continuousOn
  inj := h.inj
  mem x hx := ⟨hx.1, by rw [← h.image_V]; exact ⟨x, hx, rfl⟩⟩
  step e he x y hcap hx := by
    have hy : y ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    refine ⟨⟨hy.2, disjoint_left.mp (h.off e he) hy.1⟩, ?_, ?_, ?_⟩
    · rw [h.image_E]
      exact ⟨e, he, rfl⟩
    · rw [h.cap he, hcap, image_pair]
    · rw [h.closure_image]

omit [CompactSpace X] [T2Space X] [T2Space Y] in
theorem IsMatched.ends (h : IsMatched Γ Γ' f B) : ∀ e ∈ Γ.E, ∀ x y, closure e ∩ Γ.V = {x, y}
  → x ∈ Γ.V \ B := fun e he x y hcap => by
  have hx : x ∈ closure e ∩ Γ.V := by rw [hcap]; simp
  exact ⟨hx.2, disjoint_left.mp (h.off e he) hx.1⟩

omit [T2Space X] in
/-- The map back from `Γ'` to `Γ`. -/
theorem IsMatched.exists_inverse [Nonempty X] (h : IsMatched Γ Γ' f B) :
    ∃ ψ : Y → X, (∀ x ∈ Γ.U, ψ (f x) = x) ∧ (∀ y ∈ Γ'.U, f (ψ y) = y) ∧ IsCarry Γ' Γ ψ Γ'.V := by
  classical
  obtain ⟨ψ, hc, hl⟩ := Surface.exists_inv_of_compactOn Γ.isClosed_U.isCompact h.cont.continuousOn
    h.inj
  have hsub : Γ'.U ⊆ f '' Γ.U := by
    rw [← h.image_U]
    exact image_mono sdiff_subset
  have hfψ : ∀ y ∈ Γ'.U, f (ψ y) = y := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hsub hy
    rw [hl hx]
  have hVsub : ∀ y ∈ Γ'.V, ∃ x ∈ Γ.V \ B, f x = y := fun y hy => by
    rw [← h.image_V] at hy
    exact hy
  refine ⟨ψ, fun x hx => hl hx, hfψ, ?_⟩
  refine ⟨hc.mono hsub, fun y hy y' hy' he => by rw [← hfψ y hy, ← hfψ y' hy', he],
    fun y hy => ?_, fun e' he' x y hcap _ => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hVsub y hy
    exact ⟨hy, by rw [hl (Γ.V_subset_U hx.1)]; exact hx.1⟩
  · rw [h.image_E] at he'
    obtain ⟨e, he, rfl⟩ := he'
    have hU := Γ.closure_subset_U he
    have hee : ψ '' (f '' e) = e := by
      rw [image_image]
      exact (image_congr fun z hz => hl (hU (subset_closure hz))).trans (image_id' e)
    have hcl : ψ '' (f '' closure e) = closure e := by
      rw [image_image]
      exact (image_congr fun z hz => hl (hU hz)).trans (image_id' _)
    have hcapA : ψ '' (f '' (closure e ∩ Γ.V)) = closure e ∩ Γ.V := by
      rw [image_image]
      exact (image_congr fun z (hz : z ∈ closure e ∩ Γ.V) => hl (hU hz.1)).trans
        (image_id' _)
    have hy : y ∈ closure (f '' e) ∩ Γ'.V := by rw [hcap]; simp
    refine ⟨hy.2, by rw [hee]; exact he, ?_, ?_⟩
    · rw [hee, ← hcapA, ← h.cap he, hcap, image_pair]
    · rw [hee, h.closure_image, hcl]

omit [T2Space X] in
theorem IsMatched.isGraphForest_iff [Nonempty X] (h : IsMatched Γ Γ' f B) : IsGraphForest Γ.toGraph
  ↔ IsGraphForest Γ'.toGraph := by
  obtain ⟨ψ, -, -, hc⟩ :=
    h.exists_inverse
  refine ⟨hc.isGraphForest ?_, h.carry.isGraphForest h.ends⟩
  intro e he x y hcap
  have hx : x ∈ closure e ∩ Γ'.V := by rw [hcap]; simp
  exact hx.2

omit [CompactSpace X] [T2Space X] [T2Space Y] in
theorem IsMatched.map (h : IsMatched Γ Γ' f B) (α : X ≃ₜ X) (α₂ : Y ≃ₜ Y) (hcomm : ∀ x, f (α x)
  = α₂ (f x)) :
    IsMatched (mapDrawingHomeo α Γ) (mapDrawingHomeo α₂ Γ') f (α '' B) where
  cont := h.cont
  inj := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    rw [hcomm, hcomm] at he
    rw [h.inj hx hy (α₂.injective he)]
  sub := image_mono h.sub
  off e he := by
    rw [mapDrawingHomeo_E] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    rw [← α.image_closure]
    exact (disjoint_image_iff α.injective).mpr (h.off e₀ he₀)
  image_U := by
    change f '' (α '' Γ.U \ α '' B) = α₂ '' Γ'.U
    rw [← image_sdiff α.injective, ← h.image_U, image_image, image_image]
    exact image_congr fun x _ => hcomm x
  image_V := by
    change f '' (α '' Γ.V \ α '' B) = α₂ '' Γ'.V
    rw [← image_sdiff α.injective, ← h.image_V, image_image, image_image]
    exact image_congr fun x _ => hcomm x
  image_E := by
    rw [mapDrawingHomeo_E, mapDrawingHomeo_E, h.image_E, image_image, image_image]
    refine image_congr fun e _ => ?_
    rw [image_image, image_image]
    exact image_congr fun x _ => (hcomm x).symm

omit [T2Space X] in
/-- Homotopic forests stay homotopic under a matching. -/
theorem IsMatched.forestsHomotopic [Nonempty X] {Γ₁ Γ₂ : Drawing X} {Γ₁' Γ₂' : Drawing Y} {B₁ B₂ :
  Set X} (m₁ : IsMatched Γ₁ Γ₁' f B₁)
    (m₂ : IsMatched Γ₂ Γ₂' f B₂) (h : ForestsHomotopic Γ₁ Γ₂) (hp₁ : Γ₁'.IsProper)
      (hp₂ : Γ₂'.IsProper)
    (hV : Γ₁'.V ∩ bd Y = Γ₂'.V ∩ bd Y)
    (hlift : ∀ s ∈ Γ₁'.V ∩ bd Y, ∃ x, f x = s ∧ x ∈ Γ₁.V \ B₁ ∧ x ∈ bd X
      ∧ x ∈ Γ₂.V \ B₂) : ForestsHomotopic Γ₁' Γ₂' := by
  obtain ⟨-, -, f₁, f₂, -, hpaths⟩ := h
  obtain ⟨ψ₁, hl₁, hr₁, hc₁⟩ := m₁.exists_inverse
  obtain ⟨ψ₂, hl₂, hr₂, hc₂⟩ := m₂.exists_inverse
  refine ⟨hp₁, hp₂, m₁.isGraphForest_iff.mp f₁, m₂.isGraphForest_iff.mp f₂, hV,
    fun s hs t ht hne => ?_⟩
  obtain ⟨x, hxs, hx₁, hxb, hx₂⟩ := hlift s hs
  obtain ⟨y, hyt, hy₁, hyb, hy₂⟩ := hlift t ht
  subst hxs
  subst hyt
  have hxy : x ≠ y := fun he => hne (by rw [he])
  have hs₂ : f x ∈ Γ₂'.V := (hV ▸ hs : f x ∈ Γ₂'.V ∩ bd Y).1
  have ht₂ : f y ∈ Γ₂'.V := (hV ▸ ht : f y ∈ Γ₂'.V ∩ bd Y).1
  obtain ⟨hiff, hhom⟩ := hpaths x ⟨hx₁.1, hxb⟩ y ⟨hy₁.1, hyb⟩ hxy
  have hψ₁x := hl₁ x (Γ₁.V_subset_U hx₁.1)
  have hψ₁y := hl₁ y (Γ₁.V_subset_U hy₁.1)
  have hψ₂x := hl₂ x (Γ₂.V_subset_U hx₂.1)
  have hψ₂y := hl₂ y (Γ₂.V_subset_U hy₂.1)
  have hnodup : ∀ {Γ₀ : Drawing Y} {Γ₃ : Drawing X} {g : Y → X} {P : Set Y}, IsCarry Γ₀ Γ₃ g P
    → ∀ {l : List Y}, l.Nodup → (∀ z ∈ l, z ∈ P) →
      (l.map g).Nodup := fun {Γ₀ Γ₃ g P} hc l hn hl =>
    hn.map_on fun z hz w hw he => hc.inj (Γ₀.V_subset_U (hc.mem z (hl z hz)).1) (Γ₀.V_subset_U
      (hc.mem w (hl w hw)).1) he
  have hnodup' : ∀ {Γ₀ : Drawing X} {Γ₃ : Drawing Y} {g : X → Y} {P : Set X}, IsCarry Γ₀ Γ₃ g P
    → ∀ {l : List X}, l.Nodup → (∀ z ∈ l, z ∈ P) →
      (l.map g).Nodup := fun {Γ₀ Γ₃ g P} hc l hn hl =>
    hn.map_on fun z hz w hw he => hc.inj (Γ₀.V_subset_U (hc.mem z (hl z hz)).1) (Γ₀.V_subset_U
      (hc.mem w (hl w hw)).1) he
  refine ⟨⟨?_, ?_⟩, fun P₁ P₂ φ₁ φ₂ hs₁ hs₂' hφ₁ hφ₂ => ?_⟩
  · rintro ⟨P, hP⟩
    obtain ⟨Q, h1, -, h3, -⟩ := hc₁.walk P hs.1 x y hψ₁x hψ₁y
    obtain ⟨R, hR⟩ := hiff.mp ⟨Q, by rw [GraphWalk.IsSimple, h1]; exact hnodup hc₁ hP h3⟩
    obtain ⟨W, h4, -, h6, -⟩ := m₂.carry.walk R hx₂ _ _ rfl rfl
    exact ⟨W, by rw [GraphWalk.IsSimple, h4]; exact hnodup' m₂.carry hR h6⟩
  · rintro ⟨P, hP⟩
    obtain ⟨Q, h1, -, h3, -⟩ := hc₂.walk P hs₂ x y hψ₂x hψ₂y
    obtain ⟨R, hR⟩ := hiff.mpr ⟨Q, by rw [GraphWalk.IsSimple, h1]; exact hnodup hc₂ hP h3⟩
    obtain ⟨W, h4, -, h6, -⟩ := m₁.carry.walk R hx₁ _ _ rfl rfl
    exact ⟨W, by rw [GraphWalk.IsSimple, h4]; exact hnodup' m₁.carry hR h6⟩
  · obtain ⟨Q₁, h1, -, h3, h4⟩ := hc₁.walk P₁ hs.1 x y hψ₁x hψ₁y
    obtain ⟨Q₂, h1', -, h3', h4'⟩ := hc₂.walk P₂ hs₂ x y hψ₂x hψ₂y
    obtain ⟨c₁, hc₁t, hc₁v⟩ := h4 φ₁ hφ₁
    obtain ⟨c₂, hc₂t, hc₂v⟩ := h4' φ₂
      hφ₂
    have hQ₁ : Q₁.IsSimple := by
      rw [GraphWalk.IsSimple, h1]
      exact hnodup hc₁ hs₁ h3
    have hQ₂ : Q₂.IsSimple := by
      rw [GraphWalk.IsSimple, h1']
      exact hnodup hc₂ hs₂' h3'
    obtain ⟨H, -, h5, h6, h7, h8, h9, h10⟩ := hhom Q₁ Q₂ c₁ c₂ hQ₁ hQ₂ hc₁t hc₂t
    have hval₁ : ∀ t, f (c₁ t) = φ₁ t := fun t => by
      rw [hc₁v, hr₁ _ (CurveTracesWalk.range_subset _ φ₁ hφ₁ ⟨t, rfl⟩)]
    have hval₂ : ∀ t, f (c₂ t) = φ₂ t := fun t => by
      rw [hc₂v, hr₂ _ (CurveTracesWalk.range_subset _ φ₂ hφ₂ ⟨t, rfl⟩)]
    refine ⟨⟨fun p => f (H p), m₁.cont.comp H.continuous⟩, fun _ => mem_univ _, fun t => ?_,
      fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · change f (H (t, 0)) = _
      rw [h5, hval₁]
    · change f (H (t, 1)) = _
      rw [h6, hval₂]
    · change f (H (0, t)) = _
      rw [h7, hval₁]
    · change f (H (0, t)) = _
      rw [h8, hval₂]
    · change f (H (1, t)) = _
      rw [h9, hval₁]
    · change f (H (1, t)) = _
      rw [h10, hval₂]

end Matched

/-- `Γ` with some isolated vertices added. -/
@[expose] def addIsolated {S : Type u} [TopologicalSpace S] [T1Space S] (Γ : Drawing S) (B : Set S)
  (hf : B.Finite) (hB : Disjoint B Γ.U) : Drawing S where
  U := Γ.U ∪ B
  V := Γ.V ∪ B
  V_subset_U := union_subset_union_left _ Γ.V_subset_U
  isClosed_U := Γ.isClosed_U.union hf.isClosed
  finite_V := Γ.finite_V.union hf
  finite_edges := by
    have h : (Γ.U ∪ B) \ (Γ.V ∪ B) = Γ.U \ Γ.V := by
      ext x
      simp only [mem_sdiff, mem_union, not_or]
      constructor
      · rintro ⟨h1 | h1, h2, h3⟩
        · exact ⟨h1, h2⟩
        · exact absurd h1 h3
      · rintro ⟨h1, h2⟩
        exact ⟨.inl h1, h2, fun h3 => disjoint_left.mp hB h3 h1⟩
    rw [h]
    exact Γ.finite_edges
  edge_cond := by
    have h : (Γ.U ∪ B) \ (Γ.V ∪ B) = Γ.U \ Γ.V := by
      ext x
      simp only [mem_sdiff, mem_union, not_or]
      constructor
      · rintro ⟨h1 | h1, h2, h3⟩
        · exact ⟨h1, h2⟩
        · exact absurd h1 h3
      · rintro ⟨h1, h2⟩
        exact ⟨.inl h1, h2, fun h3 => disjoint_left.mp hB h3 h1⟩
    rw [h]
    intro e he
    have hcap : closure e ∩ (Γ.V ∪ B) = closure e ∩ Γ.V := by
      rw [inter_union_distrib_left, (disjoint_iff_inter_eq_empty.mp (hB.symm.mono_left
        (Γ.closure_subset_U he))), union_empty]
    rw [hcap]
    exact Γ.edge_cond e he


end GraphMinor.GM07
