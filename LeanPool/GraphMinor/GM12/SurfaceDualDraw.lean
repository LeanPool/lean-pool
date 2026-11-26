/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualFace

/-!
# The two drawings on the lines through the faces

From the lines of `IsDualLines` we build two drawings on the same set.
`IsDualLines.exists_lineDrawing`
has one edge for each line, and its vertices are the hubs and the points `m e`.
`IsDualLines.exists_dual`
has one edge for each edge `e` of `Γ`, made of the two lines at `m e`, and its vertices are the
hubs. This
edge is a loop when the two lines end at the same hub.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ K D : Drawing S}
  {hrad : PreRad (PaintingOrDrawing.drawing Γ) K} {A B : Set S → Set S} {m x y : Set S → S}
  {f : Set S × Bool → Set S} {h : Set S × Bool → S} {ℓ : Set S × Bool → I → S}

omit [ConnectedSpace S] in
omit [T2Space S] in
theorem line_left_mem {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : a ∈ L := by
  obtain ⟨f, h₀, -⟩ := h
  exact h₀ ▸ (f 0).2

omit [ConnectedSpace S] in
omit [T2Space S] in
theorem line_right_mem {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : b ∈ L := by
  obtain ⟨f, -, h₁⟩ := h
  exact h₁ ▸ (f 1).2

namespace IsDualLines

variable (hL : IsDualLines hrad D A B m x y f h ℓ)

include hL

omit [T2Space S] [ConnectedSpace S] in
theorem mem_line {e : Set S} (he : e ∈ Γ.E) (b : Bool) {z : S} (hz : z ∈ range (ℓ (e, b))) :
    z ∈ f (e, b) ∨ z = m e ∨ z = h (e, b) := by
  obtain ⟨t, rfl⟩ := hz
  by_cases h0 : t = 0
  · exact Or.inr (Or.inl (h0 ▸ hL.zero e he b))
  by_cases h1 : t = 1
  · exact Or.inr (Or.inr (h1 ▸ hL.one e he b))
  exact Or.inl (hL.inside e he b t h0 h1)

omit [ConnectedSpace S] in
theorem isLine {e : Set S} (he : e ∈ Γ.E) (b : Bool) :
    IsLineWithEnds (range (ℓ (e, b))) (m e) (h (e, b)) := by
  have := isLine_range (hL.cont e he b) (hL.inj e he b)
  rwa [hL.zero e he b, hL.one e he b] at this

omit [T2Space S] [ConnectedSpace S] in
theorem m_mem {e : Set S} (he : e ∈ Γ.E) : m e ∈ e := (hL.split e he).2.2.1

omit [T2Space S] [ConnectedSpace S] in
theorem m_U {e : Set S} (he : e ∈ Γ.E) : m e ∈ Γ.U :=
  Γ.closure_subset_U he (subset_closure (hL.m_mem he))

omit [T2Space S] [ConnectedSpace S] in
theorem m_K {e : Set S} (he : e ∈ Γ.E) : m e ∉ K.U :=
  disjoint_left.mp (edge_disjoint hrad he) (hL.m_mem he)

omit [T2Space S] [ConnectedSpace S] in
theorem face_off {e : Set S} (he : e ∈ Γ.E) (b : Bool) {z : S} (hz : z ∈ f (e, b)) :
    z ∉ Γ.U ∧ z ∉ K.U := by
  have := region_subset (hL.face e he b).1 hz
  exact ⟨fun h' => this (Or.inl h'), fun h' => this (Or.inr h')⟩

omit [T2Space S] [ConnectedSpace S] in
theorem m_inj {e e' : Set S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) (hm : m e = m e') : e = e' :=
  Γ.edge_eq_of_mem he he' (hL.m_mem he) (hm ▸ hL.m_mem he')

omit [T2Space S] [ConnectedSpace S] in
theorem hub_off {e : Set S} (he : e ∈ Γ.E) (b : Bool) : h (e, b) ∉ Γ.U := by
  obtain ⟨r, hr, -, hc, -⟩ := hL.hub e he b
  exact region_subset hr hc

omit [T2Space S] [ConnectedSpace S] in
theorem hub_V {e : Set S} (he : e ∈ Γ.E) (b : Bool) : h (e, b) ∈ K.V := by
  obtain ⟨r, hr, -, -, hc⟩ := hL.hub e he b
  exact hc

omit [T2Space S] [ConnectedSpace S] in
theorem hub_K {e : Set S} (he : e ∈ Γ.E) (b : Bool) : h (e, b) ∈ K.U :=
  K.V_subset_U (hL.hub_V he b)

omit [T2Space S] [ConnectedSpace S] in
theorem hub_ne_m {e e' : Set S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) (b : Bool) : h (e, b) ≠ m e' :=
  fun h' => hL.hub_off he b (h' ▸ hL.m_U he')

omit [T2Space S] [ConnectedSpace S] in
/-- Two different lines meet only at their ends. -/
theorem line_meet {e e' : Set S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) {b b' : Bool}
    (hne : (e, b) ≠ (e', b')) {z : S} (hz : z ∈ range (ℓ (e, b))) (hz' : z ∈ range (ℓ (e', b'))) :
    z = m e ∨ z = h (e, b) := by
  rcases hL.mem_line he b hz with h₁ | h₁ | h₁
  · exfalso
    rcases hL.mem_line he' b' hz' with h₂ | h₂ | h₂
    · have hff : f (e, b) = f (e', b') :=
        region_eq_of_mem (hL.face e he b).1 (hL.face e' he' b').1 h₁ h₂
      obtain rfl := hL.face_unique e he e' he' b b' hff
      have hbb : b ≠ b' := fun h' => hne (h' ▸ rfl)
      refine hL.face_ne e he ?_
      cases b <;> cases b'
      · exact (hbb rfl).elim
      · exact hff.symm
      · exact hff
      · exact (hbb rfl).elim
    · exact (hL.face_off he b h₁).1 (h₂ ▸ hL.m_U he')
    · exact (hL.face_off he b h₁).2 (h₂ ▸ hL.hub_K he' b')
  · exact Or.inl h₁
  · exact Or.inr h₁

/-- The vertices of the dual. -/
theorem exists_hub {c : S} (hc : c ∈ K.V) (hc' : c ∉ Γ.V) (hmax : RadMax
  (PaintingOrDrawing.drawing Γ) K)
    (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) : ∃ e ∈ Γ.E, ∃ b, h (e, b) = c := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨r, hr, hcr⟩ := hrad.2.2.2.2.1 c ⟨hc, hc'⟩
  obtain ⟨s, hs, hcs⟩ := hub_has_spoke hrad hS hmax hr hcr hc
  have hsH : s ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr hs
  obtain ⟨p, hp, hsp⟩ := exists_region_incident hS hsH
  obtain ⟨e, he, hep, -, -⟩ := face_edge hrad hS hmax hE hp
  obtain ⟨b, rfl⟩ := hL.face_all e he p hp hep
  obtain ⟨r', hr', hfr', hhr', hhV⟩ := hL.hub e he b
  obtain ⟨v, hv, r₀, hr₀, w, hw, hwV, hcap, hsr₀⟩ := spoke_ends hrad hS hs
  obtain ⟨q, hq⟩ := hs.1
  obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp (hsp hq) r₀ (region_isOpen hr₀) (hsr₀ hq)
  obtain rfl : r₀ = r' := region_eq_of_mem hr₀ hr' hz₁ (hfr' hz₂)
  have hcw : c = w := by
    have : c ∈ closure s ∩ K.V := ⟨hcs, hc⟩
    rw [hcap] at this
    rcases this with h' | h'
    · exact absurd (h' ▸ hv) hc'
    · exact h'
  exact ⟨e, he, b, (hub_unique hrad hr₀ hw hwV hhr' hhV).trans hcw.symm⟩

omit [ConnectedSpace S] in
/-- The drawing with one edge for each line. -/
theorem exists_lineDrawing (hfin : ((K.V \ Γ.V) ∪ m '' Γ.E).Finite) :
    ∃ N : Drawing S, N.U = ((K.V \ Γ.V) ∪ m '' Γ.E) ∪ ⋃ i ∈ Γ.E ×ˢ (univ : Set Bool), range (ℓ i) ∧
      N.V = (K.V \ Γ.V) ∪ m '' Γ.E ∧
      N.E = (fun i => range (ℓ i) \ {m i.1, h i}) '' (Γ.E ×ˢ (univ : Set Bool)) := by
  have hm : ∀ {e}, e ∈ Γ.E → m e ∈ (K.V \ Γ.V) ∪ m '' Γ.E := fun he => Or.inr ⟨_, he, rfl⟩
  have hh : ∀ {e}, e ∈ Γ.E → ∀ b, h (e, b) ∈ (K.V \ Γ.V) ∪ m '' Γ.E := fun he b =>
    Or.inl ⟨hL.hub_V he b, fun h' => hL.hub_off he b (Γ.V_subset_U h')⟩
  refine exists_drawing_of_finite_lines hfin (Γ.finite_edges.prod finite_univ) (fun i => range
    (ℓ i))
    (fun i => m i.1) h ?_ ?_ ?_ ?_
  · rintro ⟨e, b⟩ ⟨he, -⟩
    exact hL.isLine he b
  · rintro ⟨e, b⟩ ⟨he, -⟩ h'
    exact hL.hub_ne_m he he b h'.symm
  · rintro ⟨e, b⟩ ⟨he, -⟩
    apply subset_antisymm
    · rintro z ⟨hz, hzV⟩
      rcases hL.mem_line he b hz with h₁ | h₁ | h₁
      · exfalso
        rcases hzV with hzV | ⟨e', he', rfl⟩
        · exact (hL.face_off he b h₁).2 (K.V_subset_U hzV.1)
        · exact (hL.face_off he b h₁).1 (hL.m_U he')
      · exact Or.inl h₁
      · exact Or.inr h₁
    · rintro z (rfl | rfl)
      · exact ⟨(line_left_mem (hL.isLine he b)), hm he⟩
      · exact ⟨(line_right_mem (hL.isLine he b)), hh he b⟩
  · rintro ⟨e, b⟩ ⟨he, -⟩ ⟨e', b'⟩ ⟨he', -⟩ hne z ⟨hz, hz'⟩
    rcases hL.line_meet he he' hne hz hz' with rfl | rfl
    · exact hm he
    · exact hh he b

omit [ConnectedSpace S] in
/-- The dual. -/
theorem exists_dual (hfin : (K.V \ Γ.V).Finite) :
    ∃ Γ₁ : Drawing S, Γ₁.U = (K.V \ Γ.V) ∪ ⋃ e ∈ Γ.E, (range (ℓ (e, true)) ∪ range (ℓ (e, false))) ∧
      Γ₁.V = K.V \ Γ.V ∧
      Γ₁.E = (fun e => (range (ℓ (e, true)) ∪ range (ℓ (e, false))) \
        {h (e, true), h (e, false)}) '' Γ.E := by
  have hh : ∀ {e}, e ∈ Γ.E → ∀ b, h (e, b) ∈ K.V \ Γ.V := fun he b =>
    ⟨hL.hub_V he b, fun h' => hL.hub_off he b (Γ.V_subset_U h')⟩
  have hmn : ∀ {e}, e ∈ Γ.E → m e ∉ K.V \ Γ.V := fun he h' => hL.m_K he (K.V_subset_U h'.1)
  refine exists_drawing_of_curves hfin Γ.finite_edges
    (fun e => range (ℓ (e, true)) ∪ range (ℓ (e, false))) (fun e => h (e, true))
    (fun e => h (e, false)) ?_ ?_ ?_
  · intro e he
    have hT := hL.isLine he true
    have hF := hL.isLine he false
    have hne : ((e, true) : Set S × Bool) ≠ (e, false) := by simp
    by_cases heq : h (e, true) = h (e, false)
    · rw [heq] at hT ⊢
      have hF' := hF
      have hO : IsOArc (range (ℓ (e, true)) ∪ range (ℓ (e, false))) := by
        refine isOArc_union hT hF fun z hz => ?_
        rcases hL.line_meet he he hne hz.1 hz.2 with h₁ | h₁
        · exact Or.inl h₁
        · exact Or.inr (heq ▸ h₁)
      obtain ⟨D', h₁, h₂, h₃⟩ := exists_loop_drawing_E hO (a := h (e, false)) (Or.inr
        (line_right_mem hF))
      refine ⟨D', h₁, ?_, ?_⟩
      · rw [h₂, pair_eq_singleton]
      · rw [h₃, pair_eq_singleton]
    · have hcap : range (ℓ (e, true)) ∩ range (ℓ (e, false)) = {m e} := by
        apply subset_antisymm
        · rintro z ⟨h₁, h₂⟩
          rcases hL.line_meet he he hne h₁ h₂ with h₃ | h₃
          · exact h₃
          · exfalso
            rcases hL.mem_line he false h₂ with h₄ | h₄ | h₄
            · exact absurd (hL.hub_K he true) (h₃ ▸ (hL.face_off he false h₄).2)
            · exact hL.hub_ne_m he he true (h₃.symm.trans h₄)
            · exact heq (h₃.symm.trans h₄)
        · rintro z rfl
          exact ⟨(line_left_mem hT), (line_left_mem hF)⟩
      have hline := IsLineWithEnds.union hT hF hcap
      exact ⟨lineDrawing hline heq, rfl, rfl, lineDrawing_E hline heq⟩
  · intro e he
    apply subset_antisymm
    · rintro z ⟨hz | hz, hzV⟩
      · rcases hL.mem_line he true hz with h₁ | h₁ | h₁
        · exact absurd (K.V_subset_U hzV.1) (hL.face_off he true h₁).2
        · exact absurd (h₁ ▸ hzV) (hmn he)
        · exact Or.inl h₁
      · rcases hL.mem_line he false hz with h₁ | h₁ | h₁
        · exact absurd (K.V_subset_U hzV.1) (hL.face_off he false h₁).2
        · exact absurd (h₁ ▸ hzV) (hmn he)
        · exact Or.inr h₁
    · rintro z (rfl | rfl)
      · exact ⟨Or.inl (line_right_mem (hL.isLine he true)), hh he true⟩
      · exact ⟨Or.inr (line_right_mem (hL.isLine he false)), hh he false⟩
  · intro e he e' he' hne z ⟨hz, hz'⟩
    have key : ∀ {b b'}, z ∈ range (ℓ (e, b)) → z ∈ range (ℓ (e', b')) → z ∈ K.V \ Γ.V := by
      intro b b' h₁ h₂
      have hne' : ((e, b) : Set S × Bool) ≠ (e', b') := fun h' => hne (congrArg Prod.fst h')
      rcases hL.line_meet he he' hne' h₁ h₂ with rfl | rfl
      · exfalso
        rcases hL.mem_line he' b' h₂ with h₃ | h₃ | h₃
        · exact (hL.face_off he' b' h₃).1 (hL.m_U he)
        · exact hne (hL.m_inj he he' h₃)
        · exact hL.hub_ne_m he' he b' h₃.symm
      · exact hh he b
    rcases hz with hz | hz <;> rcases hz' with hz' | hz'
    · exact key hz hz'
    · exact key hz hz'
    · exact key hz hz'
    · exact key hz hz'

end IsDualLines

end GraphMinor.GM12
