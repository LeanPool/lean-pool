/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualContractLines

/-!
# The contracted dual in Case 2 of XII (7.5)

Let `Γ₁` be a line dual of `Γ` that shares the radial drawing `K`, and let `r*` be the vertex of `K`
in
the region `r` of `Γ`. Let `f` collapse the star of `r*` in `K`, as in
`exists_supported_radial_star_contraction`, and let `J` be the resulting radial drawing of `Γ₁ \
r*`.
The theorem `exists_contracted_dual` gives a drawing `Γ₃` for which `J` is also radial, with edges
the
images under `f` of the edges of `Γ` that are not in `rBar - r`. This fills in the sentence of the
text that
puts the vertex of `Γ₃` formed by contracting these edges at a point of `r`, with `Γ₃` less that
vertex
equal to `Γ \ Z`. That vertex is `r*`.

The lines of `exists_lines` give `Γ₃` by `IsDualLines.exists_dual`, and `J` is radial for it by
`IsDualLines.isRadial_dual`. The rest of the file works out the vertices and edges of `Γ₃`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

namespace IsContractSetting

variable {Γ K D₀ Γ₁ H J : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ) K}
  {A B : Set S → Set S} {m x y : Set S → S} {φ : Set S × Bool → Set S} {h : Set S × Bool → S}
  {ℓ : Set S × Bool → I → S} {hL : IsDualLines hrad D₀ A B m x y φ h ℓ} {r r₂ D : Set S} {v : S}
  {f : C(S, S)} (C : IsContractSetting hL Γ₁ r v r₂ D f H J)

include C

omit [ConnectedSpace S] in
/-- The image of `e` is the image of its closure, less the images of its ends. -/
theorem image_dual {e : Set S} (he : e ∈ Γ.E) :
    (f '' closure (hal A B e true) ∪ f '' closure (hal A B e false)) \
      {f (halEnd x y e true), f (halEnd x y e false)} = f '' e := by
  have hfwd : ∀ b, ∀ w ∈ closure (hal A B e b), f w ≠ f (halEnd x y e b) → f w ∈ f '' e := by
    intro b w hw hne
    rcases hL.mem_closure_hal he hw with h₁ | h₁ | h₁
    · exact ⟨w, hL.hal_subset he b h₁, rfl⟩
    · exact ⟨w, h₁ ▸ hL.m_mem he, rfl⟩
    · exact absurd (congrArg f h₁) hne
  apply subset_antisymm
  · rintro z ⟨⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩, hn⟩
    · exact hfwd true w hw fun h' => hn (Or.inl h')
    · exact hfwd false w hw fun h' => hn (Or.inr h')
  · rintro _ ⟨w, hw, rfl⟩
    have hwK : w ∉ K.U := disjoint_left.mp (edge_disjoint hrad he) hw
    have hne : ∀ b, f w ≠ f (halEnd x y e b) := by
      intro b h'
      rcases C.fibre h' with h₁ | h₁
      · exact edge_notMem_V he hw (h₁ ▸ hL.hal_end he b)
      · exact hwK (radialStar_subset C.hvK h₁.1)
    refine ⟨?_, ?_⟩
    · by_cases hwm : w = m e
      · exact Or.inl (mem_image_of_mem _ (hwm ▸ hL.m_mem_closure_hal he true))
      · obtain ⟨b, hb⟩ := hL.hal_cover he hw hwm
        cases b
        · exact Or.inr (mem_image_of_mem _ (subset_closure hb))
        · exact Or.inl (mem_image_of_mem _ (subset_closure hb))
    · rintro (h' | h')
      · exact hne true h'
      · exact hne false h'

theorem image_fixed {e : Set S} (he : e ∈ Γ.E) (hd : Disjoint (closure e ∩ Γ.V) (closure r \ r)) :
    f '' e = e := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [C.fix_edge he hd hw]
  · exact fun hz => ⟨z, hz, C.fix_edge he hd hz⟩

/-- The vertices of the contracted dual. -/
theorem vertices_eq : J.V \ (deleteVertices Γ₁ {v}).V = (Γ.V \ (closure r \ r)) ∪ {v} := by
  have hJV : J.V = f '' K.V := C.hc.J_V.trans C.hc.H_V
  have hvstar : v ∈ radialStar K v := Or.inl rfl
  ext z
  constructor
  · rintro ⟨hzJ, hzG⟩
    rw [hJV] at hzJ
    obtain ⟨k, hk, rfl⟩ := hzJ
    by_cases hstar : k ∈ radialStar K v
    · exact Or.inr (C.hc.collapse k hstar)
    by_cases hkΓ : k ∈ Γ.V
    · have hkr : k ∉ closure r := fun h' =>
        hstar (IsDualLines.mem_star_of_closure (hrad := hrad) C.hS C.hmax C.hE C.hr C.hvr C.hvK hkΓ
          h')
      rw [C.fix_vertex hkΓ hkr]
      exact Or.inl ⟨hkΓ, fun h' => hkr h'.1⟩
    · have hkG : k ∈ (deleteVertices Γ₁ {v}).V := by
        rw [deleteVertices_V, C.V₁]
        exact ⟨⟨hk, hkΓ⟩, fun h' => hstar ((mem_singleton_iff.mp h') ▸ hvstar)⟩
      exact absurd ((C.fix_U ((deleteVertices Γ₁ {v}).V_subset_U hkG)).symm ▸ hkG) hzG
  · rintro (⟨hz, hz'⟩ | hz)
    · refine ⟨?_, fun h' => C.vertex_off hz (U₂_sub ((deleteVertices Γ₁ {v}).V_subset_U h'))⟩
      rw [hJV]
      exact ⟨z, radial_V hrad hz, C.fix_vertex hz (C.notMem_closure hz hz')⟩
    · obtain rfl : z = v := hz
      refine ⟨?_, fun h' => ?_⟩
      · rw [hJV]
        exact ⟨z, C.hvK, C.hc.collapse z hvstar⟩
      · rw [deleteVertices_V] at h'
        exact h'.2 rfl

/-- See the module docstring. -/
theorem exists_contracted : ∃ Γ₃ : Drawing S, IsContractedDual Γ Γ₁ K J f r v Γ₃ := by
  obtain ⟨D₂, A₂, B₂, m₂, x₂, y₂, φ₂, h₂, ℓ₂, hL₂, hspec⟩ := C.exists_lines
  obtain ⟨Γ₃, h₃U, h₃V, h₃E⟩ := hL₂.exists_dual (J.finite_V.subset sdiff_subset)
  have hrad₃ := hL₂.isRadial_dual C.hS C.hJ.2.2 C.hE₂ h₃U h₃V h₃E
  have hV₃ : Γ₃.V = (Γ.V \ (closure r \ r)) ∪ {v} := h₃V.trans C.vertices_eq
  have key : ∀ e ∈ Γ.E, ¬ e ⊆ closure r \ r →
      (range (ℓ₂ (dualEdge h ℓ e, true)) ∪ range (ℓ₂ (dualEdge h ℓ e, false))) \
        {h₂ (dualEdge h ℓ e, true), h₂ (dualEdge h ℓ e, false)} = f '' e := by
    intro e he hn
    obtain ⟨-, hT, hhT⟩ := hspec e he hn true
    obtain ⟨-, hF, hhF⟩ := hspec e he hn false
    rw [hT, hF, hhT, hhF]
    exact C.image_dual he
  have hE₃ : Γ₃.E = (fun e => f '' e) '' {e ∈ Γ.E | ¬ e ⊆ closure r \ r} := by
    rw [h₃E]
    ext e'
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨e, he, hn, rfl⟩ := C.exists_of_mem hg
      exact ⟨e, ⟨he, hn⟩, (key e he hn).symm⟩
    · rintro ⟨e, ⟨he, hn⟩, rfl⟩
      exact ⟨_, C.dual_mem he hn, key e he hn⟩
  have hfix : ∀ e ∈ Γ.E, Disjoint (closure e ∩ Γ.V) (closure r \ r) → f '' e = e :=
    fun e he hd => C.image_fixed he hd
  have hvV₃ : v ∈ Γ₃.V := by
    rw [hV₃]
    exact Or.inr rfl
  have hdualK : ∀ e ∈ Γ.E, ∃ s ∈ K.R, e ⊆ s ∧ dualEdge h ℓ e ⊆ s := by
    intro e he
    obtain ⟨s, hs, hes, hs'⟩ := hL.exists_region C.hS C.hmax C.hE he
    refine ⟨s, hs, hes, fun z hz => ?_⟩
    rcases hL.mem_dualEdge he hz with ⟨b, hb⟩ | h₁
    · rw [hs']
      cases b
      · exact Or.inl (Or.inr hb)
      · exact Or.inl (Or.inl hb)
    · exact h₁ ▸ hes (hL.m_mem he)
  have hne₃ : Γ₃.E.Nonempty := by
    obtain ⟨g, hg⟩ := C.hE₂
    obtain ⟨e, he, hn, -⟩ := C.exists_of_mem hg
    rw [hE₃]
    exact ⟨_, e, ⟨he, hn⟩, rfl⟩
  refine ⟨Γ₃, hrad₃, hne₃, hV₃, ?_, hE₃, hfix, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Drawing.ext_of_V_E ?_ ?_
    · rw [deleteVertices_V, deleteVertices_V, hV₃]
      ext z
      constructor
      · rintro ⟨hz | hz, hzv⟩
        · exact ⟨hz.1, fun h' => hz.2 h'.2⟩
        · exact absurd hz hzv
      · rintro ⟨hz, hz'⟩
        exact ⟨Or.inl ⟨hz, fun h' => hz' ⟨hz, h'⟩⟩, fun h' => C.v_notMem (h' ▸ hz)⟩
    · rw [deleteVertices_E, deleteVertices_E]
      ext e'
      constructor
      · rintro ⟨he', hd⟩
        rw [hE₃] at he'
        obtain ⟨e, ⟨he, hn⟩, rfl⟩ := he'
        have hde : Disjoint (closure e ∩ Γ.V) (closure r \ r) := by
          refine disjoint_left.mpr ?_
          rintro u ⟨hu, huV⟩ huZ
          have hfu := C.collapse_vertex huV huZ.1
          have hvc : v ∈ closure (f '' e) :=
            hfu ▸ image_closure_subset_closure_image f.continuous ⟨u, hu, rfl⟩
          exact disjoint_left.mp hd ⟨hvc, hvV₃⟩ rfl
        change f '' e ∈ _
        rw [hfix e he hde]
        exact ⟨he, disjoint_left.mpr fun u h₁ h₂ => disjoint_left.mp hde h₁ h₂.2⟩
      · rintro ⟨he, hd⟩
        have hde : Disjoint (closure e' ∩ Γ.V) (closure r \ r) :=
          disjoint_left.mpr fun u h₁ h₂ => disjoint_left.mp hd h₁ ⟨h₁.2, h₂⟩
        refine ⟨?_, disjoint_left.mpr ?_⟩
        · rw [hE₃]
          exact ⟨e', ⟨he, C.not_sub_of_ends he hde⟩, hfix e' he hde⟩
        · rintro u ⟨hu, -⟩ huv
          obtain rfl : u = v := huv
          exact region_subset C.hr C.hvr (Γ.closure_subset_U he hu)
  · intro e he hn
    refine ⟨_, C.dual_mem he hn, hdualK e he, ?_⟩
    · obtain ⟨s, hs, hgs, hs'⟩ := hL₂.exists_region C.hS C.hJ.2.2 C.hE₂ (C.dual_mem he hn)
      refine ⟨s, hs, ?_, hgs⟩
      rintro _ ⟨z, hz, rfl⟩
      by_cases hzm : z = m e
      · rw [hzm, C.m_fix he hn]
        exact hgs (hL.m_mem_dualEdge he)
      · obtain ⟨b, hb⟩ := hL.hal_cover he hz hzm
        have hmem := (hspec e he hn b).1 ⟨z, hb, rfl⟩
        rw [hs']
        cases b
        · exact Or.inl (Or.inr hmem)
        · exact Or.inl (Or.inl hmem)
  · intro w hw t ht hwt
    exact C.region_mem hw.1 (C.notMem_closure hw.1 hw.2) ht hwt
  · exact fun e he hd => C.not_sub_of_ends he hd
  · exact fun u hu hur => C.collapse_vertex hu hur
  · intro e he hsub
    refine ⟨_, C.E₁ ▸ mem_image_of_mem _ he, C.mem_closure_dual he hsub, ?_⟩
    exact hdualK e he
  · exact fun u hu hur t ht hut => C.mem_closure_region hu hur ht hut

end IsContractSetting

/-- See the module docstring. The vertex `v` is `r*`, and `r₂` is the region of `Γ₁ \ v` around `v`.
The dual `Γ₁` must be a line dual, as `exists_lineDual_of_radial` gives: a dual that crosses an edge
of
`Γ` more than once could enter `r₂` through an edge that `f` must then move. -/
theorem exists_contracted_dual (hS : IsClosedSurface S) {Γ Γ₁ K : Drawing S} (hE : Γ.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K) (hdual : IsLineDual Γ K Γ₁)
    {r : Set S} (hr : r ∈ Γ.R) {v : S} (hvr : v ∈ r) (hvK : v ∈ K.V)
    {r₂ : Set S} (hr₂ : r₂ ∈ (deleteVertices Γ₁ {v}).R) (hvr₂ : v ∈ r₂)
    {D : Set S} {f : C(S, S)} {H J : Drawing S} (hc : IsStarContraction K v r₂ D f H J)
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRadialDrawing J)
    (hE₂ : (deleteVertices Γ₁ {v}).E.Nonempty) :
    ∃ Γ₃ : Drawing S, IsContractedDual Γ Γ₁ K J f r v Γ₃ := by
  obtain ⟨hrad, D₀, A, B, m, x, y, φ, h, ℓ, hL, h₁U, h₁V, h₁E⟩ := hdual
  exact IsContractSetting.exists_contracted (hL := hL) (Γ₁ := Γ₁)
    ⟨hS, hK.2.2, hE, hK₁, h₁U, h₁V, h₁E, hr, hvr, hvK, hr₂, hvr₂, hc, hJ, hE₂⟩

end GraphMinor.GM12
