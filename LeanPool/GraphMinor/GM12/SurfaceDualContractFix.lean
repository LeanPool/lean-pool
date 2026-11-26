/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualContractStar

/-!
# What the collapse moves

The setting of `exists_contracted_dual` is `IsContractSetting`. Write `G` for `Γ₁ \ v`. Points of
`G` are
fixed by `f` (`fix_U`), since `D` lies in a region of `G`. A vertex of `Γ` off `rBar` lies in a
region of
`Γ₁` with `v` off its closure (`vertex_region`), since otherwise `K` would have an edge from the
vertex
to `v`. That region is a region of `G` other than `r₂`. So an edge of `Γ` with no end in `rBar - r`
is fixed
pointwise (`fix_edge`).

An edge `e` of `Γ` is in `rBar - r` exactly when its dual is not in `G`, by `dual_mem` and
`exists_of_mem`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The hypotheses of `exists_contracted_dual`, with the lines of the dual written out. -/
structure IsContractSetting {Γ K D₀ : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ) K}
    {A B : Set S → Set S} {m x y : Set S → S} {φ : Set S × Bool → Set S} {h : Set S × Bool → S}
    {ℓ : Set S × Bool → I → S} (hL : IsDualLines hrad D₀ A B m x y φ h ℓ) (Γ₁ : Drawing S)
    (r : Set S) (v : S) (r₂ D : Set S) (f : C(S, S)) (H J : Drawing S) : Prop where
  hS : IsClosedSurface S
  hmax : RadMax (PaintingOrDrawing.drawing Γ) K
  hE : Γ.E.Nonempty
  hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K
  U₁ : Γ₁.U = (K.V \ Γ.V) ∪ ⋃ e ∈ Γ.E, (range (ℓ (e, true)) ∪ range (ℓ (e, false)))
  V₁ : Γ₁.V = K.V \ Γ.V
  E₁ : Γ₁.E = dualEdge h ℓ '' Γ.E
  hr : r ∈ Γ.R
  hvr : v ∈ r
  hvK : v ∈ K.V
  hr₂ : r₂ ∈ (deleteVertices Γ₁ {v}).R
  hvr₂ : v ∈ r₂
  hc : IsStarContraction K v r₂ D f H J
  hJ : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRadialDrawing J
  hE₂ : (deleteVertices Γ₁ {v}).E.Nonempty

namespace IsContractSetting

variable {Γ K D₀ Γ₁ H J : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ) K}
  {A B : Set S → Set S} {m x y : Set S → S} {φ : Set S × Bool → Set S} {h : Set S × Bool → S}
  {ℓ : Set S × Bool → I → S} {hL : IsDualLines hrad D₀ A B m x y φ h ℓ} {r r₂ D : Set S} {v : S}
  {f : C(S, S)} (C : IsContractSetting hL Γ₁ r v r₂ D f H J)

include C

omit [ConnectedSpace S] in
theorem hrad₂ : PreRad (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})) J := ⟨C.hJ.1, C.hJ.2.1⟩

omit [ConnectedSpace S] in
theorem hrad₁ : PreRad (PaintingOrDrawing.drawing Γ₁) K := ⟨C.hK₁.1, C.hK₁.2.1⟩

omit [ConnectedSpace S] in
theorem v_notMem : v ∉ Γ.V := fun h' => region_subset C.hr C.hvr (Γ.V_subset_U h')

omit [ConnectedSpace S] in
theorem v_mem₁ : v ∈ Γ₁.V := by
  rw [C.V₁]
  exact ⟨C.hvK, C.v_notMem⟩

omit [ConnectedSpace S] in
theorem fix_off {z : S} (hz : z ∉ D) : f z = z := C.hc.fix z fun h' => hz (discInt_subset D h')

omit [ConnectedSpace S] in
theorem fix_off_r₂ {z : S} (hz : z ∉ r₂) : f z = z := C.fix_off fun h' => hz (C.hc.sub h')

omit [ConnectedSpace S] in
theorem fix_U {z : S} (hz : z ∈ (deleteVertices Γ₁ {v}).U) : f z = z :=
  C.fix_off_r₂ fun h' => region_subset C.hr₂ h' hz

omit [ConnectedSpace S] in
theorem fibre {a b : S} (hab : f a = f b) : a = b ∨ a ∈ radialStar K v ∧ b ∈ radialStar K v :=
  (C.hc.fibre a b).1 hab

omit [ConnectedSpace S] C in
theorem U₂_sub : (deleteVertices Γ₁ {v}).U ⊆ Γ₁.U := (deleteVertices_isSubdrawing Γ₁ {v}).U_subset

omit [ConnectedSpace S] in
/-- A point off `Γ₁` and off `K` has its image off `G ∪ J`. -/
theorem image_off {z : S} (h₁ : z ∉ Γ₁.U) (hK : z ∉ K.U) : f z ∉ (radialUnion C.hrad₂).U := by
  have hstar : z ∉ radialStar K v := fun h' => hK (radialStar_subset C.hvK h')
  rw [radialUnion_U]
  rintro (h' | h')
  · rcases C.fibre (C.fix_U h') with h'' | h''
    · exact h₁ (U₂_sub (h'' ▸ h'))
    · exact hstar h''.2
  · have hH : f z ∈ H.U := C.hc.J_sub.U_subset h'
    rw [C.hc.H_U] at hH
    obtain ⟨k, hk, hkz⟩ := hH
    rcases C.fibre hkz with h'' | h''
    · exact hK (h'' ▸ hk)
    · exact hstar h''.2

omit [ConnectedSpace S] in
/-- A vertex of `K` on the star is `v` or a vertex of `Γ`. -/
theorem star_inter_V {z : S} (hz : z ∈ radialStar K v) (hzK : z ∈ K.V) : z = v ∨ z ∈ Γ.V := by
  rcases hz with hz | hz
  · exact Or.inl hz
  obtain ⟨g, ⟨hg, hvg⟩, hzg⟩ := mem_iUnion₂.mp hz
  obtain ⟨u, hu, -, -, w, -, -, hcap, -⟩ := spoke_ends hrad C.hS hg
  have hv' : v ∈ closure g ∩ K.V := ⟨hvg, C.hvK⟩
  have hz' : z ∈ closure g ∩ K.V := ⟨hzg, hzK⟩
  rw [hcap] at hv' hz'
  rcases hz' with h' | h'
  · exact Or.inr (h' ▸ hu)
  · rcases hv' with h'' | h''
    · exact absurd (h'' ▸ hu) C.v_notMem
    · exact Or.inl (h'.trans h''.symm)

omit [ConnectedSpace S] in
theorem vertex_off {w : S} (hw : w ∈ Γ.V) : w ∉ Γ₁.U := by
  intro h'
  have hwK : w ∈ K.V := radial_V hrad hw
  have : w ∈ Γ₁.V := by
    rw [← radial_inter C.hrad₁]
    exact ⟨h', K.V_subset_U hwK⟩
  rw [C.V₁] at this
  exact this.2 hw

omit [ConnectedSpace S] in
/-- Images of vertices of `Γ` are off `G`. -/
theorem end_off {u : S} (hu : u ∈ Γ.V) : f u ∉ (deleteVertices Γ₁ {v}).U := by
  intro h'
  rcases C.fibre (C.fix_U h') with h'' | ⟨h₁, -⟩
  · exact C.vertex_off hu (U₂_sub (h'' ▸ h'))
  · have hK : f u ∈ Γ₁.V := by
      rw [← radial_inter C.hrad₁]
      exact ⟨U₂_sub h', radialStar_subset C.hvK h₁⟩
    rw [C.V₁] at hK
    rcases C.star_inter_V h₁ hK.1 with h₃ | h₃
    · exact region_subset C.hr₂ C.hvr₂ (h₃ ▸ h')
    · exact hK.2 h₃

/-- See the module docstring. -/
theorem vertex_region {w : S} (hw : w ∈ Γ.V) (hwr : w ∉ closure r) {t : Set S} (ht : t ∈ Γ₁.R)
    (hwt : w ∈ t) : v ∉ closure t := by
  intro hv
  have hE₁ : Γ₁.E.Nonempty := C.hE₂.mono (deleteVertices_isSubdrawing Γ₁ {v}).2
  obtain ⟨g, hg, hcap⟩ := exists_spoke_at C.hrad₁ C.hK₁.2.2 C.hS hE₁ ht hwt (radial_V hrad hw)
    C.v_mem₁ hv
  have hv' : v ∈ closure g ∩ K.V := by rw [hcap]; simp
  have hw' : w ∈ closure g ∩ K.V := by rw [hcap]; simp
  have hstar : w ∈ radialStar K v :=
    Or.inr (mem_biUnion (show g ∈ {e ∈ K.E | v ∈ closure e} from ⟨hg, hv'.1⟩) hw'.1)
  exact hwr (IsDualLines.star_vertex (hrad := hrad) C.hS C.hr C.hvr C.hvK hstar hw)

/-- A region of `Γ₁` around a vertex of `Γ` off `rBar` is a region of `G`. -/
theorem region_mem {w : S} (hw : w ∈ Γ.V) (hwr : w ∉ closure r) {t : Set S} (ht : t ∈ Γ₁.R)
    (hwt : w ∈ t) : t ∈ (deleteVertices Γ₁ {v}).R :=
  region_mem_delete C.hS ht (C.vertex_region hw hwr ht hwt)

/-- A region of `Γ₁` around a vertex of `Γ` off `rBar` misses `r₂`. -/
theorem region_off {w : S} (hw : w ∈ Γ.V) (hwr : w ∉ closure r) {t : Set S} (ht : t ∈ Γ₁.R)
    (hwt : w ∈ t) {z : S} (hz : z ∈ t) : z ∉ r₂ := by
  intro h'
  obtain rfl := region_eq_of_mem (C.region_mem hw hwr ht hwt) C.hr₂ hz h'
  exact region_subset ht C.hvr₂ (Γ₁.V_subset_U C.v_mem₁)

theorem fix_vertex {w : S} (hw : w ∈ Γ.V) (hwr : w ∉ closure r) : f w = w := by
  obtain ⟨t, ht, hwt⟩ := exists_region_of_notMem (C.vertex_off hw)
  exact C.fix_off_r₂ (C.region_off hw hwr ht hwt hwt)

theorem fix_hal {e : Set S} (he : e ∈ Γ.E) {b : Bool} (hu : halEnd x y e b ∉ closure r) {z : S}
    (hz : z ∈ hal A B e b) : f z = z := by
  obtain ⟨t, ht, hwt⟩ := exists_region_of_notMem (C.vertex_off (hL.hal_end he b))
  exact C.fix_off_r₂ (C.region_off (hL.hal_end he b) hu ht hwt (hL.hal_in_region C.U₁ he b ht hwt
    hz))

omit [ConnectedSpace S] in
theorem dual_mem {e : Set S} (he : e ∈ Γ.E) (hn : ¬ e ⊆ closure r \ r) :
    dualEdge h ℓ e ∈ (deleteVertices Γ₁ {v}).E := by
  rw [deleteVertices_E]
  refine ⟨C.E₁ ▸ mem_image_of_mem _ he, disjoint_left.mpr ?_⟩
  rintro z ⟨hz, -⟩ hzv
  obtain rfl : z = v := hzv
  rw [hL.closure_dualEdge he] at hz
  have key : ∀ b, z ∈ range (ℓ (e, b)) → False := by
    intro b hb
    rcases hL.mem_line he b hb with h₁ | h₁ | h₁
    · exact (hL.face_off he b h₁).2 (K.V_subset_U C.hvK)
    · exact hL.m_K he (h₁ ▸ K.V_subset_U C.hvK)
    · exact hn (hL.hub_eq_subset C.hr C.hvr he h₁.symm)
  rcases hz with hz | hz
  · exact key true hz
  · exact key false hz

omit [ConnectedSpace S] in
theorem exists_of_mem {g : Set S} (hg : g ∈ (deleteVertices Γ₁ {v}).E) :
    ∃ e, e ∈ Γ.E ∧ ¬ e ⊆ closure r \ r ∧ g = dualEdge h ℓ e := by
  rw [deleteVertices_E] at hg
  obtain ⟨hg₁, hd⟩ := hg
  rw [C.E₁] at hg₁
  obtain ⟨e, he, rfl⟩ := hg₁
  refine ⟨e, he, fun hsub => ?_, rfl⟩
  obtain ⟨b, hb⟩ := hL.exists_hub_eq C.hS C.hr C.hvr C.hvK he hsub
  have hv : v ∈ closure (dualEdge h ℓ e) := by
    rw [hL.closure_dualEdge he, ← hb]
    cases b
    · exact Or.inr (hL.hub_mem_line he false)
    · exact Or.inl (hL.hub_mem_line he true)
  exact disjoint_left.mp hd ⟨hv, C.v_mem₁⟩ rfl

omit [ConnectedSpace S] in
/-- The dual of an edge in `rBar - r` is incident with `v`. -/
theorem mem_closure_dual {e : Set S} (he : e ∈ Γ.E) (hsub : e ⊆ closure r \ r) :
    v ∈ closure (dualEdge h ℓ e) := by
  obtain ⟨b, hb⟩ := hL.exists_hub_eq C.hS C.hr C.hvr C.hvK he hsub
  rw [hL.closure_dualEdge he, ← hb]
  cases b
  · exact Or.inr (hL.hub_mem_line he false)
  · exact Or.inl (hL.hub_mem_line he true)

/-- A region of `Γ₁` around a vertex of `Γ` on `rBar` has `v` in its closure, by the spoke of `K`
between
them. -/
theorem mem_closure_region {u : S} (hu : u ∈ Γ.V) (hur : u ∈ closure r) {t : Set S}
    (ht : t ∈ Γ₁.R) (hut : u ∈ t) : v ∈ closure t := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace C.hS
  obtain ⟨g, hg, hcap⟩ := exists_spoke_at hrad C.hmax C.hS C.hE C.hr C.hvr C.hvK hu hur
  have hu' : u ∈ closure g ∩ K.V := by rw [hcap]; simp
  have hv' : v ∈ closure g ∩ K.V := by rw [hcap]; simp
  obtain ⟨x, hxt, hxg⟩ := mem_closure_iff.mp hu'.1 t (region_isOpen ht) hut
  have hgt : g ⊆ t := subset_region ht hg.2.2.1.isConnected.isPreconnected
    (spoke_disjoint C.hrad₁ hg) hxg hxt
  exact closure_mono hgt hv'.1

omit [ConnectedSpace S] in
theorem dual_U {e : Set S} (he : e ∈ Γ.E) (hn : ¬ e ⊆ closure r \ r) :
    dualEdge h ℓ e ⊆ (deleteVertices Γ₁ {v}).U :=
  subset_closure.trans ((deleteVertices Γ₁ {v}).closure_subset_U (C.dual_mem he hn))

omit [ConnectedSpace S] in
theorem m_fix {e : Set S} (he : e ∈ Γ.E) (hn : ¬ e ⊆ closure r \ r) : f (m e) = m e :=
  C.fix_U (C.dual_U he hn (hL.m_mem_dualEdge he))

/-- A vertex of `Γ` on `rBar` is sent to `v`. -/
theorem collapse_vertex {u : S} (hu : u ∈ Γ.V) (hur : u ∈ closure r) : f u = v :=
  C.hc.collapse u (IsDualLines.mem_star_of_closure (hrad := hrad) C.hS C.hmax C.hE C.hr C.hvr C.hvK
    hu hur)

omit [ConnectedSpace S] in
/-- An end of an edge not in `rBar - r` lies off `rBar` when it is not in `rBar - r`. -/
theorem notMem_closure {u : S} (hu : u ∈ Γ.V) (hu' : u ∉ closure r \ r) : u ∉ closure r :=
  fun h' => hu' ⟨h', fun h'' => region_subset C.hr h'' (Γ.V_subset_U hu)⟩

omit [ConnectedSpace S] in
theorem not_sub_of_ends {e : Set S} (he : e ∈ Γ.E)
    (hd : Disjoint (closure e ∩ Γ.V) (closure r \ r)) : ¬ e ⊆ closure r \ r := by
  intro hsub
  have hmem := hL.end_mem_closure_hal he true
  have hu : halEnd x y e true ∈ closure e := closure_mono (hL.hal_subset he true) hmem
  have hV := hL.hal_end he true
  exact C.notMem_closure hV (disjoint_left.mp hd ⟨hu, hV⟩)
    (closure_minimal (hsub.trans sdiff_subset) isClosed_closure hu)

/-- See the module docstring. -/
theorem fix_edge {e : Set S} (he : e ∈ Γ.E) (hd : Disjoint (closure e ∩ Γ.V) (closure r \ r))
    {z : S} (hz : z ∈ e) : f z = z := by
  by_cases hzm : z = m e
  · exact hzm ▸ C.m_fix he (C.not_sub_of_ends he hd)
  obtain ⟨b, hb⟩ := hL.hal_cover he hz hzm
  have hV := hL.hal_end he b
  have hu : halEnd x y e b ∈ closure e := closure_mono (hL.hal_subset he b)
    (hL.end_mem_closure_hal he b)
  exact C.fix_hal he (C.notMem_closure hV (disjoint_left.mp hd ⟨hu, hV⟩)) hb

end IsContractSetting

end GraphMinor.GM12
