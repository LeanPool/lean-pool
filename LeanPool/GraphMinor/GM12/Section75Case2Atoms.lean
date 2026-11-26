/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section75
public import LeanPool.GraphMinor.GM12.SurfaceDualContractDefs

/-!
# Atoms in the end of Case 2 of XII (7.5)

Let `Γ₁` be dual to `Γ`, let `Γ₂ = Γ₁ \ r*`, and let `Γ₃` be dual to `Γ₂`. An atom of `Γ` is tied to
an
atom of `Γ₁`, and an atom of `Γ₂` to an atom of `Γ₃`, when they have the same corresponding atom in
the
common radial drawing (`SameAtom`). The metrics agree across such pairs (`dual_metric_eq`).

The rest of the file finds the atoms `a*` and `a**` for the atoms `a` of `Γ` that
`theorem_7_5_case_2_end`
uses, in `Section75Case2.lean`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The atoms `x` of `H` and `y` of `H'` have the same corresponding atom in the drawing `K`, which
is
radial for both. This is the paper's `y = x*`, for `H'` dual to `H`. -/
def SameAtom (H H' K : Drawing S) (x y : Set S) : Prop :=
  ∃ z, IsCorrespondingAtom H K x z ∧ IsCorrespondingAtom H' K y z

/-- Two atoms with the same corresponding atom are equal. -/
theorem correspondingAtom_inj (hS : IsClosedSurface S) {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) (hE : H.E.Nonempty) {x y z : Set S}
    (hx : IsCorrespondingAtom H K x z) (hy : IsCorrespondingAtom H K y z) : x = y := by
  have hrad : PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  have hnoV : ∀ {w : S}, w ∈ K.V → ({w} : Set S) ∉ K.R := fun hw hR =>
    region_subset hR (mem_singleton _) (K.V_subset_U hw)
  rcases hx with ⟨-, -, ⟨u, hu, rfl, rfl⟩ | ⟨hxE, hzR, hxz⟩ | ⟨hxR, w, ⟨hwK, hwx⟩, rfl⟩⟩ <;>
    rcases hy with ⟨-, -, ⟨u', hu', rfl, hz⟩ | ⟨hyE, hzR', hyz⟩ | ⟨hyR, w', ⟨hwK', hwy⟩, hz⟩⟩
  · exact hz
  · exact absurd hzR' (hnoV (radial_V hrad hu))
  · obtain rfl : u = w' := by simpa using hz
    exact absurd (H.V_subset_U hu) (region_subset hyR hwy)
  · exact absurd hzR (hz ▸ hnoV (radial_V hrad hu'))
  · exact (regionFacts_of_radial hrad hS hK.2.2 hE).2.1 z hzR x hxE y hyE hxz hyz
  · exact absurd hzR (hz ▸ hnoV hwK')
  · obtain rfl : w = u' := by simpa using hz
    exact absurd (H.V_subset_U hu') (region_subset hxR hwx)
  · exact absurd hzR' (hnoV hwK)
  · obtain rfl : w = w' := by simpa using hz
    exact region_eq_of_mem hxR hyR hwx hwy

namespace SameAtom

variable {H H' K : Drawing S} {a a' b b' : Set S}

omit [ConnectedSpace S] in
omit [T2Space S] in
/-- The form in which `exists_dual_tangleMetric_of_common_radial` asks for a dual pair. -/
theorem forall_iff (hS : IsClosedSurface S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hK' : (PaintingOrDrawing.drawing H').IsRadialDrawing K) (h : SameAtom H H' K a a')
      (z : Set S) :
    IsCorrespondingAtom H K a z ↔ IsCorrespondingAtom H' K a' z := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨w, hw, hw'⟩ := h
  constructor
  · intro hz
    rwa [(existsUnique_correspondingAtom hK hw.1).unique hz hw]
  · intro hz
    rwa [(existsUnique_correspondingAtom hK' hw'.1).unique hz hw']

/-- Duals of equal atoms are equal, and conversely. -/
theorem eq_iff (hS : IsClosedSurface S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hK' : (PaintingOrDrawing.drawing H').IsRadialDrawing K)
    (hE : H.E.Nonempty) (hE' : H'.E.Nonempty)
    (ha : SameAtom H H' K a a') (hb : SameAtom H H' K b b') : a = b ↔ a' = b' := by
  obtain ⟨z, hz, hz'⟩ := id ha
  obtain ⟨w, hw, hw'⟩ := id hb
  constructor
  · rintro rfl
    exact correspondingAtom_inj hS hK' hE' hz' ((hb.forall_iff hS hK hK' z).mp hz)
  · rintro rfl
    exact correspondingAtom_inj hS hK hE hz ((hb.forall_iff hS hK hK' z).mpr hz')

end SameAtom

/-- `d₁(a*, b*) = d(a, b)`, for the form of the equation that
`exists_dual_tangleMetric_of_common_radial` gives. -/
theorem dual_metric_eq (hS : IsClosedSurface S) {H H' K : Drawing S} {δ δ' : Set S → Set S → ℕ}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hK' : (PaintingOrDrawing.drawing H').IsRadialDrawing K)
    (hE : H.E.Nonempty) (hE' : H'.E.Nonempty)
    (hδ : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ a_star ∈ H'.A, ∀ b_star ∈ H'.A,
      (a = b ↔ a_star = b_star) →
      (∀ x' : Set S, IsCorrespondingAtom H K a x' ↔ IsCorrespondingAtom H' K a_star x') →
      (∀ y' : Set S, IsCorrespondingAtom H K b y' ↔ IsCorrespondingAtom H' K b_star y') →
      δ' a_star b_star = δ a b)
    {a a' b b' : Set S} (ha : SameAtom H H' K a a') (hb : SameAtom H H' K b b') :
    δ' a' b' = δ a b := by
  obtain ⟨_, hz, hz'⟩ := id ha
  obtain ⟨_, hw, hw'⟩ := id hb
  exact hδ a hz.1 b hw.1 a' hz'.1 b' hw'.1 (ha.eq_iff hS hK hK' hE hE' hb)
    (ha.forall_iff hS hK hK') (hb.forall_iff hS hK hK')

section Corr

variable {H K : Drawing S}

omit [T2Space S] [ConnectedSpace S] in
theorem corr_vertex (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {u : S} (hu : u ∈ H.V) :
    IsCorrespondingAtom H K {u} {u} :=
  ⟨Or.inl (Or.inl ⟨u, hu, rfl⟩), Or.inl (Or.inl ⟨u, hK.2.1.2.1 hu, rfl⟩), Or.inl ⟨u, hu, rfl, rfl⟩⟩

omit [T2Space S] [ConnectedSpace S] in
theorem corr_region {t : Set S} (ht : t ∈ H.R) {u : S} (huK : u ∈ K.V) (hut : u ∈ t) :
    IsCorrespondingAtom H K t {u} :=
  ⟨Or.inr ht, Or.inl (Or.inl ⟨u, huK, rfl⟩), Or.inr (Or.inr ⟨ht, u, ⟨huK, hut⟩, rfl⟩)⟩

omit [T2Space S] [ConnectedSpace S] in
theorem corr_edge {e s : Set S} (he : e ∈ H.E) (hs : s ∈ K.R) (hes : e ⊆ s) :
    IsCorrespondingAtom H K e s :=
  ⟨Or.inl (Or.inr he), Or.inr hs, Or.inr (Or.inl ⟨he, hs, hes⟩)⟩

end Corr

section Vii

variable {Γ₃ Γ' : Drawing S} {v : S} {r' : Set S}

omit [ConnectedSpace S] in
/-- (vii) of Case 2 of (7.5): `U(Γ₃) ⊆ U(Γ') ∪ r'`. Since `theorem_7_5_apply_7_4` keeps only (i), we
get (vii) from `U(Γ₃ \ r₂*) ⊆ U(Γ') ∪ r'`. An edge of `Γ₃` at `r₂*` lies in `r'`, since `r₂* ∈ r'`
and
`Γ'` is a subdrawing of `Γ₃ \ r₂*`. -/
theorem U_subset_of_delete_U_subset (hr' : r' ∈ Γ'.R) (hSub : Γ'.IsSubdrawing
  (deleteVertices Γ₃ {v}))
    (hvV : v ∈ Γ₃.V) (hvr' : v ∈ r') (hU : (deleteVertices Γ₃ {v}).U ⊆ Γ'.U ∪ r') :
    Γ₃.U ⊆ Γ'.U ∪ r' := by
  intro x hx
  by_cases hxV : x ∈ Γ₃.V
  · by_cases hxv : x = v
    · exact Or.inr (hxv ▸ hvr')
    · exact hU ((deleteVertices Γ₃ {v}).V_subset_U (by rw [deleteVertices_V]; exact ⟨hxV, hxv⟩))
  · obtain ⟨e, he, hxe⟩ := Γ₃.exists_edge_of_mem hx hxV
    by_cases hd : Disjoint (closure e ∩ Γ₃.V) {v}
    · have he' : e ∈ (deleteVertices Γ₃ {v}).E := by rw [deleteVertices_E]; exact ⟨he, hd⟩
      exact hU (he'.2.1 hxe).1
    · rw [not_disjoint_iff] at hd
      obtain ⟨z, ⟨hze, -⟩, hz⟩ := hd
      obtain rfl : z = v := hz
      exact Or.inr (incident_edge_subset_region_of_vertex_mem hr' hSub he hvV rfl hze
        (singleton_subset_iff.mpr hvr') hxe)

omit [ConnectedSpace S] in
omit [T2Space S] in
/-- A region of `Γ'` other than `r'`, off `r'`, is a region of `Γ₃`, by (vii). -/
theorem region_of_disjoint (hSub : Γ'.IsSubdrawing Γ₃) (hU : Γ₃.U ⊆ Γ'.U ∪ r') {a : Set S}
    (ha : a ∈ Γ'.R) (har' : Disjoint a r') : a ∈ Γ₃.R := by
  have hoff : Disjoint a Γ₃.U := disjoint_left.mpr fun x hxa hxU => by
    rcases hU hxU with h | h
    · exact region_subset ha hxa h
    · exact disjoint_left.mp har' hxa h
  obtain ⟨x, hx⟩ := region_nonempty ha
  obtain ⟨t, ht, hxt⟩ := exists_region_of_notMem (disjoint_left.mp hoff hx)
  have hat : a ⊆ t := subset_region ht (region_isPreconnected ha) hoff hx hxt
  have hta : t ⊆ a := region_subset_region_of_inter_nonempty hSub ht ha ⟨x, hxt, hx⟩
  exact (Subset.antisymm hat hta) ▸ ht

end Vii

section Threads

variable {Γ Γ₁ K J Γ₃ : Drawing S} {f : C(S, S)} {r : Set S} {v : S}

omit [T2Space S] [ConnectedSpace S] in
/-- A region `t` of `Γ₁` around a vertex `u` of `Γ` is `{u}*`. -/
theorem sameAtom_vertex (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K) (hV₁ : Γ₁.V = K.V \ Γ.V) {u : S}
    (hu : u ∈ Γ.V) : ∃ t ∈ Γ₁.R, u ∈ t ∧ SameAtom Γ Γ₁ K {u} t := by
  have huK : u ∈ K.V := hK.2.1.2.1 hu
  have hoff : u ∉ Γ₁.U := fun h' => by
    have : u ∈ Γ₁.V := hK₁.2.1.1.subset ⟨h', K.V_subset_U huK⟩
    rw [hV₁] at this
    exact this.2 hu
  obtain ⟨t, ht, hut⟩ := exists_region_of_notMem hoff
  exact ⟨t, ht, hut, {u}, corr_vertex hK hu, corr_region ht huK hut⟩

omit [T2Space S] [ConnectedSpace S] in
/-- `{w}` is `c*`, for a region `c` of `Γ` and the vertex `w` of `K` in it. -/
theorem sameAtom_region (_hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K) {w : S} (hw : w ∈ Γ₁.V) {c : Set S}
    (hc : c ∈ Γ.R) (hwK : w ∈ K.V) (hwc : w ∈ c) : SameAtom Γ Γ₁ K c {w} :=
  ⟨{w}, corr_region hc hwK hwc, corr_vertex hK₁ hw⟩

variable (hc : IsContractedDual Γ Γ₁ K J f r v Γ₃)
  (hK₂ : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRadialDrawing J)

include hc hK₂

omit hK₂ in
omit [ConnectedSpace S] in
/-- For a vertex `u` of `Γ` off `rBar`, the atoms `{u}*` and `{u}**`: the second is `{u}` again. -/
theorem thread_vertex (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K) (hV₁ : Γ₁.V = K.V \ Γ.V) {u : S}
    (hu : u ∈ Γ.V) (hur : u ∉ closure r) :
    ∃ t ∈ Γ₁.R, t ∈ (deleteVertices Γ₁ {v}).R ∧ SameAtom Γ Γ₁ K {u} t ∧
      u ∈ Γ₃.V ∧ SameAtom (deleteVertices Γ₁ {v}) Γ₃ J t {u} := by
  obtain ⟨t, ht, hut, hs⟩ := sameAtom_vertex hK hK₁ hV₁ hu
  have ht₂ := hc.vertex_corr u ⟨hu, fun h' => hur h'.1⟩ t ht hut
  have hu₃ : u ∈ Γ₃.V := by
    rw [hc.V_eq]
    exact Or.inl ⟨hu, fun h' => hur h'.1⟩
  exact ⟨t, ht, ht₂, hs, hu₃, {u}, corr_region ht₂ (hc.radial.2.1.2.1 hu₃) hut,
    corr_vertex hc.radial hu₃⟩

omit hK₂ in
omit [ConnectedSpace S] in
/-- For an edge `e` of `Γ` not in `rBar - r`, the atoms `e*` and `e** = f '' e`. -/
theorem thread_edge {e : Set S} (he : e ∈ Γ.E) (hn : ¬ e ⊆ closure r \ r) :
    ∃ g ∈ Γ₁.E, g ∈ (deleteVertices Γ₁ {v}).E ∧ SameAtom Γ Γ₁ K e g ∧
      f '' e ∈ Γ₃.E ∧ SameAtom (deleteVertices Γ₁ {v}) Γ₃ J g (f '' e) := by
  obtain ⟨g, hg, ⟨s, hs, hes, hgs⟩, s', hs', hfe, hgs'⟩ := hc.edge_corr e he hn
  have hg₁ : g ∈ Γ₁.E := (deleteVertices_isSubdrawing Γ₁ {v}).2 hg
  have hfeE : f '' e ∈ Γ₃.E := by
    rw [hc.E_eq]
    exact ⟨e, ⟨he, hn⟩, rfl⟩
  exact ⟨g, hg₁, hg, ⟨s, corr_edge he hs hes, corr_edge hg₁ hs hgs⟩, hfeE,
    ⟨s', corr_edge hg hs' hgs', corr_edge hfeE hs' hfe⟩⟩

omit [ConnectedSpace S] in
/-- For a region `c ≠ r` of `Γ`, the atoms `c*` and `c**`: the first is the vertex `w` of `K` in
`c`,
and the second is the region of `Γ₃` around `w`. -/
theorem thread_region (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK₁' : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K) (hV₁ : Γ₁.V = K.V \ Γ.V)
      (hr : r ∈ Γ.R) (hvr : v ∈ r) {c : Set S} (hc' : c ∈ Γ.R)
    (hcr : c ≠ r) :
    ∃ w ∈ c, ({w} : Set S) ∈ Γ₁.A ∧ ({w} : Set S) ∈ (deleteVertices Γ₁ {v}).A ∧
      SameAtom Γ Γ₁ K c {w} ∧ ∃ t ∈ Γ₃.R, w ∈ t ∧ SameAtom (deleteVertices Γ₁ {v}) Γ₃ J {w} t := by
  obtain ⟨w, ⟨hwc, hwK⟩, -⟩ := hK.2.1.2.2.1 c hc'
  have hwΓ : w ∉ Γ.V := fun h' => region_subset hc' hwc (Γ.V_subset_U h')
  have hwv : w ≠ v := by
    rintro rfl
    exact hcr (region_eq_of_mem hc' hr hwc hvr)
  have hw₁ : w ∈ Γ₁.V := by
    rw [hV₁]
    exact ⟨hwK, hwΓ⟩
  have hw₂ : w ∈ (deleteVertices Γ₁ {v}).V := by
    rw [deleteVertices_V]
    exact ⟨hw₁, hwv⟩
  have hwJ : w ∈ J.V := hK₂.2.1.2.1 hw₂
  have hoff : w ∉ Γ₃.U := fun h' => by
    have : w ∈ Γ₃.V := hc.radial.2.1.1.subset ⟨h', J.V_subset_U hwJ⟩
    rw [hc.V_eq] at this
    rcases this with h | h
    · exact hwΓ h.1
    · exact hwv h
  obtain ⟨t, ht, hwt⟩ := exists_region_of_notMem hoff
  exact ⟨w, hwc, Or.inl (Or.inl ⟨w, hw₁, rfl⟩), Or.inl (Or.inl ⟨w, hw₂, rfl⟩), ⟨{w},
    corr_region hc' hwK hwc, corr_vertex hK₁' hw₁⟩, t, ht, hwt, ⟨{w}, corr_vertex hK₂ hw₂,
    corr_region ht hwJ hwt⟩⟩

end Threads

end GraphMinor.GM12
