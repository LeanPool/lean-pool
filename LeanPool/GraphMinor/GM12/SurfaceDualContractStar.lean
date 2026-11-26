/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualContractBase

/-!
# The star of `v` and the edges of `Γ`

Facts for `exists_contracted_dual`, in the notation of `IsDualLines`, with `v` the vertex of `K` in
the
region `r` of `Γ`, and `f` a collapse of the star of `v` in `K`. The star meets `V(Γ)` in the
vertices
of `Γ` on `rBar` (`star_vertex`, `mem_star_of_closure`). An edge of `Γ` is in `rBar - r` exactly
when one of
its two hubs is `v` (`hub_eq_subset`, `exists_hub_eq`). A half `hal e b` of an edge with its end off
`rBar` misses the region `r₂` of `Γ₁ \ v` that holds `v` (`hal_off`).
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [T2Space S] [ConnectedSpace S] in
/-- A line is the range of an injective map from the unit interval. -/
theorem exists_inj_param {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) :
    ∃ p : I → S, Continuous p ∧ Function.Injective p ∧ p 0 = a ∧ p 1 = b ∧ range p = L := by
  obtain ⟨φ, h₀, h₁⟩ := hL
  have hinj : Function.Injective fun t : I => (φ t).1 :=
    fun t t' h' => φ.injective (Subtype.ext h')
  refine ⟨fun t => (φ t).1, by fun_prop, hinj, h₀, h₁, ?_⟩
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact (φ t).2
  · intro hz
    obtain ⟨t, ht⟩ := φ.surjective ⟨z, hz⟩
    exact ⟨t, congrArg Subtype.val ht⟩

omit [T2Space S] [ConnectedSpace S] in
theorem radialStar_subset {K : Drawing S} {v : S} (hv : v ∈ K.V) : radialStar K v ⊆ K.U := by
  rintro z (hz | hz)
  · exact (mem_singleton_iff.mp hz) ▸ K.V_subset_U hv
  · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp hz
    exact K.closure_subset_U hg.1 hzg

namespace IsDualLines

variable {Γ K D₀ Γ₁ : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ) K}
  {A B : Set S → Set S} {m x y : Set S → S} {φ : Set S × Bool → Set S} {h : Set S × Bool → S}
  {ℓ : Set S × Bool → I → S} (hL : IsDualLines hrad D₀ A B m x y φ h ℓ)
  (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing Γ) K) (hE : Γ.E.Nonempty)
  {r : Set S} (hr : r ∈ Γ.R) {v : S} (hvr : v ∈ r) (hvK : v ∈ K.V)

include hL hr hvr hvK

omit [T2Space S] [ConnectedSpace S] hvK in
theorem hub_eq_subset {e : Set S} (he : e ∈ Γ.E) {b : Bool} (hb : h (e, b) = v) :
    e ⊆ closure r \ r := by
  obtain ⟨r', hr', hfr, hhr, -⟩ := hL.hub e he b
  obtain rfl : r' = r := region_eq_of_mem hr' hr hhr (hb ▸ hvr)
  exact fun z hz => ⟨closure_mono hfr ((hL.face e he b).2 hz),
    fun h' => region_subset hr' h' (Γ.closure_subset_U he (subset_closure hz))⟩

include hS hmax hE

omit [ConnectedSpace S] hmax hE in
theorem exists_hub_eq {e : Set S} (he : e ∈ Γ.E) (hsub : e ⊆ closure r \ r) : ∃ b, h (e, b) = v
  := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨z, hz⟩ := he.1
  have heH : e ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he
  obtain ⟨W, A₁, A₂, hW, hzW, -, hcov, hc₁, hc₂, hd₁, hd₂, hcl₁, hcl₂⟩ :=
    exists_edge_sides hS (radialUnion hrad) heH hz
  obtain ⟨w, hwW, hwr⟩ := mem_closure_iff.mp (hsub hz).1 W hW hzW
  obtain ⟨y', ⟨hyW, hyr⟩, hyU⟩ := exists_notMem_U (Γ := radialUnion hrad) hS
    (hW.inter (region_isOpen hr)) ⟨w, hwW, hwr⟩
  have key : ∀ {A' : Set S}, IsPreconnected A' → Disjoint A' (radialUnion hrad).U →
      e ∩ W ⊆ closure A' → y' ∈ A' → ∃ b, h (e, b) = v := by
    intro A' hA hd hcl hy
    obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem hyU
    have hAp : A' ⊆ p := subset_region hp hA hd hy hyp
    have hzp : z ∈ closure p := closure_mono hAp (hcl ⟨hz, hzW⟩)
    have hep : e ⊆ closure p := edge_subset_closure_of_incident hS heH hp ⟨z, hz, hzp⟩
    obtain ⟨b, rfl⟩ := hL.face_all e he p hp hep
    obtain ⟨r', hr', hfr, hhr, hhV⟩ := hL.hub e he b
    obtain rfl : r' = r := region_eq_of_mem hr' hr (hfr hyp) hyr
    exact ⟨b, hub_unique hrad hr' hvr hvK hhr hhV⟩
  rcases hcov ⟨hyW, hyU⟩ with h₁ | h₁
  · exact key hc₁ hd₁ hcl₁ h₁
  · exact key hc₂ hd₂ hcl₂ h₁

include hrad in
omit [T2Space S] [ConnectedSpace S] hL hmax hE in
theorem star_vertex {z : S} (hz : z ∈ radialStar K v) (hzΓ : z ∈ Γ.V) : z ∈ closure r := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases hz with hz | hz
  · exact absurd (Γ.V_subset_U ((mem_singleton_iff.mp hz) ▸ hzΓ)) (region_subset hr hvr)
  obtain ⟨g, ⟨hg, hvg⟩, hzg⟩ := mem_iUnion₂.mp hz
  obtain ⟨u, hu, r', hr', w, hw, hwV, hcap, hgr⟩ := spoke_ends hrad hS hg
  have hv' : v ∈ closure g ∩ K.V := ⟨hvg, hvK⟩
  rw [hcap] at hv'
  have hvw : v = w := by
    rcases hv' with h' | h'
    · exact absurd (Γ.V_subset_U (h' ▸ hu)) (region_subset hr hvr)
    · exact h'
  obtain rfl : r' = r := region_eq_of_mem hr' hr hw (hvw ▸ hvr)
  exact closure_mono hgr hzg

include hrad in
omit hL in
theorem mem_star_of_closure {z : S} (hzΓ : z ∈ Γ.V) (hzr : z ∈ closure r) : z ∈ radialStar K v := by
  obtain ⟨g, hg, hcap⟩ := exists_spoke_at hrad hmax hS hE hr hvr hvK hzΓ hzr
  have hz' : z ∈ closure g ∩ K.V := by rw [hcap]; simp
  have hv' : v ∈ closure g ∩ K.V := by rw [hcap]; simp
  exact Or.inr (mem_biUnion (show g ∈ {e ∈ K.E | v ∈ closure e} from ⟨hg, hv'.1⟩) hz'.1)

end IsDualLines

/-- The half of `e` for `b`, and its end in `V(Γ)`. -/
def hal (A B : Set S → Set S) (e : Set S) (b : Bool) : Set S := cond b (A e) (B e)

/-- See `hal`. -/
def halEnd (x y : Set S → S) (e : Set S) (b : Bool) : S := cond b (x e) (y e)

namespace IsDualLines

variable {Γ K D₀ Γ₁ : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ) K}
  {A B : Set S → Set S} {m x y : Set S → S} {φ : Set S × Bool → Set S} {h : Set S × Bool → S}
  {ℓ : Set S × Bool → I → S} (hL : IsDualLines hrad D₀ A B m x y φ h ℓ)
  (h₁U : Γ₁.U = (K.V \ Γ.V) ∪ ⋃ e ∈ Γ.E, (range (ℓ (e, true)) ∪ range (ℓ (e, false))))

include hL

omit [T2Space S] [ConnectedSpace S] in
theorem hal_mem {e : Set S} (he : e ∈ Γ.E) (b : Bool) : hal A B e b ∈ D₀.E := by
  obtain ⟨hA, hB, -⟩ := hL.split e he
  cases b
  · exact hB
  · exact hA

omit [T2Space S] [ConnectedSpace S] in
theorem hal_end {e : Set S} (he : e ∈ Γ.E) (b : Bool) : halEnd x y e b ∈ Γ.V := by
  obtain ⟨-, -, -, -, -, -, -, hx, hy, -⟩ := hL.split e he
  cases b
  · exact hy
  · exact hx

omit [T2Space S] [ConnectedSpace S] in
theorem hal_subset {e : Set S} (he : e ∈ Γ.E) (b : Bool) : hal A B e b ⊆ e := by
  obtain ⟨-, -, -, -, -, -, hs, -⟩ := hL.split e he
  intro z hz
  rw [hs]
  cases b
  · exact Or.inr hz
  · exact Or.inl (Or.inl hz)

omit [T2Space S] [ConnectedSpace S] in
theorem m_notMem_hal {e : Set S} (he : e ∈ Γ.E) (b : Bool) : m e ∉ hal A B e b := by
  obtain ⟨-, -, -, hA, hB, -⟩ := hL.split e he
  cases b
  · exact hB
  · exact hA

omit [T2Space S] [ConnectedSpace S] in
theorem hal_cap {e : Set S} (he : e ∈ Γ.E) (b : Bool) :
    closure (hal A B e b) ∩ D₀.V = {m e, halEnd x y e b} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcA, hcB⟩ := hL.split e he
  cases b
  · exact hcB
  · rw [pair_comm]
    exact hcA

omit [T2Space S] [ConnectedSpace S] in
theorem hal_cover {e : Set S} (he : e ∈ Γ.E) {z : S} (hz : z ∈ e) (hzm : z ≠ m e) :
    ∃ b, z ∈ hal A B e b := by
  obtain ⟨-, -, -, -, -, -, hs, -⟩ := hL.split e he
  rw [hs] at hz
  rcases hz with (hz | hz) | hz
  · exact ⟨true, hz⟩
  · exact absurd hz hzm
  · exact ⟨false, hz⟩

omit [T2Space S] [ConnectedSpace S] in
theorem m_ne_end {e : Set S} (he : e ∈ Γ.E) (b : Bool) : m e ≠ halEnd x y e b := fun h' =>
  edge_notMem_V he (hL.m_mem he) (h' ▸ hL.hal_end he b)

omit [T2Space S] [ConnectedSpace S] in
theorem hal_line {e : Set S} (he : e ∈ Γ.E) (b : Bool) :
    IsLineWithEnds (closure (hal A B e b)) (m e) (halEnd x y e b) :=
  isLine_closure (hL.hal_mem he b) (hL.m_ne_end he b) (hL.hal_cap he b)

omit [T2Space S] [ConnectedSpace S] in
theorem m_mem_closure_hal {e : Set S} (he : e ∈ Γ.E) (b : Bool) : m e ∈ closure (hal A B e b) :=
  line_left_mem (hL.hal_line he b)

omit [T2Space S] [ConnectedSpace S] in
theorem end_mem_closure_hal {e : Set S} (he : e ∈ Γ.E) (b : Bool) :
    halEnd x y e b ∈ closure (hal A B e b) :=
  line_right_mem (hL.hal_line he b)

omit [T2Space S] [ConnectedSpace S] in
/-- A point of the closure of a half is in the half or is one of its two ends. -/
theorem mem_closure_hal {e : Set S} (he : e ∈ Γ.E) {b : Bool} {z : S}
    (hz : z ∈ closure (hal A B e b)) : z ∈ hal A B e b ∨ z = m e ∨ z = halEnd x y e b := by
  by_cases hzV : z ∈ D₀.V
  · have : z ∈ closure (hal A B e b) ∩ D₀.V := ⟨hz, hzV⟩
    rw [hL.hal_cap he b] at this
    exact Or.inr this
  · exact Or.inl (D₀.closure_diff_V (hL.hal_mem he b) ▸ ⟨hz, hzV⟩)

omit [T2Space S] [ConnectedSpace S] in
theorem hal_nonempty {e : Set S} (he : e ∈ Γ.E) (b : Bool) : (hal A B e b).Nonempty :=
  (hL.hal_mem he b).1

omit [T2Space S] [ConnectedSpace S] in
theorem hal_conn {e : Set S} (he : e ∈ Γ.E) (b : Bool) : IsPreconnected (hal A B e b) :=
  (hL.hal_mem he b).2.2.1.isConnected.isPreconnected

omit [T2Space S] [ConnectedSpace S] in
theorem hal_off_K {e : Set S} (he : e ∈ Γ.E) (b : Bool) {z : S} (hz : z ∈ hal A B e b) : z ∉ K.U :=
  disjoint_left.mp (edge_disjoint hrad he) (hL.hal_subset he b hz)

omit [T2Space S] [ConnectedSpace S] in
/-- A point of the closure of a half on `K` is its end in `V(Γ)`. -/
theorem closure_hal_K {e : Set S} (he : e ∈ Γ.E) {b : Bool} {z : S}
    (hz : z ∈ closure (hal A B e b)) (hzK : z ∈ K.U) : z = halEnd x y e b := by
  rcases hL.mem_closure_hal he hz with h' | h' | h'
  · exact absurd hzK (hL.hal_off_K he b h')
  · exact absurd (h' ▸ hzK) (hL.m_K he)
  · exact h'

include h₁U in
omit [T2Space S] [ConnectedSpace S] in
theorem hal_off_dual {e : Set S} (he : e ∈ Γ.E) (b : Bool) {z : S} (hz : z ∈ hal A B e b) :
    z ∉ Γ₁.U := fun h' =>
  hL.m_notMem_hal he b (hL.inter_dual h₁U he (hL.hal_subset he b hz) h' ▸ hz)

include h₁U in
omit [T2Space S] [ConnectedSpace S] in
/-- A half with its end lies in a region of `Γ₁`. -/
theorem hal_in_region {e : Set S} (he : e ∈ Γ.E) (b : Bool) {t : Set S} (ht : t ∈ Γ₁.R)
    (hend : halEnd x y e b ∈ t) : hal A B e b ⊆ t := by
  have hc : IsPreconnected (hal A B e b ∪ {halEnd x y e b}) :=
    (hL.hal_conn he b).subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.mpr (hL.end_mem_closure_hal he b)))
  have hd : Disjoint (hal A B e b ∪ {halEnd x y e b}) Γ₁.U := by
    refine disjoint_left.mpr ?_
    rintro z (hz | hz) hzU
    · exact hL.hal_off_dual h₁U he b hz hzU
    · exact region_subset ht ((mem_singleton_iff.mp hz) ▸ hend) hzU
  exact subset_union_left.trans (subset_region ht hc hd (Or.inr rfl) hend)

end IsDualLines

end GraphMinor.GM12
