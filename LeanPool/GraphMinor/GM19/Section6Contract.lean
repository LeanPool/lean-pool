/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Null
public import LeanPool.GraphMinor.GM19.Section6a
public import LeanPool.GraphMinor.GM11.Forest
public import LeanPool.GraphMinor.GM19.RadialExists

/-!
# Contracting one edge of a drawing

The proof of Graph Minors XIX, (6.3) (page 340) identifies the points of a tree of a drawing, and
uses that the surface does not change. We do this one edge at a time. By `exists_collapse`, an edge
`f` that is a line can be collapsed by a map `φ` homotopic to the identity. The images of the other
edges and of the vertices form a new drawing (`exists_contract`), and `rep` does not grow. If an
`O`-arc `F` of the old drawing misses an end of `f` then `φ` is injective on `F`. Otherwise `F` is
the union of two arcs between the ends of `f`, and one of them is mapped to a non-null-homotopic
`O`-arc by `not_null_of_two_arcs`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

variable {S : Type} [TopologicalSpace S]

/-- Each edge of the drawing is a line with two different ends. -/
def LoopFree (D : Drawing S) : Prop :=
  ∀ e ∈ D.E, ∃ u v : S, u ≠ v ∧ tilde e = {u, v} ∧ IsLineWithEnds (closure e) u v

theorem image_mem_arcComponentsIn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {φ : X → Y}
    {g : Y → X} {A : Set X} (hφ : ContinuousOn φ A) (hg : ContinuousOn g (φ '' A))
    (hl : LeftInvOn g φ A) {e : Set X} (he : e ∈ arcComponentsIn A) :
    φ '' e ∈ arcComponentsIn (φ '' A) := by
  refine ⟨he.1.image _, image_mono he.2.1, he.2.2.1.image' (hφ.mono he.2.1),
    fun D hD hpc hsub => ?_⟩
  have hgD : g '' D ⊆ A := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hD hy
    rwa [hl hx]
  have hesub : e ⊆ g '' D := fun x hx => ⟨φ x, hsub ⟨x, hx, rfl⟩, hl (he.2.1 hx)⟩
  have h1 := he.2.2.2 (g '' D) hgD (hpc.image' (hg.mono hD)) hesub
  rw [← h1, image_image]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := hD hy
    exact ⟨φ x, hy, by change φ (g (φ x)) = φ x; rw [hl hx]⟩
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x, hx, rfl⟩ := hD hy'
    change φ (g (φ x)) ∈ D
    rw [hl hx]
    exact hy'

/-- Path components under a map with a continuous inverse. -/
theorem arcComponentsIn_image_eq {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {φ : X → Y}
    {g : Y → X} {A : Set X} (hφ : ContinuousOn φ A) (hg : ContinuousOn g (φ '' A))
    (hl : LeftInvOn g φ A) : arcComponentsIn (φ '' A) = image φ '' arcComponentsIn A := by
  ext C
  constructor
  · intro hC
    have hgA : g '' (φ '' A) = A := by
      rw [image_image]
      exact (image_congr fun x hx => hl hx).trans (image_id' A)
    have hr : LeftInvOn φ g (φ '' A) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hl hx]
    have h1 := image_mem_arcComponentsIn hg (by rwa [hgA]) hr hC
    rw [hgA] at h1
    refine ⟨g '' C, h1, ?_⟩
    rw [image_image]
    exact (image_congr fun y hy => hr (hC.2.1 hy)).trans (image_id' C)
  · rintro ⟨e, he, rfl⟩
    exact image_mem_arcComponentsIn hφ hg hl he

/-- Two different edges do not meet, and they meet in closure at their common ends only. -/
theorem closure_inter_subset (D : Drawing S) {e f : Set S} (he : e ∈ D.E) (hf : f ∈ D.E)
    (hne : e ≠ f) {x : S} (h1 : x ∈ closure e) (h2 : x ∈ closure f) : x ∈ tilde e ∧ x ∈ tilde f
      := by
  have hV : x ∈ D.V := by
    by_contra hV
    have hxe : x ∈ e := by rw [← D.closure_diff_V he]; exact ⟨h1, hV⟩
    have hxf : x ∈ f := by rw [← D.closure_diff_V hf]; exact ⟨h2, hV⟩
    exact hne (arcComp_eq_of_mem he hf hxe hxf)
  rw [tilde_eq_inter_V D he, tilde_eq_inter_V D hf]
  exact ⟨⟨h1, hV⟩, h2, hV⟩

private theorem image_drawing_without_edge
    {S : Type}
    [TopologicalSpace S]
    {D : Drawing S}
    {f : Set S}
    (w : S)
    (φ : S → S)
    (hLw : ∀ x ∈ (closure f), φ x = w)
    (hLV' : ∀ x ∈ (closure f), x ∉ D.V → x ∈ f)
    (hwV : w ∈ φ '' D.V)
    (hsame : ∀ (x y : S), φ x = φ y → x = y ∨ x ∈ (closure f) ∧ y ∈ (closure f))
    (D₀ : Surface.Drawing S)
    (hD₀U : D₀.U = D.U \ f)
    (hD₀V : D₀.V = D.V) :
    φ '' D.U \ φ '' D.V = φ '' (D₀.U \ D₀.V) := by
  rw [hD₀U, hD₀V]
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    have hyV : y ∉ D.V := fun h1 => h ⟨y, h1, rfl⟩
    refine ⟨y, ⟨⟨hy, fun hyf => ?_⟩, hyV⟩, rfl⟩
    exact h (by rw [hLw y (subset_closure hyf)]; exact hwV)
  · rintro ⟨y, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    refine ⟨⟨y, h1, rfl⟩, ?_⟩
    rintro ⟨z, hz, he⟩
    rcases hsame z y he with rfl | ⟨-, hy⟩
    · exact h3 hz
    · exact h2 (by simpa using (hLV' y hy h3))

private theorem continuous_inverse_off_edge
    {S : Type}
    [TopologicalSpace S]
    {f : Set S}
    (w : S)
    (φ : S → S)
    (hφcl : IsClosedMap φ)
    (hLw : ∀ x ∈ (closure f), φ x = w)
    (hLn : ∀ x ∉ (closure f), φ x ≠ w)
    (hLi : InjOn φ (closure f)ᶜ)
    (g : S → S)
    (hgl : LeftInvOn g φ (closure f)ᶜ) :
    ContinuousOn g (φ '' (closure f)ᶜ) := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  refine ⟨φ '' (C ∪ (closure f)), hφcl _ (hC.union isClosed_closure), ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyL⟩
    refine ⟨⟨g y, .inl hy, ?_⟩, hyL⟩
    obtain ⟨x, hx, rfl⟩ := hyL
    rw [hgl hx]
  · rintro ⟨⟨x, hx, rfl⟩, ⟨z, hz, he⟩⟩
    rcases hx with hx | hx
    · refine ⟨?_, ⟨z, hz, he⟩⟩
      by_cases hxL : x ∈ (closure f)
      · exact absurd (he.trans (hLw x hxL)) (hLn z hz)
      · have : z = x := hLi hz hxL he
        subst this
        change g (φ z) ∈ C
        rw [hgl hz]
        exact hx
    · exact absurd (he.trans (hLw x hx)) (hLn z hz)

private theorem contracted_edge_has_distinct_ends
    {S : Type}
    [TopologicalSpace S]
    {D : Drawing S}
    (hD : LoopFree D)
    {f : Set S}
    (hf : f ∈ Drawing.E D)
    (hno : ∀ e ∈ Drawing.E D, e ≠ f → tilde e ≠ tilde f)
    [T2Space S]
    (u : S)
    (v : S)
    (huv : u ≠ v)
    (hfe : tilde f = {u, v})
    (a : 𝕀 → S)
    (ha0 : a 0 = u)
    (ha1 : a 1 = v)
    (φ : S → S)
    (hφc : Continuous φ)
    (hφcl : IsClosedMap φ)
    (hline : IsLineWithEnds (closure f) u v)
    (htV : ∀ x ∈ tilde f, x ∈ (closure f) ∧ x ∈ D.V)
    (huT : u ∈ tilde f)
    (hvT : v ∈ tilde f)
    (hsame : ∀ (x y : S), φ x = φ y → x = y ∨ x ∈ (closure f) ∧ y ∈ (closure f)) :
    ∀ e ∈ Drawing.E D \ {f}, ∃ p q, φ p ≠ φ q ∧ tilde e = {p, q} ∧ InjOn φ (closure e) ∧ closure
      (φ '' e) = φ '' closure e ∧ IsLineWithEnds (closure (φ '' e)) (φ p) (φ q) ∧ closure (φ '' e)
      ∩ φ '' D.V = {φ p, φ q} := by
  rintro e ⟨he, hne⟩
  obtain ⟨p, q, hpq, hte, hl⟩ := hD e he
  have hclos : ∀ x ∈ closure e, x ∈ (closure f) → x ∈ tilde e ∧ x ∈ tilde f := fun x h1 h2 =>
    closure_inter_subset D he hf hne h1 h2
  have hinj : InjOn φ (closure e) := by
    intro x hx y hy hxy
    rcases hsame x y hxy with h | ⟨h1, h2⟩
    · exact h
    · by_contra hne'
      apply hno e he hne
      have h3 := hclos x hx h1
      have h4 := hclos y hy h2
      have h5 : tilde e = {x, y} := by
        rw [hte] at h3 h4 ⊢
        rcases h3.1 with rfl | rfl <;> rcases h4.1 with rfl | rfl
        · exact absurd rfl hne'
        · rfl
        · exact pair_comm _ _
        · exact absurd rfl hne'
      have h6 : tilde f = {x, y} := by
        have h3' := h3.2
        have h4' := h4.2
        rw [hfe] at h3' h4' ⊢
        rcases h3' with rfl | rfl <;> rcases h4' with rfl | rfl
        · exact absurd rfl hne'
        · rfl
        · exact pair_comm _ _
        · exact absurd rfl hne'
      rw [h5, h6]
  have hpT : p ∈ closure e := by
    have : p ∈ tilde e := by rw [hte]; exact .inl rfl
    exact this.1
  have hqT : q ∈ closure e := by
    have : q ∈ tilde e := by rw [hte]; exact .inr rfl
    exact this.1
  have hpq' : φ p ≠ φ q := fun h => hpq (hinj hpT hqT h)
  have hcl : closure (φ '' e) = φ '' closure e :=
    Subset.antisymm (hφcl.closure_image_subset _) (image_closure_subset_closure_image hφc)
  obtain ⟨b, hb, hbr, hb0, hb1⟩ := hl.exists_arc
  have hbarc : IsArcMap (φ ∘ b) := ⟨hφc.comp hb.1, fun s t h => hb.2 (hinj
    (hbr ▸ mem_range_self s) (hbr ▸ mem_range_self t) h)⟩
  have hlin := hbarc.isLineWithEnds
  rw [range_comp, hbr, Function.comp_apply, Function.comp_apply, hb0, hb1, ← hcl] at hlin
  refine ⟨p, q, hpq', hte, hinj, hcl, hlin, ?_⟩
  rw [hcl]
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, ⟨z, hz, he'⟩⟩
    have hyV : y ∈ D.V := by
      rcases hsame z y he' with rfl | ⟨-, hyL⟩
      · exact hz
      · by_contra hyV
        have h1 : y ∈ e := by rw [← D.closure_diff_V he]; exact ⟨hy, hyV⟩
        exact hyV (htV y (hclos y hy hyL).2).2
    have hyT : y ∈ tilde e := by
      rw [tilde_eq_inter_V D he]
      exact ⟨hy, hyV⟩
    rw [hte] at hyT
    rcases hyT with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
  · have hV : ∀ x ∈ tilde e, x ∈ D.V := fun x hx => by
      rw [tilde_eq_inter_V D he] at hx
      exact hx.2
    rintro (rfl | rfl)
    · exact ⟨⟨p, hpT, rfl⟩, ⟨p, hV p (by rw [hte]; exact .inl rfl), rfl⟩⟩
    · exact ⟨⟨q, hqT, rfl⟩, ⟨q, hV q (by rw [hte]; exact .inr rfl), rfl⟩⟩

private theorem normal_set_image_under_contraction
    {S : Type}
    [TopologicalSpace S]
    {D : Drawing S}
    (φ : S → S)
    (L : Set S)
    (hsame : ∀ (x y : S), φ x = φ y → x = y ∨ x ∈ L ∧ y ∈ L)
    (D' : Drawing S)
    (hU : D'.U = φ '' D.U)
    (hV : D'.V = φ '' D.V)
    (F : Set S)
    (hFn : D.IsNormal F)
    (hFL : ∀ x ∈ F, x ∈ L → x ∈ D.V) :
    ∀ B ⊆ F, D'.IsNormal (φ '' B) ∧ (φ '' B ∩ D'.V).ncard ≤ (F ∩ D.V).ncard := by
  intro B hB
  have hnormal : φ '' B ∩ (φ '' D.U) ⊆ φ '' D.V := by
    rintro _ ⟨⟨b, hb, rfl⟩, ⟨y, hy, he⟩⟩
    rcases hsame y b he with rfl | ⟨-, h2⟩
    · exact ⟨y, hFn ⟨hB hb, hy⟩, rfl⟩
    · exact ⟨b, hFL b (hB hb) h2, rfl⟩
  refine ⟨by simpa only [Drawing.IsNormal, hU, hV] using hnormal, ?_⟩
  rw [hV]
  have h1 : φ '' B ∩ φ '' D.V ⊆ φ '' (F ∩ D.V) := by
    rintro _ ⟨⟨b, hb, rfl⟩, ⟨y, hy, he⟩⟩
    rcases hsame y b he with rfl | ⟨-, h2⟩
    · exact ⟨y, ⟨hB hb, hy⟩, rfl⟩
    · exact ⟨b, ⟨hB hb, hFL b (hB hb) h2⟩, rfl⟩
  have hfin' : (F ∩ D.V).Finite := D.finite_V.subset inter_subset_right
  exact (ncard_le_ncard h1 (hfin'.image _)).trans (ncard_image_le hfin')

private theorem arc_collapses_to_injective_loop
    {S : Type}
    [TopologicalSpace S]
    {D : Drawing S}
    {f : Set S}
    (u : S)
    (v : S)
    (hfe : tilde f = {u, v})
    (w : S)
    (c : C(𝕀 × S, S))
    (L : Set S)
    (hLV : ∀ x ∈ L, x ∈ D.V → x ∈ tilde f)
    (hsame : ∀ (x y : S), c (1, x) = c (1, y) → x = y ∨ x ∈ L ∧ y ∈ L)
    (F : Set S)
    (hFL : ∀ x ∈ F, x ∈ L → x ∈ D.V)
    (hu' : c (1, u) = w)
    (hv' : c (1, v) = w) :
    ∀ (x : 𝕀 → S), IsArcMap x → x 0 = u → x 1 = v → range x ⊆ F →
      ∃ γ : C(Circle, S), (∀ t : 𝕀, γ (arcParam 1 t) = c (1, x t)) ∧
        range γ = (fun x => c (1, x)) '' range x ∧ Function.Injective γ := by
  let φ := fun x => c (1, x)
  intro x hx hx0 hx1 hxF
  let ℓ : C(𝕀, S) := ⟨fun t => c (1, x t), by have := hx.1; fun_prop⟩
  have hℓ : ℓ 0 = ℓ 1 := by
    change c (1, x 0) = c (1, x 1)
    rw [hx0, hx1, hu', hv']
  let γ := loopLift 1 ℓ hℓ
  have hγ : ∀ t, γ (arcParam 1 t) = c (1, x t) := fun t => loopLift_apply 1 ℓ hℓ t
  refine ⟨γ, hγ, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨t, rfl⟩ := arcParam_surjective 1 z
      exact ⟨x t, ⟨t, rfl⟩, (hγ t).symm⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨arcParam 1 t, hγ t⟩
  · intro z z' he
    obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
    obtain ⟨t, rfl⟩ := arcParam_surjective 1 z'
    rw [hγ, hγ] at he
    have hends : ∀ r, x r ∈ L → r = 0 ∨ r = 1 := fun r hr => by
      have h2 := hLV _ hr (hFL _ (hxF ⟨r, rfl⟩) hr)
      rw [hfe] at h2
      rcases h2 with h2 | h2
      · exact .inl (hx.2 (h2.trans hx0.symm))
      · exact .inr (hx.2 (h2.trans hx1.symm))
    rcases hsame _ _ he with h2 | ⟨h2, h3⟩
    · rw [hx.2 h2]
    · have h4 : arcParam 1 (0 : 𝕀) = arcParam 1 (1 : 𝕀) := by
        simp [arcParam_zero, arcParam_one]
      rcases hends s h2 with rfl | rfl <;> rcases hends t h3 with rfl | rfl
      · rfl
      · exact h4
      · exact h4.symm
      · rfl

/-- **Contracting an edge.** Let `f` be an edge of a loop-free drawing in a closed surface, with no
parallel edge. Then there are a loop-free drawing `D'` with `rep(D') ≤ rep(D)` and a map `φ` that
identifies the ends of `f` and no other two vertices, and that maps the other edges of `D` onto the
edges of `D'`, preserving incidence. -/
theorem exists_contract (hT : IsClosedSurface S) {D : Drawing S} (hD : LoopFree D) {f : Set S}
    (hf : f ∈ D.E) (hno : ∀ e ∈ D.E, e ≠ f → tilde e ≠ tilde f) :
    ∃ (D' : Drawing S) (φ : S → S), LoopFree D' ∧ D'.V = φ '' D.V ∧
      (∀ x ∈ D.V, ∀ y ∈ D.V, φ x = φ y ↔ x = y ∨ (x ∈ tilde f ∧ y ∈ tilde f)) ∧
      BijOn (image φ) (D.E \ {f}) D'.E ∧ (∀ e ∈ D.E, e ≠ f → tilde (φ '' e) = φ '' tilde e) ∧
      D'.rep ≤ D.rep := by
  classical
  have hcpt : CompactSpace S := hT.1
  have ht2 : T2Space S := hT.2.1
  obtain ⟨u, v, huv, hfe, hline⟩ := hD f hf
  obtain ⟨a, ha, har, ha0, ha1⟩ := hline.exists_arc
  obtain ⟨c', w, hcc, hc0, hcL, hcn, hci, hcs⟩ := exists_collapse hT ha
  rw [har] at hcL hcn hci
  let c : C(𝕀 × S, S) := ⟨c', hcc⟩
  let φ : S → S := fun x => c (1, x)
  have hφc : Continuous φ := by fun_prop
  have hφcl : IsClosedMap φ := hφc.isClosedMap
  set L := closure f with hL
  have hne : Nonempty S := ⟨u⟩
  have hLw : ∀ x ∈ L, φ x = w := hcL
  have hLn : ∀ x, x ∉ L → φ x ≠ w := hcn
  have hLi : InjOn φ Lᶜ := hci
  have hLV : ∀ x ∈ L, x ∈ D.V → x ∈ tilde f := fun x h1 h2 => by
    rw [tilde_eq_inter_V D hf]
    exact ⟨h1, h2⟩
  have hLV' : ∀ x ∈ L, x ∉ D.V → x ∈ f := fun x h1 h2 => by
    rw [← D.closure_diff_V hf]
    exact ⟨h1, h2⟩
  have htV : ∀ x ∈ tilde f, x ∈ L ∧ x ∈ D.V := fun x hx => by
    rwa [tilde_eq_inter_V D hf] at hx
  have huT : u ∈ tilde f := by rw [hfe]; exact .inl rfl
  have hvT : v ∈ tilde f := by rw [hfe]; exact .inr rfl
  have hwV : w ∈ φ '' D.V := ⟨u, (htV u huT).2, hLw u (htV u huT).1⟩
  have hsame : ∀ x y, φ x = φ y → x = y ∨ (x ∈ L ∧ y ∈ L) := fun x y h => by
    by_cases hx : x ∈ L
    · have hy : y ∈ L := by
        by_contra hy
        exact hLn y hy (h ▸ hLw x hx)
      exact .inr ⟨hx, hy⟩
    · have hy : y ∉ L := fun hy => hLn x hx (h.trans (hLw y hy))
      exact .inl (hLi hx hy h)
  let D₀ := D.deleteEdge f
  have hD₀U : D₀.U = D.U \ f := deleteEdge_U D hf
  have hD₀V : D₀.V = D.V := Subset.antisymm (deleteEdge_isSubdrawing D f).1 fun x hx
    => .inl ⟨hx, hx⟩
  have hD₀E : arcComponentsIn (D₀.U \ D₀.V) = D.E \ {f} := deleteEdge_E D f
  have hAL : D₀.U \ D₀.V ⊆ Lᶜ := by
    rintro x ⟨h1, h2⟩ h3
    rw [hD₀U] at h1
    rw [hD₀V] at h2
    exact h1.2 (hLV' x h3 h2)
  have himg : (φ '' D.U) \ (φ '' D.V) = φ '' (D₀.U \ D₀.V) := by
    exact image_drawing_without_edge (S := S) (D := D) (f := f) w φ hLw hLV' hwV hsame D₀ hD₀U
      hD₀V
  let g : S → S := Function.invFunOn φ Lᶜ
  have hgl : LeftInvOn g φ Lᶜ := hLi.leftInvOn_invFunOn
  have hgc : ContinuousOn g (φ '' Lᶜ) := by
    exact continuous_inverse_off_edge (S := S) (f := f) w φ hφcl hLw hLn hLi g hgl
  have hcomp : arcComponentsIn (φ '' (D₀.U \ D₀.V)) = image φ '' (D.E \ {f}) := by
    rw [arcComponentsIn_image_eq hφc.continuousOn (hgc.mono (image_mono hAL)) (hgl.mono hAL), hD₀E]
  have hfin : (arcComponentsIn ((φ '' D.U) \ (φ '' D.V))).Finite := by
    rw [himg, hcomp]
    exact (D.finite_edges.subset sdiff_subset).image _
  -- facts on one other edge
  have hedge : ∀ e ∈ D.E \ {f}, ∃ p q : S, φ p ≠ φ q ∧ tilde e = {p, q} ∧ InjOn φ (closure e) ∧
      closure (φ '' e) = φ '' closure e ∧ IsLineWithEnds (closure (φ '' e)) (φ p) (φ q) ∧
      closure (φ '' e) ∩ φ '' D.V = {φ p, φ q} := by
    exact contracted_edge_has_distinct_ends (S := S) (D := D) hD (f := f) hf hno u v huv hfe a ha0
      ha1 φ hφc hφcl hline htV huT hvT hsame
  let D' : Drawing S :=
    { U := φ '' D.U
      V := φ '' D.V
      V_subset_U := image_mono D.V_subset_U
      isClosed_U := hφcl _ D.isClosed_U
      finite_V := D.finite_V.image _
      finite_edges := hfin
      edge_cond := by
        intro e he
        rw [himg, hcomp] at he
        obtain ⟨e₀, he₀, rfl⟩ := he
        obtain ⟨p, q, h1, -, -, -, h2, h3⟩ := hedge e₀ he₀
        exact .inl ⟨φ p, φ q, h1, h3, h2⟩ }
  have hE' : D'.E = image φ '' (D.E \ {f}) := by
    change arcComponentsIn ((φ '' D.U) \ (φ '' D.V)) = _
    rw [himg, hcomp]
  have htilde : ∀ e₀ ∈ D.E \ {f}, tilde (φ '' e₀) = φ '' tilde e₀ := by
    intro e₀ he₀
    obtain ⟨p, q, h1, h2, -, -, -, h3⟩ := hedge e₀ he₀
    have h4 : φ '' e₀ ∈ D'.E := by
      rw [hE']
      exact ⟨e₀, he₀, rfl⟩
    rw [tilde_eq_inter_V D' h4]
    change closure (φ '' e₀) ∩ φ '' D.V = _
    rw [h3, h2, image_pair]
  refine ⟨D', φ, ?_, rfl, ?_, ?_, fun e he hne => htilde e ⟨he, hne⟩, ?_⟩
  · intro e he
    rw [hE'] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨p, q, h1, h2, -, -, h3, h4⟩ := hedge e₀ he₀
    refine ⟨φ p, φ q, h1, ?_, h3⟩
    rw [htilde e₀ he₀, h2, image_pair]
  · intro x hx y hy
    constructor
    · intro h
      rcases hsame x y h with h1 | ⟨h1, h2⟩
      · exact .inl h1
      · exact .inr ⟨hLV x h1 hx, hLV y h2 hy⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · rfl
      · rw [hLw x (htV x h1).1, hLw y (htV y h2).1]
  · refine ⟨fun e he => ?_, ?_, ?_⟩
    · rw [hE']
      exact ⟨e, he, rfl⟩
    · intro e₁ he₁ e₂ he₂ h
      have hsubL : ∀ e ∈ D.E \ {f}, e ⊆ Lᶜ := fun e he => by
        rw [← hD₀E] at he
        exact he.2.1.trans hAL
      have h1 : g '' (φ '' e₁) = e₁ := by
        rw [image_image]
        exact (image_congr fun x hx => hgl (hsubL e₁ he₁ hx)).trans (image_id' e₁)
      have h2 : g '' (φ '' e₂) = e₂ := by
        rw [image_image]
        exact (image_congr fun x hx => hgl (hsubL e₂ he₂ hx)).trans (image_id' e₂)
      change φ '' e₁ = φ '' e₂ at h
      rw [← h1, ← h2, h]
    · rw [hE']
      exact Subset.rfl
  · refine le_sInf ?_
    rintro _ ⟨F, hFo, hFn, hFnull, rfl⟩
    have hFL : ∀ x ∈ F, x ∈ L → x ∈ D.V := fun x hxF hxL => by
      by_contra hV
      exact hV (hFn ⟨hxF, D.closure_subset_U hf hxL⟩)
    -- normality and the count for a subset of `F`
    have hsub : ∀ B ⊆ F, D'.IsNormal (φ '' B) ∧ (φ '' B ∩ D'.V).ncard ≤ (F ∩ D.V).ncard := by
      exact normal_set_image_under_contraction (S := S) (D := D) φ L hsame D' rfl rfl F hFn hFL
    have finish : ∀ B ⊆ F, IsOArc (φ '' B) → ¬ IsNullHomotopicOArc (φ '' B) →
        D'.rep ≤ (((F ∩ D.V).ncard : ℕ) : ℕ∞) := fun B hB h1 h2 =>
      (rep_le_of_arc D' h1 (hsub B hB).1 h2).trans (by exact_mod_cast (hsub B hB).2)
    by_cases hboth : u ∈ F ∧ v ∈ F
    · obtain ⟨a', b', hab, h0, h1, hunion⟩ := hFo.exists_arcs hboth.1 hboth.2 huv
      have hb0 : b' 0 = u := by rw [hab.zero, h0]
      have hb1 : b' 1 = v := by rw [hab.one, h1]
      have hu' : c (1, u) = w := hLw u (htV u huT).1
      have hv' : c (1, v) = w := hLw v (htV v hvT).1
      -- the loop of an arc
      have hloop : ∀ x : 𝕀 → S, IsArcMap x → x 0 = u → x 1 = v → range x ⊆ F →
          ∃ γ : C(Circle, S), (∀ t, γ (arcParam 1 t) = c (1, x t)) ∧ range γ = φ '' range x ∧
            Function.Injective γ := by
        exact arc_collapses_to_injective_loop (S := S) (D := D) (f := f) u v hfe w c L hLV
          hsame F hFL hu' hv'
      obtain ⟨γa, hγa, hra, hia⟩ := hloop a' hab.arc_left h0 h1 (hunion ▸ subset_union_left)
      obtain ⟨γb, hγb, hrb, hib⟩ := hloop b' hab.arc_right hb0 hb1 (hunion ▸ subset_union_right)
      have hnot : ¬ IsNullHomotopicOArc (range a' ∪ range b') := by rwa [hunion]
      rcases not_null_of_two_arcs c hc0 hab (w := w) (h0 ▸ hu') (h1 ▸ hv') hnot hγa hγb with h | h
      · refine finish (range a') (hunion ▸ subset_union_left) ?_ fun hn => ?_
        · rw [← hra]
          exact isOArc_range hia
        · exact h (null_of_param hn γa hra)
      · refine finish (range b') (hunion ▸ subset_union_right) ?_ fun hn => ?_
        · rw [← hrb]
          exact isOArc_range hib
        · exact h (null_of_param hn γb hrb)
    · have hinjF : InjOn φ F := by
        intro x hx y hy hxy
        rcases hsame x y hxy with h | ⟨h1, h2⟩
        · exact h
        · have hx' := hLV x h1 (hFL x hx h1)
          have hy' := hLV y h2 (hFL y hy h2)
          rw [hfe] at hx' hy'
          by_contra hne
          apply hboth
          rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
          · exact absurd rfl hne
          · exact ⟨hx, hy⟩
          · exact ⟨hy, hx⟩
          · exact absurd rfl hne
      obtain ⟨ξ⟩ := hFo
      let γ : C(Circle, S) := ⟨fun z => (ξ z).1, by fun_prop⟩
      let γ' : C(Circle, S) := ⟨fun z => c (1, γ z), by fun_prop⟩
      have hγr : range γ = F := by
        ext x
        constructor
        · rintro ⟨z, rfl⟩
          exact (ξ z).2
        · intro hx
          exact ⟨ξ.symm ⟨x, hx⟩, by simp [γ]⟩
      have hγ'r : range γ' = φ '' F := by
        rw [← hγr, ← range_comp]
        rfl
      have hγ'i : Function.Injective γ' := by
        intro z z' h
        exact ξ.injective (Subtype.ext (hinjF (ξ z).2 (ξ z').2 h))
      refine finish F Subset.rfl ?_ fun hn => ?_
      · rw [← hγ'r]
        exact isOArc_range hγ'i
      · have h1 := null_of_param hn γ' hγ'r
        have h2 := null_of_collapse c hc0 (ψ := γ) (ψ' := γ') (fun _ => rfl) h1
        exact hFnull ⟨ξ, h2⟩

end GraphMinor.GM19
