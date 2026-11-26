/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PerimeterPull
public import LeanPool.GraphMinor.GM11.NiceSets
public import LeanPool.GraphMinor.GM11.Section7b
public import LeanPool.GraphMinor.GM11.EvenCircuit

/-!
# Existence of perimeter walks

`exists_perimeter_of_disc`: a closed, `Γ`-nice, simply-connected set `X` inside an open disc has a
perimeter
walk, which uses each edge of `Γ ∩ bd(X)` once for each side of the edge outside `X`. The proof
collapses the
complement of the open disc to a point. In the resulting sphere `Γ ∩ bd(X)` is 2-cell, the
complement of
`X` is a region of it, and `exists_region_walk` gives the walk.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval OnePoint

universe u

/-- An injective image of an `O`-arc in a Hausdorff space is an `O`-arc. -/
theorem isOArc_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {F : Set X}
    (hF : IsOArc F) {G : X → Y} (hG : ContinuousOn G F) (hi : InjOn G F) : IsOArc (G '' F) := by
  obtain ⟨φ⟩ := hF
  have hc : CompactSpace F := φ.compactSpace
  let j : F → G '' F := fun x => ⟨G x.1, x.1, x.2, rfl⟩
  have hjc : Continuous j := Continuous.subtype_mk hG.domRestrict _
  have hjb : Function.Bijective j := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hi x.2 y.2 (congrArg Subtype.val hxy))
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨φ.trans (hjc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j hjb))⟩

section Count

variable {α β : Type*}

open Classical in
theorem edgeCount_map {S S' : Type*} {l : List (Set S')} {G : Set S' → Set S} {T : Set (Set S')}
    (hl : ∀ x ∈ l, x ∈ T) (hinj : InjOn G T) {e : Set S'} (he : e ∈ T) :
    edgeCount (l.map G) (G e) = edgeCount l e := by
  induction l with
  | nil => simp [edgeCount]
  | cons a l ih =>
    have h₁ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [edgeCount] at h₁ ⊢
    have ha := hl a List.mem_cons_self
    by_cases hae : a = e
    · subst hae
      simp [List.count_cons_self, h₁]
    · have hne : G a ≠ G e := fun h => hae (hinj ha he h)
      rw [List.map_cons, List.count_cons_of_ne hne, List.count_cons_of_ne hae, h₁]

open Classical in
theorem edgeCount_eq_zero {S : Type*} {l : List (Set S)} {e : Set S} (h : e ∉ l) : edgeCount l e
  = 0 :=
  List.count_eq_zero.mpr h

end Count

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S} {X A :
  Set S}

private theorem drawing_circle_bounds_subdisc
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    [ConnectedSpace S]
    {X : Set S}
    {A : Set S}
    (hS : IsClosedSurface S)
    (hXs : IsSimplyConnectedSet X)
    (hXA : X ⊆ A)
    [T2Space (OnePoint ↑A)]
    (hf : Continuous (collapse A))
    (g : OnePoint ↑A → S)
    (hfA : ∀ {x : S}, x ∈ A → (collapse A) x ≠ ∞)
    (hgf : ∀ (x : S), (collapse A) x ≠ ∞ → g ((collapse A) x) = x)
    (hfg : ∀ (y : OnePoint ↑A), y ≠ ∞ → (collapse A) (g y) = y)
    (hgc : ∀ (y : OnePoint ↑A), y ≠ ∞ → ContinuousAt g y)
    (hinjA : InjOn (collapse A) A)
    (hQc : IsClosed[instTopologicalSpace] ((collapse A) '' X))
    (hinf : ∞ ∉ ((collapse A) '' X))
    (D : Drawing (OnePoint ↑A))
    (hDU' : D.U = frontier ((collapse A) '' X)) :
    ∀ (F : Set (OnePoint ↑A)), IsOArc F → F ⊆ D.U → ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ ((collapse A) '' X)
      ∧ discBd Δ = F := by
  let f := collapse A
  let Q := f '' X
  intro F hF hFU
  have hFinf : ∀ y ∈ F, y ≠ ∞ := fun y hy h => hinf (h ▸ hQc.frontier_subset (hDU' ▸ hFU hy))
  have hgcF : ContinuousOn g F := fun y hy => (hgc y (hFinf y hy)).continuousWithinAt
  have hginj : InjOn g F := fun x hx y hy h => by
    rw [← hfg x (hFinf x hx), ← hfg y (hFinf y hy), h]
  have hO := isOArc_image hF hgcF hginj
  have hFX : g '' F ⊆ X := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hDU'] at hFU
    obtain ⟨x, hx, rfl⟩ := hQc.frontier_subset (hFU hy)
    rw [hgf x (hfA (hXA hx))]
    exact hx
  obtain ⟨φ⟩ := id hO
  have hnull : IsNullHomotopicOArcIn X (g '' F) := by
    refine ⟨φ, hXs.2 _ ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hFX (φ z).2
  obtain ⟨Δ, hΔX, hΔ, hbd⟩ := theorem_7_2_proof hS hO hFX hnull
  obtain ⟨h₁, h₂⟩ := isClosedDisc_image hΔ hf.continuousOn (hinjA.mono (hΔX.trans hXA))
  refine ⟨f '' Δ, h₁, image_mono hΔX, ?_⟩
  rw [h₂, ← IsClosedDisc.frontier_eq_discBd hS hΔ, ← subBd_eq_frontier, hbd, image_image]
  calc (fun x => f (g x)) '' F = id '' F := image_congr fun y hy => hfg y (hFinf y hy)
    _ = F := image_id F

private theorem map_link_of_drawing_embedding
    {S : Type u}
    [TopologicalSpace S]
    {Γ : Drawing S}
    {A : Set S}
    (g : OnePoint ↑A → S)
    (hfA : ∀ {x : S}, x ∈ A → (collapse A) x ≠ ∞)
    (hgf : ∀ (x : S), (collapse A) x ≠ ∞ → g ((collapse A) x) = x)
    (hinjA : InjOn (collapse A) A)
    (B : Drawing S)
    (hBs : B.IsSubdrawing Γ)
    (hBA : B.U ⊆ A)
    (D : Drawing (OnePoint ↑A))
    (hDV : D.V = collapse A '' B.V)
    (hcl : ∀ e ∈ B.E, closure[instTopologicalSpace] (collapse A '' e) = collapse A '' closure e)
    (hEA : ∀ {e₀ : Set S}, e₀ ∈ B.E → e₀ ⊆ A)
    (hgfe : ∀ {e₀ : Set S}, e₀ ⊆ A → g '' (collapse A) '' e₀ = e₀)
    (hEA' : ∀ e ∈ D.E, ∃ e₀ ∈ B.E, e = (collapse A) '' e₀) :
    ∀ (e : Set (OnePoint ↑A)) (x y : OnePoint ↑A), D.toGraph.IsLink e x y → Γ.toGraph.IsLink (g ''
      e) (g x) (g y) := by
  let f := collapse A
  rintro e x y ⟨he, hx, hy, hcap⟩
  obtain ⟨e₀, he₀, rfl⟩ := hEA' e he
  rw [hDV] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hxA : x₀ ∈ A := hBA (B.V_subset_U hx₀)
  have hyA : y₀ ∈ A := hBA (B.V_subset_U hy₀)
  rw [hgfe (hEA he₀), hgf x₀ (hfA hxA), hgf y₀ (hfA hyA)]
  refine ⟨hBs.2 he₀, hBs.1 hx₀, hBs.1 hy₀, ?_⟩
  rw [← hBs.closure_inter_V he₀]
  rw [hcl e₀ he₀, hDV] at hcap
  have hclA : closure e₀ ⊆ A := (B.closure_subset_U he₀).trans hBA
  ext w
  constructor
  · rintro ⟨hw, hwV⟩
    have hmem' : f w ∈ f '' closure e₀ ∩ f '' B.V := ⟨mem_image_of_mem f hw, mem_image_of_mem f
      hwV⟩
    rw [hcap] at hmem'
    rcases hmem' with h₁ | h₁
    · exact Or.inl (hinjA (hclA hw) hxA h₁)
    · exact Or.inr (hinjA (hclA hw) hyA h₁)
  · have hxm : f x₀ ∈ f '' closure e₀ ∩ f '' B.V := by
      rw [hcap]
      exact Or.inl rfl
    have hym : f y₀ ∈ f '' closure e₀ ∩ f '' B.V := by
      rw [hcap]
      exact Or.inr rfl
    rintro (rfl | rfl)
    · obtain ⟨z, hz, hze⟩ := hxm.1
      obtain rfl := hinjA (hclA hz) hxA hze
      exact ⟨hz, hx₀⟩
    · obtain ⟨z, hz, hze⟩ := hym.1
      obtain rfl := hinjA (hclA hz) hyA hze
      exact ⟨hz, hy₀⟩

open Classical in
private theorem perimeter_edge_count_pull
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {Γ : Drawing S}
    {X : Set S}
    {A : Set S}
    (hS : IsClosedSurface S)
    (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X)
    (hA : IsOpenDisc A)
    (hf : Continuous (collapse A))
    (g : OnePoint ↑A → S)
    (hfA : ∀ {x : S}, x ∈ A → (collapse A) x ≠ ∞)
    (hgf : ∀ (x : S), (collapse A) x ≠ ∞ → g ((collapse A) x) = x)
    (hopenf : ∀ {O : Set S}, IsOpen O → O ⊆ A → IsOpen[instTopologicalSpace] ((collapse A) '' O))
    (hpre : (collapse A) ⁻¹' ((collapse A) '' X) = X)
    (hfr : frontier ((collapse A) '' X) = (collapse A) '' frontier X)
    (D : Drawing (OnePoint ↑A))
    (hDE : D.E = image (collapse A) '' (Γ.interSet (frontier X)).E)
    (u' : OnePoint ↑A)
    (W' : GraphWalk D.toGraph u' u')
    (hcount : ∀ e ∈ D.E, edgeCount W'.edges e =
      if (e ∩ frontier ((collapse A '' X)ᶜ)).Nonempty then
        if IsTwoSided (collapse A '' X)ᶜ e then 2 else 1 else 0)
    (hEA : ∀ {e₀ : Set S}, e₀ ∈ (Γ.interSet (frontier X)).E → e₀ ⊆ A)
    (hgfe : ∀ {e₀ : Set S}, e₀ ⊆ A → g '' (collapse A) '' e₀ = e₀)
    (hEA' : ∀ e ∈ D.E, ∃ e₀ ∈ (Γ.interSet (frontier X)).E, e = (collapse A) '' e₀)
    (W : GraphWalk Γ.toGraph (g u') (g u'))
    (hedges : W.edges = List.map (image g) W'.edges) :
    ∀ e ∈ Γ.E, edgeCount W.edges e = if (e ∩ frontier X).Nonempty then if IsTwoSided Xᶜ e then 2
      else 1 else 0 := by
  let f := collapse A
  let Q := f '' X
  let B := Γ.interSet (frontier X)
  intro e he
  have hBE : ∀ e₀, e₀ ∈ B.E ↔ e₀ ∈ Γ.E ∧ e₀ ⊆ frontier X := by
    intro e₀
    change e₀ ∈ (Γ.span _ _).E ↔ _
    rw [Γ.span_E]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  by_cases hef : (e ∩ frontier X).Nonempty
  · obtain ⟨y, hye, hyf⟩ := hef
    have heB : e ∈ B.E := (hBE e).mpr ⟨he, edge_subset_frontier hS hXc hXn he hye hyf⟩
    have heA := hEA heB
    have heD : f '' e ∈ D.E := hDE ▸ mem_image_of_mem _ heB
    have hinjG : InjOn (image g) D.E := by
      intro e₁ h₁ e₂ h₂ h
      obtain ⟨c₁, hc₁, rfl⟩ := hEA' e₁ h₁
      obtain ⟨c₂, hc₂, rfl⟩ := hEA' e₂ h₂
      rw [hgfe (hEA hc₁), hgfe (hEA hc₂)] at h
      rw [h]
    have hmemD : ∀ x ∈ W'.edges, x ∈ D.E := fun x hx => mem_E_of_mem_edges W' hx
    have hc₁ := edgeCount_map hmemD hinjG heD
    rw [← hedges, hgfe heA] at hc₁
    rw [hc₁, hcount _ heD]
    have hn : ((f '' e) ∩ frontier Qᶜ).Nonempty := by
      refine ⟨f y, mem_image_of_mem f hye, ?_⟩
      rw [frontier_compl, hfr]
      exact mem_image_of_mem f hyf
    have hpreU : f ⁻¹' (Qᶜ ∪ f '' e) = Xᶜ ∪ e := by
      ext z
      constructor
      · rintro (hz | ⟨w, hw, hwz⟩)
        · refine Or.inl fun hzX => hz (mem_image_of_mem f hzX)
        · refine Or.inr ?_
          have hne' : f z ≠ ∞ := hwz ▸ hfA (heA hw)
          rw [← hgf z hne']
          change g (f z) ∈ e
          rw [← hwz, hgf w (hfA (heA hw))]
          exact hw
      · rintro (hz | hz)
        · refine Or.inl fun hzQ => hz ?_
          rw [← hpre]
          exact hzQ
        · exact Or.inr (mem_image_of_mem f hz)
    have hside : IsTwoSided Qᶜ (f '' e) ↔ IsTwoSided Xᶜ e := by
      constructor
      · rintro ⟨w, ⟨x, hx, rfl⟩, hw⟩
        refine ⟨x, hx, ?_⟩
        have hop₁ : IsOpen (f ⁻¹' interior (Qᶜ ∪ f '' e)) := isOpen_interior.preimage hf
        have hsub : f ⁻¹' interior (Qᶜ ∪ f '' e) ⊆ Xᶜ ∪ e := by
          rw [← hpreU]
          exact preimage_mono interior_subset
        exact interior_maximal hsub hop₁ hw
      · rintro ⟨x, hx, hxi⟩
        refine ⟨f x, mem_image_of_mem f hx, ?_⟩
        have hop₁ : IsOpen (interior (Xᶜ ∪ e) ∩ A) := isOpen_interior.inter hA.1
        have hsub : f '' (interior (Xᶜ ∪ e) ∩ A) ⊆ Qᶜ ∪ f '' e := by
          rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
          have hz' : z ∈ f ⁻¹' (Qᶜ ∪ f '' e) := by
            rw [hpreU]
            exact interior_subset hz
          exact hz'
        exact interior_maximal hsub (hopenf hop₁ inter_subset_right)
          (mem_image_of_mem f ⟨hxi, heA hx⟩)
    change (if (f '' e ∩ frontier Qᶜ).Nonempty then
      if IsTwoSided Qᶜ (f '' e) then 2 else 1 else 0) = _
    have hef' : (e ∩ frontier X).Nonempty := ⟨y, hye, hyf⟩
    simp only [hn, hside, hef', ite_true]
  · have hnot : e ∉ W.edges := by
      intro hmem'
      rw [hedges, List.mem_map] at hmem'
      obtain ⟨e₁, h₁, rfl⟩ := hmem'
      obtain ⟨c, hc, rfl⟩ := hEA' e₁ (mem_E_of_mem_edges W' h₁)
      rw [hgfe (hEA hc)] at hef
      obtain ⟨x, hx⟩ : c.Nonempty := hc.1
      exact hef ⟨x, hx, ((hBE c).mp hc).2 hx⟩
    rw [edgeCount_eq_zero hnot]
    simp only [hef, ite_false]

open Classical in
/-- **Existence of a perimeter walk**, for a set inside an open disc and with an edge on its
frontier. -/
theorem exists_perimeter_of_disc (hS : IsClosedSurface S) (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X) (hXs : IsSimplyConnectedSet X) (hne : X.Nonempty) (hA : IsOpenDisc A)
    (hXA : X ⊆ A) (hE : (Γ.interSet (frontier X)).E.Nonempty) :
    ∃ (u : S) (W : GraphWalk Γ.toGraph u u), IsPerimeterWalk Γ X W ∧ 0 < W.length ∧
      ∀ e ∈ Γ.E, edgeCount W.edges e =
        if (e ∩ frontier X).Nonempty then (if IsTwoSided Xᶜ e then 2 else 1) else 0 := by
  have hK : CompactSpace S := hS.1
  have hsph := isSphere_onePoint hA
  obtain ⟨hS', hconn'⟩ := IsSphere.isClosedSurface hsph
  have hT2' : T2Space (OnePoint A) := hS'.2.1
  have hf : Continuous (collapse A) := continuous_collapse hA.1
  obtain ⟨b, hb⟩ := hne
  let f := collapse A
  let g : OnePoint A → S := uncollapse b
  have hnS : Nonempty S := ⟨b⟩
  have hfA : ∀ {x}, x ∈ A → f x ≠ ∞ := fun {x} hx => by
    change collapse A x ≠ ∞
    rw [collapse_of_mem hx]
    exact coe_ne_infty _
  have hAf : ∀ {x}, f x ≠ ∞ → x ∈ A := fun {x} hx => by
    by_contra h
    exact hx (collapse_of_notMem h)
  have hgf : ∀ x, f x ≠ ∞ → g (f x) = x := fun x hx => by
    change uncollapse b (collapse A x) = x
    rw [collapse_of_mem (hAf hx), uncollapse_coe]
  have hfg : ∀ y, y ≠ ∞ → f (g y) = y := by
    intro y hy
    obtain ⟨a, rfl⟩ := ne_infty_iff_exists.mp hy
    change collapse A (uncollapse b (a : OnePoint A)) = a
    rw [uncollapse_coe, collapse_of_mem a.2]
  have hgc : ∀ y, y ≠ ∞ → ContinuousAt g y := by
    intro y hy
    obtain ⟨a, rfl⟩ := ne_infty_iff_exists.mp hy
    exact continuousAt_uncollapse b a
  have hinjA : InjOn f A := fun x hx y hy h => by
    rw [← hgf x (hfA hx), ← hgf y (hfA hy), h]
  have hopenf : ∀ {O : Set S}, IsOpen O → O ⊆ A → IsOpen (f '' O) := by
    intro O hO hOA
    have heq : f '' O = ((↑) : A → OnePoint A) '' (Subtype.val ⁻¹' O) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hOA hx⟩, hx, (collapse_of_mem (hOA hx)).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.1, ha, collapse_of_mem a.2⟩
    rw [heq]
    exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (hO.preimage continuous_subtype_val)
  set Q := f '' X with hQ
  have hQc : IsClosed Q := (hXc.isCompact.image hf).isClosed
  have hpre : f ⁻¹' Q = X := by
    apply subset_antisymm
    · rintro x ⟨y, hy, hxy⟩
      have hne' : f x ≠ ∞ := hxy ▸ hfA (hXA hy)
      rw [← hgf x hne', ← hxy, hgf y (hfA (hXA hy))]
      exact hy
    · exact fun x hx => mem_image_of_mem f hx
  have hinf : (∞ : OnePoint A) ∉ Q := by
    rintro ⟨x, hx, hxe⟩
    exact hfA (hXA hx) hxe
  have hfr : frontier Q = f '' frontier X := by
    rw [hQc.frontier_eq, hXc.frontier_eq]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hint⟩
      refine ⟨x, ⟨hx, fun h => hint ?_⟩, rfl⟩
      exact interior_maximal (image_mono interior_subset) (hopenf isOpen_interior
        (interior_subset.trans hXA)) (mem_image_of_mem f h)
    · rintro ⟨x, ⟨hx, hint⟩, rfl⟩
      refine ⟨mem_image_of_mem f hx, fun h => hint ?_⟩
      have hop : IsOpen (f ⁻¹' interior Q) := isOpen_interior.preimage hf
      have hsub : f ⁻¹' interior Q ⊆ X := by
        rw [← hpre]
        exact preimage_mono interior_subset
      exact interior_maximal hsub hop h
  let B := Γ.interSet (frontier X)
  have hBs : B.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hBU : B.U = frontier X := frontier_interSet hS hXc hXn
  have hfrA : frontier X ⊆ A := hXc.frontier_subset.trans hXA
  have hBA : B.U ⊆ A := hBU ▸ hfrA
  obtain ⟨D, hDU, hDV, hDE, hcl⟩ := exists_transport B hf (hinjA.mono hBA)
  have hDU' : D.U = frontier Q := by rw [hDU, hBU, hfr]
  have hdisc : ∀ F, IsOArc F → F ⊆ D.U → ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ Q ∧ discBd Δ = F := by
    exact drawing_circle_bounds_subdisc (S := S) (X := X) (A := A) hS hXs hXA hf g hfA hgf hfg hgc
      hinjA hQc hinf D hDU'
  have hQp : IsPreconnected Q := (hXs.1.image' hf.continuousOn).isConnected.isPreconnected
  have hQne : Q.Nonempty := ⟨f b, mem_image_of_mem f hb⟩
  have hQu : Q ≠ univ := fun h => hinf (h ▸ mem_univ _)
  obtain ⟨hreg, -, hT⟩ := sphere_outside hS' hsph hQc hQp hQne hQu hDU' hdisc
  have hEne : D.E.Nonempty := by
    obtain ⟨e, he⟩ := hE
    exact ⟨f '' e, hDE ▸ mem_image_of_mem _ he⟩
  obtain ⟨u', W', h', hpos, hinj, hmem, hrng, hop, hrun, hcount⟩ :=
    exists_region_walk hS' hsph hT hEne hreg
  rw [frontier_compl] at hrng
  rw [compl_compl] at hop
  have hbot : ∀ z, h' (z, 0) ∈ Q := fun z => hQc.frontier_subset (hrng ▸ mem_range_self z)
  obtain ⟨h, hinjh, hoffh, hboth, hoph⟩ := pull_collar hf hgc hgf hfg hinf h' hinj
    (fun p hp hq => hmem p hp hq) hbot hop
  rw [hpre] at hoph
  -- The edges and vertices of `D` come from those of `B`.
  have hEA : ∀ {e₀ : Set S}, e₀ ∈ B.E → e₀ ⊆ A := fun {e₀} he x hx => hBA (he.2.1 hx).1
  have hgfe : ∀ {e₀ : Set S}, e₀ ⊆ A → image g (f '' e₀) = e₀ := by
    intro e₀ he
    rw [image_image]
    calc (fun x => g (f x)) '' e₀ = id '' e₀ := image_congr fun x hx => hgf x (hfA (he hx))
      _ = e₀ := image_id e₀
  have hEA' : ∀ e ∈ D.E, ∃ e₀ ∈ B.E, e = f '' e₀ := by
    intro e he
    rw [hDE] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    exact ⟨e₀, he₀, rfl⟩
  have hlink : ∀ e x y, D.toGraph.IsLink e x y → Γ.toGraph.IsLink (image g e) (g x) (g y) := by
    exact map_link_of_drawing_embedding (S := S) (Γ := Γ) (A := A) g hfA hgf hinjA B hBs hBA D hDV
      hcl hEA hgfe hEA'
  have hvert : ∀ v ∈ D.V, g v ∈ Γ.V := by
    intro v hv
    rw [hDV] at hv
    obtain ⟨x₀, hx₀, rfl⟩ := hv
    rw [hgf x₀ (hfA (hBA (B.V_subset_U hx₀)))]
    exact hBs.1 hx₀
  have hginj : ∀ e ∈ D.E, InjOn g e := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := hEA' e he
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h₁
    rw [hgf x (hfA (hEA he₀ hx)), hgf y (hfA (hEA he₀ hy))] at h₁
    rw [h₁]
  obtain ⟨W, hW, hedges⟩ := walk_pull hlink hvert hginj (fun _ _ => rfl) W' hrun
  have hcurve : g ∘ collarCurve h' = collarCurve h := by
    funext t
    exact (hboth _).symm
  rw [hcurve] at hW
  refine ⟨_, W, ⟨h, hinjh, fun p hp hx => hoffh p hp (mem_image_of_mem f hx), ?_, hoph,
    Or.inr ⟨?_, hW⟩⟩, ?_, ?_⟩
  · rw [subBd_eq_frontier]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      have hzm : h' (z, 0) ∈ f '' frontier X := hfr ▸ hrng ▸ mem_range_self z
      obtain ⟨w, hw, hwe⟩ := hzm
      change h (z, 0) ∈ _
      rw [hboth, ← hwe, hgf w (hfA (hfrA hw))]
      exact hw
    · intro hx
      have hxm : f x ∈ range fun z : Circle => h' (z, 0) := hrng ▸ hfr ▸ mem_image_of_mem f hx
      obtain ⟨z, hz⟩ := hxm
      refine ⟨z, ?_⟩
      change h (z, 0) = x
      rw [hboth]
      have hz' : h' (z, 0) = f x := hz
      rw [hz', hgf x (hfA (hfrA hx))]
  · simpa [GraphWalk.length, hedges] using hpos
  · simpa [GraphWalk.length, hedges] using hpos
  · exact perimeter_edge_count_pull (S := S) (Γ := Γ) (X := X) (A := A) hS hXc hXn hA hf g hfA hgf
      hopenf hpre hfr D hDE u' W' hcount hEA hgfe hEA' W hedges
end GraphMinor.GM11
