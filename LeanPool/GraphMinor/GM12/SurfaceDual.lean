/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualFan

/-!
# A surface dual from a radial drawing

Graph Minors XII, (7.5), uses this step: "Let $\Gamma_1$ be a drawing in $\Sigma$ dual to $\Gamma$,
in the usual sense
of surface duals". The text gives no proof that the dual has a common radial drawing with `Γ`. This
file gives one (`exists_surfaceDual_of_radial`).

Each edge `e` of `Γ` has two regions of `Γ ∪ K` beside it. Choose a point `m e` of `e`. In each of
the
two regions, take a line from `m e` to the vertex of `K` on that region's frontier that is not in
`Γ`.
The two lines form the dual edge, which is a loop if they end at the same vertex.

The drawing `K ∪ N`, where `N` is made of the lines, is a radial drawing of `Γ` with the points `m
e` as
new vertices (`SurfaceDualSplit.lean`). So the regions of the dual are the stars of
`SurfaceDualStar.lean`, and each has one vertex of `Γ`. Then `K` satisfies conditions (i)-(iv) for
the
dual, with the roles of the two kinds of vertices swapped. Maximality is by count.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

variable [T2Space S] [ConnectedSpace S]

/-- See the module docstring. The drawing `Γ₁` here is any drawing made from the lines of `hL`. -/
theorem IsDualLines.isRadial_dual {Γ K D : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ)
  K}
    {A B : Set S → Set S} {m x y : Set S → S} {f : Set S × Bool → Set S} {h : Set S × Bool → S}
    {ℓ : Set S × Bool → I → S} (hL : IsDualLines hrad D A B m x y f h ℓ) (hS : IsClosedSurface S)
    (hmax : RadMax (PaintingOrDrawing.drawing Γ) K) (hE : Γ.E.Nonempty) {Γ₁ : Drawing S}
    (h₁U : Γ₁.U = (K.V \ Γ.V) ∪ ⋃ e ∈ Γ.E, (range (ℓ (e, true)) ∪ range (ℓ (e, false))))
    (h₁V : Γ₁.V = K.V \ Γ.V)
    (h₁E : Γ₁.E = (fun e => (range (ℓ (e, true)) ∪ range (ℓ (e, false))) \
      {h (e, true), h (e, false)}) '' Γ.E) :
    (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin : (K.V \ Γ.V).Finite := K.finite_V.subset sdiff_subset
  obtain ⟨N, hNU, hNV, hNE⟩ := hL.exists_lineDrawing (hfin.union (Γ.finite_edges.image _))
  have hKN := hL.glue_compat hNU hNV
  have hrad₁ := hL.preRad_glue hNU hNV hNE hKN hS hmax hE
  have hmax₁ := hL.radMax_glue hNU hNV hNE hKN hS hmax hE
  have hDE : D.E.Nonempty := by
    obtain ⟨e, he⟩ := hE
    exact ⟨_, (hL.split e he).1⟩
  have hsub : Γ.V ⊆ D.V := fun z hz => hL.V_eq ▸ Or.inl hz
  have hmΓ : ∀ {e}, e ∈ Γ.E → m e ∉ Γ.V := fun he => edge_notMem_V he (hL.m_mem he)
  have hX : IsSideSplit D (K.glue N hKN) N Γ.V := by
    refine ⟨hsub, ?_, ?_, ?_, ?_, ?_⟩
    · apply subset_antisymm
      · intro z hz
        have hz' := hz
        rw [hNV] at hz'
        rcases hz' with hz' | ⟨e, he, rfl⟩
        · exact ⟨Or.inl hz'.1, hz'.2⟩
        · exact ⟨Or.inr hz, hmΓ he⟩
      · rintro z ⟨hz | hz, hzΓ⟩
        · exact hNV ▸ Or.inl ⟨hz, hzΓ⟩
        · exact hz
    · intro g hg
      rw [Drawing.glue_E]
      exact Or.inr hg
    · intro g hg
      obtain ⟨e, he, rfl | rfl⟩ := hL.all g hg
      · obtain ⟨-, -, -, -, -, -, -, hx, -, -, hcA, -⟩ := hL.split e he
        exact ⟨x e, hx, m e, ⟨hL.m_mem_D he, hmΓ he⟩, hcA⟩
      · obtain ⟨-, -, -, -, -, -, -, -, hy, -, -, hcB⟩ := hL.split e he
        exact ⟨y e, hy, m e, ⟨hL.m_mem_D he, hmΓ he⟩, by rw [hcB, pair_comm]⟩
    · intro g hg hgN
      rw [Drawing.glue_E] at hg
      have hgK : g ∈ K.E := hg.resolve_right hgN
      obtain ⟨v, hv, w, -, hcap⟩ := hrad.2.2.2.2.2.1 g hgK
      have : v ∈ closure g ∩ K.V := by rw [hcap]; simp
      exact ⟨v, hv, this.1⟩
    · intro g hg
      obtain ⟨e, he, b, -, hcl⟩ := hL.N_edge hNE hg
      rw [hcl]
      refine disjoint_left.mpr fun z hz hzV => ?_
      rcases hL.mem_line he b hz with h₁ | h₁ | h₁
      · exact (hL.face_off he b h₁).1 (Γ.V_subset_U hzV)
      · exact hmΓ he (h₁ ▸ hzV)
      · exact hL.hub_off he b (h₁ ▸ Γ.V_subset_U hzV)
  have hU : Γ₁.U = N.U := by
    rw [h₁U, hNU]
    apply subset_antisymm
    · rintro z (hz | hz)
      · exact Or.inl (Or.inl hz)
      · obtain ⟨e, he, hz | hz⟩ := mem_iUnion₂.mp hz
        · exact Or.inr (mem_biUnion (show (e, true) ∈ Γ.E ×ˢ (univ : Set Bool) from ⟨he,
            mem_univ _⟩) hz)
        · exact Or.inr (mem_biUnion (show (e, false) ∈ Γ.E ×ˢ (univ : Set Bool) from ⟨he,
            mem_univ _⟩) hz)
    · rintro z ((hz | ⟨e, he, rfl⟩) | hz)
      · exact Or.inl hz
      · exact Or.inr (mem_biUnion he (Or.inl (line_left_mem (hL.isLine he true) |>
          (hL.zero e he true ▸ ·))))
      · obtain ⟨⟨e, b⟩, ⟨he, -⟩, hz⟩ := mem_iUnion₂.mp hz
        refine Or.inr (mem_biUnion he ?_)
        cases b
        · exact Or.inr hz
        · exact Or.inl hz
  have hR : Γ₁.R = N.R := by
    simp only [Drawing.R, hU]
  let H := radialUnion hrad₁
  have hsplit₁ : ∀ {v}, v ∈ Γ.V → star H v ∈ N.R := fun hv => hX.star_mem_R hrad₁ hS hmax₁ hDE hv
  have hsplit₂ : ∀ {r}, r ∈ N.R → ∃ v ∈ Γ.V, r = star H v := fun hr =>
    hX.exists_star_eq hrad₁ hS hmax₁ hDE hr
  have htwo : (PaintingOrDrawing.drawing Γ₁).IsTwoCell := by
    refine ⟨inferInstance, fun r hr => ?_⟩
    have hr' : r ∈ N.R := hR ▸ hr
    obtain ⟨v, hv, rfl⟩ := hsplit₂ hr'
    exact hX.star_isOpenDisc hrad₁ hS hmax₁ hDE hv
  have hhubK : ∀ {z}, z ∈ K.V → z ∉ Γ.V → z ∈ N.V := fun h₁ h₂ => hNV ▸ Or.inl ⟨h₁, h₂⟩
  have huniq : ∀ {v w}, v ∈ Γ.V → w ∈ star H v → w ∈ K.V → w = v := by
    intro v w hv hw hwK
    by_cases hwΓ : w ∈ Γ.V
    · exact hX.star_eq hrad₁ hS hmax₁ hDE hwΓ hv (mem_star_self _ _) hw
    · exact absurd (N.V_subset_U (hhubK hwK hwΓ)) (disjoint_left.mp (hX.star_off hrad₁ hv) hw)
  have hpre : (PaintingOrDrawing.drawing Γ₁).IsPreRadialDrawing K := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Γ₁.U ∩ K.U = Γ₁.V
      rw [hU, h₁V]
      apply subset_antisymm
      · rintro z ⟨hz, hz'⟩
        have hzV := (hKN ⟨hz', hz⟩).2
        rw [hNV] at hzV
        rcases hzV with hzV | ⟨e, he, rfl⟩
        · exact hzV
        · exact absurd hz' (hL.m_K he)
      · intro z hz
        exact ⟨N.V_subset_U (hNV ▸ Or.inl hz), K.V_subset_U hz.1⟩
    · change Γ₁.V ⊆ K.V
      rw [h₁V]
      exact sdiff_subset
    · intro r hr
      have hr' : r ∈ N.R := hR ▸ (show r ∈ Γ₁.R from hr)
      obtain ⟨v, hv, rfl⟩ := hsplit₂ hr'
      exact ⟨v, ⟨mem_star_self _ _, radial_V hrad hv⟩, fun w hw => huniq hv hw.1 hw.2⟩
    · rintro w ⟨hw, hwn⟩
      have hwΓ : w ∈ Γ.V := by
        by_contra hn
        exact hwn (show w ∈ Γ₁.V from h₁V ▸ ⟨hw, hn⟩)
      exact ⟨star H w, (show star H w ∈ Γ₁.R from hR.symm ▸ hsplit₁ hwΓ), mem_star_self _ _⟩
    · intro g hg
      obtain ⟨v, hv, w, hw, hcap⟩ := hrad.2.2.2.2.2.1 g hg
      refine ⟨w, (show w ∈ Γ₁.V from h₁V ▸ hw), v, ⟨radial_V hrad hv, ?_⟩, by rw [hcap, pair_comm]⟩
      intro hv'
      have : v ∈ K.V \ Γ.V := h₁V ▸ hv'
      exact this.2 hv
    · intro g hg g' hg' _ u hu r hr w hw hc hc' ⟨Δ, hΔ, hsubΔ, hb⟩
      have hr' : r ∈ N.R := hR ▸ (show r ∈ Γ₁.R from hr)
      obtain ⟨v, hv, rfl⟩ := hsplit₂ hr'
      have huK : u ∈ K.V \ Γ.V := h₁V ▸ (show u ∈ Γ₁.V from hu)
      have hdb : discBd Δ = closure g ∪ closure g' := by
        rw [← hb, subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hΔ]
      have hgH : ∀ {g}, g ∈ K.E → closure g ⊆ H.U := fun hg z hz =>
        Or.inr (Or.inl (K.closure_subset_U hg hz))
      refine hX.no_disc_in_star hrad₁ hS hmax₁ hDE hv hΔ hsubΔ (fun h' => ?_)
        (Or.inr (Or.inl (K.V_subset_U huK.1))) ?_
      · rw [hL.V_eq] at h'
        rcases h' with h' | ⟨e, he, rfl⟩
        · exact huK.2 h'
        · exact hL.m_K he (K.V_subset_U huK.1)
      · rw [hdb]
        exact union_subset (hgH hg) (hgH hg')
  have hallΓ₁ : ∀ z ∈ Γ₁.V, ∃ g ∈ Γ₁.E, z ∈ closure g := by
    intro z hz
    rw [h₁V] at hz
    obtain ⟨e, he, b, rfl⟩ := hL.exists_hub hz.1 hz.2 hmax hS hE
    refine ⟨_, h₁E ▸ mem_image_of_mem _ he, ?_⟩
    have hsubL : range (ℓ (e, b)) \ {m e, h (e, b)} ⊆
        (range (ℓ (e, true)) ∪ range (ℓ (e, false))) \ {h (e, true), h (e, false)} := by
      rintro w ⟨hw, hwn⟩
      have hwf : w ∈ f (e, b) := by
        rcases hL.mem_line he b hw with h₁ | h₁ | h₁
        · exact h₁
        · exact absurd (Or.inl h₁) hwn
        · exact absurd (Or.inr h₁) hwn
      refine ⟨?_, ?_⟩
      · cases b
        · exact Or.inr hw
        · exact Or.inl hw
      · rintro (h₁ | h₁)
        · exact (hL.face_off he b hwf).2 (h₁ ▸ hL.hub_K he true)
        · exact (hL.face_off he b hwf).2 (h₁ ▸ hL.hub_K he false)
    have hcl := closure_sdiff_pair (hL.isLine he b)
    refine closure_mono hsubL ?_
    rw [hcl]
    exact line_right_mem (hL.isLine he b)
  have hcard : 2 * Γ₁.E.ncard ≤ K.E.ncard := by
    have h₁ := two_mul_le_ncard_spokes hrad hS hmax hE
    have h₂ : Γ₁.E.ncard ≤ Γ.E.ncard := by
      rw [h₁E]
      exact ncard_image_le Γ.finite_edges
    omega
  exact ⟨htwo, hpre, radMax_of_card hS htwo hpre hallΓ₁ hcard⟩

/-- `Γ₁` is a dual of `Γ` made from lines through the faces of `Γ ∪ K`, as in `IsDualLines`. So each
edge of `Γ` meets `Γ₁` in one point, where it crosses its dual edge. -/
def IsLineDual (Γ K Γ₁ : Drawing S) : Prop :=
  ∃ (hrad : PreRad (PaintingOrDrawing.drawing Γ) K) (D : Drawing S) (A B : Set S → Set S)
    (m x y : Set S → S) (f : Set S × Bool → Set S) (h : Set S × Bool → S)
    (ℓ : Set S × Bool → I → S), IsDualLines hrad D A B m x y f h ℓ ∧
    Γ₁.U = (K.V \ Γ.V) ∪ ⋃ e ∈ Γ.E, (range (ℓ (e, true)) ∪ range (ℓ (e, false))) ∧
    Γ₁.V = K.V \ Γ.V ∧
    Γ₁.E = (fun e => (range (ℓ (e, true)) ∪ range (ℓ (e, false))) \
      {h (e, true), h (e, false)}) '' Γ.E

/-- `exists_surfaceDual_of_radial`, with the dual made from lines. -/
theorem exists_lineDual_of_radial (hS : IsClosedSurface S) {Γ K : Drawing S} (hE : Γ.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) :
    ∃ Γ₁ : Drawing S, (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K ∧ IsLineDual Γ K Γ₁ := by
  have hrad : PreRad (PaintingOrDrawing.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  have hmax : RadMax (PaintingOrDrawing.drawing Γ) K := hK.2.2
  obtain ⟨D, A, B, m, x, y, f, h, ℓ, hL⟩ := exists_dualLines hrad hS hmax hE
  obtain ⟨Γ₁, h₁U, h₁V, h₁E⟩ := hL.exists_dual (K.finite_V.subset sdiff_subset)
  exact ⟨Γ₁, hL.isRadial_dual hS hmax hE h₁U h₁V h₁E,
    hrad, D, A, B, m, x, y, f, h, ℓ, hL, h₁U, h₁V, h₁E⟩

omit [T2Space S] [ConnectedSpace S] in
/-- See the module docstring. -/
theorem exists_surfaceDual_of_radial (hS : IsClosedSurface S) {Γ K : Drawing S} (hE : Γ.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) :
    ∃ Γ₁ : Drawing S, (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K ∧ Γ₁.V = K.V \ Γ.V := by
  have : T2Space S := hS.2.1
  have : ConnectedSpace S := hK.1.1
  obtain ⟨Γ₁, h₁, -, -, -, -, -, -, -, -, -, -, -, -, h₁V, -⟩ := exists_lineDual_of_radial hS hE hK
  exact ⟨Γ₁, h₁, h₁V⟩

end GraphMinor.GM12
