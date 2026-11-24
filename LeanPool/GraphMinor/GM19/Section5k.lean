/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5j

/-!
# Graph Minors XIX, proof of (5.4): one fragment

We fix a linear inflation of the pull-back of `Γ` in the pull-back of `Γ'`, on one fragment, that
respects the frame
of the fragment. We study what it does to the edges and vertices that come from `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]


/-- A step of a walk maps to a step or to one vertex, so reachability maps too. -/
theorem reachable_map {A B : Type*} {G : SimpleGraph A} {G' : SimpleGraph B} (m : A → B)
    (h : ∀ a b, G.Adj a b → m a = m b ∨ G'.Adj (m a) (m b)) {a b : A} (hr : G.Reachable a b) :
    G'.Reachable (m a) (m b) := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    rcases h _ _ hadj with heq | hadj'
    · rw [heq]
      exact ih
    · exact hadj'.reachable.trans ih

variable {Φ : Frame S} {Γ Γ' : Painting S} {K : Drawing S} {ψ : S₁ → S}

/-- The edges of the pull-back. -/
theorem FrameData.mem_paint_E [Nonempty S₁] (D : FrameData Φ Γ K ψ) (flip : Set S₁
  → Bool) {p : Set S₁} :
    p ∈ (D.paint flip).E ↔ p ∈ pullPieces Γ K ψ := by
  change p ∈ arcComponentsIn (pullU Γ ψ \ pullV Γ K ψ) ↔ _
  rw [D.pull.arcComponentsIn_eq]

/-- `tilde` of the image of a boundary arc over `bd(Σ)`. -/
theorem PullData.tilde_image_arc (d : PullData Γ K ψ) {e₁ : Set S₁} (he₁ : e₁ ∈ arcComponentsIn
  (bd S₁ \ pullV Γ K ψ)) :
    tilde (ψ '' e₁) = ψ '' tilde e₁ := by
  have hc := d.frag.continuous_ψ
  rw [tilde, d.frag.isClosedMap.closure_image_eq_of_continuous hc]
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    exact ⟨w, ⟨hw, fun hwe ↦ hz (mem_image_of_mem ψ hwe)⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨mem_image_of_mem ψ hw.1, ?_⟩
    rintro ⟨w', hw', hww⟩
    exact (he₁.2.1 hw').2 (by
      change ψ w' ∈ Γ.V ∪ K.V
      rw [hww]
      exact d.tilde_subset he₁ hw)

/-- A linear inflation on a fragment, with the facts that the proof of (5.4) needs of it. -/
structure FragInflation [Nonempty S₁] (D : FrameData Φ Γ K ψ) (D' : FrameData Φ Γ' K ψ)
  (hF : IsFeature Φ K)
    (flip : Set S₁ → Bool) (σv : S₁ → Set S₁) (σe : Set S₁ → Set S₁) : Prop where
  inflation : IsLinearInflation (D.paint flip) (D'.paint flip) σv σe
  respects : RespectsFrame (D.frame hF flip) (D.paint flip) σe
  flip_spec : IsPaperFlip Φ K ψ D.pull.frag.isSurface flip
  fits : (D.paint flip).Fits (D.frame hF flip)
  fits' : (D'.paint flip).Fits (D.frame hF flip)
  same_V : ∀ v ∈ K.V, v ∈ Γ.V ↔ v ∈ Γ'.V

namespace FragInflation

variable [Nonempty S₁] {D : FrameData Φ Γ K ψ} {D' : FrameData Φ Γ' K ψ} {hF : IsFeature Φ K}
  {flip : Set S₁ → Bool} {σv : S₁ → Set S₁} {σe : Set S₁ → Set S₁} (G : FragInflation D D' hF flip
    σv σe)
include G

/-- A vertex of the frame lies in its own set. -/
theorem mem_frame {x : S₁} (hx : x ∈ pullFrameV Φ K ψ) : x ∈ σv x :=
  mem_σv_of_frame D.pull.frag.isSurface G.fits G.fits' G.inflation.toIsInflation G.respects hx

/-- A vertex of the frame in the set of `y` is `y`. -/
theorem eq_of_mem_frame {x y : S₁} (hx : x ∈ pullFrameV Φ K ψ) (hy : y ∈ pullV Γ K ψ)
  (hxy : x ∈ σv y) : x = y := by
  by_contra hne
  exact disjoint_left.mp (G.inflation.vertex_disjoint x (D.pullFrameV_subset hx) y hy hne)
    (G.mem_frame hx) hxy

/-- The image under `σ'` of a lifted edge is a lifted edge. -/
theorem sigma_lift {e : Set S} (he : e ∈ Γ.E) (hb : ¬ Painting.IsBorder e) (hne :
  (ψ ⁻¹' e).Nonempty) :
    ∃ e' ∈ Γ'.E, ¬ Painting.IsBorder e' ∧ σe (ψ ⁻¹' e) = ψ ⁻¹' e' ∧ (ψ ⁻¹' e').Nonempty ∧
      (tilde e').ncard = (tilde e).ncard := by
  have hE : ψ ⁻¹' e ∈ (D.paint flip).E := (D.mem_paint_E flip).mpr (Or.inr ⟨e, he, hb, hne, rfl⟩)
  have hsub := D.pull.subset_R he hb hne
  have hfE := G.inflation.edge_mem _ hE
  have hnb : ¬ Painting.IsBorder (σe (ψ ⁻¹' e)) := by
    rintro ⟨x, hx, hxb⟩
    obtain ⟨Θ, hΘ, hxΘ⟩ := sUnion_cuffs (S := S₁) ▸ hxb
    obtain ⟨y, hy, hyΘ⟩ := (G.inflation.borders_iff _ hE Θ hΘ).mpr ⟨x, hx, hxΘ⟩
    exact D.pull.preimage_subset_int hsub hy (cuff_subset_bd ⟨Θ, hΘ⟩ hyΘ)
  rcases (D'.mem_paint_E flip).mp hfE with hp | ⟨e', he', hb', hne', hfeq⟩
  · obtain ⟨x, hx⟩ := hp.1
    exact absurd ⟨x, hx, (hp.2.1 hx).1⟩ hnb
  · have hne'' : (ψ ⁻¹' e').Nonempty := hfeq ▸ hne'
    refine ⟨e', he', hb', hfeq, hne'', ?_⟩
    have hsize := G.inflation.edge_size _ hE
    rw [hfeq] at hsize
    have h₁ := D'.pull.ncard_tilde he' (D'.pull.subset_R he' hb' hne'')
    have h₂ := D.pull.ncard_tilde he hsub
    rw [← h₁, ← h₂]
    exact hsize

/-- The image under `σ'` of a border edge over `bd(Σ)` is a border edge in the same side. -/
theorem sigma_border {e₁ : Set S₁} (he₁ : e₁ ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) {x₀ : S₁}
  (hx₀ : x₀ ∈ e₁)
    (hb₀ : ψ x₀ ∈ bd S) :
    σe e₁ ∈ arcComponentsIn (bd S₁ \ pullV Γ' K ψ) ∧ ∃ s ∈ Φ.sides, ψ '' e₁ ⊆ s ∧ ψ '' σe e₁ ⊆ s
      := by
  have hE : e₁ ∈ (D.paint flip).E := (D.mem_paint_E flip).mpr (Or.inl he₁)
  have hbb : Painting.IsBorder e₁ := ⟨x₀, hx₀, (he₁.2.1 hx₀).1⟩
  obtain ⟨R, hR, hes⟩ := exists_arcComp_superset he₁.2.2.1 (F := bd S₁ \ pullFrameV Φ K ψ)
    (fun x hx ↦ ⟨(he₁.2.1 hx).1, fun h ↦ (he₁.2.1 hx).2 (D.pullFrameV_subset h)⟩)
  obtain ⟨s, hs, hsub⟩ := D.exists_side_of_bd hR (hes hx₀) hb₀
  have hfR : σe e₁ ⊆ R := ((G.respects e₁ hE hbb).2 R hR).mp hes
  have hfE := G.inflation.edge_mem _ hE
  rcases (D'.mem_paint_E flip).mp hfE with hp | ⟨e', he', hb', hne', hfeq⟩
  · exact ⟨hp, s, hs, (image_mono hes).trans hsub, (image_mono hfR).trans hsub⟩
  · exfalso
    obtain ⟨x, hxf⟩ := hne'
    have hx : x ∈ ψ ⁻¹' e' := hfeq ▸ hxf
    exact D'.pull.preimage_subset_int (D'.pull.subset_R he' hb' ⟨x, hx⟩) hx (hR.2.1 (hfR hxf)).1

/-- All that an edge of `Γ` with a lift to the fragment needs. -/
theorem edge_main {e : Set S} (he : e ∈ Γ.E) (hne : (ψ ⁻¹' e).Nonempty) :
    ψ '' (ψ ⁻¹' e) = e ∧ ψ ⁻¹' e ∈ (D.paint flip).E ∧ ψ '' σe (ψ ⁻¹' e) ∈ Γ'.E ∧
      ψ ⁻¹' (ψ '' σe (ψ ⁻¹' e)) = σe (ψ ⁻¹' e) ∧ (tilde (ψ '' σe (ψ ⁻¹' e))).ncard =
        (tilde e).ncard ∧
      ((D'.paint flip).γ (σe (ψ ⁻¹' e))).map ψ = Γ'.γ (ψ '' σe (ψ ⁻¹' e)) ∧
      ((D.paint flip).γ (ψ ⁻¹' e)).map ψ = Γ.γ e ∧
      (Painting.IsBorder e → ∃ s ∈ Φ.sides, e ⊆ s ∧ ψ '' σe (ψ ⁻¹' e) ⊆ s ∧ Painting.IsBorder
        (ψ '' σe (ψ ⁻¹' e))) ∧
      (¬ Painting.IsBorder e → ¬ Painting.IsBorder (ψ '' σe (ψ ⁻¹' e))) := by
  by_cases hb : Painting.IsBorder e
  · have hbe : e ⊆ bd S := (Γ.border_edge e he hb).2
    obtain ⟨x, hx⟩ := hne
    obtain ⟨he₁, hsur⟩ := D.pull.preimage_border_edge he hbe hx
    have hE : ψ ⁻¹' e ∈ (D.paint flip).E := (D.mem_paint_E flip).mpr (Or.inl he₁)
    obtain ⟨hf, s, hs, hs₁, hs₂⟩ := G.sigma_border he₁ hx (hbe hx)
    obtain ⟨y, hy⟩ := hf.1
    have hyb : ψ y ∈ bd S := (hs.2.1 (hs₂ (mem_image_of_mem ψ hy))).1
    obtain ⟨hE', hpre⟩ := D'.pull.image_border_edge hf hy hyb
    have hbE' : Painting.IsBorder (ψ '' σe (ψ ⁻¹' e)) := ⟨ψ y, mem_image_of_mem ψ hy, hyb⟩
    refine ⟨hsur, hE, hE', hpre, ?_, ?_, ?_,
      fun _ ↦ ⟨s, hs, hsur ▸ hs₁, hs₂, hbE'⟩, fun h ↦ absurd hb h⟩
    · rw [(Γ'.border_edge _ hE' hbE').1, (Γ.border_edge e he hb).1]
    · exact D'.map_march_border G.flip_spec hf hy hyb
    · have := D.map_march_border G.flip_spec he₁ hx (hbe hx)
      rwa [hsur] at this
  · obtain ⟨e', he', hb', hfeq, hne', hsize⟩ := G.sigma_lift he hb hne
    have hsub := D.pull.subset_R he hb hne
    have hsub' := D'.pull.subset_R he' hb' hne'
    have hsur' : ψ '' (ψ ⁻¹' e') = e' := image_preimage_eq_of_subset (hsub'.trans
      (image_subset_range _ _))
    rw [hfeq, hsur']
    exact ⟨image_preimage_eq_of_subset (hsub.trans (image_subset_range _ _)),
      (D.mem_paint_E flip).mpr (Or.inr ⟨e, he, hb, hne, rfl⟩), he', rfl, hsize,
      D'.map_march_lift he' hb' hne', D.map_march_lift he hb hne, fun h ↦ absurd h hb, fun _ ↦ hb'⟩

omit G in
/-- Three kinds of edge of the pull-back of `Γ'`, as seen from an end. -/
theorem edge_ends {a : S₁} {e : Set S₁} (he : e ∈ (D'.paint flip).E) (ha : a ∈ tilde e) :
    ψ a ∈ Γ'.V ∨ a ∈ pullFrameV Φ K ψ := by
  have hV : a ∈ pullV Γ' K ψ := by
    have := (D'.paint flip).tilde_subset_V he ha
    exact this
  rcases hV with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

omit G in
/-- The two ends of an edge of the pull-back of `Γ'` map to the ends of an edge of `Γ'`, or lie both
in the frame. In the
second case the edge lies over `U(K)`. -/
theorem ends_image {a b : S₁} {e : Set S₁} (he : e ∈ (D'.paint flip).E) (hae : a ∈ tilde e)
  (hbe : b ∈ tilde e) :
    (∃ e' ∈ Γ'.E, ψ a ∈ tilde e' ∧ ψ b ∈ tilde e') ∨ (a ∈ pullFrameV Φ K ψ ∧ b ∈ pullFrameV Φ K ψ)
      := by
  rcases (D'.mem_paint_E flip).mp he with hp | ⟨e', he', hb', hne', rfl⟩
  · by_cases hover : ∃ x₀ ∈ e, ψ x₀ ∈ bd S
    · obtain ⟨x₀, hx₀, hb₀⟩ := hover
      refine Or.inl ⟨ψ '' e, (D'.pull.image_border_edge hp hx₀ hb₀).1, ?_, ?_⟩
      · rw [D'.pull.tilde_image_arc hp]
        exact mem_image_of_mem ψ hae
      · rw [D'.pull.tilde_image_arc hp]
        exact mem_image_of_mem ψ hbe
    · -- `e` lies over `U(K)`, so its two ends are in the frame
      push Not at hover
      have hsubK : ψ '' e ⊆ K.U := by
        rintro _ ⟨x, hx, rfl⟩
        exact (D'.pull.frag.maps_bd (mem_image_of_mem ψ (hp.2.1 hx).1)).resolve_left (hover x hx)
      have hc := D'.pull.frag.continuous_ψ
      have hclK : ∀ {w}, w ∈ tilde e → w ∈ pullFrameV Φ K ψ := by
        intro w hw
        have hw₁ : ψ w ∈ K.U := closure_minimal hsubK K.isClosed_U
          (image_closure_subset_closure_image hc (mem_image_of_mem ψ hw.1))
        have hwV := D'.pull.tilde_subset hp hw
        rcases hwV with h | h
        · exact Or.inr (D'.pull.inter ⟨Γ'.V_subset h, hw₁⟩).2
        · exact Or.inr h
      exact Or.inr ⟨hclK hae, hclK hbe⟩
  · have hsub' := D'.pull.subset_R he' hb' hne'
    have himg := D'.pull.frag.image_tilde_preimage hsub'
    exact Or.inl ⟨e', he', himg ▸ mem_image_of_mem ψ hae, himg ▸ mem_image_of_mem ψ hbe⟩

/-- A step in `sk(Γ₂)` inside the set of a vertex maps to a step of `sk(Γ')`, or to one vertex. An
edge over `U(K)` has
its two ends in the frame, so it is not inside the set of a vertex. -/
theorem sk_step {y : S₁} (hy : y ∈ pullV Γ K ψ) {a b : S₁} (ha : a ∈ σv y) (hb : b ∈ σv y)
    (hVa : ψ a ∈ Γ'.V) (hVb : ψ b ∈ Γ'.V) (hadj : (D'.paint flip).skAdj.Adj a b) :
    ψ a = ψ b ∨ Γ'.skAdj.Adj (ψ a) (ψ b) := by
  obtain ⟨hne, -, -, e, he, hae, hbe⟩ := hadj
  by_cases hab : ψ a = ψ b
  · exact Or.inl hab
  refine Or.inr ⟨hab, hVa, hVb, ?_⟩
  rcases ends_image he hae hbe with h | ⟨h₁, h₂⟩
  · exact h
  · exact absurd ((G.eq_of_mem_frame h₁ hy ha).trans (G.eq_of_mem_frame h₂ hy hb).symm) hne

/-- If a vertex `y` of the frame does not lie over a vertex of `Γ`, then its set is `{y}`. It lies
over a point that is
no vertex of `Γ'`, so each edge at `y` lies over `U(K)`, and its other end is another frame vertex.
-/
theorem eq_of_not_V {y a : S₁} (hy : y ∈ pullV Γ K ψ) (hyF : y ∈ pullFrameV Φ K ψ)
  (hyV : ψ y ∉ Γ.V) (ha : a ∈ σv y) :
    a = y := by
  have hyK : ψ y ∈ K.V := hyF.resolve_left fun h ↦ hyV (D.fits.V_subset h)
  have hyy := G.mem_frame hyF
  obtain ⟨w⟩ := G.inflation.vertex_connected y hy ⟨y, hyy⟩ ⟨a, ha⟩
  cases w with
  | nil => rfl
  | @cons _ c _ hadj _ =>
    exfalso
    obtain ⟨hne, -, -, e, he, hae, hbe⟩ := hadj
    rcases ends_image he hae hbe with ⟨e', he', hy', -⟩ | ⟨-, h₂⟩
    · exact hyV ((G.same_V _ hyK).mpr (Γ'.tilde_subset_V he' hy'))
    · exact hne (G.eq_of_mem_frame h₂ hy c.2).symm

end FragInflation

end GraphMinor.GM19
