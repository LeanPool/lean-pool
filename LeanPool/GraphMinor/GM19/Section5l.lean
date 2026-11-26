/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5k

/-!
# Graph Minors XIX, proof of (5.4): gluing inflations

The proofs of (5.4) and (5.5) end alike: linear inflations of the fragments give a linear inflation
of `Γ` in `Γ'`, by
`σ(e) = ψ(σ'(ψ⁻¹(e)))` and `V(σ(v)) = ⋃ ψ(V(σ'(v')))` over the points `v'` over `v`. The paper says
that it is easy to
deduce this. We do it here for any family of fragments.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]


/-- The sides of a frame lie in one cuff. -/
theorem side_subset_cuff (hS : IsSurface S) (Φ : Frame S) {s : Set S}
  (hs : s ∈ Φ.sides) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hsΘ : (s ∩ Θ).Nonempty) : s ⊆ Θ := by
  obtain ⟨C, a, b, -, -, hsC, -, -, -⟩ := exists_arc_of_mem hS (cuffPar hS) Φ.finite_V
    (Frame.two_on_cuff hS Φ) hs
  have hCC : C.1 = Θ := by
    by_contra hne
    obtain ⟨x, hx₁, hx₂⟩ := hsΘ
    have hne' : C ≠ ⟨Θ, hΘ⟩ := fun h ↦ hne (congrArg Subtype.val h)
    exact disjoint_left.mp (cuffs_disjoint' hne') (arcOf_subset _ _ _ (hsC ▸ hx₁)) hx₂
  rw [hsC]
  exact hCC ▸ arcOf_subset _ _ _

omit [T2Space S] in
/-- An edge in the boundary is an arc of `bd(Σ) \ V`. -/
theorem Painting.mem_arcs_of_subset (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) (hb : e ⊆ bd S) :
    e ∈ arcComponentsIn (bd S \ Γ.V) :=
  ⟨he.1, fun _ hx ↦ ⟨hb hx, (he.2.1 hx).2⟩, he.2.2.1, fun D hD hc hsub ↦
    he.2.2.2 D (fun _ hx ↦ ⟨Γ.bd_subset (hD hx).1, (hD hx).2⟩) hc hsub⟩

variable {ι : Type} {Y : ι → Type} [∀ t, TopologicalSpace (Y t)] [∀ t, T2Space
  (Y t)] [∀ t, Nonempty (Y t)]
  {ψ : ∀ t, Y t → S}

/-- The sets `σ(v)` of the glued inflation. -/
def glueV (ψ : ∀ t, Y t → S) (σv : ∀ t, Y t → Set (Y t)) (v : S) : Set S :=
  ⋃ t, ⋃ y ∈ ψ t ⁻¹' {v}, ψ t '' σv t y

/-- The edges `σ(e)` of the glued inflation. -/
def glueE (ψ : ∀ t, Y t → S) (σe : ∀ t, Set (Y t) → Set (Y t)) (e : Set S) : Set S :=
  ⋃ t, ⋃ _ : (ψ t ⁻¹' e).Nonempty, ψ t '' σe t (ψ t ⁻¹' e)

variable {Φ : Frame S} {Γ Γ' : Painting S} {K : Drawing S} {D : ∀ t, FrameData Φ Γ K (ψ t)}
  {D' : ∀ t, FrameData Φ Γ' K (ψ t)} {hF : IsFeature Φ K} {flip : ∀ t, Set (Y t) → Bool}
  {σv : ∀ t, Y t → Set (Y t)} {σe : ∀ t, Set (Y t) → Set (Y t)}

/-- The fragments cover `Σ`, and off `U(K)` each point has one point over it. -/
structure IsCover (K : Drawing S) (ψ : ∀ t, Y t → S) : Prop where
  surj : ∀ x, ∃ t y, ψ t y = x
  one : ∀ t t' (y : Y t) (y' : Y t'), ψ t y = ψ t' y' → ψ t y ∉ K.U → (⟨t, y⟩ : Sigma Y) = ⟨t', y'⟩

/-- Off `U(K)` each point has at most one point over it. -/
structure IsOneOff (K : Drawing S) (ψ : ∀ t, Y t → S) : Prop where
  one : ∀ t t' (y : Y t) (y' : Y t'), ψ t y = ψ t' y' → ψ t y ∉ K.U → (⟨t, y⟩ : Sigma Y) = ⟨t', y'⟩

omit [T2Space S] [∀ (t : ι), T2Space (Y t)] [∀ (t : ι), Nonempty (Y t)] in
omit [(t : ι) → TopologicalSpace (Y t)] in
theorem IsCover.off {K : Drawing S} {ψ : ∀ t, Y t → S} (h : IsCover K ψ) : IsOneOff K ψ := ⟨h.one⟩

section

variable (G : ∀ t, FragInflation (D t) (D' t) hF (flip t) (σv t) (σe t)) (hC : IsOneOff K ψ)
include G hC

theorem glueE_eq {e : Set S} (he : e ∈ Γ.E) {t : ι} (hne : (ψ t ⁻¹' e).Nonempty) :
    glueE ψ σe e = ψ t '' σe t (ψ t ⁻¹' e) := by
  have huniq : ∀ t', (ψ t' ⁻¹' e).Nonempty → t' = t := by
    rintro t' ⟨x', hx'⟩
    have hsur := (G t).edge_main he hne
    obtain ⟨x, hx, hxx⟩ : ψ t' x' ∈ ψ t '' (ψ t ⁻¹' e) := by
      rw [hsur.1]
      exact hx'
    have hoff : ψ t' x' ∉ K.U := fun hK ↦ Γ.disjoint_V he hx' ((D t).pull.inter ⟨(he.2.1 hx').1,
      hK⟩).1
    exact congrArg Sigma.fst (hC.one t' t x' x hxx.symm hoff)
  ext z
  simp only [glueE, mem_iUnion]
  constructor
  · rintro ⟨t', hne', hz⟩
    exact huniq t' hne' ▸ hz
  · exact fun hz ↦ ⟨t, hne, hz⟩

omit hC in
/-- The set of a vertex of `Γ` maps into `V(Γ')`. -/
theorem piece_subset {t : ι} {y x : Y t} (hy : ψ t y ∈ Γ.V) (hx : x ∈ σv t y) : ψ t x ∈ Γ'.V := by
  have hV : x ∈ pullV Γ' K (ψ t) := (G t).inflation.vertex_subset y (Or.inl hy) hx
  rcases hV with h | h
  · exact h
  · have heq := (G t).eq_of_mem_frame (Or.inr h) (Or.inl hy) hx
    exact ((G t).same_V _ h).mp (heq ▸ hy)

/-- Each set `σ(v)` is connected. Two different points over `v` lie in the frame, so each piece
holds `v`. -/
theorem glue_connected {v : S} (hv : v ∈ Γ.V) : (Γ'.skAdj.induce (glueV ψ σv v)).Preconnected := by
  let T := glueV ψ σv v
  have hmem : ∀ t y x, ψ t y = v → x ∈ σv t y → ψ t x ∈ T := fun t y x hy hx ↦
    mem_iUnion.mpr ⟨t, mem_iUnion₂.mpr ⟨y, hy, mem_image_of_mem _ hx⟩⟩
  have key : ∀ t y (hy : ψ t y = v) a b (ha : a ∈ σv t y) (hb : b ∈ σv t y),
      (Γ'.skAdj.induce T).Reachable ⟨ψ t a, hmem t y a hy ha⟩ ⟨ψ t b, hmem t y b hy hb⟩ := by
    intro t y hy a b ha hb
    have hVy : ψ t y ∈ Γ.V := hy ▸ hv
    have hyp : y ∈ pullV Γ K (ψ t) := Or.inl hVy
    refine reachable_map (G := ((D' t).paint (flip t)).skAdj.induce (σv t y))
      (fun c : ↥(σv t y) ↦ (⟨ψ t c.1, hmem t y c.1 hy c.2⟩ : ↥T)) (fun c d hadj ↦ ?_)
      ((G t).inflation.vertex_connected y hyp ⟨a, ha⟩ ⟨b, hb⟩)
    rcases (G t).sk_step hyp c.2 d.2 (piece_subset G hVy c.2) (piece_subset G hVy d.2) hadj with h
      | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  rintro ⟨u, hu⟩ ⟨u', hu'⟩
  obtain ⟨t, hu⟩ := mem_iUnion.mp hu
  obtain ⟨y, hy, x, hx, rfl⟩ := mem_iUnion₂.mp hu
  obtain ⟨t', hu'⟩ := mem_iUnion.mp hu'
  obtain ⟨y', hy', x', hx', rfl⟩ := mem_iUnion₂.mp hu'
  have hy₀ : ψ t y = v := hy
  have hy₀' : ψ t' y' = v := hy'
  by_cases hsame : (⟨t, y⟩ : Sigma Y) = ⟨t', y'⟩
  · cases hsame
    exact key t y hy₀ x x' hx hx'
  · have hvK : v ∈ K.U := by
      by_contra hn
      exact hsame (hC.one t t' y y' (hy₀.trans hy₀'.symm) (hy₀ ▸ hn))
    have hvKV : v ∈ K.V := ((D t).pull.inter ⟨Γ.V_subset hv, hvK⟩).2
    have hF₁ : y ∈ pullFrameV Φ K (ψ t) := Or.inr (hy₀ ▸ hvKV)
    have hF₂ : y' ∈ pullFrameV Φ K (ψ t') := Or.inr (hy₀' ▸ hvKV)
    have h₁ := key t y hy₀ x y hx ((G t).mem_frame hF₁)
    have h₂ := key t' y' hy₀' y' x' ((G t').mem_frame hF₂) hx'
    have hee : (⟨ψ t y, hmem t y y hy₀ ((G t).mem_frame hF₁)⟩ : ↥T) =
        ⟨ψ t' y', hmem t' y' y' hy₀' ((G t').mem_frame hF₂)⟩ := Subtype.ext (hy₀.trans hy₀'.symm)
    exact h₁.trans (hee ▸ h₂)

/-- Different vertices have disjoint sets. -/
theorem glue_disjoint {v₁ v₂ : S} (hv₁ : v₁ ∈ Γ.V) (hv₂ : v₂ ∈ Γ.V) (hne : v₁ ≠ v₂) :
    Disjoint (glueV ψ σv v₁) (glueV ψ σv v₂) := by
  refine disjoint_left.mpr fun z hz₁ hz₂ ↦ ?_
  obtain ⟨t, hu⟩ := mem_iUnion.mp hz₁
  obtain ⟨y, hy, x, hx, rfl⟩ := mem_iUnion₂.mp hu
  obtain ⟨t', hu'⟩ := mem_iUnion.mp hz₂
  obtain ⟨y', hy', x', hx', hxx⟩ := mem_iUnion₂.mp hu'
  have hy₀ : ψ t y = v₁ := hy
  have hy₀' : ψ t' y' = v₂ := hy'
  by_cases hK : ψ t x ∈ K.U
  · have hxV := piece_subset G (hy₀ ▸ hv₁) hx
    have hxKV : ψ t x ∈ K.V := ((D' t).pull.inter ⟨Γ'.V_subset hxV, hK⟩).2
    have h₁ := (G t).eq_of_mem_frame (Or.inr hxKV) (Or.inl (hy₀ ▸ hv₁)) hx
    have h₂ := (G t').eq_of_mem_frame (Or.inr (hxx ▸ hxKV)) (Or.inl (hy₀' ▸ hv₂)) hx'
    exact hne (by rw [← hy₀, ← hy₀', ← h₁, ← h₂, hxx])
  · have hs := hC.one t t' x x' hxx.symm hK
    cases hs
    by_contra -
    have hyy : y ≠ y' := fun h ↦ hne (by rw [← hy₀, ← hy₀', h])
    exact disjoint_left.mp ((G t).inflation.vertex_disjoint y (Or.inl (hy₀ ▸ hv₁)) y' (Or.inl
      (hy₀' ▸ hv₂)) hyy) hx hx'

end

section

variable (G : ∀ t, FragInflation (D t) (D' t) hF (flip t) (σv t) (σe t)) (hC : IsCover K ψ)
include G hC

omit G in
omit [T2Space S] [∀ (t : ι), T2Space (Y t)] [∀ (t : ι), Nonempty (Y t)] in
omit [(t : ι) → TopologicalSpace (Y t)] in
theorem exists_lift {e : Set S} (he : e ∈ Γ.E) : ∃ t, (ψ t ⁻¹' e).Nonempty := by
  obtain ⟨x, hx⟩ := he.1
  obtain ⟨t, y, rfl⟩ := hC.surj x
  exact ⟨t, y, hx⟩

/-- **The glued inflation respects the frame.** -/
theorem glue_respects : RespectsFrame Φ Γ (glueE ψ σe) := by
  intro e he hb
  obtain ⟨t, hne⟩ := exists_lift hC he
  rw [glueE_eq G hC.off he hne]
  have hm := (G t).edge_main he hne
  obtain ⟨-, -, hE', -, -, -, -, hb₁, -⟩ := hm
  obtain ⟨s, hs, hes, hgs, hbg⟩ := hb₁ hb
  refine ⟨hbg, fun s' hs' ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · obtain ⟨x, hx⟩ := he.1
    have : s' = s := GM11.arcComponent_eq hs' hs (h hx) (hes hx)
    exact this ▸ hgs
  · obtain ⟨x, hx⟩ := hE'.1
    have : s' = s := GM11.arcComponent_eq hs' hs (h hx) (hgs hx)
    exact this ▸ hes

/-- **The glued inflation is linear.** -/
theorem glue_linear : IsLinearInflation Γ Γ' (glueV ψ σv) (glueE ψ σe) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨t, hne⟩ := exists_lift hC he
    rw [glueE_eq G hC.off he hne]
    exact ((G t).edge_main he hne).2.2.1
  · intro e he
    obtain ⟨t, hne⟩ := exists_lift hC he
    rw [glueE_eq G hC.off he hne]
    exact ((G t).edge_main he hne).2.2.2.2.1
  · intro e he e' he' heq
    obtain ⟨t, hne⟩ := exists_lift hC he
    obtain ⟨t', hne'⟩ := exists_lift hC he'
    have heq' := heq
    rw [glueE_eq G hC.off he hne, glueE_eq G hC.off he' hne'] at heq'
    obtain ⟨hsur, hE₁, hE', hpre, -⟩ := (G t).edge_main he hne
    obtain ⟨hsur', hE₁', hE'', hpre', -⟩ := (G t').edge_main he' hne'
    obtain ⟨_, x, hx, rfl⟩ := hE'.1
    obtain ⟨x', hx', hxx⟩ : ψ t x ∈ ψ t' '' σe t' (ψ t' ⁻¹' e') := heq' ▸ mem_image_of_mem _ hx
    have hoff : ψ t x ∉ K.U := fun hK ↦
      Γ'.disjoint_V hE' (mem_image_of_mem _ hx) ((D' t).pull.inter ⟨(hE'.2.1
        (mem_image_of_mem _ hx)).1, hK⟩).1
    have hs := hC.one t t' x x' hxx.symm hoff
    cases hs
    have hf : σe t (ψ t ⁻¹' e) = σe t (ψ t ⁻¹' e') := by
      rw [← hpre, ← hpre', heq']
    have he₁ := (G t).inflation.edge_injOn hE₁ hE₁' hf
    rw [← hsur, he₁, hsur']
  · intro v hv
    obtain ⟨t, y, rfl⟩ := hC.surj v
    obtain ⟨x, hx⟩ := (G t).inflation.vertex_nonempty y (Or.inl hv)
    exact ⟨ψ t x, mem_iUnion.mpr ⟨t, mem_iUnion₂.mpr ⟨y, rfl, mem_image_of_mem _ hx⟩⟩⟩
  · intro v hv z hz
    obtain ⟨t, hu⟩ := mem_iUnion.mp hz
    obtain ⟨y, hy, x, hx, rfl⟩ := mem_iUnion₂.mp hu
    have hy₀ : ψ t y = v := hy
    exact piece_subset G (hy₀ ▸ hv) hx
  · exact fun v hv ↦ glue_connected G hC.off hv
  · exact fun v₁ hv₁ v₂ hv₂ hne ↦ glue_disjoint G hC.off hv₁ hv₂ hne
  · intro e he i hi hi'
    obtain ⟨t, hne⟩ := exists_lift hC he
    have heq := glueE_eq G hC.off he hne
    obtain ⟨hsur, hE₁, hE', hpre, hsize, hm', hm, -⟩ := (G t).edge_main he hne
    have hi₁ : i < ((D t).paint (flip t) |>.γ (ψ t ⁻¹' e)).length := by
      rw [← List.length_map (f := ψ t), hm]
      exact hi
    have hi₂ : i < ((D' t).paint (flip t) |>.γ (σe t (ψ t ⁻¹' e))).length := by
      rw [← List.length_map (f := ψ t), hm', ← heq]
      exact hi'
    have hx := (G t).inflation.ends _ hE₁ i hi₁ hi₂
    have e₁ : (Γ.γ e)[i] = ψ t ((D t).paint (flip t) |>.γ (ψ t ⁻¹' e))[i] := by
      simp only [← hm, List.getElem_map]
    have e₂ : (Γ'.γ (glueE ψ σe e))[i] = ψ t ((D' t).paint (flip t) |>.γ (σe t (ψ t ⁻¹' e)))[i]
      := by
      simp only [heq, ← hm', List.getElem_map]
    rw [e₁, e₂]
    exact mem_iUnion.mpr ⟨t, mem_iUnion₂.mpr ⟨_, rfl, mem_image_of_mem _ hx⟩⟩
  · intro e he Θ hΘ
    obtain ⟨t, hne⟩ := exists_lift hC he
    have hS := (D t).pull.surface
    have hΘb : Θ ⊆ bd S := cuff_subset_bd ⟨Θ, hΘ⟩
    rw [glueE_eq G hC.off he hne]
    obtain ⟨-, -, hE', -, -, -, -, hb₁, hb₂⟩ := (G t).edge_main he hne
    by_cases hb : Painting.IsBorder e
    · obtain ⟨s, hs, hes, hgs, -⟩ := hb₁ hb
      obtain ⟨x, hx⟩ := he.1
      obtain ⟨z, hz⟩ := hE'.1
      constructor
      · rintro ⟨w, hw₁, hw₂⟩
        exact ⟨z, hz, side_subset_cuff hS Φ hs hΘ ⟨w, hes hw₁, hw₂⟩ (hgs hz)⟩
      · rintro ⟨w, hw₁, hw₂⟩
        exact ⟨x, hx, side_subset_cuff hS Φ hs hΘ ⟨w, hgs hw₁, hw₂⟩ (hes hx)⟩
    · constructor
      · rintro ⟨w, hw₁, hw₂⟩
        exact absurd ⟨w, hw₁, hΘb hw₂⟩ hb
      · rintro ⟨w, hw₁, hw₂⟩
        exact absurd ⟨w, hw₁, hΘb hw₂⟩ (hb₂ hb)
  · intro e' he' hb' hnot
    have hsub' := (Γ'.border_edge e' he' hb').2
    obtain ⟨x, hx⟩ := he'.1
    obtain ⟨t, y, rfl⟩ := hC.surj x
    have hyl : y ∈ ψ t ⁻¹' e' := hx
    obtain ⟨hp, hsur⟩ := (D' t).pull.preimage_border_edge he' hsub' hyl
    have hpE : ψ t ⁻¹' e' ∈ ((D' t).paint (flip t)).E := ((D' t).mem_paint_E (flip t)).mpr
      (Or.inl hp)
    have hyb : y ∈ bd (Y t) := (hp.2.1 hyl).1
    have hpb : Painting.IsBorder (ψ t ⁻¹' e') := ⟨y, hyl, hyb⟩
    have hpn : ψ t ⁻¹' e' ∉ σe t '' ((D t).paint (flip t)).E := by
      rintro ⟨e₁, he₁, hσ⟩
      obtain ⟨Θ, hΘ, hyΘ⟩ := sUnion_cuffs (S := Y t) ▸ hyb
      obtain ⟨w, hw, hwΘ⟩ := ((G t).inflation.borders_iff _ he₁ Θ hΘ).mpr ⟨y, hσ.symm ▸ hyl, hyΘ⟩
      have hwb : w ∈ bd (Y t) := cuff_subset_bd ⟨Θ, hΘ⟩ hwΘ
      have hb₁ : Painting.IsBorder e₁ := ⟨w, hw, hwb⟩
      rcases ((D t).mem_paint_E (flip t)).mp he₁ with ha | ⟨e, he, hb, hne, rfl⟩
      · obtain ⟨R, hR, hes⟩ := exists_arcComp_superset ha.2.2.1 (F := bd (Y t) \ pullFrameV Φ K
        (ψ t))
          (fun x hx ↦ ⟨(ha.2.1 hx).1, fun h ↦ (ha.2.1 hx).2 ((D t).pullFrameV_subset h)⟩)
        have hfR : σe t e₁ ⊆ R := (((G t).respects e₁ he₁ hb₁).2 R hR).mp hes
        obtain ⟨s, hs, hRs⟩ := (D t).exists_side_of_bd hR (hfR (hσ.symm ▸ hyl)) (hsub' hx)
        have hwS : ψ t w ∈ bd S := (hs.2.1 (hRs (mem_image_of_mem _ (hes hw)))).1
        obtain ⟨hE₀, hpre⟩ := (D t).pull.image_border_edge ha hw hwS
        have hlift : ((ψ t ⁻¹' (ψ t '' e₁)).Nonempty) := by
          rw [hpre]
          exact ha.1
        apply hnot
        refine ⟨ψ t '' e₁, hE₀, ?_⟩
        rw [glueE_eq G hC.off hE₀ hlift, hpre, hσ, hsur]
      · exact (D t).pull.preimage_subset_int ((D t).pull.subset_R he hb hne) hw hwb
    obtain ⟨z, hz, htil⟩ := (G t).inflation.border_edge _ hpE hpb hpn
    have htile : tilde e' = ψ t '' tilde (ψ t ⁻¹' e') := by
      rw [← (D' t).pull.tilde_image_arc hp, hsur]
    have h2 : (tilde (ψ t ⁻¹' e')).ncard = 2 := ((D' t).paint (flip t)).border_edge _ hpE hpb |>.1
    have hzV : ψ t z ∈ Γ.V := by
      by_contra hn
      have hF : z ∈ pullFrameV Φ K (ψ t) := by
        rcases hz with h | h
        · exact absurd h hn
        · exact Or.inr h
      have hsing : tilde (ψ t ⁻¹' e') ⊆ {z} := fun a ha ↦ (G t).eq_of_not_V hz hF hn (htil ha)
      have := ncard_le_ncard hsing (finite_singleton z)
      rw [h2, ncard_singleton] at this
      omega
    refine ⟨ψ t z, hzV, ?_⟩
    rw [htile]
    rintro _ ⟨a, ha, rfl⟩
    exact mem_iUnion.mpr ⟨t, mem_iUnion₂.mpr ⟨z, rfl, mem_image_of_mem _ (htil ha)⟩⟩
  · intro e he Θ hΘ hmeet f n n' hn hn' hp
    obtain ⟨t, hne⟩ := exists_lift hC he
    have hS := (D t).pull.surface
    have heq := glueE_eq G hC.off he hne
    obtain ⟨-, -, hE', -, -, -, -, hb₁, -⟩ := (G t).edge_main he hne
    obtain ⟨w, hw₁, hw₂⟩ := hmeet
    have hb : Painting.IsBorder e := ⟨w, hw₁, cuff_subset_bd ⟨Θ, hΘ⟩ hw₂⟩
    obtain ⟨s, hs, hes, hgs, hbg⟩ := hb₁ hb
    rw [← heq] at hE' hgs hbg
    exact immediatelyPrecedes_transfer hS (D t).fits (D' t).fits he
      (Γ'.mem_arcs_of_subset hE' (Γ'.border_edge _ hE' hbg).2) hE' hs hes hgs hb hbg hΘ
      ⟨w, hes hw₁, hw₂⟩ f hn hn' hp

end

end GraphMinor.GM19
