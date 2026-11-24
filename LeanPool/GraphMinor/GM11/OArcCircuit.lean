/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.EvenCircuit
public import LeanPool.GraphMinor.GM11.PaintingRegions
public import LeanPool.GraphMinor.GM11.Separate
public import LeanPool.GraphMinor.GM11.PaintingFacts

/-!
# An `O`-arc in a drawing is a circuit

`exists_circuit_of_oArc` says that an `O`-arc inside the point set of a drawing is the point set of
a circuit.
Graph Minors XI, (8.5), uses this without comment when it says that an `O`-arc in `U(W)` bounds a
disc in
`ins(W)`. An edge that meets the `O`-arc lies in it (`edge_subset_of_oArc`). Then the `O`-arc is a
union of
edges, each edge lies on a circuit of this union, since the arc stays connected when a point is
removed,
and that circuit is the whole `O`-arc, since one `O`-arc does not contain another
(`eq_of_oArc_subset`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- There is no injective continuous map from the circle to the line. -/
theorem not_injective_circle_real {g : Circle → ℝ} (hg : Continuous g) : ¬ Function.Injective g
  := by
  intro hi
  have hK : IsCompact (range g) := isCompact_range hg
  obtain ⟨z₁, hz₁⟩ : ∃ z, IsMinOn g univ z := by
    obtain ⟨z, -, h⟩ := isCompact_univ.exists_isMinOn univ_nonempty hg.continuousOn
    exact ⟨z, h⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z, IsMaxOn g univ z := by
    obtain ⟨z, -, h⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hg.continuousOn
    exact ⟨z, h⟩
  have hU : IsOArc (univ : Set Circle) := ⟨(Homeomorph.Set.univ Circle).symm⟩
  have hinf : (univ : Set Circle).Infinite := infinite_of_isOArc hU
  obtain ⟨z, -, hzne⟩ : ∃ z ∈ (univ : Set Circle), z ∉ ({z₁, z₂} : Set Circle) :=
    (hinf.sdiff (toFinite _)).nonempty.imp fun z h => ⟨h.1, h.2⟩
  have hne₁ : z ≠ z₁ := fun h => hzne (Or.inl h)
  have hne₂ : z ≠ z₂ := fun h => hzne (Or.inr h)
  have hc : IsPreconnected ({z}ᶜ : Set Circle) := by
    have := (isPathConnected_oArc_diff hU (mem_univ z)).isConnected.isPreconnected
    rwa [← compl_eq_univ_sdiff] at this
  have hsub := hc.image g hg.continuousOn
  have hle₁ : g z₁ < g z := lt_of_le_of_ne (hz₁ (mem_univ z)) (fun h => hne₁ (hi h).symm)
  have hle₂ : g z < g z₂ := lt_of_le_of_ne (hz₂ (mem_univ z)) (fun h => hne₂ (hi h))
  have hord : (g '' {z}ᶜ).OrdConnected := hsub.ordConnected
  obtain ⟨w, hw, hwz⟩ := hord.out ⟨z₁, Ne.symm hne₁, rfl⟩ ⟨z₂, Ne.symm hne₂, rfl⟩ ⟨hle₁.le, hle₂.le⟩
  exact hw (hi hwz)

/-- One `O`-arc does not contain another, except itself. -/
theorem eq_of_oArc_subset [T2Space S] {F₁ F : Set S} (h₁ : IsOArc F₁) (h : IsOArc F)
  (hsub : F₁ ⊆ F) :
    F₁ = F := by
  by_contra hne
  obtain ⟨a, haF, ha₁⟩ : ∃ a ∈ F, a ∉ F₁ := by
    by_contra hall
    push Not at hall
    exact hne (subset_antisymm hsub hall)
  obtain ⟨p, hp, h0, h2, hper, himg, hr⟩ := exists_oArc_par h haF
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  obtain ⟨φ⟩ := id h₁
  have hc₁ : IsCompact F₁ := isCompact_of_isOArc h₁
  let T : Set ℝ := Icc 0 (2 * Real.pi) ∩ p ⁻¹' F₁
  have hTc : IsCompact T := isCompact_Icc.inter_right (hc₁.isClosed.preimage hp)
  have hcT : CompactSpace T := isCompact_iff_compactSpace.mp hTc
  let j : T → F₁ := fun t => ⟨p t.1, t.2.2⟩
  have hjc : Continuous j := Continuous.subtype_mk (hp.comp continuous_subtype_val) _
  have hjb : Function.Bijective j := by
    constructor
    · rintro ⟨s, hs₁, hs₂⟩ ⟨t, ht₁, ht₂⟩ hst
      have heq : p s = p t := congrArg Subtype.val hst
      have hs0 : s ≠ 0 := fun h' => ha₁ (by rw [← h0, ← h']; exact hs₂)
      have ht0 : t ≠ 0 := fun h' => ha₁ (by rw [← h0, ← h']; exact ht₂)
      have hs2 : s ≠ 2 * Real.pi := fun h' => ha₁ (by rw [← h2, ← h']; exact hs₂)
      have ht2 : t ≠ 2 * Real.pi := fun h' => ha₁ (by rw [← h2, ← h']; exact ht₂)
      have hs' : 0 < s := lt_of_le_of_ne hs₁.1 (Ne.symm hs0)
      have ht' : 0 < t := lt_of_le_of_ne ht₁.1 (Ne.symm ht0)
      have hs'' : s < 2 * Real.pi := lt_of_le_of_ne hs₁.2 hs2
      have ht'' : t < 2 * Real.pi := lt_of_le_of_ne ht₁.2 ht2
      obtain ⟨m, hm⟩ := hper s t heq
      have hm0 : m = 0 := by
        by_contra hm0
        have h₃ : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
        have h₄ : |s - t| = |(m : ℝ)| * (2 * Real.pi) := by
          rw [hm, add_sub_cancel_left, abs_mul, abs_of_pos hpos]
        have h₅ : |s - t| < 2 * Real.pi := abs_lt.mpr ⟨by linarith, by linarith⟩
        nlinarith
      exact Subtype.ext (by simpa [hm0] using hm)
    · rintro ⟨y, hy⟩
      have hyF := hsub hy
      rw [← himg] at hyF
      obtain ⟨t, ht, rfl⟩ := hyF
      exact ⟨⟨t, ⟨ht.1, ht.2.le⟩, hy⟩, rfl⟩
  have hT2 : T2Space F₁ := inferInstance
  let J := hjc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j hjb)
  let g : Circle → ℝ := fun z => (J.symm (φ z)).1
  have hgc : Continuous g := continuous_subtype_val.comp (J.symm.continuous.comp φ.continuous)
  refine not_injective_circle_real hgc fun x y hxy => φ.injective (J.symm.injective ?_)
  exact Subtype.ext hxy

/-- An edge of a drawing that meets an `O`-arc in the drawing lies in the `O`-arc. -/
theorem edge_subset_of_oArc [T2Space S] [ConnectedSpace S] {N : Drawing S} {F e : Set S}
  (hF : IsOArc F)
    (hFU : F ⊆ N.U) (he : e ∈ N.E) (hne : (e ∩ F).Nonempty) : e ⊆ F := by
  obtain ⟨γ, hγ⟩ := exists_edgePar N
  have hc := hγ.cont e he
  have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
  -- We work in the parameter interval of the edge.
  have hsplit : ∀ t ∈ Ioo (0 : I) 1, γ e t ∈ F → ∃ O : Set I, IsOpen O ∧ t ∈ O ∧ O ⊆ γ e ⁻¹' F := by
    intro t ht htF
    obtain ⟨p, hp, h0, -, hper, -, hr⟩ := exists_oArc_par hF htF
    have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
    have hO : IsOpen (p ⁻¹' (N.U \ e)ᶜ) := (isClosed_U_sdiff_edge N he).isOpen_compl.preimage hp
    have h0O : (0 : ℝ) ∈ p ⁻¹' (N.U \ e)ᶜ := by
      change p 0 ∈ (N.U \ e)ᶜ
      rw [h0]
      exact fun h => h.2 ((hγ.image e he).subset ⟨t, ht, rfl⟩)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hO 0 h0O
    let ε : ℝ := min (δ / 2) 1
    have hε : 0 < ε := by positivity
    have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hε1 : ε ≤ 1 := min_le_right _ _
    have hpe : ∀ θ ∈ Icc (-ε) ε, p θ ∈ e := by
      intro θ hθ
      have hmem : θ ∈ Metric.ball (0 : ℝ) δ := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        exact (abs_le.mpr hθ).trans_lt hεδ
      by_contra hn
      exact hball hmem ⟨hFU (hr (mem_range_self θ)), hn⟩
    let K : Set S := p '' Icc (-ε) ε
    have hKc : IsCompact K := isCompact_Icc.image hp
    let T' : Set I := γ e ⁻¹' K
    have hT'c : IsCompact T' := (hKc.isClosed.preimage hc).isCompact
    have hT'I : T' ⊆ Ioo 0 1 := by
      intro s hs
      obtain ⟨θ, hθ, hθs⟩ := hs
      have hsV : γ e s ∉ N.V := by
        rw [← hθs]
        exact (he.2.1 (hpe θ hθ)).2
      refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
      · rintro rfl
        exact hsV (hγ.zero e he)
      · rintro rfl
        exact hsV (hγ.one e he)
    have hcT : CompactSpace T' := isCompact_iff_compactSpace.mp hT'c
    let j : T' → K := fun s => ⟨γ e s.1, s.2⟩
    have hjc : Continuous j := Continuous.subtype_mk (hc.comp continuous_subtype_val) _
    have hjb : Function.Bijective j := by
      constructor
      · rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ hs
        exact Subtype.ext (hγ.inj e he (hT'I h₁) (hT'I h₂) (congrArg Subtype.val hs))
      · rintro ⟨y, θ, hθ, rfl⟩
        obtain ⟨s, -, hs⟩ := (hγ.image e he).superset (hpe θ hθ)
        exact ⟨⟨s, θ, hθ, hs.symm⟩, Subtype.ext hs⟩
    let J := hjc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j hjb)
    have hJ : ∀ y, γ e (J.symm y).1 = y.1 := fun y => by
      have := congrArg Subtype.val (J.apply_symm_apply y)
      exact this
    have hmemK : ∀ θ : Icc (-ε) ε, p θ.1 ∈ K := fun θ => ⟨θ.1, θ.2, rfl⟩
    let f : ℝ → ℝ := fun θ =>
      ((J.symm ⟨p (projIcc (-ε) ε (by linarith) θ).1, hmemK _⟩).1.1 : ℝ)
    have hfc : Continuous f := by
      refine continuous_subtype_val.comp (continuous_subtype_val.comp (J.symm.continuous.comp ?_))
      exact Continuous.subtype_mk (hp.comp (continuous_subtype_val.comp continuous_projIcc)) _
    have hfγ : ∀ θ ∈ Icc (-ε) ε, ∃ s : I, s.1 = f θ ∧ γ e s = p θ := by
      intro θ hθ
      refine ⟨(J.symm ⟨p (projIcc (-ε) ε (by linarith) θ).1, hmemK _⟩).1, rfl, ?_⟩
      rw [hJ]
      simp [projIcc_of_mem _ hθ]
    have hfi : InjOn f (Icc (-ε) ε) := by
      intro a ha b hb hab
      obtain ⟨s₁, h₁, h₂⟩ := hfγ a ha
      obtain ⟨s₂, h₃, h₄⟩ := hfγ b hb
      have hss : s₁ = s₂ := Subtype.ext (by rw [h₁, h₃, hab])
      have hpp : p a = p b := by rw [← h₂, ← h₄, hss]
      obtain ⟨m, hm⟩ := hper a b hpp
      have hm0 : m = 0 := by
        by_contra hm0
        have h₃ : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
        have h₄ : |a - b| = |(m : ℝ)| * (2 * Real.pi) := by
          rw [hm, add_sub_cancel_left, abs_mul, abs_of_pos hpos]
        have h₅ : |a - b| ≤ 2 := by
          rw [abs_le]
          constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
        have hpi := Real.two_le_pi
        nlinarith
      simpa [hm0] using hm
    obtain ⟨s₀, hs₀, hs₀γ⟩ := hfγ 0 ⟨by linarith, hε.le⟩
    have hs₀t : s₀ = t := hγ.inj e he (hT'I (show s₀ ∈ T' from ⟨0, ⟨by linarith, hε.le⟩,
      hs₀γ.symm⟩))
      ht (by rw [hs₀γ, h0])
    have hmono := hfc.continuousOn.strictMonoOn_of_injOn_Icc' (a := -ε) (b := ε) (by linarith) hfi
    let m₁ : ℝ := min (f (-ε)) (f ε)
    let m₂ : ℝ := max (f (-ε)) (f ε)
    have hbet : m₁ < f 0 ∧ f 0 < m₂ := by
      have ha : -ε ∈ Icc (-ε) ε := ⟨le_rfl, by linarith⟩
      have hb : ε ∈ Icc (-ε) ε := ⟨by linarith, le_rfl⟩
      have h0' : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
      rcases hmono with h | h
      · have h₁ := h ha h0' (by linarith)
        have h₂ := h h0' hb hε
        exact ⟨(min_le_left _ _).trans_lt h₁, h₂.trans_le (le_max_right _ _)⟩
      · have h₁ := h ha h0' (by linarith)
        have h₂ := h h0' hb hε
        exact ⟨(min_le_right _ _).trans_lt h₂, h₁.trans_le (le_max_left _ _)⟩
    refine ⟨Subtype.val ⁻¹' Ioo m₁ m₂, isOpen_Ioo.preimage continuous_subtype_val, ?_, ?_⟩
    · change t.1 ∈ Ioo m₁ m₂
      rw [← hs₀t, hs₀]
      exact hbet
    · intro s hs
      have hIVT : Ioo m₁ m₂ ⊆ f '' Icc (-ε) ε := by
        have hle : -ε ≤ ε := by linarith
        have h₁ := intermediate_value_uIcc (a := -ε) (b := ε) (f := f)
          (by rw [uIcc_of_le hle]; exact hfc.continuousOn)
        rw [uIcc_of_le hle] at h₁
        intro y hy
        exact h₁ (by
          rw [mem_uIcc]
          rcases le_total (f (-ε)) (f ε) with hc' | hc'
          · left
            simp only [m₁, m₂, min_eq_left hc', max_eq_right hc'] at hy
            exact ⟨hy.1.le, hy.2.le⟩
          · right
            simp only [m₁, m₂, min_eq_right hc', max_eq_left hc'] at hy
            exact ⟨hy.1.le, hy.2.le⟩)
      obtain ⟨θ, hθ, hθs⟩ := hIVT hs
      obtain ⟨s', hs', hγs⟩ := hfγ θ hθ
      have hss : s' = s := Subtype.ext (hs'.trans hθs)
      change γ e s ∈ F
      rw [← hss, hγs]
      exact hr (mem_range_self θ)
  choose! O hOo hOm hOs using hsplit
  let u : Set I := ⋃ t ∈ Ioo (0 : I) 1 ∩ γ e ⁻¹' F, O t
  have hu : IsOpen u := isOpen_biUnion fun t ht => hOo t ht.1 ht.2
  obtain ⟨y, hye, hyF⟩ := hne
  obtain ⟨t₀, ht₀, rfl⟩ := (hγ.image e he).superset hye
  have hus : u ⊆ γ e ⁻¹' F := iUnion₂_subset fun t ht => hOs t ht.1 ht.2
  have hconn : IsPreconnected (Ioo (0 : I) 1) := isPreconnected_Ioo
  have hsub : Ioo (0 : I) 1 ⊆ u := hconn.subset_of_closure_inter_subset hu
    ⟨t₀, ht₀, mem_biUnion ⟨ht₀, hyF⟩ (hOm t₀ ht₀ hyF)⟩ (by
      rintro s ⟨hs₁, hs₂⟩
      have : s ∈ γ e ⁻¹' F := closure_minimal hus (hFc.preimage hc) hs₁
      exact mem_biUnion ⟨hs₂, this⟩ (hOm s hs₂ this))
  intro x hx
  obtain ⟨s, hs, rfl⟩ := (hγ.image e he).superset hx
  exact hus (hsub hs)

/-- **An `O`-arc inside a drawing is the point set of a circuit.** -/
theorem exists_circuit_of_oArc [T2Space S] [ConnectedSpace S] {N : Drawing S} {F : Set S}
  (hF : IsOArc F)
    (hFU : F ⊆ N.U) : ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing N ∧ C.U = F := by
  classical
  obtain ⟨γ, hγ⟩ := exists_edgePar N
  have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
  let H := N.interSet F
  have hHN : H.IsSubdrawing N := Drawing.span_isSubdrawing N _ _
  have hHE : ∀ f, f ∈ H.E ↔ f ∈ N.E ∧ f ⊆ F := by
    intro f
    change f ∈ (N.span _ _).E ↔ _
    rw [N.span_E]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  have hHU : H.U ⊆ F := by
    rw [H.U_eq]
    rintro x (hx | hx)
    · rcases hx with ⟨⟨-, hx⟩, -⟩ | hx
      · exact hx
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
        exact closure_minimal hf.1.2 hFc hxf.1
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      exact closure_minimal ((hHE f).mp hf).2 hFc hxf
  obtain ⟨y₀, hy₀F, hy₀V⟩ : ∃ y ∈ F, y ∉ N.V :=
    ((infinite_of_isOArc hF).sdiff N.finite_V).nonempty.imp fun _ h => ⟨h.1, h.2⟩
  obtain ⟨e, heN, hy₀e⟩ := N.exists_edge_of_mem (hFU hy₀F) hy₀V
  have heF : e ⊆ F := edge_subset_of_oArc hF hFU heN ⟨y₀, hy₀e, hy₀F⟩
  have heH : e ∈ H.E := (hHE e).mpr ⟨heN, heF⟩
  let D := H.deleteEdge e
  have hDH : D.IsSubdrawing H := deleteEdge_isSubdrawing H e
  have hDN : D.IsSubdrawing N := hDH.trans hHN
  have hDE : D.E = H.E \ {e} := deleteEdge_E H e
  have hDV : D.V = H.V := deleteEdge_V H e
  have hDU : D.U = H.U \ e := deleteEdge_U H heH
  set a := γ e (endOf false) with ha
  set b := γ e (endOf true) with hb
  have haV : a ∈ H.V := by
    have := (isLink_ends hγ hHN heH false).2.1
    exact this
  have hbV : b ∈ H.V := (isLink_ends hγ hHN heH false).2.2.1
  have hreach : Nonempty (GraphWalk D.toGraph a b) := by
    by_contra hno
    let A : Set S := {x | Nonempty (GraphWalk D.toGraph a x)}
    have haA : a ∈ A := ⟨.nil (show a ∈ D.V from hDV ▸ haV)⟩
    have hbA : b ∉ A := hno
    have hAV : A ⊆ D.V := by
      rintro x ⟨W⟩
      exact mem_V_of_mem_support W W.end_mem_support
    have hstep : ∀ f ∈ D.E, ∀ c, γ f (endOf c) ∈ A → γ f (endOf (!c)) ∈ A := by
      rintro f hf c ⟨W⟩
      exact ⟨W.append (.cons (isLink_ends hγ hDN hf c)
        (.nil (isLink_ends hγ hDN hf c).2.2.1))⟩
    let side : Set S → Prop := fun f => γ f (endOf false) ∈ A
    have hside : ∀ f ∈ D.E, ∀ x ∈ closure f, x ∈ N.V → (side f ↔ x ∈ A) := by
      intro f hf x hxf hxV
      obtain ⟨c, rfl⟩ := exists_end_eq hγ (hDN.2 hf) hxV hxf
      cases c with
      | false => exact Iff.rfl
      | true => exact ⟨hstep f hf false, hstep f hf true⟩
    let G₁ : Set S := A ∪ ⋃ f ∈ {f | f ∈ D.E ∧ side f}, closure f
    let G₂ : Set S := (D.V \ A) ∪ ⋃ f ∈ {f | f ∈ D.E ∧ ¬ side f}, closure f
    have hfinE : ∀ P : Set S → Prop, {f | f ∈ D.E ∧ P f}.Finite := fun P =>
      D.finite_edges.subset fun _ h => h.1
    have hG₁c : IsClosed G₁ := ((D.finite_V.subset hAV).isClosed).union
      ((hfinE _).isClosed_biUnion fun _ _ => isClosed_closure)
    have hG₂c : IsClosed G₂ := ((D.finite_V.subset sdiff_subset).isClosed).union
      ((hfinE _).isClosed_biUnion fun _ _ => isClosed_closure)
    have hcl : ∀ f ∈ D.E, closure f ⊆ D.U := fun f hf => D.closure_subset_U hf
    have hG₁U : G₁ ⊆ D.U := by
      rintro x (hx | hx)
      · exact D.V_subset_U (hAV hx)
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
        exact hcl f hf.1 hxf
    have hG₂U : G₂ ⊆ D.U := by
      rintro x (hx | hx)
      · exact D.V_subset_U hx.1
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
        exact hcl f hf.1 hxf
    have hmeet : Disjoint G₁ G₂ := by
      refine disjoint_left.mpr ?_
      rintro x (hx₁ | hx₁) (hx₂ | hx₂)
      · exact hx₂.2 hx₁
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx₂
        exact hf.2 ((hside f hf.1 x hxf (hDN.1 (hAV hx₁))).mpr hx₁)
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx₁
        exact hx₂.2 ((hside f hf.1 x hxf (hDN.1 hx₂.1)).mp hf.2)
      · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx₁
        obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx₂
        have hfg : f ≠ g := fun h => hg.2 (h ▸ hf.2)
        have hxV : x ∈ N.V := closure_inter_subset_V (hDN.2 hf.1) (hDN.2 hg.1) hfg ⟨hxf, hxg⟩
        exact hg.2 ((hside g hg.1 x hxg hxV).mpr ((hside f hf.1 x hxf hxV).mp hf.2))
    -- Cut `e` at an inner point `y₀`.
    obtain ⟨s₀, hs₀, rfl⟩ := (hγ.image e heN).superset hy₀e
    let P₁ : Set S := γ e '' Icc 0 s₀
    let P₂ : Set S := γ e '' Icc s₀ 1
    have hc := hγ.cont e heN
    have hP₁c : IsClosed P₁ := (isCompact_Icc.image hc).isClosed
    have hP₂c : IsClosed P₂ := (isCompact_Icc.image hc).isClosed
    have hPmem : ∀ {t : I}, t ∈ Ioo (0 : I) 1 → γ e t ∈ e := fun ht =>
      (hγ.image e heN).subset ⟨_, ht, rfl⟩
    have hsplit : ∀ t : I, t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : I) 1 := fun t => by
      by_cases h0 : t = 0
      · exact Or.inl h0
      by_cases h1 : t = 1
      · exact Or.inr (Or.inl h1)
      exact Or.inr (Or.inr ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr
        h1⟩)
    have ha0 : γ e 0 = a := by simp [ha, endOf]
    have hb1 : γ e 1 = b := by simp [hb, endOf]
    have haF : a ∈ F := hHU (H.V_subset_U haV)
    have hbF : b ∈ F := hHU (H.V_subset_U hbV)
    have hnoe : ∀ x ∈ G₁ ∪ G₂, x ∉ e := fun x hx hxe =>
      (hDU ▸ (hx.elim (fun h => hG₁U h) fun h => hG₂U h) : x ∈ H.U \ e).2 hxe
    have hcover : F \ {γ e s₀} ⊆ (P₁ ∪ G₁) ∪ (P₂ ∪ G₂) := by
      intro x hx
      by_cases hxe : x ∈ e
      · obtain ⟨t, ht, rfl⟩ := (hγ.image e heN).superset hxe
        rcases le_total t s₀ with h | h
        · exact Or.inl (Or.inl ⟨t, ⟨unitInterval.nonneg _, h⟩, rfl⟩)
        · exact Or.inr (Or.inl ⟨t, ⟨h, unitInterval.le_one _⟩, rfl⟩)
      · by_cases hxV : x ∈ N.V
        · have hxD : x ∈ D.V := hDV ▸ (Or.inl ⟨⟨hxV, hx.1⟩, hxV⟩ : x ∈ H.V)
          by_cases hxA : x ∈ A
          · exact Or.inl (Or.inr (Or.inl hxA))
          · exact Or.inr (Or.inr (Or.inl ⟨hxD, hxA⟩))
        · obtain ⟨g, hgN, hxg⟩ := N.exists_edge_of_mem (hFU hx.1) hxV
          have hgH : g ∈ H.E := (hHE g).mpr ⟨hgN, edge_subset_of_oArc hF hFU hgN ⟨x, hxg, hx.1⟩⟩
          have hgD : g ∈ D.E := hDE ▸ ⟨hgH, fun h => hxe (mem_singleton_iff.mp h ▸ hxg)⟩
          by_cases hgs : side g
          · exact Or.inl (Or.inr (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hgD, hgs⟩, subset_closure hxg⟩)))
          · exact Or.inr (Or.inr (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hgD, hgs⟩, subset_closure hxg⟩)))
    have hpc : IsPreconnected (F \ {γ e s₀}) :=
      (isPathConnected_oArc_diff hF hy₀F).isConnected.isPreconnected
    have hes : γ e s₀ ∈ e := hPmem hs₀
    have haN : a ∈ N.V := hHN.1 haV
    have hbN : b ∈ N.V := hHN.1 hbV
    have hoff : ∀ {x}, x ∈ N.V → x ∉ e := fun hx hxe => (heN.2.1 hxe).2 hx
    obtain ⟨x, hx, hx₁, hx₂⟩ := isPreconnected_closed_iff.mp hpc (P₁ ∪ G₁) (P₂ ∪ G₂)
      (hP₁c.union hG₁c) (hP₂c.union hG₂c) hcover
      ⟨a, ⟨haF, fun h => hoff haN (mem_singleton_iff.mp h ▸ hes)⟩,
        Or.inl ⟨0, ⟨le_rfl, unitInterval.nonneg _⟩, ha0⟩⟩
      ⟨b, ⟨hbF, fun h => hoff hbN (mem_singleton_iff.mp h ▸ hes)⟩,
        Or.inl ⟨1, ⟨unitInterval.le_one _, le_rfl⟩, hb1⟩⟩
    have hs₀1 : s₀ ≠ 1 := hs₀.2.ne
    have hs₀0 : (0 : I) ≠ s₀ := hs₀.1.ne
    rcases hx₁ with ⟨t, ht, rfl⟩ | hg₁ <;> rcases hx₂ with hx₂ | hg₂
    · obtain ⟨t', ht', hte⟩ := hx₂
      rcases hsplit t with rfl | rfl | hi
      · rcases hsplit t' with rfl | rfl | hi'
        · exact not_le.mpr hs₀.1 ht'.1
        · exact hbA (by
            have h₁ : b = a := by rw [← hb1, hte, ha0]
            exact h₁ ▸ haA)
        · exact hoff haN (by
            have := hPmem hi'
            rwa [hte, ha0] at this)
      · exact hs₀1 (le_antisymm (unitInterval.le_one _) ht.2)
      · rcases hsplit t' with rfl | rfl | hi'
        · exact not_le.mpr hs₀.1 ht'.1
        · exact hoff hbN (by
            have := hPmem hi
            rwa [← hte, hb1] at this)
        · have htt : t' = t := hγ.inj e heN hi' hi hte
          subst htt
          have hts : t' = s₀ := le_antisymm ht.2 ht'.1
          exact hx.2 (by rw [hts]; rfl)
    · have hne : γ e t ∉ e := hnoe _ (Or.inr hg₂)
      rcases hsplit t with rfl | rfl | hi
      · rw [ha0] at hg₂
        rcases hg₂ with h | h
        · exact h.2 haA
        · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
          exact hg.2 ((hside g hg.1 a hxg haN).mpr haA)
      · exact hs₀1 (le_antisymm (unitInterval.le_one _) ht.2)
      · exact hne (hPmem hi)
    · obtain ⟨t', ht', hte⟩ := hx₂
      have hne : x ∉ e := hnoe _ (Or.inl hg₁)
      subst hte
      rcases hsplit t' with rfl | rfl | hi
      · exact not_le.mpr hs₀.1 ht'.1
      · rw [hb1] at hg₁
        rcases hg₁ with h | h
        · exact hbA h
        · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
          exact hbA ((hside g hg.1 b hxg hbN).mp hg.2)
      · exact hne (hPmem hi)
    · exact disjoint_left.mp hmeet hg₁ hg₂
  obtain ⟨C, hC, hCs, -⟩ := exists_circuit_of_reach hγ hHN heH hreach
  exact ⟨C, hC, hCs.trans hHN, eq_of_oArc_subset (IsCircuit.isOArc_U hC) hF
    (hCs.U_subset.trans hHU)⟩

end GraphMinor.GM11
