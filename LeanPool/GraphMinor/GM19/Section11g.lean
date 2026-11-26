/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section11f
public import LeanPool.GraphMinor.GM19.Section10t
public import LeanPool.GraphMinor.GM19.FragmentOrient
public import LeanPool.GraphMinor.GM19.Conditional2

/-!
# Graph Minors XIX, Section 11: the proof of (11.1)

All the flaws on a side with one feature make a well-behaved set (`exists_class_side`). Each piece
of the side outside `Z` leaves out one `ω_h`, and the paper's sets `Z_{ωᵢ'}` are the labels of these
pieces. The
labels range over a finite set, so this is finitely many uses of `wellBehaved_side`. There are
finitely many features by (5.2), which gives (11.1).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

/-- The sides of a fragment over `side`. -/
def sidesOver {Y : Type} [TopologicalSpace Y] (χ : ColourScheme S β) (K : Drawing S) (ψ : Y → S)
  (side : Set S) (c : Set Y) : Set (Set c) :=
  {R ∈ arcComponentsIn (bd c \ pullFrameV χ.Φ K (fun x : c ↦ ψ x.1)) |
    (fun x : c ↦ ψ x.1) '' R ⊆ side}

/-- A label on each side of a fragment over `side`, chosen from `ω`, and no label on the other
sides. -/
def IsSideLabelling {Y : Type} [TopologicalSpace Y] (χ : ColourScheme S β) (K : Drawing S) (ψ : Y
  → S) (side : Set S) (ω : List β) (c : Set Y) (lab : Set c → Option β) : Prop :=
  ∀ R, (R ∈ sidesOver χ K ψ side c → ∃ w ∈ ω, lab R = some w) ∧ (R ∉ sidesOver χ K ψ side c → lab R
    = none)

omit [T2Space S] in
theorem finite_isSideLabelling {Y : Type} [TopologicalSpace Y] {K : Drawing S} {ψ : Y
  → S} {side : Set S} (ω : List β) {c : Set Y} (hf : (sidesOver χ K ψ side c).Finite) :
    {lab | IsSideLabelling χ K ψ side ω c lab}.Finite := by
  classical
  have := hf.to_subtype
  have hT : (insert none (some '' {w | w ∈ ω}) : Set (Option β)).Finite :=
    (ω.finite_toSet.image _).insert _
  have := hT.to_subtype
  let Φ' : (↥(sidesOver χ K ψ side c) → ↥(insert none (some '' {w | w ∈ ω}) : Set (Option β)))
    → Set c → Option β := fun g R ↦ if h : R ∈ sidesOver χ K ψ side c then (g ⟨R, h⟩).1 else none
  refine (finite_range Φ').subset fun lab hlab ↦ ?_
  have hmem : ∀ R, R ∈ sidesOver χ K ψ side c → lab R ∈ (insert none (some '' {w | w ∈ ω}) : Set
    (Option β)) := fun R hR ↦ by
    obtain ⟨w, hw, he⟩ := (hlab R).1 hR
    exact he ▸ Or.inr ⟨w, hw, rfl⟩
  refine ⟨fun R ↦ ⟨lab R.1, hmem R.1 R.2⟩, funext fun R ↦ ?_⟩
  by_cases h : R ∈ sidesOver χ K ψ side c
  · simp [Φ', h]
  · simp [Φ', h, (hlab R).2 h]

/-- One well-behaved set for the flaws on `side` with a given feature. -/
theorem exists_class_side (hS : IsSurface S) (hd : χ.IsDisjoint) {𝒮 : Set (ColouredPainting χ)}
  (hcl : IsPaintingClass χ 𝒮) (N : ℕ) (a₀ : β)
    (hS4 : ConditionS4 χ) {side : Set S} (hside : side ∈ χ.Φ.longSides) {ω : List β}
      (hωE : ∀ x ∈ ω, x ∈ (χ.ΩS side).E) (hpos : 0 < N) {Kc : Drawing S}
    (hg : ∃ (D : TangleDatum cap χ) (𝓓 : Set (Set Shat)) (Z : Set Shat), IsSideData D side N ω 𝓓 Z
      Kc) :
    ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → N ≤ D.ord →
      ∀ (𝓓 : Set (Set Shat)) (Z : Set Shat) (K : Drawing S) (α : S ≃ₜ S), IsSideData D side N ω 𝓓 Z
        K → IsFramePreservingHomeo χ.Φ α →
      α '' Kc.U = K.U → α '' Kc.V = K.V →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb N D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ B := by
  classical
  have : ConnectedSpace S := χ.connected
  have hT := cap.isClosedSurface
  obtain ⟨D₀, 𝓓₀, Z₀, hp⟩ := hg
  have hKne : Kc.V ⊆ ⋃ e ∈ arcComponentsIn (Kc.U \ Kc.V), closure e := fun v hv ↦ by
    obtain ⟨e, he, hve⟩ := hp.feature.no_isolated_vertices v hv
    exact mem_biUnion he hve.1
  obtain ⟨𝓞, 𝓛, h𝓞, h𝓛, hO, hL, hU⟩ := hp.pieces
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hsheet, -⟩ := exists_pullData_of_shape hS D₀.P.fits hp.inter
    hp.lines hKne h𝓞 h𝓛 hO hL hU
  have hFD := fun y ↦ frameData_of_cut hS D₀.P.fits hp.inter hp.lines hY hψ hsheet y
  have hfinite : ∀ y, (sidesOver χ Kc ψ side (connectedComponent y)).Finite := fun y ↦
    (finite_arcComponentsIn_bd (hFD y).pull.frag.isSurface (hFD y).finite_pullFrameV
      (hFD y).two).subset fun _ h ↦ h.1
  let Q : Set Y → Place χ → Prop := fun c X ↦ ∃ lab, IsSideLabelling χ Kc ψ side ω c lab ∧ X.P ∈ 𝒮 ∧
    ∀ R w, lab R = some w → ∀ e ∈ X.P.Γ.E, e ⊆ (fun x : c ↦ ψ x.1) '' R → ¬ (χ.ΩS side).le w
      (X.P.φ e)
  obtain ⟨B, hB, hmem⟩ := exists_class_cut_on (χ := χ) (K := Kc) hY (ψ := ψ) (ω.length + 1)
    (fun c ↦ OuterGood χ.Φ side Kc ψ c) Q
    (fun y l h ↦ by
      have := (finite_isSideLabelling (χ := χ) (K := Kc) (ψ := ψ) (side := side) ω
        (hfinite y)).to_subtype
      let C : {lab | IsSideLabelling χ Kc ψ side ω (connectedComponent y) lab} → Set (Place χ)
        := fun lab ↦ {X | IsCutPlace χ Kc (fun x : connectedComponent y ↦ ψ x.1) l (ω.length + 1) X
          ∧ X.P ∈ 𝒮 ∧
          ∀ R w, lab.1 R = some w → ∀ e ∈ X.P.Γ.E, e ⊆ (fun x : connectedComponent y ↦ ψ x.1) '' R
            → ¬ (χ.ΩS side).le w (X.P.φ e)}
      have h₀ : ∀ lab, IsWellBehavedPlaces (C lab) := fun lab ↦
        wellBehaved_side hS hp.feature hcl hp.lines hY hψ hsheet y l (ω.length + 1) a₀ hS4 h.2.1
          h.2.2.1 h.1 hside (lab := lab.1)
          (fun R hn ↦ (lab.2 R).2 fun hR ↦ hn hR.2) (fun R hR hsub ↦ by
            obtain ⟨w, hw, he⟩ := (lab.2 R).1 ⟨hR, hsub⟩
            exact ⟨w, hωE w hw, he⟩) h.2.2.2
      intro γ Ω hΩ seq hseq ξ hξ
      refine IsWellBehavedPlaces.iUnion h₀ Ω hΩ seq (fun i ↦ ?_) ξ hξ
      obtain ⟨hX, lab, hlab, hm, hcol⟩ := hseq i
      exact mem_iUnion.2 ⟨⟨lab, hlab⟩, hX, hm, hcol⟩)
  refine ⟨_, theorem_9_4_proof hB, ?_⟩
  rintro D hmem𝒮 hord 𝓓 Z K α hK hα hαU hαV
  obtain ⟨y, hy, hgood⟩ := outer_fragment hS (cap.ofHomeo α) (hK.shape.ofHomeo α hα hαU) hY hψ
  have hfin : (Kc.V ∩ α ⁻¹' D.P.Γ.V).Finite := Kc.finite_V.subset inter_subset_left
  let Q' : ColouredPainting χ := D.P.image α.symm hα.symm
  have hQ : IsColouredImage α.symm D.P Q' := ColouredPainting.isImage_image _ _ _
  have I : IsColouredImage α Q' D.P := hQ.symm
  have hrange : range (fun x : connectedComponent y ↦ ψ x.1) = α ⁻¹' ⋂ p ∈ discPairs cap 𝓓,
    Prod.snd p := by
    have : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
      ext z
      simp
    rw [this, hy, iInter_discPairs]
    ext x
    have hint : cap.emb (α x) ∈ discInt Z ↔ ∃ Δ ∈ 𝓓, cap.emb (α x) ∈ discInt Δ := by
      have := Set.ext_iff.1 hK.int_eq (α x)
      simpa using this
    have hcl' : ∀ Δ ∈ 𝓓, (cap.emb (α x) ∈ closure Δᶜ ↔ cap.emb (α x) ∉ discInt Δ) := fun Δ hΔ ↦ by
      rw [closure_compl_eq_compl_discInt hT (hK.discs Δ hΔ)]
      rfl
    simp only [mem_compl_iff, mem_iInter, mem_preimage]
    change ¬ cap.emb (α x) ∈ discInt Z ↔ _
    rw [hint]
    constructor
    · exact fun h Δ hΔ ↦ (hcl' Δ hΔ).2 fun hi ↦ h ⟨Δ, hΔ, hi⟩
    · rintro h ⟨Δ, hΔ, hi⟩
      exact (hcl' Δ hΔ).1 (h Δ hΔ) hi
  have hinter : Q'.Γ.U ∩ Kc.U ⊆ Q'.Γ.V ∩ Kc.V := by
    rintro x ⟨hx₁, hx₂⟩
    rw [hQ.U] at hx₁
    obtain ⟨y', hy', rfl⟩ := hx₁
    have hyK : y' ∈ K.U := by
      rw [← hαU]
      exact ⟨_, hx₂, α.apply_symm_apply y'⟩
    obtain ⟨h₁, h₂⟩ := hK.inter ⟨hy', hyK⟩
    refine ⟨?_, ?_⟩
    · rw [hQ.V]
      exact mem_image_of_mem _ h₁
    · rw [← hαV] at h₂
      obtain ⟨z, hz, rfl⟩ := h₂
      rwa [α.symm_apply_apply]
  have hl : ∀ v, v ∈ hfin.toFinset.toList ↔ v ∈ Kc.V ∩ Q'.Γ.V := fun v ↦ by
    rw [Finset.mem_toList, hfin.mem_toFinset, hQ.V]
    refine ⟨fun h ↦ ⟨h.1, _, h.2, α.symm_apply_apply v⟩, ?_⟩
    rintro ⟨h₁, u, hu, rfl⟩
    exact ⟨h₁, by simpa using hu⟩
  have hr : ∀ v, v ∈ Kc.U → v ∈ range (fun x : connectedComponent y ↦ ψ x.1) := fun v hv ↦ by
    rw [hrange]
    have hvK : α v ∈ K.U := hαU ▸ mem_image_of_mem _ hv
    rw [mem_preimage, iInter_discPairs]
    exact mem_iInter₂.2 fun Δ' hΔ' ↦ hK.outer _ hvK Δ' hΔ'
  have hπ : ∀ p ∈ discPairs cap 𝓓, ∀ v ∈ D.P.Γ.V, v ∈ p.1 → v ∈ p.2 → α.symm v ∈ Kc.U := by
    rintro _ ⟨Δ', hΔ', rfl⟩ v hv h₁ h₂
    have := hK.roots Δ' hΔ' v hv h₁ h₂
    rw [← hαU] at this
    obtain ⟨z, hz, rfl⟩ := this
    rwa [α.symm_apply_apply]
  have hm : (discPairs cap 𝓓).ncard ≤ ω.length + 1 := (ncard_image_le hK.finite).trans hK.card
  have hanc : IsAnchored Q'.Γ Kc := hK.anchored.image hαU I.V
  obtain ⟨X, hXP, hX, hXim⟩ := hK.family.exists_place (K := Kc) hd hα I hrange hinter hanc hl hr hπ
    hm
  have hX𝒮 : X.P ∈ 𝒮 := hXP ▸ hcl.image_mem _ hmem𝒮 _ _ hα.symm hQ
  set ψc : connectedComponent y → S := fun x ↦ ψ x.1 with hψc
  have hψcc : Continuous ψc := hψ.1.comp continuous_subtype_val
  have hαside : ∀ {x}, x ∈ side → α x ∈ side := fun {x} hx ↦ by
    have := hα.preserve_sides side hside.1
    exact this ▸ mem_image_of_mem α hx
  have hchoose : ∀ R : Set (connectedComponent y), ∃ o : Option β, (R ∈ sidesOver χ Kc ψ side
    (connectedComponent y) → ∃ w ∈ ω, o = some w ∧ ∀ e ∈ D.P.Γ.E, e ⊆ α '' (ψc '' R) → ¬
      (χ.ΩS side).le w (D.P.φ e)) ∧
      (R ∉ sidesOver χ Kc ψ side (connectedComponent y) → o = none) := fun R ↦ by
    by_cases hR : R ∈ sidesOver χ Kc ψ side (connectedComponent y)
    · have hconn : IsPreconnected (α '' (ψc '' R)) := (hR.1.2.2.1.isConnected.isPreconnected.image
        _ hψcc.continuousOn).image _ α.continuous.continuousOn
      have hsubB : α '' (ψc '' R) ⊆ side \ (cap.emb ⁻¹' discInt Z ∪ K.U) := by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        have hxside : ψc x ∈ side := hR.2 (mem_image_of_mem _ hx)
        refine ⟨hαside hxside, ?_⟩
        rintro (hi | hk)
        · have hmr : ψ x.1 ∈ ψ '' connectedComponent y := mem_image_of_mem _ x.2
          rw [hy] at hmr
          exact hmr hi
        · rw [← hαU] at hk
          obtain ⟨z, hz, he⟩ := hk
          obtain rfl := α.injective he
          have hb : ψc x ∈ bd S := (hside.1.2.1 hxside).1
          exact (hR.1.2.1 hx).2 (Or.inr ((hFD y).K_bd ⟨hz, hb⟩))
      obtain ⟨h, hh, hall⟩ := hK.omits _ hsubB hconn
      exact ⟨some ω[h], fun _ ↦ ⟨ω[h], List.getElem_mem hh, rfl, hall⟩, fun hn ↦ absurd hR hn⟩
    · exact ⟨none, fun h ↦ absurd h hR, fun _ ↦ rfl⟩
  choose lab hlab using hchoose
  have hQc : Q (connectedComponent y) X := by
    refine ⟨lab, fun R ↦ ⟨fun hR ↦ ?_, (hlab R).2⟩, hX𝒮, fun R w hw e he hsub ↦ ?_⟩
    · obtain ⟨w, hw, he, -⟩ := (hlab R).1 hR
      exact ⟨w, hw, he⟩
    · have hR : R ∈ sidesOver χ Kc ψ side (connectedComponent y) := by
        by_contra hn
        rw [(hlab R).2 hn] at hw
        exact absurd hw (by simp)
      obtain ⟨w', -, hw', hall⟩ := (hlab R).1 hR
      obtain rfl : w = w' := by
        rw [hw'] at hw
        exact (Option.some.inj hw).symm
      rw [hXP] at he ⊢
      have heE : e ∈ (D.P.Γ.push α.symm).E := he
      rw [push_E] at heE
      obtain ⟨c, hc, rfl⟩ := heE
      rw [hQ.φ c hc]
      refine hall c hc fun z hz ↦ ?_
      exact ⟨α.symm z, hsub (mem_image_of_mem _ hz), α.apply_symm_apply z⟩
  refine ⟨hK.family.location, hK.family.isolates hS hpos hord, X, hmem y _ X hgood ?_ hX hQc, α,
    hXim⟩
  exact fun v hv ↦ ((hl v).1 hv).1

/-- **Graph Minors XIX, (11.1)** (page 358):
"**11.1.** *Let $\chi$ satisfy $S_4$, let $S$ be a long side of $\Phi_\chi$, let
$\omega_1, \dots, \omega_m \in E(\Omega_\chi(S))$ with $m \ge 1$, and let $n \ge 4$. Then there is
a well-behaved set $\mathscr{C}_4(S, (\omega_1, \dots, \omega_m), n)$ of $\chi$-places with the
following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ be
$(n, (\omega_1, \dots, \omega_m))$-flawed on $S$. Then there is a rooted location $\mathscr{L}$
which $(m + 1)n$-isolates $\mathscr{T}$, and for which
$(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}_4(S, (\omega_1, \dots, \omega_m), n)$.*" -/
theorem theorem_11_1_proof : Theorem111Statement.{w} := by
  intro S Shat _ _ _ _ β _ cap χ hd 𝒮 hcl hS4 side hside ω hω hωE n hn
  classical
  have hS := χ.isSurface
  have : ConnectedSpace S := χ.connected
  let a₀ : β := Classical.arbitrary β
  set N := (ω.length + 1) * n with hN
  have hpos : 0 < N := by positivity
  let Data : TangleDatum cap χ → Drawing S → Prop :=
    fun D K => ∃ (𝓓 : Set (Set Shat)) (Z : Set Shat), IsSideData D side N ω 𝓓 Z K
  obtain ⟨B, hB, hMem⟩ := exists_wellBehavedPlaces_of_bounded_features hd (𝒮 := 𝒮)
    (8 * N) N Data (fun Kc hGood => by
      obtain ⟨B, hB, hMem⟩ :=
        exists_class_side hS hd hcl N a₀ hS4 hside hωE hpos (Kc := Kc) hGood
      refine ⟨B, hB, ?_⟩
      rintro D hm hord K ⟨𝓓, Z, hData⟩ ⟨f, hfp, hfU, hfV⟩
      exact hMem D hm hord 𝓓 Z K f hData hfp hfU hfV)
  refine ⟨B, hB, fun D hm hfl => ?_⟩
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨r, Θ, ℱ, X, hflaw, hsm, hlink, hmin⟩ := TangleDatum.exists_side_flaw hS h3 hside hn hω hfl
  obtain ⟨𝓓, Z, K, hK⟩ := X.exists_side_data hS hfl.2.1 rfl hpos hflaw hsm hlink hmin hω
  have hord : N ≤ D.ord := by
    have h₁ := X.rep_gt
    have h₂ : D.rep ≤ D.ord := (tangleRep_spec D.rad D.ord D.𝒯).1
    omega
  exact hMem D hm hord K ⟨𝓓, Z, hK⟩ hK.feature hK.size

end GraphMinor.GM19
