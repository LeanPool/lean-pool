/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section4c

/-!
# Graph Minors XI, Section 5: small sets, (5.1)–(5.3)

Throughout, `Γ` is a drawing in a connected closed surface with a slope `ins`, and `(Ω, ω)` is a
weighting.

(5.1) says that regions of `Γ` in one region of a subdrawing `Γ'` are linked by edges not in `Γ'`.
The paper gives this as a sequence of regions. To supply it, we delete the edges of `E(Γ) - E(Γ')`
one at a time: each deletion merges only the regions at that edge. When no edges are left, `Γ` and
`Γ'` differ only in finitely many vertices, and these do not separate a region.

(5.2) and (5.3) follow the paper.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- An open connected subset of a closed surface stays connected when finitely many points are
removed. -/
theorem isPreconnected_sdiff_finite (hS : IsClosedSurface S) {G F : Set S} (hG : IsOpen G)
    (hGc : IsPreconnected G) (hF : F.Finite) : IsPreconnected (G \ F) := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction F, hF using Set.Finite.induction_on with
  | empty => simpa using hGc
  | @insert x F hxF hF ih =>
    have hEq : G \ insert x F = (G \ F) \ {x} := by
      ext y
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
      tauto
    rw [hEq]
    by_cases hx : x ∈ G \ F
    · have hG' : IsOpen (G \ F) := hG.sdiff hF.isClosed
      obtain ⟨Z, hZ, hxZ, hZG, hZc, hZcl⟩ := exists_punctured_nbhd hS hG' hx
      obtain ⟨a, haZ⟩ : (Z \ {x}).Nonempty := by
        by_contra hcon
        rw [not_nonempty_iff_eq_empty] at hcon
        rw [hcon, closure_empty] at hZcl
        exact hZcl
      have hcl : IsClosed ((G \ F)ᶜ ∪ {x}) := hG'.isClosed_compl.union isClosed_singleton
      refine isPreconnected_sdiff_of_local hG' ih hcl ⟨x, hx, rfl⟩ ⟨hZG haZ.1, haZ.2⟩ ?_
      rintro y hy ⟨t, ⟨-, ht⟩, htc⟩
      obtain rfl : t = x := ht
      obtain ⟨b, hbZ, hbC⟩ := mem_closure_iff.mp htc Z hZ hxZ
      have hbne : b ≠ t := (connectedComponentIn_subset _ _ hbC).2
      rw [connectedComponentIn_eq hbC]
      refine hZc.subset_connectedComponentIn ⟨hbZ, hbne⟩ ?_ haZ
      exact fun q hq => ⟨hZG hq.1, hq.2⟩
    · have : (G \ F) \ {x} = G \ F := by
        ext y
        constructor
        · exact fun h => h.1
        · intro hy
          exact ⟨hy, fun h => hx (by rw [← mem_singleton_iff.mp h]; exact hy)⟩
      rw [this]
      exact ih

variable [T2Space S] {Γ : Drawing S}

theorem deleteEdge_V (Γ : Drawing S) (e : Set S) : (Γ.deleteEdge e).V = Γ.V := by
  apply subset_antisymm (Drawing.span_isSubdrawing Γ _ _).1
  intro x hx
  exact Or.inl ⟨hx, hx⟩

/-- Graph Minors XI, (5.1) (page 81): "Let $Z \subseteq R(\Gamma)$, and let $\Gamma' \subseteq
\Gamma$. Let $r'$ be a region of
$\Gamma'$. If there are regions $r_1 \in Z$, $r_2 \in R(\Gamma) - Z$ with $r_1, r_2
\subseteq r'$, then there are such regions $r_1, r_2$ which in addition are incident with
some edge $e$ of $\Gamma$ with $e \notin E(\Gamma')$." -/
theorem theorem_5_1_proof (hS : IsClosedSurface S)
    {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) {Z : Set (Set S)}
    {r' r₁ r₂ : Set S} (hr' : r' ∈ Γ'.R) (h₁ : r₁ ∈ Γ.R) (hz₁ : r₁ ∈ Z) (h₂ : r₂ ∈ Γ.R)
    (hz₂ : r₂ ∉ Z) (hs₁ : r₁ ⊆ r') (hs₂ : r₂ ⊆ r') :
    ∃ e ∈ Γ.E, e ∉ Γ'.E ∧ ∃ a b : Set S, a ∈ Z ∧ b ∉ Z ∧ a ⊆ r' ∧ b ⊆ r' ∧
      Γ.EdgeRegionIncident e a ∧ Γ.EdgeRegionIncident e b := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction hn : (Γ.E \ Γ'.E).ncard using Nat.strong_induction_on generalizing Γ Z r₁ r₂ with
  | _ n ih =>
    by_cases hE : (Γ.E \ Γ'.E).Nonempty
    · obtain ⟨e, heΓ, heΓ'⟩ := hE
      have hdel := deleteEdge_isSubdrawing Γ e
      have hUe := deleteEdge_U Γ heΓ
      have hsub'' : Γ'.IsSubdrawing (Γ.deleteEdge e) := by
        refine ⟨by rw [deleteEdge_V]; exact hsub.1, ?_⟩
        rw [deleteEdge_E]
        exact fun f hf => ⟨hsub.2 hf, fun hfe => heΓ' (hfe ▸ hf)⟩
      by_cases hA : ∃ a b : Set S, a ∈ Γ.R ∧ b ∈ Γ.R ∧ a ∈ Z ∧ b ∉ Z ∧ a ⊆ r' ∧ b ⊆ r' ∧
          e ⊆ closure a ∧ e ⊆ closure b
      · obtain ⟨a, b, ha, hb, haZ, hbZ, has, hbs, hia, hib⟩ := hA
        obtain ⟨p, hp⟩ := heΓ.1
        exact ⟨e, heΓ, heΓ', a, b, haZ, hbZ, has, hbs, ⟨heΓ, ha, p, hp, hia hp⟩,
          ⟨heΓ, hb, p, hp, hib hp⟩⟩
      push Not at hA
      -- Regions of `Γ` in one region of `Γ - e` inside `r'` are all in `Z` or all outside it.
      have hsame : ∀ s ∈ (Γ.deleteEdge e).R, s ⊆ r' → ∀ c ∈ Γ.R, ∀ d ∈ Γ.R, c ⊆ s → d ⊆ s →
          c ∈ Z → d ∈ Z := by
        intro s hs hsr c hc d hd hcs hds hcZ
        by_contra hdZ
        have hne : c ≠ d := fun h => hdZ (h ▸ hcZ)
        have honly : ∀ {t u : Set S}, t ∈ Γ.R → u ∈ Γ.R → t ⊆ s → u ⊆ s → t ≠ u →
            e ⊆ closure t := by
          intro t u ht hu hts hus htu
          rcases edge_incident_or_disjoint hS heΓ ht with h | h
          · exact h
          · exfalso
            have htdel := region_deleteEdge_of_not_incident heΓ ht h
            obtain ⟨x, hx⟩ := region_nonempty ht
            have hts' : t = s := region_eq_of_mem htdel hs hx (hts hx)
            obtain ⟨y, hy⟩ := region_nonempty hu
            exact htu (region_eq_of_mem ht hu (hts' ▸ hus hy) hy)
        exact hA c d hc hd hcZ hdZ (hcs.trans hsr) (hds.trans hsr) (honly hc hd hcs hds hne)
          (honly hd hc hds hcs hne.symm)
      -- A region of `Γ - e` that meets `r'` lies in `r'`.
      have hinr : ∀ s ∈ (Γ.deleteEdge e).R, ∀ z : Set S, z.Nonempty → z ⊆ s → z ⊆ r' → s ⊆ r' := by
        intro s hs z ⟨x, hx⟩ hzs hzr
        refine subset_region hr' (region_isPreconnected hs) ?_ (hzs hx) (hzr hx)
        exact disjoint_left.mpr fun y hy h => region_subset hs hy (hsub''.U_subset h)
      let Z'' : Set (Set S) := {s | ∃ z ∈ Γ.R, z ∈ Z ∧ z ⊆ r' ∧ z ⊆ s}
      obtain ⟨s₁, hs₁', hs₁s⟩ := exists_region_superset hdel h₁
      obtain ⟨s₂, hs₂', hs₂s⟩ := exists_region_superset hdel h₂
      have hs₂r : s₂ ⊆ r' := hinr s₂ hs₂' r₂ (region_nonempty h₂) hs₂s hs₂
      have hs₁Z : s₁ ∈ Z'' := ⟨r₁, h₁, hz₁, hs₁, hs₁s⟩
      have hs₂Z : s₂ ∉ Z'' := by
        rintro ⟨z, hz, hzZ, -, hzs⟩
        exact hz₂ (hsame s₂ hs₂' hs₂r z hz r₂ h₂ hzs hs₂s hzZ)
      have hlt : ((Γ.deleteEdge e).E \ Γ'.E).ncard < n := by
        have hEq : (Γ.deleteEdge e).E \ Γ'.E = (Γ.E \ Γ'.E) \ {e} := by
          rw [deleteEdge_E]
          ext f
          simp only [mem_sdiff, mem_singleton_iff]
          tauto
        rw [hEq, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem ⟨heΓ, heΓ'⟩
          (Γ.finite_edges.subset sdiff_subset)
      obtain ⟨e', he', he'Γ', a, b, haZ, hbZ, has, hbs, hia, hib⟩ :=
        ih _ hlt hsub'' hs₁' hs₁Z hs₂' hs₂Z
          ((hinr s₁ hs₁' r₁ (region_nonempty h₁) hs₁s hs₁)) hs₂r rfl
      have he'Γ : e' ∈ Γ.E := hdel.2 he'
      have he'e : e' ≠ e := by
        have := he'
        rw [deleteEdge_E] at this
        exact this.2
      -- A region of `Γ - e` incident with `e'` contains a region of `Γ` incident with `e'`.
      have hlift : ∀ s ∈ (Γ.deleteEdge e).R, (e' ∩ closure s).Nonempty →
          ∃ c ∈ Γ.R, c ⊆ s ∧ Γ.EdgeRegionIncident e' c := by
        rintro s hs ⟨p, hpe, hps⟩
        obtain ⟨W, A₁, A₂, hW, hpW, hWU, hcov, c₁, c₂, d₁, d₂, cl₁, cl₂⟩ :=
          exists_edge_sides hS Γ he'Γ hpe
        obtain ⟨x, hxW, hxs⟩ := mem_closure_iff.mp hps W hW hpW
        have hxU'' := region_subset hs hxs
        have hxU : x ∉ Γ.U := by
          intro hxU
          have hxe' : x ∈ e' := hWU ⟨hxW, hxU⟩
          have hxe : x ∉ e := fun hxe => he'e (Γ.edge_eq_of_mem he'Γ heΓ hxe' hxe)
          exact hxU'' (by rw [hUe]; exact ⟨hxU, hxe⟩)
        obtain ⟨c, hc, hxc⟩ := exists_region_of_notMem hxU
        have hcs : c ⊆ s := subset_region hs (region_isPreconnected hc)
          (disjoint_left.mpr fun y hy h => region_subset hc hy (hdel.U_subset h)) hxc hxs
        refine ⟨c, hc, hcs, he'Γ, hc, p, hpe, ?_⟩
        rcases hcov ⟨hxW, hxU⟩ with hx | hx
        · exact closure_mono (subset_region hc c₁ d₁ hx hxc) (cl₁ ⟨hpe, hpW⟩)
        · exact closure_mono (subset_region hc c₂ d₂ hx hxc) (cl₂ ⟨hpe, hpW⟩)
      obtain ⟨c, hc, hca, hic⟩ := hlift a hia.2.1 hia.2.2
      obtain ⟨d, hd, hdb, hid⟩ := hlift b hib.2.1 hib.2.2
      obtain ⟨z, hz, hzZ, hzr, hza⟩ := haZ
      have hcZ : c ∈ Z := hsame a hia.2.1 has z hz c hc hza hca hzZ
      have hdZ : d ∉ Z := fun h => hbZ ⟨d, hd, h, hdb.trans hbs, hdb⟩
      exact ⟨e', he'Γ, he'Γ', c, d, hcZ, hdZ, hca.trans has, hdb.trans hbs, hic, hid⟩
    · -- Now `Γ` and `Γ'` have the same edges, and only vertices separate `r'`.
      exfalso
      have hEsub : Γ.E ⊆ Γ'.E := by
        intro f hf
        by_contra hf'
        exact hE ⟨f, hf, hf'⟩
      have hconn : IsPreconnected (r' \ Γ.V) :=
        isPreconnected_sdiff_finite hS (region_isOpen hr') (region_isPreconnected hr') Γ.finite_V
      have hdisj : Disjoint (r' \ Γ.V) Γ.U := by
        refine disjoint_left.mpr fun x hx hxU => ?_
        obtain ⟨f, hf, hxf⟩ := Γ.exists_edge_of_mem hxU hx.2
        exact region_subset hr' hx.1 ((Γ'.closure_subset_U (hEsub hf)) (subset_closure hxf))
      have hin : ∀ {r : Set S}, r ∈ Γ.R → r ⊆ r' → r ⊆ r' \ Γ.V := fun hr hrr x hx =>
        ⟨hrr hx, fun hxV => region_subset hr hx (Γ.V_subset_U hxV)⟩
      obtain ⟨x, hx⟩ := region_nonempty h₁
      obtain ⟨y, hy⟩ := region_nonempty h₂
      have hy₁ : y ∈ r₁ := subset_region h₁ hconn hdisj (hin h₁ hs₁ hx) hx (hin h₂ hs₂ hy)
      exact hz₂ (region_eq_of_mem h₁ h₂ hy₁ hy ▸ hz₁)

/-- A subdrawing `N(Z)` with small weight is confined: a long circuit would have weight at least
`ω`, by the definition of a weighting. -/
theorem boundaryDrawing_isConfined {k ω : ℕ} {Ω : Set S} {Z : Set (Set S)}
    (hw : IsWeighting Γ k Ω ω) (hlt : (Ω ∩ (boundaryDrawing Γ Z).V).ncard < ω) :
    IsConfined k (boundaryDrawing Γ Z) := by
  intro C hC hCs
  by_contra hcon
  have hsub : (boundaryDrawing Γ Z).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have h₁ := hw.le_ncard C hC (hCs.trans hsub) (not_lt.mp hcon)
  have hfin : (Ω ∩ (boundaryDrawing Γ Z).V).Finite :=
    (Γ.finite_V.subset hw.subset).subset inter_subset_left
  have h₂ : (Ω ∩ C.V).ncard ≤ (Ω ∩ (boundaryDrawing Γ Z).V).ncard :=
    Set.ncard_le_ncard (inter_subset_inter_right _ hCs.1) hfin
  omega

theorem boundaryDrawing_compl {Z : Set (Set S)} (hZ : Z ⊆ Γ.R) :
    boundaryDrawing Γ (Γ.R \ Z) = boundaryDrawing Γ Z := by
  have hEq : Γ.R \ (Γ.R \ Z) = Z := by
    ext r
    constructor
    · rintro ⟨h₁, h₂⟩
      by_contra h
      exact h₂ ⟨h₁, h⟩
    · exact fun h => ⟨hZ h, fun h' => h'.2 h⟩
  unfold boundaryDrawing
  rw [hEq]
  simp only [and_comm]

/-- `N(Z)` has the edges incident with a member of `Z` and with a region outside `Z`. -/
theorem mem_boundaryDrawing_E {Z : Set (Set S)} {e : Set S} :
    e ∈ (boundaryDrawing Γ Z).E ↔ (∃ r ∈ Z, Γ.EdgeRegionIncident e r) ∧
      ∃ r ∈ Γ.R \ Z, Γ.EdgeRegionIncident e r := by
  unfold boundaryDrawing
  rw [Γ.span_E]
  constructor
  · exact fun h => h.1
  · rintro ⟨h₁, h₂⟩
    obtain ⟨r, hrZ, hr⟩ := h₁
    exact ⟨⟨⟨r, hrZ, hr⟩, h₂⟩, hr.1⟩

/-- Graph Minors XI, (5.2) (page 81): "If $Z \subseteq R(\Gamma)$ and $|\Omega \cap V(N(Z))| <
\omega$, then exactly one of $Z$,
$R(\Gamma) - Z$ is small." -/
theorem theorem_5_2_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {k ω : ℕ} {ins : Drawing S → Set S} {Ω : Set S}
    {Z : Set (Set S)} (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) (hZ : Z ⊆ Γ.R)
    (hlt : (Ω ∩ (boundaryDrawing Γ Z).V).ncard < ω) :
    (IsSmall Γ ins k Ω ω Z ∨ IsSmall Γ ins k Ω ω (Γ.R \ Z)) ∧
      ¬ (IsSmall Γ ins k Ω ω Z ∧ IsSmall Γ ins k Ω ω (Γ.R \ Z)) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set N := boundaryDrawing Γ Z with hN
  have hsub : N.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hconf : IsConfined k N := boundaryDrawing_isConfined hw hlt
  have hcomp : boundaryDrawing Γ (Γ.R \ Z) = N := boundaryDrawing_compl hZ
  have hr₀ := theorem_4_4_proof hS hs hsub hconf
  set r₀ := univ \ insOf ins N with hr₀def
  have hnotcap : ∀ r : Set S, r.Nonempty → r ⊆ r₀ → ¬ Captures ins k N r := by
    rintro r ⟨x, hx⟩ hrr ⟨C, hC, hCs, -, hin⟩
    exact (hrr hx).2 (Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hin hx⟩))
  -- A region of `Γ` is captured by `N(Z)` unless it lies in `r₀`.
  have hcap : ∀ r ∈ Γ.R, ¬ Captures ins k N r → r ⊆ r₀ := by
    intro r hr hnot
    obtain ⟨r', hr', hrr'⟩ := exists_region_superset hsub hr
    by_cases he : r' = r₀
    · exact he ▸ hrr'
    · exfalso
      obtain ⟨x, hx⟩ := region_nonempty hr
      rcases captures_of_ne hS hs hsub hconf hr' hr₀ he with
        ⟨C, hC, hCs, hl, hin⟩ | h
      · exact hnot ⟨C, hC, hCs, hl, hrr'.trans hin⟩
      · exact hnotcap r₀ (region_nonempty hr₀) subset_rfl h
  constructor
  · by_contra hcon
    push Not at hcon
    obtain ⟨hnZ, hnc⟩ := hcon
    have hexists : ∀ {Y : Set (Set S)}, boundaryDrawing Γ Y = N → ¬ IsSmall Γ ins k Ω ω Y →
        ∃ r ∈ Y, ¬ Captures ins k N r := by
      intro Y hY hnot
      by_contra hall
      push Not at hall
      refine hnot ⟨by rw [hY]; exact hlt, ?_⟩
      rw [hY]
      exact hall
    obtain ⟨r₁, hr₁, hn₁⟩ := hexists rfl hnZ
    obtain ⟨r₂, hr₂, hn₂⟩ := hexists hcomp hnc
    obtain ⟨e, -, heN, a, b, haZ, hbZ, -, -, hia, hib⟩ :=
      theorem_5_1_proof hS hsub hr₀ (hZ hr₁) hr₁ hr₂.1 hr₂.2 (hcap _ (hZ hr₁) hn₁)
        (hcap _ hr₂.1 hn₂)
    exact heN (mem_boundaryDrawing_E.mpr ⟨⟨a, haZ, hia⟩, b, ⟨hib.2.1, hbZ⟩, hib⟩)
  · rintro ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
    rw [hcomp] at h₂
    obtain ⟨y, hy⟩ := region_nonempty hr₀
    have hO : IsOpen r₀ := region_isOpen hr₀
    obtain ⟨z, hz, hzU⟩ := exists_notMem_U (Γ := Γ) hS hO ⟨y, hy⟩
    obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
    have hrr₀ : r ⊆ r₀ := subset_region hr₀ (region_isPreconnected hr)
      (disjoint_left.mpr fun q hq h => region_subset hr hq (hsub.U_subset h)) hzr hz
    by_cases hrZ : r ∈ Z
    · exact hnotcap r (region_nonempty hr) hrr₀ (h₁ r hrZ)
    · exact hnotcap r (region_nonempty hr) hrr₀ (h₂ r ⟨hr, hrZ⟩)

/-- Graph Minors XI, (5.3) (page 82): "If $Z \subseteq R(\Gamma)$ is small, $Z' \subseteq Z$, and
$|\Omega \cap V(N(Z'))| <
\omega$, then $Z'$ is small." -/
theorem theorem_5_3_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {k ω : ℕ} {ins : Drawing S → Set S} {Ω : Set S}
    {Z Z' : Set (Set S)} (hs : IsSlope Γ k ins) (hw : IsWeighting Γ k Ω ω) (hZ : Z ⊆ Γ.R)
    (hsm : IsSmall Γ ins k Ω ω Z) (hZ' : Z' ⊆ Z)
    (hlt : (Ω ∩ (boundaryDrawing Γ Z').V).ncard < ω) : IsSmall Γ ins k Ω ω Z' := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine ⟨hlt, fun r hr => ?_⟩
  obtain ⟨C, hC, hCN, hl, hin⟩ := hsm.2 r (hZ' hr)
  have hNs : (boundaryDrawing Γ Z).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hN's : (boundaryDrawing Γ Z').IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hCs := hCN.trans hNs
  have hconf := boundaryDrawing_isConfined hw hlt
  have hrR : r ∈ Γ.R := hZ (hZ' hr)
  obtain ⟨r', hr', hrr'⟩ := exists_region_superset hN's hrR
  have hΔ : IsClosed (ins C) := (hs.isClosedDisc C hC hCs hl).isClosed
  -- The claim of the paper: `r' ⊆ ins(C)`.
  have hclaim : r' ⊆ ins C := by
    by_contra hcon
    obtain ⟨x, hxr', hxC⟩ := not_subset.mp hcon
    obtain ⟨y, ⟨hyr', hyC⟩, hyU⟩ := exists_notMem_U (Γ := Γ) hS
      ((region_isOpen hr').inter hΔ.isOpen_compl) ⟨x, hxr', hxC⟩
    obtain ⟨s, hs', hys⟩ := exists_region_of_notMem hyU
    have hsr' : s ⊆ r' := subset_region hr' (region_isPreconnected hs')
      (disjoint_left.mpr fun q hq h => region_subset hs' hq (hN's.U_subset h)) hys hyr'
    let X : Set (Set S) := {t | t ⊆ ins C}
    obtain ⟨e, heΓ, heN, a, b, haZ, hbZ, has, hbs, hia, hib⟩ :=
      theorem_5_1_proof (Z := X ∩ Z') hS hN's hr' hrR ⟨hin, hr⟩ hs' (fun h => hyC (h.1 hys))
        hrr' hsr'
    have hbZ' : b ∈ Z' := by
      by_contra hb
      exact heN (mem_boundaryDrawing_E.mpr ⟨⟨a, haZ.2, hia⟩, b, ⟨hib.2.1, hb⟩, hib⟩)
    have hbX : ¬ b ⊆ ins C := fun h => hbZ ⟨h, hbZ'⟩
    have hbdis : Disjoint b (ins C) := by
      rcases region_subset_or_disjoint hs hC hCs hl hib.2.1 with h | h
      · exact absurd h hbX
      · exact h
    -- Now `e` lies in the frontier of `ins(C)`, so `e` is an edge of `C`.
    have hes : e ⊆ closure a := edge_subset_closure_of_incident hS heΓ hia.2.1 hia.2.2
    have heb : e ⊆ closure b := edge_subset_closure_of_incident hS heΓ hib.2.1 hib.2.2
    have heC : e ∈ C.E := by
      obtain ⟨p, hp⟩ := heΓ.1
      have hpU : p ∈ C.U := by
        rw [← hs.subBd_eq C hC hCs hl]
        refine ⟨subset_closure (hΔ.closure_subset_iff.mpr haZ.1 (hes hp)), closure_mono ?_ (heb hp)⟩
        exact fun q hq => ⟨mem_univ _, disjoint_left.mp hbdis hq⟩
      have hpV : p ∉ C.V := fun h => (heΓ.2.1 hp).2 (hCs.1 h)
      obtain ⟨f, hf, hpf⟩ := C.exists_edge_of_mem hpU hpV
      have := Γ.edge_eq_of_mem (hCs.2 hf) heΓ hpf hp
      exact this ▸ hf
    -- But `e` is in `N(Z)`, so a third region at `e` lies outside `Z`.
    obtain ⟨-, t, ⟨ht, htZ⟩, hit⟩ := mem_boundaryDrawing_E.mp (hCN.2 heC)
    have hab : a ≠ b := fun h => hbX (h ▸ haZ.1)
    have hti : e ⊆ closure t := edge_subset_closure_of_incident hS heΓ hit.2.1 hit.2.2
    rcases region_incident_two hS heΓ hia.2.1 hib.2.1 ht hes heb hti with h | h | h
    · exact hab h
    · exact htZ (h ▸ hZ' haZ.2)
    · exact htZ (h ▸ hZ' hbZ')
  obtain ⟨D, hD, hDs, hDl, hDin⟩ := theorem_4_5_proof hS hs hN's hconf hr'
    ⟨C, hC, hCs, hl, hclaim⟩
  exact ⟨D, hD, hDs, hDl, hrr'.trans hDin⟩

end GraphMinor.GM11
