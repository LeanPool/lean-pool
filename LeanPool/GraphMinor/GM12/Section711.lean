/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section711a
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM11.Section64b
import LeanPool.GraphMinor.GM11.FlatCover
import LeanPool.GraphMinor.GM11.OpenAround
import LeanPool.GraphMinor.GM11.GlueFaces

/-!
# Graph Minors XII, (7.11)

This file completes the proof of **(7.11)** of Robertson and Seymour,
*Graph Minors. XII. Distance on a surface*, J. Combin. Theory Ser. B 64 (1995), 240–272
(pages 271–272).

Using the restraint-union and preconnectedness results from `Section711a.lean`, we show that every
region of `Γ' = H.span ∅ {e ∈ H.E | lam < d z e}` (and thus of `deleteAtomNeighborhood H d z lam`)
is an open disc, so `Γ'` is a 2-cell drawing.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- Along any spoke `h ∈ K.E` contained in `r ∩ Z` (`r ∈ H.R`), the radial hub `w_r ∈ r ∩ K.V`
is joined in `r ∩ Z` to every point `q ∈ h`. -/
theorem joinedIn_spoke_inter_Z (hS : IsClosedSurface S)
    {H K : Drawing S} (hpre : PreRad (PaintingOrDrawing.drawing H) K)
    {Z : Set S} (hZc : IsClosed Z) {r h : Set S} (hr : r ∈ H.R) (hh : h ∈ K.E)
    (hhr : h ⊆ r) (hhZ : h ⊆ Z) {w_r q : S} (hw_r : w_r ∈ r) (hw_V : w_r ∈ K.V) (hq : q ∈ h) :
    JoinedIn (r ∩ Z) w_r q := by
  have hclZ : closure h ⊆ Z := closure_minimal hhZ hZc
  obtain ⟨v, hv, r₁, hr₁, w, hw, hwV, hcap, hsub⟩ := spoke_ends hpre hS hh
  obtain rfl : r₁ = r := region_eq_of_mem hr₁ hr (hsub hq) (hhr hq)
  obtain rfl : w = w_r := hub_unique hpre hr₁ hw_r hw_V hw hwV
  have hvw : v ≠ w := fun h => region_subset hr₁ hw_r (H.V_subset_U (h ▸ hv))
  have hline : IsLineWithEnds (closure h) v w := by
    rcases K.edge_cond h hh with ⟨a, b, hab, hc', hL⟩ | ⟨a, hc', -⟩
    · rw [hcap] at hc'
      rcases Set.pair_eq_pair_iff.mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hL
      · exact Surface.IsLineWithEnds.symm hL
    · rw [hcap] at hc'
      have h₁ : v ∈ ({a} : Set S) := hc' ▸ mem_insert _ _
      have h₂ : w ∈ ({a} : Set S) := hc' ▸ mem_insert_of_mem _ rfl
      exact absurd (h₁.trans h₂.symm) hvw
  have hsub' : closure h \ {v} ⊆ r₁ ∩ Z := by
    rintro x ⟨hx, hxv⟩
    refine ⟨?_, hclZ hx⟩
    by_cases hxV : x ∈ K.V
    · have : x ∈ closure h ∩ K.V := ⟨hx, hxV⟩
      rw [hcap] at this
      rcases this with h | h
      · exact absurd h hxv
      · exact (mem_singleton_iff.mp h) ▸ hw_r
    · exact hsub ((K.closure_diff_V hh).subset ⟨hx, hxV⟩)
  have hqv : q ≠ v := fun h => edge_notMem_V hh hq (h ▸ radial_V hpre hv)
  exact (joinedIn_line hline (subset_closure hq) hqv).symm.mono hsub'

/-- For every region `r ∈ H.R` with radial hub `w_r ∈ r ∩ K.V` and every `y ∈ r ∩ Z`
(where `Z` is a closed `K`-nice set), `w_r` is joined to `y` in `r ∩ Z`. -/
theorem joinedIn_region_inter_Z (hS : IsClosedSurface S) [ConnectedSpace S]
    {H K : Drawing S} (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    {Z : Set S} (hZc : IsClosed Z) (hZn : IsGammaNice K Z)
    {r : Set S} (hr : r ∈ H.R) {w_r y : S} (hw_r : w_r ∈ r) (hw_V : w_r ∈ K.V)
    (hy : y ∈ r ∩ Z) :
    JoinedIn (r ∩ Z) w_r y := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpre : PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  by_cases hyK : y ∈ K.U
  · by_cases hyV : y ∈ K.V
    · obtain rfl : y = w_r := hub_unique hpre hr hw_r hw_V hy.1 hyV
      exact JoinedIn.refl hy
    · obtain ⟨h, hh, hyh⟩ := K.exists_edge_of_mem hyK hyV
      have hhZ : h ⊆ Z := nice_edge hZn hh ⟨y, hyh, hy.2⟩
      obtain ⟨-, -, r₁, hr₁, -, -, -, -, hsub⟩ := spoke_ends hpre hS hh
      obtain rfl : r₁ = r := region_eq_of_mem hr₁ hr (hsub hyh) hy.1
      exact joinedIn_spoke_inter_Z hS hpre hZc hr₁ hh hsub hhZ hw_r hw_V hyh
  · have hyRU : y ∉ (radialUnion hpre).U := by
      rintro (hyH | hyK')
      · exact region_subset hr hy.1 hyH
      · exact hyK hyK'
    obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem hyRU
    obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyK
    have hsZ : s ⊆ Z := nice_region hZn hs ⟨y, hys, hy.2⟩
    have hps : p ⊆ s := region_sub_of_mem hpre hS hs hp (subset_closure hyp) hys
    have hpZ : p ⊆ Z := hps.trans hsZ
    have hcl_pZ : closure p ⊆ Z := closure_minimal hpZ hZc
    have hpr : p ⊆ r := by
      have hp_disj : Disjoint p H.U :=
        disjoint_left.mpr fun x hxp hxH => region_subset hp hxp (Or.inl hxH)
      exact subset_region hr (region_isPreconnected hp) hp_disj hyp hy.1
    have hcp : w_r ∈ closure p := hub_mem_closure hpre hS hr hp hpr hw_r hw_V
    obtain ⟨N, hNo, hwN, hNj⟩ := locJoin_region hS hp hcp r (region_isOpen hr) hw_r
    obtain ⟨z₀, hz₀N, hz₀p⟩ := mem_closure_iff.mp hcp N hNo hwN
    have hj₁ : JoinedIn (r ∩ Z) w_r z₀ :=
      (hNj z₀ ⟨subset_closure hz₀p, hz₀N⟩).mono fun u hu => ⟨hu.2, hcl_pZ hu.1⟩
    have hj₂ : JoinedIn (r ∩ Z) z₀ y :=
      ((isPathConnected_of_isOpen hS (region_isOpen hp) (region_isPreconnected hp)
        ⟨z₀, hz₀p⟩).joinedIn z₀ hz₀p y hyp).mono (subset_inter hpr hpZ)
    exact hj₁.trans hj₂

/-- Every deleted vertex `v ∈ H.V \ Γ'.V` lies in an open disc `D_v ⊆ Z`. -/
theorem exists_openDisc_around_deleted_vertex (hS : IsClosedSurface S) [ConnectedSpace S]
    {H K : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T) (hE : H.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    {z z' : Set S} (hz : z ∈ H.A) (hz' : IsCorrespondingAtom H K z z') {c : S} (hc : c ∈ z')
    (hlam : lam < θ) (hz_lam : z ∈ H.E → 2 ≤ lam)
    {v : S} (hv : v ∈ H.V \ (H.span ∅ {f ∈ H.E | lam < d z f}).V) :
    ∃ U : Set S, IsOpenDisc U ∧ v ∈ U ∧ U ⊆ restraintUnion K ins (2 * θ) c (2 * lam) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hpre : PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  have hrf := GM11.regionFacts_of_radial hpre hS hK.2.2 hE
  set Z := restraintUnion K ins (2 * θ) c (2 * lam)
  set Γ' := H.span ∅ {f ∈ H.E | lam < d z f}
  have hZc : IsClosed Z := isClosed_restraintUnion hS c (2 * lam)
  have hZn : IsGammaNice K Z := isGammaNice_restraintUnion c (2 * lam)
  -- For any `s ∈ K.R`, if `v ∈ closure s`, then `s ⊆ Z`.
  have hs_sub_Z : ∀ s ∈ K.R, v ∈ closure s → s ⊆ Z := by
    intro s hs hvs
    obtain ⟨e, he, hes⟩ := hrf.1 s hs
    have hve : v ∈ closure e := hrf.2.2 s hs e he hes v hv.1 hvs
    have he_not : e ∉ Γ'.E := by
      intro heΓ'
      apply hv.2
      exact Or.inr (mem_iUnion₂.mpr ⟨e, by rwa [← H.span_E], hve, hv.1⟩)
    have hnot_compl : ¬ (s ⊆ Zᶜ) := by
      rw [← edge_mem_span_iff hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam he hs hes]
      exact he_not
    obtain ⟨y, hys, hyZ⟩ : (s ∩ Z).Nonempty := by
      by_contra hcon
      exact hnot_compl fun x hxs hxZ => hcon ⟨x, hxs, hxZ⟩
    exact nice_region hZn hs ⟨y, hys, hyZ⟩
  -- For any `h ∈ K.E`, if `v ∈ closure h`, then `h ⊆ Z`.
  have hh_sub_Z : ∀ h ∈ K.E, v ∈ closure h → h ⊆ Z := by
    intro h hh hvh
    obtain ⟨s, hs, hhs⟩ := exists_region_incident hS hh
    have hcl_hs : closure h ⊆ closure s := closure_minimal hhs isClosed_closure
    exact hhs.trans (closure_minimal (hs_sub_Z s hs (hcl_hs hvh)) hZc)
  -- Also `v ∈ Z`.
  have hvZ : v ∈ Z := by
    obtain ⟨e₀, he₀, hve₀⟩ := exists_edge_at hpre hS hE hv.1
    obtain ⟨p₀, hp₀⟩ := he₀.1
    have hUU : H.U ∩ K.U = H.V := hK.2.1.1
    have hoff : ∀ y ∈ e₀, y ∉ K.U := fun y hy hyK => by
      have : y ∈ H.U ∩ K.U := ⟨(he₀.2.1 hy).1, hyK⟩
      rw [hUU] at this
      exact (he₀.2.1 hy).2 this
    set s₀ := connectedComponentIn (univ \ K.U) p₀
    have hs₀ : s₀ ∈ K.R := (mem_R_iff K).mpr ⟨p₀, hoff p₀ hp₀, rfl⟩
    have hes₀ : e₀ ⊆ s₀ :=
      he₀.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hp₀
        fun y hy => ⟨mem_univ y, hoff y hy⟩
    have hvs₀ : v ∈ closure s₀ := closure_mono hes₀ hve₀
    exact closure_minimal (hs_sub_Z s₀ hs₀ hvs₀) hZc hvs₀
  -- Define the closed set `B_v` of atoms of `K` outside `Z` or vertices `≠ v`.
  let B_v : Set S :=
    (K.V \ {v}) ∪ (⋃ h ∈ {h ∈ K.E | ¬ (h ⊆ Z)}, closure h) ∪
      (⋃ s ∈ {s ∈ K.R | ¬ (s ⊆ Z)}, closure s)
  have hBv_closed : IsClosed B_v := by
    refine ((K.finite_V.subset sdiff_subset).isClosed.union ?_).union ?_
    · exact (K.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
    · exact ((finite_R hS K).subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
  have hv_not_Bv : v ∉ B_v := by
    rintro ((⟨-, hvv⟩ | h) | h)
    · exact hvv rfl
    · obtain ⟨h, ⟨hh, hhZ⟩, hvh⟩ := mem_iUnion₂.mp h
      exact hhZ (hh_sub_Z h hh hvh)
    · obtain ⟨s, ⟨hs, hsZ⟩, hvs⟩ := mem_iUnion₂.mp h
      exact hsZ (hs_sub_Z s hs hvs)
  have hBv_compl_sub : B_vᶜ ⊆ Z := by
    intro y hy
    by_cases hyK : y ∈ K.U
    · by_cases hyV : y ∈ K.V
      · by_cases hyv : y = v
        · exact hyv ▸ hvZ
        · exact False.elim (hy (Or.inl (Or.inl ⟨hyV, hyv⟩)))
      · obtain ⟨h, hh, hyh⟩ := K.exists_edge_of_mem hyK hyV
        by_cases hhZ : h ⊆ Z
        · exact hhZ hyh
        · exact False.elim (hy (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨h, ⟨hh, hhZ⟩,
            subset_closure hyh⟩))))
    · obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyK
      by_cases hsZ : s ⊆ Z
      · exact hsZ hys
      · exact False.elim (hy (Or.inr (mem_iUnion₂.mpr ⟨s, ⟨hs, hsZ⟩, subset_closure hys⟩)))
  obtain ⟨D, D', hD, hD', hvD', hD'D, hDB, hbdD⟩ :=
    exists_closedDisc_nbhd hS hBv_closed.isOpen_compl hv_not_Bv
  have hInt : IsOpenDisc (discInt D) := isOpenDisc_interior hS hD
  have hvInt : v ∈ discInt D := by
    refine ⟨hD'D hvD', ?_⟩
    rw [← hbdD]
    exact fun h => h.2 hvD'
  exact ⟨discInt D, hInt, hvInt, (sdiff_subset.trans hDB).trans hBv_compl_sub⟩

private theorem flat_union_of_region_neighborhoods
    {S : Type*} [TopologicalSpace S] {ι : Type*} (Z W : Set S)
    (hZf : Flat (Subtype.val ⁻¹' Z : Set W))
    (O_S : ι → Set S) (hOS_od : ∀ i, IsOpenDisc (O_S i)) (hOS_W : ∀ i, O_S i ⊆ W)
    (b_W : ι → W) (hb_mem : ∀ i, (b_W i).1 ∈ O_S i) (hb_Z : ∀ i, (b_W i).1 ∈ Z)
    (hjoin_to_Z : ∀ i (y : W), y.1 ∈ O_S i → y.1 ∈ Z →
      ∃ f : Cl (b_W i) y, Arw (Subtype.val ⁻¹' O_S i) f ∧ Arw (Subtype.val ⁻¹' Z) f)
    (hoverlap : ∀ i j (y : W), y.1 ∈ O_S i → y.1 ∈ O_S j → i = j ∨ y.1 ∈ Z) :
    Flat (⋃ i, (Subtype.val ⁻¹' O_S i : Set W)) := by
  let O_W : ι → Set W := fun i => Subtype.val ⁻¹' O_S i
  refine flat_iUnion_cover hZf O_W b_W ?_ hb_mem ?_ ?_ ?_
  · intro i
    exact (hOS_od i).1.preimage continuous_subtype_val
  · intro i
    exact isPathConnected_preimage (hOS_od i).isPathConnected (hOS_W i)
  · intro i
    exact flat_of_simplyConnected (hOS_od i).isSimplyConnectedSet (hOS_W i)
  · intro i j y hyi hyj
    rcases hoverlap i j y hyi hyj with rfl | hyZ
    · have hpc : IsPathConnected (O_W i) :=
        isPathConnected_preimage (hOS_od i).isPathConnected (hOS_W i)
      have hj := hpc.joinedIn (b_W i) (hb_mem i) y hyi
      refine ⟨Cl.mk hj.somePath, (Cl.mk hj.somePath).symm,
        ⟨hj.somePath, hj.somePath_mem, rfl⟩,
        Arw.symm ⟨hj.somePath, hj.somePath_mem, rfl⟩, ?_⟩
      rw [cl_trans_symm]
      exact arw_refl (hb_Z i)
    · obtain ⟨f, hfO, hfZ⟩ := hjoin_to_Z i y hyi hyZ
      obtain ⟨g, hgO, hgZ⟩ := hjoin_to_Z j y hyj hyZ
      exact ⟨f, g.symm, hfO, hgO.symm, hfZ.trans hgZ.symm⟩

private theorem removed_drawing_in_region_neighborhoods
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    {H : Drawing S}
    {θ : ℕ}
    {lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hE : H.E.Nonempty)
    {z : Set S}
    (hz : z ∈ H.A)
    (hlam : lam < θ)
    (hz_lam : z ∈ H.E → 2 ≤ lam)
    (hResp : IsRespectfulDrawingTangle H θ T)
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    (z' : Set S)
    (hz' : IsCorrespondingAtom H K z z')
    (c : S)
    (hc : c ∈ z')
    (hUU : H.U ∩ K.U = H.V) (discV : S → Set S) :
    let Z := restraintUnion K ins (2 * θ) c (2 * lam)
    let Γ' := H.span ∅ {e ∈ H.E | lam < d z e}
    IsGammaNice K Z → (∀ v ∈ H.V \ Γ'.V, v ∈ discV v) →
    H.U \ Γ'.U ⊆ ⋃ i : {r // r ∈ {r | r ∈ H.R ∧ (r ∩ Z).Nonempty}} ⊕
        ({s // s ∈ {s | s ∈ K.R ∧ s ⊆ Z}} ⊕ {v // v ∈ H.V \ Γ'.V}),
      Sum.elim (fun r => r.1) (Sum.elim (fun s => s.1) fun v => discV v.1) i := by
  intro Z Γ' hZn hdiscV_mem
  rintro x ⟨hxH, hxΓ'⟩
  by_cases hxV : x ∈ H.V
  · have hxS₀ : x ∈ H.V \ Γ'.V := ⟨hxV, fun hxV' => hxΓ' (Γ'.V_subset_U hxV')⟩
    exact mem_iUnion.mpr ⟨Sum.inr (Sum.inr ⟨x, hxS₀⟩), hdiscV_mem x hxS₀⟩
  · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxH hxV
    have he_not : e ∉ Γ'.E := fun he' => hxΓ' (Γ'.closure_subset_U he' (subset_closure hxe))
    have hoff : ∀ y ∈ e, y ∉ K.U := fun y hy hyK => by
      have : y ∈ H.U ∩ K.U := ⟨(he.2.1 hy).1, hyK⟩
      rw [hUU] at this
      exact (he.2.1 hy).2 this
    set s_e := connectedComponentIn (univ \ K.U) x
    have hs_e : s_e ∈ K.R := (mem_R_iff K).mpr ⟨x, hoff x hxe, rfl⟩
    have hes_e : e ⊆ s_e :=
      he.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hxe
        fun y hy => ⟨mem_univ y, hoff y hy⟩
    have hnot_compl : ¬ (s_e ⊆ Zᶜ) := by
      rw [← edge_mem_span_iff hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam he hs_e hes_e]
      exact he_not
    obtain ⟨y, hys, hyZ⟩ : (s_e ∩ Z).Nonempty := by
      by_contra hcon
      exact hnot_compl fun x hxs hxZ => hcon ⟨x, hxs, hxZ⟩
    have hs_e_Z : s_e ⊆ Z := nice_region hZn hs_e ⟨y, hys, hyZ⟩
    exact mem_iUnion.mpr ⟨Sum.inr (Sum.inl ⟨s_e, hs_e, hs_e_Z⟩), hes_e hxe⟩

private theorem bounded_region_disc_disjoint_drawing
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    (Γ' : Drawing S)
    (hΓ'U_pre : IsPreconnected Γ'.U)
    (x₀ : S)
    (hx₀U' : x₀ ∈ Γ'.U)
    (F Δ : Set S)
    (hx₀Δ : x₀ ∉ Δ)
    (hΔ : IsClosedDisc Δ)
    (hb : discBd Δ = F)
    (hF_disj : Disjoint F Γ'.U) :
    Disjoint Δ Γ'.U := by
  refine disjoint_left.mpr fun x hxΔ hxU => ?_
  have hcov_U' : Γ'.U ⊆ discInt Δ ∪ Δᶜ := fun y hy => by
    by_cases hyΔ : y ∈ Δ
    · left
      refine ⟨hyΔ, fun hybd => ?_⟩
      rw [hb] at hybd
      exact disjoint_left.mp hF_disj hybd hy
    · exact Or.inr hyΔ
  have hInt_open : IsOpen (discInt Δ) := (isOpenDisc_interior hS hΔ).1
  have hCompl_open : IsOpen Δᶜ := hΔ.isCompact.isClosed.isOpen_compl
  have hdisj_int : Disjoint (discInt Δ) Δᶜ :=
    disjoint_left.mpr fun y hy hyc => hyc hy.1
  have hx_int : x ∈ discInt Δ := by
    refine ⟨hxΔ, fun hxbd => ?_⟩
    rw [hb] at hxbd
    exact disjoint_left.mp hF_disj hxbd hxU
  have hsub_int : Γ'.U ⊆ discInt Δ :=
    hΓ'U_pre.subset_left_of_subset_union hInt_open hCompl_open hdisj_int hcov_U' ⟨x, hxU,
      hx_int⟩
  exact hx₀Δ (hsub_int hx₀U').1

private theorem region_not_contained_in_neighborhood_lies_outside
    {S : Type u}
    [TopologicalSpace S]
    {H : Drawing S}
    [LocallyConnectedSpace S]
    (Z : Set S)
    (Γ' : Drawing S)
    (hU_diff_intZ : H.U \ Γ'.U ⊆ interior Z)
    (q : Set S)
    (hq : q ∈ (PaintingOrDrawing.drawing Γ').R)
    (y₀ : S)
    (hy₀q : y₀ ∈ q)
    (r₀ : Set S)
    (hr₀ : r₀ ∈ H.R)
    (hy₀r₀ : y₀ ∈ r₀)
    (hr₀Z_empty : r₀ ∩ Z = ∅) :
    q ⊆ r₀ := by
  by_contra hnot
  obtain ⟨z₁, hz₁q, hz₁_not⟩ := not_subset.mp hnot
  have hcov_q : q ⊆ r₀ ∪ (closure r₀)ᶜ := fun x hxq => by
    by_cases hxr₀ : x ∈ r₀
    · exact Or.inl hxr₀
    · right
      intro hxcl
      have hxH : x ∈ H.U := (closure_region_subset hr₀ hxcl).resolve_left hxr₀
      have hx_int : x ∈ interior Z := hU_diff_intZ ⟨hxH, region_subset hq hxq⟩
      obtain ⟨w, hwZ, hwr₀⟩ :=
        mem_closure_iff.mp hxcl (interior Z) isOpen_interior hx_int
      have : w ∈ r₀ ∩ Z := ⟨hwr₀, interior_subset hwZ⟩
      rw [hr₀Z_empty] at this
      exact this
  have hsub_r₀ :=
    (region_isPreconnected hq).subset_left_of_subset_union (region_isOpen hr₀)
      isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.mpr subset_closure)
      hcov_q ⟨y₀, hy₀q, hy₀r₀⟩
  exact hz₁_not (hsub_r₀ hz₁q)

/-- **(7.11)** of Graph Minors XII (page 271), for the subdrawing
`Γ' = H.span ∅ {e ∈ H.E | lam < d z e}` when `lam < θ` and `z ∈ H.E → 2 ≤ lam`. -/
theorem theorem_7_11_span (hS : IsClosedSurface S) [ConnectedSpace S]
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    {z : Set S} (hz : z ∈ H.A) (hlam : lam < θ) (hz_lam : z ∈ H.E → 2 ≤ lam) :
    (PaintingOrDrawing.drawing (H.span ∅ {f ∈ H.E | lam < d z f})).IsTwoCell := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hT := hResp.2.1
  have hpre : PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  have hpreT : IsPretangle H.toHypergraph θ T :=
    ⟨hT.one_le, hT.isSeparation, hT.order_lt, hT.axiom1, hT.axiom2⟩
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hpreT hK.2.1.1 hd
  obtain ⟨z', hz', -⟩ := existsUnique_correspondingAtom_t1 hK hz
  obtain ⟨c, hc⟩ := atom_nonempty hz'.2.1
  set Z := restraintUnion K ins (2 * θ) c (2 * lam)
  set Γ' := H.span ∅ {f ∈ H.E | lam < d z f}
  have hz'Z : z' ⊆ Z :=
    correspondingAtom_subset_restraintUnion hS hResp hE hK hd hz' hc hlam hz_lam
  have hZne : Z.Nonempty := ⟨c, hz'Z hc⟩
  have hZc : IsClosed Z := isClosed_restraintUnion hS c (2 * lam)
  have hZn : IsGammaNice K Z := isGammaNice_restraintUnion c (2 * lam)
  have hZs : IsSimplyConnectedSet Z := GM11.theorem_8_10_proof hS hsl hZne
  obtain ⟨hZuniv, hΓ'E⟩ :=
    restraintUnion_ne_univ_and_span_E_nonempty hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam
  have hΓ'U_pre : IsPreconnected Γ'.U :=
    isPreconnected_span_U hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam
  have hsub : Γ'.IsSubdrawing H := H.span_isSubdrawing ∅ _
  -- Pick `e₀ ∈ Γ'.E` and `x₀ ∈ e₀`. Then `x₀ ∈ Γ'.U \ Z`.
  obtain ⟨e₀, he₀⟩ := hΓ'E
  have he₀H : e₀ ∈ H.E := hsub.2 he₀
  obtain ⟨x₀, hx₀⟩ := he₀.1
  have hx₀U' : x₀ ∈ Γ'.U := Γ'.closure_subset_U he₀ (subset_closure hx₀)
  have hx₀U : x₀ ∈ H.U := hsub.U_subset hx₀U'
  have hUU : H.U ∩ K.U = H.V := hK.2.1.1
  have hoff₀ : ∀ y ∈ e₀, y ∉ K.U := fun y hy hyK => by
    have : y ∈ H.U ∩ K.U := ⟨(he₀H.2.1 hy).1, hyK⟩
    rw [hUU] at this
    exact (he₀H.2.1 hy).2 this
  set s₀ := connectedComponentIn (univ \ K.U) x₀
  have hs₀ : s₀ ∈ K.R := (mem_R_iff K).mpr ⟨x₀, hoff₀ x₀ hx₀, rfl⟩
  have hes₀ : e₀ ⊆ s₀ :=
    he₀H.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hx₀
      fun y hy => ⟨mem_univ y, hoff₀ y hy⟩
  have hs₀_compl : s₀ ⊆ Zᶜ :=
    (edge_mem_span_iff hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam he₀H hs₀ hes₀).mp he₀
  have hx₀_notZ : x₀ ∉ Z := hs₀_compl (hes₀ hx₀)
  -- Work in the open punctured surface `W = {x₀}ᶜ`.
  set W : Set S := {x₀}ᶜ
  have hWo : IsOpen W := isOpen_compl_singleton
  have hZW : Z ⊆ W := fun x hx hxx₀ => hx₀_notZ (mem_singleton_iff.mp hxx₀ ▸ hx)
  have hZf : Flat (Subtype.val ⁻¹' Z : Set W) := flat_of_simplyConnected hZs hZW
  -- Define the three families of open discs in `W`:
  -- 1. `R₀ = {r ∈ H.R | (r ∩ Z).Nonempty}`
  -- 2. `K₀ = {s ∈ K.R | s ⊆ Z}`
  -- 3. `S₀ = H.V \ Γ'.V`, with open discs `D_v ⊆ Z` around each `v ∈ S₀`.
  set R₀ : Set (Set S) := {r ∈ H.R | (r ∩ Z).Nonempty}
  set K₀ : Set (Set S) := {s ∈ K.R | s ⊆ Z}
  set S₀ : Set S := H.V \ Γ'.V
  have hhub : ∀ r ∈ R₀, ∃ w_r, w_r ∈ r ∧ w_r ∈ K.V ∧ w_r ∈ Z := by
    rintro r ⟨hr, y₀, hy₀⟩
    obtain ⟨w_r, ⟨hw_r, hw_V⟩, -⟩ := hK.2.1.2.2.1 r hr
    have hj := joinedIn_region_inter_Z hS hK hZc hZn hr hw_r hw_V hy₀
    obtain ⟨γ_w, hγ_w⟩ := hj
    have hw_mem : w_r ∈ r ∩ Z := by simpa using hγ_w 0
    exact ⟨w_r, hw_r, hw_V, hw_mem.2⟩
  choose! hub hub_r hub_V hub_Z using hhub
  have hK₀_pt : ∀ s ∈ K₀, ∃ b_s, b_s ∈ s := fun s hs => region_nonempty hs.1
  choose! baseK hbaseK using hK₀_pt
  have hS₀_disc : ∀ v ∈ S₀, ∃ U : Set S, IsOpenDisc U ∧ v ∈ U ∧ U ⊆ Z := fun v hv =>
    exists_openDisc_around_deleted_vertex hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam hv
  choose! discV hdiscV_od hdiscV_mem hdiscV_sub using hS₀_disc
  -- Index the open cover in `W`.
  let ι := {r // r ∈ R₀} ⊕ ({s // s ∈ K₀} ⊕ {v // v ∈ S₀})
  let O_S : ι → Set S :=
    Sum.elim (fun r => r.1) (Sum.elim (fun s => s.1) (fun v => discV v.1))
  have hOS_od : ∀ i : ι, IsOpenDisc (O_S i) := by
    rintro (r | (s | v))
    · exact hResp.1.2 r.1 r.2.1
    · exact radial_region_isOpenDisc hpre hS hK.2.2 s.2.1
    · exact hdiscV_od v.1 v.2
  have hOS_W : ∀ i : ι, O_S i ⊆ W := by
    rintro (r | (s | v)) x hx hxx₀
    · rw [mem_singleton_iff] at hxx₀
      exact region_subset r.2.1 (hxx₀ ▸ hx) hx₀U
    · exact hZW (s.2.2 hx) hxx₀
    · exact hZW (hdiscV_sub v.1 v.2 hx) hxx₀
  let b_S : ι → S :=
    Sum.elim (fun r => hub r.1) (Sum.elim (fun s => baseK s.1) (fun v => v.1))
  have hb_mem : ∀ i : ι, b_S i ∈ O_S i := by
    rintro (r | (s | v))
    · exact hub_r r.1 r.2
    · exact hbaseK s.1 s.2
    · exact hdiscV_mem v.1 v.2
  have hb_Z : ∀ i : ι, b_S i ∈ Z := by
    rintro (r | (s | v))
    · exact hub_Z r.1 r.2
    · exact s.2.2 (hbaseK s.1 s.2)
    · exact hdiscV_sub v.1 v.2 (hdiscV_mem v.1 v.2)
  let O_W : ι → Set W := fun i => Subtype.val ⁻¹' (O_S i)
  let b_W : ι → W := fun i => ⟨b_S i, hOS_W i (hb_mem i)⟩
  -- For any `i : ι` and `y ∈ O_W i` with `y.1 ∈ Z`, there is a path in `O_W i ∩ Z_W` from `b_W i`
  -- to `y`.
  have hjoin_to_Z : ∀ (i : ι) (y : W), y ∈ O_W i → y.1 ∈ Z →
      ∃ f : Cl (b_W i) y, Arw (O_W i) f ∧ Arw (Subtype.val ⁻¹' Z : Set W) f := by
    rintro (r | (s | v)) y hy hyZ
    · have hj : JoinedIn (r.1 ∩ Z) (hub r.1) y.1 :=
        joinedIn_region_inter_Z hS hK hZc hZn r.2.1 (hub_r r.1 r.2) (hub_V r.1 r.2) ⟨hy, hyZ⟩
      have hsub_W : r.1 ∩ Z ⊆ W := inter_subset_right.trans hZW
      obtain ⟨p, hp⟩ := hj
      let p_W : Path (b_W (Sum.inl r)) y :=
        ⟨⟨fun t => ⟨p t, hsub_W (hp t)⟩, by fun_prop⟩, Subtype.ext p.source, Subtype.ext p.target⟩
      exact ⟨Cl.mk p_W, ⟨p_W, fun t => (hp t).1, rfl⟩, ⟨p_W, fun t => (hp t).2, rfl⟩⟩
    · have hpc : IsPathConnected (O_W (Sum.inr (Sum.inl s))) :=
        isPathConnected_preimage (hOS_od (Sum.inr (Sum.inl s))).isPathConnected
          (hOS_W (Sum.inr (Sum.inl s)))
      have hj := hpc.joinedIn (b_W (Sum.inr (Sum.inl s))) (hb_mem (Sum.inr (Sum.inl s))) y hy
      refine ⟨Cl.mk hj.somePath, ⟨hj.somePath, hj.somePath_mem, rfl⟩,
        ⟨hj.somePath, fun t => s.2.2 (hj.somePath_mem t), rfl⟩⟩
    · have hpc : IsPathConnected (O_W (Sum.inr (Sum.inr v))) :=
        isPathConnected_preimage (hOS_od (Sum.inr (Sum.inr v))).isPathConnected
          (hOS_W (Sum.inr (Sum.inr v)))
      have hj := hpc.joinedIn (b_W (Sum.inr (Sum.inr v))) (hb_mem (Sum.inr (Sum.inr v))) y hy
      refine ⟨Cl.mk hj.somePath, ⟨hj.somePath, hj.somePath_mem, rfl⟩,
        ⟨hj.somePath, fun t => hdiscV_sub v.1 v.2 (hj.somePath_mem t), rfl⟩⟩
  -- Apply `flat_iUnion_cover` in `W`.
  have hFlat_union : Flat (⋃ i : ι, O_W i) := by
    refine flat_union_of_region_neighborhoods Z W hZf O_S hOS_od hOS_W b_W hb_mem hb_Z
      hjoin_to_Z ?_
    intro i j y hyi hyj
    rcases i with r | (s | v) <;> rcases j with r' | (s' | v')
    all_goals first
      | exact Or.inr (s.2.2 hyi)
      | exact Or.inr (s'.2.2 hyj)
      | exact Or.inr (hdiscV_sub v.1 v.2 hyi)
      | exact Or.inr (hdiscV_sub v'.1 v'.2 hyj)
      | exact Or.inl (congrArg Sum.inl (Subtype.ext (region_eq_of_mem r.2.1 r'.2.1 hyi hyj)))
  -- Show that every point of `H.U \ Γ'.U` lies in `⋃ i, O_S i` (and in fact in `interior Z`).
  have hU_diff_sub : H.U \ Γ'.U ⊆ ⋃ i : ι, O_S i := by
    exact removed_drawing_in_region_neighborhoods hS hE hz hlam hz_lam hResp K ins hK hd hd_eq
      z' hz' c hc hUU discV hZn hdiscV_mem
  have hU_diff_intZ : H.U \ Γ'.U ⊆ interior Z := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hU_diff_sub hx)
    rcases i with r | (s | v)
    · exact False.elim (region_subset r.2.1 hxi hx.1)
    · exact mem_interior.mpr ⟨s.1, s.2.2, region_isOpen s.2.1, hxi⟩
    · exact mem_interior.mpr ⟨discV v.1, hdiscV_sub v.1 v.2, (hdiscV_od v.1 v.2).1, hxi⟩
  -- Now prove `IsTwoCell` for `Γ'`: `S` is connected and every region `q ∈ Γ'.R` is an open disc.
  refine ⟨inferInstance, fun q hq => ?_⟩
  by_cases hq_sub : q ⊆ ⋃ i : ι, O_S i
  · -- `q` lies in the flat union `⋃ i, O_S i ⊆ W`.
    have hq_ne_univ : q ≠ univ := fun hun => region_subset hq (hun ▸ mem_univ x₀) hx₀U'
    refine isOpenDisc_of_bound hS (region_isOpen hq) ⟨region_nonempty hq, region_isPreconnected hq⟩
      hq_ne_univ fun F hFq hF => ?_
    have hFU : F ⊆ ⋃ i : ι, O_S i := hFq.trans hq_sub
    have hFW : F ⊆ W := fun x hx => by
      obtain ⟨i, hxi⟩ := mem_iUnion.mp (hFU hx)
      exact hOS_W i hxi
    obtain ⟨ψ⟩ := id hF
    let φ : C(Circle, S) := ⟨fun x => (ψ x).1, continuous_subtype_val.comp ψ.continuous⟩
    have hmem : ∀ t, φ (arcParam 1 t) ∈ W := fun t => hFW (ψ _).2
    let a : W := ⟨φ (arcParam 1 0), hmem 0⟩
    let γ_F : Path a a :=
      ⟨⟨fun t => ⟨φ (arcParam 1 t), hmem t⟩, by fun_prop⟩, rfl, Subtype.ext (by simp [a])⟩
    have hγ_mem : ∀ u, γ_F u ∈ ⋃ i : ι, O_W i := fun u => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hFU (ψ (arcParam 1 u)).2)
      exact mem_iUnion.mpr ⟨i, hi⟩
    have hh : γ_F.Homotopic (Path.refl a) :=
      hFlat_union γ_F (Path.refl a) hγ_mem (fun _ => by simpa using hγ_mem 0)
    have hnull : IsNullHomotopicOArcIn W F :=
      ⟨ψ, a.1, a.2, closedCurvesHomotopicIn_of_path 1 φ (ContinuousMap.const _ a.1) γ_F
        (Path.refl a) (fun _ => rfl) (fun _ => rfl) hh⟩
    have hbd : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx => hx (hS.2.2 x)
    obtain ⟨Δ, hΔW, hΔ, hb⟩ :=
      (epstein S W F (IsClosedSurface.isSurface hS) inferInstance hF hFW hbd).1 hnull
    -- `Δ` is disjoint from `Γ'.U` because `discBd Δ = F ⊆ q`, `Γ'.U` is preconnected, and `x₀ ∈
    -- Γ'.U \ Δ`.
    have hF_disj : Disjoint F Γ'.U :=
      disjoint_left.mpr fun x hxF hxU => region_subset hq (hFq hxF) hxU
    have hΔ_disj : Disjoint Δ Γ'.U := by
      exact bounded_region_disc_disjoint_drawing (S := S) hS Γ' hΓ'U_pre x₀ hx₀U' F Δ
        (fun h => hΔW h rfl) hΔ hb hF_disj
    have hy_F : a.1 ∈ F := (ψ (arcParam 1 0)).2
    have hΔ_sub_q : Δ ⊆ q :=
      subset_region hq (IsClosedDisc.isSimplyConnectedSet hΔ).1.isConnected.isPreconnected
        hΔ_disj (Surface.discBd_subset Δ (by rwa [hb])) (hFq hy_F)
    exact ⟨Δ, hΔ_sub_q, hΔ, hb⟩
  · -- Some point `y₀ ∈ q` is not in `⋃ i, O_S i`.
    obtain ⟨y₀, hy₀q, hy₀_not⟩ := not_subset.mp hq_sub
    have hy₀_notH : y₀ ∉ H.U := fun hy₀H =>
      hy₀_not (hU_diff_sub ⟨hy₀H, region_subset hq hy₀q⟩)
    obtain ⟨r₀, hr₀, hy₀r₀⟩ := exists_region_of_notMem hy₀_notH
    have hr₀Z_empty : r₀ ∩ Z = ∅ := by
      rw [← not_nonempty_iff_eq_empty]
      intro hne
      exact hy₀_not (mem_iUnion.mpr ⟨Sum.inl ⟨r₀, hr₀, hne⟩, hy₀r₀⟩)
    have hr₀_sub_q : r₀ ⊆ q := by
      have hr₀_disj : Disjoint r₀ Γ'.U :=
        disjoint_left.mpr fun x hxr₀ hxU' => region_subset hr₀ hxr₀ (hsub.U_subset hxU')
      exact subset_region hq (region_isPreconnected hr₀) hr₀_disj hy₀r₀ hy₀q
    -- Show `q ⊆ r₀`: if not, `q` meets `closure r₀ \ r₀ ⊆ H.U \ Γ'.U ⊆ interior Z`, so `r₀` meets
    -- `Z`.
    have hq_sub_r₀ : q ⊆ r₀ := by
      exact region_not_contained_in_neighborhood_lies_outside (S := S) (H := H) Z Γ'
        hU_diff_intZ q hq y₀ hy₀q r₀ hr₀ hy₀r₀ hr₀Z_empty
    have hq_eq : q = r₀ := subset_antisymm hq_sub_r₀ hr₀_sub_q
    rw [hq_eq]
    exact hResp.1.2 r₀ hr₀

/-- **(7.11)** of Graph Minors XII (page 271):
Let `H` be a 2-cell drawing in a connected surface `S` with `E(H) ≠ ∅`, let `T` be a respectful
tangle in `H` of order `θ` with metric `d`, let `z ∈ A(H)` and let `λ ≥ 0` be an integer with
`z ∈ E(H) → 2 ≤ λ`. Let `Γ'` be the subdrawing of `H` formed by the edges `e` of `H` with
`d(z, e) > λ` and their ends. Suppose that `E(Γ') ≠ ∅`. Then `Γ'` is a 2-cell drawing in `S`.

The paper omits `z ∈ E(H) → 2 ≤ λ`. A central edge belongs to the deleted neighborhood because
`d(z, z) = 0`. This is the deleted-edge bound in the corrected (7.8) and the printed (7.10). -/
theorem theorem_7_11_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    {z : Set S} (hz : z ∈ H.A) (hz_lam : z ∈ H.E → 2 ≤ lam)
    (hΓ'E : (H.span ∅ {f ∈ H.E | lam < d z f}).E.Nonempty) :
    (PaintingOrDrawing.drawing (H.span ∅ {f ∈ H.E | lam < d z f})).IsTwoCell := by
  obtain ⟨e₀, he₀⟩ := hΓ'E
  rw [H.span_E] at he₀
  obtain ⟨⟨he₀H, hgt⟩, -⟩ := he₀
  obtain ⟨-, K, ins, hK, -, hd_eq⟩ := id hMetric
  have hle_θ : d z e₀ ≤ θ := by
    rw [hd_eq z hz e₀ (Or.inl (Or.inr he₀H))]
    exact tangleMetric_le_order hK ins θ z e₀
  have hlam : lam < θ := lt_of_lt_of_le hgt hle_θ
  exact theorem_7_11_span hS hMetric hE hz hlam hz_lam

/-- **(7.11)** of Graph Minors XII (page 271) for `deleteAtomNeighborhood H d z lam`. -/
theorem theorem_7_11_deleteAtomNeighborhood (hS : IsClosedSurface S) [ConnectedSpace S]
    (H : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S)
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    (hz : z ∈ H.A) (hlam : lam < θ) (hz_lam : z ∈ H.E → 2 ≤ lam) :
    (PaintingOrDrawing.drawing (deleteAtomNeighborhood H d z lam)).IsTwoCell := by
  have hdel_eq : deleteAtomNeighborhood H d z lam = H.span ∅ {e ∈ H.E | lam < d z e} := by
    rw [deleteAtomNeighborhood, ite_eq_right_iff.mpr fun h => False.elim (hE.ne_empty h)]
  rw [hdel_eq]
  exact theorem_7_11_span hS hMetric hE hz hlam hz_lam

end GraphMinor.GM12
