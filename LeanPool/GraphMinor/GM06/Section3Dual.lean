/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Section2Count
public import LeanPool.GraphMinor.GM06.Section3Basic
import LeanPool.GraphMinor.Surface.Crossing
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Analysis.Convex.PathConnected

/-!
# Graph Minors VI, Section 3: Disjoint Janiszewski on a Disc, Region Connectivity, and (3.2)

This file proves:
- `disc_janiszewski_disjoint`: Janiszewski's theorem for disjoint closed subsets of a closed disc
  space `S`, deduced from `janiszewski` in `ℂ` via a radial retraction-and-coning map `ℂ → S`.
- `same_region_of_no_component_crosses`: if `u₁, u₂ ∈ bd S \ Γ.U` and no connected component of a
  proper drawing `Γ` on `S` has two boundary vertices crossing `{u₁, u₂}` on `bd S`, then `u₁` and
  `u₂` lie in the same region of `Γ`.
- `theorem_3_2`: **Graph Minors VI, (3.2)** ($\Delta$ is feasible in $G$ if and only if $\Delta^*$
  is feasible in $G^*$).
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric Graph GraphMinor.Surface GraphMinor.GM11

universe u v

/-! ## 1. Closed Disc Space Crossing and Walk Point-Sets -/

theorem isClosedDisc_univ_of_isClosedDiscSpace {S : Type u} [TopologicalSpace S]
    (hDisc : IsClosedDiscSpace S) : IsClosedDisc (univ : Set S) := by
  rcases hDisc with ⟨e⟩
  exact ⟨e.trans (Homeomorph.Set.univ S).symm⟩

theorem discBd_univ_eq_bd {S : Type u} [TopologicalSpace S] :
    discBd (univ : Set S) = bd S := by
  have h := image_bd_homeomorph (Homeomorph.Set.univ S)
  simpa [discBd, Homeomorph.Set.univ] using h

theorem crossesOn_iff_pairsCrossOn_discBd_univ {S : Type u} [TopologicalSpace S]
    (a c b d : S) :
    CrossesOn (bd S) a c b d ↔ PairsCrossOn (discBd (univ : Set S)) a c b d := by
  rw [discBd_univ_eq_bd]

/-- Transfer `disc_crossing` to `S` when `IsClosedDiscSpace S`. -/
theorem discCrossing_of_isClosedDiscSpace
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {A B : Set S} {a c b d : S}
    (hA_comp : IsCompact A) (hB_comp : IsCompact B)
    (hA_conn : IsConnected A) (hB_conn : IsConnected B)
    (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) (hd : d ∈ B)
    (hcross : CrossesOn (bd S) a c b d) :
    (A ∩ B).Nonempty := by
  exact disc_crossing (univ : Set S) A B a c b d
    (isClosedDisc_univ_of_isClosedDiscSpace hDisc)
    (subset_univ A) (subset_univ B)
    hA_comp hB_comp hA_conn hB_conn ha hc hb hd
    ((crossesOn_iff_pairsCrossOn_discBd_univ a c b d).mp hcross)

theorem isCompact_closure_edge {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {e : Set S} (he : e ∈ G.E) :
    IsCompact (closure e) := by
  rcases G.edge_cond e he with ⟨u, v, _, _, f, _, _⟩ | ⟨u, _, ⟨f⟩⟩
  · have : CompactSpace (closure e) := f.compactSpace
    exact isCompact_iff_compactSpace.mpr this
  · have : CompactSpace (closure e) := f.compactSpace
    exact isCompact_iff_compactSpace.mpr this

theorem isConnected_closure_edge {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {e : Set S} (he : e ∈ G.E) :
    IsConnected (closure e) := by
  rcases G.edge_cond e he with ⟨u, v, _, _, f, _, _⟩ | ⟨u, _, ⟨f⟩⟩
  · have : ConnectedSpace (closure e) := f.surjective.connectedSpace f.continuous
    exact isConnected_iff_connectedSpace.mpr this
  · have : ConnectedSpace (closure e) := f.surjective.connectedSpace f.continuous
    exact isConnected_iff_connectedSpace.mpr this

theorem disjoint_edges_of_ne {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {e₁ e₂ : Set S} (he₁ : e₁ ∈ G.E) (he₂ : e₂ ∈ G.E) (hne : e₁ ≠ e₂) :
    Disjoint e₁ e₂ := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hnon
  have hnon_empty : (e₁ ∩ e₂).Nonempty := nonempty_iff_ne_empty.mpr hnon
  have hpc : IsPathConnected (e₁ ∪ e₂) := he₁.2.2.1.union he₂.2.2.1 hnon_empty
  have hsub : e₁ ∪ e₂ ⊆ G.U \ G.V := union_subset he₁.2.1 he₂.2.1
  have heq₁ : e₁ ∪ e₂ = e₁ := he₁.2.2.2 (e₁ ∪ e₂) hsub hpc subset_union_left
  have heq₂ : e₁ ∪ e₂ = e₂ := he₂.2.2.2 (e₁ ∪ e₂) hsub hpc subset_union_right
  exact hne (heq₁.symm.trans heq₂)

theorem closure_edge_eq_union_ends {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {e : Set S} {u v : S}
    (hlink : G.toGraph.IsLink e u v) (hne : u ≠ v) :
    closure e = e ∪ {u, v} := by
  rcases hlink with ⟨he, huV, hvV, hcap⟩
  rcases G.edge_cond e he with ⟨u', v', _, hcap', f, hf0, hf1⟩ | ⟨u', hcap', _⟩
  · have hpair : ({u', v'} : Set S) = {u, v} := hcap'.symm.trans hcap
    have h_ioo_pc : IsPathConnected {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
      have hconv : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo 0 1
      have hpc0 : IsPathConnected (Ioo (0 : ℝ) 1) :=
        hconv.isPathConnected ⟨1 / 2, by constructor <;> linarith⟩
      let clamp : ℝ → unitInterval := fun x =>
        ⟨max 0 (min 1 x), le_max_left 0 _, max_le zero_le_one (min_le_left 1 x)⟩
      have hclamp_cont : Continuous clamp :=
        (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
      have himg : clamp '' Ioo (0 : ℝ) 1 = {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          simp only [clamp, mem_ofPred_eq]
          have hmin : min 1 x = x := min_eq_right (le_of_lt hx.2)
          have hmax : max 0 (min 1 x) = x := by rw [hmin]; exact max_eq_right (le_of_lt hx.1)
          rw [hmax]
          exact hx
        · intro ht
          refine ⟨(t : ℝ), ht, Subtype.ext ?_⟩
          simp only [clamp]
          have hmin : min 1 (t : ℝ) = (t : ℝ) := min_eq_right (le_of_lt ht.2)
          rw [hmin]
          exact max_eq_right (le_of_lt ht.1)
      rw [← himg]
      exact hpc0.image hclamp_cont
    let phi : unitInterval → S := fun t => (f t).1
    have hphi_cont : Continuous phi := continuous_subtype_val.comp f.continuous
    have himg_eq : phi '' {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} = closure e \ G.V := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(f t).2, ?_⟩
        intro hzV
        have hz_mem : phi t ∈ closure e ∩ G.V := ⟨(f t).2, hzV⟩
        rw [hcap'] at hz_mem
        rcases hz_mem with hzu | hzv
        · have ht0 : t = 0 := f.injective (Subtype.ext (hzu.trans hf0.symm))
          subst ht0
          exact lt_irrefl (0 : ℝ) ht.1
        · have ht1 : t = 1 := f.injective (Subtype.ext (hzv.trans hf1.symm))
          subst ht1
          exact lt_irrefl (1 : ℝ) ht.2
      · rintro ⟨hz_cl, hz_notV⟩
        let t : unitInterval := f.symm ⟨z, hz_cl⟩
        have hft : phi t = z := congrArg Subtype.val (f.apply_symm_apply ⟨z, hz_cl⟩)
        refine ⟨t, ?_, hft⟩
        have ht0 : (t : ℝ) ≠ 0 := by
          intro h0
          have ht_eq : t = 0 := Subtype.ext h0
          have hz_eq : z = u' := by rw [← hft, ht_eq]; exact hf0
          have hu'V : u' ∈ G.V := by
            have : u' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_insert u' {v'}
            exact this.2
          exact hz_notV (hz_eq ▸ hu'V)
        have ht1 : (t : ℝ) ≠ 1 := by
          intro h1
          have ht_eq : t = 1 := Subtype.ext h1
          have hz_eq : z = v' := by rw [← hft, ht_eq]; exact hf1
          have hv'V : v' ∈ G.V := by
            have : v' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_insert_of_mem u' rfl
            exact this.2
          exact hz_notV (hz_eq ▸ hv'V)
        exact ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩
    have hpc_diff : IsPathConnected (closure e \ G.V) := by
      rw [← himg_eq]
      exact h_ioo_pc.image hphi_cont
    have hsub_diff : closure e \ G.V ⊆ G.U \ G.V := by
      have hclU : closure e ⊆ G.U := G.isClosed_U.closure_subset_iff.mpr (he.2.1.trans sdiff_subset)
      exact sdiff_subset_sdiff_left hclU
    have he_sub_diff : e ⊆ closure e \ G.V :=
      subset_sdiff.mpr ⟨subset_closure, disjoint_left.mpr fun _ hxe hxV => (he.2.1 hxe).2 hxV⟩
    have hdiff_eq : closure e \ G.V = e :=
      he.2.2.2 (closure e \ G.V) hsub_diff hpc_diff he_sub_diff
    calc closure e
      _ = (closure e \ G.V) ∪ (closure e ∩ G.V) := (sdiff_union_inter (closure e) G.V).symm
      _ = e ∪ {u, v} := by rw [hdiff_eq, hcap]
  · exfalso
    have hpair : ({u, v} : Set S) = {u'} := hcap.symm.trans hcap'
    have hu_eq : u = u' := by
      have : u ∈ ({u, v} : Set S) := mem_insert u {v}
      rw [hpair] at this
      exact mem_singleton_iff.mp this
    have hv_eq : v = u' := by
      have : v ∈ ({u, v} : Set S) := mem_insert_of_mem u rfl
      rw [hpair] at this
      exact mem_singleton_iff.mp this
    exact hne (hu_eq.trans hv_eq.symm)

/-- Every walk in a subgraph `C ≤ G.toGraph` produces a compact connected point-set in `S`
contained in `V(C) ∪ ⋃ e ∈ E(C), e` (skipping self-loop steps). -/
theorem exists_compact_connected_of_walk {S : Type u} [TopologicalSpace S]
    (G : Drawing S) {C : Graph S (Set S)} (hCG : C ≤ G.toGraph)
    {u v : S} (W : GraphWalk C u v) :
    ∃ K : Set S, IsCompact K ∧ IsConnected K ∧ u ∈ K ∧ v ∈ K ∧
      K ⊆ V(C) ∪ ⋃ e ∈ E(C), e ∧
      K ⊆ G.U ∧ K ∩ G.V ⊆ V(C) := by
  induction W with
  | @nil u hu =>
    refine ⟨{u}, isCompact_singleton, isConnected_singleton,
      mem_singleton u, mem_singleton u, ?_, ?_, ?_⟩
    · intro x hx
      left
      exact (mem_singleton_iff.mp hx) ▸ hu
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact G.V_subset_U (hCG.vertexSet_mono hu)
    · intro x hx
      exact (mem_singleton_iff.mp hx.1) ▸ hu
  | @cons u w v e hlink _ ih =>
    rcases ih with ⟨K', hK'_comp, hK'_conn, hwK', hvK', hK'_sub, hK'_U, hK'_V⟩
    rcases eq_or_ne u w with rfl | hne
    · exact ⟨K', hK'_comp, hK'_conn, hwK', hvK', hK'_sub, hK'_U, hK'_V⟩
    · have hlinkG : G.toGraph.IsLink e u w := hlink.mono hCG
      have hcl_eq : closure e = e ∪ {u, w} := closure_edge_eq_union_ends G hlinkG hne
      have hu_cl : u ∈ closure e := by
        rw [hcl_eq]; exact Or.inr (mem_insert u {w})
      have hw_cl : w ∈ closure e := by
        rw [hcl_eq]; exact Or.inr (mem_insert_of_mem u rfl)
      refine ⟨closure e ∪ K',
        (isCompact_closure_edge G hlinkG.1).union hK'_comp,
        IsConnected.union ⟨w, hw_cl, hwK'⟩ (isConnected_closure_edge G hlinkG.1) hK'_conn,
        Or.inl hu_cl, Or.inr hvK', ?_, ?_, ?_⟩
      · intro x hx
        rcases hx with hx_cl | hxK'
        · rw [hcl_eq] at hx_cl
          rcases hx_cl with hxe | (rfl | rfl)
          · right
            exact mem_iUnion₂.mpr ⟨e, hlink.edge_mem, hxe⟩
          · left; exact hlink.left_mem
          · left; exact hlink.right_mem
        · exact hK'_sub hxK'
      · have hcl_U : closure e ⊆ G.U :=
          G.isClosed_U.closure_subset_iff.mpr (hlinkG.1.2.1.trans sdiff_subset)
        exact union_subset hcl_U hK'_U
      · intro x hx
        rcases hx with ⟨hx_cl | hxK', hxV⟩
        · have hx_cap : x ∈ closure e ∩ G.V := ⟨hx_cl, hxV⟩
          rw [hlinkG.2.2.2] at hx_cap
          rcases hx_cap with rfl | rfl
          · exact hlink.left_mem
          · exact hlink.right_mem
        · exact hK'_V ⟨hxK', hxV⟩

/-! ## 2. Janiszewski's Theorem for Disjoint Closed Sets on a Closed Disc Space -/

/-- **Janiszewski's theorem on a closed disc space** (disjoint case): if `K₁, K₂ ⊆ S` are disjoint
closed subsets of a closed disc space `S`, `a, b ∉ K₁ ∪ K₂`, and `b` lies in the same connected
component as `a` in both `univ \ K₁` and `univ \ K₂`, then `b` lies in the same connected component
as `a` in `univ \ (K₁ ∪ K₂)`. -/
theorem disc_janiszewski_disjoint {S : Type u} [TopologicalSpace S] (hS : IsClosedDiscSpace S)
    {K₁ K₂ : Set S} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂) (hdisj : Disjoint K₁ K₂)
    {a b : S} (ha : a ∉ K₁ ∪ K₂) (hb : b ∉ K₁ ∪ K₂)
    (hab₁ : b ∈ connectedComponentIn (univ \ K₁) a)
    (hab₂ : b ∈ connectedComponentIn (univ \ K₂) a) :
    b ∈ connectedComponentIn (univ \ (K₁ ∪ K₂)) a := by
  obtain ⟨φ⟩ := hS
  let a₀ : EuclideanPlane := (φ.symm a).1
  have ha₀ : a₀ ∈ ClosedUnitDisc := (φ.symm a).2
  let ρ : EuclideanPlane → EuclideanPlane := fun x => (max (1 : ℝ) ‖x‖)⁻¹ • x
  have hρ_cont : Continuous ρ := by
    refine (Continuous.inv₀ (continuous_const.max continuous_norm) ?_).smul continuous_id
    intro x
    positivity
  have hρ_mem : ∀ x : EuclideanPlane, ρ x ∈ ClosedUnitDisc := by
    intro x
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv]
    have hpos : 0 < max (1 : ℝ) ‖x‖ := by positivity
    rw [abs_of_pos hpos, inv_mul_le_iff₀ hpos, mul_one]
    exact le_max_right 1 ‖x‖
  have hρ_id : ∀ x : ClosedUnitDisc, ρ x.1 = x.1 := by
    intro x
    have hx1 : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    simp [ρ, max_eq_left hx1]
  let t : EuclideanPlane → ℝ := fun x => min 1 (max 0 (‖x‖ - 1))
  have ht_cont : Continuous t :=
    continuous_const.min (continuous_const.max (continuous_norm.sub continuous_const))
  have ht0 : ∀ x, 0 ≤ t x := fun x => le_min zero_le_one (le_max_left 0 _)
  have ht1 : ∀ x, t x ≤ 1 := fun x => min_le_left 1 _
  let τ : EuclideanPlane → EuclideanPlane := fun x => (1 - t x) • ρ x + t x • a₀
  have hτ_cont : Continuous τ :=
    ((continuous_const.sub ht_cont).smul hρ_cont).add (ht_cont.smul continuous_const)
  have hτ_mem : ∀ x : EuclideanPlane, τ x ∈ ClosedUnitDisc := by
    intro x
    exact convex_closedBall (0 : EuclideanPlane) 1 (hρ_mem x) ha₀
      (sub_nonneg.mpr (ht1 x)) (ht0 x) (sub_add_cancel 1 (t x))
  have hτ_id : ∀ x : ClosedUnitDisc, τ x.1 = x.1 := by
    intro x
    have hx1 : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    have htx : t x.1 = 0 := by
      dsimp [t]
      rw [max_eq_left (by linarith), min_eq_right zero_le_one]
    simp [τ, htx, hρ_id x]
  have hτ_far : ∀ x : EuclideanPlane, 2 ≤ ‖x‖ → τ x = a₀ := by
    intro x hx2
    have htx : t x = 1 := by
      dsimp [t]
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
    simp [τ, htx]
  let F : ℂ → S := fun z => φ ⟨τ (complexPlane z), hτ_mem (complexPlane z)⟩
  have hF_cont : Continuous F :=
    φ.continuous.comp ((hτ_cont.comp complexPlane.continuous).subtype_mk _)
  let emb : S → ℂ := fun s => complexPlane.symm (φ.symm s).1
  have hemb_cont : Continuous emb :=
    complexPlane.symm.continuous.comp (continuous_subtype_val.comp φ.symm.continuous)
  have hF_emb : ∀ s : S, F (emb s) = s := by
    intro s
    dsimp [F, emb]
    have h_eq : (⟨τ (complexPlane (complexPlane.symm (φ.symm s).1)),
        hτ_mem (complexPlane (complexPlane.symm (φ.symm s).1))⟩ : ClosedUnitDisc) = φ.symm s := by
      ext
      simp [hτ_id (φ.symm s)]
    rw [h_eq, φ.apply_symm_apply]
  have hF_far : ∀ z : ℂ, 2 ≤ ‖z‖ → F z = a := by
    intro z hz2
    dsimp [F]
    have hnorm : 2 ≤ ‖complexPlane z‖ := by rwa [LinearIsometryEquiv.norm_map]
    have h_eq : (⟨τ (complexPlane z), hτ_mem (complexPlane z)⟩ : ClosedUnitDisc) = φ.symm a :=
      Subtype.ext (hτ_far (complexPlane z) hnorm)
    rw [h_eq, φ.apply_symm_apply]
  let L₁ : Set ℂ := F ⁻¹' K₁
  let L₂ : Set ℂ := F ⁻¹' K₂
  have hL₁_comp : IsCompact L₁ := by
    refine (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset (hK₁.preimage hF_cont) ?_
    intro z hz
    rw [mem_closedBall_zero_iff]
    by_contra hlt
    have hz_a : F z = a := hF_far z (le_of_not_ge hlt)
    exact ha (Or.inl (hz_a ▸ hz))
  have hL₂_comp : IsCompact L₂ := by
    refine (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset (hK₂.preimage hF_cont) ?_
    intro z hz
    rw [mem_closedBall_zero_iff]
    by_contra hlt
    have hz_a : F z = a := hF_far z (le_of_not_ge hlt)
    exact ha (Or.inr (hz_a ▸ hz))
  have hL_inter : L₁ ∩ L₂ = ∅ := by
    ext z
    simp only [L₁, L₂, mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
    exact fun h1 h2 => disjoint_left.mp hdisj h1 h2
  have hemb_a : emb a ∉ L₁ ∪ L₂ := by
    simp only [L₁, L₂, mem_union, mem_preimage, hF_emb]
    exact ha
  have hemb_b : emb b ∉ L₁ ∪ L₂ := by
    simp only [L₁, L₂, mem_union, mem_preimage, hF_emb]
    exact hb
  have hemb_ab₁ : emb b ∈ connectedComponentIn L₁ᶜ (emb a) := by
    refine (isPreconnected_connectedComponentIn.image emb
      hemb_cont.continuousOn).subset_connectedComponentIn ?_ ?_ (mem_image_of_mem emb hab₁)
    · exact mem_image_of_mem emb (mem_connectedComponentIn ⟨mem_univ a, fun h => ha (Or.inl h)⟩)
    · rintro _ ⟨s, hs, rfl⟩
      change F (emb s) ∉ K₁
      rw [hF_emb]
      exact (connectedComponentIn_subset _ _ hs).2
  have hemb_ab₂ : emb b ∈ connectedComponentIn L₂ᶜ (emb a) := by
    refine (isPreconnected_connectedComponentIn.image emb
      hemb_cont.continuousOn).subset_connectedComponentIn ?_ ?_ (mem_image_of_mem emb hab₂)
    · exact mem_image_of_mem emb (mem_connectedComponentIn ⟨mem_univ a, fun h => ha (Or.inr h)⟩)
    · rintro _ ⟨s, hs, rfl⟩
      change F (emb s) ∉ K₂
      rw [hF_emb]
      exact (connectedComponentIn_subset _ _ hs).2
  have h_jan := janiszewski hL₁_comp hL₂_comp (by rw [hL_inter]; exact isPreconnected_empty)
    hemb_a hemb_b hemb_ab₁ hemb_ab₂
  refine (isPreconnected_connectedComponentIn.image F
    hF_cont.continuousOn).subset_connectedComponentIn ?_ ?_ ⟨emb b, h_jan, hF_emb b⟩
  · exact ⟨emb a, mem_connectedComponentIn hemb_a, hF_emb a⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨mem_univ _, connectedComponentIn_subset _ _ hz⟩

/-! ## 3. Point-Sets of Graph Components and Region Connectivity -/

/-- The point-set of a subgraph `C` of a drawing `Γ`: `V(C) ∪ ⋃ e ∈ E(C), e`. -/
@[expose] def compPointSet {S : Type u} (C : Graph S (Set S)) : Set S :=
  V(C) ∪ ⋃ e ∈ E(C), e

theorem compPointSet_eq_closure_union {S : Type u} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) {C : Graph S (Set S)} (hC : IsGraphComponent C Γ.toGraph) :
    compPointSet C = V(C) ∪ ⋃ e ∈ E(C), closure e := by
  ext x
  simp only [compPointSet, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (hxV | ⟨e, heC, hxe⟩)
    · exact Or.inl hxV
    · exact Or.inr ⟨e, heC, subset_closure hxe⟩
  · rintro (hxV | ⟨e, heC, hxcl⟩)
    · exact Or.inl hxV
    · obtain ⟨u, v, hlinkC⟩ := C.exists_isLink_of_mem_edgeSet heC
      have hlinkG : Γ.toGraph.IsLink e u v := hlinkC.mono hC.1
      obtain ⟨γ, hγ, _, _, _, himg, hcl, hlinkγ⟩ := exists_edge_param_isLink Γ hlinkG.1
      have hpair : ({γ 0, γ 1} : Set S) = {u, v} := hlinkγ.2.2.2.symm.trans hlinkG.2.2.2
      rw [hcl] at hxcl
      obtain ⟨t, rfl⟩ := hxcl
      by_cases ht0 : t = 0
      · subst ht0
        have : γ 0 ∈ ({u, v} : Set S) := hpair ▸ mem_insert (γ 0) {γ 1}
        rcases this with h1 | h2
        · exact Or.inl (h1 ▸ hlinkC.left_mem)
        · exact Or.inl (mem_singleton_iff.mp h2 ▸ hlinkC.right_mem)
      · by_cases ht1 : t = 1
        · subst ht1
          have : γ 1 ∈ ({u, v} : Set S) := hpair ▸ mem_insert_of_mem (γ 0) rfl
          rcases this with h1 | h2
          · exact Or.inl (h1 ▸ hlinkC.left_mem)
          · exact Or.inl (mem_singleton_iff.mp h2 ▸ hlinkC.right_mem)
        · right
          refine ⟨e, heC, ?_⟩
          rw [← himg]
          exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
            unitInterval.lt_one_iff_ne_one.mpr ht1⟩, rfl⟩

theorem isClosed_compPointSet {S : Type u} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) {C : Graph S (Set S)} (hC : IsGraphComponent C Γ.toGraph) :
    IsClosed (compPointSet C) := by
  rw [compPointSet_eq_closure_union Γ hC]
  have hV_fin : V(C).Finite := Γ.finite_V.subset hC.1.vertexSet_mono
  have hE_fin : E(C).Finite := Γ.finite_edges.subset hC.1.edgeSet_mono
  exact hV_fin.isClosed.union (hE_fin.isClosed_biUnion fun e _ => isClosed_closure)

theorem disjoint_compPointSet_of_ne {S : Type u} [TopologicalSpace S]
    (Γ : Drawing S) {C₁ C₂ : Graph S (Set S)}
    (h₁ : IsGraphComponent C₁ Γ.toGraph) (h₂ : IsGraphComponent C₂ Γ.toGraph) (hne : C₁ ≠ C₂) :
    Disjoint (compPointSet C₁) (compPointSet C₂) := by
  have hV_disj : Disjoint V(C₁) V(C₂) := h₁.disjoint_vertexSet_of_ne h₂ hne
  have hE_disj : Disjoint E(C₁) E(C₂) := h₁.disjoint_edgeSet_of_ne h₂ hne
  refine disjoint_left.mpr fun z hz1 hz2 => ?_
  rcases hz1 with hzV1 | hzE1 <;> rcases hz2 with hzV2 | hzE2
  · exact disjoint_left.mp hV_disj hzV1 hzV2
  · simp only [mem_iUnion, exists_prop] at hzE2
    rcases hzE2 with ⟨e₂, he₂C, hze₂⟩
    have he₂G : e₂ ∈ Γ.E := h₂.1.edgeSet_mono he₂C
    exact (he₂G.2.1 hze₂).2 (h₁.1.vertexSet_mono hzV1)
  · simp only [mem_iUnion, exists_prop] at hzE1
    rcases hzE1 with ⟨e₁, he₁C, hze₁⟩
    have he₁G : e₁ ∈ Γ.E := h₁.1.edgeSet_mono he₁C
    exact (he₁G.2.1 hze₁).2 (h₂.1.vertexSet_mono hzV2)
  · simp only [mem_iUnion, exists_prop] at hzE1 hzE2
    rcases hzE1 with ⟨e₁, he₁C, hze₁⟩
    rcases hzE2 with ⟨e₂, he₂C, hze₂⟩
    have he_ne : e₁ ≠ e₂ := fun h => disjoint_left.mp hE_disj he₁C (h ▸ he₂C)
    exact disjoint_left.mp
      (disjoint_edges_of_ne Γ (h₁.1.edgeSet_mono he₁C) (h₂.1.edgeSet_mono he₂C) he_ne) hze₁ hze₂

theorem finite_graphComponents {S : Type u} [TopologicalSpace S] (Γ : Drawing S) :
    (graphComponents Γ.toGraph).Finite := by
  refine (Γ.finite_V.image (compOf Γ.toGraph)).subset fun C hC => ?_
  obtain ⟨v, hv⟩ := hC.2.1.1
  exact ⟨v, hC.1.vertexSet_mono hv, (hC.eq_compOf_of_mem hv).symm⟩

theorem biUnion_compPointSet_eq_U {S : Type u} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) :
    (⋃ C ∈ graphComponents Γ.toGraph, compPointSet C) = Γ.U := by
  ext x
  simp only [mem_iUnion, exists_prop, compPointSet, mem_union]
  constructor
  · rintro ⟨C, hC, hxV | ⟨e, heC, hxe⟩⟩
    · exact Γ.V_subset_U (hC.1.vertexSet_mono hxV)
    · exact ((hC.1.edgeSet_mono heC).2.1 hxe).1
  · intro hxU
    by_cases hxV : x ∈ Γ.V
    · exact ⟨compOf Γ.toGraph x, isGraphComponent_compOf hxV, Or.inl (self_mem_reachSet hxV)⟩
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
      obtain ⟨γ, _, h0, _, _, _, _, hlink⟩ := exists_edge_param_isLink Γ he
      have hC : IsGraphComponent (compOf Γ.toGraph (γ 0)) Γ.toGraph := isGraphComponent_compOf h0
      have heC : e ∈ E(compOf Γ.toGraph (γ 0)) :=
        ((hC.isLink_iff_of_mem (self_mem_reachSet h0)).mpr hlink).edge_mem
      exact ⟨compOf Γ.toGraph (γ 0), hC, Or.inr ⟨e, heC, hxe⟩⟩

theorem compPointSet_inter_bd_eq {S : Type u} [TopologicalSpace S]
    (Γ : Drawing S) (hProper : Γ.IsProper) {C : Graph S (Set S)}
    (hC : IsGraphComponent C Γ.toGraph) :
    compPointSet C ∩ bd S = V(C) ∩ bd S := by
  ext x
  simp only [compPointSet, mem_inter_iff, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hxV | ⟨e, heC, hxe⟩, hxbd⟩
    · exact ⟨hxV, hxbd⟩
    · have heG : e ∈ Γ.E := hC.1.edgeSet_mono heC
      have hxV : x ∈ Γ.V := hProper ⟨hxbd, (heG.2.1 hxe).1⟩
      exact ((heG.2.1 hxe).2 hxV).elim
  · rintro ⟨hxV, hxbd⟩
    exact ⟨Or.inl hxV, hxbd⟩

/-- If `u₁, u₂ ∈ bd S \ Γ.U` and no connected component `C` of a proper drawing `Γ` on a closed
disc space `S` has two boundary vertices `v₁, v₂ ∈ V(C) ∩ bd S` crossing `{u₁, u₂}` on `bd S`,
then `u₁` and `u₂` lie in the same region of `Γ`. -/
theorem same_region_of_no_component_crosses {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) (Γ : Drawing S) (hProper : Γ.IsProper)
    {u₁ u₂ : S} (hu₁_bd : u₁ ∈ bd S) (hu₂_bd : u₂ ∈ bd S)
    (hu₁_U : u₁ ∉ Γ.U) (hu₂_U : u₂ ∉ Γ.U)
    (hno_cross : ∀ C ∈ graphComponents Γ.toGraph,
      ∀ v₁ ∈ V(C) ∩ bd S, ∀ v₂ ∈ V(C) ∩ bd S, ¬ CrossesOn (bd S) v₁ v₂ u₁ u₂) :
    connectedComponentIn (univ \ Γ.U) u₁ = connectedComponentIn (univ \ Γ.U) u₂ := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  rcases eq_or_ne u₁ u₂ with rfl | hne
  · rfl
  obtain ⟨φ⟩ := hS.isOArc_bd
  have hinj := injective_oArcMap φ
  let x : Circle := φ.symm ⟨u₁, hu₁_bd⟩
  let y : Circle := φ.symm ⟨u₂, hu₂_bd⟩
  have hx_map : oArcMap φ x = u₁ := by simp [oArcMap, x]
  have hy_map : oArcMap φ y = u₂ := by simp [oArcMap, y]
  have hxy : x ≠ y := fun h => hne (hx_map ▸ hy_map ▸ congrArg (oArcMap φ) h)
  let B₁ : Set S := oArcMap φ '' range (Circle.path x y)
  let B₂ : Set S := oArcMap φ '' range (Circle.path y x)
  have hB₁_conn : IsPreconnected B₁ :=
    (isConnected_range (Circle.path x y).continuous).isPreconnected.image _
      (isEmbedding_oArcMap φ).continuous.continuousOn
  have hB₂_conn : IsPreconnected B₂ :=
    (isConnected_range (Circle.path y x).continuous).isPreconnected.image _
      (isEmbedding_oArcMap φ).continuous.continuousOn
  have hu₁_B₁ : u₁ ∈ B₁ := ⟨x, ⟨0, (Circle.path x y).source⟩, hx_map⟩
  have hu₂_B₁ : u₂ ∈ B₁ := ⟨y, ⟨1, (Circle.path x y).target⟩, hy_map⟩
  have hu₁_B₂ : u₁ ∈ B₂ := ⟨x, ⟨1, (Circle.path y x).target⟩, hx_map⟩
  have hu₂_B₂ : u₂ ∈ B₂ := ⟨y, ⟨0, (Circle.path y x).source⟩, hy_map⟩
  let C₁_set := {C ∈ graphComponents Γ.toGraph | V(C) ∩ bd S ⊆ B₂}
  let C₂_set := {C ∈ graphComponents Γ.toGraph | ¬ (V(C) ∩ bd S ⊆ B₂)}
  let K₁ : Set S := ⋃ C ∈ C₁_set, compPointSet C
  let K₂ : Set S := ⋃ C ∈ C₂_set, compPointSet C
  have hC₁_fin : C₁_set.Finite := (finite_graphComponents Γ).subset fun _ h => h.1
  have hC₂_fin : C₂_set.Finite := (finite_graphComponents Γ).subset fun _ h => h.1
  have hK₁_closed : IsClosed K₁ :=
    hC₁_fin.isClosed_biUnion fun C hC => isClosed_compPointSet Γ hC.1
  have hK₂_closed : IsClosed K₂ :=
    hC₂_fin.isClosed_biUnion fun C hC => isClosed_compPointSet Γ hC.1
  have hK_union : K₁ ∪ K₂ = Γ.U := by
    rw [← biUnion_compPointSet_eq_U Γ]
    ext z
    simp only [K₁, K₂, C₁_set, C₂_set, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro (⟨C, ⟨hC, _⟩, hz⟩ | ⟨C, ⟨hC, _⟩, hz⟩) <;> exact ⟨C, hC, hz⟩
    · rintro ⟨C, hC, hz⟩
      by_cases hsub : V(C) ∩ bd S ⊆ B₂
      · exact Or.inl ⟨C, ⟨hC, hsub⟩, hz⟩
      · exact Or.inr ⟨C, ⟨hC, hsub⟩, hz⟩
  have hK_disj : Disjoint K₁ K₂ := by
    refine disjoint_left.mpr ?_
    rintro z hz1 hz2
    simp only [K₁, K₂, mem_iUnion, exists_prop] at hz1 hz2
    rcases hz1 with ⟨C₁, hC₁, hzC₁⟩
    rcases hz2 with ⟨C₂, hC₂, hzC₂⟩
    have hne_C : C₁ ≠ C₂ := fun h => hC₂.2 (h ▸ hC₁.2)
    exact disjoint_left.mp (disjoint_compPointSet_of_ne Γ hC₁.1 hC₂.1 hne_C) hzC₁ hzC₂
  have hB₁_inter_B₂ : B₁ ∩ B₂ = {u₁, u₂} := by
    dsimp only [B₁, B₂]
    rw [← image_inter hinj, Circle.range_path_inter_range_path hxy, image_pair, hx_map, hy_map]
  have hB₁_sub : B₁ ⊆ univ \ K₁ := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    simp only [K₁, mem_iUnion, exists_prop, not_exists, not_and]
    intro C hC hzC
    have hz_bd : oArcMap φ w ∈ bd S := oArcMap_mem φ w
    have hz_V : oArcMap φ w ∈ V(C) ∩ bd S := by
      rw [← compPointSet_inter_bd_eq Γ hProper hC.1]
      exact ⟨hzC, hz_bd⟩
    have hz_B₂ : oArcMap φ w ∈ B₂ := hC.2 hz_V
    have hz_pair : oArcMap φ w ∈ ({u₁, u₂} : Set S) :=
      hB₁_inter_B₂ ▸ ⟨⟨w, hw, rfl⟩, hz_B₂⟩
    have hz_U : oArcMap φ w ∈ Γ.U := by
      rw [← hK_union]
      exact Or.inl (mem_iUnion₂.mpr ⟨C, hC, hzC⟩)
    rcases hz_pair with h1 | h2
    · exact hu₁_U (h1 ▸ hz_U)
    · exact hu₂_U (mem_singleton_iff.mp h2 ▸ hz_U)
  have hB₂_sub : B₂ ⊆ univ \ K₂ := by
    rintro z ⟨w₂, hw₂, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    simp only [K₂, mem_iUnion, exists_prop, not_exists, not_and]
    intro C hC hzC
    have hv₂_bd : oArcMap φ w₂ ∈ bd S := oArcMap_mem φ w₂
    have hv₂_V : oArcMap φ w₂ ∈ V(C) ∩ bd S := by
      rw [← compPointSet_inter_bd_eq Γ hProper hC.1]
      exact ⟨hzC, hv₂_bd⟩
    obtain ⟨v₁, hv₁_V, hv₁_notB₂⟩ := not_subset.mp hC.2
    let w₁ : Circle := φ.symm ⟨v₁, hv₁_V.2⟩
    have hw₁_map : oArcMap φ w₁ = v₁ := by simp [oArcMap, w₁]
    have hw₁_arc : w₁ ∈ circleOpenArc x y := by
      rw [← compl_range_circlePath hxy.symm]
      intro hw₁_in
      exact hv₁_notB₂ ⟨w₁, hw₁_in, hw₁_map⟩
    have hw₂_notB₁ : oArcMap φ w₂ ∉ B₁ := by
      intro hz_B₁
      have hz_pair : oArcMap φ w₂ ∈ ({u₁, u₂} : Set S) :=
        hB₁_inter_B₂ ▸ ⟨hz_B₁, ⟨w₂, hw₂, rfl⟩⟩
      have hz_U : oArcMap φ w₂ ∈ Γ.U := by
        rw [← hK_union]
        exact Or.inr (mem_iUnion₂.mpr ⟨C, hC, hzC⟩)
      rcases hz_pair with h1 | h2
      · exact hu₁_U (h1 ▸ hz_U)
      · exact hu₂_U (mem_singleton_iff.mp h2 ▸ hz_U)
    have hw₂_arc : w₂ ∈ circleOpenArc y x := by
      rw [← compl_range_circlePath hxy]
      intro hw₂_in
      exact hw₂_notB₁ ⟨w₂, hw₂_in, rfl⟩
    have hcross_circle : CrossesOn (univ : Set Circle) x y w₁ w₂ := by
      have hw₁_not : w₁ ∉ ({x, y} : Set Circle) := by
        change w₁ ∈ ({x, y} : Set Circle)ᶜ
        rw [compl_pair_eq_union_circleOpenArc hxy]
        exact Or.inl hw₁_arc
      have hw₂_not : w₂ ∉ ({x, y} : Set Circle) := by
        change w₂ ∈ ({x, y} : Set Circle)ᶜ
        rw [compl_pair_eq_union_circleOpenArc hxy]
        exact Or.inr hw₂_arc
      have hw₁w₂ : w₁ ≠ w₂ := fun h =>
        (disjoint_circleOpenArc hxy).ne_of_mem hw₁_arc hw₂_arc h
      refine ⟨trivial, trivial, trivial, trivial, hxy, hw₁w₂,
        fun h => hw₁_not (Or.inl h.symm), fun h => hw₂_not (Or.inl h.symm),
        fun h => hw₁_not (Or.inr h.symm), fun h => hw₂_not (Or.inr h.symm), ?_⟩
      rw [← compl_eq_univ_sdiff,
        connectedComponentIn_compl_pair_eq_left hxy hw₁_arc,
        connectedComponentIn_compl_pair_eq_right hxy hw₂_arc]
      intro heq
      obtain ⟨z₀, hz₀⟩ := nonempty_circleOpenArc hxy
      exact (disjoint_circleOpenArc hxy).ne_of_mem hz₀ (heq ▸ hz₀) rfl
    have hcross_bd : CrossesOn (bd S) v₁ (oArcMap φ w₂) u₁ u₂ := by
      rw [← hw₁_map, ← hx_map, ← hy_map, crossesOn_oArcMap_iff]
      exact hcross_circle.comm isOArc_univ_circle
    exact hno_cross C hC.1 v₁ hv₁_V (oArcMap φ w₂) hv₂_V hcross_bd
  have hu₁_notK : u₁ ∉ K₁ ∪ K₂ := hK_union.symm ▸ hu₁_U
  have hu₂_notK : u₂ ∉ K₁ ∪ K₂ := hK_union.symm ▸ hu₂_U
  have hab₁ : u₂ ∈ connectedComponentIn (univ \ K₁) u₁ :=
    hB₁_conn.subset_connectedComponentIn hu₁_B₁ hB₁_sub hu₂_B₁
  have hab₂ : u₂ ∈ connectedComponentIn (univ \ K₂) u₁ :=
    hB₂_conn.subset_connectedComponentIn hu₁_B₂ hB₂_sub hu₂_B₂
  have h_jan := disc_janiszewski_disjoint hS hK₁_closed hK₂_closed hK_disj
    hu₁_notK hu₂_notK hab₁ hab₂
  rw [hK_union] at h_jan
  exact connectedComponentIn_eq h_jan

/-! ## 4. Spanning Trees and Proof of Theorem (3.2) -/

private def walkToRestrictDiff {α : Type u} {β : Type v} {C : Graph α β} {e₀ : β}
    {x y : α} (W : GraphWalk C x y)
    (hedges : ∀ e ∈ W.edges, e ≠ e₀) : GraphWalk (C.restrict (E(C) \ {e₀})) x y :=
  match W with
  | .nil hx => .nil hx
  | @GraphWalk.cons _ _ _ x v y e h rest =>
    have hne : e ≠ e₀ := hedges e (by simp [GraphWalk.edges])
    have hlink' : (C.restrict (E(C) \ {e₀})).IsLink e x v := by
      rw [restrict_isLink]
      exact ⟨⟨h.edge_mem, hne⟩, h⟩
    .cons hlink'
      (walkToRestrictDiff rest fun e' he' => hedges e' (by simp [GraphWalk.edges, he']))

private theorem walkAvoidEdge {α : Type u} {β : Type v} {C : Graph α β} {e₀ : β} {u₀ w₀ : α}
    (hlink₀ : C.IsLink e₀ u₀ w₀)
    (P : GraphWalk (C.restrict (E(C) \ {e₀})) w₀ u₀)
    {x y : α} (W : GraphWalk C x y) :
    Nonempty (GraphWalk (C.restrict (E(C) \ {e₀})) x y) := by
  classical
  induction W with
  | nil hx => exact ⟨.nil hx⟩
  | @cons a b y e h rest ih =>
    obtain ⟨W_rest⟩ := ih
    rcases eq_or_ne a b with rfl | hab
    · exact ⟨W_rest⟩
    · rcases eq_or_ne e e₀ with rfl | hne
      · rcases h.left_eq_or_eq hlink₀ with rfl | rfl
        · rcases h.symm.left_eq_or_eq hlink₀ with rfl | rfl
          · exact (hab rfl).elim
          · exact ⟨P.reverse.append W_rest⟩
        · rcases h.symm.left_eq_or_eq hlink₀.symm with rfl | rfl
          · exact (hab rfl).elim
          · exact ⟨P.append W_rest⟩
      · have hlink' : (C.restrict (E(C) \ {e₀})).IsLink e a b := by
          rw [restrict_isLink]
          exact ⟨⟨h.edge_mem, hne⟩, h⟩
        exact ⟨.cons hlink' W_rest⟩

/-- Every connected graph with finitely many edges has a spanning tree (a connected forest subgraph
with the same vertex set). -/
theorem exists_spanning_tree {α : Type u} {β : Type v} {C : Graph α β}
    (hE_fin : E(C).Finite) (hConn : IsGraphConnected C) :
    ∃ T : Graph α β, T ≤ C ∧ V(T) = V(C) ∧ IsGraphConnected T ∧ IsGraphForest T := by
  classical
  induction hn : E(C).ncard using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases hF : IsGraphForest C
    · exact ⟨C, le_rfl, rfl, hConn, hF⟩
    · unfold IsGraphForest at hF
      push Not at hF
      obtain ⟨u₀, W, hW_sc, hW_len⟩ := hF
      cases W with
      | nil _ => exact (hW_len rfl).elim
      | @cons _ w₀ _ e₀ hlink₀ rest =>
        have hnodup : (e₀ :: rest.edges).Nodup := hW_sc.2
        have he₀_not_rest : e₀ ∉ rest.edges := (List.nodup_cons.mp hnodup).1
        let C' := C.restrict (E(C) \ {e₀})
        have hE_C' : E(C') = E(C) \ {e₀} := by
          ext e
          simp only [C', edgeSet_restrict, mem_inter_iff, mem_sdiff, mem_singleton_iff]
          tauto
        let P : GraphWalk C' w₀ u₀ :=
          walkToRestrictDiff rest (fun e he h => he₀_not_rest (h ▸ he))
        have hConn' : IsGraphConnected C' := by
          refine ⟨hConn.1, fun x hx y hy => ?_⟩
          obtain ⟨W_xy⟩ := hConn.2 x hx y hy
          exact walkAvoidEdge hlink₀ P W_xy
        have hE'_fin : E(C').Finite := hE_fin.subset (hE_C' ▸ sdiff_subset)
        have hlt : E(C').ncard < n := by
          rw [hE_C', ← hn]
          exact ncard_sdiff_singleton_lt_of_mem hlink₀.edge_mem hE_fin
        obtain ⟨T, hTC', hVT, hConnT, hFT⟩ := ih _ hlt hE'_fin hConn' rfl
        exact ⟨T, hTC'.trans restrict_le, hVT, hConnT, hFT⟩

theorem isDivision_dualDivision {S : Type u} [TopologicalSpace S]
    {C U : Set S} {Δ : Set (Set S)}
    (hC : IsOArc C) (hV_fin : (divisionUnion Δ).Finite) (hV_sub : divisionUnion Δ ⊆ C)
    (hU : IsDualPointSet C (divisionUnion Δ) U) :
    IsDivision (dualDivision C U Δ) :=
  isDivision_dualDivision_of_isOArc hC hV_fin hV_sub hU

theorem isFeasible_empty {α β : Type*} (G : Graph α β) :
    IsFeasible G (∅ : Set (Set α)) := by
  refine ⟨⊥, ⟨finite_empty, fun _ h => False.elim h, fun _ h => False.elim h⟩, ?_, bot_le, ?_,
    fun _ => ⊥, injOn_empty _, fun _ h => False.elim h, ?_⟩
  · simp [divisionUnion]
  · intro u W _
    cases W with
    | nil hu => exact False.elim hu
    | cons h _ => exact False.elim h.left_mem
  · ext C
    simp only [graphComponents, mem_ofPred_eq, image_empty, mem_empty_iff_false, iff_false]
    intro hC
    rcases hC.2.1.1 with ⟨v, hv⟩
    exact hC.1.vertexSet_mono hv

private theorem span_V_eq_self {S : Type u} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) (E' : Set (Set S)) :
    (G.span G.V E').V = G.V := by
  refine Subset.antisymm (G.spanV_subset G.V E') ?_
  intro v hv
  exact Or.inl ⟨hv, hv⟩

private def walkSpanToSubgraph {S : Type u} [TopologicalSpace S] [T2Space S]
    {G : Drawing S} {H : Graph S (Set S)} (hHG : H ≤ G.toGraph)
    {x y : S} (hx : x ∈ V(H)) :
    GraphWalk (G.span G.V E(H)).toGraph x y → GraphWalk H x y
  | .nil _ => .nil hx
  | @GraphWalk.cons _ _ _ x v y e h rest =>
    have heH : e ∈ E(H) := by
      have he_span : e ∈ (G.span G.V E(H)).E := h.1
      rw [G.span_E G.V E(H)] at he_span
      exact he_span.1
    have hV_eq : (G.span G.V E(H)).V = G.V := span_V_eq_self G E(H)
    have hG : G.toGraph.IsLink e x v := by
      refine ⟨hHG.edgeSet_mono heH, ?_, ?_, ?_⟩
      · have := h.2.1; rwa [hV_eq] at this
      · have := h.2.2.1; rwa [hV_eq] at this
      · have := h.2.2.2; rwa [hV_eq] at this
    have hH : H.IsLink e x v := (hHG.isLink_iff heH).mpr hG
    .cons hH (walkSpanToSubgraph hHG hH.right_mem rest)

private theorem isFeasible_of_dual_components {S : Type u} [TopologicalSpace S]
    {C U : Set S} {Δ : Set (Set S)} {G_dual : Drawing S} {K_star : Graph S (Set S)}
    (hC : IsOArc C) (hV_sub : divisionUnion Δ ⊆ C) (hU_sub : U ⊆ C \ divisionUnion Δ)
    (hK_le : K_star ≤ G_dual.toGraph) (hU_vertices : U ⊆ V(K_star)) :
    let Δ_star := dualDivision C U Δ
    IsDivision Δ_star → divisionUnion Δ_star = U →
    (∀ u₁ ∈ U, ∀ u₂ ∈ U, Nonempty (GraphWalk K_star u₁ u₂) → dualEquivRel C Δ u₁ u₂) →
    (∀ u₁ ∈ U, ∀ u₂ ∈ U, dualEquivRel C Δ u₁ u₂ → Nonempty (GraphWalk K_star u₁ u₂)) →
    IsFeasible G_dual.toGraph Δ_star := by
  classical
  intro Δ_star hΔ_star_div hΔ_star_union h_walk_imp_equiv h_equiv_imp_walk
  have : Finite Δ_star := hΔ_star_div.1
  obtain ⟨k, ⟨enum₀⟩⟩ := Finite.exists_equiv_fin Δ_star
  let enum : Fin k ≃ Δ_star := enum₀.symm
  have hrep : ∀ i : Fin k, (enum i).1.Nonempty := fun i => hΔ_star_div.2.1 (enum i).1 (enum i).2
  let u₀ : Fin k → S := fun i => (hrep i).some
  have hu₀_mem : ∀ i : Fin k, u₀ i ∈ (enum i).1 := fun i => (hrep i).some_mem
  have hu₀_U : ∀ i : Fin k, u₀ i ∈ U := fun i =>
    hΔ_star_union ▸ ⟨(enum i).1, (enum i).2, hu₀_mem i⟩
  have hu₀_V : ∀ i : Fin k, u₀ i ∈ V(K_star) := fun i => hU_vertices (hu₀_U i)
  let C_fam : Fin k → Graph S (Set S) := fun i => compOf K_star (u₀ i)
  have hC_comp : ∀ i : Fin k, IsGraphComponent (C_fam i) K_star :=
    fun i => isGraphComponent_compOf (hu₀_V i)
  have hδ_sub_C : ∀ i : Fin k, (enum i).1 ⊆ V(C_fam i) := by
    intro i u hu
    have hu_U : u ∈ U := hΔ_star_union ▸ ⟨(enum i).1, (enum i).2, hu⟩
    have hδ_eq := dualDivision_mem_eq_of_mem hC hV_sub hU_sub (enum i).2 (hu₀_mem i)
    have hequiv : dualEquivRel C Δ (u₀ i) u := by
      rw [hδ_eq] at hu
      exact hu.2
    exact ⟨hU_vertices hu_U, h_equiv_imp_walk (u₀ i) (hu₀_U i) u hu_U hequiv⟩
  have hC_ne : ∀ {i j : Fin k}, i ≠ j → C_fam i ≠ C_fam j := by
    intro i j hne heq
    have hu_in : u₀ j ∈ V(C_fam i) := heq ▸ self_mem_reachSet (hu₀_V j)
    have hequiv : dualEquivRel C Δ (u₀ i) (u₀ j) :=
      h_walk_imp_equiv (u₀ i) (hu₀_U i) (u₀ j) (hu₀_U j) hu_in.2
    have hδ_eq := dualDivision_mem_eq_of_mem hC hV_sub hU_sub (enum i).2 (hu₀_mem i)
    have hu₀j_in_i : u₀ j ∈ (enum i).1 := by
      rw [hδ_eq]
      exact ⟨hu₀_U j, hequiv⟩
    have hne_δ : (enum i).1 ≠ (enum j).1 := fun h => hne (enum.injective (Subtype.ext h))
    exact (hΔ_star_div.2.2 (enum i).2 (enum j).2 hne_δ).ne_of_mem hu₀j_in_i (hu₀_mem j) rfl
  have hT_exists : ∀ i : Fin k, ∃ T : Graph S (Set S),
      T ≤ C_fam i ∧ V(T) = V(C_fam i) ∧ IsGraphConnected T ∧ IsGraphForest T := by
    intro i
    have hE_fin : E(C_fam i).Finite :=
      G_dual.finite_edges.subset ((hC_comp i).1.trans hK_le).edgeSet_mono
    exact exists_spanning_tree hE_fin (hC_comp i).2.1
  choose T_fam hT_le hT_V hT_conn hT_forest using hT_exists
  have hT_le_Gd : ∀ i : Fin k, T_fam i ≤ G_dual.toGraph :=
    fun i => (hT_le i).trans ((hC_comp i).1.trans hK_le)
  have hT_V_disj : Pairwise fun i j : Fin k => Disjoint V(T_fam i) V(T_fam j) := by
    intro i j hne
    rw [hT_V i, hT_V j]
    exact (hC_comp i).disjoint_vertexSet_of_ne (hC_comp j) (hC_ne hne)
  have hT_E_disj : Pairwise fun i j : Fin k => Disjoint E(T_fam i) E(T_fam j) := by
    intro i j hne
    exact ((hC_comp i).disjoint_edgeSet_of_ne (hC_comp j) (hC_ne hne)).mono
      (hT_le i).edgeSet_mono (hT_le j).edgeSet_mono
  have hT_is_comp_self : ∀ i : Fin k, IsGraphComponent (T_fam i) (T_fam i) :=
    fun i => ⟨le_rfl, hT_conn i, fun C' hle hle' _ => le_antisymm hle' hle⟩
  have hcomp_in_Ti : ∀ (i : Fin k) (K : Graph S (Set S)),
      IsGraphComponent K (T_fam i) ↔ K = T_fam i := by
    intro i K
    refine ⟨fun hK => (hK.2.2 (T_fam i) hK.1 le_rfl (hT_conn i)).symm, ?_⟩
    rintro rfl
    exact hT_is_comp_self i
  let H_star := graphUnionFamily G_dual.toGraph T_fam
  let H_star_comp : Set S → Graph S (Set S) := fun δ =>
    if hδ : δ ∈ Δ_star then T_fam (enum.symm ⟨δ, hδ⟩) else ⊥
  have hΔ_star_sub_Gd : divisionUnion Δ_star ⊆ V(G_dual.toGraph) := by
    rw [hΔ_star_union]
    exact hU_vertices.trans hK_le.vertexSet_mono
  refine ⟨H_star, hΔ_star_div, hΔ_star_sub_Gd,
    graphUnionFamily_le G_dual.toGraph T_fam hT_le_Gd,
    isGraphForest_graphUnionFamily hT_le_Gd hT_V_disj hT_E_disj hT_forest,
    H_star_comp, ?_, ?_, ?_⟩
  · intro δ₁ hδ₁ δ₂ hδ₂ heq
    dsimp only [H_star_comp] at heq
    simp only [hδ₁, hδ₂, ↓reduceDIte] at heq
    let i₁ := enum.symm ⟨δ₁, hδ₁⟩
    let i₂ := enum.symm ⟨δ₂, hδ₂⟩
    have hi_eq : i₁ = i₂ := by
      by_contra hne
      have h_v : u₀ i₁ ∈ V(T_fam i₁) := by rw [hT_V i₁]; exact self_mem_reachSet (hu₀_V i₁)
      have h_v2 : u₀ i₁ ∈ V(T_fam i₂) := heq ▸ h_v
      exact disjoint_left.mp (hT_V_disj hne) h_v h_v2
    exact congrArg Subtype.val (enum.symm.injective hi_eq)
  · intro δ hδ
    dsimp only [H_star_comp]
    simp only [hδ, ↓reduceDIte]
    let i := enum.symm ⟨δ, hδ⟩
    have hi_val : (enum i).1 = δ := congrArg Subtype.val (enum.apply_symm_apply ⟨δ, hδ⟩)
    refine ⟨(isGraphComponent_graphUnionFamily_iff hT_le_Gd hT_V_disj hT_E_disj).mpr
      ⟨i, hT_is_comp_self i⟩, ?_⟩
    rw [hT_V i, ← hi_val]
    exact hδ_sub_C i
  · ext K
    change IsGraphComponent K H_star ↔ K ∈ H_star_comp '' Δ_star
    rw [isGraphComponent_graphUnionFamily_iff hT_le_Gd hT_V_disj hT_E_disj, mem_image]
    constructor
    · rintro ⟨i, hKi⟩
      rw [hcomp_in_Ti i K] at hKi
      subst hKi
      refine ⟨(enum i).1, (enum i).2, ?_⟩
      dsimp only [H_star_comp]
      simp [(enum i).2]
    · rintro ⟨δ, hδ, rfl⟩
      dsimp only [H_star_comp]
      simp only [hδ, ↓reduceDIte]
      exact ⟨enum.symm ⟨δ, hδ⟩, hT_is_comp_self _⟩

/-- Forward direction of Graph Minors VI, (3.2): if `Δ` is feasible in `G`, then `Δ*` is feasible
in `G_dual`. -/
theorem isFeasible_dualDivision_of_isFeasible {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) {G G_dual : Drawing S} {Δ : Set (Set S)}
    (hDual : IsDiscDualDrawing G G_dual) (_hΔ : IsDivision Δ)
    (hΔ_union : divisionUnion Δ = G.V ∩ bd S)
    (hFeas : IsFeasible G.toGraph Δ) :
    IsFeasible G_dual.toGraph (dualDivision (bd S) (G_dual.V ∩ bd S) Δ) := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  let U := G_dual.V ∩ bd S
  let Δ_star := dualDivision (bd S) U Δ
  have hC : IsOArc (bd S) := hS.isOArc_bd
  have hV_fin : (divisionUnion Δ).Finite := by
    rw [hΔ_union]
    exact G.finite_V.subset inter_subset_left
  have hV_sub : divisionUnion Δ ⊆ bd S := by
    rw [hΔ_union]
    exact inter_subset_right
  have hU : IsDualPointSet (bd S) (divisionUnion Δ) U := by
    rw [hΔ_union]
    exact hDual.2.2.2.2.1
  have hU_sub : U ⊆ bd S \ divisionUnion Δ := isDualPointSet_subset_diff hU
  have hΔ_star_div : IsDivision Δ_star := isDivision_dualDivision hC hV_fin hV_sub hU
  have hΔ_star_union : divisionUnion Δ_star = U := divisionUnion_dualDivision (bd S) U Δ
  obtain ⟨H, _, _, hHG, _, H_comp, hinj_H, hcomp_H, _⟩ := hFeas
  obtain ⟨edgeEquiv, hedge⟩ := hDual.2.2.2.2.2.2
  let Γ' : Drawing S := G.span G.V E(H)
  have hsub_Γ' : Γ'.IsSubdrawing G := Drawing.span_isSubdrawing G G.V E(H)
  have hΓ'_V : Γ'.V = G.V := span_V_eq_self G E(H)
  have hprop_Γ' : Γ'.IsProper := by
    rintro x ⟨hxbd, hxU⟩
    rw [hΓ'_V]
    exact hDual.1 ⟨hxbd, hsub_Γ'.U_subset hxU⟩
  let E_star : Set (Set S) :=
    {e' ∈ G_dual.E | ∃ e : G.E, (edgeEquiv e).1 = e' ∧ e.1 ∉ E(H)}
  let K_star : Graph S (Set S) := G_dual.toGraph.restrict E_star
  have hK_le : K_star ≤ G_dual.toGraph := restrict_le
  -- 1. Walk in K_star between u₁, u₂ ∈ U implies dualEquivRel (bd S) Δ u₁ u₂
  have h_walk_imp_equiv : ∀ u₁ ∈ U, ∀ u₂ ∈ U,
      Nonempty (GraphWalk K_star u₁ u₂) → dualEquivRel (bd S) Δ u₁ u₂ := by
    rintro u₁ _ u₂ _ ⟨W⟩ ⟨δ, hδ, v₁, hv₁, v₂, hv₂, hcross⟩
    have hCδ : IsGraphComponent (H_comp δ) H := (hcomp_H δ hδ).1
    have hv₁C : v₁ ∈ V(H_comp δ) := (hcomp_H δ hδ).2 hv₁
    have hv₂C : v₂ ∈ V(H_comp δ) := (hcomp_H δ hδ).2 hv₂
    obtain ⟨W_H⟩ := hCδ.2.1.2 v₁ hv₁C v₂ hv₂C
    obtain ⟨K_H, hKH_comp, hKH_conn, hv₁_KH, hv₂_KH, hKH_sub, hKH_U, _⟩ :=
      exists_compact_connected_of_walk G (hCδ.1.trans hHG) W_H
    obtain ⟨K_W, hKW_comp, hKW_conn, hu₁_KW, hu₂_KW, hKW_sub, hKW_U, _⟩ :=
      exists_compact_connected_of_walk G_dual hK_le W
    obtain ⟨z, hzH, hzW⟩ := discCrossing_of_isClosedDiscSpace hS
      hKH_comp hKW_comp hKH_conn hKW_conn hv₁_KH hv₂_KH hu₁_KW hu₂_KW hcross
    rcases hKH_sub hzH with hzVH | hzEH
    · exact disjoint_left.mp hDual.disjoint_V_dual_U
        ((hCδ.1.trans hHG).vertexSet_mono hzVH) (hKW_U hzW)
    · rcases hKW_sub hzW with hzVW | hzEW
      · obtain ⟨r, hr, hzr⟩ := hDual.2.2.2.1 z hzVW
        exact region_subset hr hzr (hKH_U hzH)
      · simp only [mem_iUnion, exists_prop] at hzEH hzEW
        obtain ⟨e₁, he₁C, hze₁⟩ := hzEH
        obtain ⟨e', he'K, hze'⟩ := hzEW
        have he₁H : e₁ ∈ E(H) := hCδ.1.edgeSet_mono he₁C
        have he₁G : e₁ ∈ G.E := hHG.edgeSet_mono he₁H
        have he'E : e' ∈ E_star := he'K.2
        obtain ⟨_, e₀, rfl, he₀_notH⟩ := he'E
        have hz_cap : z ∈ (edgeEquiv e₀).1 ∩ G.U := ⟨hze', hKH_U hzH⟩
        rw [(hedge e₀).1] at hz_cap
        have heq_e : e₁ = e₀.1 := by
          by_contra hne
          exact disjoint_left.mp (disjoint_edges_of_ne G he₁G e₀.2 hne) hze₁ hz_cap.2
        exact he₀_notH (heq_e ▸ he₁H)
  -- 2. dualEquivRel (bd S) Δ u₁ u₂ implies a walk in K_star between u₁ and u₂
  have h_equiv_imp_walk : ∀ u₁ ∈ U, ∀ u₂ ∈ U,
      dualEquivRel (bd S) Δ u₁ u₂ → Nonempty (GraphWalk K_star u₁ u₂) := by
    intro u₁ hu₁ u₂ hu₂ hequiv
    have hu₁_not_GU : u₁ ∉ G.U := by
      obtain ⟨r, hr, hur⟩ := hDual.2.2.2.1 u₁ hu₁.1
      exact region_subset hr hur
    have hu₂_not_GU : u₂ ∉ G.U := by
      obtain ⟨r, hr, hur⟩ := hDual.2.2.2.1 u₂ hu₂.1
      exact region_subset hr hur
    have hu₁_not_Γ'U : u₁ ∉ Γ'.U := fun h => hu₁_not_GU (hsub_Γ'.U_subset h)
    have hu₂_not_Γ'U : u₂ ∉ Γ'.U := fun h => hu₂_not_GU (hsub_Γ'.U_subset h)
    have hno_cross : ∀ C ∈ graphComponents Γ'.toGraph,
        ∀ v₁ ∈ V(C) ∩ bd S, ∀ v₂ ∈ V(C) ∩ bd S, ¬ CrossesOn (bd S) v₁ v₂ u₁ u₂ := by
      intro C hC v₁ hv₁ v₂ hv₂ hcross
      have hv₁_div : v₁ ∈ divisionUnion Δ := by
        rw [hΔ_union]
        have hv₁_Γ' : v₁ ∈ Γ'.V := hC.1.vertexSet_mono hv₁.1
        rw [hΓ'_V] at hv₁_Γ'
        exact ⟨hv₁_Γ', hv₁.2⟩
      have hv₂_div : v₂ ∈ divisionUnion Δ := by
        rw [hΔ_union]
        have hv₂_Γ' : v₂ ∈ Γ'.V := hC.1.vertexSet_mono hv₂.1
        rw [hΓ'_V] at hv₂_Γ'
        exact ⟨hv₂_Γ', hv₂.2⟩
      obtain ⟨δ₁, hδ₁, hv₁_δ₁⟩ := hv₁_div
      obtain ⟨δ₂, hδ₂, hv₂_δ₂⟩ := hv₂_div
      have hv₁_H : v₁ ∈ V(H) :=
        (hcomp_H δ₁ hδ₁).1.1.vertexSet_mono ((hcomp_H δ₁ hδ₁).2 hv₁_δ₁)
      obtain ⟨W_C⟩ := hC.2.1.2 v₁ hv₁.1 v₂ hv₂.1
      let W_H : GraphWalk H v₁ v₂ := walkSpanToSubgraph hHG hv₁_H (W_C.mono hC.1)
      have hv₂_in_comp1 : v₂ ∈ V(H_comp δ₁) := by
        rw [(hcomp_H δ₁ hδ₁).1.eq_compOf_of_mem ((hcomp_H δ₁ hδ₁).2 hv₁_δ₁)]
        exact ⟨W_H.mem_vertexSet_of_mem_support W_H.end_mem_support, ⟨W_H⟩⟩
      have hv₂_in_comp2 : v₂ ∈ V(H_comp δ₂) := (hcomp_H δ₂ hδ₂).2 hv₂_δ₂
      have hδ_eq : δ₁ = δ₂ := hinj_H hδ₁ hδ₂
        ((hcomp_H δ₁ hδ₁).1.eq_of_mem_mem (hcomp_H δ₂ hδ₂).1 hv₂_in_comp1 hv₂_in_comp2)
      subst hδ_eq
      exact hequiv ⟨δ₁, hδ₁, v₁, hv₁_δ₁, v₂, hv₂_δ₂, hcross⟩
    have hsame_reg := same_region_of_no_component_crosses hS Γ' hprop_Γ'
      hu₁.2 hu₂.2 hu₁_not_Γ'U hu₂_not_Γ'U hno_cross
    let r' := connectedComponentIn (univ \ Γ'.U) u₁
    have hr' : r' ∈ Γ'.R := ⟨u₁, ⟨mem_univ u₁, hu₁_not_Γ'U⟩, rfl⟩
    obtain ⟨r₁, hr₁, hu₁_r₁⟩ := hDual.2.2.2.1 u₁ hu₁.1
    obtain ⟨r₂, hr₂, hu₂_r₂⟩ := hDual.2.2.2.1 u₂ hu₂.1
    have hs₁ : r₁ ⊆ r' := subset_region hr' (region_isPreconnected hr₁)
      (disjoint_left.mpr fun y hy h => region_subset hr₁ hy (hsub_Γ'.U_subset h))
      hu₁_r₁ (mem_connectedComponentIn ⟨mem_univ u₁, hu₁_not_Γ'U⟩)
    have hs₂ : r₂ ⊆ r' := subset_region hr' (region_isPreconnected hr₂)
      (disjoint_left.mpr fun y hy h => region_subset hr₂ hy (hsub_Γ'.U_subset h))
      hu₂_r₂ (by dsimp [r']; rw [hsame_reg]; exact mem_connectedComponentIn ⟨mem_univ u₂,
        hu₂_not_Γ'U⟩)
    let Z : Set (Set S) := {r ∈ G.R | ∃ w ∈ r ∩ G_dual.V, w ∈ reachSet K_star u₁}
    have hz₁ : r₁ ∈ Z := ⟨hr₁, u₁, ⟨hu₁_r₁, hu₁.1⟩, self_mem_reachSet hu₁.1⟩
    by_contra hnot_walk
    have hz₂ : r₂ ∉ Z := by
      rintro ⟨_, w, ⟨hw_r₂, hw_V⟩, hw_reach⟩
      have hwu₂ : w = u₂ := (hDual.2.2.1 r₂ hr₂).unique ⟨hw_r₂, hw_V⟩ ⟨hu₂_r₂, hu₂.1⟩
      exact hnot_walk (hwu₂ ▸ hw_reach).2
    obtain ⟨e₀, he₀G, he₀_not, a, b, haZ, hbZ, _, _, hia, hib⟩ :=
      disc_theorem_5_1 hS hDual.1 hsub_Γ' hr' hr₁ hz₁ hr₂ hz₂ hs₁ hs₂
    have haR : a ∈ G.R := hia.2.1
    have hbR : b ∈ G.R := hib.2.1
    have hab_ne : a ≠ b := fun h => hbZ (h ▸ haZ)
    have ha_inc : e₀ ⊆ closure a := disc_edge_subset_closure_of_incident hS hDual.1 he₀G haR hia.2.2
    have hb_inc : e₀ ⊆ closure b := disc_edge_subset_closure_of_incident hS hDual.1 he₀G hbR hib.2.2
    have hall_inc : ∀ r ∈ G.R, G.EdgeRegionIncident e₀ r → r = a ∨ r = b := by
      intro r hr hinc
      have hr_inc : e₀ ⊆ closure r := disc_edge_subset_closure_of_incident hS hDual.1 he₀G hr
        hinc.2.2
      rcases disc_region_incident_two hS hDual.1 he₀G haR hbR hr ha_inc hb_inc hr_inc with
        hab | har | hbr
      · exact (hab_ne hab).elim
      · exact Or.inl har.symm
      · exact Or.inr hbr.symm
    obtain ⟨_, w_a, hwa_mem, hwa_reach⟩ := haZ
    obtain ⟨w_b, hwb_mem, _⟩ := hDual.2.2.1 b hbR
    let e_sub : G.E := ⟨e₀, he₀G⟩
    have hlink_dual : G_dual.toGraph.IsLink (edgeEquiv e_sub).1 w_a w_b :=
      ((hedge e_sub).2.2.2.2 a haR b hbR w_a hwa_mem w_b hwb_mem).mpr ⟨hia, hib, hall_inc⟩
    have he'_star : (edgeEquiv e_sub).1 ∈ E_star := by
      refine ⟨(edgeEquiv e_sub).2, e_sub, rfl, ?_⟩
      intro he₀H
      apply he₀_not
      rw [G.span_E G.V E(H)]
      exact ⟨he₀H, he₀G⟩
    have hlink_K : K_star.IsLink (edgeEquiv e_sub).1 w_a w_b := by
      rw [restrict_isLink]
      exact ⟨he'_star, hlink_dual⟩
    exact hbZ ⟨hbR, w_b, hwb_mem, reachSet_step hwa_reach hlink_K⟩
  -- 3. Assemble a forest realization of Δ_star in G_dual.toGraph
  change IsFeasible G_dual.toGraph Δ_star
  by_cases hΔ_star_empty : Δ_star = ∅
  · rw [hΔ_star_empty]
    exact isFeasible_empty G_dual.toGraph
  exact isFeasible_of_dual_components hC hV_sub hU_sub hK_le inter_subset_left
    hΔ_star_div hΔ_star_union h_walk_imp_equiv h_equiv_imp_walk

/-- **Graph Minors VI, (3.2)** (page 120):
"Let $G$ be a connected graph, properly drawn on a disc $\Sigma$. Let $\Delta$ be a
cross-free division with* $$\bigcup \Delta = V(G) \cap bd(\Sigma).$$ *Let the drawing of
$G^*$ be chosen so that* $$\bigcup \Delta^* = V(G^*) \cap bd(\Sigma).$$ *Then $\Delta$ is
feasible in $G$ if and only if $\Delta^*$ is feasible in $G^*$." -/
theorem theorem_3_2_proof : Statement32.{u} := by
  intro S _ G G_dual Δ hS hConn hΔ hΔ_union hCF hDual
  constructor
  · exact isFeasible_dualDivision_of_isFeasible hS hDual hΔ hΔ_union
  · intro hFeas_dual
    have hDual_symm : IsDiscDualDrawing G_dual G := hDual.symm_of_connected hS hConn
    let U := G_dual.V ∩ bd S
    let Δ_star := dualDivision (bd S) U Δ
    have hC : IsOArc (bd S) := hS.isOArc_bd
    have hV_fin : (divisionUnion Δ).Finite := by
      rw [hΔ_union]
      exact G.finite_V.subset inter_subset_left
    have hV_sub : divisionUnion Δ ⊆ bd S := by
      rw [hΔ_union]
      exact inter_subset_right
    have hU : IsDualPointSet (bd S) (divisionUnion Δ) U := by
      rw [hΔ_union]
      exact hDual.2.2.2.2.1
    have hΔ_star_div : IsDivision Δ_star := isDivision_dualDivision hC hV_fin hV_sub hU
    have hΔ_star_union : divisionUnion Δ_star = G_dual.V ∩ bd S :=
      divisionUnion_dualDivision (bd S) U Δ
    have hFeas_double :=
      isFeasible_dualDivision_of_isFeasible hS hDual_symm hΔ_star_div hΔ_star_union hFeas_dual
    have h_double : dualDivision (bd S) (G.V ∩ bd S) Δ_star = Δ := by
      rw [← hΔ_union]
      exact theorem_2_2_proof (bd S) U Δ hC hΔ hV_fin hV_sub hU hCF
    rwa [h_double] at hFeas_double

end GraphMinor.GM06
