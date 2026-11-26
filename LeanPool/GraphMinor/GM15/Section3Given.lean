/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.ChordMove
import LeanPool.GraphMinor.GM15.Section3SpanGlue

/-!
# Graph Minors XV, (3.4), for a given drawing $H'$

(3.4), page 122, takes any drawing $H' = H \cup P_1 \cup \dots \cup P_{k-1}$ in $\Sigma$ with
$H' \cap (\Sigma - \Lambda) = H$. The proof on pages 122–123 is formalized in
`theorem_3_4_of_chart` (`GraphMinor/GM15/Section3Parallel.lean`), in a chart of $\bar\Lambda$ in
which the paths are vertical chords. Here we first show that the paths are lines across
$\bar\Lambda$, then move them onto the chords by a homeomorphism of the unit disc that fixes the
circle (`exists_ballHomeo_moving_chords`), and so get such a chart (`theorem_3_4_proof`).

Section 7 applies (3.4) to paths of $G$, which must first be drawn in $\Lambda$.
`theorem_3_4_drawn` draws them along chords of a chart (`exists_glued_span_of_lines`) and applies
`theorem_3_4_proof`.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology Metric
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM12 GM14

universe u v w

/-- A chart of $\bar\Lambda$ that puts $v_1, \dots, v_{2k}$ at the angles `parallelModelAngle k`. -/
theorem exists_chart_3_4 {S : Type w} [TopologicalSpace S] {Λ : Set S} {k : ℕ}
    (hk1 : 1 ≤ k) {v : Fin (2 * k) → S} (hCD : IsClosedDisc (closure Λ))
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hOrder_v : GM12.IsListedInOrderOn (subBd Λ) (List.ofFn v)) :
    ∃ p_circ : Circle ≃ₜ ↥(subBd Λ),
      (∀ i : Fin (2 * k), (p_circ (Circle.exp (parallelModelAngle k i.1))).1 = v i) ∧
      ∃ (h : S → ℂ) (g : ℂ → S), IsChart (closure Λ) h g ∧ ∀ w : Circle, g w = (p_circ w).1 := by
  obtain ⟨f_v, t_v, ht_v_mono, ht_v_bd, ht_v_val⟩ := hOrder_v
  obtain ⟨h_circ, hh_circ⟩ :=
    exists_circle_homeo_matching_angles (2 * k) (by omega)
      (parallelModelAngle k) t_v
      (strictMono_parallelModelAngle hk1) ht_v_mono
      (parallelModelAngle_lt_add_two_pi hk1)
      (fun i hi => ht_v_bd i (by simp [hi]))
  let p_circ : Circle ≃ₜ ↥(subBd Λ) := h_circ.trans f_v
  have hp_circ_v : ∀ i : Fin (2 * k),
      (p_circ (Circle.exp (parallelModelAngle k i.1))).1 = v i := by
    intro i
    change (f_v (h_circ (Circle.exp (parallelModelAngle k i.1)))).1 = v i
    rw [hh_circ i.1 i.2]
    exact (ht_v_val i.1 (by simp [i.2])).trans (by simp)
  let p_discBd : Circle ≃ₜ ↥(discBd (closure Λ)) :=
    p_circ.trans (Homeomorph.setCongr hdiscBd.symm)
  obtain ⟨h, g, c, hg_discBd⟩ := exists_isChart_with_bd hCD p_discBd
  exact ⟨p_circ, hp_circ_v, h, g, c, hg_discBd⟩

/-- The image of a line under a continuous map that is injective on it is a line. -/
theorem isLineWithEnds_image {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [T2Space T]
    {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) {φ : S → T} (hc : ContinuousOn φ L)
    (hi : InjOn φ L) : IsLineWithEnds (φ '' L) (φ a) (φ b) :=
  hL.image_under_injOn hc hi

/-- Replacing the chart `g` by `g ∘ Φ` for a homeomorphism `Φ` of the unit disc that fixes the
circle gives a chart that agrees with `g` on the circle. -/
theorem isChart_comp_ballHomeo {S : Type w} [TopologicalSpace S] {D : Set S} {h : S → ℂ}
    {g : ℂ → S} (c : IsChart D h g) {Φ Φ' : ℂ → ℂ} (hΦ : IsBallHomeo Φ Φ') :
    IsChart D (Φ' ∘ h) (g ∘ Φ) where
  hc := hΦ.cont'.comp c.hc c.hm
  gc := c.gc.comp hΦ.cont hΦ.maps
  hm := hΦ.maps'.comp c.hm
  gm := c.gm.comp hΦ.maps
  gh := fun x hx => by
    simp only [Function.comp_apply]
    rw [hΦ.right (c.hm hx), c.gh hx]
  hg := fun z hz => by
    simp only [Function.comp_apply]
    rw [c.hg (hΦ.maps hz), hΦ.left hz]
  bd := by
    rw [image_comp, c.bd]
    conv_rhs => rw [← image_id (sphere (0 : ℂ) 1)]
    exact image_congr fun z hz => hΦ.fix' hz

/-- **Graph Minors XV, (3.4)** (pages 122–123), for a given drawing $H'$, with the distance
monotonicity and boundary-order conclusions of `GM15Theorem34Statement`. -/
theorem theorem_3_4_proof : GM15Theorem34Statement.{u, v, w} := by
  classical
  intro S _ _ α β G H η θ_star θ k T_star T d Λ v H' η' P i_k i_last
    hSpan hd hΛ hOArc _hCirc_Λ hk hNodup_v hOrder_v hv_mem hFree_v hvm_H hem_H hInter hH'_V
    hH'_E hP_path hP_HU hP_disj hik hilast
  have hS : IsClosedSurface S :=
    ⟨hSpan.isSurface.1, hSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hResp_H : IsRespectfulDrawingTangle H θ T := hSpan.isRespectful
  have hinj : Injective v := List.nodup_ofFn.mp hNodup_v
  have h2k_le : 2 * k ≤ θ := by
    have hcard := hFree_v.2.1
    rwa [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  have hθ : 3 ≤ θ := by omega
  have hk1 : 1 ≤ k := by omega
  have hΛ_open : IsOpen Λ := GM11.region_isOpen hΛ
  obtain ⟨-, hCD, hdiscBd, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hResp_H hθ hΛ hOArc
  have hsubBd_eq_sdiff : subBd Λ = closure Λ \ Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
  obtain ⟨_, hU_bdΛ, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ hOArc
  have hsubBd_sub_HU : subBd Λ ⊆ H.U := by
    have hcl : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
    rw [← hU_bdΛ, (H.interSet (subBd Λ)).U_eq,
      interSet_V_of_isClosed H hcl, interSet_E]
    exact union_subset (inter_subset_left.trans H.V_subset_U)
      (iUnion₂_subset fun e he => H.closure_subset_U he.1)
  obtain ⟨p_circ, hp_circ_v, h, g, c, hg_circ⟩ := exists_chart_3_4 hk1 hCD hdiscBd hOrder_v
  let a : Fin (k - 1) → S := fun j => v ⟨j.1, by omega⟩
  let b : Fin (k - 1) → S := fun j => v ⟨2 * k - 2 - j.1, by omega⟩
  have hK : IsClosed (univ \ Λ) := isClosed_univ.sdiff hΛ_open
  -- `H` and each `P j` are subdrawings of `H'`.
  have hP_sub : ∀ j, (P j).IsSubdrawing H' := fun j => by
    refine ⟨?_, ?_⟩
    · rw [hH'_V]
      exact (subset_iUnion (fun j => (P j).V) j).trans subset_union_right
    · rw [hH'_E]
      exact (subset_iUnion (fun j => (P j).E) j).trans subset_union_right
  have hSub_H : H.IsSubdrawing H' := ⟨hH'_V ▸ subset_union_left, hH'_E ▸ subset_union_left⟩
  -- Each `P j` is a line from `a j` to `b j`.
  have hab : ∀ j : Fin (k - 1), a j ≠ b j := fun j hj => by
    have := congrArg Fin.val (hinj hj)
    simp only at this
    omega
  have hL_line : ∀ j, IsLineWithEnds (P j).U (a j) (b j) := fun j =>
    GM11.isLine_of_isPathBetween (hP_path j) (hab j)
  have hab_V : ∀ j, a j ∈ (P j).V ∧ b j ∈ (P j).V := fun j => by
    obtain ⟨W, -, hV, -⟩ := hP_path j
    rw [hV]
    exact ⟨W.start_mem_support, W.end_mem_support⟩
  -- Each `P j` meets `Σ - Λ` only in its ends: an edge of `P j` misses `H`, so it misses
  -- `bd(Λ)`; it is not in `Σ - Λ`, since `H' ∩ (Σ - Λ) = H`; so it lies in `Λ`.
  have hL_compl : ∀ j, (P j).U ∩ (univ \ Λ) = {a j, b j} := fun j => by
    have hends : ({a j, b j} : Set S) ⊆ (P j).V := by
      rintro _ (rfl | rfl)
      · exact (hab_V j).1
      · exact (hab_V j).2
    refine Subset.antisymm (fun x ⟨hxU, hxK⟩ => ?_) ?_
    · by_cases hxV : x ∈ (P j).V
      · have hxH : x ∈ H.V := by
          rw [← hInter, interSet_V_of_isClosed H' hK]
          exact ⟨(hP_sub j).1 hxV, hxK⟩
        rw [← hP_HU j]
        exact ⟨hxU, H.V_subset_U hxH⟩
      · exfalso
        obtain ⟨e, he, hxe⟩ := (P j).exists_edge_of_mem hxU hxV
        have heU : e ⊆ (P j).U := fun y hy => (he.2.1 hy).1
        have heV : ∀ y ∈ e, y ∉ (P j).V := fun y hy => (he.2.1 hy).2
        have heH : ∀ y ∈ e, y ∉ H.U := fun y hy hyH => by
          have : y ∈ (P j).U ∩ H.U := ⟨heU hy, hyH⟩
          rw [hP_HU j] at this
          exact heV y hy (hends this)
        have hsplit : e ⊆ Λ ∪ (closure Λ)ᶜ := fun y hy => by
          by_cases hyΛ : y ∈ Λ
          · exact Or.inl hyΛ
          · refine Or.inr fun hycl => heH y hy (hsubBd_sub_HU ?_)
            rw [hsubBd_eq_sdiff]
            exact ⟨hycl, hyΛ⟩
        rcases he.2.2.1.isConnected.isPreconnected.subset_or_subset hΛ_open
          isClosed_closure.isOpen_compl
          (disjoint_compl_right.mono_right (compl_subset_compl.mpr subset_closure)) hsplit with
          hΛe | hce
        · exact hxK.2 (hΛe hxe)
        · have heK : e ⊆ univ \ Λ := fun y hy =>
            ⟨mem_univ y, fun hyΛ => hce hy (subset_closure hyΛ)⟩
          have heHE : e ∈ H.E := by
            rw [← hInter, interSet_E]
            exact ⟨(hP_sub j).2 he, heK⟩
          exact heH x hxe (H.closure_subset_U heHE (subset_closure hxe))
    · rintro _ (rfl | rfl)
      · refine ⟨(P j).V_subset_U (hab_V j).1, mem_univ _, fun hΛa => ?_⟩
        have := (hv_mem ⟨j.1, by omega⟩).2
        rw [hsubBd_eq_sdiff] at this
        exact this.2 hΛa
      · refine ⟨(P j).V_subset_U (hab_V j).2, mem_univ _, fun hΛb => ?_⟩
        have := (hv_mem ⟨2 * k - 2 - j.1, by omega⟩).2
        rw [hsubBd_eq_sdiff] at this
        exact this.2 hΛb
  have hab_subBd : ∀ j, a j ∈ subBd Λ ∧ b j ∈ subBd Λ := fun j =>
    ⟨(hv_mem ⟨j.1, by omega⟩).2, (hv_mem ⟨2 * k - 2 - j.1, by omega⟩).2⟩
  have hL_cl : ∀ j, (P j).U ⊆ closure Λ := fun j x hx => by
    by_cases hxΛ : x ∈ Λ
    · exact subset_closure hxΛ
    · have : x ∈ (P j).U ∩ (univ \ Λ) := ⟨hx, mem_univ x, hxΛ⟩
      rw [hL_compl j] at this
      rcases this with rfl | rfl
      · exact (hab_subBd j).1.1
      · exact (hab_subBd j).2.1
  have hL_bd : ∀ j, (P j).U ∩ discBd (closure Λ) = {a j, b j} := fun j => by
    rw [← hL_compl j, hdiscBd, hsubBd_eq_sdiff]
    ext x
    exact ⟨fun ⟨hx, _, hxΛ⟩ => ⟨hx, mem_univ x, hxΛ⟩,
      fun ⟨hx, _, hxΛ⟩ => ⟨hx, hL_cl j hx, hxΛ⟩⟩
  -- The lines in the chart.
  have hg_a : ∀ j : Fin (k - 1), g ⟨parallelX k j, parallelY k j⟩ = a j := fun j => by
    rw [← circle_exp_parallelModelAngle_top j, hg_circ, hp_circ_v ⟨j.1, by omega⟩]
  have hg_b : ∀ j : Fin (k - 1), g ⟨parallelX k j, -parallelY k j⟩ = b j := fun j => by
    rw [← circle_exp_parallelModelAngle_bot j, hg_circ, hp_circ_v ⟨2 * k - 2 - j.1, by omega⟩]
  have hsph : ∀ j : Fin (k - 1), (⟨parallelX k j, parallelY k j⟩ : ℂ) ∈ closedBall (0 : ℂ) 1 ∧
      (⟨parallelX k j, -parallelY k j⟩ : ℂ) ∈ closedBall (0 : ℂ) 1 := fun j => by
    have := parallelX_sq_add_parallelY_sq j
    constructor <;> rw [mem_closedBall_unit_iff] <;> simp only <;> nlinarith
  have hh_a : ∀ j, h (a j) = ⟨parallelX k j, parallelY k j⟩ := fun j => by
    rw [← hg_a j, c.hg (hsph j).1]
  have hh_b : ∀ j, h (b j) = ⟨parallelX k j, -parallelY k j⟩ := fun j => by
    rw [← hg_b j, c.hg (hsph j).2]
  let M : Fin (k - 1) → Set ℂ := fun j => h '' (P j).U
  have hinjh : InjOn h (closure Λ) := c.gh.injOn
  have hMB : ∀ j, M j ⊆ closedBall (0 : ℂ) 1 := fun j => c.image_subset (hL_cl j)
  have hM : ∀ j, IsLineWithEnds (M j) ⟨parallelX k j, parallelY k j⟩
      ⟨parallelX k j, -parallelY k j⟩ := fun j => by
    rw [← hh_a j, ← hh_b j]
    exact isLineWithEnds_image (hL_line j) (c.hc.mono (hL_cl j)) (hinjh.mono (hL_cl j))
  have hMs : ∀ j, M j ∩ sphere (0 : ℂ) 1 =
      {⟨parallelX k j, parallelY k j⟩, ⟨parallelX k j, -parallelY k j⟩} := fun j => by
    rw [← c.bd, ← hinjh.image_inter (hL_cl j) (Surface.discBd_subset _), hL_bd j, image_pair,
      hh_a j,
      hh_b j]
  have hMdisj : Pairwise fun i j => Disjoint (M i) (M j) := fun i j hij =>
    disjoint_left.mpr fun _ ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩ =>
      disjoint_left.mp (hP_disj hij) hx
        (hinjh (hL_cl j hy) (hL_cl i hx) (hyz.trans hxz.symm) ▸ hy)
  obtain ⟨Φ, Φ', hΦ, hΦM⟩ := exists_ballHomeo_moving_chords (strictAnti_parallelX hk1)
    parallelX_sq_add_parallelY_sq parallelY_pos hMB hM hMs hMdisj
  -- The new chart `g ∘ Φ`, in which `P j` is the chord at `parallelX k j`.
  have c' := isChart_comp_ballHomeo c hΦ
  have hg'_circ : ∀ w : Circle, (g ∘ Φ) w = (p_circ w).1 := fun w => by
    simp only [Function.comp_apply]
    rw [hΦ.fix w (by simp), hg_circ]
  have hchord : ∀ j : Fin (k - 1), (g ∘ Φ) '' vertChord (parallelX k j) = (P j).U := fun j => by
    rw [image_comp, hΦM j, image_image]
    conv_rhs => rw [← image_id (P j).U]
    exact image_congr fun x hx => c.gh (hL_cl j hx)
  have hH'_U : H'.U = H.U ∪ ⋃ j : Fin (k - 1), (g ∘ Φ) '' vertChord (parallelX k j) := by
    simp_rw [hchord]
    apply Subset.antisymm
    · intro x hx
      by_cases hxV : x ∈ H'.V
      · rw [hH'_V] at hxV
        rcases hxV with hx | hx
        · exact Or.inl (H.V_subset_U hx)
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
          exact Or.inr (mem_iUnion.mpr ⟨j, (P j).V_subset_U hj⟩)
      · obtain ⟨e, he, hxe⟩ := H'.exists_edge_of_mem hx hxV
        rw [hH'_E] at he
        rcases he with he | he
        · exact Or.inl (H.closure_subset_U he (subset_closure hxe))
        · obtain ⟨j, hj⟩ := mem_iUnion.mp he
          exact Or.inr (mem_iUnion.mpr ⟨j, (P j).closure_subset_U hj (subset_closure hxe)⟩)
    · exact union_subset (isSubdrawing_U_subset hSub_H)
        (iUnion_subset fun j => isSubdrawing_U_subset (hP_sub j))
  have hP' : ∀ j : Fin (k - 1), (P j).U = (g ∘ Φ) '' vertChord (parallelX k j) ∧
      (P j).IsPathBetween (v ⟨j.1, by omega⟩) (v ⟨2 * k - 2 - j.1, by omega⟩) ∧
      (P j).IsSubdrawing H' ∧ v ⟨j.1, by omega⟩ ∈ (P j).V ∧
      v ⟨2 * k - 2 - j.1, by omega⟩ ∈ (P j).V := fun j =>
    ⟨(hchord j).symm, hP_path j, hP_sub j, (hab_V j).1, (hab_V j).2⟩
  obtain ⟨T', d', r₁, r₂, h₁, h₂, h₃, h₄, h₅, h₆, -, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆,
      h₁₇, h₁₈, h₁₉, h₂₀⟩ :=
    theorem_3_4_of_chart G H η θ_star θ k T_star T d Λ v i_k i_last hSpan hd hΛ hOArc hk
      hNodup_v hv_mem hFree_v hik hilast p_circ hp_circ_v c' hg'_circ H' η' P hH'_U hH'_V hH'_E
      hSub_H hP' hP_disj hvm_H hem_H
  exact ⟨T', d', r₁, r₂, h₁, h₂, h₃, h₄, h₅, h₆, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇,
    h₁₈, h₁₉, h₂₀⟩

/-- Graph Minors XV, (3.4), with auxiliary conclusions, applied to paths of `G`. The paths are
drawn along chords of a chart of $\bar\Lambda$, and `theorem_3_4_proof` applies to the drawing. -/
theorem theorem_3_4_drawn : GM15Theorem34DrawnStatement.{u, v, w} := by
  classical
  intro S _ _ α β G H η θ_star θ k T_star T d Λ v P i_k i_last
    hSpan hd hΛ hOArc hCirc_Λ hk hNodup_v hOrder_v hv_mem hFree_v
    hP_ex hP_disj hik hilast
  have hS : IsClosedSurface S :=
    ⟨hSpan.isSurface.1, hSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hResp_H : IsRespectfulDrawingTangle H θ T := hSpan.isRespectful
  have h2k_le : 2 * k ≤ θ := by
    have hinj : Injective v := List.nodup_ofFn.mp hNodup_v
    have hcard := hFree_v.2.1
    rwa [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  have hθ : 3 ≤ θ := by omega
  have hk1 : 1 ≤ k := by omega
  have hΛ_open : IsOpen Λ := GM11.region_isOpen hΛ
  obtain ⟨-, hCD, hdiscBd, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hResp_H hθ hΛ hOArc
  obtain ⟨_, hU_bdΛ, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ hOArc
  have hsubBd_sub_HU : subBd Λ ⊆ H.U := by
    have hcl : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
    rw [← hU_bdΛ, (H.interSet (subBd Λ)).U_eq,
      interSet_V_of_isClosed H hcl, interSet_E]
    exact union_subset (inter_subset_left.trans H.V_subset_U)
      (iUnion₂_subset fun e he => H.closure_subset_U he.1)
  have hHU_compl : H.U ⊆ univ \ Λ :=
    fun x hxU => ⟨mem_univ x, fun hxΛ => GM11.region_subset hΛ hxΛ hxU⟩
  obtain ⟨p_circ, hp_circ_v, h, g, c, hg_circ⟩ := exists_chart_3_4 hk1 hCD hdiscBd hOrder_v
  let a : Fin (k - 1) → S := fun j => v ⟨j.1, by omega⟩
  let b : Fin (k - 1) → S := fun j => v ⟨2 * k - 2 - j.1, by omega⟩
  have hg_a : ∀ j : Fin (k - 1), g ⟨parallelX k j, parallelY k j⟩ = a j :=
    fun j => (parallelChart_endpoints hg_circ hp_circ_v j).1
  have hg_b : ∀ j : Fin (k - 1), g ⟨parallelX k j, -parallelY k j⟩ = b j :=
    fun j => (parallelChart_endpoints hg_circ hp_circ_v j).2
  -- The paths are drawn along the vertical chords `L j` of the chart.
  let L : Fin (k - 1) → Set S := fun j => g '' vertChord (parallelX k j)
  have hcl_inter_compl : closure Λ ∩ (univ \ Λ) = subBd Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and]
  have hL_props := fun j : Fin (k - 1) =>
    parallelChart_chord_data c hdiscBd hcl_inter_compl hHU_compl hsubBd_sub_HU j (hg_a j) (hg_b j)
  have hL_line : ∀ j : Fin (k - 1), IsLineWithEnds (L j) (a j) (b j) :=
    fun j => (hL_props j).1
  have hL_inter_compl : ∀ j : Fin (k - 1), L j ∩ (univ \ Λ) = {a j, b j} :=
    fun j => (hL_props j).2.2.2.1
  have hL_inter_HU : ∀ j : Fin (k - 1), L j ∩ H.U = {a j, b j} :=
    fun j => (hL_props j).2.2.2.2
  have hL_disj : Pairwise (fun j₁ j₂ => Disjoint (L j₁) (L j₂)) := by
    intro j₁ j₂ hj
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, h_eq⟩
    exact Set.disjoint_left.mp
      (vertChord_disjoint ((strictAnti_parallelX hk1).injective.ne hj))
      hz₁ (c.injOn hz₁.1 hz₂.1 h_eq.symm ▸ hz₂)
  have ha_mem : ∀ j : Fin (k - 1), a j ∈ H.V ∩ subBd Λ := fun j => hv_mem ⟨j.1, by omega⟩
  have hb_mem : ∀ j : Fin (k - 1), b j ∈ H.V ∩ subBd Λ := fun j => hv_mem ⟨2 * k - 2 - j.1, by
    omega⟩
  have ha_V : ∀ j : Fin (k - 1), a j ∈ H.V := fun j => (ha_mem j).1
  have hb_V : ∀ j : Fin (k - 1), b j ∈ H.V := fun j => (hb_mem j).1
  have hP_ab : ∀ j : Fin (k - 1),
      IsHPathWithEnds G η.imageGraph (P j) (η.vMap (a j)) (η.vMap (b j)) := by
    intro j
    obtain ⟨i₁, i₂, hi₁, hi₂, hPj⟩ := hP_ex j
    have hi₁_eq : i₁ = ⟨j.1, by omega⟩ := Fin.ext hi₁
    have hi₂_eq : i₂ = ⟨2 * k - 2 - j.1, by omega⟩ := Fin.ext hi₂
    rwa [hi₁_eq, hi₂_eq] at hPj
  obtain ⟨P', H', η', hH'_U, hH'_V, hH'_E, hSub_H, hP', hP'_disj, hImG, hvm_H, hem_H, _, _⟩ :=
    exists_glued_span_of_lines H η a b P L ha_V hb_V hP_ab hP_disj hL_line hL_disj hL_inter_HU
  obtain ⟨-, -, hInter_compl⟩ :=
    glued_interSet_base_eq (isClosed_univ.sdiff hΛ_open) ha_V hb_V hHU_compl
      hL_inter_compl hH'_U hH'_V hH'_E hP'
  obtain ⟨T', d', r₁, r₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆,
      h₁₇, h₁₈, h₁₉⟩ :=
    theorem_3_4_proof G H η θ_star θ k T_star T d Λ v H' η' P' i_k i_last hSpan hd hΛ hOArc
      hCirc_Λ hk hNodup_v hOrder_v hv_mem hFree_v hvm_H hem_H hInter_compl hH'_V hH'_E
      (fun j => (hP' j).2.1) (fun j => (hP' j).1 ▸ hL_inter_HU j) hP'_disj hik hilast
  exact ⟨H', η', T', d', r₁, r₂, h₁, h₂, h₃, h₄, h₅, h₆, hInter_compl, h₇, hSub_H, hvm_H, hem_H,
    hImG, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩

end GraphMinor.GM15
