/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section7
public import LeanPool.GraphMinor.GM07.CutEdges
public import LeanPool.GraphMinor.GM07.Section9Grid
import LeanPool.GraphMinor.GM07.CuffSlide
import LeanPool.GraphMinor.GM07.Section35
public import LeanPool.GraphMinor.GM11.ArcDrawings
public import LeanPool.GraphMinor.Surface.DiscMerge
public import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Graph Minors VII, (9.1) and (9.2)

The proof of (9.1) inducts on the number of internal isolated vertices and
uses (7.5) in the base case. The closed-surface consequence (9.2) follows
from (9.1). These proofs precede the punctured-cylinder deduction of (9.3).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## Loop-addition invariance for boundary-rooted minors -/

/-- Unconditional proof of the observation in Graph Minors VII, proof of (9.1) (page 243: "If the
theorem is true for this new digraph it is true for $(H, H^+, H^-)$"): if `H'` is obtained from `H`
by adding edges (keeping the same vertex set `H'.G.V = H.G.V` and the same `plus`/`minus` endpoints
on `H.G.E`), then `IsBoundaryRootedMinor H' G` implies `IsBoundaryRootedMinor H G`. -/
theorem isBoundaryRootedMinor_of_edge_subdigraph {H H' G : SurfaceDigraph S}
    (hV : H'.G.V = H.G.V) (hE : H.G.E ⊆ H'.G.E)
    (hends : ∀ e ∈ H.G.E, H'.plus e = H.plus e ∧ H'.minus e = H.minus e)
    (hMinor : IsBoundaryRootedMinor H' G) :
    IsBoundaryRootedMinor H G := by
  rcases hMinor with ⟨hbd, φv, φe, hφv, hφe, hdisj, hinj, hnotMem, hinc, hroot⟩
  refine ⟨by rw [← hV]; exact hbd, φv, φe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact hφv v (hV.symm ▸ hv)
  · intro e he
    exact hφe e (hE he)
  · intro v hv v' hv' hne
    exact hdisj v (hV.symm ▸ hv) v' (hV.symm ▸ hv') hne
  · intro e he e' he' hne
    exact hinj e (hE he) e' (hE he') hne
  · intro v hv e he
    exact hnotMem v (hV.symm ▸ hv) e (hE he)
  · intro e he
    have h := hinc e (hE he)
    rw [(hends e he).1, (hends e he).2] at h
    exact h
  · intro v hv
    exact hroot v ⟨hV.symm ▸ hv.1, hv.2⟩

/-- `vModel a b c k` is monotone in `c` for all `c₁ ≤ c₂`. -/
theorem vModel_mono_c_le (a b : ℕ) {c₁ c₂ : ℕ} (hc : c₁ ≤ c₂) (k : ℕ) :
    vModel a b c₁ k ≤ vModel a b c₂ k := by
  induction hc with
  | refl => exact le_rfl
  | @step m _ ih => exact le_trans ih (vModel_mono_c a b m k)

private theorem punctured_circle_is_angle_image
    {S : Type u}
    (v : S)
    (F : Set S) :
    let e₀ : Set S := F \ {v}
    ∀ (p : ℝ → S),
    (p 0 = v) →
    (∀ (s t : ℝ), p s = p t → ∃ m : ℤ, s = t + (m : ℝ) * (2 * Real.pi)) →
    (p '' Ico 0 (2 * Real.pi) = F) →
    (range p ⊆ F) →
    (0 < 2 * Real.pi) →
    e₀ = p '' Ioo 0 (2 * Real.pi) := by
  intro e₀ p hp0 hper himg hr hpos
  ext y
  constructor
  · rintro ⟨hy, hyv⟩
    rw [← himg] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun hs0 => hyv ?_, hs.2⟩, rfl⟩
    rw [← hs0, hp0]
    rfl
  · rintro ⟨s, hs, rfl⟩
    refine ⟨hr ⟨s, rfl⟩, fun h => ?_⟩
    have h' : p s = p 0 := h.trans hp0.symm
    obtain ⟨m, hm⟩ := hper s 0 h'
    rw [zero_add] at hm
    have h₁ : (0 : ℝ) < m := by
      by_contra hc
      push Not at hc
      nlinarith [hs.1]
    have h₂ : (m : ℝ) < 1 := by
      by_contra hc
      push Not at hc
      nlinarith [hs.2]
    have h₃ : (0 : ℤ) < m := by exact_mod_cast h₁
    have h₄ : m < (1 : ℤ) := by exact_mod_cast h₂
    omega

private theorem auxiliary_loop_meets_graph_at_vertices {S : Type u} [TopologicalSpace S]
    (H : SurfaceDigraph S) {v : S} (hvV : v ∈ H.G.V) {Bad F : Set S}
    (hU_sub_Bad : H.G.U \ {v} ⊆ Bad) (hF_not_Bad : ∀ x ∈ F, x ∉ Bad)
    (D : Drawing S) (hDU : D.U = F) (hDV : D.V = {v}) :
    H.G.U ∩ D.U ⊆ H.G.V ∩ D.V := by
  rw [hDU, hDV]
  rintro x ⟨hxU, hxF⟩
  by_cases hxv : x = v
  · subst hxv
    exact ⟨hvV, rfl⟩
  · exact (hF_not_Bad x hxF (hU_sub_Bad ⟨hxU, hxv⟩)).elim

/-- Graph Minors VII, proof of (9.1), Step 1 (page 243):
"If $g \ne 0$, let us add a (directed) loop to an isolated vertex of $H$ not in $bd(\Sigma)$. If
the theorem is true for this new digraph it is true for $(H, H^+, H^-)$; and the new digraph
satisfies all the hypotheses of the theorem (leaving $k$ and $c$ unchanged)." -/
theorem addLoop_to_isolatedVertex [T1Space S] (hS : IsSurface S)
    (H : SurfaceDigraph S) (hH : H.IsProper)
    (hg_pos : 0 < numInternalIsolatedVertices H.G) :
    ∃ H' : SurfaceDigraph S,
      H'.IsProper ∧
      H'.G.V = H.G.V ∧
      H.G.E ⊆ H'.G.E ∧
      (∀ e ∈ H.G.E, H'.plus e = H.plus e ∧ H'.minus e = H.minus e) ∧
      H'.G.E.ncard = H.G.E.ncard + 1 ∧
      numInternalIsolatedVertices H'.G + 1 = numInternalIsolatedVertices H.G := by
  classical
  have : T2Space S := hS.2.1
  let IsoSet : Set S := {v ∈ H.G.V \ bd S | IsIsolatedVertex H.G v}
  have hIso_fin : IsoSet.Finite := (H.G.finite_V.subset sdiff_subset).sep _
  have hIso_ne : IsoSet.Nonempty := (ncard_pos hIso_fin).mp hg_pos
  obtain ⟨v, ⟨hvV, hv_not_bd⟩, hiso⟩ := hIso_ne
  have hv_not_cl : ∀ e ∈ H.G.E, v ∉ closure e := fun e he hcl =>
    hiso.2 e he ⟨hvV, Or.inl he, hcl⟩
  let Bad : Set S := bd S ∪ (H.G.V \ {v}) ∪ ⋃ e ∈ H.G.E, closure e
  have hBad_closed : IsClosed Bad :=
    ((isClosed_bd S).union (H.G.finite_V.subset sdiff_subset).isClosed).union
      (H.G.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
  have hv_not_Bad : v ∉ Bad := by
    rintro ((h | h) | h)
    · exact hv_not_bd h
    · exact h.2 rfl
    · obtain ⟨e, he, hve⟩ := mem_iUnion₂.mp h
      exact hv_not_cl e he hve
  have hU_sub_Bad : H.G.U \ {v} ⊆ Bad := by
    rintro x ⟨hxU, hxv⟩
    rw [H.G.U_eq] at hxU
    rcases hxU with hxV | hxE
    · exact Or.inl (Or.inr ⟨hxV, hxv⟩)
    · exact Or.inr hxE
  have hv_int : IsInteriorPoint v := not_not.mp hv_not_bd
  obtain ⟨U₀, h, g, hc, hU₀, h0⟩ :=
    hv_int.exists_ballChart hBad_closed.isOpen_compl hv_not_Bad (R := 3) (by norm_num)
  have hmem_ball : ∀ u : Circle, (u : ℂ) - 1 ∈ Metric.ball (0 : ℂ) 3 := fun u => by
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖(u : ℂ) - 1‖ ≤ ‖(u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by simp [Circle.norm_coe]
      _ < 3 := by norm_num
  let j : Circle → S := fun u => g ((u : ℂ) - 1)
  have hj_cont : Continuous j := hc.gc.comp_continuous (by fun_prop) hmem_ball
  have hj_inj : Function.Injective j := by
    intro u₁ u₂ heq
    have h₁ := hc.hg (hmem_ball u₁)
    have h₂ := hc.hg (hmem_ball u₂)
    have hsub_eq : (u₁ : ℂ) - 1 = (u₂ : ℂ) - 1 := by
      calc
        (u₁ : ℂ) - 1 = h (j u₁) := h₁.symm
        _ = h (j u₂) := congrArg h heq
        _ = (u₂ : ℂ) - 1 := h₂
    exact Subtype.ext (sub_left_inj.mp hsub_eq)
  let F : Set S := range j
  have hF_oarc : IsOArc F := ⟨(hj_cont.isClosedEmbedding hj_inj).isEmbedding.toHomeomorph⟩
  have hvF : v ∈ F := ⟨1, by simp [j, h0]⟩
  have hF_not_Bad : ∀ x ∈ F, x ∉ Bad := by
    rintro _ ⟨u, rfl⟩
    exact hU₀ (hc.gm (hmem_ball u))
  obtain ⟨D, hDU, hDV⟩ := GM11.exists_loop_drawing hF_oarc hvF
  let e₀ : Set S := F \ {v}
  obtain ⟨p, hp, hp0, hp2, hper, himg, hr⟩ := GM11.exists_oArc_par hF_oarc hvF
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hsd : e₀ = p '' Ioo 0 (2 * Real.pi) := by
    exact punctured_circle_is_angle_image (S := S) v F p hp0 hper himg hr hpos
  have hpc : IsPathConnected e₀ := by
    rw [hsd]
    exact ((convex_Ioo _ _).isPathConnected (nonempty_Ioo.mpr hpos)).image hp
  have he₀_ne : e₀.Nonempty := hpc.nonempty
  have hDE : D.E = {e₀} := by
    change arcComponentsIn (D.U \ D.V) = {e₀}
    rw [hDU, hDV]
    apply Subset.antisymm
    · rintro C ⟨-, hsub, -, hmax⟩
      exact mem_singleton_iff.mpr (hmax e₀ Subset.rfl hpc hsub).symm
    · rintro _ rfl
      exact ⟨he₀_ne, Subset.rfl, hpc, fun C hC _ hsub => Subset.antisymm hC hsub⟩
  have he₀_D : e₀ ∈ D.E := by rw [hDE]; exact mem_singleton e₀
  have hcl_e₀ : closure e₀ = F := by
    have hFc : IsClosed F := isCompact_range hj_cont |>.isClosed
    apply Subset.antisymm (closure_minimal sdiff_subset hFc)
    change F ⊆ closure e₀
    rw [hsd]
    intro y hy
    rw [← himg] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hs_cl : s ∈ closure (Ioo 0 (2 * Real.pi)) := by
      rw [closure_Ioo hpos.ne]
      exact Ico_subset_Icc_self hs
    exact map_mem_closure hp hs_cl fun t ht => ⟨t, ht, rfl⟩
  have htilde_e₀ : tilde e₀ = {v} := by
    change closure e₀ \ e₀ = {v}
    rw [hcl_e₀]
    ext x
    simp only [e₀, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨hxF, h⟩ => not_not.mp fun hxv => h ⟨hxF, hxv⟩,
      fun hxv => ⟨hxv ▸ hvF, fun ⟨_, hne⟩ => hne hxv⟩⟩
  have hmeet : H.G.U ∩ D.U ⊆ H.G.V ∩ D.V :=
    auxiliary_loop_meets_graph_at_vertices H hvV hU_sub_Bad hF_not_Bad D hDU hDV
  let G' : Drawing S := H.G.glue D hmeet
  have hG'_U : G'.U = H.G.U ∪ F := by
    change H.G.U ∪ D.U = H.G.U ∪ F
    rw [hDU]
  have hG'_V : G'.V = H.G.V := by
    change H.G.V ∪ D.V = H.G.V
    rw [hDV, union_eq_left]
    exact singleton_subset_iff.mpr hvV
  have hG'_E : G'.E = insert e₀ H.G.E := by
    change (H.G.glue D hmeet).E = insert e₀ H.G.E
    rw [Drawing.glue_E, hDE, union_singleton]
  have he₀_notMem : e₀ ∉ H.G.E := by
    intro he₀H
    obtain ⟨x₀, hx₀F, hx₀v⟩ := he₀_ne
    have hx₀U : x₀ ∈ H.G.U := (he₀H.2.1 ⟨hx₀F, hx₀v⟩).1
    exact hF_not_Bad x₀ hx₀F (hU_sub_Bad ⟨hx₀U, hx₀v⟩)
  let H' : SurfaceDigraph S := {
    G := G'
    plus := fun e => if e = e₀ then v else H.plus e
    minus := fun e => if e = e₀ then v else H.minus e
    plus_mem := by
      intro e he
      rw [hG'_V]
      rw [hG'_E] at he
      rcases mem_insert_iff.mp he with rfl | heH
      · simp [hvV]
      · rw [ite_eq_right (ne_of_mem_of_not_mem heH he₀_notMem)]
        exact H.plus_mem e heH
    minus_mem := by
      intro e he
      rw [hG'_V]
      rw [hG'_E] at he
      rcases mem_insert_iff.mp he with rfl | heH
      · simp [hvV]
      · rw [ite_eq_right (ne_of_mem_of_not_mem heH he₀_notMem)]
        exact H.minus_mem e heH
    ends_eq := by
      intro e he
      rw [hG'_E] at he
      rcases mem_insert_iff.mp he with rfl | heH
      · simp [htilde_e₀]
      · have hne : e ≠ e₀ := ne_of_mem_of_not_mem heH he₀_notMem
        rw [ite_eq_right hne, ite_eq_right hne]
        exact H.ends_eq e heH
  }
  refine ⟨H', ?_, hG'_V, ?_, ?_, ?_, ?_⟩
  · change bd S ∩ G'.U ⊆ G'.V
    rw [hG'_U, hG'_V]
    rintro x ⟨hx_bd, hxU | hxF⟩
    · exact hH ⟨hx_bd, hxU⟩
    · exact (hF_not_Bad x hxF (Or.inl (Or.inl hx_bd))).elim
  · change H.G.E ⊆ G'.E
    rw [hG'_E]
    exact subset_insert e₀ H.G.E
  · intro e he
    have hne : e ≠ e₀ := ne_of_mem_of_not_mem he he₀_notMem
    exact ⟨ite_eq_right hne, ite_eq_right hne⟩
  · change G'.E.ncard = H.G.E.ncard + 1
    rw [hG'_E, ncard_insert_of_notMem he₀_notMem H.G.finite_edges]
  · change {w ∈ G'.V \ bd S | IsIsolatedVertex G' w}.ncard + 1 = IsoSet.ncard
    let IsoSet' : Set S := {w ∈ G'.V \ bd S | IsIsolatedVertex G' w}
    have hIso_eq : IsoSet = insert v IsoSet' := by
      ext w
      simp only [IsoSet, IsoSet', mem_sdiff, mem_insert_iff]
      constructor
      · rintro ⟨⟨hwV, hw_bd⟩, hw_iso⟩
        by_cases hwv : w = v
        · exact Or.inl hwv
        · have hwV' : w ∈ G'.V := hG'_V.symm ▸ hwV
          refine Or.inr ⟨⟨hwV', hw_bd⟩, hwV', fun e he hinc => ?_⟩
          rcases hinc with ⟨_, _, hw_cl⟩
          rw [hG'_E] at he
          rcases mem_insert_iff.mp he with rfl | heH
          · rw [hcl_e₀] at hw_cl
            exact hF_not_Bad w hw_cl (Or.inl (Or.inr ⟨hwV, hwv⟩))
          · exact hw_iso.2 e heH ⟨hwV, Or.inl heH, hw_cl⟩
      · rintro (rfl | ⟨⟨hwV', hw_bd⟩, hw_iso'⟩)
        · exact ⟨⟨hvV, hv_not_bd⟩, hiso⟩
        · have hwV : w ∈ H.G.V := hG'_V ▸ hwV'
          refine ⟨⟨hwV, hw_bd⟩, hwV, fun e he hinc => ?_⟩
          rcases hinc with ⟨_, _, hw_cl⟩
          have he' : e ∈ G'.E := by rw [hG'_E]; exact mem_insert_of_mem e₀ he
          exact hw_iso'.2 e he' ⟨hwV', Or.inl he', hw_cl⟩
    have hv_notMem_Iso' : v ∉ IsoSet' := by
      rintro ⟨_, hv_iso'⟩
      have he₀_G' : e₀ ∈ G'.E := by rw [hG'_E]; exact mem_insert e₀ H.G.E
      exact hv_iso'.2 e₀ he₀_G' ⟨hG'_V.symm ▸ hvV, Or.inl he₀_G', by rw [hcl_e₀]; exact hvF⟩
    have hIso'_fin : IsoSet'.Finite := hIso_fin.subset (hIso_eq ▸ subset_insert v IsoSet')
    rw [hIso_eq, ncard_insert_of_notMem hv_notMem_Iso' hIso'_fin]

/-! ## Proof of (9.1) -/

/-- General form of Graph Minors VII, (9.1) (pages 242–243), proved by induction on
`g = numInternalIsolatedVertices H.G` and calling `theorem_7_5_proof` in the base case `g = 0`. -/
theorem theorem_9_1_general
    (g : ℕ) :
    ∀ {S : Type u} [TopologicalSpace S] [T1Space S],
      IsSurface S →
      ∀ a b c : ℕ, 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
      ∀ H : SurfaceDigraph S, H.IsProper →
        numInternalIsolatedVertices H.G = g →
        ∀ k c₀ : ℕ,
          2 * k ≥ 4 * H.G.E.ncard + 4 * g + (H.G.V ∩ bd S).ncard + 2 * c + 2 →
          c₀ ≥ c + H.G.E.ncard + g + 1 →
          ∀ G : SurfaceDigraph S, G.IsProper →
            G.G.V ∩ bd S = H.G.V ∩ bd S →
            IsBoundaryLinked G.G →
            alpha G.G ≥ 42 * k * 5 ^ (g + H.G.E.ncard) * vModel a b c₀ k →
            IsBoundaryRootedMinor H G := by
  induction g with
  | zero =>
    intro S _ _ hS a b c h3 he H hH hg0 k c₀ hk hc₀ G hG hbd_eq hBL halpha
    have hk' : 2 * k ≥ 4 * H.G.E.ncard + (H.G.V ∩ bd S).ncard + 2 * c + 2 := by omega
    have halpha' : alpha G.G ≥ 42 * k * 5 ^ H.G.E.ncard * vModel a b c₀ k := by
      simpa using halpha
    obtain ⟨S_r, tS_r, t1S_r, G_r, H', hS_r, he_r, hBL_r, halpha_r, hbd_card_r, hH'_forest,
        hbd_eq_r, himp⟩ :=
      cutEdgesForestReduction hS a b c h3 he H hH hg0 k c₀ hk' G hbd_eq hBL halpha'
    have h3_r : 3 ≤ 3 * a + 3 * b + (c + H.G.E.ncard) := by omega
    have hv_mono : vModel a b (c + H.G.E.ncard + 1) k ≤ vModel a b c₀ k :=
      vModel_mono_c_le a b (by omega) k
    have halpha_r' : 42 * k * vModel a b (c + H.G.E.ncard + 1) k ≤ alpha G_r := by
      have hmul :
          42 * k * vModel a b (c + H.G.E.ncard + 1) k ≤
            42 * k * vModel a b c₀ k :=
        Nat.mul_le_mul_left (42 * k) hv_mono
      exact le_trans hmul halpha_r
    have hFeas : @IsGFeasible S_r tS_r G_r H' :=
      @theorem_7_5_proof S_r tS_r t1S_r hS_r a b (c + H.G.E.ncard) h3_r he_r k G_r H' hBL_r
        halpha_r' hbd_card_r hH'_forest hbd_eq_r
    exact himp hFeas
  | succ g ih =>
    intro S _ _ hS a b c h3 he H hH hg_succ k c₀ hk hc₀ G hG hbd_eq hBL halpha
    have hg_pos : 0 < numInternalIsolatedVertices H.G := by omega
    obtain ⟨H₁, hH₁_prop, hV₁, hE₁, hends₁, hE_card₁, hg_card₁⟩ :=
      addLoop_to_isolatedVertex hS H hH hg_pos
    have hg₁ : numInternalIsolatedVertices H₁.G = g := by omega
    have hk₁ : 2 * k ≥ 4 * H₁.G.E.ncard + 4 * g + (H₁.G.V ∩ bd S).ncard + 2 * c + 2 := by
      rw [hV₁, hE_card₁]
      omega
    have hc₀₁ : c₀ ≥ c + H₁.G.E.ncard + g + 1 := by
      rw [hE_card₁]
      omega
    have hbd_eq₁ : G.G.V ∩ bd S = H₁.G.V ∩ bd S := by
      rw [hV₁, hbd_eq]
    have hsum_eq : g + H₁.G.E.ncard = (g + 1) + H.G.E.ncard := by omega
    have halpha₁ : alpha G.G ≥ 42 * k * 5 ^ (g + H₁.G.E.ncard) * vModel a b c₀ k := by
      rw [hsum_eq]
      exact halpha
    have hMinor₁ : IsBoundaryRootedMinor H₁ G :=
      ih hS a b c h3 he H₁ hH₁_prop hg₁ k c₀ hk₁ hc₀₁ G hG hbd_eq₁ hBL halpha₁
    exact isBoundaryRootedMinor_of_edge_subdigraph hV₁ hE₁ hends₁ hMinor₁

/-- Graph Minors VII, (9.1) (pages 242–243):
"(9.1) *Let $\Sigma \cong \Sigma(a, b, c)$ where $3a + 3b + c \ge 3$. Let $(H, H^+, H^-)$ be a
proper digraph in $\Sigma$. Let $g$ be the number of isolated vertices of $H$ which are not in
$bd(\Sigma)$. Let $k$ be an integer with*
$$2k \ge 4|E(H)| + 4g + |V(H) \cap bd(\Sigma)| + 2c + 2$$
*and let $c_0$ be an integer with $c_0 \ge c + |E(H)| + g + 1$. Let $(G, G^+, G^-)$ be a proper
digraph in $\Sigma$ such that* ...
(i) $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$,
(ii) $G$ *is boundary-linked, and*
(iii) $\alpha(G) \ge 42k 5^{(g+|E(H)|)} v(\Sigma(a, b, c_0), k)$.
*Then $(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_1_proof
    [T1Space S] (hS : IsSurface S) (a b c : ℕ) (h3 : 3 * a + 3 * b + c ≥ 3)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (H : SurfaceDigraph S) (hH : H.IsProper)
    (k c₀ : ℕ)
    (hk : 2 * k ≥ 4 * H.G.E.ncard + 4 * numInternalIsolatedVertices H.G +
      (H.G.V ∩ bd S).ncard + 2 * c + 2)
    (hc₀ : c₀ ≥ c + H.G.E.ncard + numInternalIsolatedVertices H.G + 1)
    (G : SurfaceDigraph S) (hG : G.IsProper)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    (hBL : IsBoundaryLinked G.G)
    (halpha : alpha G.G ≥
      42 * k * 5 ^ (numInternalIsolatedVertices H.G + H.G.E.ncard) * vModel a b c₀ k) :
    IsBoundaryRootedMinor H G :=
  theorem_9_1_general (numInternalIsolatedVertices H.G) hS a b c h3 he H hH rfl k c₀
    hk hc₀ G hG hbd_eq hBL halpha

/-- Graph Minors VII, (9.1) for the interface `GM07Theorem91Statement`. -/
theorem gm07_theorem_9_1
    :
    GM07Theorem91Statement.{u} := by
  intro S _ _ hS a b c h3 he H hH k c₀ _ hk hc₀ G hG hbd_eq hBL halpha
  exact theorem_9_1_proof hS a b c h3 he H hH k c₀ hk hc₀ G hG hbd_eq hBL halpha

/-! ## Proof of (9.2) from (9.1) -/

/-- On a surface with empty boundary `bd S = ∅`, every drawing `G` is proper. -/
theorem isProper_of_bd_eq_empty (hbd : bd S = ∅) (G : Drawing S) :
    G.IsProper := by
  change bd S ∩ G.U ⊆ G.V
  rw [hbd, empty_inter]
  exact empty_subset G.V

/-- On a surface with `cuffs S = ∅` and `bd S = ∅`, every drawing `G` is boundary-linked. -/
theorem isBoundaryLinked_of_bd_eq_empty (hcuffs : cuffs S = ∅) (hbd : bd S = ∅)
    (G : Drawing S) :
    IsBoundaryLinked G := by
  refine ⟨isProper_of_bd_eq_empty hbd G, ?_⟩
  intro C hC
  rw [hcuffs] at hC
  exact False.elim hC

/-- Graph Minors VII, (9.2) (page 244):
"(9.2) *Let $\Sigma \cong \Sigma(a, b, 0)$ where $a + b \ge 1$, and let $(H, H^+, H^-)$ be a digraph
in $\Sigma$. Then there is a number $N$ such that $(H, H^+, H^-)$ is a minor of every digraph
$(G, G^+, G^-)$ in $\Sigma$ with $\alpha(G) \ge N$.*"
Proved directly from `theorem_9_1_proof` by setting `k = 2 * |E(H)| + 2 * g + 1`,
`c₀ = |E(H)| + g + 1`, and `N = 42 * k * 5 ^ (g + |E(H)|) * vModel a b c₀ k`. -/
theorem theorem_9_2_proof
    [T1Space S] (hS : IsSurface S) (a b : ℕ) (hab : a + b ≥ 1)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (H : SurfaceDigraph S) :
    ∃ N : ℕ, ∀ G : SurfaceDigraph S, alpha G.G ≥ N → IsDigraphMinor H G := by
  obtain ⟨hcuffs, hbd⟩ := bd_eq_empty_of_homeomorph_surfaceModel_zero he
  let g := numInternalIsolatedVertices H.G
  let k := 2 * H.G.E.ncard + 2 * g + 1
  let c₀ := H.G.E.ncard + g + 1
  use 42 * k * 5 ^ (g + H.G.E.ncard) * vModel a b c₀ k
  intro G halpha
  refine ⟨hbd, ?_⟩
  have h3 : 3 * a + 3 * b + 0 ≥ 3 := by omega
  have hH_prop : H.IsProper := isProper_of_bd_eq_empty hbd H.G
  have hG_prop : G.IsProper := isProper_of_bd_eq_empty hbd G.G
  have hBL : IsBoundaryLinked G.G := isBoundaryLinked_of_bd_eq_empty hcuffs hbd G.G
  have hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S := by rw [hbd, inter_empty, inter_empty]
  have hbd_card : (H.G.V ∩ bd S).ncard = 0 := by rw [hbd, inter_empty, ncard_empty]
  have hk : 2 * k ≥ 4 * H.G.E.ncard + 4 * g + (H.G.V ∩ bd S).ncard + 2 * 0 + 2 := by
    rw [hbd_card]
    dsimp [k]
    omega
  have hc₀ : c₀ ≥ 0 + H.G.E.ncard + g + 1 := by
    dsimp [c₀]
    omega
  exact theorem_9_1_proof hS a b 0 h3 he H hH_prop k c₀ hk hc₀ G hG_prop hbd_eq hBL halpha

/-- Graph Minors VII, (9.2) for `GM07Theorem92Statement`, proved directly from
`theorem_9_2_proof`. -/
theorem gm07_theorem_9_2
    :
    GM07Theorem92Statement.{u} := by
  intro S _ _ hS a b hab he H
  exact theorem_9_2_proof hS a b hab he H

end GraphMinor.GM07
