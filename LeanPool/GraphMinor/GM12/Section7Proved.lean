/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section78
import LeanPool.GraphMinor.GM12.Section75Proof
import LeanPool.GraphMinor.GM11.Section64
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Graph Minors XII, (7.6) and (7.8)

Use the proved (7.5) in the induction deleting vertices near a region, then apply
that induction to the edge deletion in (7.8). The preliminary metric lemmas remain
in Sections 76 and 78, since the proof of (7.5) uses them too.
-/

public section

namespace GraphMinor.GM12

open Set Function Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
private theorem isPreconnected_of_isLine {F : Set S} (hF : IsLine F) : IsPreconnected F := by
  obtain ⟨e⟩ := hF
  have heq : F = range fun t : unitInterval => (e t).1 := by
    ext x
    exact ⟨fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨t, rfl⟩; exact (e t).2⟩
  rw [heq]
  exact isPreconnected_range (continuous_subtype_val.comp e.continuous)

omit [T2Space S] in
private theorem frontier_region_subset_U [LocallyConnectedSpace S]
    {Γ : Drawing S} {r : Set S} (hr : r ∈ Γ.R) : frontier r ⊆ Γ.U := by
  intro x hx
  by_contra hxU
  have hx_compl : x ∈ univ \ Γ.U := ⟨mem_univ x, hxU⟩
  have hopen : IsOpen (connectedComponentIn (univ \ Γ.U) x) :=
    IsOpen.connectedComponentIn (isOpen_univ.sdiff Γ.isClosed_U)
  obtain ⟨y, hy_cc, hy_r⟩ :=
    mem_closure_iff.mp hx.1 (connectedComponentIn (univ \ Γ.U) x) hopen
      (mem_connectedComponentIn hx_compl)
  have hcc_R : connectedComponentIn (univ \ Γ.U) x ∈ Γ.R :=
    (mem_R_iff Γ).mpr ⟨x, hxU, rfl⟩
  have heq : connectedComponentIn (univ \ Γ.U) x = r :=
    atom_eq_of_inter_nonempty (Or.inr hcc_R) (Or.inr hr) ⟨y, hy_cc, hy_r⟩
  have hxr : x ∈ r := heq ▸ mem_connectedComponentIn hx_compl
  exact hx.2 ((region_isOpen hr).interior_eq.symm ▸ hxr)

/-- **(7.6)** of Graph Minors XII (page 266):
"(7.6) *Let $k \ge 0$ be an integer, and let $\mathscr{T}$ be a respectful tangle of order
$\theta \ge 2k + 1$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$. Let its metric be
$d$. Let $r$ be a region of $\Gamma$, and let $Z$ be the set of all vertices $v$ of $\Gamma$ such
that there is a $\Gamma$-normal line $F$ with $v \in F$, $F \cap r \ne \emptyset$ and
$|F \cap V(\Gamma)| \le k$. Then there is a 2-cell subdrawing $\Gamma'$ of $\Gamma \setminus Z$, and
a respectful tangle $\mathscr{T}'$ of order $\theta - 2k$ in $\Gamma'$, with metric $d'$, such that
if $r'$ is the region of $\Gamma'$ with $r \subseteq r'$, then*
$$
\begin{aligned}
\text{(i)} \quad & U(\Gamma) \subseteq U(\Gamma') \cup r' \\
\text{(ii)} \quad & d'(a, b) \ge d(a, b) - 4k \text{ for all } a, b \in A(\Gamma) \cap A(\Gamma') \\
\text{(iii)} \quad & d'(a, r') \ge d(a, r) - 2k \text{ for all } a \in A(\Gamma) \cap A(\Gamma'),
\text{ and} \\
\text{(iv)} \quad & d(a, r) \le 2k + 1 \text{ for all } a \in A(\Gamma) \text{ with } a \subseteq
r'.
\end{aligned}
$$
*In particular, if $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and
$b \subseteq b'$, then $d'(a', b') \ge d(a, b) - 4k - 2$.*" -/
theorem theorem_7_6_proof
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {θ : ℕ} (k : ℕ)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Set S}
    (hθ : 2 * k + 1 ≤ θ)
    (hd : HasTangleMetric Γ θ T d)
    (hr : r ∈ Γ.R) :
    ∃ (Γ' : Drawing S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r' : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ (regionLineVertices Γ r k)) ∧
      (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
      HasTangleMetric Γ' (θ - 2 * k) T' d' ∧
      r' ∈ Γ'.R ∧ r ⊆ r' ∧
      Γ.U ⊆ Γ'.U ∪ r' ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 * k ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 * k ≤ d' a r') ∧
      (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 2 * k + 1) ∧
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d' a' b') := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction k generalizing Γ θ T d r with
  | zero =>
    have hZ_empty : regionLineVertices Γ r 0 = ∅ := by
      ext v
      simp only [regionLineVertices, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and,
        not_exists]
      intro hv F _ _ hvF _ hcard0
      have hpos : 0 < (F ∩ Γ.V).ncard :=
        (ncard_pos (Γ.finite_V.subset inter_subset_right)).mpr ⟨v, hvF, hv⟩
      omega
    have hSub0 : Γ.IsSubdrawing (deleteVertices Γ (regionLineVertices Γ r 0)) := by
      rw [hZ_empty, isSubdrawing_deleteVertices_iff]
      exact ⟨Drawing.IsSubdrawing.refl Γ, disjoint_empty _⟩
    have h_i : Γ.U ⊆ Γ.U ∪ r := subset_union_left
    have h_ii : ∀ a ∈ Γ.A ∩ Γ.A, ∀ b ∈ Γ.A ∩ Γ.A, d a b - 4 * 0 ≤ d a b :=
      fun _ _ _ _ => Nat.sub_le _ _
    have h_iii : ∀ a ∈ Γ.A ∩ Γ.A, d a r - 2 * 0 ≤ d a r :=
      fun _ _ => Nat.sub_le _ _
    have h_iv : ∀ a ∈ Γ.A, a ⊆ r → d a r ≤ 2 * 0 + 1 := by
      intro a ha har
      obtain ⟨x, hxa⟩ := atom_nonempty' ha
      have heq : a = r := atom_eq_of_inter_nonempty ha (Or.inr hr) ⟨x, hxa, har hxa⟩
      subst heq
      rw [metric_self hd (Or.inr hr)]
      omega
    refine ⟨Γ, T, d, r, hSub0, hd.1.1, by simpa using hd, hr, Subset.rfl, h_i, h_ii, h_iii, h_iv,
      fun a ha b hb a' ha' b' hb' haa' hbb' =>
        theorem_7_6_in_particular hS hd (by simpa using hd) (Drawing.IsSubdrawing.refl Γ) hr hr
          h_i h_ii h_iii h_iv ha hb ha' hb' haa' hbb'⟩
  | succ k ih =>
    have hθ3 : 3 ≤ θ := by omega
    obtain ⟨Γ'', T'', d'', r'', hSub'', h2cell'', hd'', hr'', hr_sub'',
      hU'', hd''_ab, hd''_ar, hd_le3⟩ := theorem_7_5_proof S hS Γ θ T d r hθ3 hd hr
    obtain ⟨hSubΓ'', hDisjY⟩ := isSubdrawing_deleteVertices_iff.mp hSub''
    have hθ'' : 2 * k + 1 ≤ θ - 2 := by omega
    obtain ⟨Γ', T', d', r', hSub', h2cell', hd', hr', hr''_sub',
      hU', hd'_ab, hd'_ar'', hd''_le, _⟩ := ih hθ'' hd'' hr''
    obtain ⟨hSubΓ'Γ'', hDisjZ''⟩ := isSubdrawing_deleteVertices_iff.mp hSub'
    have hSubΓ'Γ : Γ'.IsSubdrawing Γ := hSubΓ'Γ''.trans hSubΓ''
    -- Any vertex in `regionLineVertices Γ r (k + 1) ∩ Γ''.V` belongs to `regionLineVertices Γ'' r''
    -- k`.
    have hZ_sub_Z'' : regionLineVertices Γ r (k + 1) ∩ Γ''.V ⊆ regionLineVertices Γ'' r'' k := by
      intro v hv
      rcases hv with ⟨⟨hvΓ, F, hF_line, hF_norm, hvF, ⟨p, hpF, hpr⟩, hF_card⟩, hvΓ''⟩
      have hv_not_cl : v ∉ closure r := fun hv_cl =>
        disjoint_left.mp hDisjY hvΓ'' ⟨hvΓ, hv_cl⟩
      have hF_pre : IsPreconnected F := isPreconnected_of_isLine hF_line
      have hF_fr : (F ∩ frontier r).Nonempty := by
        by_contra h_emp
        have hdis : Disjoint F (frontier (closure r)) := by
          refine Disjoint.mono_right frontier_closure_subset ?_
          exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h_emp)
        exact hv_not_cl
          (subset_of_disjoint_frontier hF_pre isClosed_closure hdis hpF (subset_closure hpr) hvF)
      obtain ⟨w, hwF, hw_fr⟩ := hF_fr
      have hwU : w ∈ Γ.U := frontier_region_subset_U hr hw_fr
      have hwV : w ∈ Γ.V := hF_norm ⟨hwF, hwU⟩
      have hw_cl : w ∈ closure r := hw_fr.1
      have hw_not_Γ'' : w ∉ Γ''.V := fun hw'' =>
        disjoint_left.mp hDisjY hw'' ⟨hwV, hw_cl⟩
      have hw_not_inter : w ∉ F ∩ Γ''.V := fun h => hw_not_Γ'' h.2
      have hins_sub : insert w (F ∩ Γ''.V) ⊆ F ∩ Γ.V := by
        rintro x (rfl | ⟨hxF, hxV''⟩)
        · exact ⟨hwF, hwV⟩
        · exact ⟨hxF, hSubΓ''.1 hxV''⟩
      have hcard_ins : (insert w (F ∩ Γ''.V)).ncard ≤ k + 1 :=
        (ncard_le_ncard hins_sub (Γ.finite_V.subset inter_subset_right)).trans hF_card
      rw [ncard_insert_of_notMem hw_not_inter (Γ''.finite_V.subset inter_subset_right)] at hcard_ins
      refine ⟨hvΓ'', F, hF_line, isNormal_of_isSubdrawing hSubΓ'' hF_norm, hvF,
        ⟨p, hpF, hr_sub'' hpr⟩, by omega⟩
    have hSub_del : Γ'.IsSubdrawing (deleteVertices Γ (regionLineVertices Γ r (k + 1))) := by
      rw [isSubdrawing_deleteVertices_iff]
      refine ⟨hSubΓ'Γ, disjoint_left.mpr fun v hvΓ' hvZ => ?_⟩
      exact disjoint_left.mp hDisjZ'' hvΓ' (hZ_sub_Z'' ⟨hvZ, hSubΓ'Γ''.1 hvΓ'⟩)
    have hr_sub' : r ⊆ r' := hr_sub''.trans hr''_sub'
    have h_i : Γ.U ⊆ Γ'.U ∪ r' := by
      intro x hx
      rcases hU'' hx with hxU'' | hxr''
      · exact hU' hxU''
      · exact Or.inr (hr''_sub' hxr'')
    have hA_sub'' : Γ.A ∩ Γ'.A ⊆ Γ''.A := by
      rintro a ⟨haΓ, haΓ'⟩
      obtain ⟨x, hxa⟩ := atom_nonempty' haΓ
      obtain ⟨a'', ha'', haa''⟩ := exists_atom_superset_of_isSubdrawing hSubΓ'' haΓ
      obtain ⟨a₁', ha₁', ha''a₁'⟩ := exists_atom_superset_of_isSubdrawing hSubΓ'Γ'' ha''
      have heq : a₁' = a :=
        atom_eq_of_inter_nonempty ha₁' haΓ' ⟨x, ha''a₁' (haa'' hxa), hxa⟩
      have ha_eq : a = a'' := Subset.antisymm haa'' (heq ▸ ha''a₁')
      exact ha_eq ▸ ha''
    have h_ii : ∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 * (k + 1) ≤ d' a b := by
      intro a ha b hb
      have ha'' : a ∈ Γ''.A := hA_sub'' ha
      have hb'' : b ∈ Γ''.A := hA_sub'' hb
      have h1 := hd''_ab a ⟨ha.1, ha''⟩ b ⟨hb.1, hb''⟩
      have h2 := hd'_ab a ⟨ha'', ha.2⟩ b ⟨hb'', hb.2⟩
      omega
    have h_iii : ∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 * (k + 1) ≤ d' a r' := by
      intro a ha
      have ha'' : a ∈ Γ''.A := hA_sub'' ha
      have h1 := hd''_ar a ⟨ha.1, ha''⟩
      have h2 := hd'_ar'' a ⟨ha'', ha.2⟩
      omega
    have h_iv : ∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 2 * (k + 1) + 1 := by
      intro a ha har'
      obtain ⟨a'', ha'', haa''⟩ := exists_atom_superset_of_isSubdrawing hSubΓ'' ha
      rcases atom_eq_or_eq_region_of_U_subset hSubΓ'' hr'' hU'' ha ha'' haa'' with
        ⟨rfl, ha_mem''⟩ | ⟨rfl, har''⟩
      · have h1 := hd''_ar a ha_mem''
        have h2 := hd''_le a ha_mem''.2 har'
        omega
      · have h1 := hd_le3 a ha har''
        omega
    have hd'_eq : HasTangleMetric Γ' (θ - 2 * (k + 1)) T' d' := by
      have h_ord_eq : θ - 2 - 2 * k = θ - 2 * (k + 1) := by omega
      rwa [h_ord_eq] at hd'
    refine ⟨Γ', T', d', r', hSub_del, h2cell', hd'_eq, hr', hr_sub', h_i, h_ii, h_iii, h_iv,
      fun a ha b hb a' ha' b' hb' haa' hbb' =>
        theorem_7_6_in_particular hS hd hd'_eq hSubΓ'Γ hr hr'
          h_i h_ii h_iii h_iv ha hb ha' hb' haa' hbb'⟩


/-! ## 2. Proof of (7.8) -/

private theorem deleted_encircling_region_le_target_drawing
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    {Γ : Drawing S}
    {Γ' : Drawing S}
    {θ : ℕ}
    {k : ℕ}
    (hθ : 2 * k + 2 ≤ θ)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {c : Set S}
    (hc : c ∈ Γ.A)
    (hSub : Γ'.IsSubdrawing Γ)
    (hdist : ∀ e ∈ Γ.E \ Γ'.E, d c e ≤ k)
    (hck : c ∈ Γ.E \ Γ'.E → 2 ≤ k)
    (hResp : IsRespectfulDrawingTangle Γ θ T)
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hds : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hd_eq : ∀ x ∈ Γ.A, ∀ y ∈ Γ.A, d x y = tangleMetric Γ K ins θ x y)
    (hUU : Γ.U ∩ K.U = Γ.V)
    (hsl : IsSlope K (2 * θ) ins)
    (hE_ne : Γ.E.Nonempty)
    (h : Set S)
    (hh : IsCorrespondingAtom Γ K c h)
    (u_init : S)
    (W_init : GraphWalk K.toGraph u_init u_init)
    (u₀ : S)
    (W₀ : GraphWalk K.toGraph u₀ u₀)
    (hW₀_len : W₀.length ≤ 2 * k)
    (hh_W₀ : h ⊆ insWalk ins K W₀)
    (hW₀_max : ∀ ⦃y : Set S⦄,
      (∃ (u : S) (W : GraphWalk K.toGraph u u), W.length ≤ 2 * k ∧ h ⊆ insWalk ins K W ∧
        insWalk ins K W_init ⊆ y ∧ y = insWalk ins K W) →
      insWalk ins K W₀ ⊆ y → y ⊆ insWalk ins K W₀)
    (hinit_W₀ : insWalk ins K W_init ⊆ insWalk ins K W₀)
    (v₀ : S)
    (hv₀_W₀ : v₀ ∈ (walkDrawing K W₀).V)
    (hv₀_not_Γ : v₀ ∉ Γ.V)
    (r : Set S)
    (hr : r ∈ Γ.R)
    (hv₀_r : v₀ ∈ r)
    (hr_corr : IsCorrespondingAtom Γ K r {v₀})
    (Γ'' : Drawing S)
    (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d'' : Set S → Set S → ℕ)
    (r'' : Set S)
    (h2cell'' : (PaintingOrDrawing.drawing Γ'').IsTwoCell)
    (hd'' : HasTangleMetric Γ'' (θ - 2 * k) T'' d'')
    (hU'' : Γ.U ⊆ Γ''.U ∪ r'')
    (h_iv'' : ∀ a ∈ Γ.A, a ⊆ r'' → d a r ≤ 2 * k + 1)
    (hSubΓ'' : Γ''.IsSubdrawing Γ)
    (hDisjZ : Disjoint Γ''.V (regionLineVertices Γ r k)) :
    Γ''.IsSubdrawing Γ' := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let 𝒜 : Set (Set S) := {X | ∃ (u : S) (W : GraphWalk K.toGraph u u),
    W.length ≤ 2 * k ∧ h ⊆ insWalk ins K W ∧ insWalk ins K W_init ⊆ X ∧ X = insWalk ins K W}
  have hE_sub : Γ''.E ⊆ Γ'.E := by
    intro e he''
    by_contra he_not_Γ'
    have he_Γ : e ∈ Γ.E := hSubΓ''.2 he''
    obtain ⟨u₁, W₁, hW₁_len, hh_W₁, he_W₁⟩ :=
      exists_walk_of_edge_dist_le hS hResp hE_ne hK hds hd_eq hc hh he_Γ (by omega)
        (hdist e ⟨he_Γ, he_not_Γ'⟩) (fun hce => hck (hce ▸ ⟨he_Γ, he_not_Γ'⟩))
    -- Combine `W₀` and `W₁` into a single closed walk `W` of length `≤ 4 * k` with `v₀ ∈ V(W)`
    -- and `e ⊆ insWalk ins K W`.
    have hex_W : ∃ (u : S) (W : GraphWalk K.toGraph u u),
        W.length ≤ 4 * k ∧ v₀ ∈ (walkDrawing K W).V ∧ e ⊆ insWalk ins K W := by
      by_cases hsub₁₀ : insWalk ins K W₁ ⊆ insWalk ins K W₀
      · exact ⟨u₀, W₀, by omega, hv₀_W₀, he_W₁.trans hsub₁₀⟩
      · have hW₀_lt : W₀.length < 2 * θ := by omega
        have hW₁_lt : W₁.length < 2 * θ := by omega
        have hr₀ : IsRestraint K ins (2 * θ) (insWalk ins K W₀) :=
          (GM11.theorem_8_5_proof hS hsl W₀ hW₀_lt).1
        have hr₁ : IsRestraint K ins (2 * θ) (insWalk ins K W₁) :=
          (GM11.theorem_8_5_proof hS hsl W₁ hW₁_lt).1
        have hpre₀ : IsPreconnected (subBd (insWalk ins K W₀)) :=
          isPreconnected_subBd_of_isRestraint hS hr₀
        have hpre₁ : IsPreconnected (subBd (insWalk ins K W₁)) :=
          isPreconnected_subBd_of_isRestraint hS hr₁
        obtain ⟨xh, hxh⟩ := atom_nonempty hh.2.1
        have hmeet : (insWalk ins K W₀ ∩ insWalk ins K W₁).Nonempty :=
          ⟨xh, hh_W₀ hxh, hh_W₁ hxh⟩
        have hneq : insWalk ins K W₀ ∪ insWalk ins K W₁ ≠ univ := by
          have h84 := GM11.theorem_8_4_proof hS hsl hr₀ hr₁ hr₁
          rwa [Set.union_assoc, Set.union_self] at h84
        have hnot_sub₀₁ : ¬ insWalk ins K W₀ ⊆ insWalk ins K W₁ := by
          intro hsub₀₁
          have hmem₁ : insWalk ins K W₁ ∈ 𝒜 :=
            ⟨u₁, W₁, hW₁_len, hh_W₁, hinit_W₀.trans hsub₀₁, rfl⟩
          exact hsub₁₀ (hW₀_max hmem₁ hsub₀₁)
        have hbd_meet : ¬ Disjoint (subBd (insWalk ins K W₀)) (subBd (insWalk ins K W₁)) := by
          intro hdisj
          rcases GM11.theorem_7_7_proof hpre₀ hpre₁ hmeet hneq hdisj with h₀₁ | h₁₀
          · exact hnot_sub₀₁ h₀₁
          · exact hsub₁₀ h₁₀
        rw [not_disjoint_iff_nonempty_inter] at hbd_meet
        have hfr₀ : subBd (insWalk ins K W₀) ⊆ (walkDrawing K W₀).U := by
          rw [subBd_eq_frontier]
          exact (frontier_insOf_subset hsl (walkDrawing_isSubdrawing K W₀)
            (isConfined_walk W₀ hW₀_lt)).2
        have hfr₁ : subBd (insWalk ins K W₁) ⊆ (walkDrawing K W₁).U := by
          rw [subBd_eq_frontier]
          exact (frontier_insOf_subset hsl (walkDrawing_isSubdrawing K W₁)
            (isConfined_walk W₁ hW₁_lt)).2
        have hU_meet : ((walkDrawing K W₀).U ∩ (walkDrawing K W₁).U).Nonempty :=
          hbd_meet.mono (inter_subset_inter hfr₀ hfr₁)
        obtain ⟨w, hw₀, hw₁⟩ :=
          subdrawings_common_vertex (walkDrawing_isSubdrawing K W₀)
            (walkDrawing_isSubdrawing K W₁) hU_meet
        rw [walkDrawing_V] at hw₀ hw₁
        obtain ⟨V₁, hV₁_len, hV₁_draw⟩ := rotate_closed_walk W₁ hw₁
        obtain ⟨W, hW_len, hW₀_sub, hV₁_sub⟩ := splice_closed_walks W₀ V₁ hw₀
        have hW₁_sub : (walkDrawing K W₁).IsSubdrawing (walkDrawing K W) :=
          hV₁_draw ▸ hV₁_sub
        refine ⟨u₀, W, by omega, hW₀_sub.1 hv₀_W₀, he_W₁.trans (insOf_mono hW₁_sub)⟩
    obtain ⟨u, W, hW_len, hv₀_W, he_W⟩ := hex_W
    have hW_lt : W.length < 2 * θ := by omega
    obtain ⟨hclW, hfrW⟩ :=
      frontier_insOf_subset hsl (walkDrawing_isSubdrawing K W) (isConfined_walk W hW_lt)
    change IsClosed (insWalk ins K W) at hclW
    change frontier (insWalk ins K W) ⊆ (walkDrawing K W).U at hfrW
    -- Every vertex in `(walkDrawing K W).V ∩ Γ.V` belongs to `regionLineVertices Γ r k`,
    -- so `Γ''.U` is disjoint from `frontier (insWalk ins K W)`.
    have hdisj_fr : Disjoint Γ''.U (frontier (insWalk ins K W)) := by
      refine disjoint_left.mpr fun x hxU'' hxfr => ?_
      have hxW_U : x ∈ (walkDrawing K W).U := hfrW hxfr
      have hx_ΓV : x ∈ Γ.V := hUU ▸
        ⟨hSubΓ''.U_subset hxU'', (walkDrawing_isSubdrawing K W).U_subset hxW_U⟩
      have hx_V'' : x ∈ Γ''.V := subdrawing_vertex_of_mem_U hSubΓ'' hxU'' hx_ΓV
      have hx_WV : x ∈ (walkDrawing K W).V :=
        subdrawing_vertex_of_mem_U (walkDrawing_isSubdrawing K W) hxW_U (hK.2.1.2.1 hx_ΓV)
      have hx_Z : x ∈ regionLineVertices Γ r k :=
        mem_regionLineVertices_of_closed_walk hK.2.1 hv₀_r hv₀_not_Γ W hW_len hv₀_W hx_WV hx_ΓV
      exact disjoint_left.mp hDisjZ hx_V'' hx_Z
    obtain ⟨p_e, hp_e⟩ := he''.1
    have hU''_sub : Γ''.U ⊆ insWalk ins K W :=
      subset_of_disjoint_frontier (isPreconnected_U_of_isTwoCell hS h2cell'') hclW hdisj_fr
        ((he''.2.1 hp_e).1) (he_W hp_e)
    -- By (1.2), there is an edge `f ∈ Γ.E` with `d r f = θ`.
    have hr_not_E : r ∉ Γ.E := fun hrE => by
      obtain ⟨x, hxr⟩ := region_nonempty hr
      exact region_subset hr hxr ((hrE.2.1 hxr).1)
    obtain ⟨f, hf_Γ, hd_rf⟩ :=
      exists_edge_dist_eq_theta_uncond hS ⟨hResp, K, ins, hK, hds, hd_eq⟩
        (by omega) (Or.inr hr) (Or.inr hr_not_E)
    -- Show `f ∈ Γ''.E` using (iv) of (7.6).
    have hf_Γ'' : f ∈ Γ''.E := by
      by_contra hf_not_Γ''
      have hf_sub_r'' : f ⊆ r'' := by
        intro x hxf
        rcases hU'' ((hf_Γ.2.1 hxf).1) with hxU'' | hxr''
        · exfalso
          have hx_not_V'' : x ∉ Γ''.V := fun hxV'' => (hf_Γ.2.1 hxf).2 (hSubΓ''.1 hxV'')
          obtain ⟨g, hg'', hxg⟩ := Γ''.exists_edge_of_mem hxU'' hx_not_V''
          have hfg : f = g := Γ.edge_eq_of_mem hf_Γ (hSubΓ''.2 hg'') hxf hxg
          exact hf_not_Γ'' (hfg ▸ hg'')
        · exact hxr''
      have hd_fr_le : d f r ≤ 2 * k + 1 := h_iv'' f (Or.inl (Or.inr hf_Γ)) hf_sub_r''
      obtain ⟨_, _, _, hsym, _, _, _⟩ :=
        GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance ⟨hResp, K, ins, hK, hds, hd_eq⟩
      have hd_rf_le : d r f ≤ 2 * k + 1 :=
        (hsym r (Or.inr hr) f (Or.inl (Or.inr hf_Γ))).trans_le hd_fr_le
      omega
    have hf_sub_W : f ⊆ insWalk ins K W :=
      fun x hx => hU''_sub (hf_Γ''.2.1 hx).1
    obtain ⟨r_f, hr_f, -⟩ := existsUnique_correspondingAtom hK (Or.inl (Or.inr hf_Γ))
    have hr_f_R : r_f ∈ K.R := by
      rcases hr_f.2.2 with ⟨v, hv, rfl, -⟩ | ⟨_, hr_f_R, _⟩ | ⟨hr_f_Γ, -⟩
      · exact absurd hv (hf_Γ.2.1 (mem_singleton v)).2
      · exact hr_f_R
      · obtain ⟨x, hxf⟩ := hf_Γ.1
        exact absurd (hf_Γ.2.1 hxf).1 (region_subset hr_f_Γ hxf)
    have hf_sub_rf : f ⊆ r_f := by
      rcases hr_f.2.2 with ⟨v, hv, rfl, -⟩ | ⟨_, _, hsub⟩ | ⟨hr_f_Γ, -⟩
      · exact absurd hv (hf_Γ.2.1 (mem_singleton v)).2
      · exact hsub
      · obtain ⟨x, hxf⟩ := hf_Γ.1
        exact absurd (hf_Γ.2.1 hxf).1 (region_subset hr_f_Γ hxf)
    obtain ⟨pf, hpf⟩ := hf_Γ.1
    have hrf_W : r_f ⊆ insWalk ins K W :=
      nice_region (GM11.theorem_8_5_proof hS hsl W hW_lt).1.isGammaNice hr_f_R
        ⟨pf, hf_sub_rf hpf, hf_sub_W hpf⟩
    have hv₀_in_W : ({v₀} : Set S) ⊆ insWalk ins K W :=
      singleton_subset_iff.mpr (Or.inl ((walkDrawing K W).V_subset_U hv₀_W))
    obtain ⟨m, hm⟩ : ∃ m, W.length = 2 * m := ⟨_, closed_walk_length_eq_two_mul hK.2.1 W⟩
    have hd_rf_le : d r f ≤ m := by
      rw [hd_eq r (Or.inr hr) f (Or.inl (Or.inr hf_Γ))]
      exact tangleMetric_le_of_walk hr_corr hr_f W hW_lt hm hv₀_in_W hrf_W
    omega
  -- Deduce `Γ''.V ⊆ Γ'.V` since `Γ''` has no isolated vertices.
  refine ⟨fun v hv'' => ?_, hE_sub⟩
  have hE''_ne : Γ''.E.Nonempty :=
    edgeSet_nonempty_of_isTangle_of_two_le hd''.1.2.1 (by omega)
  obtain ⟨K'', hK''⟩ := GM11.exists_radialDrawing hS h2cell''
  have hrf'' := GM11.regionFacts_of_radial ⟨hK''.1, hK''.2.1⟩ hS hK''.2.2 hE''_ne
  obtain ⟨e, he'', hve⟩ := exists_edge_of_regionFacts hS hrf'' hv''
  have he' : e ∈ Γ'.E := hE_sub he''
  have hv_in : v ∈ closure e ∩ Γ'.V := by
    rw [hSub.closure_inter_V he', ← hSubΓ''.closure_inter_V he'']
    exact ⟨hve, hv''⟩
  exact hv_in.2

/-- **(7.8)** of Graph Minors XII (page 268):
"Let $k \ge 0$ be an integer, and let $\mathscr{T}$ be a respectful tangle of order $\theta
\ge 2k + 2$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$. Let its metric be
$d$. Let $c \in A(\Gamma)$, and let $\Gamma'$ be a 2-cell subdrawing of $\Gamma$ such that
$d(c, e) \le k$ for all $e \in E(\Gamma) - E(\Gamma')$, and such that if $c \in E(\Gamma')$
then $k \ge 2$. Then there is a respectful tangle $\mathscr{T}'$ of order $\theta - 2k$ in
$\Gamma'$, with metric $d'$, such that $d'(a', b') \ge d(a, b) - 4k - 2$ for all $a, b \in
A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b \subseteq b'$."

The printed statement of (7.8) requires `k ≥ 2` if `c ∈ Γ'.E`. The corrected hypothesis is
`c ∈ Γ.E \ Γ'.E → 2 ≤ k`, as in (7.10) on page 270. On page 269 the printed proof uses the
bound when the radial atom of the center is a region, and again for a deleted edge `e = c`.
The Lean proof starts with a deleted edge within distance `k` of the center. Its initial-walk
construction requires `2 ≤ k` when that edge equals `c`. -/
theorem theorem_7_8_proof
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {c : Set S}
    (hθ : 2 * k + 2 ≤ θ)
    (hd : HasTangleMetric Γ θ T d)
    (hc : c ∈ Γ.A)
    (hSub : Γ'.IsSubdrawing Γ)
    (h2cell' : (PaintingOrDrawing.drawing Γ').IsTwoCell)
    (hdist : ∀ e ∈ Γ.E \ Γ'.E, d c e ≤ k)
    (hck : c ∈ Γ.E \ Γ'.E → 2 ≤ k) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ),
      HasTangleMetric Γ' (θ - 2 * k) T' d' ∧
      ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d' a' b' := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  -- First handle the case `Γ.E \ Γ'.E = ∅`, where `Γ' = Γ`.
  by_cases hE_diff : (Γ.E \ Γ'.E).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hE_diff
    have hE_eq : Γ'.E = Γ.E := Subset.antisymm hSub.2 hE_diff
    have hE_ne : Γ.E.Nonempty :=
      edgeSet_nonempty_of_isTangle_of_two_le hd.1.2.1 (by omega)
    obtain ⟨K₀, hK₀⟩ := GM11.exists_radialDrawing hS hd.1.1
    have hrf := GM11.regionFacts_of_radial ⟨hK₀.1, hK₀.2.1⟩ hS hK₀.2.2 hE_ne
    have hV_eq : Γ'.V = Γ.V := by
      refine Subset.antisymm hSub.1 fun v hv => ?_
      obtain ⟨e, he, hve⟩ := exists_edge_of_regionFacts hS hrf hv
      have he' : e ∈ Γ'.E := hE_eq.symm ▸ he
      have hv_in : v ∈ closure e ∩ Γ'.V := by
        rw [hSub.closure_inter_V he']
        exact ⟨hve, hv⟩
      exact hv_in.2
    have hΓ_eq : Γ' = Γ := Drawing.ext_of_V_E hV_eq hE_eq
    subst hΓ_eq
    have htrunc : HasTangleMetric Γ' (θ - 2 * k) (GM10.truncation T (θ - 2 * k))
        (fun x y => min (d x y) (θ - 2 * k)) :=
      HasTangleMetric.truncation hd (by omega) (Nat.sub_le θ (2 * k))
    refine ⟨GM10.truncation T (θ - 2 * k), fun x y => min (d x y) (θ - 2 * k), htrunc, ?_⟩
    intro a ha b hb a' ha' b' hb' haa' hbb'
    obtain ⟨xa, hxa⟩ := atom_nonempty' ha
    obtain ⟨xb, hxb⟩ := atom_nonempty' hb
    have ha_eq : a' = a := atom_eq_of_inter_nonempty ha' ha ⟨xa, haa' hxa, hxa⟩
    have hb_eq : b' = b := atom_eq_of_inter_nonempty hb' hb ⟨xb, hbb' hxb, hxb⟩
    rw [ha_eq, hb_eq]
    have hd_le : d a b ≤ θ := by
      obtain ⟨_, K, ins, hK, _, hd_eq⟩ := id hd
      rw [hd_eq a ha b hb]
      exact tangleMetric_le_order hK ins θ a b
    change d a b - 4 * k - 2 ≤ min (d a b) (θ - 2 * k)
    omega
  -- Now `Γ.E \ Γ'.E` is nonempty; choose `e₀ ∈ Γ.E \ Γ'.E`.
  obtain ⟨e₀, he₀_Γ, he₀_not_Γ'⟩ := hE_diff
  obtain ⟨hResp, K, ins, hK, hds, hd_eq⟩ := hd
  have h2cell := hResp.1
  have hT := hResp.2.1
  have hUU : Γ.U ∩ K.U = Γ.V := hK.2.1.1
  have hpreT : IsPretangle Γ.toHypergraph θ T :=
    ⟨hT.one_le, hT.isSeparation, hT.order_lt, hT.axiom1, hT.axiom2⟩
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing Γ) hS hpreT hK.2.1.1 hds
  have hE_ne : Γ.E.Nonempty := ⟨e₀, he₀_Γ⟩
  obtain ⟨h, hh, -⟩ := existsUnique_correspondingAtom hK hc
  -- Initial closed walk `W_init` of length `≤ 2 * k` containing `h` and `e₀`.
  obtain ⟨u_init, W_init, hW_init_len, hh_init, he₀_init⟩ :=
    exists_walk_of_edge_dist_le hS hResp hE_ne hK hds hd_eq hc hh he₀_Γ (by omega)
      (hdist e₀ ⟨he₀_Γ, he₀_not_Γ'⟩) (fun hce => hck (hce ▸ ⟨he₀_Γ, he₀_not_Γ'⟩))
  -- Choose `W₀` of length `≤ 2 * k` with `insWalk ins K W_init ⊆ insWalk ins K W₀` and
  -- `insWalk ins K W₀` maximal among closed walks of length `≤ 2 * k` containing `h`.
  let 𝒜 : Set (Set S) :=
    {X : Set S | ∃ (u : S) (W : GraphWalk K.toGraph u u),
      W.length ≤ 2 * k ∧ h ⊆ insWalk ins K W ∧ insWalk ins K W_init ⊆ X ∧ X = insWalk ins K W}
  have h𝒜_fin : 𝒜.Finite := by
    have hSub_fin : {D : Drawing S | D.IsSubdrawing K}.Finite := by
      refine Set.Finite.of_finite_image (f := fun D : Drawing S => (D.V, D.E)) ?_ ?_
      · refine (K.finite_V.finite_subsets.prod K.finite_edges.finite_subsets).subset ?_
        rintro _ ⟨D, hD, rfl⟩
        exact ⟨hD.1, hD.2⟩
      · intro D₁ _ D₂ _ hpair
        exact Drawing.ext_of_V_E (congrArg Prod.fst hpair) (congrArg Prod.snd hpair)
    refine (hSub_fin.image (insOf ins)).subset ?_
    rintro X ⟨u, W, -, -, -, rfl⟩
    exact ⟨walkDrawing K W, walkDrawing_isSubdrawing K W, rfl⟩
  have h𝒜_ne : 𝒜.Nonempty :=
    ⟨insWalk ins K W_init, u_init, W_init, hW_init_len, hh_init, Subset.rfl, rfl⟩
  obtain ⟨X₀, ⟨u₀, W₀, hW₀_len, hh_W₀, hinit_W₀, rfl⟩, hW₀_max⟩ :=
    h𝒜_fin.exists_maximal h𝒜_ne
  have he₀_W₀ : e₀ ⊆ insWalk ins K W₀ := he₀_init.trans hinit_W₀
  -- Show that `(walkDrawing K W₀).V \ Γ.V` is nonempty.
  have hv₀_exists : ∃ v₀ ∈ (walkDrawing K W₀).V, v₀ ∉ Γ.V := by
    cases hW₀_case : W₀ with
    | nil hu₀ =>
      exfalso
      obtain ⟨p₀, hp₀⟩ := he₀_Γ.1
      have hp₀_not_K : p₀ ∉ K.U := fun hpK => by
        have hp_in : p₀ ∈ Γ.U ∩ K.U := ⟨(he₀_Γ.2.1 hp₀).1, hpK⟩
        rw [hUU] at hp_in
        exact (he₀_Γ.2.1 hp₀).2 hp_in
      have hp₀_in : p₀ ∈ insWalk ins K (GraphWalk.nil hu₀) := hW₀_case ▸ he₀_W₀ hp₀
      rcases hp₀_in with hpU | hpC
      · exact hp₀_not_K ((walkDrawing_isSubdrawing K _).U_subset hpU)
      · obtain ⟨C, ⟨hC, hCs⟩, _⟩ := mem_iUnion₂.mp hpC
        obtain ⟨_, W_C, _, hpos, _, hCE⟩ := hC
        cases W_C with
        | nil _ => exact (lt_irrefl 0 hpos).elim
        | @cons _ _ _ f hl _ =>
          have hfC : f ∈ C.E := by rw [hCE]; exact List.mem_cons_self
          have hfW : f ∈ (walkDrawing K (GraphWalk.nil hu₀)).E := hCs.2 hfC
          rw [walkDrawing_E] at hfW
          exact List.not_mem_nil hfW
    | @cons _ w₀ _ f hl rest =>
      have hbip := bipartite_of_preRadial hK.2.1 f u₀ w₀ hl
      by_cases hu₀ : u₀ ∈ Γ.V
      · refine ⟨w₀, ?_, hbip.mp hu₀⟩
        rw [walkDrawing_V]
        exact List.mem_cons_of_mem _ rest.start_mem_support
      · refine ⟨u₀, ?_, hu₀⟩
        rw [walkDrawing_V]
        exact List.mem_cons_self
  obtain ⟨v₀, hv₀_W₀, hv₀_not_Γ⟩ := hv₀_exists
  have hv₀_K : v₀ ∈ K.V := (walkDrawing_isSubdrawing K W₀).1 hv₀_W₀
  have hv₀_not_ΓU : v₀ ∉ Γ.U := fun hvU => hv₀_not_Γ (hUU ▸ ⟨hvU, K.V_subset_U hv₀_K⟩)
  obtain ⟨r, hr, hv₀_r⟩ := exists_region_of_notMem hv₀_not_ΓU
  have hr_corr : IsCorrespondingAtom Γ K r {v₀} :=
    ⟨Or.inr hr, Or.inl (Or.inl ⟨v₀, hv₀_K, rfl⟩), Or.inr (Or.inr ⟨hr, v₀, ⟨hv₀_K, hv₀_r⟩, rfl⟩)⟩
  -- Apply (7.6) to `(Γ, θ, k, T, d, r)`.
  obtain ⟨Γ'', T'', d'', r'', hSub''_del, h2cell'', hd'', hr'', hr_sub'',
    hU'', _, _, h_iv'', h_part''⟩ :=
    theorem_7_6_proof hS k (by omega) ⟨hResp, K, ins, hK, hds, hd_eq⟩ hr
  obtain ⟨hSubΓ'', hDisjZ⟩ := isSubdrawing_deleteVertices_iff.mp hSub''_del
  -- Prove `Γ''.IsSubdrawing Γ'`.
  have hSubΓ''Γ' : Γ''.IsSubdrawing Γ' := by
    exact deleted_encircling_region_le_target_drawing hS hθ (T := T) (d := d) (c := c)
      hc hSub hdist hck hResp K ins hK hds hd_eq hUU hsl hE_ne h hh u_init W_init u₀ W₀ hW₀_len
      hh_W₀ hW₀_max hinit_W₀ v₀ hv₀_W₀ hv₀_not_Γ r hr hv₀_r hr_corr Γ'' T'' d'' r'' h2cell'' hd''
      hU'' h_iv'' hSubΓ'' hDisjZ
  -- Induce `T''` in `Γ'` and apply (7.7)(ii).
  let T' := inducedBySubgraph Γ'.toHypergraph Γ''.toHypergraph (θ - 2 * k) T''
  have hSubHyp : Γ''.toHypergraph ≤ Γ'.toHypergraph := toHypergraph_le_of_isSubdrawing hSubΓ''Γ'
  have hT' : IsTangle Γ'.toHypergraph (θ - 2 * k) T' :=
    inducedBySubgraph_isTangle hSubHyp hd''.1.2.1
  have hResp' : (PaintingOrDrawing.drawing Γ').IsRespectful (θ - 2 * k) T' :=
    isRespectful_inducedBySubgraph hSubΓ''Γ' hd''.1.2.2
  have hRDT' : IsRespectfulDrawingTangle Γ' (θ - 2 * k) T' :=
    ⟨h2cell', hT', hResp'⟩
  obtain ⟨d', hd'⟩ := exists_hasTangleMetric hS hRDT'
  refine ⟨T', d', hd', fun a ha b hb a' ha' b' hb' haa' hbb' => ?_⟩
  obtain ⟨a'', ha'', ha'a''⟩ := exists_atom_superset_of_isSubdrawing hSubΓ''Γ' ha'
  obtain ⟨b'', hb'', hb'b''⟩ := exists_atom_superset_of_isSubdrawing hSubΓ''Γ' hb'
  have h1 : d a b - 4 * k - 2 ≤ d'' a'' b'' :=
    h_part'' a ha b hb a'' ha'' b'' hb'' (haa'.trans ha'a'') (hbb'.trans hb'b'')
  have h2 : d'' a'' b'' ≤ d' a' b' :=
    (theorem_7_7_proof hS hd' hSubΓ''Γ' h2cell'' le_rfl hd'').2 rfl rfl
      a' ha' b' hb' a'' ha'' b'' hb'' ha'a'' hb'b''
  exact h1.trans h2


end GraphMinor.GM12
