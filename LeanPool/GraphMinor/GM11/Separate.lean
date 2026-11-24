/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section5c
public import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.GM11.ForestRegions
public import LeanPool.GraphMinor.Surface.SphereDisc
public import LeanPool.GraphMinor.Surface.DiscGrow
public import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# Points that a drawing in a sphere does not separate

`IsCircuit.isOArc_U` says that the point set of a circuit is an `O`-arc. `same_region_of_discs` is
the main
result: if every `O`-arc of a drawing in a sphere bounds a disc in a set `Q`, then the points
outside `Q`
lie in one region. This is the part of (7.6) of Graph Minors XI needed for a perimeter walk: the
paper gets
it from Graph Minors VII, (11.10), for a surface with two holes. We use circuits of `N(Z)` instead.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- **The point set of a circuit is an `O`-arc.** -/
theorem IsCircuit.isOArc_U {C : Drawing S} (hC : C.IsCircuit) : IsOArc C.U := by
  classical
  obtain ⟨u₀, W₀, -, hpos₀, hV₀, hE₀⟩ := id hC
  have hu : u₀ ∈ C.V := by
    rw [hV₀]
    cases W₀ <;> simp [GraphWalk.support]
  by_cases hone : ∃ b ∈ C.V, b ≠ u₀
  · obtain ⟨b, hb, hne⟩ := hone
    obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, hVc, hEd, hsup⟩ := Drawing.IsCircuit.exists_two_paths hC
      hu hb hne.symm
    have hl₁ := isLine_of_isPathBetween hP hne.symm
    have hl₂ := isLine_of_isPathBetween hQ hne.symm
    have hU : C.U = P.U ∪ Q.U := by
      apply subset_antisymm
      · rw [C.U_eq]
        rintro x (hx | hx)
        · rw [← hsup, Drawing.sup_V hPs hQs] at hx
          rcases hx with h | h
          · exact Or.inl (P.V_subset_U h)
          · exact Or.inr (Q.V_subset_U h)
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
          rw [← hsup, Drawing.sup_E hPs hQs] at he
          rcases he with h | h
          · exact Or.inl (P.closure_subset_U h hxe)
          · exact Or.inr (Q.closure_subset_U h hxe)
      · exact union_subset hPs.U_subset hQs.U_subset
    rw [hU]
    refine isOArc_union hl₁ hl₂ ?_
    rintro x ⟨hxP, hxQ⟩
    -- A point on both paths is a vertex of both.
    have hV : x ∈ C.V := by
      by_contra hx
      have hxPV : x ∉ P.V := fun h => hx (hPs.1 h)
      have hxQV : x ∉ Q.V := fun h => hx (hQs.1 h)
      rw [P.U_eq] at hxP
      rw [Q.U_eq] at hxQ
      obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp (hxP.resolve_left hxPV)
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp (hxQ.resolve_left hxQV)
      have h₁ : x ∈ f := (P.closure_diff_V hf).subset ⟨hxf, hxPV⟩
      have h₂ : x ∈ g := (Q.closure_diff_V hg).subset ⟨hxg, hxQV⟩
      have := C.edge_eq_of_mem (hPs.2 hf) (hQs.2 hg) h₁ h₂
      exact disjoint_left.mp hEd hf (this ▸ hg)
    have hmem : ∀ {R : Drawing S}, R.IsSubdrawing C → x ∈ R.U → x ∈ R.V := by
      intro R hR hx
      by_contra hxV
      rw [R.U_eq] at hx
      obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp (hx.resolve_left hxV)
      exact ((C.closure_diff_V (hR.2 hf)).superset ((R.closure_diff_V hf).subset ⟨hxf, hxV⟩)).2 hV
    exact hVc ▸ (⟨hmem hPs hxP, hmem hQs hxQ⟩ : x ∈ P.V ∩ Q.V)
  · push Not at hone
    have hVs : C.V = {u₀} := subset_antisymm (fun x hx => hone x hx) (singleton_subset_iff.mpr hu)
    obtain ⟨f, hf⟩ := IsCircuit.E_nonempty hC
    have hl : closure f ∩ C.V = {u₀} := by
      rcases C.edge_cond f hf with ⟨x, y, hxy, hcap, -⟩ | ⟨x, hcap, -⟩
      · have hx : x ∈ closure f ∩ C.V := by rw [hcap]; simp
        have hy : y ∈ closure f ∩ C.V := by rw [hcap]; simp
        exact (hxy ((hone x hx.2).trans (hone y hy.2).symm)).elim
      · have hx : x ∈ closure f ∩ C.V := by rw [hcap]; simp
        rw [hcap, hone x hx.2]
    have hEs := IsCircuit.E_eq_of_loop hC hf hl
    have hU : C.U = closure f := by
      rw [C.U_eq, hEs]
      simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
      exact union_eq_right.mpr (by
        rw [hVs, singleton_subset_iff]
        exact (hl.ge rfl).1)
    rw [hU]
    rcases C.edge_cond f hf with ⟨x, y, hxy, hcap, -⟩ | ⟨x, hcap, hF⟩
    · have hx : x ∈ closure f ∩ C.V := by rw [hcap]; simp
      have hy : y ∈ closure f ∩ C.V := by rw [hcap]; simp
      exact (hxy ((hone x hx.2).trans (hone y hy.2).symm)).elim
    · exact hF

variable [ConnectedSpace S]

/-- **Two points outside `Q`.** If every `O`-arc of a drawing `M` in a sphere bounds a disc inside a
set
`Q ⊇ U(M)`, then any two points outside `Q` lie in one region of `M`. -/
theorem same_region_of_discs (hS : IsClosedSurface S) (hsph : IsSphere S) {Q : Set S} {a b : S}
    (ha : a ∉ Q) (hb : b ∉ Q) :
    ∀ (k : ℕ) (M : Drawing S), M.E.ncard = k → M.U ⊆ Q →
      (∀ F, IsOArc F → F ⊆ M.U → ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ Q ∧ discBd Δ = F) →
      ∃ r ∈ M.R, a ∈ r ∧ b ∈ r := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M hk hMQ hdisc
    have haU : a ∉ M.U := fun h => ha (hMQ h)
    have hbU : b ∉ M.U := fun h => hb (hMQ h)
    obtain ⟨p, hp, hap⟩ := exists_region_of_notMem haU
    obtain ⟨q, hq, hbq⟩ := exists_region_of_notMem hbU
    by_cases hpq : p = q
    · exact ⟨p, hp, hap, hpq ▸ hbq⟩
    exfalso
    by_cases hcirc : ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing M
    swap
    · push Not at hcirc
      exact hpq (region_eq_of_noCircuit hS (fun C h₁ h₂ => hcirc C h₁ h₂) hp hq)
    obtain ⟨C₀, hC₀, hC₀s⟩ := hcirc
    obtain ⟨e, he₀⟩ := IsCircuit.E_nonempty hC₀
    have he : e ∈ M.E := hC₀s.2 he₀
    -- Delete `e`: the two points are then in one region.
    have hlt : (M.deleteEdge e).E.ncard < k := by
      rw [deleteEdge_E, ← hk]
      exact ncard_lt_ncard (sdiff_singleton_ssubset.mpr he) M.finite_edges
    have hsubD := deleteEdge_isSubdrawing M e
    obtain ⟨r', hr', har', hbr'⟩ := ih _ hlt (M.deleteEdge e) rfl (hsubD.U_subset.trans hMQ)
      fun F hF hFU => hdisc F hF (hFU.trans hsubD.U_subset)
    have hinc : ∀ {p₁ p₂ : Set S} {x y : S}, p₁ ∈ M.R → p₂ ∈ M.R → p₁ ≠ p₂ → x ∈ p₁ → y ∈ p₂ →
        x ∈ r' → y ∈ r' → (e ∩ closure p₁).Nonempty := by
      intro p₁ p₂ x y h₁ h₂ hne hx hy hxr hyr
      by_contra hdis
      have hdisj : Disjoint e (closure p₁) := disjoint_iff_inter_eq_empty.mpr
        (not_nonempty_iff_eq_empty.mp hdis)
      have hreg := region_deleteEdge_of_not_incident he h₁ hdisj
      obtain rfl := region_eq_of_mem hreg hr' hx hxr
      exact hne (region_eq_of_mem h₁ h₂ hyr hy)
    have hincp := hinc hp hq hpq hap hbq har' hbr'
    have hincq := hinc hq hp (Ne.symm hpq) hbq hap hbr' har'
    have hp₁ : M.EdgeRegionIncident e p := ⟨he, hp, hincp⟩
    have hq₁ : M.EdgeRegionIncident e q := ⟨he, hq, hincq⟩
    have heN : e ∈ (boundaryDrawing M {p}).E := mem_boundaryDrawing_E.mpr
      ⟨⟨p, rfl, hp₁⟩, q, ⟨hq, fun h => hpq (mem_singleton_iff.mp h).symm⟩, hq₁⟩
    obtain ⟨C, hC, hCN, heC⟩ := exists_circuit_N hS {p} e heN
    have hCM : C.IsSubdrawing M := hCN.trans (Drawing.span_isSubdrawing M _ _)
    have hF := IsCircuit.isOArc_U hC
    obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, huniq⟩ := sphere_disc S hsph C.U hF
    have hint₁ := IsClosedDisc.isOpen_discInt hman hΔ₁
    have hint₂ := IsClosedDisc.isOpen_discInt hman hΔ₂
    have hdint : Disjoint (discInt Δ₁) (discInt Δ₂) := by
      refine disjoint_left.mpr ?_
      rintro x ⟨h₁, h₂⟩ ⟨h₃, -⟩
      exact h₂ (by
        rw [hb₁, ← hcap]
        exact ⟨h₁, h₃⟩)
    have hcover : (C.U)ᶜ ⊆ discInt Δ₁ ∪ discInt Δ₂ := by
      intro x hx
      have hxu : x ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ x
      rcases hxu with h | h
      · exact Or.inl ⟨h, by rwa [hb₁]⟩
      · exact Or.inr ⟨h, by rwa [hb₂]⟩
    have hsplit : ∀ t ∈ M.R, t ⊆ discInt Δ₁ ∨ t ⊆ discInt Δ₂ := by
      intro t ht
      have hdisU : t ⊆ (C.U)ᶜ := fun x hx hxC => region_subset ht hx (hCM.U_subset hxC)
      exact (region_isPreconnected ht).subset_or_subset hint₁ hint₂
        hdint (hdisU.trans hcover)
    obtain ⟨y, hye⟩ := he.1
    have hyF : y ∈ C.U := C.closure_subset_U heC (subset_closure hye)
    obtain ⟨W, A₁, A₂, hW, hyW, hWU, hWcov, c₁, c₂, d₁, d₂, h₁, h₂⟩ :=
      exists_edge_sides hS M he hye
    -- Each side lies in `p` or `q`, and all points near `y` off `U(M)` lie in `p ∪ q`.
    have hyp : y ∈ closure p := edge_subset_closure_of_incident hS he hp hincp hye
    have hyq : y ∈ closure q := edge_subset_closure_of_incident hS he hq hincq hye
    obtain ⟨u₁, huW, hup⟩ := mem_closure_iff.mp hyp W hW hyW
    obtain ⟨u₂, huW', huq⟩ := mem_closure_iff.mp hyq W hW hyW
    have hreg : ∀ {A : Set S}, IsPreconnected A → Disjoint A M.U → ∀ {x}, x ∈ A → x ∈ p → A ⊆ p :=
      fun hA hd _ hx hxp => subset_region hp hA hd hx hxp
    have hreg' : ∀ {A : Set S}, IsPreconnected A → Disjoint A M.U → ∀ {x}, x ∈ A → x ∈ q → A ⊆ q :=
      fun hA hd _ hx hxp => subset_region hq hA hd hx hxp
    have hnear : W \ M.U ⊆ p ∪ q := by
      have hupU : u₁ ∈ W \ M.U := ⟨huW, region_subset hp hup⟩
      have huqU : u₂ ∈ W \ M.U := ⟨huW', region_subset hq huq⟩
      have hdis : Disjoint p q := by
        refine disjoint_left.mpr fun x hxp hxq => hpq (region_eq_of_mem hp hq hxp hxq)
      rcases hWcov hupU with a₁ | a₁ <;> rcases hWcov huqU with a₂ | a₂
      · have hs := hreg c₁ d₁ a₁ hup
        exact (disjoint_left.mp hdis (hs a₂) huq).elim
      · have hs₁ := hreg c₁ d₁ a₁ hup
        have hs₂ := hreg' c₂ d₂ a₂ huq
        exact fun x hx => (hWcov hx).elim (fun h => Or.inl (hs₁ h)) fun h => Or.inr (hs₂ h)
      · have hs₁ := hreg c₂ d₂ a₁ hup
        have hs₂ := hreg' c₁ d₁ a₂ huq
        exact fun x hx => (hWcov hx).elim (fun h => Or.inr (hs₂ h)) fun h => Or.inl (hs₁ h)
      · have hs := hreg c₂ d₂ a₁ hup
        exact (disjoint_left.mp hdis (hs a₂) huq).elim
    -- Near `y` there are points inside each of the two discs.
    have hnearInt : ∀ {Δ : Set S}, IsClosedDisc Δ → discBd Δ = C.U → ∃ z ∈ discInt Δ, z ∈ p ∪ q
      := by
      intro Δ hΔ hbd
      have hyΔ : y ∈ Δ := discBd_subset Δ (hbd ▸ hyF)
      obtain ⟨w, hwW, hwI⟩ := mem_closure_iff.mp (IsClosedDisc.subset_closure_discInt hΔ hyΔ) W hW
        hyW
      obtain ⟨z, ⟨hzW, hzI⟩, hzU⟩ := exists_notMem_U (Γ := M) hS
        (hW.inter (IsClosedDisc.isOpen_discInt hman hΔ)) ⟨w, hwW, hwI⟩
      exact ⟨z, hzI, hnear ⟨hzW, hzU⟩⟩
    obtain ⟨z₁, hz₁, hz₁r⟩ := hnearInt hΔ₁ hb₁
    obtain ⟨z₂, hz₂, hz₂r⟩ := hnearInt hΔ₂ hb₂
    have hpart : (p ⊆ discInt Δ₁ ∧ q ⊆ discInt Δ₂) ∨ (p ⊆ discInt Δ₂ ∧ q ⊆ discInt Δ₁) := by
      have hno : ∀ {t}, t ⊆ discInt Δ₁ → t ⊆ discInt Δ₂ → ∀ x ∈ t, False := fun h₃ h₄ x hx =>
        disjoint_left.mp hdint (h₃ hx) (h₄ hx)
      rcases hsplit p hp with h₃ | h₃ <;> rcases hsplit q hq with h₄ | h₄
      · exfalso
        rcases hz₂r with h₅ | h₅
        · exact disjoint_left.mp hdint (h₃ h₅) hz₂
        · exact disjoint_left.mp hdint (h₄ h₅) hz₂
      · exact Or.inl ⟨h₃, h₄⟩
      · exact Or.inr ⟨h₃, h₄⟩
      · exfalso
        rcases hz₁r with h₅ | h₅
        · exact disjoint_left.mp hdint hz₁ (h₃ h₅)
        · exact disjoint_left.mp hdint hz₁ (h₄ h₅)
    obtain ⟨Δ, hΔ, hΔQ, hΔb⟩ := hdisc C.U hF hCM.U_subset
    have hnot : ∀ {x}, x ∉ Q → x ∉ Δ := fun hx h => hx (hΔQ h)
    rcases huniq Δ hΔ hΔb with rfl | rfl
    · rcases hpart with ⟨h₃, -⟩ | ⟨-, h₃⟩
      · exact hnot ha (h₃ hap).1
      · exact hnot hb (h₃ hbq).1
    · rcases hpart with ⟨-, h₃⟩ | ⟨h₃, -⟩
      · exact hnot hb (h₃ hbq).1
      · exact hnot ha (h₃ hap).1

end GraphMinor.GM11
