/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM19.Section7d
import LeanPool.GraphMinor.GM11.Solid

import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XIX, (7.1)

The proof of the paper works with the sets `Z(i)`, the unions of `ins(W)` over closed walks `W` with
`z* ⊆ ins(W)`. We use `TangleDatum.reach c k`, the union of all restraints that contain the point
`c` and
have length at most `k`. This is the set of (8.10) of Graph Minors XI. By
`TangleDatum.exists_walk_of_restraint`
it is also a union of sets `ins(W)`, so that `Z(i)` is `reach c (2 i - 2)`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

theorem isOArc_nonempty {T : Type} [TopologicalSpace T] {F : Set T} (hF : IsOArc F) : F.Nonempty
  := by
  obtain ⟨φ⟩ := hF
  exact ⟨(φ 1).1, (φ 1).2⟩

namespace TangleDatum

/-- The union of all restraints that contain `c`, of length at most `k`. -/
noncomputable def reach (D : TangleDatum cap χ) (c : Shat) (k : ℕ) : Set Shat :=
  restraintUnion D.rad.G D.ins (2 * D.rep) c k

omit [T2Space S] in
theorem mem_reach {D : TangleDatum cap χ} {c x : Shat} {k : ℕ} :
    x ∈ D.reach c k ↔ ∃ X, IsRestraint D.rad.G D.ins (2 * D.rep) X ∧
      perimeterWalkLength D.rad.G X ≤ k ∧ c ∈ X ∧ x ∈ X := by
  simp only [reach, restraintUnion, mem_iUnion, exists_prop, mem_ofPred_eq]
  constructor
  · rintro ⟨X, ⟨h₁, h₂, h₃⟩, hx⟩
    exact ⟨X, h₁, h₂, h₃, hx⟩
  · rintro ⟨X, h₁, h₂, h₃, hx⟩
    exact ⟨X, ⟨h₁, h₂, h₃⟩, hx⟩

omit [T2Space S] in
theorem reach_mono (D : TangleDatum cap χ) (c : Shat) {a b : ℕ} (h : a ≤ b) :
    D.reach c a ⊆ D.reach c b := fun _ hx ↦ by
  obtain ⟨X, h₁, h₂, h₃⟩ := mem_reach.mp hx
  exact mem_reach.mpr ⟨X, h₁, h₂.trans h, h₃⟩

omit [T2Space S] in
theorem subset_reach {D : TangleDatum cap χ} {c : Shat} {k : ℕ} {X : Set Shat}
    (hX : IsRestraint D.rad.G D.ins (2 * D.rep) X) (hl : perimeterWalkLength D.rad.G X ≤ k)
    (hc : c ∈ X) : X ⊆ D.reach c k := fun _ hx ↦ mem_reach.mpr ⟨X, hX, hl, hc, hx⟩

omit [T2Space S] in
theorem dist_self (D : TangleDatum cap χ) (a : Set Shat) : D.dist a a = 0 := by
  simp [dist, tangleMetric]

omit [T2Space S] [T2Space Shat] in
/-- Each edge of `Γ` lies in a region of `Γ*`. -/
theorem exists_region_of_edge (D : TangleDatum cap χ) {e : Set S} (he : e ∈ D.P.Γ.E) :
    ∃ s ∈ D.rad.G.R, cap.emb '' e ⊆ s := by
  have hoff : Disjoint (cap.emb '' e) D.rad.G.U :=
    disc_edge_disjoint D.rad ⟨subset_rfl, subset_rfl⟩ he
  obtain ⟨x, hx⟩ := he.1
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hoff (mem_image_of_mem _ hx))
  exact ⟨r, hr, subset_region hr (he.2.2.1.isConnected.isPreconnected.image _
    cap.isEmbedding.continuous.continuousOn) hoff (mem_image_of_mem _ hx) hxr⟩

omit [T2Space S] [T2Space Shat] in
/-- The three kinds of atoms. -/
theorem atom_cases {Γ : Painting S} {z : Set Shat} (hz : z ∈ Γ.atoms cap) :
    (∃ v ∈ Γ.V, z = {cap.emb v}) ∨ (∃ e ∈ Γ.E, z = cap.emb '' e) ∨ z ∈ Γ.hatRegions cap := by
  rcases hz with (⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩) | h
  · exact Or.inl ⟨v, hv, rfl⟩
  · exact Or.inr (Or.inl ⟨e, he, rfl⟩)
  · exact Or.inr (Or.inr h)

section Main



omit [T2Space S] in
/-- `ins(W)` is a restraint, by (8.5) of Graph Minors XI. -/
theorem isRestraint_ins (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep)
    (T : ClosedWalkIns D.rad D.ord D.𝒯) :
    IsRestraint D.rad.G D.ins (2 * D.rep) T.ins ∧
      perimeterWalkLength D.rad.G T.ins ≤ 2 * T.halfLen := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlen : T.walk.length < 2 * D.rep := by
    rw [T.walk_len]
    have := T.halfLen_lt
    change T.halfLen < D.rep at this
    omega
  have h := GM11.theorem_8_5_proof hT (D.isSlope hrep) T.walk hlen
  rw [D.ins_eq_insWalk]
  exact ⟨h.1, h.2.trans T.walk_len.le⟩

/-- Each restraint is `ins(W)` for a closed walk `W` of its length, by (8.3) of Graph Minors XI. -/
theorem exists_walk_of_restraint (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {X : Set Shat}
    (hX : IsRestraint D.rad.G D.ins (2 * D.rep) X) :
    ∃ T : ClosedWalkIns D.rad D.ord D.𝒯, T.ins = X ∧
      2 * T.halfLen = perimeterWalkLength D.rad.G X := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨u, W, -, hl, hlt, -, hd⟩ := hX.exists_walk hT
  have h₁ := insWalk_eq hT (D.isSlope hrep) hX hd
  obtain ⟨T, h₂, h₃⟩ := D.exists_closedWalkIns W hlt
  exact ⟨T, h₂.trans h₁, h₃.trans hl⟩

omit [T2Space S] in
/-- A restraint that meets `reach c a` lies in a larger `reach`, by the step of (9.1) of Graph
Minors XI. -/
theorem reach_grow (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {c x : Shat} {a b : ℕ}
    (hx : x ∈ D.reach c a) {X : Set Shat} (hX : IsRestraint D.rad.G D.ins (2 * D.rep) X)
    (hxX : x ∈ X) (hl : perimeterWalkLength D.rad.G X ≤ b) (hab : a + b < 2 * D.rep) :
    X ⊆ D.reach c (a + b) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨Y, hY, hlY, hc, hxY⟩ := mem_reach.mp hx
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := exists_restraint_union hT (D.isSlope hrep) hY hX
    ⟨x, hxY, hxX⟩ (by omega)
  exact h₃.trans (subset_reach h₁ (by omega) (h₂ hc))

omit [T2Space S] in
/-- A short circuit of `Γ*` lies in a restraint of its length. -/
theorem exists_restraint_of_circuit (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {F : Drawing Shat}
    (hF : F.IsCircuitOf D.rad.G) (hlt : F.E.ncard < 2 * D.rep) :
    ∃ X, IsRestraint D.rad.G D.ins (2 * D.rep) X ∧ perimeterWalkLength D.rad.G X ≤ F.E.ncard ∧
      D.ins F ⊆ X ∧ F.U ⊆ X := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨u, W, ⟨hnd, hed⟩, -, hV, hE⟩ := hF.2
  obtain ⟨W', hs, he⟩ := hF.1.exists_walk_up W
  have hlen : W'.length = F.E.ncard := by
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set Shat)) := by
      ext x
      simp
    rw [hE, h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    change W'.edges.length = _
    rw [he]
  have hsub : F.IsSubdrawing (walkDrawing D.rad.G W') := by
    refine ⟨?_, ?_⟩
    · rw [walkDrawing_V, hV, hs]
    · rw [walkDrawing_E, hE, he]
  have h := GM11.theorem_8_5_proof hT (D.isSlope hrep) W' (by omega)
  refine ⟨_, h.1, h.2.trans hlen.le, ?_, ?_⟩
  · exact fun y hy ↦ Or.inr (mem_iUnion₂.mpr ⟨F, ⟨hF.2, hsub⟩, hy⟩)
  · exact hsub.U_subset.trans subset_union_left

/-- The closure of each region of `Γ*` lies in a restraint of length at most 6. -/
theorem exists_tie (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {s : Set Shat} (hs : s ∈ D.rad.G.R) :
    ∃ X, IsRestraint D.rad.G D.ins (2 * D.rep) X ∧ perimeterWalkLength D.rad.G X ≤ 6 ∧
      closure s ⊆ X := by
  obtain ⟨g, hg, hgs⟩ := (D.rad.region_facts χ.isSurface D.P.fits.internally_three_connected).1 s hs
  obtain ⟨F, hF, hle, hin⟩ := D.exists_circuit_around hrep hg hs hgs
  obtain ⟨X, hX, hl, hi, -⟩ := exists_restraint_of_circuit D (by omega) hF (by omega)
  exact ⟨X, hX, by omega, closure_minimal (hin.trans hi) hX.isClosed⟩

omit [T2Space S] in
/-- A vertex of `Γ*` is in a restraint of length 0. -/
theorem exists_point_restraint (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {x : Shat}
    (hx : x ∈ D.rad.G.V) :
    ∃ X, IsRestraint D.rad.G D.ins (2 * D.rep) X ∧ perimeterWalkLength D.rad.G X ≤ 0 ∧ x ∈ X := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hx' : x ∈ D.rad.G.toGraph.vertexSet := hx
  have hW : (GraphWalk.nil hx' : GraphWalk D.rad.G.toGraph x x).length < 2 * D.rep := by
    change 0 < _
    omega
  have h := GM11.theorem_8_5_proof hT (D.isSlope hrep) (GraphWalk.nil hx') hW
  refine ⟨_, h.1, h.2, Or.inl ?_⟩
  exact (walkDrawing D.rad.G _).V_subset_U (by rw [walkDrawing_V]; simp [GraphWalk.support])

/-- Each atom `z` has a point `c` with these properties: if `ins(W)` meets `z` then `c ∈ ins(W)`,
and
`z` lies in `reach c 6`. -/
theorem exists_anchor (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {z : Set Shat}
    (hz : z ∈ D.P.Γ.atoms cap) :
    ∃ c ∈ z, (∀ T : ClosedWalkIns D.rad D.ord D.𝒯, (z ∩ T.ins).Nonempty → c ∈ T.ins) ∧
      z ⊆ D.reach c 6 := by
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hR := fun T ↦ isRestraint_ins D (by omega) T
  obtain ⟨hG1, hG2, hG3, -⟩ := id D.rad.isPreRadial
  rcases atom_cases hz with ⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩ | hρ
  · refine ⟨_, mem_singleton _, ?_, ?_⟩
    · rintro T ⟨y, rfl, hy⟩
      exact hy
    · rintro _ rfl
      have hx := hG2 (mem_image_of_mem cap.emb hv)
      obtain ⟨X, hX, hl, hxX⟩ := exists_point_restraint D (by omega) hx
      exact subset_reach hX (by omega) hxX hxX
  · obtain ⟨s, hs, hes⟩ := D.exists_region_of_edge he
    obtain ⟨x, hx⟩ := he.1
    refine ⟨_, mem_image_of_mem _ hx, ?_, ?_⟩
    · rintro T ⟨y, hye, hy⟩
      exact nice_region (hR T).1.isGammaNice hs ⟨y, hes hye, hy⟩ (hes (mem_image_of_mem _ hx))
    · obtain ⟨X, hX, hl, hsX⟩ := exists_tie D hrep hs
      have hsub := hes.trans (subset_closure.trans hsX)
      exact hsub.trans (subset_reach hX hl (hsub (mem_image_of_mem _ hx)))
  · obtain ⟨w, ⟨hw, hwG⟩, huniq⟩ := hG3 z hρ
    refine ⟨w, hw, ?_, ?_⟩
    · rintro T ⟨y, hyz, hy⟩
      have hX := (hR T).1
      by_cases hyU : y ∈ D.rad.G.U
      · by_cases hyV : y ∈ D.rad.G.V
        · rw [huniq y ⟨hyz, hyV⟩] at hy
          exact hy
        · obtain ⟨e, he, hye⟩ := D.rad.G.exists_edge_of_mem hyU hyV
          have hsub : e ⊆ T.ins := nice_atom hX.isGammaNice (Or.inl (Or.inr he)) ⟨y, hye, hy⟩
          exact closure_minimal hsub hX.isClosed
            (D.rad.center_mem_closure hS he hρ ⟨y, hye, hyz⟩ hw hwG)
      · obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyU
        have hsub := nice_region hX.isGammaNice hs ⟨y, hys, hy⟩
        exact closure_minimal hsub hX.isClosed
          (D.rad.center_mem_closure_region hS hs hρ ⟨y, hys, hyz⟩ hw hwG)
    · intro q hq
      obtain ⟨s, hs, hm, hqs⟩ := D.rad.exists_region_at hS hρ (subset_closure hq)
      obtain ⟨X, hX, hl, hsX⟩ := exists_tie D hrep hs
      exact subset_reach hX hl
        (hsX (D.rad.center_mem_closure_region hS hs hρ hm hw hwG)) (hsX hqs)

/-- If `reach c a` meets the closure of a region `r` of `sk(Γ)` in `Σ̂`, then a slightly larger
`reach`
includes that closure. This is claim (1) of the paper's proof of (7.1). -/
theorem closure_sk_region (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {Sk : Drawing Shat}
    (hSk : IsSkHat cap D.P.Γ Sk) {c : Shat} {a : ℕ} {r : Set Shat} (hr : r ∈ Sk.R)
    (hm : (closure r ∩ D.reach c a).Nonempty) (ha : a + 12 < 2 * D.rep) :
    closure r ⊆ D.reach c (a + 12) := by
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  obtain ⟨p, hpr, hpa⟩ := hm
  rcases hSk.region_cases hr with hρ | ⟨c₀, hc₀, -, hrsub⟩
  · obtain ⟨w, ⟨hw, hwG⟩, -⟩ := D.rad.isPreRadial.2.2.1 r hρ
    obtain ⟨s₁, hs₁, hm₁, hp₁⟩ := D.rad.exists_region_at hS hρ hpr
    obtain ⟨X₁, hX₁, hl₁, hsX₁⟩ := exists_tie D hrep hs₁
    have h₁ := reach_grow D (by omega) hpa hX₁ (hsX₁ hp₁) hl₁ (by omega)
    have hw₁ := h₁ (hsX₁ (D.rad.center_mem_closure_region hS hs₁ hρ hm₁ hw hwG))
    intro q hq
    obtain ⟨s₂, hs₂, hm₂, hq₂⟩ := D.rad.exists_region_at hS hρ hq
    obtain ⟨X₂, hX₂, hl₂, hsX₂⟩ := exists_tie D hrep hs₂
    have hw₂ := hsX₂ (D.rad.center_mem_closure_region hS hs₂ hρ hm₂ hw hwG)
    exact reach_grow D (by omega) hw₁ hX₂ hw₂ hl₂ (by omega) (hsX₂ hq₂)
  · obtain ⟨s, hs, hcs⟩ := D.exists_region_of_edge hc₀
    have hsub : closure r ⊆ closure s := by
      refine closure_minimal (hrsub.trans ?_) isClosed_closure
      rw [← (cap.isClosedEmbedding hS).closure_image_eq]
      exact closure_mono hcs
    obtain ⟨X, hX, hl, hsX⟩ := exists_tie D hrep hs
    have h₁ := reach_grow D (by omega) hpa hX (hsX (hsub hpr)) hl (by omega)
    exact (hsub.trans hsX).trans (h₁.trans (D.reach_mono c (by omega)))

/-- **Graph Minors XIX, (7.1).** "**7.1.** *Let $\Gamma$ be a 2-cell painting with
$E(\Gamma)\ne \emptyset$ in a surface $\Sigma$, and let $\mathscr{T}$ be a tangle in $\Gamma$ with
metric $d$. Let $z\in A(\Gamma)$, and let $\kappa$ be an integer with
$4\le \kappa\le rep(\mathscr{T}) - 6$. Then there is a circuit $C$ of $sk(\Gamma)$, bounding an
open disc $\Lambda\subseteq \hat{\Sigma}$ with $z\subseteq \Lambda$, such that*" the four listed
assertions hold.

The print calls the open disc `Λ` throughout, as the Lean does. The bound `d(x, {v}) ≤ 1` in the
paper's proof of the third assertion is not needed, since
`d(z, x) < κ` already puts `x` in `ins(W)` for a walk `W` with `ins(W) ⊆ Z(κ)`. -/
theorem theorem_7_1_proof (D : TangleDatum cap χ) {z : Set Shat} (hz : z ∈ D.P.Γ.atoms cap) {κ : ℕ}
    (h4 : 4 ≤ κ) (hκ : κ + 6 ≤ D.rep) {Sk : Drawing Shat} (hSk : IsSkHat cap D.P.Γ Sk) :
    ∃ (C : Drawing Shat) (Λ : Set Shat), C.IsSubdrawing Sk ∧ C.IsCircuit ∧ IsOpenDisc Λ ∧
      IsClosedDisc (closure Λ) ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧ z ⊆ Λ ∧
      (∀ x ∈ D.P.Γ.atoms cap, (x ∩ closure Λ).Nonempty → D.dist z x ≤ κ + 5) ∧
      (∀ x ∈ D.P.Γ.atoms cap, Disjoint x Λ → κ ≤ D.dist z x) ∧
      (∀ x ∈ D.P.Γ.atoms cap, D.dist z x ≤ κ - 2 → x ⊆ Λ) ∧
      ∀ F : Drawing Shat, F.IsCircuitOf D.rad.G → F.U ⊆ closure Λ →
        F.E.ncard + 2 * (κ + 5) < 2 * D.rep → D.ins F ⊆ closure Λ := by
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hrep : 4 ≤ D.rep := by omega
  have hsl := D.isSlope (by omega)
  have hR := fun T ↦ isRestraint_ins D (by omega) T
  obtain ⟨c, hcz, hanchor, hzreach⟩ := exists_anchor D hrep hz
  have hcreach : c ∈ D.reach c 6 := hzreach hcz
  obtain ⟨r₀, hr₀, hno⟩ := GM11.theorem_8_12_proof hT hsl c
  have hdisj : ∀ k, Disjoint r₀ (D.reach c k) := by
    intro k
    refine disjoint_left.mpr fun y hy hyk ↦ ?_
    obtain ⟨X, hX, -, hc, hyX⟩ := mem_reach.mp hyk
    exact hno X hX ⟨hc, nice_region hX.isGammaNice hr₀ ⟨y, hy, hyX⟩⟩
  have hsc : ∀ k, 6 ≤ k → IsSimplyConnectedSet (D.reach c k) := fun k hk ↦
    GM11.theorem_8_10_proof hT hsl ⟨c, D.reach_mono c hk hcreach⟩
  have hcl : ∀ k, IsClosed (D.reach c k) := fun k ↦ isClosed_restraintUnion hT c k
  -- A closed disc around all of the restraints through `c`.
  set Full := D.reach c (2 * D.rep) with hFull
  have hFu : Full ≠ univ := by
    obtain ⟨y, hy⟩ := region_nonempty hr₀
    exact fun h ↦ disjoint_left.mp (hdisj _) hy (h ▸ mem_univ y)
  have hflat : IsFlat Full := fun φ hφ ↦ by
    obtain ⟨b, hb, hhom⟩ := (hsc _ (by omega)).2 φ hφ
    exact ⟨b, mem_univ _, hhom.mono (subset_univ _)⟩
  obtain ⟨Δ, hΔ, hsub⟩ := (GraphMinor.GM07.gm07_theorem_11_10.{0} Shat
    (IsClosedSurface.isSurface hT) inferInstance Full
    (isSolid_of_nice hT (hcl _) (isGammaNice_restraintUnion c _)) hflat).resolve_left hFu
  obtain ⟨Δ', hΔ', h₁, -⟩ := Surface.exists_disc_around hman hΔ (fun x _ ↦ hT.2.2 x) isOpen_univ
    (subset_univ _)
  have hFullint : Full ⊆ Δ' \ subBd Δ' := by
    rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hT hΔ']
    exact hsub.trans h₁
  have hZle : ∀ a, a ≤ 2 * D.rep → D.reach c a ⊆ Full := fun a h ↦ D.reach_mono c h
  have hrule : ∀ r ∈ Sk.R, (closure r ∩ D.reach c (2 * κ - 2)).Nonempty →
      closure r ⊆ D.reach c (2 * κ + 10) := by
    intro r hr hm
    have := closure_sk_region D hrep hSk hr hm (by omega)
    rwa [show 2 * κ - 2 + 12 = 2 * κ + 10 by omega] at this
  obtain ⟨C, Λ, hCS, hC, -, hΛo, hclΛ, hcld, hbdΛ, hbdcl, hdiff, hZΛ, heR⟩ :=
    GM14.theorem_5_2_full hT Sk hΔ' ⟨c, D.reach_mono c (by omega) hcreach⟩
    (hsc (2 * κ - 2) (by omega)).1.isConnected.isPreconnected fun r hr hm ↦
      (subset_closure.trans (hrule r hr hm)).trans ((hZle _ (by omega)).trans hFullint)
  set L := D.reach c (2 * κ + 10) with hL
  have hsubΛ : ∀ {a}, a ≤ 2 * κ - 2 → D.reach c a ⊆ Λ := fun h ↦ (D.reach_mono c h).trans hZΛ
  have hzΛ : z ⊆ Λ := hzreach.trans (hsubΛ (by omega))
  -- `U(C)` lies in `L`, and so does `ΛBar`, since `L` is simply-connected.
  have hedgeL : ∀ e ∈ C.E, closure e ⊆ L := by
    intro e he
    obtain ⟨r, hr, hinc, hm⟩ := heR e he
    have := edge_subset_closure_of_incident hT (hCS.2 he) hr hinc.2.2
    exact closure_minimal (this.trans (hrule r hr hm)) (hcl _)
  have hUL : C.U ⊆ L := by
    rw [C.U_eq]
    refine union_subset (fun v hv ↦ ?_) (iUnion₂_subset hedgeL)
    obtain ⟨e, he, hve⟩ := exists_edge_at_vertex hC hv
    exact hedgeL e he hve
  have hO := GM14.isOArc_of_isCircuit hC
  have hnull : IsNullHomotopicOArcIn L C.U := by
    obtain ⟨ψ⟩ := id hO
    refine ⟨ψ, (hsc _ (by omega)).2 _ ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hUL (ψ x).2
  obtain ⟨Δ₁, hΔ₁L, hd₁, hb₁⟩ := GM11.theorem_7_2_proof hT hO hUL hnull
  have hb₁' : discBd Δ₁ = C.U := by
    rw [← IsClosedDisc.frontier_eq_discBd hT hd₁, ← subBd_eq_frontier, hb₁]
  have hb₂' : discBd (closure Λ) = C.U := by
    rw [← IsClosedDisc.frontier_eq_discBd hT hcld, ← subBd_eq_frontier, hbdcl]
  obtain ⟨y₀, hy₀⟩ : ∃ y, y ∉ Δ' := by
    by_contra hall
    push Not at hall
    have huniv : Δ' = univ := eq_univ_of_forall hall
    obtain ⟨y, hy⟩ := isOArc_nonempty hΔ'.isOArc_discBd
    rw [← IsClosedDisc.frontier_eq_discBd hT hΔ', huniv, frontier_univ] at hy
    exact hy
  have hclsub : closure Λ = Δ₁ := disc_unique hT hO hcld hd₁ hb₂' hb₁' (fun h ↦ hy₀ (hclΛ h))
    fun h ↦ hy₀ (sdiff_subset (hFullint (hZle _ (by omega) (hΔ₁L h))))
  have hclL : closure Λ ⊆ L := hclsub ▸ hΔ₁L
  refine ⟨C, Λ, hCS, hC, hΛo, hcld, hbdcl, hdiff, hzΛ, ?_, ?_, ?_, ?_⟩
  · -- The first assertion.
    rintro x - ⟨p, hpx, hpcl⟩
    by_cases hzx : z = x
    · rw [hzx, D.dist_self]
      omega
    obtain ⟨X, hX, hl, hc, hpX⟩ := mem_reach.mp (hclL hpcl)
    obtain ⟨T, hTi, hTl⟩ := exists_walk_of_restraint D (by omega) hX
    have := D.dist_le T ⟨c, hcz, hTi ▸ hc⟩ ⟨p, hpx, hTi ▸ hpX⟩
    omega
  · -- The second assertion.
    rintro x - hdis
    by_contra hlt
    push Not at hlt
    have hne : z ≠ x := fun h ↦ disjoint_left.mp hdis (h ▸ hcz) (hzΛ hcz)
    obtain ⟨T, h₁', ⟨y, hyx, hyT⟩, h₃⟩ := D.exists_of_dist_lt hne (by omega)
    have hsubT := subset_reach (k := 2 * κ - 2) (hR T).1 (by have := (hR T).2; omega)
      (hanchor T h₁')
    exact disjoint_left.mp hdis hyx (hZΛ (hsubT hyT))
  · -- The third assertion.
    intro x hx hle
    by_cases hzx : z = x
    · exact hzx ▸ hzΛ
    obtain ⟨T, h₁', ⟨y, hyx, hyT⟩, h₃⟩ := D.exists_of_dist_lt hzx (by omega)
    have hsubT : T.ins ⊆ Λ := (subset_reach (k := 2 * κ - 2) (hR T).1 (by have := (hR T).2; omega)
      (hanchor T h₁')).trans hZΛ
    rcases atom_cases hx with ⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩ | hρ
    · rintro _ rfl
      exact hsubT (mem_singleton_iff.mp hyx ▸ hyT)
    · obtain ⟨s, hs, hes⟩ := D.exists_region_of_edge he
      exact (hes.trans (nice_region (hR T).1.isGammaNice hs ⟨y, hes hyx, hyT⟩)).trans hsubT
    · have hpre : IsPreconnected x := by
        obtain ⟨u, -, rfl⟩ := hρ
        exact isPreconnected_connectedComponentIn
      have hoff : Disjoint x (frontier (closure Λ)) := by
        refine disjoint_left.mpr fun q hq hqf ↦ ?_
        rw [← subBd_eq_frontier, hbdcl] at hqf
        have hqS := hCS.U_subset hqf
        rw [hSk.hU] at hqS
        have hqU : q ∈ D.P.Γ.hatU cap := image_mono D.P.Γ.skU_subset hqS
        obtain ⟨u, -, rfl⟩ := hρ
        exact (connectedComponentIn_subset _ _ hq) hqU
      rcases subset_or_disjoint_of_frontier isClosed_closure hpre hoff with h | h
      · refine fun q hq ↦ hdiff ▸ ⟨h hq, fun hqC ↦ disjoint_left.mp hoff hq ?_⟩
        rw [← subBd_eq_frontier, hbdcl]
        exact hqC
      · exact absurd (subset_closure (hsubT hyT)) (disjoint_left.mp h hyx)
  · -- The fourth assertion.
    intro F hF hFU hlen
    have hlt : F.E.ncard < 2 * D.rep := by omega
    obtain ⟨X, hX, hl, hi, hU⟩ := exists_restraint_of_circuit D (by omega) hF hlt
    obtain ⟨p, hp⟩ := isOArc_nonempty (GM14.isOArc_of_isCircuit hF.2)
    have hgrow := reach_grow D (by omega) (hclL (hFU hp)) hX (hU hp) hl (by omega)
    have hy₁ : ∃ y ∈ r₀, y ∉ D.ins F ∧ y ∉ closure Λ := by
      obtain ⟨y, hy⟩ := region_nonempty hr₀
      refine ⟨y, hy, fun h ↦ disjoint_left.mp (hdisj _) hy (hgrow (hi h)), fun h ↦
        disjoint_left.mp (hdisj _) hy (hclL h)⟩
    obtain ⟨y, -, hyi, hycl⟩ := hy₁
    have hd := D.ins_spec hF hlt
    obtain ⟨Δ₂, ⟨hΔ₂D, dΔ₂, bΔ₂, -⟩, -⟩ := disc_oArc (closure Λ) F.U hcld hFU
      (GM14.isOArc_of_isCircuit hF.2)
    have := disc_unique hT (GM14.isOArc_of_isCircuit hF.2) hd.2.2.1 dΔ₂ hd.2.2.2.1 bΔ₂ hyi
      fun h ↦ hycl (hΔ₂D h)
    exact this ▸ hΔ₂D

end Main

end TangleDatum

end GraphMinor.GM19
