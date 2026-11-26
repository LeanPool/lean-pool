/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46ClaimOne
public import LeanPool.GraphMinor.GM07.Section46Lambda
public import LeanPool.GraphMinor.GM07.Section46BoundaryPaths
public import LeanPool.GraphMinor.GM07.Section46Constants
public import LeanPool.GraphMinor.GM07.Section46ConstructAndCount
public import LeanPool.GraphMinor.GM07.Section46SlideWrap
import LeanPool.GraphMinor.GM07.Section46Descend
import LeanPool.GraphMinor.GM07.Section46PsiFibres
import LeanPool.GraphMinor.GM07.Section41
import LeanPool.GraphMinor.GM07.Section46PullGraph
import LeanPool.GraphMinor.GM07.Section46NoArcs
import LeanPool.GraphMinor.GM07.Section46CuffBound
import LeanPool.GraphMinor.GM07.Section46WTransport
import LeanPool.GraphMinor.GM07.Section46Psi
import LeanPool.GraphMinor.GM07.Section46CentralLift
import LeanPool.GraphMinor.GM07.CuffSlide
import LeanPool.GraphMinor.GM07.Section35
import LeanPool.GraphMinor.GM07.NetExists
import LeanPool.GraphMinor.GM07.NetSwapBasic
import LeanPool.GraphMinor.GM07.Section2
import LeanPool.GraphMinor.GM07.Section2Base

/-!
# The reduction to the disc in VII (4.6)

Pages 224 to 228, up to the application of (4.1). From the hypotheses of (4.6)
we build the minimal net, the graphs `J`, `K`, `L`, the two cuts `θ` and `ψ`,
and the forest of claim (1). Then we pull `G` and the forest back to the disc,
and we prove `|Λ| ≤ w + k`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

theorem IsW36Bound.mono {X : Type} [TopologicalSpace X] {k n w w' : ℕ} (h : IsW36Bound X k n w)
    (hw : w ≤ w') : IsW36Bound X k n w' := by
  intro G H hG hV hH hk
  obtain ⟨H', hF, hhom, hfin, hle⟩ := h G H hG hV hH hk
  exact ⟨H', hF, hhom, hfin, hle.trans hw⟩

private theorem ncard_range_le {α β : Type*} [Finite α] (f : α → β) :
    (range f).ncard ≤ Nat.card α := by
  rw [← image_univ]
  exact (ncard_image_le finite_univ).trans_eq (ncard_univ α)

/-- The two components of `bd(Δ) - {s, t}` lie in `bd(Δ)` and are disjoint. -/
private theorem components_facts {D : Type} [TopologicalSpace D] {s t : D} {C₁ C₂ : Set D}
    (h : componentsIn (bd D \ {s, t}) = {C₁, C₂}) (hne : C₁ ≠ C₂) :
    C₁ ⊆ bd D ∧ C₂ ⊆ bd D ∧ Disjoint C₁ C₂ := by
  have hmem : ∀ C ∈ componentsIn (bd D \ {s, t}), C ⊆ bd D := by
    rintro _ ⟨x, -, rfl⟩
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have h₁ : C₁ ∈ componentsIn (bd D \ {s, t}) := h ▸ mem_insert _ _
  have h₂ : C₂ ∈ componentsIn (bd D \ {s, t}) := h ▸ mem_insert_of_mem _ rfl
  refine ⟨hmem _ h₁, hmem _ h₂, ?_⟩
  obtain ⟨x, hx, rfl⟩ := h₁
  obtain ⟨y, hy, rfl⟩ := h₂
  rw [disjoint_left]
  intro z hz₁ hz₂
  exact hne ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm)

private theorem bound_lifted_seam_vertices
    {S : Type}
    [TopologicalSpace S]
    (k : ℕ)
    (G : Drawing S)
    (a : ℕ)
    (b : ℕ)
    (c : ℕ)
    (J : Drawing S)
    (γ : Set S → ↑unitInterval → S)
    (s : ↑(longSeamEdges G J (muModel a b c k) (wMaxModel a b c k)) → ↑unitInterval)
    (t : ↑(longSeamEdges G J (muModel a b c k) (wMaxModel a b c k)) → ↑unitInterval)
    (W : ↑(longSeamEdges G J (muModel a b c k) (wMaxModel a b c k)) → Set S)
    (K : Drawing S)
    (hparts : ∀ (e : ↑(longSeamEdges G J (muModel a b c k) (wMaxModel a b c k))), s e ∈ Ioo 0 1 ∧
      t e ∈ Ioo 0 1 ∧ s e < t e ∧ W e = {γ (↑e) (s e), γ (↑e) (t e)} ∧ (W e).ncard = 2 ∧ W e ⊆ ↑e
      ∩ G.V ∧ (γ ↑e '' Iic (s e) ∩ G.V).ncard = muModel a b c k + 1 ∧ (γ ↑e '' Ici (t e) ∩
      G.V).ncard = muModel a b c k + 1 ∧ wMaxModel a b c k ≤ (γ ↑e '' Ioo (s e) (t e) ∩
      G.V).ncard)
    (hKV : K.V = ⋃ e, W e)
    (S' : Type)
    [TopologicalSpace S']
    (θ : S' → S)
    (hinj : InjOn θ (θ ⁻¹' K.U))
    (K' : Drawing S')
    (hp : IsPullbackDrawing θ K K')
    (hJE : J.E.ncard ≤ 3 * (2 * a + b + c - 1)) :
    K'.V.ncard ≤ 2 * (3 * (2 * a + b + c - 1)) := by
  let μ := muModel a b c k
  let w := wMaxModel a b c k
  have : Finite (longSeamEdges G J μ w) :=
    Set.Finite.to_subtype (J.finite_edges.subset fun e (he : e ∈ longSeamEdges G J μ w) => he.1)
  have hK'sub : InjOn θ K'.V := hinj.mono fun x hx => by
    have := K'.V_subset_U hx
    rw [hp.1] at this
    exact this
  have h1 : K'.V.ncard = (θ '' K'.V).ncard := (hK'sub.ncard_image).symm
  have h2 : θ '' K'.V ⊆ K.V := by
    rw [hp.2]
    exact image_preimage_subset _ _
  have h3 : K.V ⊆ range fun p : longSeamEdges G J μ w × Bool =>
      bif p.2 then γ p.1.1 (s p.1) else γ p.1.1 (t p.1) := by
    rw [hKV]
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    rw [(hparts e).2.2.2.1] at he
    rcases he with rfl | h
    · exact ⟨(e, true), rfl⟩
    · exact ⟨(e, false), (mem_singleton_iff.mp h).symm⟩
  have hrf := Set.toFinite (range fun p : longSeamEdges G J μ w × Bool =>
      bif p.2 then γ p.1.1 (s p.1) else γ p.1.1 (t p.1))
  have h4 := ncard_le_ncard h2 (hrf.subset h3)
  have h5 := ncard_le_ncard h3 hrf
  have h6 := ncard_range_le fun p : longSeamEdges G J μ w × Bool =>
      bif p.2 then γ p.1.1 (s p.1) else γ p.1.1 (t p.1)
  have h7 : Nat.card (longSeamEdges G J μ w × Bool) = 2 * (longSeamEdges G J μ w).ncard := by
    rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm]
  have h8 : (longSeamEdges G J μ w).ncard ≤ J.E.ncard :=
    ncard_le_ncard (fun e he => he.1) J.finite_edges
  omega

private theorem boundary_vertex_lifts_to_cuff
    {S : Type}
    [TopologicalSpace S]
    [T1Space S]
    (hS : IsSurface S)
    [ConnectedSpace S]
    (hcuffs : 2 ≤ (cuffs S).ncard)
    (k : ℕ)
    (G : Drawing S)
    (hG : G.IsProper)
    (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    (a : ℕ)
    (b : ℕ)
    (c : ℕ)
    (hii : ∀ (B : Set S), G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vModel a b c k →
      IsNullHomotopicOArc B ∨ ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hc : 2 ≤ c)
    [hmodel : Nonempty (S ≃ₜ SurfaceModel a b c)]
    (hv : vSurface S k = vModel a b c k)
    (N : Net S)
    (hmin : N.IsMinimalFor G)
    (J : Drawing S)
    (hJ : N.IsSeamGraphFor J)
    (hnorm : G.IsNormal J.U)
    (z : S)
    (hz : z ∈ G.V ∩ bd S) :
    ∃ l : N.D, N.φ l = z ∧ ∃ C ∈ cuffs S, z ∈ C ∧
      ∃ (n : ℕ) (P : Fin n → Drawing S) (e : Fin n → S),
        (∀ i, (P i).IsSubdrawing G ∧ e i ∈ G.V ∩ (bd S \ C) ∧ (P i).IsPathBetween z (e i)) ∧
        (∀ i j, i ≠ j → Disjoint ((P i).V \ {z, e i}) ((P j).V \ {z, e j})) ∧
        ∃ I : Finset (Fin n), muModel a b c k ≤ I.card ∧
          ∀ i ∈ I, ∃ f ∈ (P i).E, l ∈ closure (N.φ ⁻¹' f) ∧
            ∀ x ∈ closure (N.φ ⁻¹' f), N.φ x = z → x = l := by
  obtain ⟨C, hC, hzC⟩ : ∃ C ∈ cuffs S, z ∈ C := by
    have := hz.2
    rw [← sUnion_cuffs] at this
    exact this
  obtain ⟨C', hC', hne⟩ := Set.exists_ne_of_one_lt_ncard (s := cuffs S)
    (lt_of_lt_of_le one_lt_two hcuffs) C
  obtain ⟨P, e, l, hl, h1, h2, h3⟩ := N.exists_boundary_paths_and_lift_4_6 hS hc hmodel hv hG hmin
    hJ hnorm hbd (by rw [hv]; exact hii) hiii hC hC' hne.symm hz.1 hzC
  exact ⟨l, hl, C, hC, hzC, _, P, e, h1, h2, h3⟩

/-- Pages 224 to 228 of VII (4.6). -/
theorem exists_disc_reduction [T1Space S] (hS : IsSurface S) [ConnectedSpace S]
    (hcuffs : 2 ≤ (cuffs S).ncard) (k : ℕ) (G H : Drawing S)
    (hG : G.IsProper) (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    (hH : IsSurfaceForest H) (hbdeq : G.V ∩ bd S = H.V ∩ bd S) :
    ∃ (N : Net S) (J K : Drawing S) (a b c : ℕ) (Gd Hd : Drawing N.D)
      (γ : Set S → unitInterval → S)
      (sK tK : longSeamEdges G J (muModel a b c k) (wMaxModel a b c k) → unitInterval)
      (l : S → N.D),
      N.IsMinimalFor G ∧ N.IsSeamGraphFor J ∧ 2 ≤ c ∧ Nonempty (S ≃ₜ SurfaceModel a b c) ∧
      vSurface S k = vModel a b c k ∧ IsPullbackDrawing N.φ G Gd ∧ EdgePar J γ ∧
      (∀ e, sK e ∈ Ioo 0 1 ∧ tK e ∈ Ioo 0 1 ∧ sK e < tK e ∧
        (γ e.1 '' Iic (sK e) ∩ G.V).ncard = muModel a b c k + 1 ∧
        (γ e.1 '' Ici (tK e) ∩ G.V).ncard = muModel a b c k + 1) ∧
      K.U ⊆ (⋃ e, γ e.1 '' Icc (sK e) (tK e)) ∧
      (∀ z ∈ G.V ∩ bd S, N.φ (l z) = z ∧ ∃ C ∈ cuffs S, z ∈ C ∧
        ∃ (n : ℕ) (P : Fin n → Drawing S) (e : Fin n → S),
          (∀ i, (P i).IsSubdrawing G ∧ e i ∈ G.V ∩ (bd S \ C) ∧ (P i).IsPathBetween z (e i)) ∧
          (∀ i j, i ≠ j → Disjoint ((P i).V \ {z, e i}) ((P j).V \ {z, e j})) ∧
          ∃ I : Finset (Fin n), muModel a b c k ≤ I.card ∧
            ∀ i ∈ I, ∃ f ∈ (P i).E, l z ∈ closure (N.φ ⁻¹' f) ∧
              ∀ x ∈ closure (N.φ ⁻¹' f), N.φ x = z → x = l z) ∧
      Gd.IsProper ∧ IsSurfaceForest Hd ∧ Hd.V ∩ bd N.D = Gd.V ∩ bd N.D ∧
      (IsGFeasible Gd Hd → IsGFeasible G H) ∧
      ∀ s t : N.D, ∀ C₁ C₂ : Set N.D, componentsIn (bd N.D \ {s, t}) = {C₁, C₂} → C₁ ≠ C₂ →
        ∀ Λ : Set (Set N.D), Λ = {V₀ : Set N.D | ∃ C : Drawing N.D,
          GM06.IsGraphComponent C.toGraph Hd.toGraph ∧ V₀ = C.V ∧
          (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀} →
        Λ.ncard ≤ wMaxModel a b c k + k ∧ Λ.PairwiseDisjoint id ∧
        (∀ lam ∈ Λ, (lam ∩ C₁).Nonempty ∧ (lam ∩ C₂).Nonempty) ∧
        ∀ lam ∈ Λ, ∀ d ∈ lam ∩ (C₁ ∪ C₂), d ∈ Gd.V ∧
          (N.φ d ∈ K.U ∨ ∃ z ∈ G.V ∩ bd S, d = l z) := by
  classical
  have : T2Space S := hS.2.1
  have : Nonempty S := inferInstance
  obtain ⟨a, b, c, hc, hmodel, hv⟩ := exists_model_vSurface_two_cuffs hS hcuffs k
  obtain ⟨N, hmin⟩ := exists_minimal_net S hS inferInstance hcuffs G hG
  obtain ⟨J, hJ, hnorm⟩ := hmin.1
  obtain ⟨γ, hγ, hsides⟩ := N.exists_edgePar_sides hJ
  set μ := muModel a b c k with hμ
  set w := wMaxModel a b c k with hw
  obtain ⟨s, t, W, J', K, L, hparts, hU, hV, hKsub, hKV, hKE, hLsub, hLV, hLE, hLp, hLn, hLc⟩ :=
    exists_seam_parts_with_L_bound hS N hG hmin hJ hc hmodel hcuffs hbd hiii hγ
  rw [hv] at hi hii
  have h2k : 2 * k ≤ vModel a b c k := by
    unfold vModel
    omega
  have hsum : (G.V ∩ L.U).ncard + (G.V ∩ bd S).ncard ≤ vModel a b c k := by omega
  obtain ⟨S', top, θ, c', hθ, -, hmodel'⟩ :=
    exists_cut_L_4_6 hS hmodel N hcuffs hJ hG hnorm hLsub hU hLp hLn hsum hi hii hiii
  have hNo := noArcs_L_of_contact_sum hS N hcuffs hJ hG hnorm hLsub hU hLp hsum hi hii hiii
  have hbounds := constants_bounds_4_6 (a := a) (b := b) (k := k) hc
  have hsmall : (G.V ∩ bd S).ncard < 2 * μ + w + 2 := by omega
  have hlong : ∀ e : longSeamEdges G J μ w, Disjoint e.1 (bd S) := fun e =>
    longSeamEdge_disjoint_bd hS N hJ hbd e.2
  obtain ⟨hPair, hKp, hKL, hKn, hKU, hcover, hoff⟩ := central_K_facts hS N hJ hγ
    (fun e => ⟨(hparts e).1, (hparts e).2.1, (hparts e).2.2.1, (hparts e).2.2.2.1,
      (hparts e).2.2.2.2.1⟩) hsmall hlong hU hV hKsub hKV hKE hLsub hLV hLE
  have hJU : J.U = bd S ∪ L.U ∪ K.U := by rw [hcover]; exact hJ.2.1
  have hLseam : L.U ⊆ N.seamU := by
    rw [← hcover]
    exact fun x hx => .inl (.inr hx)
  obtain ⟨ψ, hψc, hψs, hψ⟩ := N.exists_psi hS hθ hLseam
  have hS' := hθ.isSurface
  have : T2Space S' := hS'.2.1
  choose i hi using fun e : longSeamEdges G J μ w =>
    hsides e.1 e.2.1 (disjoint_iff_inter_eq_empty.mp (hlong e))
  have hIoo : ∀ e, ∀ r ∈ Icc (s e) (t e), r ∈ Ioo (0 : unitInterval) 1 := fun e r hr =>
    ⟨lt_of_lt_of_le (hparts e).1.1 hr.1, lt_of_le_of_lt hr.2 (hparts e).2.1.2⟩
  have hoff' : ∀ e, ∀ r ∈ Ioo (s e) (t e), N.φ (N.f (i e) r) ∉ bd S ∪ L.U := fun e r hr => by
    rw [← hi e r]
    exact hoff e r hr
  have hsame : ∀ e, ∀ r ∈ Icc (s e) (t e), ψ (N.f (i e) r) = ψ (N.g (i e) r) := fun e =>
    N.psi_sides_eq hθ hψc hψ (i e) (hparts e).2.2.1 (hoff' e)
  have hfibre : ∀ e, ∀ r ∈ Icc (s e) (t e), ∀ z : S', θ z = γ e.1 r → z = ψ (N.f (i e) r) := by
    intro e r hr z hz
    obtain ⟨z₀, rfl⟩ := hψs z
    have hmem : z₀ ∈ N.φ ⁻¹' {N.φ (N.f (i e) r)} := by
      change N.φ z₀ = _
      rw [← hψ z₀, hz, hi e r]
    rw [N.fiber_eq_pair_of_mem_Ioo (i e) (hIoo e r hr)] at hmem
    rcases hmem with h | h
    · rw [h]
    · rw [mem_singleton_iff.mp h, hsame e r hr]
  have hinj : InjOn θ (θ ⁻¹' K.U) := by
    intro x hx y hy hxy
    obtain ⟨e, r, hr, hrr⟩ := mem_iUnion.mp (hKU hx)
    rw [hfibre e r hr x hrr.symm, hfibre e r hr y (hxy ▸ hrr.symm)]
  obtain ⟨K', hp, hmatch, hpair⟩ := exists_lifted_matching hS hθ hPair hKp hKL hKn hinj
  have hψcut := N.isCutAlongGraph_psi hθ hp hmatch hpair hψc hψs hψ hcover
  have hendsG : ∀ e, γ e.1 (s e) ∈ G.V ∧ γ e.1 (t e) ∈ G.V := fun e => by
    have hW := (hparts e).2.2.2.2.2.1
    have heq := (hparts e).2.2.2.1
    exact ⟨(hW (heq ▸ mem_insert _ _)).2, (hW (heq ▸ mem_insert_of_mem _ rfl)).2⟩
  have hendsL : ∀ e, γ e.1 (s e) ∈ L.U ∧ γ e.1 (t e) ∈ L.U := fun e => by
    have heq := (hparts e).2.2.2.1
    have hsub : W e ⊆ L.U := fun x hx => L.V_subset_U (by
      rw [hLV, hV]
      exact .inr (mem_iUnion.mpr ⟨e, hx⟩))
    exact ⟨hsub (heq ▸ mem_insert _ _), hsub (heq ▸ mem_insert_of_mem _ rfl)⟩
  have hKIoo : ∀ e, ∀ r ∈ Ioo (s e) (t e), γ e.1 r ∈ K.U := fun e r hr => by
    have hseam : γ e.1 r ∈ bd S ∪ L.U ∪ K.U := by
      rw [hcover, hi e r]
      exact mem_image_of_mem _ (N.range_f_subset_bd _ (mem_range_self r))
    exact hseam.resolve_left (hoff e r hr)
  have hslide := N.exists_matching_slide hγ hsides hlong s t
    (fun e => ⟨(hparts e).1, (hparts e).2.1, (hparts e).2.2.1⟩) hendsG hendsL
    (fun e => (hparts e).2.2.2.2.2.2.2.2) hKU hKIoo hoff hθ hp hψcut hψc hψs hψ hinj
  have habc : 2 * a + b + c > 1 := by omega
  obtain ⟨-, hJE⟩ := theorem_2_4_proof hS habc hmodel hG hmin hJ
  have hK'c : K'.V.ncard ≤ 2 * (3 * (2 * a + b + c - 1)) := by
    exact bound_lifted_seam_vertices (S := S) k G a b c J γ s t W K hparts hKV S' θ hinj K'
      hp hJE
  have hcc := cut_model_cuff_bound_4_6 hS N hG hmin hJ hc hmodel hmodel' hγ s t W
    (fun e => ⟨(hparts e).1, (hparts e).2.1, (hparts e).2.2.1, (hparts e).2.2.2.1⟩) hU hV hLE hLn
      hθ hNo
  have hw36 : IsW36Bound S' (2 * k) (3 * (2 * a + b + c - 1)) w :=
    (theorem_3_6_proof hS' _ _).mono
      (wSurface_cut_model_le_wMaxModel hmodel' hcc)
  have hlift : ∀ z ∈ G.V ∩ bd S, ∃ l : N.D, N.φ l = z ∧ ∃ C ∈ cuffs S, z ∈ C ∧
      ∃ (n : ℕ) (P : Fin n → Drawing S) (e : Fin n → S),
        (∀ i, (P i).IsSubdrawing G ∧ e i ∈ G.V ∩ (bd S \ C) ∧ (P i).IsPathBetween z (e i)) ∧
        (∀ i j, i ≠ j → Disjoint ((P i).V \ {z, e i}) ((P j).V \ {z, e j})) ∧
        ∃ I : Finset (Fin n), muModel a b c k ≤ I.card ∧
          ∀ i ∈ I, ∃ f ∈ (P i).E, l ∈ closure (N.φ ⁻¹' f) ∧
            ∀ x ∈ closure (N.φ ⁻¹' f), N.φ x = z → x = l := fun z hz => by
    exact boundary_vertex_lifts_to_cuff (S := S) hS hcuffs k G hG hbd hiii a b c hii hc hv N hmin
      J hJ hnorm z hz
  have : Nonempty N.D := ⟨(N.quotientMap_φ.surjective (Classical.arbitrary S)).choose⟩
  choose! l hl using hlift
  have hnormL : G.IsNormal L.U := fun x hx => hnorm ⟨hJU ▸ .inl (.inr hx.1), hx.2⟩
  obtain ⟨H₆, H₆', T, hF₆, hhom₆, hp₆, hF₆', hE₆, hmain, hGV, hTc, hT, hTf, hTc', hTb⟩ :=
    exists_claim_one hS hθ hNo hH hbdeq hbd (fun z => ψ (l z))
      (fun z hz => by rw [hψ, (hl z hz).1]) hp hmatch hK'c hw36 hslide
  have hnormH : H₆.IsNormal L.U := fun x hx => hGV (hmain ⟨hx.2, .inl (.inr hx.1)⟩)
  have hnormH' : H₆'.IsNormal K'.U := by
    rintro x ⟨hxK, hxU⟩
    rw [hp₆.2]
    rw [hp₆.1] at hxU
    rw [hp.1] at hxK
    exact hGV (hmain ⟨hxU, .inr hxK⟩)
  obtain ⟨Hd, hpd, hFd⟩ := exists_pull_forest hS' hψcut hF₆' hnormH'
  obtain ⟨G₁, hG₁, hG₁p, hG₁E⟩ := exists_pullback_graph hS hθ hG hnormL
  have hnormG₁ : G₁.IsNormal K'.U := by
    rintro x ⟨hxK, hxU⟩
    rw [hG₁.2]
    rw [hG₁.1] at hxU
    rw [hp.1] at hxK
    exact hnorm ⟨hJU ▸ .inr hxK, hxU⟩
  obtain ⟨Gd, hGd, hGdp, hGdE⟩ := exists_pullback_graph hS' hψcut hG₁p hnormG₁
  have hcomp : θ ∘ ψ = N.φ := funext hψ
  have hE : ∀ e' ∈ Gd.E, ∃ e ∈ G.E, (θ ∘ ψ) '' e' = e := by
    intro e' he'
    obtain ⟨e₁, he₁, rfl⟩ := hGdE e' he'
    obtain ⟨g, hg, rfl⟩ := hG₁E e₁ he₁
    refine ⟨g, hg, ?_⟩
    rw [← preimage_comp, image_preimage_eq _ (hθ.quotientMap.surjective.comp hψs)]
  have hpull : IsPullbackDrawing N.φ G Gd := by
    rw [← hcomp]
    exact ⟨by rw [hGd.1, hG₁.1, preimage_comp], by rw [hGd.2, hG₁.2, preimage_comp]⟩
  have hHd : Hd.V = N.φ ⁻¹' H₆.V := by
    rw [← hcomp, hpd.2, hp₆.2, preimage_comp]
  have hbdD : Hd.V ∩ bd N.D = Gd.V ∩ bd N.D := by
    rw [hHd, hpull.2]
    ext x
    constructor
    · rintro ⟨hx, hb⟩
      refine ⟨?_, hb⟩
      have hseam : N.φ x ∈ bd S ∪ L.U ∪ K.U := by
        rw [hcover]
        exact mem_image_of_mem _ hb
      exact hmain ⟨H₆.V_subset_U hx, hseam⟩
    · rintro ⟨hx, hb⟩
      exact ⟨hGV hx, hb⟩
  have : T2Space N.D := N.isSurface_D.2.1
  have hTbf : (T ∩ bd S').Finite := ((G.finite_V.subset inter_subset_left).image _).subset hTb
  have hTbc : (T ∩ bd S').ncard ≤ 2 * k :=
    (ncard_le_ncard hTb ((G.finite_V.subset inter_subset_left).image _)).trans
      ((ncard_image_le (G.finite_V.subset inter_subset_left)).trans hbd)
  have hfib : ∀ v ∈ K'.U, (ψ ⁻¹' {v}).ncard ≤ 2 := by
    intro v hv'
    have hvK : θ v ∈ K.U := by
      rw [hp.1] at hv'
      exact hv'
    obtain ⟨e, r, hr, hrr⟩ := mem_iUnion.mp (hKU hvK)
    have hsub : ψ ⁻¹' {v} ⊆ N.φ ⁻¹' {N.φ (N.f (i e) r)} := by
      intro x hx
      change N.φ x = _
      rw [← hψ x, show ψ x = v from hx, ← hrr, hi e r]
    have h2 := N.fiber_ncard_two_of_mem_Ioo (i e) (hIoo e r hr)
    rw [← h2]
    exact ncard_le_ncard hsub (N.finite_fiber _)
  refine ⟨N, J, K, a, b, c, Gd, Hd, γ, s, t, l, hmin, hJ, hc, hmodel, hv, hpull, hγ,
    fun e => ⟨(hparts e).1, (hparts e).2.1, (hparts e).2.2.1, (hparts e).2.2.2.2.2.2.1,
      (hparts e).2.2.2.2.2.2.2.1⟩, hKU, hl, hGdp, hFd, hbdD, ?_, ?_⟩
  · intro hfe
    have hfe₆ : IsGFeasible G H₆ := isGFeasible_of_pullback hS hθ hψcut hF₆ hnormH hF₆' hnormH'
      hp₆ hpd hG₁ hGd hE hfe
    obtain ⟨X, hX, hhX, hsub⟩ := hfe₆
    exact ⟨X, hX, hhom₆.trans hhX, hsub⟩
  · rintro s₀ t₀ C₁ C₂ hcomps hne Λ rfl
    obtain ⟨hC₁, hC₂, hdis⟩ := components_facts hcomps hne
    refine ⟨card_Lambda_le hS' hψcut hpd hTc hT hTf hTc' hTbf hTbc hfib hC₁ hC₂ hdis s₀ t₀, ?_,
      ?_, ?_⟩
    · rintro A ⟨C, hC, rfl, -⟩ B ⟨C', hC', rfl, -⟩ hAB
      change Disjoint C.V C'.V
      rw [disjoint_left]
      intro x hx hx'
      have : C.toGraph = C'.toGraph := hC.eq_of_mem_mem hC' hx hx'
      exact hAB (congrArg (fun g : Graph N.D (Set N.D) => g.vertexSet) this)
    · rintro _ ⟨C, -, rfl, h₁, h₂, -⟩
      exact ⟨h₁, h₂⟩
    · rintro _ ⟨C, hC, rfl, ⟨d₁, hd₁, hd₁C⟩, ⟨d₂, hd₂, hd₂C⟩, -⟩ d ⟨hd, hdC⟩
      have hne' : d₁ ≠ d₂ := fun h => disjoint_left.mp hdis hd₁C (h ▸ hd₂C)
      have hdb : d ∈ bd N.D := hdC.elim (fun h => hC₁ h) fun h => hC₂ h
      have hdHd : d ∈ Hd.V := hC.1.vertexSet_mono hd
      have hdG : d ∈ Gd.V := (hbdD.subset ⟨hdHd, hdb⟩).1
      obtain ⟨d', hd', hdne⟩ : ∃ d' ∈ C.V, d ≠ d' := by
        by_cases h : d = d₁
        · exact ⟨d₂, hd₂, h ▸ hne'⟩
        · exact ⟨d₁, hd₁, h⟩
      obtain ⟨hT₁, hor⟩ := image_mem_of_component hψcut hpd hTc hT hC hd hd' hdne hdb
      refine ⟨hdG, ?_⟩
      by_cases hK : ψ d ∈ K'.U
      · left
        rw [← hψ d]
        rw [hp.1] at hK
        exact hK
      · right
        obtain ⟨z, hz, hzeq⟩ := hTb _ ⟨hT₁, hor.resolve_left hK⟩
        exact ⟨z, hz, hψcut.eq_of_eq_of_notMem hS' hzeq.symm hK⟩

end GraphMinor.GM07
