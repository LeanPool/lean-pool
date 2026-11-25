/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM14.DiscSlope
public import LeanPool.GraphMinor.GM14.Section3
public import LeanPool.GraphMinor.GM11.RadialFaces
import LeanPool.GraphMinor.Surface.Collar

/-!
# Graph Minors XIV, Section 6 (Part 1): Rigidity in Subsurfaces and Regions of Rigid Drawings

This file formalizes the first part of Section 6 (pages 33–34) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50:

- `IsRigidIn`: rigidity of a drawing `H` inside a subset `S' ⊆ Σ`.
- `no_circuit_in_dial`: a dial `Δ` for `F, H` cannot contain any circuit `C` of `H`.
- `theorem_6_1`: Graph Minors XIV, (6.1) (page 33), showing that if `H` is rigid in `Σ` and
  `Σ' ⊆ Σ` is a subsurface with `bd(Σ') ∩ U(H) ⊆ V(H)` such that every closed disc `Δ' ⊆ Σ` with
  `Δ' ∩ Σ' = bd(Δ') ⊆ bd(Σ')` contains a circuit of `H`, then `H ∩ Σ'` is rigid in `Σ'`, together
  with concrete instances for `Σ \ Λ`, closed discs `Δ₀`, and cylinders `Δ₀ \ (Δ₂ \ bd(Δ₂))`.
- `theorem_6_2`: Graph Minors XIV, (6.2) (page 33), showing that around any vertex `v ∈ V(H)` of a
  rigid drawing `H`, the incident regions in cyclic order around `v` are all distinct
  (`corner_regions_injective`), and every region `r ∈ H.R` is simply-connected
  (`isArcSimplyConnected_region`) and (when `U(H) ≠ ∅`) an open disc
  (`isOpenDisc_region_of_isRigid`).
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph Hypergraph unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Rigidity in a Subset and Basic Dial Lemmas -/

/-- `H` is a rigid drawing in `S' ⊆ Σ` if for every `O`-arc `F ⊆ S'` with `F ∩ U(H) ⊆ V(H)` and
`|F ∩ V(H)| ≤ 2`, there is a dial `Δ ⊆ S'` for `F, H`
(Graph Minors XIV, Section 4, page 29, and Section 6, page 33). -/
def IsRigidIn [T1Space S] (H : Drawing S) (S' : Set S) : Prop :=
  ∀ F : Set S, F ⊆ S' → IsOArc F → F ∩ H.U ⊆ H.V → (F ∩ H.V).ncard ≤ 2 →
    ∃ Δ : Set S, Δ ⊆ S' ∧ IsDial H F Δ

/-- Rigidity in `univ` is equivalent to `IsRigid`. -/
theorem isRigidIn_univ_iff [T1Space S] {H : Drawing S} :
    IsRigidIn H univ ↔ IsRigid H := by
  constructor
  · intro h F hF hFU hFV
    obtain ⟨Δ, _, hDial⟩ := h F (subset_univ F) hF hFU hFV
    exact ⟨Δ, hDial⟩
  · intro h F _ hF hFU hFV
    obtain ⟨Δ, hDial⟩ := h F hF hFU hFV
    exact ⟨Δ, subset_univ Δ, hDial⟩

/-- Two drawings with the same point set and vertex set are equal. -/
theorem Drawing.ext_UV {Γ₁ Γ₂ : Drawing S} (hU : Γ₁.U = Γ₂.U) (hV : Γ₁.V = Γ₂.V) :
    Γ₁ = Γ₂ := by
  cases Γ₁
  cases Γ₂
  congr

/-- Two drawings with the same vertex set and edge set are equal. -/
theorem Drawing.ext_VE {Γ₁ Γ₂ : Drawing S} (hV : Γ₁.V = Γ₂.V) (hE : Γ₁.E = Γ₂.E) :
    Γ₁ = Γ₂ := by
  refine Drawing.ext_UV ?_ hV
  rw [Γ₁.U_eq, Γ₂.U_eq, hV, hE]

/-- A path drawing `P` between distinct vertices `u ≠ v` cannot contain the point set of a circuit
`C`. -/
theorem no_circuit_in_path [T2Space S] {P C : Drawing S} {u v : S}
    (hP : P.IsPathBetween u v) (huv : u ≠ v) (hC : C.IsCircuit) (hsub : C.U ⊆ P.U) : False := by
  obtain ⟨φ_L, _, _⟩ := isLine_of_isPathBetween hP huv
  obtain ⟨φ_C⟩ := isOArc_of_isCircuit hC
  let f : Circle → ℝ := fun z => (φ_L.symm ⟨(φ_C z).1, hsub (φ_C z).2⟩).1
  have hf_cont : Continuous f := by fun_prop
  have hf_inj : Function.Injective f := by
    intro z₁ z₂ hz
    have h₁ := φ_L.symm.injective (Subtype.ext hz)
    have h₂ : (φ_C z₁).1 = (φ_C z₂).1 := congrArg (·.1) h₁
    exact φ_C.injective (Subtype.ext h₂)
  exact not_injective_circle_real hf_cont hf_inj

/-- A dial `Δ` for `F, H` (where `F ∩ U(H) ⊆ V(H)`) cannot contain any circuit `C` of `H`. -/
theorem no_circuit_in_dial [T2Space S] {H C : Drawing S} {F Δ : Set S}
    (hDial : IsDial H F Δ) (hFV : F ∩ H.U ⊆ H.V)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hCU : C.U ⊆ Δ) : False := by
  rcases hDial.2.2 with h1 | ⟨u, v, huv, _, hP⟩
  · obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC
    obtain ⟨x, hxe⟩ := he.1
    have hxCU : x ∈ C.U := (he.2.1 hxe).1
    have hxHU : x ∈ H.U := hCs.U_subset hxCU
    have hxF : x ∈ F := h1 ⟨hCU hxCU, hxHU⟩
    have hxV : x ∈ H.V := hFV ⟨hxF, hxHU⟩
    have heH : e ∈ H.E := hCs.2 he
    exact (heH.2.1 hxe).2 hxV
  · have hsub : C.U ⊆ (H.interSet Δ).U := by
      intro x hx
      by_cases hxV : x ∈ C.V
      · exact (H.interSet Δ).V_subset_U (Or.inl ⟨⟨hCs.1 hxV, hCU hx⟩, hCs.1 hxV⟩)
      · obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem hx hxV
        have heH : e ∈ H.E := hCs.2 he
        have heΔ : e ⊆ Δ := fun z hz => hCU (he.2.1 hz).1
        have he_inter : e ∈ (H.interSet Δ).E := by
          change e ∈ (H.span _ _).E
          rw [H.span_E]
          exact ⟨⟨heH, heΔ⟩, heH⟩
        exact (H.interSet Δ).closure_subset_U he_inter (subset_closure hxe)
    exact no_circuit_in_path hP huv hC hsub

/-! ## 2. Subdrawings on Closed Subsets `S'` with `subBd S' ∩ U(H) ⊆ V(H)` -/

/-- Iterated `interSet` for `Δ ⊆ S'` equals `H.interSet Δ`. -/
theorem interSet_interSet_of_subset [T2Space S] (H : Drawing S) {S' Δ : Set S} (hsub : Δ ⊆ S') :
    (H.interSet S').interSet Δ = H.interSet Δ := by
  have hE_S' : (H.interSet S').E = {e ∈ H.E | e ⊆ S'} := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have hE_set : {e | e ∈ (H.interSet S').E ∧ e ⊆ Δ} ∩ (H.interSet S').E =
      {e | e ∈ H.E ∧ e ⊆ Δ} ∩ H.E := by
    rw [hE_S']
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨⟨⟨he, _⟩, heΔ⟩, _⟩ => ⟨⟨he, heΔ⟩, he⟩,
      fun ⟨⟨he, heΔ⟩, _⟩ => ⟨⟨⟨he, heΔ.trans hsub⟩, heΔ⟩, he, heΔ.trans hsub⟩⟩
  have hE_eq : ((H.interSet S').interSet Δ).E = (H.interSet Δ).E := by
    change ((H.interSet S').span _ _).E = (H.span _ _).E
    rw [(H.interSet S').span_E, H.span_E, hE_set]
  have hV_sub1 : H.V ∩ S' ⊆ (H.interSet S').V := fun x hx => Or.inl ⟨hx, hx.1⟩
  have hV_sub2 : (H.interSet S').V ⊆ H.V := H.spanV_subset _ _
  have hV_inter : (H.interSet S').V ∩ Δ = H.V ∩ Δ := by
    ext x
    exact ⟨fun ⟨hxV, hxΔ⟩ => ⟨hV_sub2 hxV, hxΔ⟩,
      fun ⟨hxV, hxΔ⟩ => ⟨hV_sub1 ⟨hxV, hsub hxΔ⟩, hxΔ⟩⟩
  have hV_eq : ((H.interSet S').interSet Δ).V = (H.interSet Δ).V := by
    change (H.interSet S').spanV ((H.interSet S').V ∩ Δ) _ = H.spanV (H.V ∩ Δ) _
    unfold Drawing.spanV
    rw [hE_set, hV_inter]
    ext x
    simp only [mem_union, mem_inter_iff, mem_iUnion]
    refine or_congr
      ⟨fun ⟨hx, _⟩ => ⟨hx, hx.1⟩, fun ⟨hx, _⟩ => ⟨hx, hV_sub1 ⟨hx.1, hsub hx.2⟩⟩⟩ ⟨?_, ?_⟩
    · rintro ⟨e, he, hxe, hxV⟩
      exact ⟨e, he, hxe, hV_sub2 hxV⟩
    · rintro ⟨e, he, hxe, hxV⟩
      have heS' : e ∈ {e | e ∈ H.E ∧ e ⊆ S'} ∩ H.E :=
        ⟨⟨he.2, he.1.2.trans hsub⟩, he.2⟩
      exact ⟨e, he, hxe, Or.inr (mem_iUnion₂.mpr ⟨e, heS', hxe, hxV⟩)⟩
  exact Drawing.ext_VE hV_eq hE_eq

/-- If `S'` is closed and `subBd S' ∩ U(H) ⊆ V(H)`, every edge of `H` that meets `S'` is contained
in `S'`. -/
theorem edge_subset_of_inter_nonempty {H : Drawing S} {S' e : Set S}
    (hS'_cl : IsClosed S') (hbd : subBd S' ∩ H.U ⊆ H.V) (he : e ∈ H.E)
    (hmeet : (e ∩ S').Nonempty) : e ⊆ S' := by
  obtain ⟨x, hxe, hxS'⟩ := hmeet
  have hdis : Disjoint e (frontier S') := by
    rw [← subBd_eq_frontier]
    refine disjoint_left.mpr fun y hye hybd => ?_
    have hyU : y ∈ H.U := (he.2.1 hye).1
    have hyV : y ∈ H.V := hbd ⟨hybd, hyU⟩
    exact (he.2.1 hye).2 hyV
  exact subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected hS'_cl hdis hxe hxS'

/-- If `S'` is closed and `subBd S' ∩ U(H) ⊆ V(H)`, then `(H.interSet S').V = H.V ∩ S'` and
`(H.interSet S').U = H.U ∩ S'`. -/
theorem interSet_V_and_U [T2Space S] {H : Drawing S} {S' : Set S}
    (hS'_cl : IsClosed S') (hbd : subBd S' ∩ H.U ⊆ H.V) :
    (H.interSet S').V = H.V ∩ S' ∧ (H.interSet S').U = H.U ∩ S' := by
  have hE : (H.interSet S').E = {e | e ∈ H.E ∧ e ⊆ S'} := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have hV : (H.interSet S').V = H.V ∩ S' := by
    apply subset_antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, he, hxe, hxV⟩ := mem_iUnion₂.mp hx
        exact ⟨hxV, hS'_cl.closure_subset_iff.mpr he.1.2 hxe⟩
    · exact fun x hx => Or.inl ⟨hx, hx.1⟩
  refine ⟨hV, subset_antisymm ?_ ?_⟩
  · rw [(H.interSet S').U_eq, hV, hE]
    refine union_subset (fun x hx => ⟨H.V_subset_U hx.1, hx.2⟩) (iUnion₂_subset fun e he x hx => ?_)
    exact ⟨H.closure_subset_U he.1 hx, hS'_cl.closure_subset_iff.mpr he.2 hx⟩
  · rintro x ⟨hxU, hxS'⟩
    by_cases hxV : x ∈ H.V
    · exact (H.interSet S').V_subset_U (hV.symm ▸ ⟨hxV, hxS'⟩)
    · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxU hxV
      have heS' : e ⊆ S' := edge_subset_of_inter_nonempty hS'_cl hbd he ⟨x, hxe, hxS'⟩
      have he' : e ∈ (H.interSet S').E := hE.symm ▸ ⟨he, heS'⟩
      exact (H.interSet S').closure_subset_U he' (subset_closure hxe)

/-- If `S'` is closed and `subBd S' ∩ U(H) ⊆ V(H)`, then for `F ⊆ S'` and `Δ ⊆ S'`, `Δ` is a dial
for `F, H.interSet S'` if and only if `Δ` is a dial for `F, H`. -/
theorem isDial_interSet_iff [T2Space S] {H : Drawing S} {S' F Δ : Set S}
    (hS'_cl : IsClosed S') (hbd : subBd S' ∩ H.U ⊆ H.V) (hF : F ⊆ S') (hΔ : Δ ⊆ S') :
    IsDial (H.interSet S') F Δ ↔ IsDial H F Δ := by
  obtain ⟨hV, hU⟩ := interSet_V_and_U hS'_cl hbd
  have hΔU : Δ ∩ (H.interSet S').U = Δ ∩ H.U := by
    rw [hU]
    ext x
    exact ⟨fun ⟨hxΔ, hxU, _⟩ => ⟨hxΔ, hxU⟩, fun ⟨hxΔ, hxU⟩ => ⟨hxΔ, hxU, hΔ hxΔ⟩⟩
  have hFV : F ∩ (H.interSet S').V = F ∩ H.V := by
    rw [hV]
    ext x
    exact ⟨fun ⟨hxF, hxV, _⟩ => ⟨hxF, hxV⟩, fun ⟨hxF, hxV⟩ => ⟨hxF, hxV, hF hxF⟩⟩
  have hinter : (H.interSet S').interSet Δ = H.interSet Δ :=
    interSet_interSet_of_subset H hΔ
  unfold IsDial
  rw [hΔU, hFV, hinter]

/-! ## 3. Proof of (6.1) (page 33) -/

/-- Graph Minors XIV, (6.1) (page 33):
"Let $H$ be a rigid drawing in a surface $\Sigma$, and let $\Sigma' \subseteq \Sigma$ be a
surface, such that $\text{bd}(\Sigma') \cap U(H) \subseteq V(H)$. Suppose that for every
closed disc $\Delta' \subseteq \Sigma$ with $\Delta' \cap \Sigma' = \text{bd}(\Delta')
\subseteq \text{bd}(\Sigma')$ there is a circuit $C$ of $H$ with $U(C) \subseteq \Delta'$.
Then $H \cap \Sigma'$ is a rigid drawing in $\Sigma'$." -/
theorem theorem_6_1_proof [T2Space S] {H : Drawing S} {S' : Set S}
    (hRig : IsRigid H) (hS'_cl : IsClosed S') (hbd : subBd S' ∩ H.U ⊆ H.V)
    (hSubsurf : ∀ Δ : Set S, IsClosedDisc Δ → subBd Δ ⊆ S' → ¬ (Δ ⊆ S') →
      ∃ Δ' : Set S, IsClosedDisc Δ' ∧ Δ' ⊆ Δ ∧ Δ' ∩ S' = subBd Δ' ∧ subBd Δ' ⊆ subBd S')
    (hCirc : ∀ Δ' : Set S, IsClosedDisc Δ' → Δ' ∩ S' = subBd Δ' → subBd Δ' ⊆ subBd S' →
      ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing H ∧ C.U ⊆ Δ') :
    IsRigidIn (H.interSet S') S' := by
  obtain ⟨hV, hU⟩ := interSet_V_and_U hS'_cl hbd
  intro F hFS' hF_oArc hFU' hFV_card'
  have hFU : F ∩ H.U = F ∩ (H.interSet S').U := by
    rw [hU]
    ext x
    exact ⟨fun ⟨hxF, hxU⟩ => ⟨hxF, hxU, hFS' hxF⟩, fun ⟨hxF, hxU, _⟩ => ⟨hxF, hxU⟩⟩
  have hFV : F ∩ H.V = F ∩ (H.interSet S').V := by
    rw [hV]
    ext x
    exact ⟨fun ⟨hxF, hxV⟩ => ⟨hxF, hxV, hFS' hxF⟩, fun ⟨hxF, hxV, _⟩ => ⟨hxF, hxV⟩⟩
  have hFU_sub : F ∩ H.U ⊆ H.V := by
    rw [hFU]
    exact hFU'.trans (H.spanV_subset _ _)
  have hFV_card : (F ∩ H.V).ncard ≤ 2 := by
    rwa [hFV]
  obtain ⟨Δ, hDial⟩ := hRig F hF_oArc hFU_sub hFV_card
  have hΔ_sub : Δ ⊆ S' := by
    by_contra hnot
    obtain ⟨Δ', hΔ'_disc, hΔ'_sub, hΔ'_inter, hΔ'_bd⟩ :=
      hSubsurf Δ hDial.1 (hDial.2.1 ▸ hFS') hnot
    obtain ⟨C, hC, hCs, hCU⟩ := hCirc Δ' hΔ'_disc hΔ'_inter hΔ'_bd
    exact no_circuit_in_dial hDial hFU_sub hC hCs (hCU.trans hΔ'_sub)
  exact ⟨Δ, hΔ_sub, (isDial_interSet_iff hS'_cl hbd hFS' hΔ_sub).mpr hDial⟩

/-- Helper: `subBd (closure Λ) = subBd Λ` when `Λ` is an open disc whose boundary `subBd Λ` is an
`O`-arc and whose closure `closure Λ` is a closed disc. -/
theorem subBd_closure_eq_subBd_of_isOpenDisc (hS : IsClosedSurface S) {Λ : Set S}
    (hΛ_open : IsOpenDisc Λ) (hΛ_bd : IsOArc (subBd Λ)) (hΛ_cl : IsClosedDisc (closure Λ)) :
    subBd (closure Λ) = subBd Λ := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨Δ₀, ⟨hΔ₀sub, hΔ₀disc, hΔ₀bd, -⟩, -⟩ :=
    disc_oArc (closure Λ) (subBd Λ) hΛ_cl (fun x hx => hx.1) hΛ_bd
  have hΔ₀bd_sub : subBd Δ₀ = subBd Λ := by
    rw [IsClosedDisc.subBd_eq_discBd hS hΔ₀disc, hΔ₀bd]
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hOD₀ : IsOpenDisc (Δ₀ \ subBd Λ) :=
    hΔ₀bd_sub ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₀disc).1
  obtain ⟨φ⟩ := hOD₀.2
  have h0 : (0 : EuclideanPlane) ∈ OpenUnitDisc := by simp [OpenUnitDisc]
  have hp : (φ ⟨0, h0⟩).1 ∈ Δ₀ \ subBd Λ := (φ ⟨0, h0⟩).2
  have hpΛ : (φ ⟨0, h0⟩).1 ∈ Λ := by
    have hp_cl : (φ ⟨0, h0⟩).1 ∈ closure Λ := hΔ₀sub hp.1
    rw [hclL] at hp_cl
    exact hp_cl.resolve_right hp.2
  have hfr₀ : frontier Δ₀ = subBd Λ := by rw [← subBd_eq_frontier, hΔ₀bd_sub]
  have hΛ_sub : Λ ⊆ Δ₀ :=
    subset_of_disjoint_frontier hΛ_open.isPathConnected.isConnected.isPreconnected hΔ₀disc.isClosed
      (hfr₀ ▸ hdisL) hpΛ hp.1
  have h_eq : closure Λ = Δ₀ :=
    subset_antisymm (hΔ₀disc.isClosed.closure_subset_iff.mpr hΛ_sub) hΔ₀sub
  rw [h_eq, hΔ₀bd_sub]

/-- Subsurface disc property for `S' = univ \ Λ`, where `Λ` is an open disc whose boundary is an
`O`-arc and whose closure is a closed disc. -/
theorem subsurf_compl_openDisc (hS : IsClosedSurface S) {Λ Δ : Set S}
    (hΛ_open : IsOpenDisc Λ) (hΛ_bd : IsOArc (subBd Λ)) (hΛ_cl : IsClosedDisc (closure Λ))
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ ⊆ univ \ Λ) (hnot : ¬ (Δ ⊆ univ \ Λ)) :
    ∃ Δ' : Set S, IsClosedDisc Δ' ∧ Δ' ⊆ Δ ∧
      Δ' ∩ (univ \ Λ) = subBd Δ' ∧ subBd Δ' ⊆ subBd (univ \ Λ) := by
  have : T2Space S := hS.2.1
  have hmeet : (Λ ∩ Δ).Nonempty := by
    by_contra h
    apply hnot
    intro x hx
    exact ⟨mem_univ x, fun hxΛ => h ⟨x, hxΛ, hx⟩⟩
  obtain ⟨x, hxΛ, hxΔ⟩ := hmeet
  have hdis : Disjoint Λ (frontier Δ) := by
    rw [← subBd_eq_frontier]
    exact disjoint_left.mpr fun y hyΛ hybd => (hbd hybd).2 hyΛ
  have hΛ_sub : Λ ⊆ Δ :=
    subset_of_disjoint_frontier hΛ_open.isPathConnected.isConnected.isPreconnected
      hΔ.isClosed hdis hxΛ hxΔ
  have hcl_sub : closure Λ ⊆ Δ := hΔ.isClosed.closure_subset_iff.mpr hΛ_sub
  obtain ⟨hdis_bd, hcl_eq⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hbd_cl : subBd (closure Λ) = subBd Λ :=
    subBd_closure_eq_subBd_of_isOpenDisc hS hΛ_open hΛ_bd hΛ_cl
  refine ⟨closure Λ, hΛ_cl, hcl_sub, ?_, ?_⟩
  · rw [hbd_cl, hcl_eq]
    ext y
    simp only [mem_inter_iff, mem_union, mem_sdiff, mem_univ, true_and]
    exact ⟨fun ⟨h, hyn⟩ => h.resolve_left hyn,
      fun hy => ⟨Or.inr hy, disjoint_right.mp hdis_bd hy⟩⟩
  · rw [hbd_cl, subBd_eq_frontier, subBd_eq_frontier, ← compl_eq_univ_sdiff, frontier_compl]

/-- Subsurface disc property for `S' = Δ₀`, where `Δ₀` is a closed disc in a connected closed
surface `S`. -/
theorem subsurf_closedDisc [ConnectedSpace S] (hS : IsClosedSurface S) {Δ₀ Δ : Set S}
    (hΔ₀ : IsClosedDisc Δ₀) (hΔ : IsClosedDisc Δ)
    (hbd : subBd Δ ⊆ Δ₀) (hnot : ¬ (Δ ⊆ Δ₀)) :
    ∃ Δ' : Set S, IsClosedDisc Δ' ∧ Δ' ⊆ Δ ∧
      Δ' ∩ Δ₀ = subBd Δ' ∧ subBd Δ' ⊆ subBd Δ₀ := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hF_oArc : IsOArc (subBd Δ) := by
    rw [IsClosedDisc.subBd_eq_discBd hS hΔ]
    exact hΔ.isOArc_discBd
  obtain ⟨Δ₁, ⟨hΔ₁_sub, hΔ₁_disc, hΔ₁_bd, -⟩, -⟩ := disc_oArc Δ₀ (subBd Δ) hΔ₀ hbd hF_oArc
  have hΔ_bd : discBd Δ = subBd Δ := (IsClosedDisc.subBd_eq_discBd hS hΔ).symm
  have hb_eq : discBd Δ = discBd Δ₁ := hΔ_bd.trans hΔ₁_bd.symm
  have hne : Δ ≠ Δ₁ := fun h => hnot (h ▸ hΔ₁_sub)
  have hcov : Δ ∪ Δ₁ = univ := cover_of_discBd_eq hS hΔ hΔ₁_disc hb_eq hne
  have hsph : IsSphere S := by
    by_contra hns
    exact hne (eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns hΔ hΔ₁_disc hb_eq)
  obtain ⟨D₁, D₂, hne_D, hD₁, hD₂, hb₁, hb₂, hcov_D, hmeet_D, _, huniq_D⟩ :=
    sphere_disc S hsph (discBd Δ₀) hΔ₀.isOArc_discBd
  have haux : ∀ D' : Set S, IsClosedDisc D' → discBd D' = discBd Δ₀ →
      Δ₀ ∪ D' = univ → Δ₀ ∩ D' = discBd Δ₀ →
      IsClosedDisc D' ∧ D' ⊆ Δ ∧ D' ∩ Δ₀ = subBd D' ∧ subBd D' ⊆ subBd Δ₀ := by
    intro D' hD' hb' hcov' hmeet'
    have hbd_D' : subBd D' = discBd Δ₀ :=
      (IsClosedDisc.subBd_eq_discBd hS hD').trans hb'
    have hbd_Δ₀ : subBd Δ₀ = discBd Δ₀ :=
      IsClosedDisc.subBd_eq_discBd hS hΔ₀
    obtain ⟨_, hcl_D', _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hD'
    have hdiff_sub : D' \ subBd D' ⊆ Δ := by
      intro x ⟨hxD', hxb⟩
      rw [hbd_D'] at hxb
      have hx_not_0 : x ∉ Δ₀ := fun hx0 => hxb (hmeet' ▸ ⟨hx0, hxD'⟩)
      have hx_not_1 : x ∉ Δ₁ := fun hx1 => hx_not_0 (hΔ₁_sub hx1)
      have hx_univ : x ∈ Δ ∪ Δ₁ := hcov.symm ▸ mem_univ x
      exact hx_univ.resolve_right hx_not_1
    have hD'_sub : D' ⊆ Δ := hcl_D' ▸ hΔ.isClosed.closure_subset_iff.mpr hdiff_sub
    refine ⟨hD', hD'_sub, ?_, ?_⟩
    · rw [inter_comm, hmeet', hbd_D']
    · rw [hbd_D', hbd_Δ₀]
  rcases huniq_D Δ₀ hΔ₀ rfl with rfl | rfl
  · exact ⟨D₂, haux D₂ hD₂ hb₂ hcov_D hmeet_D⟩
  · refine ⟨D₁, haux D₁ hD₁ hb₁ (union_comm D₁ Δ₀ ▸ hcov_D) (inter_comm D₁ Δ₀ ▸ hmeet_D)⟩

/-! ## 4. Proof of (6.2) (page 33) -/

/-- Graph Minors XIV, (6.2), Part 1 (page 33), in a subset `S' ⊆ Σ`:
at any vertex `v ∈ V(H) ∩ S'` of a drawing `H` that is rigid in `S'`, if `ρ k ⊆ S'`, then no other
corner `k' ≠ k` at `v` has `ρ k' = ρ k`. -/
theorem corner_regions_ne_in [T2Space S] (hS : IsClosedSurface S) {H : Drawing S} {S' : Set S}
    (hRig : IsRigidIn H S') {γ : Set S → I → S} {v : S} (hv : v ∈ H.V) (hvS' : v ∈ S')
    {next : halfEdges H γ v → halfEdges H γ v}
    {ρ P Q : halfEdges H γ v → Set S} {W : Set S} {τ : halfEdges H γ v → I}
    (hsec : IsSectors H γ v next ρ P W Q τ)
    {k k' : halfEdges H γ v} (hρ_sub : ρ k ⊆ S') (hkk : k ≠ k') :
    ρ k ≠ ρ k' := by
  refine GM11.corner_regions_ne_of_free_disc hS (H.V_subset_U hv) hsec hkk ?_
  intro J hJ hvJ hJp
  have hpR : ρ k ∈ H.R := IsCorners.region (IsSectors.corners hsec) k
  have hJS' : J ⊆ S' := fun y hy => (hJp y hy).elim (fun h => h ▸ hvS') (fun h => hρ_sub h)
  have hJU : J ∩ H.U ⊆ {v} := by
    rintro y ⟨hyJ, hyU⟩
    rcases hJp y hyJ with rfl | hyr
    · rfl
    · exact (region_subset hpR hyr hyU).elim
  have hJV : J ∩ H.V = {v} := by
    apply subset_antisymm
    · exact fun y ⟨hyJ, hyV⟩ => hJU ⟨hyJ, H.V_subset_U hyV⟩
    · rintro y rfl
      exact ⟨hvJ, hv⟩
  have hJU_sub : J ∩ H.U ⊆ H.V := hJU.trans (singleton_subset_iff.mpr hv)
  have hJV_card : (J ∩ H.V).ncard ≤ 2 := by
    rw [hJV, ncard_singleton]
    omega
  obtain ⟨Δ, _, hΔ, hbd_Δ, hDial_cases⟩ := hRig J hJS' hJ hJU_sub hJV_card
  have hb : discBd Δ = J := (IsClosedDisc.subBd_eq_discBd hS hΔ).symm.trans hbd_Δ
  have hfree : Disjoint (Δ \ discBd Δ) H.U := by
    rcases hDial_cases with h1 | ⟨u₁, u₂, hu12, hJV_eq, _⟩
    · exact disjoint_left.mpr fun y ⟨hyΔ, hyb⟩ hyU => hyb (hb ▸ h1 ⟨hyΔ, hyU⟩)
    · exfalso
      have h1 : (J ∩ H.V).ncard = 1 := by rw [hJV, ncard_singleton]
      have h2 : (J ∩ H.V).ncard = 2 := by rw [hJV_eq, ncard_pair hu12]
      omega
  exact ⟨Δ, hΔ, hb, hfree⟩

/-- Graph Minors XIV, (6.2), Part 1 (page 33):
"Let $H$ be a rigid drawing in a surface $\Sigma$. Let $v \in V(H)$, and let the regions of
$H$ incident with $v$ be $r_1, \dots, r_k$, enumerated in the cyclic order of their
occurrence around $v$. Then $r_1, \dots, r_k$ are all distinct." -/
theorem corner_regions_injective [T2Space S] (hS : IsClosedSurface S) {H : Drawing S}
    (hRig : IsRigid H) {γ : Set S → I → S} {v : S} (hv : v ∈ H.V)
    {next : halfEdges H γ v → halfEdges H γ v}
    {ρ P Q : halfEdges H γ v → Set S} {W : Set S} {τ : halfEdges H γ v → I}
    (hsec : IsSectors H γ v next ρ P W Q τ) :
    Function.Injective ρ := by
  intro k k' hρ
  by_contra hkk
  exact corner_regions_ne_in hS (isRigidIn_univ_iff.mpr hRig) hv (mem_univ v) hsec
    (subset_univ (ρ k)) hkk hρ

/-- Every region `r` of a drawing `H` that is rigid in `S'` (with `r ⊆ S'`) is simply-connected in
the sense of Section 6 (`IsArcSimplyConnected r`). -/
theorem isArcSimplyConnected_region_in [T2Space S] (hS : IsClosedSurface S) {H : Drawing S}
    {S' r : Set S} (hRig : IsRigidIn H S') (hr : r ∈ H.R) (hr_sub : r ⊆ S') :
    IsArcSimplyConnected r := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨y₀, hy₀⟩ := region_nonempty hr
  have hpath : IsPathConnected r :=
    isPathConnected_of_isOpen hS (region_isOpen hr) (region_isPreconnected hr) ⟨y₀, hy₀⟩
  have harc : IsArcConnected r := by
    intro a ha b hb hab
    obtain ⟨m, hm⟩ := hpath.joinedIn a ha b hb
    obtain ⟨e, he, hi, he0, he1, hsub⟩ :=
      exists_arc_of_path (γ := m) m.continuous (by simpa using hab)
    have he0' : e 0 = a := by simpa using he0
    have he1' : e 1 = b := by simpa using he1
    exact ⟨range e, hsub.trans (range_subset_iff.mpr hm), he0' ▸ he1' ▸ isLine_range he hi⟩
  refine ⟨harc, fun F hF hFr => ?_⟩
  have hFS' : F ⊆ S' := hFr.trans hr_sub
  have hFU_emp : F ∩ H.U = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hxU⟩ => region_subset hr (hFr hxF) hxU
  have hFU : F ∩ H.U ⊆ H.V := by
    rw [hFU_emp]
    exact empty_subset _
  have hFV_emp : F ∩ H.V = ∅ :=
    eq_empty_of_subset (inter_subset_inter_right F H.V_subset_U) hFU_emp
  have hFV_card : (F ∩ H.V).ncard ≤ 2 := by
    rw [hFV_emp, ncard_empty]
    omega
  obtain ⟨Δ, _, hΔ, hbd_Δ, hDial_cases⟩ := hRig F hFS' hF hFU hFV_card
  have hΔ_disj : Disjoint Δ H.U := by
    rcases hDial_cases with h1 | ⟨u₁, u₂, hu12, hJV_eq, _⟩
    · exact disjoint_left.mpr fun x hxΔ hxU =>
        (eq_empty_iff_forall_notMem.mp hFU_emp x) ⟨h1 ⟨hxΔ, hxU⟩, hxU⟩
    · exfalso
      have h1 : (F ∩ H.V).ncard = 0 := by rw [hFV_emp, ncard_empty]
      have h2 : (F ∩ H.V).ncard = 2 := by rw [hJV_eq, ncard_pair hu12]
      omega
  obtain ⟨φ⟩ := hF
  have hpF : (φ 1).1 ∈ F := (φ 1).2
  have hpΔ : (φ 1).1 ∈ Δ := by
    have hbd_disc : discBd Δ = F := (IsClosedDisc.subBd_eq_discBd hS hΔ).symm.trans hbd_Δ
    exact Surface.discBd_subset Δ (hbd_disc.symm ▸ hpF)
  have hΔ_r : Δ ⊆ r :=
    subset_region hr hΔ.isPathConnected.isConnected.isPreconnected hΔ_disj hpΔ (hFr hpF)
  exact ⟨Δ, hΔ, hbd_Δ, hΔ_r⟩

/-- Every region `r` of a rigid drawing `H` is simply-connected (`IsArcSimplyConnected r`). -/
theorem isArcSimplyConnected_region [T2Space S] (hS : IsClosedSurface S) {H : Drawing S}
    (hRig : IsRigid H) {r : Set S} (hr : r ∈ H.R) :
    IsArcSimplyConnected r :=
  isArcSimplyConnected_region_in hS (isRigidIn_univ_iff.mpr hRig) hr (subset_univ r)

/-- Every region `r` of a rigid drawing `H` with `U(H) ≠ ∅` in a connected closed surface `S` is an
open disc (`IsOpenDisc r`), so `H` is a 2-cell drawing. -/
theorem isOpenDisc_region_of_isRigid [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {H : Drawing S} (hRig : IsRigid H) (hU : H.U.Nonempty) {r : Set S} (hr : r ∈ H.R) :
    IsOpenDisc r := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hsc := isArcSimplyConnected_region hS hRig hr
  have h_od := open_disc S r hS ‹ConnectedSpace S›
    ⟨region_nonempty hr, region_isPreconnected hr⟩ (region_isOpen hr)
    (fun F hFr hF => by
      obtain ⟨Δ, hΔ, hbd, hΔr⟩ := hsc.2 F hF hFr
      exact ⟨Δ, hΔr, hΔ, (IsClosedDisc.subBd_eq_discBd hS hΔ).symm.trans hbd⟩)
  rcases h_od with ⟨_, hr_univ⟩ | hr_disc
  · exfalso
    obtain ⟨x, hx⟩ := hU
    exact region_subset hr (hr_univ ▸ mem_univ x) hx
  · exact hr_disc

/-- Graph Minors XIV, (6.2) (page 33):
"Let $H$ be a rigid drawing in a surface $\Sigma$. Let $v \in V(H)$, and let the regions of
$H$ incident with $v$ be $r_1, \dots, r_k$, enumerated in the cyclic order of their
occurrence around $v$. Then $r_1, \dots, r_k$ are all distinct. Consequently $\bar{r}$ is
simply-connected for every region $r$ of $H$." -/
theorem theorem_6_2_proof [T2Space S] (hS : IsClosedSurface S) {H : Drawing S} (hRig : IsRigid H) :
    (∀ {γ : Set S → I → S} {v : S}, v ∈ H.V →
      ∀ {next : halfEdges H γ v → halfEdges H γ v}
        {ρ P Q : halfEdges H γ v → Set S} {W : Set S} {τ : halfEdges H γ v → I},
        IsSectors H γ v next ρ P W Q τ → Function.Injective ρ) ∧
    (∀ r ∈ H.R, IsArcSimplyConnected r) := by
  refine ⟨?_, ?_⟩
  · intro γ v hv next ρ P Q W τ hsec
    exact corner_regions_injective hS hRig hv hsec
  · intro r hr
    exact isArcSimplyConnected_region hS hRig hr

end GraphMinor.GM14
