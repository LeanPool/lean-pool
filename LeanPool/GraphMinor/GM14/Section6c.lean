/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section6b
import LeanPool.GraphMinor.GM14.Section7a
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Graph Minors XIV, Section 6 (Part 3): Rigidity after Clearing a Zone (`(6.3)`)

This file proves `(6.3)` (`theorem_6_3`, pages 33–34) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50:
if `H` is a rigid drawing in a closed surface `Σ`, `Λ ⊆ Σ` is an open disc bounded by the point set
of a circuit `C` of `H`, and `closure r ∩ closure Λ` is preconnected for every region `r` of `H`
disjoint from `Λ`, then `H ∩ (Σ - Λ)` is a rigid drawing in `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph Hypergraph unitInterval
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

local notation "𝕀" => unitInterval

/-! ## 1. Splitting an `O`-Arc Across `bd(Λ)` -/

/-- Every line is contained in the closure of its interior. -/
theorem IsLineWithEnds.subset_closure_sdiff_pair {L : Set S} {a b : S}
    (h : IsLineWithEnds L a b) : L ⊆ closure (L \ {a, b}) := by
  obtain ⟨f, hf0, hf1⟩ := h
  intro x hxL
  rw [mem_closure_iff]
  intro U hU hxU
  let t : 𝕀 := f.symm ⟨x, hxL⟩
  have ht : (f t).1 = x := congrArg Subtype.val (f.apply_symm_apply ⟨x, hxL⟩)
  have hcont : Continuous (fun s : 𝕀 => (f s).1) := continuous_subtype_val.comp f.continuous
  have hOpen_pre : IsOpen ((fun s : 𝕀 => (f s).1) ⁻¹' U) := hU.preimage hcont
  have ht_pre : t ∈ (fun s : 𝕀 => (f s).1) ⁻¹' U := by simp [ht, hxU]
  obtain ⟨V, hV_open, hV_eq⟩ := isOpen_induced_iff.mp hOpen_pre
  have htV : t.1 ∈ V := by
    have : t ∈ Subtype.val ⁻¹' V := hV_eq ▸ ht_pre
    exact this
  have ht_cl : t.1 ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (zero_ne_one' ℝ)]
    exact t.2
  obtain ⟨r, hrV, hr_Ioo⟩ := mem_closure_iff.mp ht_cl V hV_open htV
  let s : 𝕀 := ⟨r, hr_Ioo.1.le, hr_Ioo.2.le⟩
  have hs_pre : s ∈ (fun s : 𝕀 => (f s).1) ⁻¹' U := hV_eq ▸ hrV
  refine ⟨(f s).1, hs_pre, (f s).2, ?_⟩
  rintro (h1 | h2)
  · have : s = 0 := f.injective (Subtype.ext (h1.trans hf0.symm))
    exact hr_Ioo.1.ne (congrArg Subtype.val this).symm
  · have : s = 1 := f.injective (Subtype.ext (h2.trans hf1.symm))
    exact hr_Ioo.2.ne (congrArg Subtype.val this)

/-- The interior of a line is nonempty. -/
theorem IsLineWithEnds.nonempty_sdiff_pair {L : Set S} {a b : S}
    (h : IsLineWithEnds L a b) : (L \ {a, b}).Nonempty := by
  obtain ⟨f, hf0, hf1⟩ := h
  let mid : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
  refine ⟨(f mid).1, (f mid).2, ?_⟩
  rintro (h1 | h2)
  · have : mid = 0 := f.injective (Subtype.ext (h1.trans hf0.symm))
    exact absurd (congrArg Subtype.val this) (by norm_num [mid])
  · have : mid = 1 := f.injective (Subtype.ext (h2.trans hf1.symm))
    exact absurd (congrArg Subtype.val this) (by norm_num [mid])

/-- An `O`-arc `F` that meets both `Λ` and `Σ \ closure Λ` meets `subBd Λ` in at least two points.
-/
private theorem two_le_ncard_inter_subBd (hS : IsClosedSurface S) {F Λ : Set S}
    (hF : IsOArc F) (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hO_bd : IsOArc (subBd Λ)) (hF_in : (F ∩ Λ).Nonempty) (hF_out : (F \ closure Λ).Nonempty)
    (hfin : (F ∩ subBd Λ).Finite) : 2 ≤ (F ∩ subBd Λ).ncard := by
  by_contra hlt
  have hle1 : (F ∩ subBd Λ).ncard ≤ 1 := Nat.lt_succ_iff.mp (not_le.mp hlt)
  obtain ⟨x₁, hx₁F, hx₁Λ⟩ := hF_in
  obtain ⟨x₂, hx₂F, hx₂_out⟩ := hF_out
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hfr_cl : frontier (closure Λ) = subBd Λ := by
    rw [← subBd_eq_frontier, subBd_closure_eq_subBd_of_isOpenDisc hS hΛ_open hO_bd hΛ_cl]
  by_cases hne : (F ∩ subBd Λ).Nonempty
  · obtain ⟨z, hz⟩ := hne
    have hsub_z : F ∩ subBd Λ ⊆ {z} := fun w hw =>
      mem_singleton_iff.mpr ((Set.ncard_le_one_iff hfin).mp hle1 hw hz)
    have hz_bd : z ∈ subBd Λ := hz.2
    have hpre : IsPreconnected (F \ {z}) :=
      (isPathConnected_oArc_diff hF hz.1).isConnected.isPreconnected
    have hdis_fr : Disjoint (F \ {z}) (frontier (closure Λ)) := by
      rw [hfr_cl]
      exact disjoint_left.mpr fun w hw hw_bd => hw.2 (hsub_z ⟨hw.1, hw_bd⟩)
    have hx₁_ne : x₁ ≠ z := fun h => disjoint_left.mp hdisL hx₁Λ (h ▸ hz_bd)
    have hx₂_ne : x₂ ≠ z := fun h => hx₂_out (h ▸ hz_bd.1)
    rcases subset_or_disjoint_of_frontier isClosed_closure hpre hdis_fr with hsub | hdis
    · exact hx₂_out (hsub ⟨hx₂F, hx₂_ne⟩)
    · exact disjoint_left.mp hdis ⟨hx₁F, hx₁_ne⟩ (subset_closure hx₁Λ)
  · have h_empty : F ∩ subBd Λ = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hdis_fr : Disjoint F (frontier (closure Λ)) := by
      rw [hfr_cl, disjoint_iff_inter_eq_empty]
      exact h_empty
    obtain ⟨φ⟩ := hF
    have hF_pre : IsPreconnected F := by
      have hEq : F = (fun w : Circle => (φ w).1) '' univ := by
        ext x
        exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, trivial, by simp⟩, fun ⟨w, _, hw⟩ => hw ▸ (φ w).2⟩
      rw [hEq]
      exact isPreconnected_univ.image _ (continuous_subtype_val.comp φ.continuous).continuousOn
    rcases subset_or_disjoint_of_frontier isClosed_closure hF_pre hdis_fr with hsub | hdis
    · exact hx₂_out (hsub hx₂F)
    · exact disjoint_left.mp hdis hx₁F (subset_closure hx₁Λ)

/-- If an `O`-arc `F` with `F ∩ H'.U ⊆ H'.V` and `(F ∩ H'.V).ncard ≤ 2` meets both `Λ` and
`Σ \ closure Λ`, then `F ∩ H'.V = {v₁, v₂}` for two distinct vertices `v₁, v₂ ∈ C.V`, and `F` splits
into two lines `F₁, F₂` between `v₁` and `v₂` with `F₁ ⊆ closure Λ` and `F₂ \ {v₁, v₂} ⊆ r` for a
region `r ∈ H'.R` disjoint from `Λ`. -/
private theorem split_oArc_across_openDisc [T2Space S] (hS : IsClosedSurface S)
    {H H' C : Drawing S} {Λ F : Set S}
    (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hC : C.IsCircuit) (hC_sub' : C.IsSubdrawing H') (hbd : subBd Λ = C.U)
    (_hΛ_R : Λ ∈ H'.R) (hR'_other : ∀ r ∈ H'.R, r ≠ Λ → r ∈ H.R ∧ Disjoint r Λ)
    (hF : IsOArc F) (hFU : F ∩ H'.U ⊆ H'.V) (hFV : (F ∩ H'.V).ncard ≤ 2)
    (hF_in : (F ∩ Λ).Nonempty) (hF_out : (F \ closure Λ).Nonempty) :
    ∃ (v₁ v₂ : S) (F₁ F₂ r : Set S),
      v₁ ≠ v₂ ∧ v₁ ∈ C.V ∧ v₂ ∈ C.V ∧
      F ∩ H'.V = {v₁, v₂} ∧ F ∩ H'.U = {v₁, v₂} ∧ F ∩ subBd Λ = {v₁, v₂} ∧
      IsLineWithEnds F₁ v₁ v₂ ∧ IsLineWithEnds F₂ v₁ v₂ ∧
      F = F₁ ∪ F₂ ∧ F₁ ∩ F₂ = {v₁, v₂} ∧
      F₁ ⊆ closure Λ ∧ F₁ \ {v₁, v₂} ⊆ Λ ∧
      r ∈ H'.R ∧ r ∈ H.R ∧ Disjoint r Λ ∧ r ⊆ univ \ Λ ∧
      F₂ \ {v₁, v₂} ⊆ r ∧ v₁ ∈ closure r ∧ v₂ ∈ closure r := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hO_bd : IsOArc (subBd Λ) := hbd ▸ isOArc_of_isCircuit hC
  have hbd_sub_U' : subBd Λ ⊆ H'.U := hbd ▸ hC_sub'.U_subset
  have hsub1 : F ∩ subBd Λ ⊆ F ∩ H'.U := inter_subset_inter_right F hbd_sub_U'
  have hsub2 : F ∩ H'.U ⊆ F ∩ H'.V := fun x hx => ⟨hx.1, hFU hx⟩
  have hfin_FV : (F ∩ H'.V).Finite := H'.finite_V.subset inter_subset_right
  have hfin_FU : (F ∩ H'.U).Finite := hfin_FV.subset hsub2
  have hfin_Fbd : (F ∩ subBd Λ).Finite := hfin_FU.subset hsub1
  have h2_le : 2 ≤ (F ∩ subBd Λ).ncard :=
    two_le_ncard_inter_subBd hS hF hΛ_open hΛ_cl hO_bd hF_in hF_out hfin_Fbd
  have h_eq_bd_V : F ∩ subBd Λ = F ∩ H'.V :=
    eq_of_subset_of_ncard_le (hsub1.trans hsub2) (hFV.trans h2_le) hfin_FV
  have h_eq_U_V : F ∩ H'.U = F ∩ H'.V :=
    eq_of_subset_of_ncard_le hsub2
      (hFV.trans (h2_le.trans (ncard_le_ncard hsub1 hfin_FU))) hfin_FV
  have h_card2 : (F ∩ H'.V).ncard = 2 :=
    le_antisymm hFV (h_eq_bd_V ▸ h2_le)
  obtain ⟨v₁, v₂, hv12, hFV_eq⟩ := ncard_eq_two.mp h_card2
  have hFU_eq : F ∩ H'.U = {v₁, v₂} := h_eq_U_V.trans hFV_eq
  have hFbd_eq : F ∩ subBd Λ = {v₁, v₂} := h_eq_bd_V.trans hFV_eq
  have hv₁_mem : v₁ ∈ F ∩ subBd Λ := by rw [hFbd_eq]; exact mem_insert v₁ {v₂}
  have hv₂_mem : v₂ ∈ F ∩ subBd Λ := by rw [hFbd_eq]; exact mem_insert_of_mem v₁ rfl
  have hv₁_V' : v₁ ∈ H'.V := by
    have : v₁ ∈ F ∩ H'.V := by rw [hFV_eq]; exact mem_insert v₁ {v₂}
    exact this.2
  have hv₂_V' : v₂ ∈ H'.V := by
    have : v₂ ∈ F ∩ H'.V := by rw [hFV_eq]; exact mem_insert_of_mem v₁ rfl
    exact this.2
  have hv_CV : ∀ v, v ∈ subBd Λ → v ∈ H'.V → v ∈ C.V := by
    intro v hv_bd hv_V
    by_contra hv_not_CV
    obtain ⟨e, heC, hve⟩ := C.exists_edge_of_mem (hbd ▸ hv_bd) hv_not_CV
    exact ((hC_sub'.2 heC).2.1 hve).2 hv_V
  have hv₁C : v₁ ∈ C.V := hv_CV v₁ hv₁_mem.2 hv₁_V'
  have hv₂C : v₂ ∈ C.V := hv_CV v₂ hv₂_mem.2 hv₂_V'
  obtain ⟨a, b, hab, ha0, ha1, hun⟩ := IsOArc.exists_arcs hF hv₁_mem.1 hv₂_mem.1 hv12
  have hb0 : b 0 = v₁ := hab.zero.trans ha0
  have hb1 : b 1 = v₂ := hab.one.trans ha1
  have ha_line : IsLineWithEnds (range a) v₁ v₂ := ha0 ▸ ha1 ▸ hab.arc_left.isLineWithEnds
  have hb_line : IsLineWithEnds (range b) v₁ v₂ := hb0 ▸ hb1 ▸ hab.arc_right.isLineWithEnds
  have hab_inter : range a ∩ range b = {v₁, v₂} := by
    apply subset_antisymm
    · rintro x ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
      rcases hab.meet s t hst.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl ha0
      · exact Or.inr ha1
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, ha0⟩, ⟨0, hb0⟩⟩
      · exact ⟨⟨1, ha1⟩, ⟨1, hb1⟩⟩
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hfr_cl : frontier (closure Λ) = subBd Λ := by
    rw [← subBd_eq_frontier, subBd_closure_eq_subBd_of_isOpenDisc hS hΛ_open hO_bd hΛ_cl]
  have h_arc_side : ∀ L' : Set S, IsLineWithEnds L' v₁ v₂ → L' ⊆ F →
      (L' \ {v₁, v₂} ⊆ Λ ∧ L' ⊆ closure Λ) ∨ Disjoint (L' \ {v₁, v₂}) (closure Λ) := by
    intro L' hL' hL'F
    have hdis_fr : Disjoint (L' \ {v₁, v₂}) (frontier (closure Λ)) := by
      rw [hfr_cl]
      refine disjoint_left.mpr fun x hx hx_bd => hx.2 ?_
      exact hFbd_eq ▸ ⟨hL'F hx.1, hx_bd⟩
    rcases subset_or_disjoint_of_frontier isClosed_closure
        (IsLineWithEnds.isPreconnected_sdiff_pair hL') hdis_fr with hsub | hdis
    · left
      have hsub_Λ : L' \ {v₁, v₂} ⊆ Λ := by
        intro x hx
        have hx_cl : x ∈ Λ ∪ subBd Λ := hclL ▸ hsub hx
        exact hx_cl.resolve_right fun hx_bd => hx.2 (hFbd_eq ▸ ⟨hL'F hx.1, hx_bd⟩)
      refine ⟨hsub_Λ, fun x hx => ?_⟩
      by_cases hx12 : x ∈ ({v₁, v₂} : Set S)
      · rcases hx12 with rfl | rfl
        · exact hv₁_mem.2.1
        · exact hv₂_mem.2.1
      · exact subset_closure (hsub_Λ ⟨hx, hx12⟩)
    · exact Or.inr hdis
  obtain ⟨x₁, hx₁F, hx₁Λ⟩ := hF_in
  obtain ⟨x₂, hx₂F, hx₂_out⟩ := hF_out
  have hx₁_not12 : x₁ ∉ ({v₁, v₂} : Set S) := by
    rintro (rfl | rfl)
    · exact disjoint_left.mp hdisL hx₁Λ hv₁_mem.2
    · exact disjoint_left.mp hdisL hx₁Λ hv₂_mem.2
  have hx₂_not12 : x₂ ∉ ({v₁, v₂} : Set S) := by
    rintro (rfl | rfl)
    · exact hx₂_out hv₁_mem.2.1
    · exact hx₂_out hv₂_mem.2.1
  have hF₁₂_exists : ∃ F₁ F₂ : Set S,
      IsLineWithEnds F₁ v₁ v₂ ∧ IsLineWithEnds F₂ v₁ v₂ ∧
      F = F₁ ∪ F₂ ∧ F₁ ∩ F₂ = {v₁, v₂} ∧
      F₁ ⊆ closure Λ ∧ F₁ \ {v₁, v₂} ⊆ Λ ∧ Disjoint (F₂ \ {v₁, v₂}) (closure Λ) := by
    have ha_F : range a ⊆ F := hun ▸ subset_union_left
    have hb_F : range b ⊆ F := hun ▸ subset_union_right
    rcases h_arc_side (range a) ha_line ha_F with ⟨ha_in, ha_cl⟩ | ha_out
    · rcases h_arc_side (range b) hb_line hb_F with ⟨_, hb_cl⟩ | hb_out
      · exfalso
        have : F ⊆ closure Λ := hun ▸ union_subset ha_cl hb_cl
        exact hx₂_out (this hx₂F)
      · exact ⟨range a, range b, ha_line, hb_line, hun.symm, hab_inter, ha_cl, ha_in, hb_out⟩
    · rcases h_arc_side (range b) hb_line hb_F with ⟨hb_in, hb_cl⟩ | hb_out
      · exact ⟨range b, range a, hb_line, ha_line, by rw [Set.union_comm, hun],
          by rw [Set.inter_comm, hab_inter], hb_cl, hb_in, ha_out⟩
      · exfalso
        rcases hun ▸ hx₁F with hx₁a | hx₁b
        · exact disjoint_left.mp ha_out ⟨hx₁a, hx₁_not12⟩ (subset_closure hx₁Λ)
        · exact disjoint_left.mp hb_out ⟨hx₁b, hx₁_not12⟩ (subset_closure hx₁Λ)
  obtain ⟨F₁, F₂, hF₁_line, hF₂_line, hF_union, hF12_inter, hF₁_cl, hF₁_Λ, hF₂_dis⟩ :=
    hF₁₂_exists
  have hF₂_sub_F : F₂ ⊆ F := hF_union ▸ subset_union_right
  have hF₂_dis_U' : Disjoint (F₂ \ {v₁, v₂}) H'.U := by
    refine disjoint_left.mpr fun x hx hxU' => hx.2 ?_
    exact hFU_eq ▸ ⟨hF₂_sub_F hx.1, hxU'⟩
  obtain ⟨p₂, hp₂⟩ := IsLineWithEnds.nonempty_sdiff_pair hF₂_line
  have hp₂_not_U' : p₂ ∉ H'.U := disjoint_left.mp hF₂_dis_U' hp₂
  obtain ⟨r, hr_R', hp₂_r⟩ := exists_region_of_notMem hp₂_not_U'
  have hF₂_r : F₂ \ {v₁, v₂} ⊆ r :=
    subset_region hr_R' (IsLineWithEnds.isPreconnected_sdiff_pair hF₂_line) hF₂_dis_U' hp₂ hp₂_r
  have hr_ne_Λ : r ≠ Λ := by
    intro hrΛ
    exact disjoint_left.mp hF₂_dis hp₂ (subset_closure (hrΛ ▸ hp₂_r))
  obtain ⟨hr_H, hdis_rΛ⟩ := hR'_other r hr_R' hr_ne_Λ
  have hr_sub : r ⊆ univ \ Λ := fun x hxr => ⟨mem_univ x, disjoint_left.mp hdis_rΛ hxr⟩
  obtain ⟨hv₁F₂, hv₂F₂⟩ := IsLineWithEnds.ends_mem hF₂_line
  have hv₁_cl_r : v₁ ∈ closure r :=
    closure_mono hF₂_r (IsLineWithEnds.subset_closure_sdiff_pair hF₂_line hv₁F₂)
  have hv₂_cl_r : v₂ ∈ closure r :=
    closure_mono hF₂_r (IsLineWithEnds.subset_closure_sdiff_pair hF₂_line hv₂F₂)
  exact ⟨v₁, v₂, F₁, F₂, r, hv12, hv₁C, hv₂C, hFV_eq, hFU_eq, hFbd_eq,
    hF₁_line, hF₂_line, hF_union, hF12_inter, hF₁_cl, hF₁_Λ,
    hr_R', hr_H, hdis_rΛ, hr_sub, hF₂_r, hv₁_cl_r, hv₂_cl_r⟩

/-! ## 2. Proof of (6.3) -/

/-- Criterion for `IsRigid (clearedSubdrawing H Λ)` in terms of circuit arcs between any two
vertices `v₁ ≠ v₂ ∈ C.V` joined by an interior arc `F₂ \ {v₁, v₂} ⊆ r` of a region `r ∈ H.R`
disjoint from `Λ`. -/
theorem isRigid_clearedSubdrawing_of_arc_subset [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H C : Drawing S} {Λ : Set S}
    (hRig : IsRigid H) (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hbd : subBd Λ = C.U)
    (harc : ∀ (r : Set S) (v₁ v₂ : S) (F₂ : Set S) (P₁ P₂ : Drawing S),
      r ∈ H.R → Disjoint r Λ → v₁ ≠ v₂ → v₁ ∈ C.V → v₂ ∈ C.V →
      IsLineWithEnds F₂ v₁ v₂ → F₂ \ {v₁, v₂} ⊆ r →
      P₁.IsPathBetween v₁ v₂ → P₂.IsPathBetween v₁ v₂ →
      P₁.IsSubdrawing C → P₂.IsSubdrawing C →
      P₁.V ∩ P₂.V = {v₁, v₂} → Disjoint P₁.E P₂.E → C.sup P₁ P₂ = C →
      P₁.U ⊆ closure r ∨ P₂.U ⊆ closure r) :
    IsRigid (clearedSubdrawing H Λ) := by
  have : CompactSpace S := hS.1
  let H' : Drawing S := clearedSubdrawing H Λ
  obtain ⟨_, hE'_eq, hU'_eq, hC_sub', hΛ_R, hR_or, _⟩ :=
    clearedSubdrawing_props_of_circuit hΛ_open hC hCs hbd
  have hE'_sub : ∀ e ∈ H'.E, e ⊆ univ \ Λ := fun e he => (hE'_eq ▸ he).2
  have hR'_other : ∀ r ∈ H'.R, r ≠ Λ → r ∈ H.R ∧ Disjoint r Λ :=
    fun r hr hne => (hR_or r hr).resolve_left hne
  have hRig' : IsRigidIn H' (univ \ Λ) :=
    isRigidIn_clearedSubdrawing hS hRig hΛ_open hΛ_cl hC hCs hbd
  have hO_bd : IsOArc (subBd Λ) := hbd ▸ isOArc_of_isCircuit hC
  have hsubBd_cl : subBd (closure Λ) = C.U :=
    (subBd_closure_eq_subBd_of_isOpenDisc hS hΛ_open hO_bd hΛ_cl).trans hbd
  have hdiscBd_cl : discBd (closure Λ) = C.U :=
    (IsClosedDisc.subBd_eq_discBd hS hΛ_cl).symm.trans hsubBd_cl
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hU'_sub : H'.U ⊆ univ \ Λ := by
    rw [hU'_eq]
    exact fun x hx => ⟨mem_univ x, hx.2⟩
  intro F hF hFU hFV
  by_cases hF_sub_out : F ⊆ univ \ Λ
  · obtain ⟨Δ, _, hDial⟩ := hRig' F hF_sub_out hF hFU hFV
    exact ⟨Δ, hDial⟩
  · by_cases hF_sub_cl : F ⊆ closure Λ
    · obtain ⟨Δ, ⟨hΔ_sub, hΔ_disc, hΔ_bd, -, hΔ_dis, -⟩, -⟩ :=
        disc_oArc (closure Λ) F hΛ_cl hF_sub_cl hF
      have hΔ_subBd : subBd Δ = F :=
        (IsClosedDisc.subBd_eq_discBd hS hΔ_disc).trans hΔ_bd
      refine ⟨Δ, hΔ_disc, hΔ_subBd, Or.inl ?_⟩
      rintro x ⟨hxΔ, hxU'⟩
      by_contra hxF
      have hx_cl : x ∈ Λ ∪ subBd Λ := hclL ▸ hΔ_sub hxΔ
      have hx_bd : x ∈ subBd Λ := hx_cl.resolve_left (hU'_sub hxU').2
      exact disjoint_left.mp hΔ_dis ⟨hxΔ, hxF⟩ (hdiscBd_cl.symm ▸ (hbd ▸ hx_bd))
    · have hF_in : (F ∩ Λ).Nonempty := by
        rw [Set.not_subset] at hF_sub_out
        obtain ⟨x, hxF, hx_not⟩ := hF_sub_out
        exact ⟨x, hxF, by_contra fun hxΛ => hx_not ⟨mem_univ x, hxΛ⟩⟩
      have hF_out : (F \ closure Λ).Nonempty := by
        rw [Set.not_subset] at hF_sub_cl
        obtain ⟨x, hxF, hx_not⟩ := hF_sub_cl
        exact ⟨x, hxF, hx_not⟩
      obtain ⟨v₁, v₂, F₁, F₂, r, hv12, hv₁C, hv₂C, hFV_eq, hFU_eq, hFbd_eq,
        hF₁_line, hF₂_line, hF_union, hF12_inter, hF₁_cl, hF₁_Λ,
        hr_R', hr_H, hdis_rΛ, hr_sub, hF₂_r, _, _⟩ :=
        split_oArc_across_openDisc hS hΛ_open hΛ_cl hC hC_sub' hbd hΛ_R hR'_other
          hF hFU hFV hF_in hF_out
      have hCU_cl : C.U ⊆ closure Λ := hbd ▸ fun _ hx => hx.1
      obtain ⟨P₁, P₂, hP₁, hP₂, hP₁s, hP₂s, _, _, hV_inter12, hE_disj12, hsup12⟩ :=
        hC.exists_two_paths hv₁C hv₂C hv12
      have hPP'_exists : ∃ P P' : Drawing S,
          P.IsPathBetween v₁ v₂ ∧ P.IsSubdrawing C ∧ P'.IsSubdrawing C ∧
          P.V ∩ P'.V = {v₁, v₂} ∧ Disjoint P.E P'.E ∧ C.sup P P' = C ∧
          P.U ⊆ closure r := by
        rcases harc r v₁ v₂ F₂ P₁ P₂ hr_H hdis_rΛ hv12 hv₁C hv₂C hF₂_line hF₂_r
          hP₁ hP₂ hP₁s hP₂s hV_inter12 hE_disj12 hsup12 with hsub1 | hsub2
        · exact ⟨P₁, P₂, hP₁, hP₁s, hP₂s, hV_inter12, hE_disj12, hsup12, hsub1⟩
        · have hsup21 : C.sup P₂ P₁ = C := by
            apply Drawing.ext_VE
            · rw [C.sup_V hP₂s hP₁s, Set.union_comm, ← C.sup_V hP₁s hP₂s, hsup12]
            · rw [C.sup_E hP₂s hP₁s, Set.union_comm, ← C.sup_E hP₁s hP₂s, hsup12]
          exact ⟨P₂, P₁, hP₂, hP₂s, hP₁s, by rw [Set.inter_comm, hV_inter12],
            hE_disj12.symm, hsup21, hsub2⟩
      obtain ⟨P, P', hP, hPs, hP's, hV_inter, hE_disj, hsup, hPU_r⟩ := hPP'_exists
      let L : Set S := P.U
      obtain ⟨f_L, hfL0, hfL1⟩ := isLine_of_isPathBetween hP hv12
      have hL_line : IsLineWithEnds L v₁ v₂ := ⟨f_L, hfL0, hfL1⟩
      obtain ⟨hv₁L, hv₂L⟩ := IsLineWithEnds.ends_mem hL_line
      obtain ⟨hv₁F₁, hv₂F₁⟩ := IsLineWithEnds.ends_mem hF₁_line
      obtain ⟨hv₁F₂, hv₂F₂⟩ := IsLineWithEnds.ends_mem hF₂_line
      have hL_CU : L ⊆ C.U := hPs.U_subset
      have hL_cl : L ⊆ closure Λ := hL_CU.trans hCU_cl
      have hF₁L_inter : F₁ ∩ L ⊆ {v₁, v₂} := by
        rintro x ⟨hxF₁, hxL⟩
        by_contra hx12
        exact disjoint_left.mp hdisL (hF₁_Λ ⟨hxF₁, hx12⟩) (hbd.symm ▸ hL_CU hxL)
      have hF₁L_oArc : IsOArc (F₁ ∪ L) := isOArc_union hF₁_line hL_line hF₁L_inter
      have hF₁L_cl : F₁ ∪ L ⊆ closure Λ := union_subset hF₁_cl hL_cl
      obtain ⟨Δ₁, ⟨hΔ₁_sub, hΔ₁_disc, hΔ₁_bd_disc, -, hΔ₁_dis, -⟩, -⟩ :=
        disc_oArc (closure Λ) (F₁ ∪ L) hΛ_cl hF₁L_cl hF₁L_oArc
      have hΔ₁_bd : subBd Δ₁ = F₁ ∪ L :=
        (IsClosedDisc.subBd_eq_discBd hS hΔ₁_disc).trans hΔ₁_bd_disc
      have hP_H' : P.IsSubdrawing H' := hPs.trans hC_sub'
      have hΔ₁_U' : Δ₁ ∩ H'.U = L := by
        apply subset_antisymm
        · rintro x ⟨hxΔ₁, hxU'⟩
          have hx_cl : x ∈ Λ ∪ subBd Λ := hclL ▸ hΔ₁_sub hxΔ₁
          have hx_bd : x ∈ subBd Λ := hx_cl.resolve_left (hU'_sub hxU').2
          have hx_F₁L : x ∈ F₁ ∪ L := by
            by_contra hx_not
            exact disjoint_left.mp hΔ₁_dis ⟨hxΔ₁, hx_not⟩ (hdiscBd_cl.symm ▸ (hbd ▸ hx_bd))
          rcases hx_F₁L with hxF₁ | hxL
          · by_cases hx12 : x ∈ ({v₁, v₂} : Set S)
            · rcases mem_insert_iff.mp hx12 with hx1 | hx2
              · exact hx1 ▸ hv₁L
              · exact mem_singleton_iff.mp hx2 ▸ hv₂L
            · exact absurd (hbd ▸ hx_bd) (disjoint_left.mp hdisL (hF₁_Λ ⟨hxF₁, hx12⟩) ∘
                (fun h => hbd.symm ▸ h))
          · exact hxL
        · intro x hxL
          have hx_bd₁ : x ∈ subBd Δ₁ := hΔ₁_bd ▸ Or.inr hxL
          exact ⟨hΔ₁_disc.isClosed.closure_eq ▸ hx_bd₁.1, hP_H'.U_subset hxL⟩
      obtain ⟨Δ₂, hΔ₂_disc, hΔ₂_bd, hΔ₂_clΛ, hΔ₂_U'⟩ :=
        exists_pushed_disc_of_arc hS hRig' hΛ_open hΛ_cl hC hC_sub' hbd hE'_sub hΛ_R
          hv₁C hv₂C hv12 hP hPs hP's hV_inter hE_disj hsup hr_R' hr_sub hPU_r hF₂_line hF₂_r
      have hΔ12_inter : Δ₁ ∩ Δ₂ = L := by
        apply subset_antisymm
        · rintro x ⟨hxΔ₁, hxΔ₂⟩
          change x ∈ P.U
          rw [← hΔ₂_clΛ]
          exact ⟨hxΔ₂, hΔ₁_sub hxΔ₁⟩
        · intro x hxL
          have hxΔ₁ : x ∈ Δ₁ := by
            have : x ∈ Δ₁ ∩ H'.U := by rw [hΔ₁_U']; exact hxL
            exact this.1
          have hxΔ₂ : x ∈ Δ₂ := by
            have : x ∈ Δ₂ ∩ H'.U := by rw [hΔ₂_U']; exact hxL
            exact this.1
          exact ⟨hxΔ₁, hxΔ₂⟩
      have hL_bd₁ : L ⊆ discBd Δ₁ := hΔ₁_bd_disc ▸ subset_union_right
      have hL_bd₂ : L ⊆ discBd Δ₂ :=
        (IsClosedDisc.subBd_eq_discBd hS hΔ₂_disc).symm ▸ hΔ₂_bd ▸ subset_union_right
      obtain ⟨hΔ_disc, hΔ_bd_disc⟩ :=
        disc_union Δ₁ Δ₂ L v₁ v₂ hΔ₁_disc hΔ₂_disc hL_line hΔ12_inter hL_bd₁ hL_bd₂
      have hΔ_bd : subBd (Δ₁ ∪ Δ₂) = F := by
        rw [IsClosedDisc.subBd_eq_discBd hS hΔ_disc, hΔ_bd_disc,
          ← IsClosedDisc.subBd_eq_discBd hS hΔ₁_disc, ← IsClosedDisc.subBd_eq_discBd hS hΔ₂_disc,
          hΔ₁_bd, hΔ₂_bd, hF_union]
        ext x
        constructor
        · rintro ⟨(hxF₁ | hxL) | (hxF₂ | hxL), hx_not⟩
          · exact Or.inl hxF₁
          · have hx12 : x ∈ ({v₁, v₂} : Set S) := by_contra fun hn => hx_not ⟨hxL, hn⟩
            rcases mem_insert_iff.mp hx12 with hx1 | hx2
            · exact Or.inl (hx1 ▸ hv₁F₁)
            · exact Or.inl (mem_singleton_iff.mp hx2 ▸ hv₂F₁)
          · exact Or.inr hxF₂
          · have hx12 : x ∈ ({v₁, v₂} : Set S) := by_contra fun hn => hx_not ⟨hxL, hn⟩
            rcases mem_insert_iff.mp hx12 with hx1 | hx2
            · exact Or.inl (hx1 ▸ hv₁F₁)
            · exact Or.inl (mem_singleton_iff.mp hx2 ▸ hv₂F₁)
        · rintro (hxF₁ | hxF₂)
          · refine ⟨Or.inl (Or.inl hxF₁), fun ⟨hxL, hx12⟩ => hx12 (hF₁L_inter ⟨hxF₁, hxL⟩)⟩
          · refine ⟨Or.inr (Or.inl hxF₂), fun ⟨hxL, hx12⟩ => ?_⟩
            exact region_subset hr_R' (hF₂_r ⟨hxF₂, hx12⟩) (hP_H'.U_subset hxL)
      have hΔ_U' : (Δ₁ ∪ Δ₂) ∩ H'.U = P.U := by
        rw [union_inter_distrib_right, hΔ₁_U', hΔ₂_U', Set.union_self]
      obtain ⟨hinter_V, hinter_U⟩ := interSet_V_and_U hΔ_disc.isClosed (hΔ_bd ▸ hFU)
      have hΔ_interSet : H'.interSet (Δ₁ ∪ Δ₂) = P := by
        apply Drawing.ext_UV
        · rw [hinter_U, Set.inter_comm, hΔ_U']
        · rw [hinter_V]
          apply subset_antisymm
          · rintro x ⟨hxV', hxΔ⟩
            have hxPU : x ∈ P.U := hΔ_U' ▸ ⟨hxΔ, H'.V_subset_U hxV'⟩
            by_contra hxPV
            obtain ⟨e, heP, hxe⟩ := P.exists_edge_of_mem hxPU hxPV
            exact ((hP_H'.2 heP).2.1 hxe).2 hxV'
          · intro x hxPV
            exact ⟨hP_H'.1 hxPV, (hΔ_U' ▸ P.V_subset_U hxPV).1⟩
      refine ⟨Δ₁ ∪ Δ₂, hΔ_disc, hΔ_bd, Or.inr ⟨v₁, v₂, hv12, hFV_eq, ?_⟩⟩
      rwa [hΔ_interSet]

/-- **Graph Minors XIV, (6.3)** (page 33):
"Let $H$ be a rigid drawing in a surface $\Sigma$, and let $\Lambda \subseteq \Sigma$ be an
open disc with $\text{bd}(\Lambda) \subseteq U(H)$ such that $\text{bd}(\Lambda)$ is an
O-arc. Suppose that $\bar{r} \cap \bar{\Lambda}$ is null or connected for every region $r$
of $H$ with $r \cap \Lambda = \emptyset$. Then $H \cap (\Sigma - \Lambda)$ is a rigid
drawing in $\Sigma$." -/
theorem theorem_6_3_proof [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {H C : Drawing S} {Λ : Set S}
    (hRig : IsRigid H) (hΛ_open : IsOpenDisc Λ) (hΛ_cl : IsClosedDisc (closure Λ))
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hbd : subBd Λ = C.U)
    (hconn : ∀ r ∈ H.R, Disjoint r Λ → IsPreconnected (closure r ∩ closure Λ)) :
    IsRigid (clearedSubdrawing H Λ) := by
  refine isRigid_clearedSubdrawing_of_arc_subset hS hRig hΛ_open hΛ_cl hC hCs hbd ?_
  intro r v₁ v₂ F₂ P₁ P₂ hr_H hdis_rΛ hv12 hv₁C hv₂C hF₂_line hF₂_r
    hP₁ hP₂ hP₁s hP₂s hV_inter12 hE_disj12 hsup12
  obtain ⟨_, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hΛ_open.1
  have hCU_cl : C.U ⊆ closure Λ := hbd ▸ fun _ hx => hx.1
  have hdis_clr_Λ : Disjoint (closure r) Λ := hdis_rΛ.closure_left hΛ_open.1
  have hK_eq : closure r ∩ closure Λ = closure r ∩ C.U := by
    apply subset_antisymm
    · rintro x ⟨hxr, hxcl⟩
      have hx_bd : x ∈ subBd Λ := (hclL ▸ hxcl).resolve_left (disjoint_left.mp hdis_clr_Λ hxr)
      exact ⟨hxr, hbd ▸ hx_bd⟩
    · exact inter_subset_inter_right (closure r) hCU_cl
  have hK_pre : IsPreconnected (closure r ∩ C.U) := hK_eq ▸ hconn r hr_H hdis_rΛ
  obtain ⟨hv₁F₂, hv₂F₂⟩ := IsLineWithEnds.ends_mem hF₂_line
  have hv₁_cl_r : v₁ ∈ closure r :=
    closure_mono hF₂_r (IsLineWithEnds.subset_closure_sdiff_pair hF₂_line hv₁F₂)
  have hv₂_cl_r : v₂ ∈ closure r :=
    closure_mono hF₂_r (IsLineWithEnds.subset_closure_sdiff_pair hF₂_line hv₂F₂)
  have hU_union12 : P₁.U ∪ P₂.U = C.U := by
    rw [← hsup12]
    exact (Drawing.sup_U hP₁s hP₂s).symm
  rcases path_subset_of_isPreconnected_inter_circuit hP₁ hP₂ hP₁s hP₂s hv12
    hV_inter12 hE_disj12 hU_union12 hK_pre inter_subset_right
    ⟨hv₁_cl_r, C.V_subset_U hv₁C⟩ ⟨hv₂_cl_r, C.V_subset_U hv₂C⟩ with hsub1 | hsub2
  · exact Or.inl (hsub1.trans inter_subset_left)
  · exact Or.inr (hsub2.trans inter_subset_left)

end GraphMinor.GM14
