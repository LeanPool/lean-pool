/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement
import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM16.ProperDiscExtension
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

/-!
# Transporting a local arrangement into its containing disc

In XV (7.7), pages 139–140, a planar disc arrangement is moved into the closed disc around an eye.
We match the prescribed boundary vertices, extend the boundary map, and transport every arrangement
condition.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

theorem exists_bd_homeo_of_agreesWithOArcHomeo
    {S₁ : Type*} {S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂] {α : Type*}
    {ν₁ : α → S₁} {ν₂ : α → S₂} {Ω : CyclicPerm α} {C₁ : Set S₁} {C₂ : Set S₂}
    {φ₁ : Circle ≃ₜ C₁} {φ₂ : Circle ≃ₜ C₂}
    (hA₁ : AgreesWithOArcHomeo ν₁ Ω C₁ φ₁) (hA₂ : AgreesWithOArcHomeo ν₂ Ω C₂ φ₂)
    (hinj₁ : InjOn ν₁ Ω.bar) (hinj₂ : InjOn ν₂ Ω.bar) :
    ∃ e_bd : C₁ ≃ₜ C₂, ∀ v (hv : v ∈ Ω.bar), (e_bd ⟨ν₁ v, hA₁.1 v hv⟩).1 = ν₂ v := by
  rcases Ω.bar.eq_empty_or_nonempty with hemp | ⟨w₀, hw₀⟩
  · refine ⟨φ₁.symm.trans φ₂, fun v hv => ?_⟩
    rw [hemp] at hv
    exact hv.elim
  · obtain ⟨L, hL_len, hL_set, _, hcw⟩ := Ω.exists_isClockwiseSeq_of_subset_bar Subset.rfl hw₀
    have hlen_pos : 1 ≤ L.length := by
      have hw₀L : w₀ ∈ L := by
        have : w₀ ∈ {v | v ∈ L} := hL_set.symm ▸ hw₀
        exact this
      exact List.length_pos_of_mem hw₀L
    obtain ⟨t₁, ht₁_mono, ht₁_bd, ht₁_pt⟩ := exists_angles_of_isClockwiseSeq hA₁ hinj₁ hcw hlen_pos
    obtain ⟨t₂, ht₂_mono, ht₂_bd, ht₂_pt⟩ := exists_angles_of_isClockwiseSeq hA₂ hinj₂ hcw hlen_pos
    obtain ⟨h_circ, hh_circ⟩ :=
      exists_circle_homeo_matching_angles L.length hlen_pos t₁ t₂ ht₁_mono ht₂_mono ht₁_bd ht₂_bd
    refine ⟨φ₁.symm.trans (h_circ.trans φ₂), fun v hv => ?_⟩
    have hvL : v ∈ L := by
      have : v ∈ {x | x ∈ L} := hL_set.symm ▸ hv
      exact this
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvL
    have hφ₁_eq : (⟨ν₁ (L[i]'hi), hA₁.1 _ hv⟩ : C₁) = φ₁ (Circle.exp (t₁ i)) :=
      Subtype.ext (ht₁_pt i hi).symm
    simp only [Homeomorph.trans_apply]
    rw [hφ₁_eq, φ₁.symm_apply_apply, hh_circ i hi, ht₂_pt i hi]

/-- Transporting a disc arrangement `IsDiscArrangement` in `EuclideanPlane` to a closed disc `Δ_S`
in a surface `S` matching a given natural order on `subBd Δ_S`. -/
theorem exists_surface_disc_arrangement_of_isDiscArrangement
    {S : Type w} [TopologicalSpace S] (hS : IsClosedSurface S) {α : Type u} {β : Type v}
    (S_soc : Society α β) {m : ℕ} (A₀ : Society α β) (A : Fin m → Society α β)
    (Δ_E α₀_E : Set EuclideanPlane) (α_disc_E : Fin m → Set EuclideanPlane)
    (α_pt_E : α → EuclideanPlane)
    (hBar : S_soc.Ω.bar ⊆ segregationVertices (insert A₀ (range A)))
    (hArr : IsDiscArrangement S_soc A₀ A Δ_E α₀_E α_disc_E α_pt_E)
    (Δ_S : Set S) (hΔ_S : IsClosedDisc Δ_S)
    (α₀_pt : α → S) (hinj_S : InjOn α₀_pt S_soc.Ω.bar)
    (hNat_S : IsNaturalOrderFrom α₀_pt S_soc.Ω (subBd Δ_S)) :
    let S_seg := insert A₀ (range A)
    ∃ (α_disc_S : Society α β → Set S) (α_pt_S : α → S),
      (∀ v ∈ S_soc.Ω.bar, α_pt_S v = α₀_pt v) ∧
      (∀ v ∈ segregationVertices S_seg, α_pt_S v ∈ Δ_S) ∧
      (∀ v ∈ segregationVertices S_seg, v ∉ S_soc.Ω.bar → α_pt_S v ∈ Δ_S \ subBd Δ_S) ∧
      InjOn α_pt_S (segregationVertices S_seg) ∧
      (∀ B ∈ S_seg, IsClosedDisc (α_disc_S B) ∧ α_disc_S B ⊆ Δ_S ∧
        ∀ x ∈ B.Ω.bar, α_pt_S x ∈ subBd (α_disc_S B)) ∧
      (∀ B ∈ S_seg, IsNaturalOrderFrom α_pt_S B.Ω (subBd (α_disc_S B))) ∧
      (∀ B ∈ S_seg, α_disc_S B ∩ subBd Δ_S ⊆ α_pt_S '' (B.Ω.bar ∩ S_soc.Ω.bar)) ∧
      (∀ B₁ ∈ S_seg, ∀ B₂ ∈ S_seg, B₁ ≠ B₂ →
        α_disc_S B₁ ∩ α_disc_S B₂ ⊆ α_pt_S '' (B₁.Ω.bar ∩ B₂.Ω.bar)) := by
  classical
  intro S_seg
  have hseg_eq : segregationVertices S_seg = A₀.Ω.bar ∪ ⋃ j : Fin m, (A j).Ω.bar := by
    ext v
    simp only [segregationVertices, S_seg, mem_iUnion, mem_insert_iff, mem_range, mem_union]
    constructor
    · rintro ⟨B, rfl | ⟨j, rfl⟩, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨j, hv⟩
    · rintro (hv | ⟨j, hv⟩)
      · exact ⟨A₀, Or.inl rfl, hv⟩
      · exact ⟨A j, Or.inr ⟨j, rfl⟩, hv⟩
  have hinj_E_seg : InjOn α_pt_E (segregationVertices S_seg) := hseg_eq ▸ hArr.injOn_pts
  obtain ⟨φ_E, _, hA_E⟩ := hArr.bd_outer
  obtain ⟨_, φ_S, hA_S⟩ := hNat_S
  obtain ⟨e_subBd, he_subBd⟩ :=
    exists_bd_homeo_of_agreesWithOArcHomeo hA_E hA_S (hinj_E_seg.mono hBar) hinj_S
  have hbd_E : subBd Δ_E = discBd Δ_E :=
    isClosedDisc_subBd_eq_discBd_euclideanPlane hArr.isClosedDisc_Δ
  have hbd_S : subBd Δ_S = discBd Δ_S := IsClosedDisc.subBd_eq_discBd hS hΔ_S
  let e_bd : discBd Δ_E ≃ₜ discBd Δ_S :=
    (Homeomorph.setCongr hbd_E.symm).trans (e_subBd.trans (Homeomorph.setCongr hbd_S))
  obtain ⟨f, f', hf_maps, hf'_maps, hf_cont, hf'_cont, hf_left, hf_right, hf_bd⟩ :=
    exists_disc_extension_of_bd_homeo hArr.isClosedDisc_Δ hΔ_S e_bd
  have hf_subBd : ∀ x (hx : x ∈ subBd Δ_E), f x = (e_subBd ⟨x, hx⟩).1 := by
    intro x hx
    have hx' : x ∈ discBd Δ_E := hbd_E ▸ hx
    have h := hf_bd ⟨x, hx'⟩
    exact h
  have hf_mem_subBd_iff : ∀ x ∈ Δ_E, f x ∈ subBd Δ_S ↔ x ∈ subBd Δ_E := by
    intro x hx
    constructor
    · intro hfx
      have hfx' : f x ∈ discBd Δ_S := hbd_S ▸ hfx
      let x₀ : discBd Δ_E := e_bd.symm ⟨f x, hfx'⟩
      have hx₀_eq : f x₀.1 = f x := by
        rw [hf_bd x₀, e_bd.apply_symm_apply]
      have hx_eq : x₀.1 = x := hf_left.injOn (Surface.discBd_subset Δ_E x₀.2) hx hx₀_eq
      rw [← hx_eq, hbd_E]
      exact x₀.2
    · intro hx_bd
      rw [hf_subBd x hx_bd]
      exact (e_subBd ⟨x, hx_bd⟩).2
  let disc_E : Society α β → Set EuclideanPlane := fun B =>
    if B = A₀ then α₀_E
    else if h : ∃ j : Fin m, A j = B then α_disc_E (Classical.choose h)
    else ∅
  have hdisc_E_zero : disc_E A₀ = α₀_E := by simp [disc_E]
  have hdisc_E_ne : ∀ {B : Society α β}, B ∈ S_seg → B ≠ A₀ →
      ∃ j : Fin m, A j = B ∧ disc_E B = α_disc_E j := by
    intro B hB hne
    have hex : ∃ j : Fin m, A j = B := by
      rcases hB with rfl | ⟨j, rfl⟩
      · exact (hne rfl).elim
      · exact ⟨j, rfl⟩
    refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
    simp [disc_E, hne, hex]
  have hdisc_E_closed : ∀ B ∈ S_seg, IsClosedDisc (disc_E B) ∧ disc_E B ⊆ Δ_E := by
    intro B hB
    by_cases h0 : B = A₀
    · subst h0; rw [hdisc_E_zero]; exact hArr.isClosedDisc_zero
    · obtain ⟨j, _, hj_disc⟩ := hdisc_E_ne hB h0
      rw [hj_disc]; exact hArr.isClosedDisc_succ j
  have hdisc_E_bd : ∀ B ∈ S_seg, ∃ φ : Circle ≃ₜ subBd (disc_E B),
      AgreesWithOArcHomeo α_pt_E B.Ω (subBd (disc_E B)) φ := by
    intro B hB
    by_cases h0 : B = A₀
    · subst h0; rw [hdisc_E_zero]; obtain ⟨φ, _, h⟩ := hArr.bd_zero; exact ⟨φ, h⟩
    · obtain ⟨j, rfl, hj_disc⟩ := hdisc_E_ne hB h0
      rw [hj_disc]; obtain ⟨φ, _, h⟩ := hArr.bd_succ j; exact ⟨φ, h⟩
  have hdisc_E_inter_bd : ∀ B ∈ S_seg,
      disc_E B ∩ subBd Δ_E ⊆ α_pt_E '' (B.Ω.bar ∩ S_soc.Ω.bar) := by
    intro B hB
    by_cases h0 : B = A₀
    · subst h0; rw [hdisc_E_zero]; exact hArr.inter_bd_zero
    · obtain ⟨j, rfl, hj_disc⟩ := hdisc_E_ne hB h0
      rw [hj_disc]; exact hArr.inter_bd_succ j
  have hdisc_E_inter : ∀ B₁ ∈ S_seg, ∀ B₂ ∈ S_seg, B₁ ≠ B₂ →
      disc_E B₁ ∩ disc_E B₂ ⊆ α_pt_E '' (B₁.Ω.bar ∩ B₂.Ω.bar) := by
    intro B₁ hB₁ B₂ hB₂ hne
    by_cases h10 : B₁ = A₀
    · subst h10
      obtain ⟨j, rfl, hj_disc⟩ := hdisc_E_ne hB₂ hne.symm
      rw [hdisc_E_zero, hj_disc]
      exact hArr.inter_zero j
    · obtain ⟨i, hAi, hi_disc⟩ := hdisc_E_ne hB₁ h10
      by_cases h20 : B₂ = A₀
      · subst h20
        rw [hi_disc, hdisc_E_zero, ← hAi, Set.inter_comm, Set.inter_comm (A i).Ω.bar]
        exact hArr.inter_zero i
      · obtain ⟨j, hAj, hj_disc⟩ := hdisc_E_ne hB₂ h20
        have hij : i ≠ j := fun heq => hne (hAi.symm.trans (congrArg A heq |>.trans hAj))
        rw [hi_disc, hj_disc, ← hAi, ← hAj]
        exact hArr.inter_succ i j hij
  have hpt_E_mem : ∀ v ∈ segregationVertices S_seg, α_pt_E v ∈ Δ_E := by
    intro v hv
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    obtain ⟨φ_B, hA_B⟩ := hdisc_E_bd B hB
    have hsub : subBd (disc_E B) ⊆ disc_E B := by
      rw [isClosedDisc_subBd_eq_discBd_euclideanPlane (hdisc_E_closed B hB).1]
      exact Surface.discBd_subset (disc_E B)
    exact (hdisc_E_closed B hB).2 (hsub (hA_B.1 v hvB))
  let α_disc_S : Society α β → Set S := fun B => f '' disc_E B
  let α_pt_S : α → S := fun v => f (α_pt_E v)
  have hB_img : ∀ B ∈ S_seg,
      IsClosedDisc (α_disc_S B) ∧ subBd (α_disc_S B) = f '' subBd (disc_E B) := by
    intro B hB
    obtain ⟨hB_disc, hB_sub⟩ := hdisc_E_closed B hB
    have hf'_B : ContinuousOn f' (f '' disc_E B) :=
      hf'_cont.mono (image_subset_iff.mpr fun x hx => hf_maps (hB_sub hx))
    obtain ⟨himg_disc, himg_bd⟩ :=
      hB_disc.image (hf_cont.mono hB_sub) hf'_B (hf_left.mono hB_sub)
    refine ⟨himg_disc, ?_⟩
    rw [IsClosedDisc.subBd_eq_discBd hS himg_disc, himg_bd,
      isClosedDisc_subBd_eq_discBd_euclideanPlane hB_disc]
  refine ⟨α_disc_S, α_pt_S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    dsimp only [α_pt_S]
    rw [hf_subBd (α_pt_E v) (hA_E.1 v hv), he_subBd v hv]
  · intro v hv
    exact hf_maps (hpt_E_mem v hv)
  · intro v hv hv_not
    refine ⟨hf_maps (hpt_E_mem v hv), fun hbd => ?_⟩
    have hx_bd : α_pt_E v ∈ subBd Δ_E := (hf_mem_subBd_iff (α_pt_E v) (hpt_E_mem v hv)).mp hbd
    rcases mem_iUnion₂.mp hv with ⟨B, hB, hvB⟩
    obtain ⟨φ_B, hA_B⟩ := hdisc_E_bd B hB
    have hsub : subBd (disc_E B) ⊆ disc_E B := by
      rw [isClosedDisc_subBd_eq_discBd_euclideanPlane (hdisc_E_closed B hB).1]
      exact Surface.discBd_subset (disc_E B)
    have hmem_inter : α_pt_E v ∈ disc_E B ∩ subBd Δ_E := ⟨hsub (hA_B.1 v hvB), hx_bd⟩
    obtain ⟨w, ⟨hwB, hwS⟩, hw_eq⟩ := hdisc_E_inter_bd B hB hmem_inter
    have hw_seg : w ∈ segregationVertices S_seg := mem_biUnion hB hwB
    have hvw : w = v := hinj_E_seg hw_seg hv hw_eq
    exact hv_not (hvw ▸ hwS)
  · intro u hu v hv huv
    exact hinj_E_seg hu hv (hf_left.injOn (hpt_E_mem u hu) (hpt_E_mem v hv) huv)
  · intro B hB
    obtain ⟨hdisc_B, hbd_B⟩ := hB_img B hB
    refine ⟨hdisc_B, image_subset_iff.mpr fun x hx => hf_maps ((hdisc_E_closed B hB).2 hx), ?_⟩
    intro x hx
    obtain ⟨φ_B, hA_B⟩ := hdisc_E_bd B hB
    rw [hbd_B]
    exact mem_image_of_mem f (hA_B.1 x hx)
  · intro B hB
    obtain ⟨hdisc_B, hbd_B⟩ := hB_img B hB
    obtain ⟨φ_B, hA_B⟩ := hdisc_E_bd B hB
    have hsub_B : subBd (disc_E B) ⊆ Δ_E := by
      rw [isClosedDisc_subBd_eq_discBd_euclideanPlane (hdisc_E_closed B hB).1]
      exact (Surface.discBd_subset (disc_E B)).trans (hdisc_E_closed B hB).2
    have hf'_bdB : ContinuousOn f' (f '' subBd (disc_E B)) :=
      hf'_cont.mono (image_subset_iff.mpr fun x hx => hf_maps (hsub_B hx))
    obtain ⟨e_B, he_B⟩ := exists_homeomorph_image (hf_cont.mono hsub_B) hf'_bdB
      (hf_left.mono hsub_B)
    let φ_B_S : Circle ≃ₜ subBd (α_disc_S B) :=
      φ_B.trans (e_B.trans (Homeomorph.setCongr hbd_B.symm))
    refine ⟨⟨φ_B_S⟩, φ_B_S, ?_, ?_⟩
    · intro v hv
      rw [hbd_B]
      exact mem_image_of_mem f (hA_B.1 v hv)
    · intro v₁ v₂ v₃ hcw3
      obtain ⟨t₁, t₂, t₃, ht12, ht23, ht31, h1, h2, h3⟩ := hA_B.2 v₁ v₂ v₃ hcw3
      refine ⟨t₁, t₂, t₃, ht12, ht23, ht31, ?_, ?_, ?_⟩
      · exact (he_B (φ_B (Circle.exp t₁))).trans (congrArg f h1)
      · exact (he_B (φ_B (Circle.exp t₂))).trans (congrArg f h2)
      · exact (he_B (φ_B (Circle.exp t₃))).trans (congrArg f h3)
  · rintro B hB _ ⟨⟨x, hxB, rfl⟩, hy_bd⟩
    have hx_Δ : x ∈ Δ_E := (hdisc_E_closed B hB).2 hxB
    have hx_bd : x ∈ subBd Δ_E := (hf_mem_subBd_iff x hx_Δ).mp hy_bd
    obtain ⟨v, hv, hxv⟩ := hdisc_E_inter_bd B hB ⟨hxB, hx_bd⟩
    exact ⟨v, hv, congrArg f hxv⟩
  · rintro B₁ hB₁ B₂ hB₂ hne _ ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx_eq⟩⟩
    have hx12 : x₁ = x₂ :=
      hf_left.injOn ((hdisc_E_closed B₁ hB₁).2 hx₁) ((hdisc_E_closed B₂ hB₂).2 hx₂) hx_eq.symm
    subst hx12
    obtain ⟨v, hv, hxv⟩ := hdisc_E_inter B₁ hB₁ B₂ hB₂ hne ⟨hx₁, hx₂⟩
    exact ⟨v, hv, congrArg f hxv⟩


end GraphMinor.GM16
