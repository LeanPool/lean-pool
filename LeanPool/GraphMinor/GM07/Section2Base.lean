/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Open
import LeanPool.GraphMinor.GM07.Section11
import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.GM11.Section4b
import LeanPool.GraphMinor.Surface.Circle
import LeanPool.GraphMinor.Surface.EdgeLoop
import LeanPool.GraphMinor.Surface.Gluing
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors VII, Section 2: Surfaces and Nets

This file formalizes Section 2 (pages 213–218) of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254:
- Unconditional properties of nets and seam graphs (`Net.preimage_seamU`, `Net.image_compl_bd`,
  `Net.homeomorph_compl_seamU`, `Net.isOpenDisc_compl_seamU`, `Net.bd_subset_seamU`,
  `Net.seamGraph_unique_region`, `Net.seamGraph_region_nullHomotopic`);
- `(2.1)` (`theorem_2_1_forward`, `theorem_2_1_proof`): characterization of seam graphs for nets;
- Unconditional edge-end and handshaking lemmas for drawings (`tilde_eq_closure_inter_V`,
  `ncard_tilde_of_mem_E`, `sum_vertexValency_eq_two_mul_ncard_E`,
  `three_mul_ncard_V_le_two_mul_ncard_E`);
- `(2.2)` (`theorem_2_2`): vertex and edge bounds for seam graphs of minimum valency at least `3`;
- `(2.3)` (`theorem_2_3`): every vertex of the seam graph of a minimal net has valency at least `3`;
- `(2.4)` (`theorem_2_4`): vertex and edge bounds for the seam graph of a minimal net, deduced from
  `(2.2)`, `(2.3)`, and `Surface.modelCriterion`;
- `(2.5)` (`theorem_2_5`): existence of a path in `J'` between `φ(s)` and `φ(t)` with no edges of
  type (iii) or (iv);
- `(2.6)` (`theorem_2_6`): shortcutting a `φ⁻¹(G)`-normal proper `I`-arc `F` in `Δ` by a `G`-normal
  `O`-arc `A` in `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Unconditional topology of nets and seam graphs -/

namespace Net

/-- The preimage under `N.φ` of the seam set `N.seamU = N.φ '' bd N.D` is `bd N.D`, because `N.φ`
makes no identifications on `(bd N.D)ᶜ`. -/
theorem preimage_seamU (N : Net S) : N.φ ⁻¹' N.seamU = bd N.D := by
  ext x
  simp only [seamU, mem_preimage, mem_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    by_contra hx
    have hxeq : x = y := N.interior_inj x hx y hxy.symm
    exact hx (hxeq ▸ hy)
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The image under `N.φ` of the interior `(bd N.D)ᶜ` of the disc `N.D` is `univ \ N.seamU`. -/
theorem image_compl_bd (N : Net S) : N.φ '' (bd N.D)ᶜ = univ \ N.seamU := by
  ext z
  simp only [mem_image, mem_compl_iff, mem_sdiff, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩ hz
    have hx' : x ∈ N.φ ⁻¹' N.seamU := hz
    rw [N.preimage_seamU] at hx'
    exact hx hx'
  · intro hz
    obtain ⟨x, rfl⟩ := N.quotientMap_φ.surjective z
    refine ⟨x, ?_, rfl⟩
    intro hx
    exact hz ⟨x, hx, rfl⟩

/-- The restriction of `N.φ` to `(bd N.D)ᶜ` is a homeomorphism onto `univ \ N.seamU`.
Graph Minors VII, Section 2, proof of (2.1) (page 215):
"Then the restriction of $\phi$ to $\Delta - bd(\Delta)$ is injective, and hence provides a
homeomorphism from $\Delta - bd(\Delta)$ to $\Sigma - U(J)$." -/
theorem homeomorph_compl_seamU [T2Space S] (N : Net S) :
    Nonempty (((bd N.D)ᶜ : Set N.D) ≃ₜ (univ \ N.seamU : Set S)) := by
  have : CompactSpace N.D := N.isSurface_D.1
  have hclosed_φ : IsClosedMap N.φ := N.quotientMap_φ.continuous.isClosedMap
  have hbd_closed : IsClosed (bd N.D) := isClosed_bd N.D
  have hopen_compl : IsOpen ((bd N.D)ᶜ : Set N.D) := hbd_closed.isOpen_compl
  let toFun : ((bd N.D)ᶜ : Set N.D) → (univ \ N.seamU : Set S) := fun x =>
    ⟨N.φ x.1, by
      rw [← N.image_compl_bd]
      exact ⟨x.1, x.2, rfl⟩⟩
  have hcont : Continuous toFun :=
    (N.quotientMap_φ.continuous.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective toFun := by
    intro x y hxy
    ext
    exact N.interior_inj x.1 x.2 y.1 (congr_arg Subtype.val hxy)
  have hsurj : Function.Surjective toFun := by
    rintro ⟨z, hz⟩
    rw [← N.image_compl_bd] at hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hopenMap : IsOpenMap toFun := by
    intro U hU
    have hU_open_D : IsOpen (Subtype.val '' U : Set N.D) :=
      hopen_compl.isOpenMap_subtype_val U hU
    have hK_closed : IsClosed ((Subtype.val '' U : Set N.D)ᶜ) := hU_open_D.isClosed_compl
    have hφK_closed : IsClosed (N.φ '' (Subtype.val '' U : Set N.D)ᶜ) :=
      hclosed_φ _ hK_closed
    have himg_eq : toFun '' U =
        Subtype.val ⁻¹' ((N.φ '' (Subtype.val '' U : Set N.D)ᶜ)ᶜ) := by
      ext ⟨z, hz⟩
      simp only [mem_image, mem_preimage, mem_compl_iff]
      constructor
      · rintro ⟨⟨x, hxbd⟩, hxU, hzx⟩ ⟨y, hynot, hyz⟩
        have hzx' : N.φ x = z := congr_arg Subtype.val hzx
        have hxy : x = y := N.interior_inj x hxbd y (hzx'.trans hyz.symm)
        subst hxy
        exact hynot ⟨⟨x, hxbd⟩, hxU, rfl⟩
      · intro hnot
        have hz' : z ∈ N.φ '' (bd N.D)ᶜ := by
          rw [N.image_compl_bd]
          exact hz
        rcases hz' with ⟨x, hxbd, rfl⟩
        have hx_in : x ∈ (Subtype.val '' U : Set N.D) := by
          by_contra hxnot
          exact hnot ⟨x, hxnot, rfl⟩
        rcases hx_in with ⟨⟨x', hx'bd⟩, hx'U, rfl⟩
        exact ⟨⟨x', hx'bd⟩, hx'U, rfl⟩
    rw [himg_eq]
    exact hφK_closed.isOpen_compl.preimage continuous_subtype_val
  exact ⟨(Equiv.ofBijective toFun ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopenMap⟩

/-- The interior `(bd N.D)ᶜ` of `N.D` is homeomorphic to `OpenUnitDisc`, so `univ \ N.seamU` is an
open disc in `S`. -/
theorem isOpenDisc_compl_seamU [T2Space S] (N : Net S) : IsOpenDisc (univ \ N.seamU) := by
  have : CompactSpace N.D := N.isSurface_D.1
  have hclosed_seamU : IsClosed N.seamU :=
    N.quotientMap_φ.continuous.isClosedMap _ (isClosed_bd N.D)
  have hopen : IsOpen (univ \ N.seamU) := by
    rw [← compl_eq_univ_sdiff]
    exact hclosed_seamU.isOpen_compl
  obtain ⟨hD₀⟩ := N.isClosedDisc_D
  let hD : ClosedUnitDisc ≃ₜ N.D := hD₀.trans (Homeomorph.Set.univ N.D)
  have hbd_img : hD '' bd ClosedUnitDisc = bd N.D := image_bd_homeomorph hD
  have hcompl_img : hD '' (bd ClosedUnitDisc)ᶜ = (bd N.D)ᶜ := by
    rw [← hbd_img, image_compl_eq hD.bijective]
  have hbd_unit : ((bd ClosedUnitDisc)ᶜ : Set ClosedUnitDisc) = Subtype.val ⁻¹' OpenUnitDisc := by
    rw [bd_closedUnitDisc]
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, UnitCircle, mem_sphere_zero_iff_norm,
      mem_preimage, OpenUnitDisc, mem_ball_zero_iff]
    have hle : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    exact ⟨fun hne => lt_of_le_of_ne hle hne, fun hlt heq => ne_of_lt hlt heq⟩
  let e₁ : OpenUnitDisc ≃ₜ ((bd ClosedUnitDisc)ᶜ : Set ClosedUnitDisc) :=
    openPartHomeomorph.symm.trans (Homeomorph.setCongr hbd_unit.symm)
  let e₂ : ((bd ClosedUnitDisc)ᶜ : Set ClosedUnitDisc) ≃ₜ ((bd N.D)ᶜ : Set N.D) :=
    (hD.image (bd ClosedUnitDisc)ᶜ).trans (Homeomorph.setCongr hcompl_img)
  obtain ⟨e₃⟩ := N.homeomorph_compl_seamU
  exact ⟨hopen, ⟨(e₁.trans e₂).trans e₃⟩⟩

/-- For any net `N : Net S`, `bd S ⊆ N.seamU`, because `univ \ N.seamU` is an open subset of `S`
homeomorphic to `OpenUnitDisc` and hence consists entirely of interior points of `S`. -/
theorem bd_subset_seamU [T2Space S] (N : Net S) : bd S ⊆ N.seamU := by
  obtain ⟨hopen, ⟨f⟩⟩ := N.isOpenDisc_compl_seamU
  intro x hxbd
  by_contra hxnot
  have hxmem : x ∈ univ \ N.seamU := ⟨trivial, hxnot⟩
  exact hxbd ⟨univ \ N.seamU, hopen, hxmem, ⟨f.symm⟩⟩

/-- Graph Minors VII, (2.1)(iii) (page 215):
Every seam graph `J` for a net `N` has a unique region `univ \ J.U`. -/
theorem seamGraph_unique_region [T2Space S] (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    J.R = {univ \ J.U} ∧ J.R.ncard = 1 := by
  have hOpenDisc : IsOpenDisc (univ \ J.U) := by
    rw [hJ.2.1]
    exact N.isOpenDisc_compl_seamU
  have hpc : IsPathConnected (univ \ J.U) := hOpenDisc.isPathConnected
  have hconn : IsConnected (univ \ J.U) := hpc.isConnected
  rcases hconn.nonempty with ⟨x₀, hx₀⟩
  have hR_eq : J.R = {univ \ J.U} := by
    ext r
    simp only [Drawing.R, componentsIn, mem_image, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply Subset.antisymm (connectedComponentIn_subset _ _)
      exact hconn.isPreconnected.subset_connectedComponentIn hx Subset.rfl
    · rintro rfl
      refine ⟨x₀, hx₀, ?_⟩
      apply Subset.antisymm (connectedComponentIn_subset _ _)
      exact hconn.isPreconnected.subset_connectedComponentIn hx₀ Subset.rfl
  exact ⟨hR_eq, by rw [hR_eq, ncard_singleton]⟩

/-- Graph Minors VII, (2.1)(iv) (page 215):
For any seam graph `J` of a net `N`, every `O`-arc included in the unique region of `J` is
null-homotopic in `S`. -/
theorem seamGraph_region_nullHomotopic (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    ∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F := by
  have : T2Space S := hS.2.1
  have hOpenDisc : IsOpenDisc (univ \ J.U) := by
    rw [hJ.2.1]
    exact N.isOpenDisc_compl_seamU
  have hR := (N.seamGraph_unique_region hJ).1
  intro r hr F hFr hFO
  rw [hR, mem_singleton_iff] at hr
  subst hr
  have hF_closed : IsClosed F := by
    rcases hFO with ⟨f⟩
    have hcomp : IsCompact (range (Subtype.val ∘ f)) := isCompact_range (by fun_prop)
    have hrange : range (Subtype.val ∘ f) = F := by
      ext x
      simp only [Function.comp_apply, mem_range]
      exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hx => ⟨f.symm ⟨x, hx⟩, by simp⟩⟩
    rw [← hrange]
    exact hcomp.isClosed
  obtain ⟨Δ, hΔ_disc, hF_Δ⟩ :=
    isPlanar_of_isClosed_subset_isOpenDisc hS hF_closed hOpenDisc hFr
  exact isNullHomotopicOArcIn_of_subset_disc hFO (subset_univ Δ) hΔ_disc hF_Δ

/-- For any `i : Fin N.r` and `t ∈ Ioo (0 : unitInterval) 1`, the fiber of `N.φ` over
`N.φ (N.f i t) = N.φ (N.g i t)` is `{N.f i t, N.g i t}`. -/
theorem eq_f_or_g_of_φ_eq_of_mem_Ioo (N : Net S) (i : Fin N.r) {t : unitInterval}
    (ht : t ∈ Ioo (0 : unitInterval) 1) {y : N.D} (hy : N.φ (N.f i t) = N.φ y) :
    y = N.f i t ∨ y = N.g i t := by
  let R : N.D → N.D → Prop := fun a b =>
    ∃ (j : Fin N.r) (s : unitInterval), a = N.f j s ∧ b = N.g j s
  have hrel : Relation.EqvGen R (N.f i t) y := (N.bd_eq_iff (N.f i t) y).mp hy
  let P : Set N.D := {N.f i t, N.g i t}
  have hstep : ∀ a b : N.D, R a b → (a ∈ P ↔ b ∈ P) := by
    rintro a b ⟨j, s, rfl, rfl⟩
    simp only [P, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (hff | hfg)
      · by_cases hij : i = j
        · subst hij
          have hst : s = t := N.injective_f i hff
          subst hst
          exact Or.inr rfl
        · exfalso
          exact N.internally_disjoint_ff i j hij t ht ⟨s, hff⟩
      · exfalso
        exact N.internally_disjoint_gf i j t ht ⟨s, hfg⟩
    · rintro (hgf | hgg)
      · exfalso
        exact N.internally_disjoint_fg i j t ht ⟨s, hgf⟩
      · by_cases hij : i = j
        · subst hij
          have hst : s = t := N.injective_g i hgg
          subst hst
          exact Or.inl rfl
        · exfalso
          exact N.internally_disjoint_gg i j hij t ht ⟨s, hgg⟩
  have heqv : ∀ a b : N.D, Relation.EqvGen R a b → (a ∈ P ↔ b ∈ P) := by
    intro a b hab
    induction hab with
    | rel x z hxz => exact hstep x z hxz
    | refl x => exact Iff.rfl
    | symm x z _ ih => exact ih.symm
    | trans x w z _ _ ih1 ih2 => exact ih1.trans ih2
  exact (heqv (N.f i t) y hrel).mp (Or.inl rfl)

/-- For any `i : Fin N.r` and `t ∈ Ioo (0 : unitInterval) 1`, `N.φ (N.f i t) ∉ N.seamV`. -/
theorem notMem_seamV_of_mem_Ioo (N : Net S) (i : Fin N.r) {t : unitInterval}
    (ht : t ∈ Ioo (0 : unitInterval) 1) :
    N.φ (N.f i t) ∉ N.seamV := by
  rintro ⟨j, hj0 | hj1⟩
  · rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht hj0.symm with hff | hfg
    · by_cases hij : i = j
      · subst hij
        have h0t : (0 : unitInterval) = t := N.injective_f i hff
        exact ht.1.ne h0t
      · exact N.internally_disjoint_ff i j hij t ht ⟨0, hff⟩
    · exact N.internally_disjoint_gf i j t ht ⟨0, hfg⟩
  · rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht hj1.symm with hff | hfg
    · by_cases hij : i = j
      · subst hij
        have h1t : (1 : unitInterval) = t := N.injective_f i hff
        exact ht.2.ne h1t.symm
      · exact N.internally_disjoint_ff i j hij t ht ⟨1, hff⟩
    · exact N.internally_disjoint_gf i j t ht ⟨1, hfg⟩

/-- For any `i : Fin N.r` and `t : unitInterval`, `N.φ (N.f i t) = N.φ (N.g i t)`. -/
theorem φ_f_eq_φ_g (N : Net S) (i : Fin N.r) (t : unitInterval) :
    N.φ (N.f i t) = N.φ (N.g i t) :=
  (N.bd_eq_iff (N.f i t) (N.g i t)).mpr (.rel _ _ ⟨i, t, rfl, rfl⟩)

/-- Every `t : unitInterval` is `0`, `1`, or in `Ioo (0 : unitInterval) 1`. -/
theorem unitInterval_eq_zero_or_one_or_mem_Ioo (t : unitInterval) :
    t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : unitInterval) 1 := by
  have h0_le : (0 : unitInterval) ≤ t := Subtype.coe_le_coe.mp t.2.1
  have hle_1 : t ≤ (1 : unitInterval) := Subtype.coe_le_coe.mp t.2.2
  rcases eq_or_lt_of_le h0_le with h0 | h0
  · exact Or.inl h0.symm
  · rcases eq_or_lt_of_le hle_1 with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h0, h1⟩)

/-- The preimage `N.φ ⁻¹' N.seamV` is contained in the finite set of endpoints of `N.f i` and
`N.g i` (`i : Fin N.r`). -/
theorem preimage_seamV_subset_endpoints (N : Net S) :
    N.φ ⁻¹' N.seamV ⊆ ⋃ i : Fin N.r, ({N.f i 0, N.f i 1, N.g i 0, N.g i 1} : Set N.D) := by
  let Ends : Set N.D := ⋃ i : Fin N.r, ({N.f i 0, N.f i 1, N.g i 0, N.g i 1} : Set N.D)
  have hEnds_seamV : ∀ x ∈ Ends, N.φ x ∈ N.seamV := by
    intro x hx
    simp only [Ends, mem_iUnion, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with ⟨i, rfl | rfl | rfl | rfl⟩
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩
    · exact ⟨i, Or.inl (N.φ_f_eq_φ_g i 0)⟩
    · exact ⟨i, Or.inr (N.φ_f_eq_φ_g i 1)⟩
  let R : N.D → N.D → Prop := fun a b =>
    ∃ (j : Fin N.r) (s : unitInterval), a = N.f j s ∧ b = N.g j s
  have hstep : ∀ a b : N.D, R a b → (a ∈ Ends ↔ b ∈ Ends) := by
    rintro a b ⟨j, s, rfl, rfl⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
    · constructor <;> intro _ <;> refine mem_iUnion.mpr ⟨j, ?_⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
    · constructor <;> intro _ <;> refine mem_iUnion.mpr ⟨j, ?_⟩
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inl rfl)
    · constructor <;> intro hmem
      · exfalso
        exact N.notMem_seamV_of_mem_Ioo j hs (hEnds_seamV _ hmem)
      · exfalso
        have hmem' : N.φ (N.f j s) ∈ N.seamV := by
          rw [N.φ_f_eq_φ_g j s]
          exact hEnds_seamV _ hmem
        exact N.notMem_seamV_of_mem_Ioo j hs hmem'
  have heqv : ∀ a b : N.D, Relation.EqvGen R a b → (a ∈ Ends ↔ b ∈ Ends) := by
    intro a b hab
    induction hab with
    | rel x z hxz => exact hstep x z hxz
    | refl x => exact Iff.rfl
    | symm x z _ ih => exact ih.symm
    | trans x w z _ _ ih1 ih2 => exact ih1.trans ih2
  rintro x ⟨i, hi | hi⟩
  · have hrel : Relation.EqvGen R (N.f i 0) x := (N.bd_eq_iff (N.f i 0) x).mp hi
    exact (heqv (N.f i 0) x hrel).mp (mem_iUnion.mpr ⟨i, Or.inl rfl⟩)
  · have hrel : Relation.EqvGen R (N.f i 1) x := (N.bd_eq_iff (N.f i 1) x).mp hi
    exact (heqv (N.f i 1) x hrel).mp (mem_iUnion.mpr ⟨i, Or.inr (Or.inl rfl)⟩)

/-- The preimage `N.φ ⁻¹' N.seamV` is finite. -/
theorem finite_preimage_seamV (N : Net S) : (N.φ ⁻¹' N.seamV).Finite := by
  refine (finite_iUnion fun i : Fin N.r => ?_).subset N.preimage_seamV_subset_endpoints
  exact ((finite_singleton _).insert _).insert _ |>.insert _

/-- Every fiber `N.φ ⁻¹' {z}` of a net surjection `N.φ` is finite. -/
theorem finite_preimage_singleton (N : Net S) (z : S) : (N.φ ⁻¹' {z}).Finite := by
  by_cases hzV : z ∈ N.seamV
  · refine N.finite_preimage_seamV.subset fun x hx => ?_
    rw [mem_preimage, mem_singleton_iff] at hx
    simpa [hx] using hzV
  · by_cases hIoo : ∃ (i : Fin N.r) (t : unitInterval),
      t ∈ Ioo (0 : unitInterval) 1 ∧ N.φ (N.f i t) = z
    · rcases hIoo with ⟨i, t, ht, rfl⟩
      refine ((finite_singleton (N.g i t)).insert (N.f i t)).subset fun y hy => ?_
      exact N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht (mem_singleton_iff.mp hy).symm
    · refine Set.Subsingleton.finite fun x hx y hy => ?_
      have hxy : N.φ x = N.φ y := by
        rw [mem_preimage, mem_singleton_iff] at hx hy
        exact hx.trans hy.symm
      let R : N.D → N.D → Prop := fun a b =>
        ∃ (j : Fin N.r) (s : unitInterval), a = N.f j s ∧ b = N.g j s
      have hrel : Relation.EqvGen R x y := (N.bd_eq_iff x y).mp hxy
      have hno_step : ∀ a b : N.D, R a b → N.φ a ≠ z := by
        rintro a b ⟨j, s, rfl, rfl⟩ hφ
        rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
        · exact hzV ⟨j, Or.inl hφ⟩
        · exact hzV ⟨j, Or.inr hφ⟩
        · exact hIoo ⟨j, s, hs, hφ⟩
      have heq_of_rel : ∀ a b : N.D, Relation.EqvGen R a b → (N.φ a = z → a = b) := by
        intro a b hab
        induction hab with
        | rel u v huv =>
          intro hu
          exact False.elim (hno_step u v huv hu)
        | refl u =>
          intro _
          rfl
        | symm u v huv ih =>
          intro hv
          have huv_φ : N.φ u = N.φ v := (N.bd_eq_iff u v).mpr huv
          exact (ih (huv_φ.trans hv)).symm
        | trans u w v huw _ ih1 ih2 =>
          intro hu
          have huw_φ : N.φ u = N.φ w := (N.bd_eq_iff u w).mpr huw
          exact (ih1 hu).trans (ih2 (huw_φ.symm.trans hu))
      exact heq_of_rel x y hrel (mem_singleton_iff.mp hx)

/-- The preimage under `N.φ` of any finite subset of `S` is finite. -/
theorem finite_preimage (N : Net S) {A : Set S} (hA : A.Finite) : (N.φ ⁻¹' A).Finite := by
  have heq : N.φ ⁻¹' A = ⋃ z ∈ A, N.φ ⁻¹' {z} := by
    ext x
    simp
  rw [heq]
  exact hA.biUnion fun z _ => N.finite_preimage_singleton z

/-- Any point `x ∈ bd N.D` whose image `N.φ x` lies outside `bd S ∪ N.seamV` belongs to the
interior of one of the pasted boundary arcs `N.f i` or `N.g i`, so its fiber `N.φ ⁻¹' {N.φ x}` is
a two-point set `{N.f i w, N.g i w}` with `w ∈ Ioo (0 : unitInterval) 1`. -/
theorem exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV [T2Space S] (N : Net S)
    {x : N.D} (hx_bd : x ∈ bd N.D) (hx_not_bdS : N.φ x ∉ bd S) (hx_not_V : N.φ x ∉ N.seamV) :
    ∃ (i : Fin N.r) (w : unitInterval),
      w ∈ Ioo (0 : unitInterval) 1 ∧
      N.φ (N.f i w) = N.φ x ∧
      N.φ ⁻¹' {N.φ x} = {N.f i w, N.g i w} ∧
      N.f i w ≠ N.g i w := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  let M_D : Set N.D := ⋃ i : Fin N.r, (range (N.f i) ∪ range (N.g i))
  have hMD_closed : IsClosed M_D := by
    refine isClosed_iUnion_of_finite fun i => ?_
    exact (isCompact_range (N.f i).continuous).isClosed.union
      (isCompact_range (N.g i).continuous).isClosed
  have hφ_closed : IsClosedMap N.φ := N.quotientMap_φ.continuous.isClosedMap
  let M : Set S := N.φ '' M_D
  have hM_closed : IsClosed M := hφ_closed M_D hMD_closed
  have h_inj_compl : ∀ y ∈ M_Dᶜ, ∀ z : N.D, N.φ y = N.φ z → y = z := by
    intro y hy z hyz
    let R : N.D → N.D → Prop := fun a b =>
      ∃ (j : Fin N.r) (s : unitInterval), a = N.f j s ∧ b = N.g j s
    have hrel : Relation.EqvGen R y z := (N.bd_eq_iff y z).mp hyz
    have hno_step : ∀ a b : N.D, R a b → a ∈ M_D ∧ b ∈ M_D := by
      rintro a b ⟨j, s, rfl, rfl⟩
      exact ⟨mem_iUnion.mpr ⟨j, Or.inl ⟨s, rfl⟩⟩, mem_iUnion.mpr ⟨j, Or.inr ⟨s, rfl⟩⟩⟩
    have heq_of_rel : ∀ a b : N.D, Relation.EqvGen R a b →
        (a ∈ M_Dᶜ ↔ b ∈ M_Dᶜ) ∧ (a ∈ M_Dᶜ → a = b) := by
      intro a b hab
      induction hab with
      | rel u v huv =>
        refine ⟨⟨fun hu => False.elim (hu (hno_step u v huv).1),
          fun hv => False.elim (hv (hno_step u v huv).2)⟩,
          fun hu => False.elim (hu (hno_step u v huv).1)⟩
      | refl _ =>
        exact ⟨Iff.rfl, fun _ => rfl⟩
      | symm _ _ _ ih =>
        exact ⟨ih.1.symm, fun hv => (ih.2 (ih.1.mpr hv)).symm⟩
      | trans _ _ _ _ _ ih1 ih2 =>
        exact ⟨ih1.1.trans ih2.1, fun hu => (ih1.2 hu).trans (ih2.2 (ih1.1.mp hu))⟩
    exact (heq_of_rel y z hrel).2 hy
  have hx_in_MD : x ∈ M_D := by
    by_contra hx_not_MD
    have hx_compl : x ∈ M_Dᶜ := hx_not_MD
    let toFun : (M_Dᶜ : Set N.D) → (Mᶜ : Set S) := fun y =>
      ⟨N.φ y.1, fun ⟨z, hz, hzy⟩ => y.2 (h_inj_compl y.1 y.2 z hzy.symm ▸ hz)⟩
    have hcont : Continuous toFun :=
      (N.quotientMap_φ.continuous.comp continuous_subtype_val).subtype_mk _
    have hinj : Function.Injective toFun := by
      intro y₁ y₂ h12
      ext
      exact h_inj_compl y₁.1 y₁.2 y₂.1 (congr_arg Subtype.val h12)
    have hsurj : Function.Surjective toFun := by
      rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := N.quotientMap_φ.surjective z
      have hy : y ∈ M_Dᶜ := fun hyM => hz ⟨y, hyM, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    have hclosed_map : IsClosedMap toFun := by
      intro F hF
      rw [isClosed_induced_iff] at hF
      rcases hF with ⟨K, hK, rfl⟩
      have hφK_closed : IsClosed (N.φ '' K) := hφ_closed K hK
      have himg_eq : toFun '' (Subtype.val ⁻¹' K) = Subtype.val ⁻¹' (N.φ '' K) := by
        ext ⟨z, hz⟩
        simp only [mem_image, mem_preimage]
        constructor
        · rintro ⟨⟨y, hy⟩, hyK, hyz⟩
          exact ⟨y, hyK, congr_arg Subtype.val hyz⟩
        · rintro ⟨w, hwK, rfl⟩
          have hw_compl : w ∈ M_Dᶜ := fun hwM => hz ⟨w, hwM, rfl⟩
          exact ⟨⟨w, hw_compl⟩, hwK, rfl⟩
      rw [himg_eq]
      exact hφK_closed.preimage continuous_subtype_val
    let e_homeo : (M_Dᶜ : Set N.D) ≃ₜ (Mᶜ : Set S) :=
      (Equiv.ofBijective toFun ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed hcont hclosed_map
    have hemb_S : IsOpenEmbedding (Subtype.val ∘ e_homeo) :=
      hM_closed.isOpen_compl.isOpenEmbedding_subtypeVal.comp e_homeo.isOpenEmbedding
    have hemb_D : IsOpenEmbedding (Subtype.val : (M_Dᶜ : Set N.D) → N.D) :=
      hMD_closed.isOpen_compl.isOpenEmbedding_subtypeVal
    have hint_φx : IsInteriorPoint (N.φ x) := not_not.mp hx_not_bdS
    have hint_sub : IsInteriorPoint (⟨x, hx_compl⟩ : (M_Dᶜ : Set N.D)) :=
      (isInteriorPoint_iff_of_isOpenEmbedding hemb_S).mp hint_φx
    have hint_x : IsInteriorPoint x :=
      isInteriorPoint_of_isOpenEmbedding hemb_D hint_sub
    exact hx_bd hint_x
  simp only [M_D, mem_iUnion, mem_union, mem_range] at hx_in_MD
  obtain ⟨i, w, hφw⟩ : ∃ (i : Fin N.r) (w : unitInterval), N.φ (N.f i w) = N.φ x := by
    rcases hx_in_MD with ⟨i, ⟨w, rfl⟩ | ⟨w, rfl⟩⟩
    · exact ⟨i, w, rfl⟩
    · exact ⟨i, w, N.φ_f_eq_φ_g i w⟩
  have hw_Ioo : w ∈ Ioo (0 : unitInterval) 1 := by
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo w with rfl | rfl | hw
    · exact False.elim (hx_not_V ⟨i, Or.inl hφw⟩)
    · exact False.elim (hx_not_V ⟨i, Or.inr hφw⟩)
    · exact hw
  refine ⟨i, w, hw_Ioo, hφw, ?_, ?_⟩
  · ext y
    simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro hy
      exact N.eq_f_or_g_of_φ_eq_of_mem_Ioo i hw_Ioo (hφw.trans hy.symm)
    · rintro (rfl | rfl)
      · exact hφw
      · exact (N.φ_f_eq_φ_g i w).symm.trans hφw
  · intro hfg
    exact N.internally_disjoint_fg i i w hw_Ioo ⟨w, hfg.symm⟩

/-- Removing two distinct points `x, y` from an `O`-arc `F₀` in a `T2Space` leaves two disjoint
connected components `B₁, B₂`, each of whose closures `Bᵢ ∪ {x, y}` is a line with ends `x, y`. -/
theorem oArc_components_diff_pair {X : Type*} [TopologicalSpace X] [T2Space X]
    {F₀ : Set X} (hF₀ : IsOArc F₀) {x y : X} (hx : x ∈ F₀) (hy : y ∈ F₀) (hxy : x ≠ y) :
    ∃ B₁ B₂ : Set X,
      componentsIn (F₀ \ {x, y}) = {B₁, B₂} ∧
      Disjoint B₁ B₂ ∧
      F₀ \ {x, y} = B₁ ∪ B₂ ∧
      IsLineWithEnds (B₁ ∪ {x, y}) x y ∧
      IsLineWithEnds (B₂ ∪ {x, y}) x y := by
  obtain ⟨φ⟩ := id hF₀
  let a : Circle := φ.symm ⟨x, hx⟩
  let b : Circle := φ.symm ⟨y, hy⟩
  have hab : a ≠ b := by
    intro h
    have h' : (⟨x, hx⟩ : F₀) = ⟨y, hy⟩ := by simpa [a, b] using congrArg φ h
    exact hxy (congrArg Subtype.val h')
  let ι : Circle → X := fun w => (φ w).1
  have hι : Continuous ι := continuous_subtype_val.comp φ.continuous
  have hιinj : Function.Injective ι := fun u w h => φ.injective (Subtype.ext h)
  have hιa : ι a = x := by simp [ι, a]
  have hιb : ι b = y := by simp [ι, b]
  have h_arc_props : ∀ c d : Circle, c ≠ d → (c = a ∧ d = b ∨ c = b ∧ d = a) →
      (∃ w₀ ∈ circleOpenArc c d,
        ι '' circleOpenArc c d = connectedComponentIn (F₀ \ {x, y}) (ι w₀) ∧
        ι w₀ ∈ F₀ \ {x, y}) ∧
      IsLineWithEnds (ι '' circleOpenArc c d ∪ {x, y}) x y := by
    intro c d hcd hor
    have hsub_diff : ι '' circleOpenArc c d ⊆ F₀ \ {x, y} := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨(φ w).2, ?_⟩
      have h₁ : w ∈ ({a, b}ᶜ : Set Circle) := by
        rw [compl_pair_eq_union_circleOpenArc hab]
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl hw
        · exact Or.inr hw
      rintro (h | h)
      · exact h₁ (Or.inl (hιinj (h.trans hιa.symm)))
      · exact h₁ (Or.inr (mem_singleton_iff.mpr (hιinj ((mem_singleton_iff.mp h).trans hιb.symm))))
    have hsub_rev : ι '' circleOpenArc d c ⊆ F₀ \ {x, y} := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨(φ w).2, ?_⟩
      have h₁ : w ∈ ({a, b}ᶜ : Set Circle) := by
        rw [compl_pair_eq_union_circleOpenArc hab]
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr hw
        · exact Or.inl hw
      rintro (h | h)
      · exact h₁ (Or.inl (hιinj (h.trans hιa.symm)))
      · exact h₁ (Or.inr (mem_singleton_iff.mpr (hιinj ((mem_singleton_iff.mp h).trans hιb.symm))))
    let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    have hm_ioo : m ∈ Ioo (0 : unitInterval) 1 :=
      ⟨by change (0 : ℝ) < 1 / 2; norm_num, by change (1 / 2 : ℝ) < 1; norm_num⟩
    let w₀ : Circle := Circle.path c d m
    have hw₀ : w₀ ∈ circleOpenArc c d := ⟨m, hm_ioo, rfl⟩
    have hconn : IsPreconnected (ι '' circleOpenArc c d) :=
      (isPathConnected_circleOpenArc c d).isConnected.isPreconnected.image _ hι.continuousOn
    have h_sub_cc : ι '' circleOpenArc c d ⊆ connectedComponentIn (F₀ \ {x, y}) (ι w₀) :=
      hconn.subset_connectedComponentIn ⟨w₀, hw₀, rfl⟩ hsub_diff
    let K₁ : Set X := range (ι ∘ Circle.path c d)
    let K₂ : Set X := range (ι ∘ Circle.path d c)
    have hK₁_closed : IsClosed K₁ := (isCompact_range (hι.comp (Circle.path c
      d).continuous)).isClosed
    have hK₂_closed : IsClosed K₂ := (isCompact_range (hι.comp (Circle.path d
      c).continuous)).isClosed
    have h_open_in_K₂c : ι '' circleOpenArc c d ⊆ K₂ᶜ := by
      rintro _ ⟨w, hw, rfl⟩ ⟨t, ht⟩
      have hwt : Circle.path d c t = w := hιinj ht
      rw [← compl_range_circlePath hcd.symm] at hw
      exact hw ⟨t, hwt⟩
    have h_rev_in_K₁c : ι '' circleOpenArc d c ⊆ K₁ᶜ := by
      rintro _ ⟨w, hw, rfl⟩ ⟨t, ht⟩
      have hwt : Circle.path c d t = w := hιinj ht
      rw [← compl_range_circlePath hcd] at hw
      exact hw ⟨t, hwt⟩
    have h_diff_union : F₀ \ {x, y} = (ι '' circleOpenArc c d) ∪ (ι '' circleOpenArc d c) := by
      ext p
      constructor
      · rintro ⟨hpF₀, hp_xy⟩
        let w : Circle := φ.symm ⟨p, hpF₀⟩
        have hιw : ι w = p := by simp [ι, w]
        have hw_ab : w ∈ ({a, b}ᶜ : Set Circle) := by
          rintro (h | h)
          · exact hp_xy (Or.inl (by rw [← hιw, h, hιa]))
          · exact hp_xy (Or.inr (mem_singleton_iff.mpr (by rw [← hιw, mem_singleton_iff.mp h,
              hιb])))
        rw [compl_pair_eq_union_circleOpenArc hab] at hw_ab
        rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases hw_ab with h | h
          · exact Or.inl ⟨w, h, hιw⟩
          · exact Or.inr ⟨w, h, hιw⟩
        · rcases hw_ab with h | h
          · exact Or.inr ⟨w, h, hιw⟩
          · exact Or.inl ⟨w, h, hιw⟩
      · rintro (h | h)
        · exact hsub_diff h
        · exact hsub_rev h
    have h_cc_sub : connectedComponentIn (F₀ \ {x, y}) (ι w₀) ⊆ ι '' circleOpenArc c d := by
      intro z hz
      have hz_diff : z ∈ F₀ \ {x, y} := connectedComponentIn_subset _ _ hz
      by_contra hz_not
      have hz_rev : z ∈ ι '' circleOpenArc d c :=
        (h_diff_union ▸ hz_diff).resolve_left hz_not
      have hcov : connectedComponentIn (F₀ \ {x, y}) (ι w₀) ⊆ K₂ᶜ ∪ K₁ᶜ := fun p hp => by
        rcases h_diff_union ▸ connectedComponentIn_subset _ _ hp with h | h
        · exact Or.inl (h_open_in_K₂c h)
        · exact Or.inr (h_rev_in_K₁c h)
      obtain ⟨q, hq_cc, hqK₂, hqK₁⟩ :=
        isPreconnected_connectedComponentIn K₂ᶜ K₁ᶜ hK₂_closed.isOpen_compl hK₁_closed.isOpen_compl
          hcov ⟨ι w₀, mem_connectedComponentIn (hsub_diff ⟨w₀, hw₀, rfl⟩), h_open_in_K₂c ⟨w₀, hw₀,
            rfl⟩⟩
          ⟨z, hz, h_rev_in_K₁c hz_rev⟩
      rcases h_diff_union ▸ connectedComponentIn_subset _ _ hq_cc with ⟨w, ⟨t, _, rfl⟩, rfl⟩ | ⟨w,
        ⟨t, _, rfl⟩, rfl⟩
      · exact hqK₁ ⟨t, rfl⟩
      · exact hqK₂ ⟨t, rfl⟩
    have h_eq_cc : ι '' circleOpenArc c d = connectedComponentIn (F₀ \ {x, y}) (ι w₀) :=
      Subset.antisymm h_sub_cc h_cc_sub
    have h_line_cd : IsLineWithEnds (ι '' circleOpenArc c d ∪ {ι c, ι d}) (ι c) (ι d) := by
      have heq_range : ι '' circleOpenArc c d ∪ {ι c, ι d} = range (ι ∘ Circle.path c d) := by
        ext p
        constructor
        · rintro (⟨w, ⟨t, ht, rfl⟩, rfl⟩ | (rfl | hp))
          · exact ⟨t, rfl⟩
          · exact ⟨0, by simp⟩
          · rw [mem_singleton_iff.mp hp]
            exact ⟨1, by simp⟩
        · rintro ⟨t, rfl⟩
          by_cases ht0 : t = 0
          · subst ht0; exact Or.inr (Or.inl (by simp))
          · by_cases ht1 : t = 1
            · subst ht1; exact Or.inr (Or.inr (by simp))
            · exact Or.inl ⟨Circle.path c d t, ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
                unitInterval.lt_one_iff_ne_one.mpr ht1⟩, rfl⟩, rfl⟩
      rw [heq_range]
      have h_inj : Function.Injective (ι ∘ Circle.path c d) :=
        hιinj.comp (Circle.path_injective_of_ne hcd)
      have hemb : IsEmbedding (ι ∘ Circle.path c d) :=
        ((hι.comp (Circle.path c d).continuous).isClosedEmbedding h_inj).isEmbedding
      exact ⟨hemb.toHomeomorph, by simp, by simp⟩
    refine ⟨⟨w₀, hw₀, h_eq_cc, hsub_diff ⟨w₀, hw₀, rfl⟩⟩, ?_⟩
    rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rwa [hιa, hιb] at h_line_cd
    · rw [hιa, hιb, pair_comm y x] at h_line_cd
      exact h_line_cd.symm
  obtain ⟨⟨w₁, hw₁, hB₁_cc, hw₁_diff⟩, hB₁_line⟩ := h_arc_props a b hab (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨⟨w₂, hw₂, hB₂_cc, hw₂_diff⟩, hB₂_line⟩ := h_arc_props b a hab.symm (Or.inr ⟨rfl, rfl⟩)
  let B₁ := ι '' circleOpenArc a b
  let B₂ := ι '' circleOpenArc b a
  have h_disj : Disjoint B₁ B₂ :=
    (disjoint_circleOpenArc hab).image hιinj.injOn (subset_univ _) (subset_univ _)
  have h_diff_union : F₀ \ {x, y} = B₁ ∪ B₂ := by
    ext p
    constructor
    · rintro ⟨hpF₀, hp_xy⟩
      let w : Circle := φ.symm ⟨p, hpF₀⟩
      have hιw : ι w = p := by simp [ι, w]
      have hw_ab : w ∈ ({a, b}ᶜ : Set Circle) := by
        rintro (h | h)
        · exact hp_xy (Or.inl (by rw [← hιw, h, hιa]))
        · exact hp_xy (Or.inr (mem_singleton_iff.mpr (by rw [← hιw, mem_singleton_iff.mp h, hιb])))
      rw [compl_pair_eq_union_circleOpenArc hab] at hw_ab
      rcases hw_ab with h | h
      · exact Or.inl ⟨w, h, hιw⟩
      · exact Or.inr ⟨w, h, hιw⟩
    · rintro (h | h)
      · dsimp only [B₁] at h
        rw [hB₁_cc] at h
        exact connectedComponentIn_subset _ _ h
      · dsimp only [B₂] at h
        rw [hB₂_cc] at h
        exact connectedComponentIn_subset _ _ h
  refine ⟨B₁, B₂, ?_, h_disj, h_diff_union, hB₁_line, hB₂_line⟩
  ext C
  simp only [componentsIn, mem_image, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases h_diff_union ▸ hz with hz₁ | hz₂
    · left
      dsimp only [B₁]
      rw [hB₁_cc]
      exact (connectedComponentIn_eq (hB₁_cc ▸ hz₁)).symm
    · right
      dsimp only [B₂]
      rw [hB₂_cc]
      exact (connectedComponentIn_eq (hB₂_cc ▸ hz₂)).symm
  · rintro (rfl | rfl)
    · exact ⟨ι w₁, hw₁_diff, hB₁_cc.symm⟩
    · exact ⟨ι w₂, hw₂_diff, hB₂_cc.symm⟩

/-- The boundary `bd N.D` of the disc of a net `N` is an `O`-arc. -/
theorem isOArc_bd_D (N : Net S) : IsOArc (bd N.D) := by
  have heq : discBd (univ : Set N.D) = bd N.D := image_bd_homeomorph (Homeomorph.Set.univ N.D)
  exact heq ▸ N.isClosedDisc_D.isOArc_discBd

/-- The open part of the unit interval is path connected. -/
theorem unitInterval_interior_isPathConnected :
    IsPathConnected (Ioo (0 : unitInterval) 1) := by
  have heq : projIcc (0 : ℝ) 1 zero_le_one '' Ioo (0 : ℝ) 1 = Ioo (0 : unitInterval) 1 := by
    ext x
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨r, ⟨hr0, hr1⟩, rfl⟩
      have hval : (projIcc (0 : ℝ) 1 zero_le_one r : ℝ) = r :=
        congr_arg Subtype.val (projIcc_of_mem zero_le_one ⟨hr0.le, hr1.le⟩)
      exact ⟨Subtype.coe_lt_coe.mp (by simpa [hval] using hr0),
        Subtype.coe_lt_coe.mp (by simpa [hval] using hr1)⟩
    · rintro ⟨hx0, hx1⟩
      refine ⟨x.1, ⟨Subtype.coe_lt_coe.mpr hx0, Subtype.coe_lt_coe.mpr hx1⟩, ?_⟩
      exact projIcc_val zero_le_one x
  rw [← heq]
  exact ((convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num, by norm_num⟩).image
    continuous_projIcc

/-- The open unit interval is dense in the closed unit interval. -/
theorem unitInterval_interior_closure : closure (Ioo (0 : unitInterval) 1) = univ := by
  rw [closure_Ioo zero_ne_one]
  exact eq_univ_of_forall fun t => ⟨unitInterval.nonneg t, unitInterval.le_one t⟩

/-- For any net `N`, `i : Fin N.r`, and preconnected subset `U ⊆ bd N.D` avoiding `N.f i 0` and
`N.f i 1`, if `U` contains `N.f i t` for some `t ∈ Ioo (0 : unitInterval) 1`, then
`U ⊆ N.f i '' Ioo (0 : unitInterval) 1` (and hence `N.g i t ∉ U`). -/
theorem subset_image_Ioo_f_of_isPreconnected (N : Net S) (i : Fin N.r) {U : Set N.D}
    (hU_conn : IsPreconnected U) (hU_bd : U ⊆ bd N.D)
    (hf0 : N.f i 0 ∉ U) (hf1 : N.f i 1 ∉ U)
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) (htU : N.f i t ∈ U) :
    U ⊆ N.f i '' Ioo (0 : unitInterval) 1 ∧ N.g i t ∉ U := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hOArc : IsOArc (bd N.D) := N.isOArc_bd_D
  have hf0_bd : N.f i 0 ∈ bd N.D := N.range_f_subset_bd i ⟨0, rfl⟩
  have hf1_bd : N.f i 1 ∈ bd N.D := N.range_f_subset_bd i ⟨1, rfl⟩
  have hf01_ne : N.f i 0 ≠ N.f i 1 := fun h => zero_ne_one (N.injective_f i h)
  obtain ⟨B₁, B₂, hcomp, hdisj, hunion, hline₁, hline₂⟩ :=
    oArc_components_diff_pair hOArc hf0_bd hf1_bd hf01_ne
  have hIoo_pc : IsPathConnected (Ioo (0 : unitInterval) 1) := by
    exact unitInterval_interior_isPathConnected
  have hfIoo_conn : IsPreconnected (N.f i '' Ioo (0 : unitInterval) 1) :=
    (hIoo_pc.image (N.f i).continuous).isConnected.isPreconnected
  have hfIoo_sub : N.f i '' Ioo (0 : unitInterval) 1 ⊆ bd N.D \ {N.f i 0, N.f i 1} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨N.range_f_subset_bd i ⟨s, rfl⟩, ?_⟩
    rintro (h0 | h1)
    · exact hs.1.ne (N.injective_f i h0).symm
    · exact hs.2.ne (N.injective_f i (mem_singleton_iff.mp h1))
  let B := connectedComponentIn (bd N.D \ {N.f i 0, N.f i 1}) (N.f i t)
  have hB_mem : B ∈ componentsIn (bd N.D \ {N.f i 0, N.f i 1}) :=
    ⟨N.f i t, hfIoo_sub ⟨t, ht, rfl⟩, rfl⟩
  rw [hcomp] at hB_mem
  have hB_line : IsLineWithEnds (B ∪ {N.f i 0, N.f i 1}) (N.f i 0) (N.f i 1) := by
    rcases hB_mem with rfl | rfl
    · exact hline₁
    · exact hline₂
  have hfIoo_sub_B : N.f i '' Ioo (0 : unitInterval) 1 ⊆ B :=
    hfIoo_conn.subset_connectedComponentIn ⟨t, ht, rfl⟩ hfIoo_sub
  have hrange_sub : range (N.f i) ⊆ B ∪ {N.f i 0, N.f i 1} := by
    rintro _ ⟨s, rfl⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (hfIoo_sub_B ⟨s, hs, rfl⟩)
  have hrange_eq : range (N.f i) = B ∪ {N.f i 0, N.f i 1} :=
    hB_line.eq_of_subset (isPreconnected_range (N.f i).continuous) hrange_sub ⟨0, rfl⟩ ⟨1, rfl⟩
  have hB_sub_fIoo : B ⊆ N.f i '' Ioo (0 : unitInterval) 1 := by
    intro y hy
    have hy_diff : y ∈ bd N.D \ {N.f i 0, N.f i 1} := connectedComponentIn_subset _ _ hy
    have hy_range : y ∈ range (N.f i) := hrange_eq ▸ Or.inl hy
    rcases hy_range with ⟨s, rfl⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
    · exact False.elim (hy_diff.2 (Or.inl rfl))
    · exact False.elim (hy_diff.2 (Or.inr rfl))
    · exact ⟨s, hs, rfl⟩
  have hU_sub_diff : U ⊆ bd N.D \ {N.f i 0, N.f i 1} := by
    intro y hy
    refine ⟨hU_bd hy, ?_⟩
    rintro (rfl | h1)
    · exact hf0 hy
    · exact hf1 (mem_singleton_iff.mp h1 ▸ hy)
  have hU_sub_B : U ⊆ B := hU_conn.subset_connectedComponentIn htU hU_sub_diff
  have hU_sub_fIoo : U ⊆ N.f i '' Ioo (0 : unitInterval) 1 := hU_sub_B.trans hB_sub_fIoo
  refine ⟨hU_sub_fIoo, fun hgU => ?_⟩
  rcases hU_sub_fIoo hgU with ⟨s, hs, hsg⟩
  exact N.internally_disjoint_fg i i s hs ⟨t, hsg.symm⟩

/-- On any preconnected subset `U ⊆ bd N.D` disjoint from `N.φ ⁻¹' N.seamV`, `N.φ` is injective. -/
theorem injOn_φ_of_isPreconnected (N : Net S) {U : Set N.D}
    (hU_conn : IsPreconnected U) (hU_bd : U ⊆ bd N.D) (hU_V : Disjoint U (N.φ ⁻¹' N.seamV)) :
    InjOn N.φ U := by
  intro x hx y hy hxy
  by_contra hne
  let R : N.D → N.D → Prop := fun a b =>
    ∃ (j : Fin N.r) (s : unitInterval), a = N.f j s ∧ b = N.g j s
  have hrel : Relation.EqvGen R x y := (N.bd_eq_iff x y).mp hxy
  have hex_step : ∃ (i : Fin N.r) (t : unitInterval), N.φ (N.f i t) = N.φ x := by
    by_contra! hno
    have heq_of_rel : ∀ a b : N.D, Relation.EqvGen R a b → (N.φ a = N.φ x → a = b) := by
      intro a b hab
      induction hab with
      | rel u v huv =>
        intro hu
        rcases huv with ⟨i, t, rfl, rfl⟩
        exact False.elim (hno i t hu)
      | refl _ =>
        intro _
        rfl
      | symm u v huv ih =>
        intro hv
        have huv_φ : N.φ u = N.φ v := (N.bd_eq_iff u v).mpr huv
        exact (ih (huv_φ.trans hv)).symm
      | trans u w v huw _ ih1 ih2 =>
        intro hu
        have huw_φ : N.φ u = N.φ w := (N.bd_eq_iff u w).mpr huw
        exact (ih1 hu).trans (ih2 (huw_φ.symm.trans hu))
    exact hne (heq_of_rel x y hrel rfl)
  rcases hex_step with ⟨i, t, hφt⟩
  have hx_not_V : N.φ x ∉ N.seamV := Disjoint.notMem_of_mem_left hU_V hx
  have ht : t ∈ Ioo (0 : unitInterval) 1 := by
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · exact False.elim (hx_not_V ⟨i, Or.inl hφt⟩)
    · exact False.elim (hx_not_V ⟨i, Or.inr hφt⟩)
    · exact ht
  have hx_fg := N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht hφt
  have hy_fg := N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht (hφt.trans hxy)
  have hf_in_U : N.f i t ∈ U := by
    rcases hx_fg with rfl | rfl
    · exact hx
    · rcases hy_fg with rfl | rfl
      · exact hy
      · exact False.elim (hne rfl)
  have hg_in_U : N.g i t ∈ U := by
    rcases hx_fg with rfl | rfl
    · rcases hy_fg with rfl | rfl
      · exact False.elim (hne rfl)
      · exact hy
    · exact hx
  have hf0_not_U : N.f i 0 ∉ U := fun h =>
    Disjoint.notMem_of_mem_left hU_V h ⟨i, Or.inl rfl⟩
  have hf1_not_U : N.f i 1 ∉ U := fun h =>
    Disjoint.notMem_of_mem_left hU_V h ⟨i, Or.inr rfl⟩
  exact (N.subset_image_Ioo_f_of_isPreconnected i hU_conn hU_bd hf0_not_U hf1_not_U ht hf_in_U).2
    hg_in_U

/-- Every seam graph `J` for a net `N` has no isolated vertices.
Graph Minors VII, Section 2, proof of (2.1) and (2.3) (pages 215–217):
"Certainly $J$ has no isolated vertices." -/
theorem hasNoIsolatedVertices_seamGraph (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) : HasNoIsolatedVertices J := by
  intro v hv
  rw [hJ.2.2] at hv
  rcases hv with ⟨i, hi⟩
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have hsub : (N.φ ∘ N.f i) '' Ioo (0 : unitInterval) 1 ⊆ J.U \ J.V := by
    rintro z ⟨t, ht, rfl⟩
    rw [hJ.2.1, hJ.2.2]
    exact ⟨⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩, N.notMem_seamV_of_mem_Ioo i ht⟩
  have hz₀ : N.φ (N.f i t₀) ∈ J.U \ J.V := hsub ⟨t₀, ht₀, rfl⟩
  let e := pathComponentIn (J.U \ J.V) (N.φ (N.f i t₀))
  have heE : e ∈ J.E := pathComponentIn_mem_arcComponentsIn hz₀
  have hIoo_pc := Net.unitInterval_interior_isPathConnected
  have himg_pc : IsPathConnected ((N.φ ∘ N.f i) '' Ioo (0 : unitInterval) 1) :=
    hIoo_pc.image (N.quotientMap_φ.continuous.comp (N.f i).continuous)
  have himg_sub_e : (N.φ ∘ N.f i) '' Ioo (0 : unitInterval) 1 ⊆ e :=
    himg_pc.subset_pathComponentIn ⟨t₀, ht₀, rfl⟩ hsub
  have hrange_sub_cl : range (N.φ ∘ N.f i) ⊆ closure e := by
    rw [← image_univ, ← Net.unitInterval_interior_closure]
    exact (image_closure_subset_closure_image
      (N.quotientMap_φ.continuous.comp (N.f i).continuous)).trans (closure_mono himg_sub_e)
  refine ⟨e, heE, ?_⟩
  rw [Drawing.VertexIncident]
  refine ⟨?_, Or.inl heE, ?_⟩
  · rw [hJ.2.2]
    exact ⟨i, hi⟩
  · rcases hi with rfl | rfl
    · exact hrange_sub_cl ⟨0, rfl⟩
    · exact hrange_sub_cl ⟨1, rfl⟩

end Net

/-- The empty drawing `emptyDrawing S` (`U = ∅`, `V = ∅`) is never a seam graph for any net,
because every net `N` with `0 < N.r` has `N.seamV.Nonempty`. In particular, on the sphere
`S = SurfaceModel 0 0 0`, `emptyDrawing S` satisfies conditions (i)–(iv) of (2.1) (page 215)
without being a seam graph. -/
theorem not_isSeamGraph_emptyDrawing : ¬ IsSeamGraph (emptyDrawing S) := by
  rintro ⟨N, hpos, _, hV⟩
  have h0 : N.φ (N.f ⟨0, hpos⟩ 0) ∈ (emptyDrawing S).V := by
    rw [hV]
    exact ⟨⟨0, hpos⟩, Or.inl rfl⟩
  exact h0

/-! ## 2. Handshaking lemma and model bounds -/

/-- For every edge `e ∈ J.E` of a drawing `J`, `tilde e = closure e ∩ J.V`. -/
theorem tilde_eq_closure_inter_V (J : Drawing S) {e : Set S} (he : e ∈ J.E) :
    tilde e = closure e ∩ J.V := by
  have hdiff : closure e \ J.V = e := J.closure_diff_V he
  ext x
  simp only [tilde, mem_sdiff, mem_inter_iff]
  constructor
  · rintro ⟨hxcl, hxe⟩
    refine ⟨hxcl, ?_⟩
    by_contra hxV
    exact hxe (hdiff ▸ ⟨hxcl, hxV⟩)
  · rintro ⟨hxcl, hxV⟩
    refine ⟨hxcl, ?_⟩
    intro hxe
    rw [← hdiff] at hxe
    exact hxe.2 hxV

/-- Every edge `e ∈ J.E` of a drawing `J` in a `T1Space` has `(tilde e).ncard = 2` (a non-loop edge)
or `(tilde e).ncard = 1` (a loop edge). -/
theorem ncard_tilde_of_mem_E (J : Drawing S) {e : Set S} (he : e ∈ J.E) :
    (tilde e).ncard = 2 ∨ (tilde e).ncard = 1 := by
  rw [tilde_eq_closure_inter_V J he]
  rcases J.edge_cond e he with ⟨u, v, huv, hcap, -⟩ | ⟨u, hcap, -⟩
  · left
    rw [hcap, ncard_pair huv]
  · right
    rw [hcap, ncard_singleton]

/-- For `v ∈ J.V` and `e ∈ J.E`, `J.VertexIncident v e` holds if and only if `v ∈ tilde e`. -/
theorem vertexIncident_iff_mem_tilde (J : Drawing S) {v : S} (hv : v ∈ J.V)
    {e : Set S} (he : e ∈ J.E) :
    J.VertexIncident v e ↔ v ∈ tilde e := by
  rw [tilde_eq_closure_inter_V J he]
  simp [Drawing.VertexIncident, hv, he]

/-- The handshaking lemma for drawings: the sum of `vertexValency J v` over all `v ∈ J.V` equals
`2 * J.E.ncard`. -/
theorem sum_vertexValency_eq_two_mul_ncard_E (J : Drawing S) :
    ∑ v ∈ J.finite_V.toFinset, vertexValency J v = 2 * J.E.ncard := by
  classical
  let V_fin := J.finite_V.toFinset
  let E_fin := J.finite_edges.toFinset
  let E₂ := E_fin.filter (fun e => (tilde e).ncard = 2)
  let E₁ := E_fin.filter (fun e => (tilde e).ncard = 1)
  have hV_mem : ∀ v, v ∈ V_fin ↔ v ∈ J.V := fun v => Finite.mem_toFinset _
  have hE_mem : ∀ e, e ∈ E_fin ↔ e ∈ J.E := fun e => Finite.mem_toFinset _
  have hval_eq : ∀ v ∈ V_fin,
      vertexValency J v =
        (E₂.filter (fun e => v ∈ tilde e)).card + 2 * (E₁.filter (fun e => v ∈ tilde e)).card := by
    intro v hv
    have hvV : v ∈ J.V := (hV_mem v).mp hv
    have hset2 : {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 2} =
        ↑(E₂.filter (fun e => v ∈ tilde e)) := by
      ext e
      simp only [mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, E₂, hE_mem]
      constructor
      · rintro ⟨he, hinc, hcard⟩
        exact ⟨⟨he, hcard⟩, (vertexIncident_iff_mem_tilde J hvV he).mp hinc⟩
      · rintro ⟨⟨he, hcard⟩, hvtilde⟩
        exact ⟨he, (vertexIncident_iff_mem_tilde J hvV he).mpr hvtilde, hcard⟩
    have hset1 : {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1} =
        ↑(E₁.filter (fun e => v ∈ tilde e)) := by
      ext e
      simp only [mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, E₁, hE_mem]
      constructor
      · rintro ⟨he, hinc, hcard⟩
        exact ⟨⟨he, hcard⟩, (vertexIncident_iff_mem_tilde J hvV he).mp hinc⟩
      · rintro ⟨⟨he, hcard⟩, hvtilde⟩
        exact ⟨he, (vertexIncident_iff_mem_tilde J hvV he).mpr hvtilde, hcard⟩
    unfold vertexValency
    rw [hset2, hset1, ncard_coe_finset, ncard_coe_finset]
  have htilde_eq : ∀ e ∈ E_fin,
      (V_fin.filter (fun v => v ∈ tilde e)).card = (tilde e).ncard := by
    intro e he
    have heE : e ∈ J.E := (hE_mem e).mp he
    have hsub : tilde e = ↑(V_fin.filter (fun v => v ∈ tilde e)) := by
      ext v
      simp only [Finset.mem_coe, Finset.mem_filter, hV_mem]
      constructor
      · intro hv
        have hv' := hv
        rw [tilde_eq_closure_inter_V J heE] at hv'
        exact ⟨hv'.2, hv⟩
      · exact And.right
    conv_rhs => rw [hsub, ncard_coe_finset]
  have hsum2 : ∑ v ∈ V_fin, (E₂.filter (fun e => v ∈ tilde e)).card = 2 * E₂.card := by
    calc
      ∑ v ∈ V_fin, (E₂.filter (fun e => v ∈ tilde e)).card
        = ∑ v ∈ V_fin, ∑ e ∈ E₂, if v ∈ tilde e then 1 else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.card_filter]
      _ = ∑ e ∈ E₂, ∑ v ∈ V_fin, if v ∈ tilde e then 1 else 0 := Finset.sum_comm
      _ = ∑ e ∈ E₂, (V_fin.filter (fun v => v ∈ tilde e)).card := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.card_filter]
      _ = ∑ e ∈ E₂, 2 := by
          refine Finset.sum_congr rfl fun e he => ?_
          have heFin : e ∈ E_fin := (Finset.mem_filter.mp he).1
          have he2 : (tilde e).ncard = 2 := (Finset.mem_filter.mp he).2
          rw [htilde_eq e heFin, he2]
      _ = 2 * E₂.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum1 : ∑ v ∈ V_fin, (E₁.filter (fun e => v ∈ tilde e)).card = E₁.card := by
    calc
      ∑ v ∈ V_fin, (E₁.filter (fun e => v ∈ tilde e)).card
        = ∑ v ∈ V_fin, ∑ e ∈ E₁, if v ∈ tilde e then 1 else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.card_filter]
      _ = ∑ e ∈ E₁, ∑ v ∈ V_fin, if v ∈ tilde e then 1 else 0 := Finset.sum_comm
      _ = ∑ e ∈ E₁, (V_fin.filter (fun v => v ∈ tilde e)).card := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.card_filter]
      _ = ∑ e ∈ E₁, 1 := by
          refine Finset.sum_congr rfl fun e he => ?_
          have heFin : e ∈ E_fin := (Finset.mem_filter.mp he).1
          have he1 : (tilde e).ncard = 1 := (Finset.mem_filter.mp he).2
          rw [htilde_eq e heFin, he1]
      _ = E₁.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hpart : E₂.card + E₁.card = J.E.ncard := by
    have hdisj : Disjoint E₂ E₁ := by
      rw [Finset.disjoint_filter]
      intro e _ h2 h1
      omega
    have hunion : E₂ ∪ E₁ = E_fin := by
      ext e
      simp only [Finset.mem_union, Finset.mem_filter, E₂, E₁]
      constructor
      · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
      · intro he
        rcases ncard_tilde_of_mem_E J ((hE_mem e).mp he) with h2 | h1
        · exact Or.inl ⟨he, h2⟩
        · exact Or.inr ⟨he, h1⟩
    have hcard_E : E_fin.card = J.E.ncard := by
      have : (J.E : Set (Set S)) = ↑E_fin := by
        ext e; simp [hE_mem]
      rw [this, ncard_coe_finset]
    rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard_E]
  calc
    ∑ v ∈ V_fin, vertexValency J v
      = ∑ v ∈ V_fin,
          ((E₂.filter (fun e => v ∈ tilde e)).card +
            2 * (E₁.filter (fun e => v ∈ tilde e)).card) :=
        Finset.sum_congr rfl hval_eq
    _ = (∑ v ∈ V_fin, (E₂.filter (fun e => v ∈ tilde e)).card) +
          2 * ∑ v ∈ V_fin, (E₁.filter (fun e => v ∈ tilde e)).card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * E₂.card + 2 * E₁.card := by rw [hsum2, hsum1]
    _ = 2 * (E₂.card + E₁.card) := by ring
    _ = 2 * J.E.ncard := by rw [hpart]

/-- In any drawing `J` where every vertex has valency at least `3`, `3 * J.V.ncard ≤ 2 * J.E.ncard`.
Graph Minors VII, proof of (2.2) (page 216):
"But every vertex of $J$ in $\Sigma'$ has valency $\ge 3$, and so $|V(J)| \le \frac{2}{3} |E(J)|$."
-/
theorem three_mul_ncard_V_le_two_mul_ncard_E (J : Drawing S)
    (hval : ∀ v ∈ J.V, 3 ≤ vertexValency J v) :
    3 * J.V.ncard ≤ 2 * J.E.ncard := by
  let V_fin := J.finite_V.toFinset
  have hcard_V : V_fin.card = J.V.ncard := by
    have : J.V = ↑V_fin := by ext v; simp [V_fin]
    rw [this, ncard_coe_finset]
  calc
    3 * J.V.ncard = V_fin.card * 3 := by rw [hcard_V, mul_comm]
    _ = ∑ _v ∈ V_fin, 3 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ V_fin, vertexValency J v := by
        refine Finset.sum_le_sum fun v hv => hval v ((Finite.mem_toFinset _).mp hv)
    _ = 2 * J.E.ncard := sum_vertexValency_eq_two_mul_ncard_E J

/-- If `S ≃ₜ SurfaceModel a b c` with `2 * a + b + c > 1`, then `S` is connected and not
homeomorphic to `SurfaceModel 0 0 0`, `SurfaceModel 0 0 1`, or `SurfaceModel 0 1 0`. -/
theorem not_homeo_small_models_of_gt_one {a b c : ℕ} (habc : 2 * a + b + c > 1)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) :
    ConnectedSpace S ∧
    ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 0) ∧
    ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 1) ∧
    ¬ Nonempty (S ≃ₜ SurfaceModel 0 1 0) := by
  rcases he with ⟨e⟩
  have : ConnectedSpace (SurfaceModel a b c) := (modelCriterion.1 a b c).2
  have hconn : ConnectedSpace S := e.symm.surjective.connectedSpace e.symm.continuous
  refine ⟨hconn, ?_, ?_, ?_⟩
  · rintro ⟨e0⟩
    have hcrit := (modelCriterion.2 a b c 0 0 0).mp ⟨e.symm.trans e0⟩
    omega
  · rintro ⟨e1⟩
    have hcrit := (modelCriterion.2 a b c 0 0 1).mp ⟨e.symm.trans e1⟩
    omega
  · rintro ⟨e2⟩
    have hcrit := (modelCriterion.2 a b c 0 1 0).mp ⟨e.symm.trans e2⟩
    omega

/-! ## 3. Augmented seam paths ((2.5)) -/

/-- Filtering out all occurrences of `x` from a list `L` reduces `L.countP p` by
`if p x then L.count x else 0`. -/
private theorem countP_filter_ne_add {β : Type*} [DecidableEq β] (L : List β) (p : β → Bool)
    (x : β) :
    (L.filter (· != x)).countP p + (if p x then L.count x else 0) = L.countP p := by
  induction L with
  | nil => simp
  | cons a as ih =>
    by_cases hax : a = x
    · subst hax
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.count_cons_self, List.countP_cons, ← ih]
      split_ifs with hpa <;> omega
    · have hne : (a != x) = true := bne_iff_ne.mpr hax
      simp only [List.filter_cons, hne, ↓reduceIte, List.count_cons_of_ne hax,
        List.countP_cons, ← ih]
      split_ifs with hpa <;> omega

/-- Filtering out all occurrences of `x` from a list `L` leaves `count y` unchanged for `y ≠ x`
and `0` for `y = x`. -/
private theorem count_filter_ne {β : Type*} [DecidableEq β] (L : List β) (x y : β) :
    (L.filter (· != x)).count y = if y = x then 0 else L.count y := by
  induction L with
  | nil => simp
  | cons a as ih =>
    by_cases hax : a = x
    · subst hax
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih]
      split_ifs with hyx
      · rfl
      · rw [List.count_cons_of_ne (Ne.symm hyx)]
    · have hne : (a != x) = true := bne_iff_ne.mpr hax
      simp only [List.filter_cons, hne, ↓reduceIte]
      by_cases hya : y = a
      · subst hya
        simp [hax, List.count_cons_self, ih]
      · rw [List.count_cons_of_ne (Ne.symm hya), List.count_cons_of_ne (Ne.symm hya), ih]

/-- If every element `e` of `L` satisfying `p e = true` occurs an even number of times in `L`, then
`L.countP p` is even. -/
private theorem even_countP_of_forall_even_count {β : Type*} [DecidableEq β] :
    ∀ (n : ℕ) (L : List β) (p : β → Bool), L.length ≤ n →
      (∀ e, p e = true → Even (L.count e)) → Even (L.countP p)
  | 0, L, p, hlen, _ => by
    have hnil : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    simp
  | n + 1, [], p, _, _ => by simp
  | n + 1, a :: as, p, hlen, heven => by
    let L := a :: as
    let L' := L.filter (· != a)
    have hlen' : L'.length ≤ n := by
      have hsub : L' = as.filter (· != a) := by
        simp [L', L]
      rw [hsub]
      exact (List.length_filter_le _ as).trans (by simpa [L] using hlen)
    have heven' : ∀ e, p e = true → Even (L'.count e) := by
      intro e hpe
      rw [count_filter_ne L a e]
      split_ifs with hea
      · exact Even.zero
      · exact heven e hpe
    have ih := even_countP_of_forall_even_count n L' p hlen' heven'
    have hsum := countP_filter_ne_add L p a
    rw [← hsum]
    refine ih.add ?_
    split_ifs with hpa
    · exact heven a hpa
    · exact Even.zero

/-- In any multigraph `G`, if there is a walk `W₀` from `a` to `b`, then there is a walk `P` from
`a` to `b` every edge of which occurs an odd number of times in `W₀.edges`. -/
theorem GraphWalk.exists_odd_count_walk {α : Type u} {β : Type*} [DecidableEq β]
    {G : Graph α β} {a b : α} (W₀ : GraphWalk G a b) :
    ∃ P : GraphWalk G a b, ∀ e ∈ P.edges, Odd (W₀.edges.count e) := by
  classical
  let ReachOdd (x : α) : Prop :=
    ∃ P : GraphWalk G a x, ∀ e ∈ P.edges, Odd (W₀.edges.count e)
  let Cross (e : β) : Prop :=
    ∃ u v : α, G.IsLink e u v ∧ ReachOdd u ∧ ¬ ReachOdd v
  have hReach_step : ∀ {e u v}, G.IsLink e u v → Odd (W₀.edges.count e) →
      ReachOdd u → ReachOdd v := by
    rintro e u v huv hodd ⟨P, hP⟩
    refine ⟨P.append (.cons huv (.nil huv.right_mem)), ?_⟩
    intro e' he'
    rw [GraphWalk.edges_append, GraphWalk.edges_cons, GraphWalk.edges_nil,
      List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact hP e' he'
    · exact hodd
  have hCross_even : ∀ e, decide (Cross e) = true → Even (W₀.edges.count e) := by
    intro e he
    rw [decide_eq_true_iff] at he
    rcases he with ⟨u, v, huv, hu, hnv⟩
    rw [← Nat.not_odd_iff_even]
    intro hodd
    exact hnv (hReach_step huv hodd hu)
  have hCross_iff : ∀ {e u v}, G.IsLink e u v → (Cross e ↔ ¬ (ReachOdd u ↔ ReachOdd v)) := by
    intro e u v huv
    constructor
    · rintro ⟨u', v', hu'v', hu', hnv'⟩ hiff
      rcases huv.eq_and_eq_or_eq_and_eq hu'v' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnv' (hiff.mp hu')
      · exact hnv' (hiff.mpr hu')
    · intro hnot
      by_cases hu : ReachOdd u
      · have hnv : ¬ ReachOdd v := fun hv => hnot ⟨fun _ => hv, fun _ => hu⟩
        exact ⟨u, v, huv, hu, hnv⟩
      · have hv : ReachOdd v := by
          by_contra hnv
          exact hnot ⟨fun h => False.elim (hu h), fun h => False.elim (hnv h)⟩
        exact ⟨v, u, huv.symm, hv, hu⟩
  have hprop_odd : ∀ (P Q R : Prop) (n : ℕ),
      ¬ (P ↔ Q) → ((Q ↔ R) ↔ Even n) → ((P ↔ R) ↔ Even (n + 1)) := by
    intro P Q R n hPQ hQR
    rw [Nat.even_add_one, ← hQR]
    tauto
  have hprop_even : ∀ (P Q R : Prop) (n : ℕ),
      (P ↔ Q) → ((Q ↔ R) ↔ Even n) → ((P ↔ R) ↔ Even n) := by
    intro P Q R n hPQ hQR
    rw [← hQR]
    tauto
  have hwalk_parity : ∀ {u v : α} (W : GraphWalk G u v),
      (ReachOdd u ↔ ReachOdd v) ↔ Even (W.edges.countP (fun e => decide (Cross e))) := by
    intro u v W
    induction W with
    | nil _ => simp
    | @cons x y z e hxy r ih =>
      rw [GraphWalk.edges_cons, List.countP_cons]
      have hce := hCross_iff hxy
      by_cases hc : Cross e
      · have hdec : decide (Cross e) = true := decide_eq_true hc
        rw [hdec, ite_eq_left rfl]
        exact hprop_odd (ReachOdd x) (ReachOdd y) (ReachOdd z) _ (hce.mp hc) ih
      · have hdec : decide (Cross e) = false := decide_eq_false hc
        have hxy_iff : ReachOdd x ↔ ReachOdd y := Decidable.of_not_not (mt hce.mpr hc)
        rw [hdec, ite_eq_right Bool.false_ne_true, add_zero]
        exact hprop_even (ReachOdd x) (ReachOdd y) (ReachOdd z) _ hxy_iff ih
  have heven_W₀ : Even (W₀.edges.countP (fun e => decide (Cross e))) :=
    even_countP_of_forall_even_count W₀.edges.length W₀.edges _ le_rfl hCross_even
  have ha_mem : a ∈ G.vertexSet := by
    cases W₀ with
    | nil h => exact h
    | cons h _ => exact h.left_mem
  have ha : ReachOdd a := ⟨.nil ha_mem, by simp⟩
  exact ((hwalk_parity W₀).mpr heven_W₀).mp ha

/-- A continuous injective map on `Ioo (0 : ℝ) 1` into `ℝ` has open image in `ℝ`. -/
private theorem isOpen_image_Ioo_of_continuousOn_injOn {ψ : ℝ → ℝ}
    (hcont : ContinuousOn ψ (Ioo (0 : ℝ) 1)) (hinj : InjOn ψ (Ioo (0 : ℝ) 1)) :
    IsOpen (ψ '' Ioo (0 : ℝ) 1) := by
  rw [ isOpen_iff_mem_nhds ]
  rintro _ ⟨t₁, ht₁, rfl⟩
  let a : ℝ := t₁ / 2
  let b : ℝ := (t₁ + 1) / 2
  have ha_mem : a ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [a]; linarith [ht₁.1], by dsimp [a]; linarith
    [ht₁.2]⟩
  have hb_mem : b ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [b]; linarith [ht₁.1], by dsimp [b]; linarith
    [ht₁.2]⟩
  have hat₁ : a < t₁ := by dsimp [a]; linarith [ht₁.1]
  have ht₁b : t₁ < b := by dsimp [b]; linarith [ht₁.2]
  have hsub_ab : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun x hx => ⟨lt_of_lt_of_le ha_mem.1 hx.1,
    lt_of_le_of_lt hx.2 hb_mem.2⟩
  have hsub_at₁ : Icc a t₁ ⊆ Ioo (0 : ℝ) 1 := fun x hx => hsub_ab ⟨hx.1, hx.2.trans ht₁b.le⟩
  have hsub_t₁b : Icc t₁ b ⊆ Ioo (0 : ℝ) 1 := fun x hx => hsub_ab ⟨hat₁.le.trans hx.1, hx.2⟩
  have hconn_at₁ : IsPreconnected (ψ '' Icc a t₁) :=
    isPreconnected_Icc.image ψ (hcont.mono hsub_at₁)
  have hconn_t₁b : IsPreconnected (ψ '' Icc t₁ b) :=
    isPreconnected_Icc.image ψ (hcont.mono hsub_t₁b)
  have hconn_ab : IsPreconnected (ψ '' Icc a b) :=
    isPreconnected_Icc.image ψ (hcont.mono hsub_ab)
  have hne_at₁ : ψ a ≠ ψ t₁ := fun h => hat₁.ne (hinj ha_mem ht₁ h)
  have hne_t₁b : ψ t₁ ≠ ψ b := fun h => ht₁b.ne (hinj ht₁ hb_mem h)
  have hmin_lt : min (ψ a) (ψ b) < ψ t₁ := by
    by_contra! hle
    have hlt : ψ t₁ < min (ψ a) (ψ b) := by
      rcases lt_or_gt_of_ne hne_at₁ with h1 | h1
      · linarith [min_le_left (ψ a) (ψ b)]
      · rcases lt_or_gt_of_ne hne_t₁b with h2 | h2
        · exact lt_min h1 h2
        · linarith [min_le_right (ψ a) (ψ b)]
    have hm1 : min (ψ a) (ψ b) ∈ ψ '' Icc a t₁ :=
      hconn_at₁.Icc_subset ⟨t₁, ⟨hat₁.le, le_rfl⟩, rfl⟩ ⟨a, ⟨le_rfl, hat₁.le⟩, rfl⟩
        ⟨hlt.le, min_le_left _ _⟩
    have hm2 : min (ψ a) (ψ b) ∈ ψ '' Icc t₁ b :=
      hconn_t₁b.Icc_subset ⟨t₁, ⟨le_rfl, ht₁b.le⟩, rfl⟩ ⟨b, ⟨ht₁b.le, le_rfl⟩, rfl⟩
        ⟨hlt.le, min_le_right _ _⟩
    rcases hm1 with ⟨x₁, hx₁, hx₁_eq⟩
    rcases hm2 with ⟨x₂, hx₂, hx₂_eq⟩
    have hx12 : x₁ = x₂ := hinj (hsub_at₁ hx₁) (hsub_t₁b hx₂) (hx₁_eq.trans hx₂_eq.symm)
    have hxt₁ : x₁ = t₁ := le_antisymm hx₁.2 (hx12 ▸ hx₂.1)
    subst hxt₁
    exact hlt.ne hx₁_eq
  have hlt_max : ψ t₁ < max (ψ a) (ψ b) := by
    by_contra! hge
    have hgt : max (ψ a) (ψ b) < ψ t₁ := by
      rcases lt_or_gt_of_ne hne_at₁ with h1 | h1
      · rcases lt_or_gt_of_ne hne_t₁b with h2 | h2
        · linarith [le_max_right (ψ a) (ψ b)]
        · exact max_lt h1 h2
      · linarith [le_max_left (ψ a) (ψ b)]
    have hm1 : max (ψ a) (ψ b) ∈ ψ '' Icc a t₁ :=
      hconn_at₁.Icc_subset ⟨a, ⟨le_rfl, hat₁.le⟩, rfl⟩ ⟨t₁, ⟨hat₁.le, le_rfl⟩, rfl⟩
        ⟨le_max_left _ _, hgt.le⟩
    have hm2 : max (ψ a) (ψ b) ∈ ψ '' Icc t₁ b :=
      hconn_t₁b.Icc_subset ⟨b, ⟨ht₁b.le, le_rfl⟩, rfl⟩ ⟨t₁, ⟨le_rfl, ht₁b.le⟩, rfl⟩
        ⟨le_max_right _ _, hgt.le⟩
    rcases hm1 with ⟨x₁, hx₁, hx₁_eq⟩
    rcases hm2 with ⟨x₂, hx₂, hx₂_eq⟩
    have hx12 : x₁ = x₂ := hinj (hsub_at₁ hx₁) (hsub_t₁b hx₂) (hx₁_eq.trans hx₂_eq.symm)
    have hxt₁ : x₁ = t₁ := le_antisymm hx₁.2 (hx12 ▸ hx₂.1)
    subst hxt₁
    exact hgt.ne hx₁_eq.symm
  have hIoo_sub : Ioo (min (ψ a) (ψ b)) (max (ψ a) (ψ b)) ⊆ ψ '' Ioo (0 : ℝ) 1 := by
    intro y hy
    have hy_img : y ∈ ψ '' Icc a b := by
      rcases le_total (ψ a) (ψ b) with hab | hba
      · exact hconn_ab.Icc_subset ⟨a, ⟨le_rfl, (hat₁.trans ht₁b).le⟩, rfl⟩
          ⟨b, ⟨(hat₁.trans ht₁b).le, le_rfl⟩, rfl⟩
          ⟨(min_eq_left hab) ▸ hy.1.le, (max_eq_right hab) ▸ hy.2.le⟩
      · exact hconn_ab.Icc_subset ⟨b, ⟨(hat₁.trans ht₁b).le, le_rfl⟩, rfl⟩
          ⟨a, ⟨le_rfl, (hat₁.trans ht₁b).le⟩, rfl⟩
          ⟨(min_eq_right hba) ▸ hy.1.le, (max_eq_left hba) ▸ hy.2.le⟩
    exact image_mono hsub_ab hy_img
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hmin_lt, hlt_max⟩) hIoo_sub

/-- If `c : C(unitInterval, S)` has `c 0, c 1 ∈ Γ.V`, maps `Ioo (0 : unitInterval) 1` injectively
into `Γ.U \ Γ.V`, then `e = c '' Ioo (0 : unitInterval) 1` is an edge in `Γ.E` linking `c 0` and
`c 1` in `Γ.toGraph`. -/
theorem Drawing.eq_edge_of_injOn_Ioo [T2Space S] (Γ : Drawing S) (c : C(unitInterval, S))
    (hc0 : c 0 ∈ Γ.V) (hc1 : c 1 ∈ Γ.V)
    (hIoo : ∀ t ∈ Ioo (0 : unitInterval) 1, c t ∈ Γ.U \ Γ.V)
    (hinj : InjOn c (Ioo (0 : unitInterval) 1)) :
    c '' Ioo (0 : unitInterval) 1 ∈ Γ.E ∧
      Γ.toGraph.IsLink (c '' Ioo (0 : unitInterval) 1) (c 0) (c 1) := by
  let e := c '' Ioo (0 : unitInterval) 1
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have hz₀ : c t₀ ∈ Γ.U \ Γ.V := hIoo t₀ ht₀
  let e₀ := pathComponentIn (Γ.U \ Γ.V) (c t₀)
  have he₀E : e₀ ∈ Γ.E := pathComponentIn_mem_arcComponentsIn hz₀
  have hIoo_pc := Net.unitInterval_interior_isPathConnected
  have he_pc : IsPathConnected e := hIoo_pc.image c.continuous
  have he_sub_UV : e ⊆ Γ.U \ Γ.V := by
    rintro _ ⟨t, ht, rfl⟩
    exact hIoo t ht
  have he_sub_e₀ : e ⊆ e₀ := he_pc.subset_pathComponentIn ⟨t₀, ht₀, rfl⟩ he_sub_UV
  have hcl_e : closure e = e ∪ {c 0, c 1} := by
    have hcl1 : closure e = range c := by
      apply Subset.antisymm
      · exact (isCompact_range c.continuous).isClosed.closure_subset_iff.mpr
          (image_subset_range _ _)
      · rw [← image_univ, ← Net.unitInterval_interior_closure]
        exact image_closure_subset_closure_image c.continuous
    rw [hcl1]
    ext z
    simp only [e, mem_range, mem_union, mem_image, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨t, rfl⟩
      rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨t, ht, rfl⟩
    · rintro (⟨t, ht, rfl⟩ | rfl | rfl)
      · exact ⟨t, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have he₀_sub : e₀ ⊆ Γ.U \ Γ.V := pathComponentIn_subset
  obtain ⟨γ₀, hγ₀_cont, hγ₀0, hγ₀1, hγ₀_inj, hγ₀_img⟩ := GM11.exists_edge_param Γ he₀E
  let g₀ : Ioo (0 : unitInterval) 1 → e₀ := fun t =>
    ⟨γ₀ t.1, hγ₀_img ▸ ⟨t.1, t.2, rfl⟩⟩
  have hg₀_cont : Continuous g₀ := by fun_prop
  have hg₀_inj : Function.Injective g₀ := by
    intro t₁ t₂ h12
    ext
    exact congr_arg Subtype.val (hγ₀_inj t₁.2 t₂.2 (congr_arg Subtype.val h12))
  have hg₀_surj : Function.Surjective g₀ := by
    rintro ⟨z, hz⟩
    rw [← hγ₀_img] at hz
    rcases hz with ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hg₀_closed : IsClosedMap g₀ := by
    intro F hF
    rw [isClosed_induced_iff] at hF
    rcases hF with ⟨K, hK, rfl⟩
    have hγK_closed : IsClosed (γ₀ '' K) := hγ₀_cont.isClosedMap K hK
    have himg_eq : g₀ '' (Subtype.val ⁻¹' K) = Subtype.val ⁻¹' (γ₀ '' K) := by
      ext ⟨z, hz⟩
      simp only [mem_image, mem_preimage]
      constructor
      · rintro ⟨⟨t, ht⟩, htK, htz⟩
        exact ⟨t, htK, congr_arg Subtype.val htz⟩
      · rintro ⟨s, hsK, rfl⟩
        rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
        · exact False.elim ((he₀_sub hz).2 hγ₀0)
        · exact False.elim ((he₀_sub hz).2 hγ₀1)
        · exact ⟨⟨s, hs⟩, hsK, rfl⟩
    rw [himg_eq]
    exact hγK_closed.preimage continuous_subtype_val
  let φ : e₀ ≃ₜ Ioo (0 : unitInterval) 1 :=
    ((Equiv.ofBijective g₀ ⟨hg₀_inj, hg₀_surj⟩).toHomeomorphOfContinuousClosed hg₀_cont
      hg₀_closed).symm
  let S_e : Set e₀ := Subtype.val ⁻¹' e
  have hS_closed : IsClosed S_e := by
    have heq : S_e = Subtype.val ⁻¹' closure e := by
      ext ⟨z, hz⟩
      simp only [S_e, mem_preimage, hcl_e, mem_union, mem_insert_iff, mem_singleton_iff]
      constructor
      · exact Or.inl
      · rintro (hze | rfl | rfl)
        · exact hze
        · exact False.elim ((he₀_sub hz).2 hc0)
        · exact False.elim ((he₀_sub hz).2 hc1)
    rw [heq]
    exact isClosed_closure.preimage continuous_subtype_val
  have hS_open : IsOpen S_e := by
    let g_sub : Ioo (0 : ℝ) 1 → ℝ := fun r =>
      ((φ ⟨c ⟨r.1, r.2.1.le, r.2.2.le⟩,
        he_sub_e₀ ⟨⟨r.1, r.2.1.le, r.2.2.le⟩,
          ⟨Subtype.coe_lt_coe.mp r.2.1, Subtype.coe_lt_coe.mp r.2.2⟩, rfl⟩⟩).1 : ℝ)
    have hg_cont : Continuous g_sub := by fun_prop
    let ψ : ℝ → ℝ := fun r =>
      if hr : r ∈ Ioo (0 : ℝ) 1 then g_sub ⟨r, hr⟩ else 0
    have hψ_eq : (Ioo (0 : ℝ) 1).domRestrict ψ = g_sub := by
      ext r
      change (if hr : r.1 ∈ Ioo (0 : ℝ) 1 then g_sub ⟨r.1, hr⟩ else 0) = g_sub r
      exact dite_eq_left r.2
    have hψ_cont : ContinuousOn ψ (Ioo (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict, hψ_eq]
      exact hg_cont
    have hψ_inj : InjOn ψ (Ioo (0 : ℝ) 1) := by
      intro r₁ hr₁ r₂ hr₂ h12
      have h12' : g_sub ⟨r₁, hr₁⟩ = g_sub ⟨r₂, hr₂⟩ := by
        simpa only [ψ, dite_eq_left hr₁, dite_eq_left hr₂] using h12
      have hφ_eq : φ ⟨c ⟨r₁, hr₁.1.le, hr₁.2.le⟩, _⟩ = φ ⟨c ⟨r₂, hr₂.1.le, hr₂.2.le⟩, _⟩ :=
        Subtype.ext (Subtype.ext h12')
      have hc_eq : c ⟨r₁, hr₁.1.le, hr₁.2.le⟩ = c ⟨r₂, hr₂.1.le, hr₂.2.le⟩ :=
        congr_arg Subtype.val (φ.injective hφ_eq)
      have ht_eq : (⟨r₁, hr₁.1.le, hr₁.2.le⟩ : unitInterval) = ⟨r₂, hr₂.1.le, hr₂.2.le⟩ :=
        hinj ⟨Subtype.coe_lt_coe.mp hr₁.1, Subtype.coe_lt_coe.mp hr₁.2⟩
          ⟨Subtype.coe_lt_coe.mp hr₂.1, Subtype.coe_lt_coe.mp hr₂.2⟩ hc_eq
      exact congr_arg Subtype.val ht_eq
    have hopen_img : IsOpen (ψ '' Ioo (0 : ℝ) 1) :=
      isOpen_image_Ioo_of_continuousOn_injOn hψ_cont hψ_inj
    have hSe_eq : S_e = (fun x : e₀ => ((φ x).1 : ℝ)) ⁻¹' (ψ '' Ioo (0 : ℝ) 1) := by
      ext ⟨z, hz⟩
      simp only [S_e, mem_preimage, mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩
        have ht_real : (t : ℝ) ∈ Ioo (0 : ℝ) 1 :=
          ⟨Subtype.coe_lt_coe.mpr ht.1, Subtype.coe_lt_coe.mpr ht.2⟩
        refine ⟨(t : ℝ), ht_real, ?_⟩
        change (if hr : (t : ℝ) ∈ Ioo (0 : ℝ) 1 then g_sub ⟨t, hr⟩ else 0) = ((φ ⟨c t, hz⟩).1 : ℝ)
        exact dite_eq_left ht_real
      · rintro ⟨r, hr, hrz⟩
        have hrz' : g_sub ⟨r, hr⟩ = ((φ ⟨z, hz⟩).1 : ℝ) := by
          simpa only [ψ, dite_eq_left hr] using hrz
        have hφ_eq : φ ⟨c ⟨r, hr.1.le, hr.2.le⟩, _⟩ = φ ⟨z, hz⟩ :=
          Subtype.ext (Subtype.ext hrz')
        have hc_eq : c ⟨r, hr.1.le, hr.2.le⟩ = z := congr_arg Subtype.val (φ.injective hφ_eq)
        exact ⟨⟨r, hr.1.le, hr.2.le⟩,
          ⟨Subtype.coe_lt_coe.mp hr.1, Subtype.coe_lt_coe.mp hr.2⟩, hc_eq⟩
    rw [hSe_eq]
    exact hopen_img.preimage (by fun_prop)
  have hconn_e₀ : ConnectedSpace e₀ :=
    Subtype.connectedSpace ((isPathConnected_pathComponentIn hz₀).isConnected)
  have hSe_nonempty : S_e.Nonempty :=
    ⟨⟨c t₀, mem_pathComponentIn_self hz₀⟩, ⟨t₀, ht₀, rfl⟩⟩
  have hSe_univ : S_e = univ := IsClopen.eq_univ ⟨hS_closed, hS_open⟩ hSe_nonempty
  have he_eq_e₀ : e = e₀ := by
    apply Subset.antisymm he_sub_e₀
    intro z hz
    have hmem : (⟨z, hz⟩ : e₀) ∈ S_e := by rw [hSe_univ]; trivial
    exact hmem
  have heE : e ∈ Γ.E := he_eq_e₀.symm ▸ he₀E
  refine ⟨heE, heE, hc0, hc1, ?_⟩
  rw [hcl_e]
  ext z
  simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hze | rfl | rfl, hzV⟩
    · exact False.elim ((he_sub_UV hze).2 hzV)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), hc0⟩
    · exact ⟨Or.inr (Or.inr rfl), hc1⟩

/-- Assembling a sequence of `n` consecutive links `(v i.castSucc, e i, v i.succ)` into a walk
`W : GraphWalk G (v 0) (v (Fin.last n))` with `W.edges = List.ofFn e`. -/
theorem GraphWalk.exists_ofFn_edges {α : Type u} {β : Type*} {G : Graph α β} :
    ∀ (n : ℕ) (v : Fin (n + 1) → α) (e : Fin n → β),
      v 0 ∈ G.vertexSet →
      (∀ i : Fin n, G.IsLink (e i) (v i.castSucc) (v i.succ)) →
      ∃ W : GraphWalk G (v 0) (v (Fin.last n)), W.edges = List.ofFn e
  | 0, v, e, hv0, _ => ⟨.nil hv0, rfl⟩
  | n + 1, v, e, _, hlink => by
    obtain ⟨W', hW'⟩ := GraphWalk.exists_ofFn_edges n (fun i => v i.succ) (fun i => e i.succ)
      (hlink 0).right_mem (fun i => hlink i.succ)
    have h0 : G.IsLink (e 0) (v 0) (v (Fin.succ 0)) := by simpa using hlink 0
    exact ⟨.cons h0 W', by rw [GraphWalk.edges_cons, hW', List.ofFn_succ]⟩

/-- If `f : α → β` takes the value `e` on `L : List α` only at `p₁` and `p₂` (`p₁ ≠ p₂`), then
`(L.map f).count e = L.count p₁ + L.count p₂`. -/
private theorem count_map_eq_add_of_iff_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (L : List α) (f : α → β) (e : β) {p₁ p₂ : α} (hp12 : p₁ ≠ p₂)
    (hiff : ∀ p : α, f p = e ↔ p = p₁ ∨ p = p₂) :
    (L.map f).count e = L.count p₁ + L.count p₂ := by
  induction L with
  | nil => simp
  | cons a as ih =>
    by_cases ha1 : a = p₁
    · subst ha1
      have hfa : f a = e := (hiff a).mpr (Or.inl rfl)
      rw [List.map_cons, hfa, List.count_cons_self, List.count_cons_self,
        List.count_cons_of_ne hp12, ih]
      omega
    · by_cases ha2 : a = p₂
      · subst ha2
        have hfa : f a = e := (hiff a).mpr (Or.inr rfl)
        rw [List.map_cons, hfa, List.count_cons_self, List.count_cons_of_ne (Ne.symm hp12),
          List.count_cons_self, ih]
        omega
      · have hfa : f a ≠ e := fun h => by
          rcases (hiff a).mp h with rfl | rfl
          · exact ha1 rfl
          · exact ha2 rfl
        rw [List.map_cons, List.count_cons_of_ne hfa, List.count_cons_of_ne ha1,
          List.count_cons_of_ne ha2, ih]

/-- If `f : Fin m → β` equals `e` at exactly two distinct indices `p₁ ≠ p₂`, then
`(List.ofFn f).count e = 2`. -/
private theorem count_ofFn_eq_two {m : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin m → β) (e : β) {p₁ p₂ : Fin m} (hp12 : p₁ ≠ p₂)
    (hiff : ∀ p : Fin m, f p = e ↔ p = p₁ ∨ p = p₂) :
    (List.ofFn f).count e = 2 := by
  rw [List.ofFn_eq_map, count_map_eq_add_of_iff_pair (List.finRange m) f e hp12 hiff,
    List.count_eq_one_of_mem (List.nodup_finRange m) (List.mem_finRange p₁),
    List.count_eq_one_of_mem (List.nodup_finRange m) (List.mem_finRange p₂)]

/-- Given `τ : ℕ → ℝ` with `τ 0 = 0`, `τ m = 1`, and `∀ p < m, τ p < τ (p + 1)`, every
`x ∈ Ioo (0 : ℝ) 1` with `∀ p ≤ m, x ≠ τ p` belongs to `Ioo (τ p.1) (τ (p.1 + 1))` for a unique
`p : Fin m`. -/
private theorem exists_unique_interval_of_sorted {m : ℕ} {τ : ℕ → ℝ}
    (hτ0 : τ 0 = 0) (hτm : τ m = 1) (hτ_lt : ∀ p < m, τ p < τ (p + 1)) :
    (∀ {a b : ℕ}, a < b → b ≤ m → τ a < τ b) ∧
    (∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → (∀ p ≤ m, x ≠ τ p) →
      ∃ p : Fin m, x ∈ Ioo (τ p.1) (τ (p.1 + 1)) ∧
        ∀ q : Fin m, x ∈ Ioo (τ q.1) (τ (q.1 + 1)) → q = p) := by
  have hmono : ∀ {a b : ℕ}, a < b → b ≤ m → τ a < τ b := by
    intro a b hab hbm
    induction b with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hab) with rfl | hlt
      · exact hτ_lt a (Nat.lt_of_succ_le hbm)
      · exact (ih hlt (Nat.le_of_succ_le hbm)).trans (hτ_lt k (Nat.lt_of_succ_le hbm))
  refine ⟨hmono, ?_⟩
  intro x hx hx_ne
  have hex : ∀ k ≤ m, τ 0 < x → x < τ k → ∃ p < k, x ∈ Ioo (τ p) (τ (p + 1)) := by
    intro k hk h0x hxk
    induction k with
    | zero => exact False.elim ((h0x.trans hxk).ne rfl)
    | succ n ih =>
      rcases lt_or_gt_of_ne (hx_ne n (Nat.le_of_succ_le hk)) with hlt | hgt
      · obtain ⟨p, hp, hpx⟩ := ih (Nat.le_of_succ_le hk) hlt
        exact ⟨p, Nat.lt_succ_of_lt hp, hpx⟩
      · exact ⟨n, Nat.lt_succ_self n, ⟨hgt, hxk⟩⟩
  obtain ⟨p, hpm, hpx⟩ := hex m le_rfl (hτ0 ▸ hx.1) (hτm ▸ hx.2)
  refine ⟨⟨p, hpm⟩, hpx, ?_⟩
  intro q hqx
  ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : τ (q.1 + 1) ≤ τ p := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq | hlt'
      · exact (congr_arg τ heq).le
      · exact (hmono hlt' hpm.le).le
    linarith [hqx.2, hpx.1]
  · have hle : τ (p + 1) ≤ τ q.1 := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with heq | hlt'
      · exact (congr_arg τ heq).le
      · exact (hmono hlt' q.2.le).le
    linarith [hpx.2, hqx.1]

private theorem boundary_arc_interior_image
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    {s : N.D}
    {t : N.D}
    {C₁ : Set N.D}
    (hC₁_sub : C₁ ⊆ bd N.D \ {s, t})
    (f_C₁ : ↑unitInterval ≃ₜ ↑(C₁ ∪ {s, t}))
    (hγ0 : (f_C₁ 0).1 = s)
    (hγ1 : (f_C₁ 1).1 = t)
    (hγ_inj : Function.Injective (Subtype.val ∘ f_C₁)) :
    (Subtype.val ∘ f_C₁) '' Ioo (0 : unitInterval) 1 = C₁ := by
  let γ : unitInterval → N.D := Subtype.val ∘ f_C₁
  change γ '' Ioo 0 1 = C₁
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    change (f_C₁ u).1 ∈ C₁
    rcases (f_C₁ u).2 with huC₁ | h0 | h1
    · exact huC₁
    · exact False.elim (hu.1.ne (hγ_inj (h0.trans hγ0.symm)).symm)
    · exact False.elim (hu.2.ne (hγ_inj ((mem_singleton_iff.mp h1).trans hγ1.symm)))
  · intro hx
    let u := f_C₁.symm ⟨x, Or.inl hx⟩
    have hγu : γ u = x := by simp [γ, u]
    have hu_Ioo : u ∈ Ioo (0 : unitInterval) 1 := by
      rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo u with hu0 | hu1 | hu
      · exfalso
        exact (hC₁_sub hx).2 (Or.inl (hγu.symm.trans (hu0 ▸ hγ0)))
      · exfalso
        exact (hC₁_sub hx).2 (Or.inr (mem_singleton_iff.mpr (hγu.symm.trans (hu1 ▸ hγ1))))
      · exact hu
    exact ⟨u, hu_Ioo, hγu⟩

private theorem affine_subinterval_interior_image
    (m : ℕ)
    (τ : ℕ → ℝ)
    (hτ_lt : ∀ p < m, τ p < τ (p + 1))
    (α_fn : Fin m → C(unitInterval, unitInterval))
    (hα : ∀ (p : Fin m) (u : unitInterval),
      (α_fn p u : ℝ) = (1 - u.1) * τ p.1 + u.1 * τ (p.1 + 1)) :
    ∀ (p : Fin m), α_fn p '' Ioo (0 : unitInterval) 1 =
      {q : unitInterval | q.1 ∈ Ioo (τ p.1) (τ (p.1 + 1))} := by
  intro p
  have hlt : τ p.1 < τ (p.1 + 1) := hτ_lt p.1 p.2
  ext q
  simp only [mem_image, mem_Ioo, mem_ofPred]
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
    have hu0' : (0 : ℝ) < u.1 := Subtype.coe_lt_coe.mpr hu0
    have hu1' : u.1 < 1 := Subtype.coe_lt_coe.mpr hu1
    rw [hα]
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨hq0, hq1⟩
    have hpos : 0 < τ (p.1 + 1) - τ p.1 := sub_pos.mpr hlt
    have hu0 : 0 < (q.1 - τ p.1) / (τ (p.1 + 1) - τ p.1) :=
      div_pos (sub_pos.mpr hq0) hpos
    have hu1 : (q.1 - τ p.1) / (τ (p.1 + 1) - τ p.1) < 1 :=
      (div_lt_one hpos).mpr (by linarith)
    let u : unitInterval := ⟨(q.1 - τ p.1) / (τ (p.1 + 1) - τ p.1), ⟨hu0.le, hu1.le⟩⟩
    refine ⟨u, ⟨Subtype.coe_lt_coe.mp hu0, Subtype.coe_lt_coe.mp hu1⟩, ?_⟩
    ext
    rw [hα]
    dsimp [u]
    have hne : τ (p.1 + 1) - τ p.1 ≠ 0 := hpos.ne'
    field_simp
    ring

private theorem boundary_segment_maps_to_edge
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (J : Drawing S)
    (J' : Drawing S)
    (hSeam : N.IsSeamGraphFor J)
    (hJ'U : J'.U = J.U)
    [T2Space S]
    (γ : C(↑unitInterval, N.D))
    (hγ_inj : Function.Injective ⇑γ)
    (α : C(unitInterval, unitInterval))
    (hα_inj : Function.Injective α)
    (hU_disj_V : Disjoint ((γ ∘ α) '' Ioo (0 : unitInterval) 1) (N.φ ⁻¹' J'.V))
    (hU_bd : (γ ∘ α) '' Ioo (0 : unitInterval) 1 ⊆ bd N.D)
    (hU_injOn : InjOn N.φ ((γ ∘ α) '' Ioo (0 : unitInterval) 1))
    (h0 : N.φ (γ (α 0)) ∈ J'.V) (h1 : N.φ (γ (α 1)) ∈ J'.V) :
    let c : C(unitInterval, S) := ⟨N.φ ∘ γ ∘ α,
      N.quotientMap_φ.continuous.comp (γ.continuous.comp α.continuous)⟩
    c '' Ioo (0 : unitInterval) 1 ∈ J'.E ∧
      J'.toGraph.IsLink (c '' Ioo (0 : unitInterval) 1) (c 0) (c 1) := by
  intro c
  let U := (γ ∘ α) '' Ioo (0 : unitInterval) 1
  have hc_Ioo : ∀ u ∈ Ioo (0 : unitInterval) 1, c u ∈ J'.U \ J'.V := by
    intro u hu
    have hxU : γ (α u) ∈ U := ⟨u, hu, rfl⟩
    refine ⟨?_, Disjoint.notMem_of_mem_left hU_disj_V hxU⟩
    rw [hJ'U, hSeam.2.1]
    exact ⟨γ (α u), hU_bd hxU, rfl⟩
  have hc_inj : InjOn c (Ioo (0 : unitInterval) 1) := by
    intro u₁ hu₁ u₂ hu₂ h12
    have hx_eq : γ (α u₁) = γ (α u₂) :=
      hU_injOn ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩ h12
    exact hα_inj (hγ_inj hx_eq)
  exact Drawing.eq_edge_of_injOn_Ioo J' c h0 h1 hc_Ioo hc_inj

private theorem unique_arc_segment_away_from_vertices
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (J' : Drawing S)
    {C₁ : Set N.D}
    (γ : C(↑unitInterval, N.D))
    (hγ_inj : Function.Injective ⇑γ)
    (hγ_Ioo : ⇑γ '' Ioo 0 1 = C₁)
    (m : ℕ)
    (τ : ℕ → ℝ)
    (hτ_unique : ∀ {x : ℝ}, x ∈ Ioo 0 1 → (∀ p ≤ m, x ≠ τ p) →
      ∃ p : Fin m, x ∈ Ioo (τ p.1) (τ (p.1 + 1)) ∧
        ∀ q : Fin m, x ∈ Ioo (τ q.1) (τ (q.1 + 1)) → q = p)
    (τ_I : (p : ℕ) → p ≤ m → unitInterval)
    (hτ_I : ∀ (p : ℕ) (hp : p ≤ m), (τ_I p hp : ℝ) = τ p)
    (hτ_V : ∀ (p : ℕ) (hp : p ≤ m), N.φ (γ (τ_I p hp)) ∈ J'.V)
    (U_fn : Fin m → Set N.D)
    (hU_eq : ∀ (p : Fin m), U_fn p = ⇑γ '' {q | ↑q ∈ Ioo (τ ↑p) (τ (↑p + 1))}) :
    ∀ y ∈ C₁, N.φ y ∉ J'.V → ∃ p, ∀ (q : Fin m), y ∈ U_fn q ↔ q = p := by
  intro y hyC₁ hyV
  rw [← hγ_Ioo] at hyC₁
  rcases hyC₁ with ⟨q₀, hq₀, rfl⟩
  have hq₀_real : (q₀ : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Subtype.coe_lt_coe.mpr hq₀.1, Subtype.coe_lt_coe.mpr hq₀.2⟩
  have hq₀_ne : ∀ p ≤ m, (q₀ : ℝ) ≠ τ p := by
    intro p hp h_eq
    have hq_τ : q₀ = τ_I p hp := Subtype.ext (h_eq.trans (hτ_I p hp).symm)
    exact hyV (hq_τ ▸ hτ_V p hp)
  obtain ⟨p, hp_mem, hp_uniq⟩ := hτ_unique hq₀_real hq₀_ne
  refine ⟨p, fun q => ?_⟩
  rw [hU_eq q]
  constructor
  · rintro ⟨q', hq', hγ_eq⟩
    have hqq' : q' = q₀ := hγ_inj hγ_eq
    subst hqq'
    exact hp_uniq q hq'
  · rintro rfl
    exact ⟨q₀, hp_mem, rfl⟩

private theorem edge_subdivision_indices_of_fiber
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (J' : Drawing S)
    (m : ℕ)
    (U_fn : Fin m → Set N.D)
    (e_fn : Fin m → Set S)
    (he_eq_φU : ∀ (p : Fin m), e_fn p = N.φ '' U_fn p)
    (he_edge : ∀ p : Fin m, e_fn p ∈ J'.E)
    (p₀ : Fin m)
    (z₀ : S)
    (hz₀_e : z₀ ∈ e_fn p₀)
    (i : Fin N.r)
    (w : ↑unitInterval)
    (hφw : N.φ ((N.f i) w) = z₀)
    (hfiber : N.φ ⁻¹' {z₀} = {(N.f i) w, (N.g i) w})
    (p₁ : Fin m)
    (hp₁ : ∀ (q : Fin m), (N.f i) w ∈ U_fn q ↔ q = p₁)
    (p₂ : Fin m)
    (hp₂ : ∀ (q : Fin m), (N.g i) w ∈ U_fn q ↔ q = p₂)
    :
    ∀ (p : Fin m), e_fn p = e_fn p₀ ↔ p = p₁ ∨ p = p₂ := by
  intro p
  have hz₀_iff : e_fn p = e_fn p₀ ↔ z₀ ∈ e_fn p := by
    constructor
    · intro h; exact h.symm ▸ hz₀_e
    · intro hz_p
      exact J'.edge_eq_of_mem (he_edge p) (he_edge p₀) hz_p hz₀_e
  rw [hz₀_iff, he_eq_φU p]
  constructor
  · rintro ⟨y, hyU, hyz⟩
    have hy_fg : y ∈ ({N.f i w, N.g i w} : Set N.D) := hfiber ▸ hyz
    rcases hy_fg with rfl | rfl
    · exact Or.inl ((hp₁ p).mp hyU)
    · exact Or.inr ((hp₂ p).mp hyU)
  · rintro (rfl | rfl)
    · exact ⟨N.f i w, (hp₁ p).mpr rfl, hφw⟩
    · exact ⟨N.g i w, (hp₂ p).mpr rfl, (N.φ_f_eq_φ_g i w).symm.trans hφw⟩

/-- Graph Minors VII, (2.5) (page 217):
"(2.5) *There is a path of $J'$ between $\phi(s)$ and $\phi(t)$ with no edges of type (iii) or
(iv).*" -/
theorem exists_path_no_type3_type4 [T1Space S] (hS : IsSurface S) (N : Net S) (J J' : Drawing S)
    (hSeam : N.IsSeamGraphFor J) {s t : N.D} (hs : s ∈ bd N.D) (ht : t ∈ bd N.D) (hst : s ≠ t)
    {C₁ C₂ : Set N.D} (hcomp : componentsIn (bd N.D \ {s, t}) = {C₁, C₂}) (hC12 : C₁ ≠ C₂)
    (hJ'U : J'.U = J.U) (hJ'V : J'.V = J.V ∪ {N.φ s, N.φ t}) :
    ∃ P : Drawing S, P.IsSubdrawing J' ∧ P.IsPathBetween (N.φ s) (N.φ t) ∧
      ∀ e ∈ P.E, ¬ IsNetEdgeType3 N C₁ e ∧ ¬ IsNetEdgeType4 N C₂ e := by
  have : T2Space S := hS.2.1
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  -- Step 1: Parametrize `C₁ ∪ {s, t}` by `γ : C(unitInterval, N.D)` with ends `s, t`.
  obtain ⟨B₁, B₂, hcomp_B, hdisj_B, hunion_B, hline_B₁, hline_B₂⟩ :=
    Net.oArc_components_diff_pair N.isOArc_bd_D hs ht hst
  have hpair_eq : ({C₁, C₂} : Set (Set N.D)) = {B₁, B₂} := hcomp.symm.trans hcomp_B
  have hC₁_mem : C₁ ∈ ({B₁, B₂} : Set (Set N.D)) := hpair_eq ▸ Or.inl rfl
  have hC₂_mem : C₂ ∈ ({B₁, B₂} : Set (Set N.D)) := hpair_eq ▸ Or.inr rfl
  have hC₁_props : Disjoint C₁ C₂ ∧ C₁ ⊆ bd N.D \ {s, t} ∧ IsLineWithEnds (C₁ ∪ {s, t}) s t := by
    rcases hC₁_mem with rfl | rfl <;> rcases hC₂_mem with rfl | rfl
    · exact False.elim (hC12 rfl)
    · exact ⟨hdisj_B, fun x hx => hunion_B ▸ Or.inl hx, hline_B₁⟩
    · exact ⟨hdisj_B.symm, fun x hx => hunion_B ▸ Or.inr hx, hline_B₂⟩
    · exact False.elim (hC12 rfl)
  rcases hC₁_props with ⟨hdisj_C12, hC₁_sub, f_C₁, hf0, hf1⟩
  let γ : C(unitInterval, N.D) := ⟨Subtype.val ∘ f_C₁, continuous_subtype_val.comp f_C₁.continuous⟩
  have hγ0 : γ 0 = s := hf0
  have hγ1 : γ 1 = t := hf1
  have hγ_inj : Function.Injective γ := fun u v h => f_C₁.injective (Subtype.ext h)
  have hγ_bd : range γ ⊆ bd N.D := by
    rintro _ ⟨u, rfl⟩
    change (f_C₁ u).1 ∈ bd N.D
    rcases (f_C₁ u).2 with hu | hus | hut
    · exact (hC₁_sub hu).1
    · rw [hus]; exact hs
    · rw [mem_singleton_iff.mp hut]; exact ht
  have hγ_Ioo : γ '' Ioo (0 : unitInterval) 1 = C₁ := by
    exact boundary_arc_interior_image (S := S) N (s := s) (t := t) (C₁ := C₁) hC₁_sub f_C₁ hγ0
      hγ1 hγ_inj
  -- Step 2: Subdivide `[0, 1]` at the finite set `T` of preimages of `J'.V` under `N.φ ∘ γ`.
  let T_I : Set unitInterval := γ ⁻¹' (N.φ ⁻¹' J'.V)
  have hTI_fin : T_I.Finite := (N.finite_preimage J'.finite_V).preimage hγ_inj.injOn
  let T : Set ℝ := Subtype.val '' T_I
  have hT_fin : T.Finite := hTI_fin.image _
  have hT_sub : T ⊆ Icc (0 : ℝ) 1 := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  have hφs_V : N.φ s ∈ J'.V := by rw [hJ'V]; exact Or.inr (Or.inl rfl)
  have hφt_V : N.φ t ∈ J'.V := by rw [hJ'V]; exact Or.inr (Or.inr rfl)
  have h0_T : (0 : ℝ) ∈ T := ⟨0, by simpa [T_I, hγ0] using hφs_V, rfl⟩
  have h1_T : (1 : ℝ) ∈ T := ⟨1, by simpa [T_I, hγ1] using hφt_V, rfl⟩
  obtain ⟨m, τ, _, hτ0, hτm, hτ_lt, hτ_mem, hτ_no, hτ_all⟩ :=
    exists_sorted hT_fin hT_sub h0_T h1_T
  obtain ⟨hτ_mono, hτ_unique⟩ := exists_unique_interval_of_sorted hτ0 hτm hτ_lt
  have hτ_Icc : ∀ p ≤ m, τ p ∈ Icc (0 : ℝ) 1 := fun p hp => hT_sub (hτ_mem p hp)
  let τ_I : (p : ℕ) → p ≤ m → unitInterval := fun p hp => ⟨τ p, hτ_Icc p hp⟩
  have hτ_V : ∀ p (hp : p ≤ m), N.φ (γ (τ_I p hp)) ∈ J'.V := by
    intro p hp
    rcases hτ_mem p hp with ⟨u, hu, hu_eq⟩
    have hu' : u = τ_I p hp := Subtype.ext hu_eq
    exact hu' ▸ hu
  -- Step 3: On each open subinterval `(τ p, τ (p + 1))`, `N.φ ∘ γ` traces an edge `e_fn p ∈ J'.E`.
  let α_fn (p : Fin m) : C(unitInterval, unitInterval) :=
    ⟨fun u => ⟨(1 - u.1) * τ p.1 + u.1 * τ (p.1 + 1), by
      have hp0 := (hτ_Icc p.1 p.2.le).1
      have hp1 := (hτ_Icc (p.1 + 1) p.2).2
      have hlt := (hτ_lt p.1 p.2).le
      have hu0 := u.2.1
      have hu1 := u.2.2
      exact ⟨by nlinarith, by nlinarith⟩⟩, by fun_prop⟩
  have hα0 : ∀ p : Fin m, α_fn p 0 = τ_I p.1 p.2.le := by
    intro p; ext; simp [α_fn, τ_I]
  have hα1 : ∀ p : Fin m, α_fn p 1 = τ_I (p.1 + 1) p.2 := by
    intro p; ext; simp [α_fn, τ_I]
  have hα_inj : ∀ p : Fin m, Function.Injective (α_fn p) := by
    intro p u₁ u₂ h12
    have hval : (1 - u₁.1) * τ p.1 + u₁.1 * τ (p.1 + 1) =
        (1 - u₂.1) * τ p.1 + u₂.1 * τ (p.1 + 1) := congr_arg Subtype.val h12
    have hlt : τ p.1 < τ (p.1 + 1) := hτ_lt p.1 p.2
    ext
    nlinarith
  have hα_Ioo : ∀ p : Fin m,
      α_fn p '' Ioo (0 : unitInterval) 1 =
        {q : unitInterval | q.1 ∈ Ioo (τ p.1) (τ (p.1 + 1))} := by
    exact affine_subinterval_interior_image m τ hτ_lt α_fn (fun _ _ => rfl)
  let U_fn (p : Fin m) : Set N.D := (γ ∘ α_fn p) '' Ioo (0 : unitInterval) 1
  have hU_eq : ∀ p : Fin m,
      U_fn p = γ '' {q : unitInterval | q.1 ∈ Ioo (τ p.1) (τ (p.1 + 1))} := by
    intro p
    dsimp only [U_fn]
    rw [image_comp, hα_Ioo p]
  have hU_sub_C₁ : ∀ p : Fin m, U_fn p ⊆ C₁ := by
    intro p
    rw [hU_eq p, ← hγ_Ioo]
    refine image_mono fun q hq => ?_
    have hp0 := (hτ_Icc p.1 p.2.le).1
    have hp1 := (hτ_Icc (p.1 + 1) p.2).2
    exact ⟨Subtype.coe_lt_coe.mp (lt_of_le_of_lt hp0 hq.1),
      Subtype.coe_lt_coe.mp (lt_of_lt_of_le hq.2 hp1)⟩
  have hU_disj_V : ∀ p : Fin m, Disjoint (U_fn p) (N.φ ⁻¹' J'.V) := by
    intro p
    rw [disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ hφV
    have hmem_T : (α_fn p u).1 ∈ T := ⟨α_fn p u, hφV, rfl⟩
    have hmem_Ioo : (α_fn p u).1 ∈ Ioo (τ p.1) (τ (p.1 + 1)) := by
      have : α_fn p u ∈ {q : unitInterval | q.1 ∈ Ioo (τ p.1) (τ (p.1 + 1))} :=
        hα_Ioo p ▸ ⟨u, hu, rfl⟩
      exact this
    exact hτ_no p.1 p.2 (α_fn p u).1 hmem_T hmem_Ioo
  have hU_conn : ∀ p : Fin m, IsPreconnected (U_fn p) := fun p =>
    (Net.unitInterval_interior_isPathConnected.image
      (γ.continuous.comp (α_fn p).continuous)).isConnected.isPreconnected
  have hU_bd : ∀ p : Fin m, U_fn p ⊆ bd N.D := fun p =>
    (hU_sub_C₁ p).trans (hC₁_sub.trans sdiff_subset)
  have hU_disj_seamV : ∀ p : Fin m, Disjoint (U_fn p) (N.φ ⁻¹' N.seamV) := by
    intro p
    refine (hU_disj_V p).mono_right (preimage_mono ?_)
    rw [hJ'V, hSeam.2.2]
    exact subset_union_left
  have hU_injOn : ∀ p : Fin m, InjOn N.φ (U_fn p) := fun p =>
    N.injOn_φ_of_isPreconnected (hU_conn p) (hU_bd p) (hU_disj_seamV p)
  let c_fn (p : Fin m) : C(unitInterval, S) :=
    ⟨N.φ ∘ γ ∘ α_fn p, N.quotientMap_φ.continuous.comp (γ.continuous.comp (α_fn p).continuous)⟩
  let v_fn (k : Fin (m + 1)) : S := N.φ (γ (τ_I k.1 (Nat.le_of_lt_succ k.2)))
  let e_fn (p : Fin m) : Set S := c_fn p '' Ioo (0 : unitInterval) 1
  have he_eq_φU : ∀ p : Fin m, e_fn p = N.φ '' U_fn p := fun p => by
    dsimp only [e_fn, U_fn, c_fn]
    rw [← image_comp]
    rfl
  have he_edge : ∀ p : Fin m,
      e_fn p ∈ J'.E ∧ J'.toGraph.IsLink (e_fn p) (v_fn p.castSucc) (v_fn p.succ) := by
    intro p
    have h0 : N.φ (γ (α_fn p 0)) = v_fn p.castSucc := by rw [hα0]; rfl
    have h1 : N.φ (γ (α_fn p 1)) = v_fn p.succ := by rw [hα1]; rfl
    have he := boundary_segment_maps_to_edge N J J' hSeam hJ'U γ hγ_inj (α_fn p)
      (hα_inj p) (hU_disj_V p) (hU_bd p) (hU_injOn p)
      (h0.symm ▸ hτ_V p.1 p.2.le) (h1.symm ▸ hτ_V (p.1 + 1) p.2)
    change e_fn p ∈ J'.E ∧ J'.toGraph.IsLink (e_fn p)
      (N.φ (γ (α_fn p 0))) (N.φ (γ (α_fn p 1))) at he
    rwa [h0, h1] at he
  -- Step 4: Extract an odd-count walk and then a simple walk in `J'`.
  have hv0_eq : v_fn 0 = N.φ s := by
    have h0 : τ_I 0 (Nat.zero_le m) = 0 := Subtype.ext hτ0
    simp [v_fn, h0, hγ0]
  have hvm_eq : v_fn (Fin.last m) = N.φ t := by
    have hm : τ_I m le_rfl = 1 := Subtype.ext hτm
    simp [v_fn, hm, hγ1]
  obtain ⟨W₀', hW₀'_edges⟩ := GraphWalk.exists_ofFn_edges m v_fn e_fn
    (hτ_V 0 (Nat.zero_le m)) (fun p => (he_edge p).2)
  obtain ⟨W₀, hW₀_edges⟩ :
      ∃ W₀ : GraphWalk J'.toGraph (N.φ s) (N.φ t), W₀.edges = List.ofFn e_fn := by
    rw [← hv0_eq, ← hvm_eq]
    exact ⟨W₀', hW₀'_edges⟩
  obtain ⟨W₁, hW₁_odd⟩ := GraphWalk.exists_odd_count_walk W₀
  obtain ⟨W₂, hW₂_simple, _, hW₂_sub_W₁⟩ := GM11.GraphWalk.exists_isSimple W₁
  let P : Drawing S := GM11.walkDrawing J' W₂
  refine ⟨P, GM11.walkDrawing_isSubdrawing J' W₂, GM11.walkDrawing_isPathBetween J' hW₂_simple, ?_⟩
  -- Step 5: Every edge `e ∈ P.E` has odd count in `List.ofFn e_fn`, hence is neither type (iii)
  -- nor type (iv).
  intro e heP
  rw [GM11.walkDrawing_E] at heP
  have hodd : Odd ((List.ofFn e_fn).count e) := hW₀_edges ▸ hW₁_odd e (hW₂_sub_W₁ e heP)
  have hcount_pos : 0 < (List.ofFn e_fn).count e := by
    rcases hodd with ⟨k, hk⟩
    omega
  have he_mem_ofFn : e ∈ List.ofFn e_fn := List.count_pos_iff.mp hcount_pos
  rw [List.mem_ofFn] at he_mem_ofFn
  rcases he_mem_ofFn with ⟨p₀, rfl⟩
  let u₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hu₀ : u₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [u₀]
  let x₀ : N.D := γ (α_fn p₀ u₀)
  have hx₀_U : x₀ ∈ U_fn p₀ := ⟨u₀, hu₀, rfl⟩
  have hx₀_C₁ : x₀ ∈ C₁ := hU_sub_C₁ p₀ hx₀_U
  let z₀ : S := N.φ x₀
  have hz₀_e : z₀ ∈ e_fn p₀ := ⟨u₀, hu₀, rfl⟩
  constructor
  · -- `e_fn p₀` is not of type (iii)
    rintro ⟨he_bdS, he_sub_C₁⟩
    have hz₀_not_bdS : z₀ ∉ bd S := fun h => Set.eq_empty_iff_forall_notMem.mp he_bdS z₀ ⟨hz₀_e, h⟩
    have hz₀_not_seamV : z₀ ∉ N.seamV :=
      Disjoint.notMem_of_mem_left (hU_disj_seamV p₀) hx₀_U
    obtain ⟨i, w, hw_Ioo, hφw, hfiber, hfg_ne⟩ :=
      N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV
        (hU_bd p₀ hx₀_U) hz₀_not_bdS hz₀_not_seamV
    have hfw_C₁ : N.f i w ∈ C₁ := he_sub_C₁ z₀ hz₀_e (hfiber ▸ Or.inl rfl)
    have hgw_C₁ : N.g i w ∈ C₁ := he_sub_C₁ z₀ hz₀_e (hfiber ▸ Or.inr rfl)
    have hz₀_not_V : z₀ ∉ J'.V :=
      Disjoint.notMem_of_mem_left (hU_disj_V p₀) hx₀_U
    have hex_unique_U : ∀ y ∈ C₁, N.φ y ∉ J'.V →
        ∃ p : Fin m, ∀ q : Fin m, y ∈ U_fn q ↔ q = p := by
      exact unique_arc_segment_away_from_vertices (S := S) N J' (C₁ := C₁) γ hγ_inj hγ_Ioo m τ
        hτ_unique τ_I (fun _ _ => rfl) hτ_V U_fn hU_eq
    obtain ⟨p₁, hp₁⟩ := hex_unique_U (N.f i w) hfw_C₁ (hφw.symm ▸ hz₀_not_V)
    obtain ⟨p₂, hp₂⟩ := hex_unique_U (N.g i w) hgw_C₁
      (((N.φ_f_eq_φ_g i w).symm.trans hφw).symm ▸ hz₀_not_V)
    have hp12 : p₁ ≠ p₂ := by
      rintro rfl
      have hf_U : N.f i w ∈ U_fn p₁ := (hp₁ p₁).mpr rfl
      have hg_U : N.g i w ∈ U_fn p₁ := (hp₂ p₁).mpr rfl
      exact hfg_ne (hU_injOn p₁ hf_U hg_U (N.φ_f_eq_φ_g i w))
    have hiff : ∀ p : Fin m, e_fn p = e_fn p₀ ↔ p = p₁ ∨ p = p₂ := by
      exact edge_subdivision_indices_of_fiber (S := S) N J' m U_fn e_fn he_eq_φU
        (fun p => (he_edge p).1) p₀ z₀ hz₀_e i w hφw hfiber p₁ hp₁ p₂ hp₂
    have hcount2 : (List.ofFn e_fn).count (e_fn p₀) = 2 :=
      count_ofFn_eq_two e_fn (e_fn p₀) hp12 hiff
    rw [hcount2] at hodd
    rcases hodd with ⟨k, hk⟩
    omega
  · -- `e_fn p₀` is not of type (iv)
    rintro ⟨_, he_sub_C₂⟩
    have hx₀_C₂ : x₀ ∈ C₂ := he_sub_C₂ z₀ hz₀_e rfl
    exact Disjoint.notMem_of_mem_left hdisj_C12 hx₀_C₁ hx₀_C₂

end GraphMinor.GM07
