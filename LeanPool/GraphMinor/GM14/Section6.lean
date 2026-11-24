/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section6a
public import LeanPool.GraphMinor.GM14.Section6b
public import LeanPool.GraphMinor.GM14.Section6c
public import LeanPool.GraphMinor.GM14.Section8a
public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM14.Adapted
public import LeanPool.GraphMinor.GM14.RigidExtension
public import LeanPool.GraphMinor.GM14.RigidSegregation

/-!
# Graph Minors XIV, Section 6: Rigidity

This file completes the formalization of Section 6 ("Rigidity", pages 33–35) of
N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an embedding*, J. Combin. Theory
Ser. B **65** (1995) 23–50, re-exporting `GraphMinor.GM14.Section6a` (`(6.1)`, `(6.2)`),
`GraphMinor.GM14.Section6b`, and `GraphMinor.GM14.Section6c` (`(6.3)`), and proving:

- `theorem_6_4` (Graph Minors XIV, (6.4), page 34): an isomorphism between drawings `H₁, H₂` in a
  closed disc `Δ` that is the identity on `V(H₁) ∩ bd(Δ)` extends to a homeomorphism of `Δ` when
  `H₁` is rigid in `Δ`, from `Whitney.extension_64`.
- `claim_2_three_disjoint_paths_to_bar_6_5` and `theorem_6_5`
  (Graph Minors XIV, (6.5), pages 34–35): any arrangement `α` of a 3-segregation of `G` in `Δ` that
  fixes `V(H) ∩ bd(Δ)` can be modified to an arrangement `α'` compatible with `H`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM11

universe u v w

variable {S : Type u} [TopologicalSpace S]

/-! ## Homeomorphism Pushforwards for Surface Arrangements -/

/-- If `y ∈ f '' D` for a homeomorphism `f : S ≃ₜ S`, then `f.symm y ∈ D`. -/
theorem symm_mem_of_mem_image (f : S ≃ₜ S) {D : Set S} (y : f '' D) : f.symm y.1 ∈ D := by
  rcases y with ⟨_, x, hx, rfl⟩
  simpa using hx

/-- Restriction of a homeomorphism `f : S ≃ₜ S` to a subset `D : Set S` onto `f '' D`. -/
def homeomorphImageSet (f : S ≃ₜ S) (D : Set S) : D ≃ₜ f '' D where
  toFun x := ⟨f x.1, mem_image_of_mem f x.2⟩
  invFun y := ⟨f.symm y.1, symm_mem_of_mem_image f y⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x.1)
  right_inv y := Subtype.ext (f.apply_symm_apply y.1)
  continuous_toFun :=
    (f.continuous.comp continuous_subtype_val).subtype_mk (fun x => mem_image_of_mem f x.2)
  continuous_invFun :=
    (f.symm.continuous.comp continuous_subtype_val).subtype_mk (symm_mem_of_mem_image f)

/-- The image of a closed disc under a homeomorphism of `S` is a closed disc. -/
theorem isClosedDisc_image_homeomorph {D : Set S} (hD : IsClosedDisc D)
    (f : S ≃ₜ S) : IsClosedDisc (f '' D) := by
  obtain ⟨φ⟩ := hD
  exact ⟨φ.trans (homeomorphImageSet f D)⟩

/-- The image of an `O`-arc under a homeomorphism of `S` is an `O`-arc. -/
theorem isOArc_image_homeomorph {F : Set S} (hF : IsOArc F) (f : S ≃ₜ S) :
    IsOArc (f '' F) := by
  obtain ⟨φ⟩ := hF
  exact ⟨φ.trans (homeomorphImageSet f F)⟩

/-- A homeomorphism `f : S ≃ₜ S` commutes with `subBd`. -/
theorem image_subBd (f : S ≃ₜ S) (D : Set S) : f '' subBd D = subBd (f '' D) := by
  rw [subBd_eq_frontier, subBd_eq_frontier, Homeomorph.image_frontier]

/-- A homeomorphism `f : S ≃ₜ S` preserves interior points of `S`. -/
theorem isInteriorPoint_map_iff (f : S ≃ₜ S) (x : S) :
    IsInteriorPoint (f x) ↔ IsInteriorPoint x := by
  constructor
  · rintro ⟨U, hU, hfxU, ⟨φ⟩⟩
    refine ⟨f.symm '' U, f.symm.isOpenMap U hU, ⟨f x, hfxU, f.symm_apply_apply x⟩, ?_⟩
    exact ⟨(homeomorphImageSet f.symm U).symm.trans φ⟩
  · rintro ⟨U, hU, hxU, ⟨φ⟩⟩
    refine ⟨f '' U, f.isOpenMap U hU, mem_image_of_mem f hxU, ?_⟩
    exact ⟨(homeomorphImageSet f U).symm.trans φ⟩

/-- A homeomorphism `f : S ≃ₜ S` preserves `bd S`. -/
theorem mem_bd_map_iff (f : S ≃ₜ S) (x : S) : f x ∈ bd S ↔ x ∈ bd S :=
  not_congr (isInteriorPoint_map_iff f x)

/-- Pushing a surface arrangement through a homeomorphism `f : S ≃ₜ S` yields a surface
arrangement. -/
theorem IsSurfaceArrangement.map_homeomorph {α : Type v} {β : Type w}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (harr : IsSurfaceArrangement S_seg α_disc α_pt) (f : S ≃ₜ S) :
    IsSurfaceArrangement S_seg (fun S₀ => f '' α_disc S₀) (fun x => f (α_pt x)) where
  isClosedDisc S₀ hS₀ := by
    obtain ⟨hd, hpt⟩ := harr.isClosedDisc S₀ hS₀
    refine ⟨isClosedDisc_image_homeomorph hd f, fun x hx => ?_⟩
    rw [← image_subBd]
    exact mem_image_of_mem f (hpt x hx)
  inter_discs S₁ hS₁ S₂ hS₂ hne := by
    rw [← image_inter f.injective]
    exact (image_mono (harr.inter_discs S₁ hS₁ S₂ hS₂ hne)).trans (by rw [image_image])
  inter_bd S₀ hS₀ := by
    rintro _ ⟨⟨z, hzD, rfl⟩, hzbd⟩
    have hz_in : z ∈ α_disc S₀ ∩ bd S := ⟨hzD, (mem_bd_map_iff f z).mp hzbd⟩
    obtain ⟨v, hv, rfl⟩ := harr.inter_bd S₀ hS₀ hz_in
    exact ⟨v, hv, rfl⟩
  injOn_pts := f.injective.comp_injOn harr.injOn_pts
  natural_order S₀ hS₀ := by
    obtain ⟨hFo, φ, hpt, hcw⟩ := harr.natural_order S₀ hS₀
    rw [← image_subBd]
    refine ⟨isOArc_image_homeomorph hFo f, φ.trans (homeomorphImageSet f (subBd (α_disc S₀))),
      ?_, ?_⟩
    · intro v hv
      exact mem_image_of_mem f (hpt v hv)
    · intro v₁ v₂ v₃ h123
      obtain ⟨t₁, t₂, t₃, ht12, ht23, htpi, h1, h2, h3⟩ := hcw v₁ v₂ v₃ h123
      refine ⟨t₁, t₂, t₃, ht12, ht23, htpi, ?_, ?_, ?_⟩
      · change f (φ (Circle.exp t₁)).1 = f (α_pt v₁); rw [h1]
      · change f (φ (Circle.exp t₂)).1 = f (α_pt v₂); rw [h2]
      · change f (φ (Circle.exp t₃)).1 = f (α_pt v₃); rw [h3]

/-! ## Theorems (6.4) and (6.5) -/

variable [T2Space S]

/-- **Graph Minors XIV, (6.4)** (page 34):
"Let $\Delta$ be a closed disc, let $H_1, H_2$ be drawings in $\Delta$ with $V(H_1) \cap
\text{bd}(\Delta) = V(H_2) \cap \text{bd}(\Delta)$, and let $\phi \colon H_1 \to H_2$ be an
isomorphism such that $\phi(v) = v$ for all $v \in V(H_1) \cap \text{bd}(\Delta)$. If $H_1$ is
rigid in $\Delta$ then there is a homeomorphism $\psi \colon \Delta \to \Delta$ extending $\phi$."
-/
theorem theorem_6_4_proof {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ)
    {H₁ H₂ : Drawing S} (hH₁Δ : H₁.U ⊆ Δ) (hH₂Δ : H₂.U ⊆ Δ)
    (hH₁bd : H₁.U ∩ subBd Δ ⊆ H₁.V) (hH₂bd : H₂.U ∩ subBd Δ ⊆ H₂.V)
    (hbdV : H₁.V ∩ subBd Δ = H₂.V ∩ subBd Δ)
    (φ : Iso H₁.toGraph H₂.toGraph)
    (hφ_bd : ∀ v : V(H₁.toGraph), v.1 ∈ subBd Δ → (φ.vertexEquiv v).1 = v.1)
    (hrigid : ∀ F : Set S, F ⊆ Δ → IsOArc F → F ∩ H₁.U ⊆ H₁.V →
      (F ∩ H₁.V).ncard ≤ 2 → ∃ Δ' : Set S, Δ' ⊆ Δ ∧ IsDial H₁ F Δ') :
    ∃ ψ : S ≃ₜ S,
      ψ '' Δ = Δ ∧
      (∀ v : V(H₁.toGraph), ψ v.1 = (φ.vertexEquiv v).1) ∧
      (∀ e : E(H₁.toGraph), ψ '' e.1 = (φ.edgeEquiv e).1) ∧
      ψ '' H₁.V = H₂.V ∧
      ψ '' H₁.U = H₂.U ∧
      (∀ v ∈ H₁.V ∩ subBd Δ, ψ v = v) ∧
      (∀ x ∈ subBd Δ, ψ x = x) := by
  obtain ⟨ψ, hψΔ, hψ_bd, hψHV, hψHE⟩ :=
    Whitney.extension_64 hΔ hbdΔ hH₁Δ hH₂Δ hH₁bd hH₂bd hbdV φ hφ_bd hrigid
  have hVH : ψ '' H₁.V = H₂.V := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hψHV ⟨x, hx⟩
      rw [this]
      exact (φ.vertexEquiv ⟨x, hx⟩).2
    · intro hy
      let v : V(H₁.toGraph) := φ.vertexEquiv.symm ⟨y, hy⟩
      refine ⟨v.1, v.2, ?_⟩
      rw [hψHV v, Equiv.apply_symm_apply]
  have hUH : ψ '' H₁.U = H₂.U := by
    rw [H₁.U_eq, H₂.U_eq, image_union, hVH]
    refine congrArg (H₂.V ∪ ·) ?_
    ext y
    simp only [mem_image, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, ⟨e, he, hxe⟩, rfl⟩
      let e' : E(H₂.toGraph) := φ.edgeEquiv ⟨e, he⟩
      refine ⟨e'.1, e'.2, ?_⟩
      rw [← hψHE ⟨e, he⟩, ← Homeomorph.image_closure ψ]
      exact mem_image_of_mem ψ hxe
    · rintro ⟨f, hf, hyf⟩
      let e : E(H₁.toGraph) := φ.edgeEquiv.symm ⟨f, hf⟩
      have he_eq : ψ '' e.1 = f := by
        simpa [e] using hψHE e
      have hcl_eq : ψ '' closure e.1 = closure f := by
        rw [Homeomorph.image_closure ψ, he_eq]
      rw [← hcl_eq] at hyf
      obtain ⟨x, hxe, rfl⟩ := hyf
      exact ⟨x, ⟨e.1, e.2, hxe⟩, rfl⟩
  refine ⟨ψ, hψΔ, hψHV, hψHE, hVH, hUH, ?_, hψ_bd⟩
  rintro v ⟨hvV, hvbd⟩
  have h1 := hψHV ⟨v, hvV⟩
  have h2 := hφ_bd ⟨v, hvV⟩ hvbd
  exact h1.trans h2

omit [T2Space S] in
/-- **Graph Minors XIV, (6.5), Claim (2), path-truncation step** (page 35):
Let `(A_H, B_H)` be the separation of `H` induced by `(A, Ω) ∈ S_seg` with
`V(A_H) ∩ V(B_H) = Ω_bar_H` and `|S₀.Ω.bar| ≤ 3`. If `A_H` contains a circuit `C` and there are
three mutually vertex-disjoint paths in `H` from `V(C)` to `V(B_H) ∪ Ω_bar_H` (by Claim (1), since
`V(H) ∩ bd(Δ) ⊆ V(B_H) ∪ Ω_bar_H`), then there are three mutually vertex-disjoint paths in `A_H`
from `V(C)` to `S₀.Ω.bar`, and hence `S₀.Ω.bar ⊆ V(A_H)` and `PreservesBarPaths S₀ A_H`. -/
theorem claim_2_three_disjoint_paths_to_bar_6_5 {α : Type v} {β : Type w}
    {H_G A_H B_H C : Graph α β} {S₀ : Society α β}
    (hSep : IsGraphSeparation H_G A_H B_H)
    (hInter : V(A_H) ∩ V(B_H) = S₀.Ω.bar)
    (hBar3 : S₀.Ω.bar.ncard ≤ 3)
    (hC : IsGraphCircuit A_H C)
    {P : Fin 3 → Graph α β} {u v : Fin 3 → α}
    (hP : ∀ i, IsGraphPathWithEnds H_G (P i) (u i) (v i) ∧ u i ∈ V(C) ∧ v i ∈ V(B_H) ∪ S₀.Ω.bar)
    (hDisj : Pairwise (fun i j => Disjoint V(P i) V(P j))) :
    (∃ (Q : Fin 3 → Graph α β) (x y : Fin 3 → α),
      (∀ i, Q i ≤ P i ∧ IsFromToPathWithEnds A_H (Q i) V(C) S₀.Ω.bar (x i) (y i)) ∧
      Pairwise (fun i j => Disjoint V(Q i) V(Q j))) ∧
    S₀.Ω.bar ⊆ V(A_H) ∧ E(A_H).Nonempty ∧ PreservesBarPaths S₀ A_H := by
  obtain ⟨Q, x, y, hQ, hQ_disj⟩ :=
    exists_three_disjoint_paths_from_circuit_to_bar hSep hInter hC.1 hP hDisj
  refine ⟨⟨Q, x, y, hQ, hQ_disj⟩,
    preservesBarPaths_of_three_disjoint_paths_from_circuit hBar3 hC (fun i => (hQ i).2) hQ_disj⟩

/-- **Graph Minors XIV, (6.5)** (pages 34–35):
"Let $H$ be a rigid drawing in a closed disc $\Delta$. Let $H$ be a subgraph of $G$, let
$\mathscr{S}$ be a 3-segregation of $G$ with $V(H) \cap \text{bd}(\Delta) \subseteq
V(\mathscr{S})$, and let $\alpha$ be an arrangement of $\mathscr{S}$ in $\Delta$ such that
$\alpha(v) = v$ for all $v \in V(H) \cap \text{bd}(\Delta)$. Then there is an arrangement
$\alpha'$ of $\mathscr{S}$ in $\Delta$ such that $\alpha'$ is compatible with $H$." -/
theorem theorem_6_5_proof {α : Type v} {β : Type w}
    {G : Graph α β} {H : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ)
    (hHΔ : H.U ⊆ Δ) (hHbd : H.U ∩ subBd Δ ⊆ H.V)
    (hrigid : ∀ F : Set S, F ⊆ Δ → IsOArc F → F ∩ H.U ⊆ H.V →
      (F ∩ H.V).ncard ≤ 2 → ∃ Δ' : Set S, Δ' ⊆ Δ ∧ IsDial H F Δ')
    (η : SpanEmbedding H G)
    {S_seg : Set (Society α β)} (hseg : IsThreeSegregation G S_seg)
    (hbd_in_seg : ∀ v ∈ H.V ∩ subBd Δ, η.vMap v ∈ segregationVertices S_seg)
    {α_disc : Society α β → Set S} {α_pt : α → S}
    (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (harr_Δ : ∀ S₀ ∈ S_seg, α_disc S₀ ⊆ Δ)
    (hα_id : ∀ v ∈ H.V ∩ subBd Δ, α_pt (η.vMap v) = v)
    (hα_bd : ∀ v ∈ H.V, η.vMap v ∈ segregationVertices S_seg → α_pt (η.vMap v) ∈ subBd Δ →
      v ∈ subBd Δ) :
    ∃ (α'_disc : Society α β → Set S) (α'_pt : α → S),
      IsSurfaceArrangement S_seg α'_disc α'_pt ∧
      (∀ S₀ ∈ S_seg, α'_disc S₀ ⊆ Δ) ∧
      IsCompatibleWith G H η S_seg α'_disc α'_pt ∧
      (∀ x, α_pt x ∈ subBd Δ → α'_pt x = α_pt x) ∧
      (∀ x, α_pt x ∈ Δ \ subBd Δ → α'_pt x ∈ Δ \ subBd Δ) ∧
      (∀ S₀ ∈ S_seg, α'_disc S₀ ∩ subBd Δ = α_disc S₀ ∩ subBd Δ) := by
  obtain ⟨H', φ, hH'Δ, hH'bd, hbdV, h_i, h_ii⟩ :=
    Whitney.union_drawing_65 hΔ hbdΔ hHΔ hHbd hrigid η hseg hbd_in_seg harr harr_Δ hα_id hα_bd
  -- From (i), `φ(v) = v` for all `v ∈ V(H) ∩ bd(Δ)` since `α(v) = v` on `V(H) ∩ bd(Δ)`.
  have hφ_bd : ∀ v : V(H.toGraph), v.1 ∈ subBd Δ → (φ.vertexEquiv v).1 = v.1 := by
    intro v hvbd
    have hv_mem : v.1 ∈ H.V ∩ subBd Δ := ⟨v.2, hvbd⟩
    have h1 := (h_i v (hbd_in_seg v.1 hv_mem)).symm
    have h2 := hα_id v.1 hv_mem
    exact h1.trans h2
  -- By (6.4), there is a homeomorphism `ψ : Δ → Δ` extending `φ`.
  obtain ⟨ψ, hψΔ, hψV, hψE, _, hψHU, _, hψ_bd⟩ :=
    theorem_6_4_proof hΔ hbdΔ hHΔ hH'Δ hHbd hH'bd hbdV φ hφ_bd hrigid
  -- Define `α'(A, Ω) = ψ⁻¹(α(A, Ω))` and `α'(v) = ψ⁻¹(α(v))`.
  let α'_disc : Society α β → Set S := fun S₀ => ψ.symm '' α_disc S₀
  let α'_pt : α → S := fun x => ψ.symm (α_pt x)
  have hψ_symm_bd : ∀ y ∈ subBd Δ, ψ.symm y = y := fun y hy =>
    ψ.symm_apply_eq.mpr (hψ_bd y hy).symm
  refine ⟨α'_disc, α'_pt, harr.map_homeomorph ψ.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro S₀ hS₀
    rintro _ ⟨y, hy, rfl⟩
    have hyΔ : y ∈ ψ '' Δ := hψΔ.symm ▸ harr_Δ S₀ hS₀ hy
    obtain ⟨x, hxΔ, rfl⟩ := hyΔ
    simpa using hxΔ
  · refine ⟨?_, ?_, ?_, ?_⟩
    · -- `(i)` `α'(η(v)) = v` for `v ∈ V(H)` with `η(v) ∈ V(S_seg)`.
      intro v hvV hsegv
      change ψ.symm (α_pt (η.vMap v)) = v
      rw [h_i ⟨v, hvV⟩ hsegv, ← hψV ⟨v, hvV⟩, ψ.symm_apply_apply]
    · -- `(ii)` `U(H) ∩ bd(α'(A, Ω)) = {v ∈ V(H) : η(v) ∈ ΩBar}`.
      intro S₀ hS₀
      obtain ⟨hbd_S₀, -, -⟩ := h_ii S₀ hS₀
      ext x
      simp only [α'_disc, ← image_subBd ψ.symm (α_disc S₀), mem_inter_iff]
      constructor
      · rintro ⟨hxU, y, hybd, rfl⟩
        have hyH'U : y ∈ H'.U := by
          rw [← hψHU]
          exact ⟨ψ.symm y, hxU, ψ.apply_symm_apply y⟩
        have hy_in : y ∈ H'.U ∩ subBd (α_disc S₀) := ⟨hyH'U, hybd⟩
        rw [hbd_S₀] at hy_in
        obtain ⟨v, rfl, hv_bar⟩ := hy_in
        rw [← hψV v, ψ.symm_apply_apply]
        exact ⟨v.2, hv_bar⟩
      · rintro ⟨hxV, hx_bar⟩
        refine ⟨H.V_subset_U hxV, ψ x, ?_, ψ.symm_apply_apply x⟩
        have hxH' : ψ x ∈ H'.U ∩ subBd (α_disc S₀) := by
          rw [hbd_S₀]
          exact ⟨⟨x, hxV⟩, (hψV ⟨x, hxV⟩).symm, hx_bar⟩
        exact hxH'.2
    · -- `(ii)` `v ∈ α'(A, Ω) ↔ η(v) ∈ V(A)` for `v ∈ V(H)`.
      intro S₀ hS₀ v hvV
      obtain ⟨-, hV_S₀, -⟩ := h_ii S₀ hS₀
      have h1 := (hV_S₀ ⟨v, hvV⟩).symm
      have h2 : ψ v = (φ.vertexEquiv ⟨v, hvV⟩).1 := hψV ⟨v, hvV⟩
      rw [h1, ← h2]
      exact ⟨fun ⟨y, hy, hy_eq⟩ => by rwa [← hy_eq, ψ.apply_symm_apply],
        fun h => ⟨ψ v, h, ψ.symm_apply_apply v⟩⟩
    · -- `(ii)` `e ⊆ α'(A, Ω) ↔ η(e) ∈ E(A)` for `e ∈ E(H)`.
      intro S₀ hS₀ e heE
      obtain ⟨-, -, hE_S₀⟩ := h_ii S₀ hS₀
      have h1 := (hE_S₀ ⟨e, heE⟩).symm
      have h2 : ψ '' e = (φ.edgeEquiv ⟨e, heE⟩).1 := hψE ⟨e, heE⟩
      rw [h1, ← h2]
      constructor
      · rintro hsub _ ⟨x, hxe, rfl⟩
        obtain ⟨y, hy, hy_eq⟩ := hsub hxe
        rwa [← hy_eq, ψ.apply_symm_apply]
      · intro hsub x hxe
        exact ⟨ψ x, hsub (mem_image_of_mem ψ hxe), ψ.symm_apply_apply x⟩
  · intro x hx
    exact hψ_symm_bd (α_pt x) hx
  · rintro x ⟨hxΔ, hxnot⟩
    refine ⟨?_, fun hbd => hxnot ?_⟩
    · have hyΔ : α_pt x ∈ ψ '' Δ := hψΔ.symm ▸ hxΔ
      obtain ⟨y, hy, hy_eq⟩ := hyΔ
      simpa [α'_pt, ← hy_eq] using hy
    · have h_eq := hψ_bd (ψ.symm (α_pt x)) hbd
      rw [ψ.apply_symm_apply] at h_eq
      rw [h_eq]
      exact hbd
  · intro S₀ hS₀
    ext y
    simp only [α'_disc, mem_inter_iff, mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hybd⟩
      have hz_eq : ψ.symm z = z := by
        have h1 := hψ_bd (ψ.symm z) hybd
        rw [ψ.apply_symm_apply] at h1
        exact h1.symm
      refine ⟨?_, hybd⟩
      rwa [hz_eq]
    · rintro ⟨hyS₀, hybd⟩
      exact ⟨⟨y, hyS₀, hψ_symm_bd y hybd⟩, hybd⟩

end GraphMinor.GM14
