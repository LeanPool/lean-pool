/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PullLift
public import LeanPool.GraphMinor.GM19.ThinPainting
public import LeanPool.GraphMinor.GM19.Section4c

/-!
# Pulling a painting back to a fragment

Let `Γ` be a painting in `Σ`, let `K` be a drawing with `U(Γ) ∩ U(K) = V(Γ) ∩ V(K)`, and let `Σ₁` be
a
fragment of `Σ` after cutting along `U(K)`, with associated surjection `ψ`. Graph Minors XIX,
Section 5
(page 336) defines the painting `ψ⁻¹(Γ) ∩ Σ₁` by
`U₁ = ψ⁻¹(U(Γ)) ∪ bd(Σ₁)` and `V₁ = ψ⁻¹(V(Γ) ∪ V(K))`.

Its edges are of two kinds. The inner edges are the lifts of the edges of `Γ` that lie in the part
of `Σ`
that `Σ₁` covers, and such an edge has the same shape as the edge of `Γ` by `homeoClosure`. The
others are
the open arcs of `bd(Σ₁)` between points of `V₁`, and these are lines as long as each cuff of `Σ₁`
has two
points of `V₁`. That is a real condition. Cutting along a loop with one vertex gives a cuff with one
vertex, which no painting has. So we ask for it (`PullData.two`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [TopologicalSpace S₁] [T2Space S] [T2Space S₁]

/-- The set `V₁ = ψ⁻¹(V(Γ) ∪ V(K))`. -/
def pullV (Γ : Painting S) (K : Drawing S) (ψ : S₁ → S) : Set S₁ := ψ ⁻¹' (Γ.V ∪ K.V)

/-- The set `U₁ = ψ⁻¹(U(Γ)) ∪ bd(Σ₁)`. -/
def pullU (Γ : Painting S) (ψ : S₁ → S) : Set S₁ := ψ ⁻¹' Γ.U ∪ bd S₁

/-- The hypotheses of the pull-back. -/
structure PullData (Γ : Painting S) (K : Drawing S) (ψ : S₁ → S) : Prop where
  surface : IsSurface S
  frag : IsCuttingFragment S K S₁ ψ
  inter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V
  two : ∀ C : cuffs S₁, ∃ p ∈ pullV Γ K ψ ∩ C.1, ∃ q ∈ pullV Γ K ψ ∩ C.1, p ≠ q

/-- The lifts of the inner edges of `Γ`. -/
def liftPieces (Γ : Painting S) (ψ : S₁ → S) : Set (Set S₁) :=
  {p | ∃ e ∈ Γ.E, ¬ Painting.IsBorder e ∧ p.Nonempty ∧ p = ψ ⁻¹' e}

/-- The edges of the pull-back. -/
def pullPieces (Γ : Painting S) (K : Drawing S) (ψ : S₁ → S) : Set (Set S₁) :=
  arcComponentsIn (bd S₁ \ pullV Γ K ψ) ∪ liftPieces Γ ψ

namespace PullData

variable {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S} (d : PullData Γ K ψ)
include d

omit [T2Space S] [T2Space S₁] in
theorem isClosed_bd : IsClosed (bd S₁) := (cuff_statement S₁ d.frag.isSurface).1

omit [T2Space S] [T2Space S₁] in
theorem isOpen_R : IsOpen (IsCuttingFragment.R ψ) :=
  d.frag.isOpen_R d.surface K.isClosed_U

omit [T2Space S] [T2Space S₁] in
theorem finite_pullV : (pullV Γ K ψ).Finite :=
  (Γ.finite_V.union K.finite_V).preimage' fun y _ ↦ d.frag.finite_fibres y

omit [T2Space S] [T2Space S₁] in
theorem disjoint_K {e : Set S} (he : e ∈ Γ.E) : Disjoint e K.U := by
  refine disjoint_left.mpr fun x hx hxK ↦ ?_
  exact Γ.disjoint_V he hx (d.inter ⟨he.2.1 hx |>.1, hxK⟩).1

omit [T2Space S] [T2Space S₁] in
theorem subset_R {e : Set S} (he : e ∈ Γ.E) (hb : ¬ Painting.IsBorder e)
    (hne : (ψ ⁻¹' e).Nonempty) : e ⊆ IsCuttingFragment.R ψ := by
  obtain ⟨x, hx⟩ := hne
  have hoff : e ⊆ (bd S ∪ K.U)ᶜ := by
    rintro y hy (hyb | hyK)
    · exact hb ⟨y, hy, hyb⟩
    · exact disjoint_left.mp (d.disjoint_K he) hy hyK
  have hxi : x ∉ bd S₁ := fun hxb ↦ hoff hx (d.frag.maps_bd (mem_image_of_mem ψ hxb))
  obtain ⟨z, hz, hzc⟩ := d.frag.interior_component
  have hxR : ψ x ∈ connectedComponentIn (bd S ∪ K.U)ᶜ z := by
    rw [hzc]
    exact mem_image_of_mem ψ hxi
  have hsub := he.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hx hoff
  rw [← connectedComponentIn_eq hxR] at hsub
  rwa [IsCuttingFragment.R, ← hzc]

omit [T2Space S] [T2Space S₁] in
theorem preimage_subset_int {e : Set S} (hsub : e ⊆ IsCuttingFragment.R ψ) :
    ψ ⁻¹' e ⊆ (bd S₁)ᶜ := fun _ hx ↦ d.frag.mem_R_iff.mp (hsub hx)

omit [T2Space S] [T2Space S₁] in
theorem mem_bd_of_notMem_R {x : S₁} (hx : ψ x ∈ bd S ∪ K.U) : x ∈ bd S₁ := by
  by_contra hn
  exact disjoint_left.mp d.frag.disjoint_R (mem_image_of_mem ψ hn) hx

omit [T2Space S] [T2Space S₁] in
/-- A point of `V₁` over `V(K)`, or any point over `U(K)`, lies on the boundary. -/
theorem pullV_subset : pullV Γ K ψ ⊆ pullU Γ ψ := by
  rintro x (hx | hx)
  · exact Or.inl (Γ.V_subset hx)
  · exact Or.inr (d.mem_bd_of_notMem_R (Or.inr (K.V_subset_U hx)))

omit [T2Space S] in
theorem finite_pieces : (pullPieces Γ K ψ).Finite := by
  refine (finite_arcComponentsIn_bd d.frag.isSurface d.finite_pullV d.two).union ?_
  refine (Γ.finite_edges.image fun e ↦ ψ ⁻¹' e).subset ?_
  rintro p ⟨e, he, -, -, rfl⟩
  exact mem_image_of_mem _ he

/-- The pieces are the edges: they are connected, disjoint, closed in `U₁ \ V₁`, and cover `U₁ \
V₁`. -/
theorem arcComponentsIn_eq : arcComponentsIn (pullU Γ ψ \ pullV Γ K ψ) = pullPieces Γ K ψ := by
  have hSur := d.frag.isSurface
  have hR := d.isOpen_R
  have hbd := d.isClosed_bd
  have har := fun {p} (hp : p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) ↦
    exists_arc_of_mem hSur (fun C ↦ ((cuff_statement S₁ hSur).2.2 C.1 C.2).some) d.finite_pullV
      d.two hp
  refine arcComponentsIn_of_pieces d.finite_pieces ?_ ?_ ?_ ?_
  · rintro p (hp | ⟨e, he, hb, hne, rfl⟩)
    · exact hp.2.2.1
    · exact d.frag.isPathConnected_preimage hbd hR (d.subset_R he hb hne) he.2.2.1
  · have hbl : ∀ {p q}, p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ) → q ∈ liftPieces Γ ψ →
        Disjoint p q := by
      rintro p _ hp ⟨e, he, hb, hne, rfl⟩
      exact disjoint_left.mpr fun x hxp hxq ↦
        d.preimage_subset_int (d.subset_R he hb hne) hxq (hp.2.1 hxp).1
    rintro p (hp | hp) q (hq | hq) hne
    · exact disjoint_iff_forall_ne.mpr fun x hx y hy he ↦ hne
        (arcComp_eq_of_mem hp hq hx (he ▸ hy))
    · exact hbl hp hq
    · exact (hbl hq hp).symm
    · obtain ⟨e, he, -, -, rfl⟩ := hp
      obtain ⟨e', he', -, -, rfl⟩ := hq
      have hee : e ≠ e' := fun h ↦ hne (h ▸ rfl)
      refine disjoint_left.mpr fun x hx hx' ↦ hee ?_
      exact arcComp_eq_of_mem he he' hx hx'
  · rintro p (hp | ⟨e, he, hb, hne, rfl⟩) x ⟨hxc, hxU, hxV⟩
    · obtain ⟨C, a, b, hab, hub, rfl, -, ha, hb⟩ := har hp
      by_contra hxn
      have ht : x ∈ tilde (arcOf _ a b) := ⟨hxc, hxn⟩
      rw [tilde_arcOf _ hab hub] at ht
      rcases ht with rfl | rfl
      · exact hxV ha
      · exact hxV hb
    · by_contra hxn
      have hsur := d.frag.image_tilde_preimage (d.subset_R he hb hne)
      have ht : ψ x ∈ tilde e := hsur ▸ mem_image_of_mem ψ ⟨hxc, hxn⟩
      exact hxV (Or.inl (Γ.tilde_subset_V he ht))
  · ext x
    constructor
    · rintro ⟨hxU | hxb, hxV⟩
      · have hxV' : ψ x ∉ Γ.V := fun h ↦ hxV (Or.inl h)
        obtain ⟨e, he, hxe⟩ := exists_arcComp_superset (F := Γ.U \ Γ.V)
          (isPathConnected_singleton (ψ x)) (singleton_subset_iff.mpr ⟨hxU, hxV'⟩)
        have hxe' : ψ x ∈ e := hxe rfl
        by_cases hb : Painting.IsBorder e
        · have hxb : ψ x ∈ bd S := (Γ.border_edge e he hb).2 hxe'
          have hxi := d.mem_bd_of_notMem_R (Or.inl hxb)
          obtain ⟨p, hp, hxp⟩ := exists_arcComp_superset (F := bd S₁ \ pullV Γ K ψ)
            (isPathConnected_singleton x) (singleton_subset_iff.mpr ⟨hxi, hxV⟩)
          exact ⟨p, Or.inl hp, hxp rfl⟩
        · exact ⟨ψ ⁻¹' e, Or.inr ⟨e, he, hb, ⟨x, hxe'⟩, rfl⟩, hxe'⟩
      · obtain ⟨p, hp, hxp⟩ := exists_arcComp_superset (F := bd S₁ \ pullV Γ K ψ)
          (isPathConnected_singleton x) (singleton_subset_iff.mpr ⟨hxb, hxV⟩)
        exact ⟨p, Or.inl hp, hxp rfl⟩
    · rintro ⟨p, hp | ⟨e, he, hb, hne, rfl⟩, hxp⟩
      · exact ⟨Or.inr (hp.2.1 hxp).1, (hp.2.1 hxp).2⟩
      · refine ⟨Or.inl (he.2.1 hxp).1, ?_⟩
        rintro (hxV | hxK)
        · exact (he.2.1 hxp).2 hxV
        · exact disjoint_left.mp (d.disjoint_K he) hxp (K.V_subset_U hxK)

/-! ### The shape of a lifted edge -/

variable {e : Set S}

theorem injOn_closure (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ) :
    InjOn ψ (closure (ψ ⁻¹' e)) := by
  intro x hx y hy hxy
  have h := (d.frag.bijective_closureMap d.isClosed_bd d.isOpen_R hsub
    (fun _ hv ↦ Γ.isConnectedNear he hv)).1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
  exact congrArg Subtype.val h

theorem ncard_tilde (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ) :
    (tilde (ψ ⁻¹' e)).ncard = (tilde e).ncard := by
  rw [← d.frag.image_tilde_preimage hsub]
  exact ((d.injOn_closure he hsub).mono sdiff_subset).ncard_image.symm

theorem finite_tilde (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ) :
    (tilde (ψ ⁻¹' e)).Finite := by
  have hfin : (ψ '' tilde (ψ ⁻¹' e)).Finite := by
    rw [d.frag.image_tilde_preimage hsub]
    exact Γ.finite_V.subset (Γ.tilde_subset_V he)
  exact Set.Finite.of_finite_image hfin ((d.injOn_closure he hsub).mono sdiff_subset)

/-- The closure of a lifted edge is homeomorphic to the closure of the edge, by `ψ`. -/
noncomputable def edgeHomeo (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ) :
    ↥(closure (ψ ⁻¹' e)) ≃ₜ ↥(closure e) :=
  d.frag.homeoClosure d.isClosed_bd d.isOpen_R hsub (fun _ hv ↦ Γ.isConnectedNear he hv)

theorem edgeHomeo_apply (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ)
    (x : ↥(closure (ψ ⁻¹' e))) : (d.edgeHomeo he hsub x).1 = ψ x.1 := rfl

/-- The ends of a lifted line are the points of `tilde` of the lift. -/
theorem lineEnds_closure (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ)
    (hends : lineEnds (closure e) = tilde e) :
    lineEnds (closure (ψ ⁻¹' e)) = tilde (ψ ⁻¹' e) := by
  have hinj := d.injOn_closure he hsub
  have himg := d.frag.image_tilde_preimage hsub
  let H := d.edgeHomeo he hsub
  ext u
  constructor
  · rintro ⟨w, f, hf₀, hf₁⟩
    have hu : ψ u ∈ tilde e := by
      rw [← hends]
      refine ⟨ψ w, f.trans H, ?_, ?_⟩
      · change (H (f 0)).1 = ψ u
        rw [d.edgeHomeo_apply he hsub, hf₀]
      · change (H (f 1)).1 = ψ w
        rw [d.edgeHomeo_apply he hsub, hf₁]
    rw [← himg] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    have hucl : u ∈ closure (ψ ⁻¹' e) := hf₀ ▸ (f 0).2
    exact hinj hx.1 hucl hxu ▸ hx
  · intro hu
    have hv : ψ u ∈ tilde e := himg ▸ mem_image_of_mem ψ hu
    rw [← hends] at hv
    obtain ⟨w, g, hg₀, hg₁⟩ := hv
    refine ⟨(H.symm (g 1)).1, g.trans H.symm, ?_, rfl⟩
    change (H.symm (g 0)).1 = u
    refine hinj (Subtype.property _) hu.1 ?_
    rw [← d.edgeHomeo_apply he hsub, Homeomorph.apply_symm_apply, hg₀]

theorem tilde_subset_discBd (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ)
    (hd : tilde e ⊆ discBd (closure e)) : tilde (ψ ⁻¹' e) ⊆ discBd (closure (ψ ⁻¹' e)) := by
  have hinj := d.injOn_closure he hsub
  have himg := d.frag.image_tilde_preimage hsub
  let H := d.edgeHomeo he hsub
  intro u hu
  obtain ⟨y, hy, hyu⟩ := hd (himg ▸ mem_image_of_mem ψ hu)
  refine ⟨H.symm y, ?_, ?_⟩
  · rw [← image_bd H.symm]
    exact mem_image_of_mem _ hy
  · refine hinj (Subtype.property _) hu.1 ?_
    rw [← d.edgeHomeo_apply he hsub, Homeomorph.apply_symm_apply, hyu]

/-- The shape of a lifted edge. -/
theorem edge_shape_lift (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ) :
    ((tilde (ψ ⁻¹' e)).ncard = 2 ∧ (tilde (ψ ⁻¹' e)).Finite ∧ IsLine (closure (ψ ⁻¹' e)) ∧
        lineEnds (closure (ψ ⁻¹' e)) = tilde (ψ ⁻¹' e)) ∨
      ((tilde (ψ ⁻¹' e)).ncard = 3 ∧ (tilde (ψ ⁻¹' e)).Finite ∧ IsClosedDisc (closure (ψ ⁻¹' e)) ∧
        tilde (ψ ⁻¹' e) ⊆ discBd (closure (ψ ⁻¹' e))) := by
  have hc := d.ncard_tilde he hsub
  have hf := d.finite_tilde he hsub
  let H := d.edgeHomeo he hsub
  rcases Γ.edge_shape e he with ⟨h₂, -, ⟨f⟩, hends⟩ | ⟨h₃, -, ⟨φ⟩, hs⟩
  · exact Or.inl ⟨hc.trans h₂, hf, ⟨f.trans H.symm⟩, d.lineEnds_closure he hsub hends⟩
  · exact Or.inr ⟨hc.trans h₃, hf, ⟨φ.trans H.symm⟩, d.tilde_subset_discBd he hsub hs⟩

end PullData

/-! ### The painting -/

/-- The march of a lifted edge. -/
noncomputable def liftMarch [Nonempty S₁] (Γ : Painting S) (ψ : S₁ → S) (p : Set S₁) : List S₁ :=
  (Γ.γ (ψ '' p)).map (Function.invFunOn ψ (tilde p))

open Classical in
/-- The marches of the pull-back: `γb` on the boundary arcs, and the lift of `γ_Γ` on the others. -/
noncomputable def pullγ [Nonempty S₁] (Γ : Painting S) (ψ : S₁ → S)
    (γb : Set S₁ → List S₁) (p : Set S₁) : List S₁ :=
  if p ∈ liftPieces Γ ψ then liftMarch Γ ψ p else γb p

namespace PullData

variable {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S} (d : PullData Γ K ψ)
include d

theorem liftMarch_spec [Nonempty S₁] {e : Set S} (he : e ∈ Γ.E) (hsub : e ⊆ IsCuttingFragment.R ψ) :
    (liftMarch Γ ψ (ψ ⁻¹' e)).Nodup ∧ {v | v ∈ liftMarch Γ ψ (ψ ⁻¹' e)} = tilde (ψ ⁻¹' e) := by
  have hsur : ψ '' (ψ ⁻¹' e) = e := image_preimage_eq_of_subset (hsub.trans
    (image_subset_range _ _))
  have hinj := (d.injOn_closure he hsub).mono (sdiff_subset (t := ψ ⁻¹' e))
  have himg := d.frag.image_tilde_preimage hsub
  have hright : ∀ y ∈ tilde e, Function.invFunOn ψ (tilde (ψ ⁻¹' e)) y ∈ tilde (ψ ⁻¹' e) ∧
      ψ (Function.invFunOn ψ (tilde (ψ ⁻¹' e)) y) = y := fun y hy ↦ by
    exact
    have hy' : y ∈ ψ '' tilde (ψ ⁻¹' e) := himg ▸ hy
    ⟨Function.invFunOn_mem hy', Function.invFunOn_eq hy'⟩
  have hset : ∀ v, v ∈ Γ.γ e ↔ v ∈ tilde e := fun v ↦ by
    have := Γ.γ_set e he
    exact Set.ext_iff.mp this v
  rw [liftMarch, hsur]
  constructor
  · refine List.Nodup.map_on (fun x hx y hy hxy ↦ ?_) (Γ.γ_nodup e he)
    rw [← (hright x ((hset x).mp hx)).2, hxy, (hright y ((hset y).mp hy)).2]
  · ext v
    simp only [mem_ofPred_eq, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hright y ((hset y).mp hy)).1
    · intro hv
      have hy : ψ v ∈ tilde e := himg ▸ mem_image_of_mem ψ hv
      refine ⟨ψ v, (hset _).mpr hy, ?_⟩
      exact hinj (hright _ hy).1 hv (hright _ hy).2

omit [T2Space S] in
/-- A boundary arc has the shape of a border edge. -/
theorem exists_ends {p : Set S₁} (hp : p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) :
    ∃ u v, u ≠ v ∧ tilde p = {u, v} ∧ IsLineWithEnds (closure p) u v := by
  have hSur := d.frag.isSurface
  let par : ∀ C : cuffs S₁, Circle ≃ₜ C.1 := fun C ↦ ((cuff_statement S₁ hSur).2.2 C.1 C.2).some
  obtain ⟨C, a, b, hab, hub, rfl, -, -, -⟩ := exists_arc_of_mem hSur par d.finite_pullV d.two hp
  have hL := isLine_arcOf (par C) hab hub
  exact ⟨_, _, (GM20.line_facts hL).1, tilde_arcOf (par C) hab hub, hL⟩

omit [T2Space S] [T2Space S₁] in
theorem notMem_liftPieces {p : Set S₁} (hp : p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) :
    p ∉ liftPieces Γ ψ := by
  rintro ⟨e, he, hb, hne, rfl⟩
  obtain ⟨x, hx⟩ := hne
  exact d.preimage_subset_int (d.subset_R he hb ⟨x, hx⟩) hx (hp.2.1 hx).1

end PullData

omit [T2Space S] [T2Space S₁] in
theorem pullγ_lift [Nonempty S₁] {Γ : Painting S} {ψ : S₁ → S} {γb : Set S₁ → List S₁} {p : Set S₁}
    (hp : p ∈ liftPieces Γ ψ) : pullγ Γ ψ γb p = liftMarch Γ ψ p := by
  simp [pullγ, hp]

omit [T2Space S] [T2Space S₁] in
theorem pullγ_arc [Nonempty S₁] {Γ : Painting S} {ψ : S₁ → S} {γb : Set S₁ → List S₁} {p : Set S₁}
    (hp : p ∉ liftPieces Γ ψ) : pullγ Γ ψ γb p = γb p := by
  simp [pullγ, hp]

/-- **The painting `ψ⁻¹(Γ) ∩ Σ₁`** (Graph Minors XIX, Section 5, page 336). The marches of the
boundary
arcs are given by `γb`. -/
noncomputable def pullPainting [Nonempty S₁] {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}
    (d : PullData Γ K ψ) (γb : Set S₁ → List S₁)
    (hγ₁ : ∀ p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ), (γb p).Nodup)
    (hγ₂ : ∀ p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ), {v | v ∈ γb p}
      = tilde p) : Painting S₁ where
  U := pullU Γ ψ
  V := pullV Γ K ψ
  γ := pullγ Γ ψ γb
  isClosed_U := (Γ.isClosed_U.preimage d.frag.continuous_ψ).union d.isClosed_bd
  V_subset := d.pullV_subset
  finite_V := d.finite_pullV
  bd_subset := subset_union_right
  finite_edges := by
    rw [d.arcComponentsIn_eq]
    exact d.finite_pieces
  edge_shape := by
    rw [d.arcComponentsIn_eq]
    rintro p (hp | ⟨e, he, hb, hne, rfl⟩)
    · obtain ⟨u, v, huv, ht, hL⟩ := d.exists_ends hp
      obtain ⟨f, -⟩ := id hL
      exact Or.inl ⟨by rw [ht, ncard_pair huv], by rw [ht]; exact (finite_singleton v).insert u,
        ⟨f⟩,
        by rw [ht]; exact (GM20.line_facts hL).2.2.2⟩
    · exact d.edge_shape_lift he (d.subset_R he hb hne)
  γ_nodup := by
    rw [d.arcComponentsIn_eq]
    rintro p (hp | hp)
    · rw [pullγ_arc (d.notMem_liftPieces hp)]
      exact hγ₁ p hp
    · rw [pullγ_lift hp]
      obtain ⟨e, he, hb, hne, rfl⟩ := hp
      exact (d.liftMarch_spec he (d.subset_R he hb hne)).1
  γ_set := by
    rw [d.arcComponentsIn_eq]
    rintro p (hp | hp)
    · rw [pullγ_arc (d.notMem_liftPieces hp)]
      exact hγ₂ p hp
    · rw [pullγ_lift hp]
      obtain ⟨e, he, hb, hne, rfl⟩ := hp
      exact (d.liftMarch_spec he (d.subset_R he hb hne)).2
  border_edge := by
    rw [d.arcComponentsIn_eq]
    rintro p (hp | ⟨e, he, hb, hne, rfl⟩) ⟨x, hxp, hxb⟩
    · obtain ⟨u, v, huv, ht, -⟩ := d.exists_ends hp
      exact ⟨by rw [ht, ncard_pair huv], fun y hy ↦ (hp.2.1 hy).1⟩
    · exact absurd hxb (d.preimage_subset_int (d.subset_R he hb hne) hxp)

end GraphMinor.GM19
