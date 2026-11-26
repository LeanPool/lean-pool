/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5i

/-!
# Graph Minors XIX, proof of (5.4): the marches of the pull-back

The map `ψ` carries the march of an edge of `Γ₁` over `bd(Σ)`, or of a lifted edge, to the march of
its image. For a
lifted edge this holds by definition. For a border edge we use that the side above it is directed as
in the paper, so
that `ψ` maps its direction to that of the side of `Φ` below it.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]


omit [T2Space S] [T2Space S₁] in
/-- A map that is one-to-one on the closure of `R` and carries the direction of `R` to that of `s`
carries the direction
of each part of `R` to that of `s`. -/
theorem dirAgrees_image {ψ : S₁ → S} (hc : Continuous ψ) {R e₁ : Set S₁} {s : Set S} {γR l : List
  S₁} {γs : List S}
    (hd₁ : DirAgrees R γR e₁ l) (hd₂ : DirAgrees s γs (ψ '' R) (γR.map ψ)) (hinj : InjOn ψ
      (closure R))
    (hcl : MapsTo ψ (closure R) (closure s)) : DirAgrees s γs (ψ '' e₁) (l.map ψ) := by
  obtain ⟨f₁, t₁, t₂, h12, hsub, h01, h11, hl1, hl2⟩ := hd₁
  obtain ⟨c, t₃, t₄, h34, hsub2, hc0, hc1, hhead, hlast⟩ := hd₂
  let G : unitInterval → unitInterval := fun t ↦ c.symm ⟨ψ (f₁ t).1, hcl (f₁ t).2⟩
  have hcG : ∀ t, (c (G t)).1 = ψ (f₁ t).1 := fun t ↦ by simp [G]
  have hGc : Continuous G := c.symm.continuous.comp ((hc.comp (continuous_subtype_val.comp
    f₁.continuous)).subtype_mk _)
  have hGi : Function.Injective G := fun a b hab ↦ by
    have h := (hcG a).symm.trans ((congrArg (fun t ↦ (c t).1) hab).trans (hcG b))
    exact f₁.injective (Subtype.ext (hinj (f₁ a).2 (f₁ b).2 h))
  rw [List.head?_map, h01] at hhead
  rw [List.getLast?_map, h11] at hlast
  simp only [Option.map_some, Option.some.injEq] at hhead hlast
  have hG0 : G ⊥ = t₃ := c.injective (Subtype.ext ((hcG _).trans hhead))
  have hG1 : G ⊤ = t₄ := c.injective (Subtype.ext ((hcG _).trans hlast))
  have hmono : StrictMono G :=
    hGc.strictMono_of_inj_boundedOrder (by rw [hG0, hG1]; exact h34.le) hGi
  refine ⟨c, G t₁, G t₂, hmono h12, (image_mono hsub).trans hsub2, hc0, hc1, ?_, ?_⟩
  · rw [List.head?_map, hl1, hcG]
    rfl
  · rw [List.getLast?_map, hl2, hcG]
    rfl

variable {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}

/-- The painting `ψ⁻¹(Γ) ∩ Σ₁`. -/
noncomputable abbrev FrameData.paint [Nonempty S₁] (D : FrameData Φ Γ K ψ) (flip : Set S₁
  → Bool) : Painting S₁ :=
  pullPainting D.pull (D.borderMarch flip)
    (fun _ hp ↦ (D.nodup_arcMarch _ D.pull.finite_pullV D.pull.two hp).1)
    (fun _ hp ↦ (D.nodup_arcMarch _ D.pull.finite_pullV D.pull.two hp).2)

/-- The frame `ψ⁻¹(Φ) ∩ Σ₁`. -/
noncomputable abbrev FrameData.frame (D : FrameData Φ Γ K ψ) (hF : IsFeature Φ K) (flip : Set S₁
  → Bool) : Frame S₁ :=
  pullFrame D flip (D.long_disjoint hF)

/-- The choice of direction of the sides of the frame of a fragment that the paper makes. -/
def IsPaperFlip (Φ : Frame S) (K : Drawing S) (ψ : S₁ → S) (hS₁ : IsSurface S₁) (flip : Set S₁
  → Bool) : Prop :=
  ∀ R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ), ∀ s ∈ Φ.sides, ψ '' R ⊆ s →
    DirAgrees s (Φ.γ s) (ψ '' R) ((arcMarch hS₁ (flip R) R).map ψ)

omit [T2Space S] in
/-- The ends of an arc of `bd(Σ₁) \ V₁` lie in `V₁`. -/
theorem PullData.tilde_subset {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}
  (d : PullData Γ K ψ) {R : Set S₁}
    (hR : R ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) : tilde R ⊆ pullV Γ K ψ := by
  obtain ⟨C, a, b, hab, hub, rfl, -, ha, hb⟩ :=
    exists_arc_of_mem d.frag.isSurface (cuffPar d.frag.isSurface) d.finite_pullV d.two hR
  rw [tilde_arcOf _ hab hub]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

namespace FrameData

variable [Nonempty S₁] (D : FrameData Φ Γ K ψ) {flip : Set S₁ → Bool}
include D

omit [Nonempty S₁] in
omit [T2Space S] in
/-- The march of an arc is its two ends. -/
theorem exists_march_pair {e₁ : Set S₁} (he₁ : e₁ ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ))
  (ε : Bool) :
    ∃ x y, arcMarch D.pull.frag.isSurface ε e₁ = [x, y] ∧ tilde e₁ = {x, y} := by
  have hS₁ := D.pull.frag.isSurface
  obtain ⟨C, a, b, hab, hub, he, -, -, -⟩ := exists_arc_of_mem hS₁ (cuffPar hS₁)
    D.pull.finite_pullV D.pull.two he₁
  obtain ⟨C', a', b', hab', hub', he', hl⟩ := arcMarch_spec hS₁ ε hab hub he
  have ht := tilde_arcOf (cuffPar hS₁ C') hab' hub'
  rw [← he'] at ht
  cases ε
  · exact ⟨_, _, by simpa using hl, ht⟩
  · exact ⟨_, _, by simpa using hl, by rw [ht, pair_comm]⟩

omit [Nonempty S₁] in
omit [T2Space S] [T2Space S₁] in
/-- A side of the fragment that has a point over `bd(Σ)` lies over a side of `Φ`. -/
theorem exists_side_of_bd {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) {x :
  S₁} (hx : x ∈ R)
    (hb : ψ x ∈ bd S) : ∃ s ∈ Φ.sides, ψ '' R ⊆ s := by
  rcases D.image_side hR with h | ⟨e, he, hsub⟩
  · exact h
  · have hxe := he.2.1 (hsub (mem_image_of_mem ψ hx))
    exact absurd (D.K_bd ⟨hxe.1, hb⟩) hxe.2

omit [Nonempty S₁] in
/-- `ψ` is one-to-one on the closure of a side of the fragment over a side of `Φ`. -/
theorem injOn_closure_side {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) {s :
  Set S}
    (hs : s ∈ Φ.sides) (hsub : ψ '' R ⊆ s) : InjOn ψ (closure R) := by
  have hS₁ := D.pull.frag.isSurface
  obtain ⟨C, a, b, hab, hub, rfl, -, ha, hb⟩ := exists_arc_of_mem hS₁
    (cuffPar hS₁) D.finite_pullFrameV D.two hR
  have hLn := isLine_arcOf (cuffPar hS₁ C) hab hub
  have hne := D.image_ends_ne hR hs hsub hLn (tilde_arcOf _ hab hub)
  have hmem : ∀ {x}, x ∈ closure (arcOf (cuffPar hS₁ C) a b) → x ∈ arcOf (cuffPar hS₁ C) a b ∨
      x = cuffPoint (cuffPar hS₁ C) a ∨ x = cuffPoint (cuffPar hS₁ C) b := fun {x} hx ↦ by
    by_cases h : x ∈ arcOf (cuffPar hS₁ C) a b
    · exact Or.inl h
    · have ht : x ∈ tilde (arcOf (cuffPar hS₁ C) a b) := ⟨hx, h⟩
      rw [tilde_arcOf _ hab hub] at ht
      exact Or.inr ht
  have hoff : ∀ {x y}, x ∈ arcOf (cuffPar hS₁ C) a b → y ∈ pullFrameV Φ K ψ → ψ x ≠ ψ y
    := fun hx hy heq ↦
    (hR.2.1 hx).2 (by
      change ψ _ ∈ Φ.V ∪ K.V
      rw [heq]
      exact hy)
  intro x hx y hy hxy
  rcases hmem hx with h₁ | rfl | rfl <;> rcases hmem hy with h₂ | rfl | rfl
  · exact D.injOn_side hR hR hs hs hsub hsub h₁ h₂ hxy
  · exact absurd hxy (hoff h₁ ha)
  · exact absurd hxy (hoff h₁ hb)
  · exact absurd hxy.symm (hoff h₂ ha)
  · rfl
  · exact absurd hxy hne
  · exact absurd hxy.symm (hoff h₂ hb)
  · exact absurd hxy.symm hne
  · rfl

/-- `ψ` carries the march of a border edge of `Γ₁` over `bd(Σ)` to the march of its image. -/
theorem map_march_border (hflip : IsPaperFlip Φ K ψ D.pull.frag.isSurface flip) {e₁ : Set S₁}
    (he₁ : e₁ ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ)) {x₀ : S₁} (hx₀ : x₀ ∈ e₁)
      (hb₀ : ψ x₀ ∈ bd S) :
    ((D.paint flip).γ e₁).map ψ = Γ.γ (ψ '' e₁) := by
  have hS₁ := D.pull.frag.isSurface
  have hc := D.pull.frag.continuous_ψ
  obtain ⟨he, hpre⟩ := D.pull.image_border_edge he₁ hx₀ hb₀
  obtain ⟨R, hR, hes⟩ := exists_arcComp_superset he₁.2.2.1 (F := bd S₁ \ pullFrameV Φ K ψ)
    (fun x hx ↦ ⟨(he₁.2.1 hx).1, fun h ↦ (he₁.2.1 hx).2 (D.pullFrameV_subset h)⟩)
  obtain ⟨s, hs, hsub⟩ := D.exists_side_of_bd hR (hes hx₀) hb₀
  have hl := D.pull.notMem_liftPieces he₁
  have hγ : (D.paint flip).γ e₁ = arcMarch hS₁ (flip R) e₁ := by
    change pullγ Γ ψ _ e₁ = _
    rw [pullγ_arc hl]
    change arcMarch _ (flip (sideOf Φ K ψ e₁)) e₁ = _
    rw [sideOf_eq he₁.1 hR hes]
  rw [hγ]
  have hd₁ := D.dirAgrees_pull flip he₁ hR hes
  have hd₂ := hflip R hR s hs hsub
  have hcl : MapsTo ψ (closure R) (closure s) := fun x hx ↦
    closure_mono hsub (image_closure_subset_closure_image hc (mem_image_of_mem ψ hx))
  have hT := dirAgrees_image hc hd₁ hd₂ (D.injOn_closure_side hR hs hsub) hcl
  have hbd := D.pull.image_arc_subset_bd he₁ hx₀ hb₀
  obtain ⟨x, y, hl, ht⟩ := D.exists_march_pair he₁ (flip R)
  have htx : x ∈ tilde e₁ := by rw [ht]; exact mem_insert _ _
  have hty : y ∈ tilde e₁ := by rw [ht]; exact mem_insert_of_mem _ rfl
  have hxV := D.pull.tilde_subset he₁ htx
  have hyV := D.pull.tilde_subset he₁ hty
  have hx : ψ x ∉ ψ '' e₁ := by
    rintro ⟨w, hw, hwx⟩
    exact (he₁.2.1 hw).2 (by change ψ w ∈ Γ.V ∪ K.V; rw [hwx]; exact hxV)
  have hy : ψ y ∉ ψ '' e₁ := by
    rintro ⟨w, hw, hwx⟩
    exact (he₁.2.1 hw).2 (by change ψ w ∈ Γ.V ∪ K.V; rw [hwx]; exact hyV)
  have hte : tilde (ψ '' e₁) = {ψ x, ψ y} := by
    rw [tilde, D.pull.frag.isClosedMap.closure_image_eq_of_continuous hc]
    ext z
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hz⟩
      have hwt : w ∈ tilde e₁ := ⟨hw, fun hwe ↦ hz (mem_image_of_mem ψ hwe)⟩
      rw [ht] at hwt
      rcases hwt with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨mem_image_of_mem ψ htx.1, hx⟩
      · exact ⟨mem_image_of_mem ψ hty.1, hy⟩
  have hbE : Painting.IsBorder (ψ '' e₁) := ⟨ψ x₀, mem_image_of_mem ψ hx₀, hb₀⟩
  have hne : ψ x ≠ ψ y := by
    intro h
    have h2 := (Γ.border_edge _ he hbE).1
    rw [hte, h, pair_eq_singleton, ncard_singleton] at h2
    omega
  rw [hl]
  rcases Γ.march_of_arc he hne hte with h | h
  · exact h.symm
  · have hd := D.fits.border_dir _ he hbE s hs ((image_mono hes).trans hsub)
    rw [h] at hd
    rw [hl] at hT
    exact (dirAgrees_not_reverse hT hd).elim

/-- `ψ` carries the march of a lifted edge to the march of the edge. -/
theorem map_march_lift {e : Set S} (he : e ∈ Γ.E) (hb : ¬ Painting.IsBorder e) (hne :
  (ψ ⁻¹' e).Nonempty) :
    ((D.paint flip).γ (ψ ⁻¹' e)).map ψ = Γ.γ e := by
  have hsub := D.pull.subset_R he hb hne
  have hl : ψ ⁻¹' e ∈ liftPieces Γ ψ := ⟨e, he, hb, hne, rfl⟩
  have hsur : ψ '' (ψ ⁻¹' e) = e := image_preimage_eq_of_subset (hsub.trans
    (image_subset_range _ _))
  change (pullγ Γ ψ _ (ψ ⁻¹' e)).map ψ = _
  rw [pullγ_lift hl, liftMarch, hsur, List.map_map]
  have himg := D.pull.frag.image_tilde_preimage hsub
  conv_rhs => rw [← List.map_id (Γ.γ e)]
  refine List.map_congr_left fun y hy ↦ ?_
  have hy' : y ∈ ψ '' tilde (ψ ⁻¹' e) := by
    rw [himg, ← Γ.γ_set e he]
    exact hy
  exact Function.invFunOn_eq hy'

end FrameData

end GraphMinor.GM19
