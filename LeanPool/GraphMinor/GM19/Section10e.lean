/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10d
public import LeanPool.GraphMinor.GM19.Section6a

/-!
# Arms of a side, and images

Tools for (10.2) and (10.3): the arm `(Γ ∩ Σ₁, π)` of a location with one member, and its image
under a homeomorphism.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


/-- The arm with sides `Γ ∩ A` and `Γ ∩ B`. -/
def restrictArm (Γ : Painting S) (A B : Set S) (h : Γ.toHypergraph.IsSeparation (Γ.restrict A)
  (Γ.restrict B)) (π : List S)
    (hn : π.Nodup) (hs : {v | v ∈ π} = (Γ.restrict A ∩ Γ.restrict B).vertexSet) : Arm Γ where
  minus := Γ.restrict A
  compl := Γ.restrict B
  isSeparation := h
  π := π
  π_nodup := hn
  π_set := hs

/-- A location with one member. -/
def oneLocation {Γ : Painting S} (A : Arm Γ) : RootedLocation Γ where
  arms := {A}
  finite_arms := finite_singleton A
  disjoint_arms _A₁ h₁ _A₂ h₂ hne := absurd (h₁.trans h₂.symm) hne

omit [T2Space S] in
theorem oneLocation_M_V {Γ : Painting S} (A : Arm Γ) :
    (oneLocation A).M.vertexSet = Γ.V ∩ {v | v ∈ A.compl.vertexSet} := by
  ext v
  simp [RootedLocation.M, oneLocation]

omit [T2Space S] in
theorem oneLocation_M_E {Γ : Painting S} (A : Arm Γ) :
    (oneLocation A).M.edgeSet = Γ.E ∩ {e | e ∈ A.compl.edgeSet} := by
  ext e
  simp [RootedLocation.M, oneLocation]

variable {f : S ≃ₜ S} {P P' : ColouredPainting χ}

omit [T2Space S] in
theorem restrict_image_V (I : IsColouredImage f P P') (A : Set S) :
    (P'.Γ.restrict (f '' A)).vertexSet = f '' (P.Γ.restrict A).vertexSet := by
  change P'.Γ.V ∩ f '' A = f '' (P.Γ.V ∩ A)
  rw [I.V, image_inter f.injective]

omit [T2Space S] in
theorem restrict_image_E (I : IsColouredImage f P P') (A : Set S) :
    (P'.Γ.restrict (f '' A)).edgeSet = (fun e ↦ f '' e) '' (P.Γ.restrict A).edgeSet := by
  ext e
  constructor
  · rintro ⟨he, hs, ht⟩
    rw [I.E_eq] at he
    obtain ⟨c, hc, rfl⟩ := he
    refine ⟨c, ⟨hc, (image_subset_image_iff f.injective).1 hs, ?_⟩, rfl⟩
    rintro x ⟨hx, hxV⟩
    obtain ⟨y, hy, hyx⟩ := ht ⟨tilde_image_homeo f c ▸ mem_image_of_mem _ hx, I.V ▸
      mem_image_of_mem _ hxV⟩
    exact f.injective hyx ▸ hy
  · rintro ⟨c, ⟨hc, hs, ht⟩, rfl⟩
    refine ⟨I.E_eq ▸ mem_image_of_mem _ hc, image_mono hs, ?_⟩
    rintro x ⟨hx, hxV⟩
    rw [tilde_image_homeo] at hx
    rw [I.V] at hxV
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, hzy⟩ := hxV
    obtain rfl := f.injective hzy
    exact mem_image_of_mem _ (ht ⟨hy, hz⟩)

omit [T2Space S] in
/-- A separation by two sets moves along a homeomorphism. -/
theorem sep_image (I : IsColouredImage f P P') {A B : Set S}
    (h : P.Γ.toHypergraph.IsSeparation (P.Γ.restrict A) (P.Γ.restrict B)) :
    P'.Γ.toHypergraph.IsSeparation (P'.Γ.restrict (f '' A)) (P'.Γ.restrict (f '' B)) := by
  rw [isSeparation_iff_of_le (P'.Γ.restrict_le _) (P'.Γ.restrict_le _)]
  rw [isSeparation_iff_of_le (P.Γ.restrict_le _) (P.Γ.restrict_le _)] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [restrict_image_V I, restrict_image_V I, ← image_union, h₁]
    exact I.V.symm
  · rw [restrict_image_E I, restrict_image_E I, ← image_union, h₂]
    exact I.E_eq.symm
  · rw [restrict_image_E I, restrict_image_E I, ← image_inter f.injective.image_injective, h₃,
      image_empty]

omit [T2Space Shat] in
omit [T2Space S] in
/-- The cut form moves to the cap twisted by a homeomorphism. -/
theorem IsCutFormOf.ofHomeo {K K' : Drawing S} {F : Set Shat}
  (hf : IsCutFormOf cap K' F)
    (f : S ≃ₜ S) (hU : f '' K.U = K'.U) : IsCutFormOf (cap.ofHomeo f) K F := by
  have hemb : (cap.ofHomeo f).emb '' K.U = cap.emb '' K'.U := by
    rw [← hU, image_image]
    rfl
  have hbd : ∀ {x}, x ∈ bd S → f x ∈ bd S := fun hx ↦ image_bd f ▸ mem_image_of_mem _ hx
  have hbd' : ∀ {x}, f x ∈ bd S → x ∈ bd S := fun {x} hx ↦ by
    have := image_bd f.symm ▸ mem_image_of_mem f.symm hx
    rwa [f.symm_apply_apply] at this
  have hmem : ∀ {x}, x ∈ K.U ↔ f x ∈ K'.U := fun {x} ↦ by
    rw [← hU]
    exact ⟨mem_image_of_mem _, fun ⟨y, hy, hyx⟩ ↦ f.injective hyx ▸ hy⟩
  obtain ⟨rfl, hO, hs⟩ | ⟨s, t, Θ, hΘ, hst, hsΘ, htΘ, hbdK, hl, h₁, h₂⟩ := hf
  · refine Or.inl ⟨hemb.symm, isOArc_comap f.isClosedEmbedding (hU ▸ hO), fun x hx y hy ↦ ?_⟩
    exact f.injective (hs ⟨hmem.1 hx.1, hbd hx.2⟩ ⟨hmem.1 hy.1, hbd hy.2⟩)
  · refine Or.inr ⟨f.symm s, f.symm t, f.symm '' Θ, ?_, fun h ↦ hst (f.symm.injective h),
      mem_image_of_mem _ hsΘ,
      mem_image_of_mem _ htΘ, ?_, ?_, hemb ▸ h₁, ?_⟩
    · rw [cuffs_eq_image f.symm]
      exact mem_image_of_mem _ hΘ
    · ext x
      constructor
      · rintro ⟨hx, hxb⟩
        have : f x ∈ K'.U ∩ bd S := ⟨hmem.1 hx, hbd hxb⟩
        rw [hbdK] at this
        rcases this with h | h
        · exact Or.inl (by rw [← h, f.symm_apply_apply])
        · exact Or.inr (by rw [← h, f.symm_apply_apply]; rfl)
      · have key : ∀ {z}, z ∈ K'.U ∩ bd S → f.symm z ∈ K.U ∩ bd S := fun {z} hz ↦
          ⟨hmem.2 (by rw [f.apply_symm_apply]; exact hz.1), hbd' (by rw [f.apply_symm_apply]; exact
            hz.2)⟩
        rintro (rfl | rfl)
        · exact key (hbdK ▸ mem_insert _ _)
        · exact key (hbdK ▸ mem_insert_of_mem _ rfl)
    · refine isLine_comap f.isClosedEmbedding ?_
      rw [hU, f.apply_symm_apply, f.apply_symm_apply]
      exact hl
    · rw [hemb]
      change _ ⊆ cap.cuffDisc (f '' (f.symm '' Θ))
      simpa [image_image] using h₂

omit [T2Space Shat] in
omit [T2Space S] in
/-- A point of `F` in `Σ` lies in `K`. -/
theorem IsCutFormOf.mem_U {K : Drawing S} {F : Set Shat} (hf : IsCutFormOf cap K F) {x : S}
  (hx : cap.emb x ∈ F) :
    x ∈ K.U := by
  obtain ⟨rfl, -, -⟩ | ⟨s, t, Θ, hΘ, -, -, -, -, -, -, hd⟩ := hf
  · obtain ⟨y, hy, hyx⟩ := hx
    exact cap.isEmbedding.injective hyx ▸ hy
  · by_contra hn
    refine cap.notMem_range hΘ (hd ⟨hx, ?_⟩) (mem_range_self x)
    rintro ⟨y, hy, hyx⟩
    exact hn (cap.isEmbedding.injective hyx ▸ hy)

omit [T2Space S] [T2Space Shat] in
/-- A sphere is simpler than a closed surface that is not a sphere. -/
theorem simpler_of_sphere {T : Type} [TopologicalSpace T] (cap : IsCappedSurface S Shat)
  (hns : ¬ IsSphere Shat)
    (h : Nonempty (T ≃ₜ SurfaceModel 0 0 0)) : IsSimplerThan T Shat := by
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification Shat cap.isSurface cap.connected
  have hc : c = 0 := by
    have h₁ := numCuffs_eq e
    rw [numCuffs_model] at h₁
    rw [← h₁, numCuffs, cuffs, cap.bd_empty, componentsIn, image_empty, ncard_empty]
  subst hc
  have hab : 1 ≤ 2 * a + b := by
    by_contra hn
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    obtain ⟨g⟩ := isSphere_model
    exact hns ⟨e.trans g⟩
  exact ⟨0, 0, 0, a, b, 0, h, ⟨e⟩, by omega, by omega, by omega⟩

end GraphMinor.GM19
