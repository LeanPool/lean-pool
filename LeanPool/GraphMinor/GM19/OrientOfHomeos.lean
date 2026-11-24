/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PlaneOrientation
public import LeanPool.GraphMinor.GM19.FragmentOrient
public import LeanPool.GraphMinor.GM19.FragmentCapping
public import LeanPool.GraphMinor.Surface.DiscMatch
public import LeanPool.GraphMinor.Surface.RemoveDiscs

/-!
# An orientation from the homeomorphisms of a surface

Let `T` be a closed connected surface, with a family of disjoint closed discs and one more disc `A₀`
off them. We show that if no
homeomorphism fixing the family reverses `A₀`, then `T` is orientable (`orientable_of_no_reversal`).
So on a surface that is not
orientable some homeomorphism fixing the family reverses `A₀`. This proves the sentence in step (2)
of the proof of Graph Minors XIX, (15.2), page 382:
"Since $\Sigma_\chi$ is connected, there is, for each internal $e \in E(\Gamma_0)$ with $|\tilde{e}|
= 3$, a $\Phi_\chi$-preserving homeomorphism $\alpha_e \colon \Sigma_\chi \to \Sigma_\chi$ which
maps $\beta(e)$ onto itself with reversed orientation, and fixes $bd(\Sigma)$ and every $\beta(f)$
($f \in E(\Gamma_0)\setminus \{e\}$) pointwise."

The direction of a disc `Δ` off the family is read from `A₀` through any homeomorphism fixing the
family and sending `A₀` to `Δ`. No choice
matters, since no homeomorphism reverses `A₀`. Nested discs agree: a disc `F` around them lies in a
chart, so it is oriented by
`planeOrientation`, a homeomorphism supported inside `F` keeps this orientation by `sameOn_const`,
and the discs are images of one
small disc under such homeomorphisms.

This orients the surface made by removing the open discs, and the closed surface `T` caps it. So
`isOrientable_of_inside` orients `T`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology Filter GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
/-- A closed disc has an orientation on its subdiscs, from a chart. -/
theorem exists_local_orientation {F : Set T} (hF : IsClosedDisc F) : ∃ pos : Set T → T → T → T
  → Prop, IsPartialOrientation {Δ | Δ ⊆ F} pos := by
  obtain ⟨h, g, c⟩ := hF.exists_isChart
  refine ⟨pullPos h planeOrientation.pos, (planeOrientation.isPartial univ).pull fun Δ hΔ
    => ⟨c.hc.mono hΔ, ?_, mem_univ _⟩⟩
  exact (c.gh.injOn).mono hΔ

omit [T2Space T] in
theorem isPreconnected_discInt {F : Set T} (hF : IsClosedDisc F) : IsPreconnected (discInt F) := by
  obtain ⟨h, g, c⟩ := hF.exists_isChart
  rw [c.discInt_eq]
  exact (convex_ball (0 : ℂ) 1).isPreconnected.image g (c.gc.mono ball_subset_closedBall)

/-- A homeomorphism supported inside a disc keeps an orientation of that disc. -/
theorem sameOn_of_support (hT : IsClosedSurface T) {F F₁ : Set T} (hF : IsClosedDisc F)
  (hF₁ : IsClosedDisc F₁) (hsub : F₁ ⊆ discInt F) {pos : Set T → T → T → T → Prop}
    (hpos : IsPartialOrientation {Δ | Δ ⊆ discInt F} pos) (e : T ≃ₜ T) (he : ∀ x, x ∉ F₁ → e x
      = x) {D : Set T} (hD : IsClosedDisc D) (hDF : D ⊆ discInt F) :
    SameOn (pullPos e pos) pos D := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hin : ∀ {x}, x ∈ F₁ → e x ∈ F₁ := fun {x} hx => by
    by_contra hn
    have h1 := he _ hn
    have h2 := e.injective h1
    exact hn (by rw [h2]; exact hx)
  have hmaps : MapsTo e (discInt F) (discInt F) := fun x hx => by
    by_cases h : x ∈ F₁
    · exact hsub (hin h)
    · rw [he x h]; exact hx
  have hP' : IsPartialOrientation {Δ | Δ ⊆ discInt F} (pullPos e pos) :=
    hpos.pull fun Δ hΔ => ⟨e.continuous.continuousOn, e.injective.injOn, by
      rintro _ ⟨x, hx, rfl⟩
      exact hmaps (hΔ hx)⟩
  have hO : IsOpen (discInt F) := hF.isOpen_discInt hman
  have hopen : IsOpen (discInt F \ F₁) := hO.sdiff hF₁.isClosed
  obtain ⟨h, g, c⟩ := hF.exists_isChart
  have hne : (discInt F \ F₁).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hn
    have h1 : F ⊆ F₁ := by
      have := closure_mono hn
      rw [hF₁.isClosed.closure_eq] at this
      exact hF.subset_closure_discInt.trans this
    obtain ⟨y, hy⟩ := (IsOArc.isConnected' hF.isOArc_discBd).nonempty
    exact (hsub (h1 (discBd_subset _ hy))).2 hy
  obtain ⟨y, hy⟩ := hne
  obtain ⟨E, hE, -, hEs⟩ := exists_small_disc (hT.2.2 y) hopen hy
  have hEsame : SameOn (pullPos e pos) pos E := by
    intro a b c ha hb hc _ _ _
    have hfix : ∀ {x}, x ∈ E → e x = x := fun hx => he _ (hEs hx).2
    have himg : e '' E = E := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hfix hz]; exact hz
      · exact fun hx => ⟨x, hx, hfix hx⟩
    change pos (e '' E) (e a) (e b) (e c) ↔ _
    rw [himg, hfix (discBd_subset _ ha), hfix (discBd_subset _ hb), hfix (discBd_subset _ hc)]
  exact (sameOn_const hman hO (isPreconnected_discInt hF) (fun x _ => hT.2.2 x) hP' hpos hE hD
    (hEs.trans sdiff_subset) hDF).1 hEsame

section Capping

variable [ConnectedSpace T] {ι : Type} [Finite ι] {P : ι → Set T}

/-- A closed surface caps the surface made by removing disjoint open discs. -/
theorem nonempty_capped_of_removal (hT : IsClosedSurface T) (hP : ∀ i, IsClosedDisc (P i))
  (hd : Pairwise fun i j => Disjoint (P i) (P j)) :
    Nonempty (IsCappedSurface ↥(⋃ i, discInt (P i))ᶜ T) := by
  classical
  have hS : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  obtain ⟨hc, hW, hbd, hconn, hcuffs⟩ := remove_discs hS hT.2.2 hP hd
  have hclo : ∀ i, closure (discInt (P i)) = P i := fun i =>
    Subset.antisymm (closure_minimal (discInt_subset _) (hP i).isClosed)
      (hP i).subset_closure_discInt
  have hbW : ∀ i, discBd (P i) ⊆ (⋃ i, discInt (P i))ᶜ := fun i x hx hu => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hij : i = j
    · subst hij
      exact hj.2 hx
    · exact Set.disjoint_left.mp (hd hij) (discBd_subset _ hx) hj.1
  have hinj : ∀ {i j}, (Subtype.val ⁻¹' discBd (P i) : Set ↥(⋃ i, discInt (P i))ᶜ)
    = Subtype.val ⁻¹' discBd (P j) → i = j := by
    intro i j he
    by_contra hij
    obtain ⟨y, hy⟩ := (IsOArc.isConnected' (hP i).isOArc_discBd).nonempty
    have h1 : (⟨y, hbW i hy⟩ : ↥(⋃ i, discInt (P i))ᶜ) ∈ (Subtype.val ⁻¹' discBd
      (P j) : Set ↥(⋃ i, discInt (P i))ᶜ) := by
      rw [← he]; exact hy
    exact Set.disjoint_left.mp (hd hij) (discBd_subset _ hy) (discBd_subset _ h1)
  let cd : Set ↥(⋃ i, discInt (P i))ᶜ → Set T := fun Θ => {x | ∃ i, Θ = Subtype.val ⁻¹' discBd
    (P i) ∧ x ∈ discInt (P i)}
  have hcd : ∀ i, cd (Subtype.val ⁻¹' discBd (P i)) = discInt (P i) := fun i => by
    ext x
    constructor
    · rintro ⟨j, he, hx⟩
      rw [hinj he]; exact hx
    · exact fun hx => ⟨i, rfl, hx⟩
  refine ⟨⟨hS, inferInstance, ?_, Subtype.val, IsEmbedding.subtypeVal, cd, ?_, ?_, ?_, ?_⟩⟩
  · ext x
    simp only [mem_empty_iff_false, iff_false]
    exact hT.2.2 x |> fun h hb => hb h
  · rintro Θ hΘ
    rw [hcuffs] at hΘ
    obtain ⟨i, rfl⟩ := hΘ
    show IsClosedDisc (closure (cd _))
    rw [hcd, hclo]
    exact hP i
  · rintro Θ hΘ
    rw [hcuffs] at hΘ
    obtain ⟨i, rfl⟩ := hΘ
    show discBd (closure (cd _)) = _
    rw [hcd, hclo, Subtype.image_preimage_coe, inter_eq_right.mpr (hbW i)]
  · rintro Θ₁ hΘ₁ Θ₂ hΘ₂ hne
    rw [hcuffs] at hΘ₁ hΘ₂
    obtain ⟨i, rfl⟩ := hΘ₁
    obtain ⟨j, rfl⟩ := hΘ₂
    rw [hcd, hcd, hclo, hclo]
    exact hd fun h => hne (by rw [h])
  · rw [Subtype.range_coe, compl_compl]
    ext x
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hx⟩
      refine ⟨_, ?_, (show x ∈ cd _ by rw [hcd]; exact hx)⟩
      rw [hcuffs]
      exact ⟨i, rfl⟩
    · rintro ⟨Θ, hΘ, hx⟩
      rw [hcuffs] at hΘ
      obtain ⟨i, rfl⟩ := hΘ
      rw [hcd] at hx
      exact ⟨i, hx⟩

/-- An orientation of the part of `T` off disjoint closed discs orients `T`. -/
theorem orientable_of_off_discs (hT : IsClosedSurface T) (hP : ∀ i, IsClosedDisc (P i))
  (hd : Pairwise fun i j => Disjoint (P i) (P j)) {pos : Set T → T → T → T → Prop}
    (hpos : IsPartialOrientation {Δ | Δ ⊆ (⋃ i, P i)ᶜ} pos) : IsOrientableSurface T := by
  classical
  have hS : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  obtain ⟨hc, hW, hbd, hconn, hcuffs⟩ := remove_discs hS hT.2.2 hP hd
  obtain ⟨cap⟩ := nonempty_capped_of_removal hT hP hd
  have : Nonempty ↥(⋃ i, discInt (P i))ᶜ := hconn.toNonempty
  obtain ⟨e, X, hX, hs, ht, -⟩ := exists_cap_chart hW cap
  refine isOrientable_of_inside hT hX e hs ht (pos := pullPos Subtype.val pos) (hpos.pull fun Δ hΔ
    => ⟨continuous_subtype_val.continuousOn, Subtype.val_injective.injOn, ?_⟩)
  rintro _ ⟨x, hx, rfl⟩ hu
  obtain ⟨i, hi⟩ := mem_iUnion.mp hu
  by_cases hb : x.1 ∈ discBd (P i)
  · apply hΔ hx
    rw [hbd]
    exact mem_iUnion.mpr ⟨i, hb⟩
  · exact x.2 (mem_iUnion.mpr ⟨i, hi, hb⟩)

end Capping

section Reading

variable {ι : Type} [Finite ι]

/-- The cyclic order on `bd(Δ)` read from the parametrization `p` of `bd(A₀)` through a
homeomorphism that fixes the family `P`. -/
def homeoPos (P : ι → Set T) (A₀ : Set T) (p : Circle → T) (Δ : Set T) (a b c : T) : Prop :=
  ∃ e : T ≃ₜ T, (∀ i, ∀ z ∈ P i, e z = z) ∧ e '' A₀ = Δ ∧ ∃ u v w, e (p u) = a ∧ e (p v) = b ∧ e
    (p w) = c ∧ CircleCyclic u v w

omit [T2Space T] [Finite ι] in
theorem homeoPos.map {P : ι → Set T} {A₀ : Set T} {p : Circle → T} {Δ : Set T} {a b c : T}
  (h : homeoPos P A₀ p Δ a b c) (f : T ≃ₜ T) (hf : ∀ i, ∀ z ∈ P i, f z = z) :
    homeoPos P A₀ p (f '' Δ) (f a) (f b) (f c) := by
  obtain ⟨e, he, rfl, u, v, w, rfl, rfl, rfl, hc⟩ := h
  refine ⟨e.trans f, fun i z hz => ?_, ?_, u, v, w, rfl, rfl, rfl, hc⟩
  · change f (e z) = z
    rw [he i z hz, hf i z hz]
  · exact (image_image f e A₀).symm ▸ rfl

omit [T2Space T] [Finite ι] in
theorem homeoPos_map_iff {P : ι → Set T} {A₀ : Set T} {p : Circle → T} {Δ : Set T} {a b c : T}
  (f : T ≃ₜ T) (hf : ∀ i, ∀ z ∈ P i, f z = z) :
    homeoPos P A₀ p (f '' Δ) (f a) (f b) (f c) ↔ homeoPos P A₀ p Δ a b c := by
  refine ⟨fun h => ?_, fun h => h.map f hf⟩
  have := h.map f.symm fun i z hz => by
    rw [Homeomorph.symm_apply_eq, hf i z hz]
  simpa [image_image] using this

/-- **No reversal gives an orientation.** Let `A₀` be a closed disc off the disjoint closed discs `P
i`, and let `p` parametrize its boundary.
If each homeomorphism that fixes every `P i` pointwise and maps `A₀` onto itself keeps the cyclic
order of `p`, then `T` is orientable. -/
theorem orientable_of_no_reversal [ConnectedSpace T] (hT : IsClosedSurface T) {P : ι → Set T}
  (hP : ∀ i, IsClosedDisc (P i)) (hd : Pairwise fun i j => Disjoint (P i) (P j)) {A₀ : Set T}
    (hA : IsClosedDisc A₀) (hAP : Disjoint A₀ (⋃ i, P i)) {p : Circle → T} (hpc : Continuous p)
      (hpi : Function.Injective p) (hpr : range p = discBd A₀)
    (hno : ∀ α : T ≃ₜ T, (∀ i, ∀ z ∈ P i, α z = z) → α '' A₀ = A₀ → ∀ u v w u' v' w', α (p u)
      = p u' → α (p v) = p v' → α (p w) = p w' → CircleCyclic u v w → CircleCyclic u' v' w') :
    IsOrientableSurface T := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hBc : IsClosed (⋃ i, P i) := isClosed_iUnion_of_finite fun i => (hP i).isClosed
  have hbdimg : ∀ (f : T ≃ₜ T) {D : Set T}, IsClosedDisc D → IsClosedDisc (f '' D) ∧ discBd
    (f '' D) = f '' discBd D := fun f D hD =>
    hD.image f.continuous.continuousOn f.symm.continuous.continuousOn fun _ _
      => f.symm_apply_apply _
  have hdisj : ∀ {Δ : Set T}, Δ ⊆ (⋃ i, P i)ᶜ → Disjoint Δ (⋃ i, P i) := fun h
    => Set.disjoint_left.mpr fun x hx hu => h hx hu
  have hdir : ∀ Δ ∈ {Δ | Δ ⊆ (⋃ i, P i)ᶜ}, IsClosedDisc Δ → IsDirectionOf (discBd Δ)
    (homeoPos P A₀ p Δ) := by
    intro Δ hs hΔ
    obtain ⟨e, he, hfix⟩ := exists_disc_match hT P hP hd hA hΔ hAP (hdisj hs)
    refine ⟨fun w => e (p w), e.continuous.comp hpc, fun a b h => hpi (e.injective h), ?_,
      fun a b c _ _ _ => ⟨?_, fun h => ⟨e, hfix, he, a, b, c, rfl, rfl, rfl, h⟩⟩⟩
    · have : (fun w => e (p w)) = e ∘ p := rfl
      rw [this, range_comp, hpr, ← (hbdimg e hA).2, he]
    · rintro ⟨e', he', himg, u, v, w, hu, hv, hw, hc⟩
      refine hno (e'.trans e.symm) (fun i z hz => ?_) ?_ u v w a b c ?_ ?_ ?_ hc
      · change e.symm (e' z) = z
        rw [he' i z hz, Homeomorph.symm_apply_eq, hfix i z hz]
      · change (fun x => e.symm (e' x)) '' A₀ = A₀
        rw [← image_image (g := e.symm) (f := e'), himg, ← he, image_image]
        simp
      · change e.symm (e' (p u)) = _
        rw [hu, Homeomorph.symm_apply_apply]
      · change e.symm (e' (p v)) = _
        rw [hv, Homeomorph.symm_apply_apply]
      · change e.symm (e' (p w)) = _
        rw [hw, Homeomorph.symm_apply_apply]
  refine orientable_of_off_discs hT hP hd (pos := homeoPos P A₀ p) ⟨hdir, ?_⟩
  intro Δ₁ h₁ Δ₂ h₂ hd₁ hd₂ hsub a b c ha hb hc hab hbc hac
  obtain ⟨F₁, hF₁, hsF₁, hdF₁⟩ := GM12.exists_disc_enlargement_avoiding hT hd₂ hBc (hdisj h₂)
  obtain ⟨F, hF, hsF, hdF⟩ := GM12.exists_disc_enlargement_avoiding hT hF₁ hBc hdF₁
  obtain ⟨pos, hpos⟩ := exists_local_orientation hF
  have hpos' : IsPartialOrientation {Δ | Δ ⊆ discInt F} pos := hpos.mono fun Δ hs => hs.trans
    (discInt_subset F)
  obtain ⟨D, hD, hDin⟩ := exists_inner_disc hd₁
  have hint : discInt Δ₁ ⊆ discInt Δ₂ := discInt_mono hman hd₁ hsub
  have hDF : D ⊆ discInt F := fun x hx => hsF (hsF₁ (hsub (discInt_subset _ (hDin hx)))).1
  have hin₂ : Δ₂ ⊆ discInt F := fun x hx => hsF (hsF₁ hx).1
  have hin₁ : Δ₁ ⊆ discInt F := hsub.trans hin₂
  have hF₁F : F₁ ⊆ discInt F := hsF
  have key : ∀ {Δ : Set T}, IsClosedDisc Δ → Δ ⊆ F₁ \ discBd F₁ → D ⊆ Δ \ discBd Δ → Δ ⊆ discInt F
    → (SameOn (homeoPos P A₀ p) pos D ↔ SameOn (homeoPos P A₀ p) pos Δ) := by
    intro Δ hΔ hΔF hDΔ hΔI
    obtain ⟨e, he, hfix⟩ := exists_disc_onto_nested hman hD hΔ hF₁ hDΔ hΔF
    have heP : ∀ i, ∀ z ∈ P i, e z = z := fun i z hz => hfix z fun hzF
      => Set.disjoint_left.mp hdF₁ hzF (mem_iUnion.mpr ⟨i, hz⟩)
    have hs := sameOn_of_support hT hF hF₁ hF₁F hpos' e hfix hD hDF
    have hbd : discBd Δ = e '' discBd D := by rw [← he]; exact (hbdimg e hD).2
    constructor
    · intro hS x y z hx hy hz hxy hyz hxz
      rw [hbd] at hx hy hz
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨z, hz, rfl⟩ := hz
      have hxy' : x ≠ y := fun h => hxy (by rw [h])
      have hyz' : y ≠ z := fun h => hyz (by rw [h])
      have hxz' : x ≠ z := fun h => hxz (by rw [h])
      rw [← he, homeoPos_map_iff e heP, hS x y z hx hy hz hxy' hyz' hxz']
      exact (hs x y z hx hy hz hxy' hyz'
        hxz').symm
    · intro hS x y z hx hy hz hxy hyz hxz
      have hmem : ∀ {w}, w ∈ discBd D → e w ∈ discBd Δ := by
        intro w hw
        rw [hbd]
        exact mem_image_of_mem e hw
      rw [← homeoPos_map_iff (Δ := D) e heP, he, hS _ _ _ (hmem hx) (hmem hy) (hmem hz) (fun h
        => hxy (e.injective h)) (fun h => hyz (e.injective h)) (fun h => hxz (e.injective h)), ← he]
      exact hs x y z hx hy hz hxy hyz hxz
  have hk₁ := key hd₁ (hsub.trans hsF₁) hDin hin₁
  have hk₂ := key hd₂ hsF₁ (hDin.trans hint) hin₂
  by_cases hs : SameOn (homeoPos P A₀ p) pos D
  · exact (hk₁.1 hs a b c ha.1 hb.1 hc.1 hab hbc hac).trans ((hpos'.agree Δ₁ hin₁ Δ₂ hin₂ hd₁ hd₂
    hsub a b c ha hb hc hab hbc hac).trans
      (hk₂.1 hs a b c ha.2 hb.2 hc.2 hab hbc hac).symm)
  · have hs₁ := sameOn_of_notSame (hdir Δ₁ h₁ hd₁) (hpos'.dir Δ₁ hin₁ hd₁) (mt hk₁.2 hs)
    have hs₂ := sameOn_of_notSame (hdir Δ₂ h₂ hd₂) (hpos'.dir Δ₂ hin₂ hd₂) (mt hk₂.2 hs)
    exact (hs₁ a b c ha.1 hb.1 hc.1 hab hbc hac).trans ((hpos'.rev.agree Δ₁ hin₁ Δ₂ hin₂ hd₁ hd₂
      hsub a b c ha hb hc hab hbc hac).trans
      (hs₂ a b c ha.2 hb.2 hc.2 hab hbc hac).symm)

end Reading

end GraphMinor.GM19
