/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PadFlower

/-!
# Discs through prescribed ends

This is the frame of steps (2) and (3) of the proof of Graph Minors XIX, (15.2), pages 381 and 382,
on a closed connected surface, without any painting. We are given disjoint closed discs `Δ i`, a
finite set
`V`, and pads `C i` that meet only in `V`, with `V` on the boundary of each pad. Each `Δ i` has a
finite set `Y i` of ends on its boundary, and each end has a vertex in `V`, on the boundary of `C
i`.

The model is made of small discs `E v` around the vertices and a flower `M i` in each pad, by
`exists_pad_flower`. Step (2) is `exists_marked_match`: a homeomorphism `α` carries `M i` to `Δ i`
and the peaks
to the ends. Step (3) pulls the model back: the discs `α '' E v` meet `⋃ Δ i` in exactly the ends
(`exists_realizing_discs`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology Filter GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

theorem planePos_iff {Δ : Set ℂ} (hΔ : IsClosedDisc Δ) {φ : Circle → ℂ} (hφ : IsPosParam Δ φ)
  (a b c : Circle) : planePos Δ (φ a) (φ b) (φ c) ↔ CircleCyclic a b c :=
  ⟨fun ⟨_φ', _, _, _, hφ', ha, hb, hc, hcy⟩ => order_of_nested hΔ hΔ subset_rfl hφ' hφ hcy ha hb hc,
    fun h => ⟨φ, a, b, c, hφ, rfl, rfl, rfl, h⟩⟩

theorem circleCyclic_preserves {τ : Circle ≃ₜ Circle} (hτ : PreservesCircleOrientation τ)
  (a b c : Circle) : CircleCyclic (τ a) (τ b) (τ c) ↔ CircleCyclic a b c := by
  constructor
  · intro h
    obtain ⟨l, hl, hm, he⟩ := preserves_symm hτ
    have := circleCyclic_map_mono hl hm he h
    simpa using this
  · obtain ⟨l, hl, hm, he⟩ := hτ
    exact circleCyclic_map_mono hl hm he

/-- `exists_marked_match` for any finite index type. -/
theorem exists_marked_match' [ConnectedSpace T] (hT : IsClosedSurface T) {ι : Type} [Finite ι] {A
  A' : ι → Set T} (hA : ∀ i, IsClosedDisc (A i)) (hA' : ∀ i, IsClosedDisc (A' i))
    (hAA : Pairwise fun i j => Disjoint (A i) (A j)) (hAA' : Pairwise fun i j => Disjoint (A' i)
      (A' j)) {p p' : ι → Circle → T} (hp : ∀ i, IsBdParam (A i) (p i)) (hp' : ∀ i, IsBdParam
        (A' i) (p' i))
    (H : ¬ IsOrientableSurface T ∨ ∃ ω : SurfaceOrientation T, ∀ i a b c, a ≠ b → b ≠ c → a ≠ c →
      (ω.pos (A i) (p i a) (p i b) (p i c) ↔ ω.pos (A' i) (p' i a) (p' i b) (p' i c))) :
    ∃ e : T ≃ₜ T, (∀ i, e '' A i = A' i) ∧ ∀ i w, e (p i w) = p' i w := by
  obtain ⟨n, ⟨f⟩⟩ := Finite.exists_equiv_fin ι
  have hinj : ∀ {i j : Fin n}, i ≠ j → f.symm i ≠ f.symm j := fun h he => h (f.symm.injective he)
  obtain ⟨e, h1, h2⟩ := exists_marked_match hT (A := fun i => A (f.symm i)) (A' := fun i => A'
    (f.symm i)) (p := fun i => p (f.symm i)) (p' := fun i => p' (f.symm i)) (fun i => hA _) (fun i
      => hA' _)
    (fun i j h => hAA (hinj h)) (fun i j h => hAA' (hinj h)) (fun i => hp _) (fun i => hp' _)
      (H.imp id fun ⟨ω, hω⟩ => ⟨ω, fun i => hω _⟩)
  refine ⟨e, fun i => ?_, fun i w => ?_⟩
  · simpa using h1 (f i)
  · simpa using h2 (f i) w

private theorem prescribed_points_respect_the_orientation
    {T : Type}
    [TopologicalSpace T]
    {ι : Type}
    {Δ : ι → Set T}
    {C : ι → Set T}
    {c : ι → T → ℂ}
    {g : ι → ℂ → T}
    (hch : ∀ (i : ι), IsChart (C i) (c i) (g i))
    {q : ι → Circle → T}
    (H : ¬IsOrientableSurface T ∨ ∃ ω : SurfaceOrientation T, ∀ (i : ι), ∃ ϖ : Set T → T → T → T
      → Prop, (ϖ = ω.pos ∨ ϖ = revPos ω.pos) ∧ (∀ (D :
      Set T), IsClosedDisc D → D ⊆ C i → SameOn ϖ (pullPos (c i) planePos) D) ∧ ∀ (a b d :
      Circle), a ≠ b → b ≠ d → a ≠ d → (ϖ (Δ i) (q i a) (q i b) (q i d) ↔ CircleCyclic a b d))
    (ρ : ι → Circle → ℝ)
    (τ : ι → Circle ≃ₜ Circle)
    (hτ : ∀ (i : ι), PreservesCircleOrientation (τ i))
    (St : ι → Set ℂ)
    (hStC : ∀ (i : ι), St i ⊆ closedBall 0 1)
    (hStd : ∀ (i : ι), IsClosedDisc (St i))
    (hSp : ∀ (i : ι), IsPosParam (St i) fun w => (ρ i w : ℂ) * w)
    (M : ι → Set T)
    (hM : ∀ i, M i = g i '' St i)
    (hMd : ∀ (i : ι), IsClosedDisc (M i))
    (p : ι → Circle → T)
    (hpg : ∀ i w, p i w = g i ((ρ i w : ℂ) * w))
    (hpS : ∀ (i : ι) (w : Circle), (ρ i w : ℂ) * w ∈ St i)
    (hpM : ∀ (i : ι), IsBdParam (M i) (p i))
    (hMC : ∀ (i : ι), M i ⊆ discInt (C i))
    (p' : ι → Circle → T)
    (hp'q : ∀ i w, p' i w = q i (τ i w)) :
    ¬IsOrientableSurface T ∨ ∃ ω : SurfaceOrientation T, ∀ (i : ι) (a b d : Circle), a ≠ b → b ≠ d
      → a ≠ d → (ω.pos (M i)
      (p i a) (p i b) (p i d) ↔ ω.pos (Δ i) (p' i a) (p' i b) (p' i d)) := by
  refine H.imp id fun ⟨ω, hω⟩ => ⟨ω, fun i => ?_⟩
  obtain ⟨ϖ, hϖ, h1, h2⟩ := hω i
  have key : ∀ a b d, a ≠ b → b ≠ d → a ≠ d → (ϖ (M i) (p i a) (p i b) (p i d) ↔ ϖ (Δ i) (p' i a)
    (p' i b) (p' i d)) := fun a b d hab hbd had => by
    have hmem : ∀ w, p i w ∈ discBd (M i) := fun w => by rw [← (hpM i).2.2]; exact mem_range_self w
    have hsub : M i ⊆ C i := fun x hx => discInt_subset _ (hMC i hx)
    have h3 := h1 (M i) (hMd i) hsub _ _ _ (hmem a) (hmem b) (hmem d) (fun h => hab
      ((hpM i).2.1 h)) (fun h => hbd ((hpM i).2.1 h)) (fun h => had ((hpM i).2.1 h))
    have hcM : c i '' M i = St i := by
      rw [hM i]
      ext z
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        rw [(hch i).hg (hStC i hx)]
        exact hx
      · exact fun hz => ⟨g i z, mem_image_of_mem _ hz, (hch i).hg (hStC i hz)⟩
    have hcp : ∀ w, c i (p i w) = (ρ i w : ℂ) * w := fun w =>
      (congrArg (c i) (hpg i w)).trans ((hch i).hg (hStC i (hpS i w)))
    have h4 : pullPos (c i) planePos (M i) (p i a) (p i b) (p i d) ↔ CircleCyclic a b d := by
      change planePos (c i '' M i) (c i (p i a)) (c i (p i b)) (c i (p i d)) ↔ _
      rw [hcM, hcp, hcp, hcp]
      exact planePos_iff (hStd i) (hSp i) a b d
    have hτne : ∀ {x y : Circle}, x ≠ y → τ i x ≠ τ i y := fun h he => h ((τ i).injective he)
    rw [h3, h4, ← circleCyclic_preserves (hτ i), hp'q, hp'q, hp'q]
    exact (h2 _ _ _ (hτne hab) (hτne hbd) (hτne had)).symm
  rcases hϖ with rfl | rfl
  · exact key
  · exact fun a b d hab hbd had => key a d b had hbd.symm hab

/-- **Discs through prescribed ends.** See the top of this file. In the orientable case an
orientation `ω`, or its reverse `ϖ i`, must agree with the chart on the pad `C i` and with the
parametrization `q i` on `Δ i`. -/
theorem exists_realizing_discs [ConnectedSpace T] (hT : IsClosedSurface T) {ι : Type} [Finite ι] {Δ
  C : ι → Set T} {c : ι → T → ℂ} {g : ι → ℂ → T} (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hΔΔ : Pairwise fun i j => Disjoint (Δ i) (Δ j)) (hC : ∀ i, IsClosedDisc (C i))
      (hch : ∀ i, IsChart (C i) (c i) (g i)) {V : Set T} (hV : V.Finite) (hCC : ∀ i j, i ≠ j
        → C i ∩ C j ⊆ V)
    (hVC : ∀ i, V ∩ C i ⊆ discBd (C i)) {Y : ι → Set T} {φ : ι → T → T} {q : ι → Circle
      → T} {A U : ι → T → ℝ} (hφ : ∀ i, ∀ y ∈ Y i, φ i y ∈ V ∩ C i) (hq : ∀ i, IsBdParam (Δ i)
        (q i))
    (hO : ∀ i, PadOrder (q i) (g i) (Y i) (φ i) (A i) (U i))
    (H : ¬ IsOrientableSurface T ∨ ∃ ω : SurfaceOrientation T, ∀ i, ∃ ϖ : Set T → T → T → T → Prop,
      (ϖ = ω.pos ∨ ϖ = revPos ω.pos) ∧ (∀ D, IsClosedDisc D → D ⊆ C i → SameOn ϖ (pullPos
        (c i) planePos) D) ∧
      ∀ a b d, a ≠ b → b ≠ d → a ≠ d → (ϖ (Δ i) (q i a) (q i b) (q i d) ↔ CircleCyclic a b d)) :
    ∃ D : T → Set T, (∀ v ∈ V, IsClosedDisc (D v)) ∧ (∀ v ∈ V, ∀ v' ∈ V, v ≠ v' → Disjoint (D v)
      (D v')) ∧ ∀ v ∈ V, D v ∩ ⋃ i, Δ i = ⋃ i, {y ∈ Y i | φ i y = v} := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hci : ∀ i, InjOn (c i) (C i) := fun i x hx y hy h => by rw [← (hch i).gh hx, ←
    (hch i).gh hy, h]
  have hgi : ∀ i, InjOn (g i) (closedBall 0 1) := fun i x hx y hy h => by rw [← (hch i).hg hx, ←
    (hch i).hg hy, h]
  have hunit : ∀ i, ∀ v ∈ V ∩ C i, ‖c i v‖ = 1 := fun i v hv => by
    have : c i v ∈ sphere (0 : ℂ) 1 := by
      rw [← (hch i).bd]
      exact mem_image_of_mem _ (hVC i hv)
    simpa using this
  obtain ⟨s, hs0, hs1, hsep⟩ : ∃ s : ℝ, 0 < s ∧ s < 1 / 4 ∧ ∀ i, ∀ v ∈ V ∩ C i, ∀ v' ∈ V ∩ C i, v ≠
    v' → 4 * s ≤ ‖c i v - c i v'‖ := by
    have : Finite V := hV.to_subtype
    have e : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ i, ∀ v : V, ∀ v' : V, v.1 ∈ C i → v'.1 ∈ C i → v ≠ v' → 4 * s
      ≤ ‖c i v.1 - c i v'.1‖ := by
      refine eventually_all.mpr fun i => eventually_all.mpr fun v => eventually_all.mpr fun v' => ?_
      by_cases h : v.1 ∈ C i ∧ v'.1 ∈ C i ∧ v ≠ v'
      · obtain ⟨h1, h2, h3⟩ := h
        have hp : 0 < ‖c i v.1 - c i v'.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun he => h3
          (Subtype.ext (hci i h1 h2 he)))
        have hc : Continuous fun s : ℝ => 4 * s := by fun_prop
        have h0 : (fun s : ℝ => 4 * s) 0 < ‖c i v.1 - c i v'.1‖ := by simpa using hp
        have := (hc.tendsto 0).eventually (gt_mem_nhds h0)
        exact (this.filter_mono nhdsWithin_le_nhds).mono fun s hs _ _ _ => hs.le
      · exact Eventually.of_forall fun s h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
    obtain ⟨s, h1, h2⟩ := (e.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
    exact ⟨s, h2.1, h2.2, fun i v hv v' hv' hne => h1 i ⟨v, hv.1⟩ ⟨v',
      hv'.1⟩ hv.2 hv'.2 fun h => hne (congrArg Subtype.val h)⟩
  obtain ⟨W, hW, hWd⟩ := hV.t2_separation
  have hdisc : ∀ v, ∃ E : Set T, IsClosedDisc E ∧ v ∈ discInt E ∧ E ⊆ W v ∧ ∀ x ∈ E, ∀ i, x ∈ C i
    → v ∈ C i ∧ ‖c i x - c i v‖ < s := by
    intro v
    have hev : ∀ᶠ x in 𝓝 v, ∀ i, x ∈ C i → v ∈ C i ∧ ‖c i x - c i v‖ < s := by
      refine eventually_all.mpr fun i => ?_
      by_cases hv : v ∈ C i
      · have h1 := (hch i).hc v hv
        have h2 := (Metric.tendsto_nhds.mp h1 s hs0)
        refine (eventually_nhdsWithin_iff.mp h2).mono fun x hx hxC => ⟨hv, ?_⟩
        have := hx hxC
        rwa [dist_eq_norm] at this
      · exact Filter.mem_of_superset ((hC i).isClosed.isOpen_compl.mem_nhds hv) fun x hx hxC
        => absurd hxC hx
    obtain ⟨E, hE, hvE, hEs⟩ := exists_small_disc (hT.2.2 v) (isOpen_interior.inter
      (hW v).2) ⟨mem_interior_iff_mem_nhds.mpr hev, (hW v).1⟩
    exact ⟨E, hE, hvE, fun x hx => (hEs hx).2, fun x hx => interior_subset (hEs hx).1⟩
  choose E hE hvE hEW hEC using hdisc
  have hEd : ∀ v ∈ V, ∀ v' ∈ V, v ≠ v' → Disjoint (E v) (E v') := fun v hv v' hv' hne =>
    (hWd hv hv' hne).mono (hEW v) (hEW v')
  let X : Set T := ⋃ v ∈ V, E v
  have hXc : IsClosed X := hV.isClosed_biUnion fun v _ => (hE v).isClosed
  have hmemX : ∀ {x}, x ∈ X → ∃ v ∈ V, x ∈ E v := fun {x} hx => by simpa [X] using hx
  have hfar : ∀ i, ∀ x ∈ C i ∩ X, 1 / 2 < ‖c i x‖ := fun i x hx => by
    obtain ⟨v, hv, hxv⟩ := hmemX hx.2
    obtain ⟨h1, h2⟩ := hEC v x hxv i hx.1
    have h3 := hunit i v ⟨hv, h1⟩
    have h4 := norm_sub_norm_le (c i v) (c i x)
    rw [norm_sub_rev, h3] at h4
    linarith
  have hnear : ∀ i, ∀ y ∈ Y i, ∀ᶠ z in 𝓝 (ee (U i y) : ℂ), z ∈ closedBall (0 : ℂ) 1 → g i z ∈ X
    := fun i y hy => by
    have hb : (ee (U i y) : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
    have h1 := (hch i).gc _ hb
    obtain ⟨hv, -⟩ := hφ i y hy
    rw [ContinuousWithinAt, (hO i).g_U y hy] at h1
    have h2 := h1.eventually (((hE (φ i y)).isOpen_discInt hman).mem_nhds (hvE (φ i y)))
    refine (eventually_nhdsWithin_iff.mp h2).mono fun z hz hzb => ?_
    exact mem_biUnion hv (discInt_subset _ (hz hzb))
  have hpad := fun i => exists_pad_flower (hC i).isCompact (hch i) (hO i) hXc (hfar i) (hnear i) hs0
  choose ρ hρc hρ u hu1 hu2 hu3 τ hτ hτq using hpad
  have hρp : ∀ i x, 0 < ρ i x := fun i x => (hρ i x).1
  let St : ι → Set ℂ := fun i => starDisc (hρc i) (hρp i)
  have hStB : ∀ i, St i ⊆ ball 0 1 := fun i => starDisc_subset_ball fun x => (hρ i x).2
  have hStC : ∀ i, St i ⊆ closedBall 0 1 := fun i => (hStB i).trans ball_subset_closedBall
  have hStd : ∀ i, IsClosedDisc (St i) := fun i => isClosedDisc_starDisc _ _
  have hSp : ∀ i, IsPosParam (St i) fun w => (ρ i w : ℂ) * w := fun i => isPosParam_star _ _
  let M : ι → Set T := fun i => g i '' St i
  have hMim := fun i => isClosedDisc_image_injOn (hStd i) ((hch i).gc.mono (hStC i)) ((hgi i).mono
    (hStC i))
  have hMd : ∀ i, IsClosedDisc (M i) := fun i => (hMim i).1
  let p : ι → Circle → T := fun i w => g i ((ρ i w : ℂ) * w)
  have hpS : ∀ i w, (ρ i w : ℂ) * w ∈ St i := fun i w => by
    apply discBd_subset _
    rw [← (hSp i).2.2.1]
    exact mem_range_self w
  have hpM : ∀ i, IsBdParam (M i) (p i) := fun i => by
    refine ⟨(hch i).gc.comp_continuous (hSp i).1 fun w => hStC i (hpS i w),
      fun a b h => (hSp i).2.1 (hgi i (hStC i (hpS i a)) (hStC i (hpS i b)) h), ?_⟩
    have : p i = g i ∘ fun w => (ρ i w : ℂ) * w := rfl
    rw [this, range_comp, (hSp i).2.2.1, (hMim i).2]
  have hMC : ∀ i, M i ⊆ discInt (C i) := fun i => by
    rw [(hch i).discInt_eq]
    exact image_mono (hStB i)
  have hMM : Pairwise fun i j => Disjoint (M i) (M j) := fun i j hij => by
    refine Set.disjoint_left.mpr fun x hi hj => ?_
    have hxi := hMC i hi
    have hxj := hMC j hj
    have hxV := hCC i j hij ⟨discInt_subset _ hxi, discInt_subset _ hxj⟩
    exact hxi.2 (hVC i ⟨hxV, discInt_subset _ hxi⟩)
  let p' : ι → Circle → T := fun i w => q i (τ i w)
  have hp' : ∀ i, IsBdParam (Δ i) (p' i) := fun i => by
    refine ⟨(hq i).1.comp (τ i).continuous, fun a b h => (τ i).injective ((hq i).2.1 h), ?_⟩
    have : p' i = q i ∘ τ i := rfl
    rw [this, range_comp, (τ i).range_coe, image_univ, (hq i).2.2]
  have hH : ¬ IsOrientableSurface T ∨ ∃ ω : SurfaceOrientation T, ∀ i a b d, a ≠ b → b ≠ d → a ≠ d
    → (ω.pos (M i) (p i a) (p i b) (p i d) ↔ ω.pos (Δ i) (p' i a) (p' i b) (p' i d)) := by
    exact prescribed_points_respect_the_orientation (T := T) (ι := ι) (Δ := Δ) (C := C) (c := c)
      (g := g) hch (q := q) H ρ τ hτ St hStC hStd hSp M (fun _ => rfl) hMd p (fun _ _ => rfl)
      hpS hpM hMC p' (fun _ _ => rfl)
  obtain ⟨α, hα, hαw⟩ := exists_marked_match' hT hMd hΔ hMM hΔΔ hpM hp' hH
  have hαY : ∀ i (y : {y // y ∈ Y i}), α (p i (u i y)) = y.1 := fun i y => by
    rw [hαw]
    exact hτq i y
  have hclaim : ∀ i (y : {y // y ∈ Y i}), ∀ v ∈ V, p i (u i y) ∈ E v → v = φ i y.1
    := fun i y v hv hx => by
    have hxC : p i (u i y) ∈ C i := (hch i).gm (hStC i (hpS i _))
    obtain ⟨h1, h2⟩ := hEC v _ hx i hxC
    have hcp : c i (p i (u i y)) = (ρ i (u i y) : ℂ) * u i y := (hch i).hg (hStC i (hpS i _))
    rw [hcp] at h2
    by_contra hne
    have hyV := hφ i y.1 y.2
    have h3 := hsep i v ⟨hv, h1⟩ _ hyV hne
    have hcy : c i (φ i y.1) = ee (U i y.1) := by
      rw [← (hO i).g_U y.1 y.2]
      exact (hch i).hg (by simp)
    rw [hcy] at h3
    have h4 := hu1 i y
    have hr := hρ i (u i y)
    have hnv := hunit i v ⟨hv, h1⟩
    have hn1 : ‖(ρ i (u i y) : ℂ) * u i y‖ = ρ i (u i y) := by
      rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.1.le]
    have h5 : 1 - ρ i (u i y) < s := by
      have := norm_sub_norm_le (c i v) ((ρ i (u i y) : ℂ) * u i y)
      rw [hnv, hn1, norm_sub_rev] at this
      linarith
    have h6 : ‖(u i y : ℂ) - (ρ i (u i y) : ℂ) * u i y‖ = 1 - ρ i (u i y) := by
      have : (u i y : ℂ) - (ρ i (u i y) : ℂ) * u i y = ((1 - ρ i (u i y) : ℝ) : ℂ) * u i y := by
        push_cast
        ring
      rw [this, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
        Real.norm_of_nonneg (by linarith [hr.2])]
    have h7 : c i v - ee (U i y.1) = ((u i y : ℂ) - ee (U i y.1)) - ((u i y : ℂ) - (ρ i
      (u i y) : ℂ) * u i y) - ((ρ i (u i y) : ℂ) * u i y - c i v) := by ring
    rw [h7] at h3
    have h8 := norm_sub_le (((u i y : ℂ) - ee (U i y.1)) - ((u i y : ℂ) - (ρ i
      (u i y) : ℂ) * u i y)) ((ρ i (u i y) : ℂ) * u i y - c i v)
    have h9 := norm_sub_le ((u i y : ℂ) - ee (U i y.1)) ((u i y : ℂ) - (ρ i (u i y) : ℂ) * u i y)
    linarith
  refine ⟨fun v => α '' E v, fun v _ => (image_disc α (hE v)).1, fun v hv v' hv' hne =>
    (Set.disjoint_image_iff α.injective).mpr (hEd v hv v' hv' hne), fun v hv => ?_⟩
  ext x
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, i, hi⟩
    rw [← hα i] at hi
    obtain ⟨z', hz', hzz⟩ := hi
    obtain rfl := α.injective hzz
    obtain ⟨w, hw, rfl⟩ := hz'
    have hw' : w ∈ closedBall (0 : ℂ) 1 := hStC i hw
    have hgC : g i w ∈ C i := (hch i).gm hw'
    have hmF : w ∈ c i '' (C i ∩ X) := ⟨g i w, ⟨hgC, mem_biUnion hv hz⟩, (hch i).hg hw'⟩
    have hw0 : w ≠ 0 := fun h => by
      have := hfar i (g i w) ⟨hgC, mem_biUnion hv hz⟩
      rw [(hch i).hg hw', h, norm_zero] at this
      linarith
    obtain ⟨y, hy⟩ := hu3 i w hw0 hmF ((mem_starDisc hw0).mp hw)
    have hgp : g i w = p i (u i y) := by rw [hy]
    refine ⟨i, ?_⟩
    rw [hgp, hαY i y]
    refine ⟨y.2, ?_⟩
    rw [hgp] at hz
    exact (hclaim i y v hv hz).symm
  · rintro ⟨i, hy, rfl⟩
    let y' : {y // y ∈ Y i} := ⟨x, hy⟩
    have hmem : p i (u i y') ∈ X := by
      obtain ⟨z, hz, hzc⟩ := hu2 i y'
      have hgz : z = p i (u i y') := by
        change z = g i _
        rw [← hzc, (hch i).gh hz.1]
      rw [← hgz]
      exact hz.2
    obtain ⟨v', hv', hxv⟩ := hmemX hmem
    have hvv := hclaim i y' v' hv' hxv
    refine ⟨⟨p i (u i y'), ?_, hαY i y'⟩, i, ?_⟩
    · rw [show φ i x = v' from hvv.symm]
      exact hxv
    · have h1 : p i (u i y') ∈ M i := by
        apply discBd_subset _
        rw [← (hpM i).2.2]
        exact mem_range_self _
      have h2 := hαY i y'
      have h3 : x = α (p i (u i y')) := h2.symm
      rw [h3, ← hα i]
      exact mem_image_of_mem _ h1

end GraphMinor.GM19
