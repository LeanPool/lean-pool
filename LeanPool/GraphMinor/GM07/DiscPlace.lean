/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.MoveOff
public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM12.Section4MarkedDiscMatch

/-!
# Placing discs

Tools for step 2 of (9.1), page 243. Finitely many disjoint closed discs off the boundary go onto
finitely many others, with two marked boundary
points of each going to two given ones, by a homeomorphism fixing the boundary
(`exists_disc_family_placement`). We cap all the cuffs and move one
disc at a time, keeping the caps and the discs already placed fixed. A line off the boundary is a
chord of a closed disc inside any open set
around it (`exists_chord_disc`). `GraphMinor/GM07/ArcPlace.lean` uses both to map lines onto lines.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- Finitely many disjoint discs off the boundary go to others, with two marked points on each
boundary, by a homeomorphism fixing the boundary. -/
theorem exists_disc_family_placement {S : Type u} [TopologicalSpace S]
  (hS : IsSurface S) [ConnectedSpace S] {ι : Type*} [Finite ι] (A B : ι → Set S)
    (hA : ∀ i, IsClosedDisc (A i)) (hB : ∀ i, IsClosedDisc (B i)) (hAA : Pairwise fun i j
      => Disjoint (A i) (A j))
    (hBB : Pairwise fun i j => Disjoint (B i) (B j)) (hAb : ∀ i, Disjoint (A i) (bd S))
      (hBb : ∀ i, Disjoint (B i) (bd S))
    (a b a' b' : ι → S) (ha : ∀ i, a i ∈ discBd (A i)) (hb : ∀ i, b i ∈ discBd (A i))
      (hab : ∀ i, a i ≠ b i)
    (ha' : ∀ i, a' i ∈ discBd (B i)) (hb' : ∀ i, b' i ∈ discBd (B i)) (hab' : ∀ i, a' i ≠ b' i) :
    ∃ e : S ≃ₜ S, (∀ x ∈ bd S, e x = x) ∧ ∀ i, e '' A i = B i ∧ e (a i) = a' i ∧ e (b i) = b' i
      := by
  classical
  have ht2 : T2Space S := hS.2.1
  obtain ⟨T, tT, j, K, hT, hj, hK, hun, hint, hconn, 𝓓, hfD, hUD, hdD, hdisjD⟩
    := exists_capAll_discs S hS
  have : ConnectedSpace T := hconn inferInstance
  have ht2T : T2Space T := hT.2.1
  have hjinj := hj.injective
  have hjc := hj.continuous
  -- The images in the capped surface.
  have hdisc : ∀ {D : Set S}, IsClosedDisc D → IsClosedDisc (j '' D) ∧ discBd (j '' D)
    = j '' discBd D := fun hD =>
    isClosedDisc_image_of_injOn hD hjc hjinj.injOn
  have hoffK : ∀ {D : Set S}, Disjoint D (bd S) → Disjoint (j '' D) K := fun {D} hD => by
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hK'
    have h1 : j x ∈ range j ∩ K := ⟨mem_range_self _, hK'⟩
    rw [hint] at h1
    obtain ⟨y, hy, he⟩ := h1
    rw [hjinj he] at hy
    exact disjoint_left.mp hD hx hy
  have hdisjimg : ∀ {D D' : Set S}, Disjoint D D' → Disjoint (j '' D) (j '' D') := fun h =>
    (disjoint_image_iff hjinj).mpr h
  have key : ∀ F : Set ι, F.Finite → ∃ e : T ≃ₜ T, (∀ z ∈ K, e z = z) ∧ ∀ i ∈ F, e '' (j '' A i)
    = j '' B i ∧ e (j (a i)) = j (a' i) ∧ e (j (b i)) = j (b' i) := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty => exact ⟨Homeomorph.refl T, fun _ _ => rfl, by simp⟩
    | @insert i F hi hF ih =>
      obtain ⟨e, hefix, he⟩ := ih
      -- The discs to protect: the caps, and the discs placed so far.
      let D : 𝓓 ⊕ F → Set T := Sum.elim (fun d => d.1) fun l => j '' B l.1
      have hD : ∀ l, IsClosedDisc (D l) := fun l => by
        rcases l with d | l
        · exact (hdD d.1 d.2).1
        · exact (hdisc (hB l.1)).1
      have hKsub : ∀ d ∈ 𝓓, d ⊆ K := fun d hd => hUD ▸ subset_sUnion_of_mem hd
      have hDD : Pairwise fun l m => Disjoint (D l) (D m) := by
        rintro (d | l) (d' | m) hne
        · exact hdisjD d.1 d.2 d'.1 d'.2 fun h => hne (congrArg Sum.inl (Subtype.ext h))
        · exact ((hoffK (hBb m.1)).mono_right (hKsub d.1 d.2)).symm
        · exact (hoffK (hBb l.1)).mono_right (hKsub d'.1 d'.2)
        · exact hdisjimg (hBB fun h => hne (congrArg Sum.inr (Subtype.ext h)))
      have hei := isClosedDisc_image_of_injOn (hdisc (hA i)).1 e.continuous e.injective.injOn
      have hAD : Disjoint (e '' (j '' A i)) (⋃ l, D l) := by
        rw [disjoint_iUnion_right]
        rintro (d | l)
        · rw [disjoint_left]
          rintro _ ⟨x, hx, rfl⟩ hz
          have h1 : e x = x := by
            have h2 := hefix _ (hKsub d.1 d.2 hz)
            exact e.injective h2
          rw [h1] at hz
          exact disjoint_left.mp (hoffK (hAb i)) hx (hKsub d.1 d.2 hz)
        · change Disjoint _ (j '' B l.1)
          rw [← (he l.1 l.2).1]
          refine (disjoint_image_iff e.injective).mpr (hdisjimg (hAA ?_))
          rintro rfl
          exact hi l.2
      have hBD : Disjoint (j '' B i) (⋃ l, D l) := by
        rw [disjoint_iUnion_right]
        rintro (d | l)
        · exact (hoffK (hBb i)).mono_right (hKsub d.1 d.2)
        · refine hdisjimg (hBB ?_)
          rintro rfl
          exact hi l.2
      have hbdmem : ∀ {x : S}, x ∈ discBd (A i) → e (j x) ∈ discBd (e '' (j '' A i)) := fun {x} hx
        => by
        rw [hei.2, (hdisc (hA i)).2]
        exact ⟨j x, ⟨x, hx, rfl⟩, rfl⟩
      have hbdB : ∀ {x : S}, x ∈ discBd (B i) → j x ∈ discBd (j '' B i) := fun {x} hx => by
        rw [(hdisc (hB i)).2]
        exact ⟨x, hx, rfl⟩
      have : Finite 𝓓 := hfD
      have : Finite F := hF
      obtain ⟨g, hg1, hg2, hg3, hg4⟩ := GraphMinor.GM12.exists_marked_disc_match_fixing_discs hT D
        hD hDD hei.1 (hdisc (hB i)).1 hAD hBD
        (hbdmem (ha i)) (hbdmem (hb i)) (fun h => hab i (hjinj (e.injective h))) (hbdB (ha' i))
          (hbdB (hb' i)) fun h => hab' i (hjinj h)
      refine ⟨e.trans g, fun z hz => ?_, ?_⟩
      · rw [Homeomorph.trans_apply, hefix z hz]
        rw [← hUD] at hz
        obtain ⟨d, hd, hzd⟩ := hz
        exact hg4 (.inl ⟨d, hd⟩) z hzd
      · rintro l (rfl | hl)
        · refine ⟨?_, hg2, hg3⟩
          rw [← hg1]
          change (g ∘ e) '' _ = _
          rw [image_comp]
        · obtain ⟨h1, h2, h3⟩ := he l hl
          have hfixB : ∀ z ∈ j '' B l, g z = z := fun z hz => hg4 (.inr ⟨l, hl⟩) z hz
          have hmem : ∀ {x : S}, x ∈ B l → g (j x) = j x := fun {x} hx => hfixB _ ⟨x, hx, rfl⟩
          refine ⟨?_, ?_, ?_⟩
          · change (fun x => g (e x)) '' _ = _
            rw [show (fun x => g (e x)) = g ∘ e from rfl, image_comp, h1]
            exact (image_congr hfixB).trans (image_id' _)
          · rw [Homeomorph.trans_apply, h2, hmem (Surface.discBd_subset _ (ha' l))]
          · rw [Homeomorph.trans_apply, h3, hmem (Surface.discBd_subset _ (hb' l))]
  obtain ⟨e, hefix, he⟩ := key univ (toFinite _)
  -- Restrict to the surface.
  have hrange : ∀ (e₀ : T ≃ₜ T), (∀ z ∈ K, e₀ z = z) → ∀ x, e₀ (j x) ∈ range j := fun e₀ h0 x => by
    by_contra hn
    have h1 : e₀ (j x) ∈ K := (hun.ge (mem_univ _)).resolve_left hn
    have h2 := h0 _ h1
    have h3 : e₀ (j x) = j x := e₀.injective h2
    rw [h3] at hn
    exact hn (mem_range_self x)
  have hne : Nonempty S := inferInstance
  let J : T → S := invFun j
  have hJ : ∀ x, J (j x) = x := leftInverse_invFun hjinj
  have hjJ : ∀ y ∈ range j, j (J y) = y := fun y ⟨x, hx⟩ => by rw [← hx, hJ]
  have hefixs : ∀ z ∈ K, e.symm z = z := fun z hz => by
    rw [Homeomorph.symm_apply_eq, hefix z hz]
  have hdown : ∀ (e₀ : T ≃ₜ T), (∀ z ∈ K, e₀ z = z) → ∃ d : S → S, Continuous d ∧ ∀ x, j (d x) = e₀
    (j x) := fun e₀ h0 => by
    refine ⟨fun x => J (e₀ (j x)), ?_, fun x => hjJ _ (hrange e₀ h0 x)⟩
    rw [hj.isEmbedding.continuous_iff]
    have : j ∘ (fun x => J (e₀ (j x))) = e₀ ∘ j := funext fun x => hjJ _ (hrange e₀ h0 x)
    rw [this]
    exact e₀.continuous.comp hjc
  obtain ⟨d₁, hd₁, h₁⟩ := hdown e hefix
  obtain ⟨d₂, hd₂, h₂⟩ := hdown e.symm hefixs
  have hbdK : ∀ x ∈ bd S, j x ∈ K := fun x hx => by
    have : j x ∈ j '' bd S := ⟨x, hx, rfl⟩
    rw [← hint] at this
    exact this.2
  refine ⟨⟨⟨d₁, d₂, fun x => hjinj ?_, fun x => hjinj ?_⟩, hd₁, hd₂⟩, fun x hx => hjinj ?_,
    fun i => ?_⟩
  · rw [h₂, h₁, Homeomorph.symm_apply_apply]
  · rw [h₁, h₂, Homeomorph.apply_symm_apply]
  · exact (h₁ x).trans (hefix _ (hbdK x hx))
  · obtain ⟨h1, h2, h3⟩ := he i (mem_univ i)
    refine ⟨?_, hjinj ((h₁ _).trans h2), hjinj ((h₁ _).trans h3)⟩
    apply hjinj.image_injective
    change j '' (d₁ '' A i) = _
    rw [← h1, ← image_comp, ← image_comp]
    exact image_congr fun x _ => h₁ x

/-- A chart of a disc around a line off the boundary: the line is a segment of a diameter. -/
theorem exists_line_chart_aux {M : Type} [TopologicalSpace M] (hM : IsSurface M) {L : Set M} {u v :
  M} (hL : IsLineWithEnds L u v) (hd : L ∩ bd M = ∅)
    {W : Set M} (hW : IsOpen W) (hLW : L ⊆ W) :
    ∃ (K₀ : ℂ → M) (s : ℝ), 0 < s ∧ s < 1 ∧ ContinuousOn K₀ (closedBall 0 1) ∧ InjOn K₀
      (closedBall 0 1) ∧ K₀ '' closedBall 0 1 ⊆ W ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, K₀ z ∉ bd M) ∧ K₀ (-s : ℝ) = u ∧ K₀ (s : ℝ) = v
        ∧ ∀ x, x ∈ L ↔ ∃ z ∈ closedBall (0 : ℂ) 1, z.im = 0 ∧ |z.re| ≤ s ∧ K₀ z = x := by
  classical
  obtain ⟨T, tT, j, Kc, hT, hj, hKc, hun, hint, -⟩ := exists_capAll M hM
  have ht2 : T2Space T := hT.2.1
  have ht2M : T2Space M := hM.2.1
  have hcM : CompactSpace M := hM.1
  obtain ⟨a₀, ha₀, hr, ha0, ha1⟩ := hL.exists_arc
  have ha : IsArcMap (j ∘ a₀) := ⟨hj.continuous.comp ha₀.1, hj.injective.comp ha₀.2⟩
  have hWT : IsOpen (Kcᶜ ∩ (j '' Wᶜ)ᶜ) := hKc.isOpen_compl.inter (hj.isClosedMap _
    hW.isClosed_compl).isOpen_compl
  have haW : range (j ∘ a₀) ⊆ Kcᶜ ∩ (j '' Wᶜ)ᶜ := by
    rintro _ ⟨t, rfl⟩
    have htL : a₀ t ∈ L := hr ▸ mem_range_self t
    refine ⟨fun hc => ?_, ?_⟩
    · have h1 : j (a₀ t) ∈ range j ∩ Kc := ⟨mem_range_self _, hc⟩
      rw [hint] at h1
      obtain ⟨y, hy, he⟩ := h1
      have h3 : a₀ t ∈ L ∩ bd M := ⟨htL, hj.injective he ▸ hy⟩
      rw [hd] at h3
      exact h3
    · rintro ⟨y, hy, he⟩
      exact hy (hj.injective he ▸ hLW htL)
  obtain ⟨O, K, s, hK, hs0, hs1, hBO, hBW, hKm, hKp, hrange⟩ := exists_ball_chart hT ha hWT haW
  let B : Set ℂ := closedBall 0 1
  have hKr : ∀ z ∈ B, K z ∈ range j := fun z hz => by
    have h1 := hun.ge (mem_univ (K z))
    exact h1.resolve_right (hBW ⟨z, hz, rfl⟩).1
  have : Nonempty M := by
    obtain ⟨y, -⟩ := hKr 0 (by simp [B])
    exact ⟨y⟩
  let J : T → M := Function.invFun j
  have hJ : ∀ x, J (j x) = x := Function.leftInverse_invFun hj.injective
  have hjJ : ∀ y ∈ range j, j (J y) = y := fun y ⟨x, hx⟩ => by rw [← hx, hJ]
  let K₀ : ℂ → M := fun z => J (K z)
  have hjK : ∀ z ∈ B, j (K₀ z) = K z := fun z hz => hjJ _ (hKr z hz)
  have hK₀i : InjOn K₀ B := fun z hz w hw he => hK.hi (hBO hz) (hBO hw)
    (by rw [← hjK z hz, ← hjK w hw, he])
  have hK₀c : ContinuousOn K₀ B := by
    rw [hj.isEmbedding.continuousOn_iff]
    exact (hK.hc.mono hBO).congr fun z hz => hjK z hz
  have hsB : ∀ σ : ℝ, |σ| ≤ s → (σ : ℂ) ∈ B := fun σ hσ => by
    change _ ∈ closedBall (0 : ℂ) 1
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    linarith
  refine ⟨K₀, s, hs0, hs1, hK₀c, hK₀i, ?_, ?_, ?_, ?_, fun x => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    by_contra hn
    exact (hBW ⟨z, hz, rfl⟩).2 ⟨_, hn, hjK z hz⟩
  · intro z hz hb
    have h1 : j (K₀ z) ∈ range j ∩ Kc := hint ▸ mem_image_of_mem j hb
    rw [hjK z hz] at h1
    exact (hBW ⟨z, hz, rfl⟩).1 h1.2
  · apply hj.injective
    rw [hjK _ (hsB _ (by rw [abs_neg, abs_of_pos hs0]))]
    have : (((-s : ℝ) : ℂ)) = -(s : ℂ) := by push_cast; rfl
    simpa [ha0] using hKm
  · apply hj.injective
    rw [hjK _ (hsB _ (by rw [abs_of_pos hs0])), hKp]
    simp [ha1]
  · constructor
    · intro hx
      rw [← hr] at hx
      obtain ⟨t, rfl⟩ := hx
      obtain ⟨z, hz, h1, h2, h3⟩ := (hrange (j (a₀ t))).mp ⟨t, rfl⟩
      exact ⟨z, hz, h1, h2, hj.injective (by rw [hjK z hz, h3])⟩
    · rintro ⟨z, hz, h1, h2, rfl⟩
      obtain ⟨t, ht⟩ := (hrange (K z)).mpr ⟨z, hz, h1, h2, rfl⟩
      have : a₀ t = K₀ z := hj.injective (by rw [hjK z hz]; exact ht)
      rw [← this, ← hr]
      exact mem_range_self t

theorem isLineWithEnds_range_of_arc {X : Type*} [TopologicalSpace X] [T2Space X] {a : unitInterval
  → X} (ha : IsArcMap a) : IsLineWithEnds (range a) (a 0) (a 1) :=
  ⟨(ha.1.isClosedEmbedding ha.2).isEmbedding.toHomeomorph, rfl, rfl⟩

theorem exists_line_chart {S : Type u} [TopologicalSpace S] {M : Type} [TopologicalSpace M]
  (hM : IsSurface M) (h : S ≃ₜ M) {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) (hd : L ∩ bd S = ∅) {W : Set S} (hW : IsOpen W) (hLW : L ⊆ W) :
    ∃ (K₀ : ℂ → S) (s : ℝ), 0 < s ∧ s < 1 ∧ ContinuousOn K₀ (closedBall 0 1) ∧ InjOn K₀
      (closedBall 0 1) ∧ K₀ '' closedBall 0 1 ⊆ W ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, K₀ z ∉ bd S) ∧ K₀ (-s : ℝ) = u ∧ K₀ (s : ℝ) = v
        ∧ ∀ x, x ∈ L ↔ ∃ z ∈ closedBall (0 : ℂ) 1, z.im = 0 ∧ |z.re| ≤ s ∧ K₀ z = x := by
  have hbd : h '' bd S = bd M := image_bd_homeomorph h
  have hb : ∀ x, x ∈ bd S ↔ h x ∈ bd M := fun x => by
    rw [← hbd]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, he⟩ => h.injective he ▸ hy⟩
  have hL' : IsLineWithEnds (h '' L) (h u) (h v) := by
    obtain ⟨f, h0, h1⟩ := hL
    refine ⟨f.trans (h.image L), ?_, ?_⟩
    · change h (f 0).1 = h u
      rw [h0]
    · change h (f 1).1 = h v
      rw [h1]
  obtain ⟨K₀, s, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_line_chart_aux hM hL'
    (by rw [← hbd, ← image_inter h.injective, hd, image_empty])
    ((h.isOpenMap _ hW)) (image_mono hLW)
  have hinv : ∀ x, h (h.symm x) = x := h.apply_symm_apply
  refine ⟨h.symm ∘ K₀, s, h1, h2, h.symm.continuous.comp_continuousOn h3,
    h.symm.injective.comp_injOn h4, ?_, fun z hz hb' => h6 z hz ?_, ?_, ?_, fun x => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, he⟩ := h5 ⟨z, hz, rfl⟩
    change h.symm (K₀ z) ∈ W
    rw [← he, h.symm_apply_apply]
    exact hy
  · have := (hb _).mp hb'
    simpa [hinv] using this
  · change h.symm (K₀ ((-s : ℝ) : ℂ)) = u
    rw [h7, h.symm_apply_apply]
  · change h.symm (K₀ ((s : ℝ) : ℂ)) = v
    rw [h8, h.symm_apply_apply]
  · constructor
    · intro hx
      obtain ⟨z, hz, h10, h11, h12⟩ := (h9 (h x)).mp ⟨x, hx, rfl⟩
      exact ⟨z, hz, h10, h11, by simp [h12]⟩
    · rintro ⟨z, hz, h10, h11, rfl⟩
      obtain ⟨y, hy, he⟩ := (h9 (K₀ z)).mpr ⟨z, hz, h10, h11, rfl⟩
      change h.symm (K₀ z) ∈ L
      rw [← he, h.symm_apply_apply]
      exact hy

theorem isClosedDisc_of_chart {S : Type*} [TopologicalSpace S] [T2Space S] {K₀ : ℂ → S}
  (hc : ContinuousOn K₀ (closedBall 0 1)) (hi : InjOn K₀ (closedBall 0 1))
    {c : ℂ} {ε : ℝ} (hε : 0 < ε) (hsub : closedBall c ε ⊆ closedBall 0 1) :
    IsClosedDisc (K₀ '' closedBall c ε) ∧ discBd (K₀ '' closedBall c ε) = K₀ '' sphere c ε := by
  have hne : Nonempty ℂ := ⟨0⟩
  let K₁ : ℂ → S := fun z => K₀ (c + z)
  have hmap : ∀ z ∈ closedBall (0 : ℂ) ε, c + z ∈ closedBall c ε := fun z hz => by
    rw [mem_closedBall, dist_eq_norm]
    simpa using hz
  have hc₁ : ContinuousOn K₁ (closedBall 0 ε) := (hc.mono hsub).comp (by fun_prop) hmap
  have hi₁ : InjOn K₁ (closedBall 0 ε) := fun z hz w hw he => by
    simpa using hi (hsub (hmap z hz)) (hsub (hmap w hw)) he
  obtain ⟨hD, hDb⟩ := closedBall_disc hε
  obtain ⟨K', hK'c, hK'l⟩ := Surface.exists_inv_of_compactOn (isCompact_closedBall _ _) hc₁ hi₁
  obtain ⟨hE, hEb⟩ := hD.image hc₁ hK'c hK'l
  have h1 : K₁ '' closedBall 0 ε = K₀ '' closedBall c ε := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hmap z hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z - c, by simpa [dist_eq_norm] using hz, by simp [K₁]⟩
  have h2 : K₁ '' sphere 0 ε = K₀ '' sphere c ε := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨c + z, by simpa [dist_eq_norm] using hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z - c, by simpa [dist_eq_norm] using hz, by simp [K₁]⟩
  rw [hDb, h2] at hEb
  rw [h1] at hE hEb
  exact ⟨hE, hEb⟩

/-- A disc around a line off the boundary, inside a given open set, with the line as a chord. -/
theorem exists_chord_disc {S : Type u} [TopologicalSpace S] [T2Space S] {M : Type}
  [TopologicalSpace M] (hM : IsSurface M) (h : S ≃ₜ M) {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) (hd : L ∩ bd S = ∅) {W : Set S} (hW : IsOpen W) (hLW : L ⊆ W) :
    ∃ B, IsClosedDisc B ∧ L ⊆ B ∧ B ⊆ W ∧ Disjoint B (bd S) ∧ u ∈ discBd B ∧ v ∈ discBd B
      ∧ L ∩ discBd B = {u, v} := by
  obtain ⟨K₀, s, hs0, hs1, hc, hi, h1, h2, h3, h4, h5⟩ := exists_line_chart hM h hL hd hW hLW
  have hsub : closedBall (0 : ℂ) s ⊆ closedBall 0 1 := closedBall_subset_closedBall hs1.le
  obtain ⟨hB, hBb⟩ := isClosedDisc_of_chart hc hi hs0 hsub
  have hsph : ∀ σ : ℝ, |σ| = s → (σ : ℂ) ∈ sphere (0 : ℂ) s := fun σ hσ => by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, hσ]
  refine ⟨K₀ '' closedBall 0 s, hB, fun x hx => ?_, (image_mono hsub).trans h1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, him, hre, rfl⟩ := (h5 x).mp hx
    refine ⟨z, ?_, rfl⟩
    have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [mem_closedBall_zero_iff, this, Complex.norm_real, Real.norm_eq_abs]
    simpa using hre
  · rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩
    exact h2 z (hsub hz)
  · rw [hBb, ← h3]
    exact ⟨_, by simp [abs_of_pos hs0], rfl⟩
  · rw [hBb, ← h4]
    exact ⟨_, by simp [abs_of_pos hs0], rfl⟩
  · rw [hBb]
    apply Subset.antisymm
    · rintro x ⟨hxL, w, hw, rfl⟩
      obtain ⟨z, hz, him, hre, he⟩ := (h5 _).mp hxL
      have hw1 : w ∈ closedBall (0 : ℂ) 1 := hsub (sphere_subset_closedBall hw)
      have hzw : z = w := hi hz hw1 he
      subst hzw
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
      have hn : |z.re| = s := by
        rw [mem_sphere_zero_iff_norm, hzr, Complex.norm_real, Real.norm_eq_abs] at hw
        simpa using hw
      rcases abs_eq hs0.le |>.mp hn with h6 | h6
      · right
        rw [mem_singleton_iff, ← h4, hzr, h6]
      · left
        rw [← h3, hzr, h6]
    · have hu : u ∈ L := (h5 u).mpr
        ⟨_, hsub (sphere_subset_closedBall (hsph (-s) (by simp [abs_of_pos hs0]))),
          by simp, by simp [abs_of_pos hs0], h3⟩
      have hv : v ∈ L := (h5 v).mpr
        ⟨_, hsub (sphere_subset_closedBall (hsph s (by simp [abs_of_pos hs0]))),
          by simp, by simp [abs_of_pos hs0], h4⟩
      rintro x (rfl | hx)
      · exact ⟨hu, _, hsph (-s) (by simp [abs_of_pos hs0]), h3⟩
      · rw [mem_singleton_iff] at hx
        subst hx
        exact ⟨hv, _, hsph s (by simp [abs_of_pos hs0]), h4⟩

end GraphMinor.GM07
