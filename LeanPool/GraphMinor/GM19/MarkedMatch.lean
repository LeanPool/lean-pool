/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.OrientOfHomeos
public import LeanPool.GraphMinor.GM19.FeatureOrient

/-!
# Matching marked discs

We prove the homeomorphism of step (2) of the proof of Graph Minors XIX, (15.2), page 381. On a
closed connected surface, let two families of
disjoint closed discs be given, each disc with a parametrized boundary. There is a homeomorphism
that carries each disc to its partner and
each parametrization to its partner, if the surface is not orientable, or if some orientation agrees
with the parametrizations on each pair
of discs (`exists_marked_match`).

A homeomorphism `e` matching one disc induces a map `τ` of the circle. If `τ` keeps the direction of
the circle, then a twist in a collar
finishes (`exists_boundary_twist`). If it reverses the direction, then there are two cases. A
homeomorphism that fixes a disc keeps each
orientation, so this does not happen when the parametrizations agree with an orientation. On a
surface that is not orientable,
`orientable_of_no_reversal` gives a homeomorphism that fixes the matched discs and reverses this
one.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology Filter GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- `p` parametrizes the boundary of `D`. -/
def IsBdParam (D : Set T) (p : Circle → T) : Prop :=
  Continuous p ∧ Function.Injective p ∧ range p = discBd D

theorem IsBdParam.exists_homeo {D : Set T} {p : Circle → T} (h : IsBdParam D p) : ∃ ψ : Circle ≃ₜ
  discBd D, ∀ w, (ψ w).1 = p w := by
  obtain ⟨hc, hi, hr⟩ := h
  let f : Circle → discBd D := fun w => ⟨p w, by rw [← hr]; exact mem_range_self w⟩
  have hfb : Function.Bijective f := ⟨fun a b h => hi (congrArg Subtype.val h), fun x => by
    obtain ⟨w, hw⟩ : x.1 ∈ range p := by rw [hr]; exact x.2
    exact ⟨w, Subtype.ext hw⟩⟩
  have hfc : Continuous f := hc.subtype_mk _
  exact ⟨hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hfb), fun w => rfl⟩

omit [T2Space T] in
theorem image_disc (e : T ≃ₜ T) {D : Set T} (hD : IsClosedDisc D) : IsClosedDisc (e '' D) ∧ discBd
  (e '' D) = e '' discBd D :=
  hD.image e.continuous.continuousOn e.symm.continuous.continuousOn fun _ _ => e.symm_apply_apply _

omit [T2Space T] in
theorem IsBdParam.image {D : Set T} {p : Circle → T} (h : IsBdParam D p) (e : T ≃ₜ T)
  (hD : IsClosedDisc D) : IsBdParam (e '' D) fun w => e (p w) := by
  refine ⟨e.continuous.comp h.1, fun a b he => h.2.1 (e.injective he), ?_⟩
  have : (fun w => e (p w)) = e ∘ p := rfl
  rw [this, range_comp, h.2.2, (image_disc e hD).2]

/-- A homeomorphism carrying `D` onto `D'` induces a map of the circle between parametrizations. -/
theorem exists_circle_transfer {D D' : Set T} {p p' : Circle → T} (hp : IsBdParam D p)
  (hp' : IsBdParam D' p') (e : T ≃ₜ T) (hD : IsClosedDisc D) (he : e '' D = D') :
    ∃ τ : Circle ≃ₜ Circle, ∀ w, p' (τ w) = e (p w) := by
  obtain ⟨ψ', hψ'⟩ := hp'.exists_homeo
  have hbd : discBd D' = e '' discBd D := by rw [← he]; exact (image_disc e hD).2
  have hmem : ∀ w, e (p w) ∈ discBd D' := fun w => by
    rw [hbd, ← hp.2.2]
    exact mem_image_of_mem e (mem_range_self w)
  let f : Circle → Circle := fun w => ψ'.symm ⟨e (p w), hmem w⟩
  have hspec : ∀ w, p' (f w) = e (p w) := fun w => by
    rw [← hψ', Homeomorph.apply_symm_apply]
  have hfc : Continuous f := ψ'.symm.continuous.comp ((e.continuous.comp hp.1).subtype_mk _)
  have hfi : Function.Injective f := fun a b h => hp.2.1 (e.injective (by rw [← hspec, ← hspec, h]))
  have hfs : Function.Surjective f := fun x => by
    have h1 : p' x ∈ discBd D' := by rw [← hp'.2.2]; exact mem_range_self x
    rw [hbd, ← hp.2.2] at h1
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := h1
    exact ⟨w, hp'.2.1 (by rw [hspec, hw])⟩
  exact ⟨hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩), hspec⟩

omit [T2Space T] in
/-- A closed disc has three distinct boundary points. -/
theorem exists_three_bd {D : Set T} {p : Circle → T} (hp : IsBdParam D p) : ∃ a ∈ discBd D, ∃ b ∈
  discBd D, ∃ c ∈ discBd D, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  have hm : ∀ w, p w ∈ discBd D := fun w => by rw [← hp.2.2]; exact mem_range_self w
  have hpi := Real.pi_gt_three
  have h1 : Circle.exp 0 ≠ Circle.exp 1 := circle_exp_ne (by norm_num) (by rw [abs_lt]; constructor
    <;> linarith)
  have h2 : Circle.exp 1 ≠ Circle.exp 2 := circle_exp_ne (by norm_num) (by rw [abs_lt]; constructor
    <;> linarith)
  have h3 : Circle.exp 0 ≠ Circle.exp 2 := circle_exp_ne (by norm_num) (by rw [abs_lt]; constructor
    <;> linarith)
  exact ⟨_, hm _, _, hm _, _, hm _, fun h => h1 (hp.2.1 h), fun h => h2 (hp.2.1 h),
    fun h => h3 (hp.2.1 h)⟩

omit [T2Space T] in
/-- A homeomorphism that fixes a closed disc keeps each orientation. -/
theorem preserved_of_fix (hT : IsClosedSurface T) [ConnectedSpace T] (ω : SurfaceOrientation T)
  (e : T ≃ₜ T) {Q : Set T} (hQ : IsClosedDisc Q) (hfix : ∀ z ∈ Q, e z = z) : ω.IsPreservedBy e := by
  have hS : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  rcases homeo_orientation hS e with h | h
  · exact h ω
  exfalso
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac⟩ : ∃ a ∈ discBd Q, ∃ b ∈ discBd Q, ∃ c ∈ discBd Q, a ≠
    b ∧ b ≠ c ∧ a ≠ c := by
    obtain ⟨ψ⟩ := hQ.isOArc_discBd
    exact exists_three_bd (p := fun w => (ψ w).1) ⟨continuous_subtype_val.comp ψ.continuous,
      fun a b h => ψ.injective (Subtype.ext h), by
      ext y
      exact ⟨fun ⟨w, hw⟩ => hw ▸ (ψ w).2, fun hy => ⟨ψ.symm ⟨y, hy⟩, by simp⟩⟩⟩
  have himg : e '' Q = Q := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hfix z hz]; exact hz
    · exact fun hx => ⟨x, hx, hfix x hx⟩
  have := h ω Q hQ a b c ha hb hc hab hbc hac
  rw [himg, hfix a (discBd_subset _ ha), hfix b (discBd_subset _ hb),
    hfix c (discBd_subset _ hc)] at this
  exact iff_not_self this

/-- A strictly increasing angle finishes the match of one disc: a twist in a collar corrects the
boundary. -/
theorem finish_match (hT : IsClosedSurface T) {ι : Type} [Finite ι] {P : ι → Set T}
  (hP : ∀ i, IsClosedDisc (P i)) {A' : Set T} (hA' : IsClosedDisc A')
    (hAP' : Disjoint A' (⋃ i, P i)) {p' : Circle → T} (hp' : IsBdParam A' p') {τ : Circle ≃ₜ
      Circle} (hτ : PreservesCircleOrientation τ) :
    ∃ e : T ≃ₜ T, e '' A' = A' ∧ (∀ i, ∀ z ∈ P i, e z = z) ∧ ∀ w, e (p' (τ w)) = p' w := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hBc : IsClosed (⋃ i, P i) := isClosed_iUnion_of_finite fun i => (hP i).isClosed
  obtain ⟨E, hE, hsub, hEP⟩ := GM12.exists_disc_enlargement_avoiding hT hA' hBc hAP'
  obtain ⟨ψ, hψ⟩ := hp'.exists_homeo
  obtain ⟨e, he, htw, hfix⟩ := exists_boundary_twist hman hA' hE hsub ψ (preserves_symm hτ)
  refine ⟨e, he, fun i z hz => hfix z fun hzE => Set.disjoint_left.mp hEP hzE (mem_iUnion.mpr ⟨i,
    hz⟩), fun w => ?_⟩
  have := htw (τ w)
  rw [hψ, hψ, Homeomorph.symm_apply_apply] at this
  exact this

/-- **One marked disc.** A homeomorphism fixing the protected discs carries `(A, p)` to `(A', p')`,
if the surface is not orientable, or if an
orientation agrees with `p` and `p'`. -/
theorem exists_param_match [ConnectedSpace T] (hT : IsClosedSurface T) {ι : Type} [Finite ι] {P : ι
  → Set T} (hP : ∀ i, IsClosedDisc (P i)) (hPP : Pairwise fun i j => Disjoint (P i) (P j))
    {A A' : Set T} (hA : IsClosedDisc A) (hA' : IsClosedDisc A') (hAP : Disjoint A (⋃ i, P i))
      (hAP' : Disjoint A' (⋃ i, P i)) {p p' : Circle → T} (hp : IsBdParam A p)
        (hp' : IsBdParam A' p')
    (H : ¬ IsOrientableSurface T ∨ ∃ (_ : ι) (ω : SurfaceOrientation T), ∀ a b c, a ≠ b → b ≠ c
      → a ≠ c → (ω.pos A (p a) (p b) (p c) ↔ ω.pos A' (p' a) (p' b) (p' c))) :
    ∃ e : T ≃ₜ T, e '' A = A' ∧ (∀ i, ∀ z ∈ P i, e z = z) ∧ ∀ w, e (p w) = p' w := by
  obtain ⟨e₀, he₀, hfix₀⟩ := exists_disc_match hT P hP hPP hA hA' hAP hAP'
  obtain ⟨τ, hτ⟩ := exists_circle_transfer hp hp' e₀ hA he₀
  have done : ∀ (e₁ : T ≃ₜ T) (τ₁ : Circle ≃ₜ Circle), (∀ i, ∀ z ∈ P i, e₁ z = z) → e₁ '' A = A' →
    (∀ w, p' (τ₁ w) = e₁ (p w)) → PreservesCircleOrientation τ₁ →
      ∃ e : T ≃ₜ T, e '' A = A' ∧ (∀ i, ∀ z ∈ P i, e z = z) ∧ ∀ w, e (p w) = p' w := by
    intro e₁ τ₁ h1 h2 h3 h4
    obtain ⟨f, hf, hfix, hw⟩ := finish_match hT hP hA' hAP' hp' h4
    refine ⟨e₁.trans f, ?_, fun i z hz => ?_, fun w => ?_⟩
    · change (fun x => f (e₁ x)) '' A = A'
      rw [← image_image (g := f) (f := e₁), h2, hf]
    · change f (e₁ z) = z
      rw [h1 i z hz, hfix i z hz]
    · change f (e₁ (p w)) = p' w
      rw [← h3, hw]
  obtain ⟨L, hLc, hL, hl⟩ := exists_circle_lift τ
  rcases hL with hL | hL
  · exact done e₀ τ hfix₀ he₀ hτ ⟨L, hLc, hL, hl⟩
  rcases H with h | ⟨i₀, ω, hω⟩
  · have hex : ¬ ∀ α : T ≃ₜ T, (∀ i, ∀ z ∈ P i, α z = z) → α '' A' = A' → ∀ u v w u' v' w',
      α (p' u) = p' u' → α (p' v) = p' v' → α (p' w) = p' w' →
        CircleCyclic u v w → CircleCyclic u' v' w' :=
      fun hno => h (orientable_of_no_reversal hT hP hPP hA' hAP' hp'.1 hp'.2.1 hp'.2.2 hno)
    push Not at hex
    obtain ⟨α, hαf, hαi, u, v, w, u', v', w', hu, hv, hw, hc, hnc⟩ := hex
    obtain ⟨σ, hσ⟩ := exists_circle_transfer hp' hp' α hA' hαi
    obtain ⟨M, hMc, hM, hm⟩ := exists_circle_lift σ
    rcases hM with hM | hM
    · exfalso
      have h1 := circleCyclic_map_mono hMc hM hm hc
      have e1 : σ u = u' := hp'.2.1 (by rw [hσ, hu])
      have e2 : σ v = v' := hp'.2.1 (by rw [hσ, hv])
      have e3 : σ w = w' := hp'.2.1 (by rw [hσ, hw])
      rw [e1, e2, e3] at h1
      exact hnc h1
    · refine done (e₀.trans α) (τ.trans σ) (fun i z hz => ?_) ?_ (fun x => ?_) ⟨fun t => M (L t),
        hMc.comp hLc, hM.comp hL, fun t => ?_⟩
      · change α (e₀ z) = z
        rw [hfix₀ i z hz, hαf i z hz]
      · change (fun x => α (e₀ x)) '' A = A'
        rw [← image_image (g := α) (f := e₀), he₀, hαi]
      · change p' (σ (τ x)) = α (e₀ (p x))
        rw [hσ, hτ]
      · change σ (τ _) = _
        rw [hl, hm]
  · exfalso
    have hpres := preserved_of_fix hT ω e₀ (hP i₀) (hfix₀ i₀)
    obtain ⟨φ, hφc, hφi, hφr, hφ⟩ := ω.isDirection A' hA'
    obtain ⟨s, hs⟩ := exists_circle_transfer hp' (D' := A') ⟨hφc, hφi, hφr⟩ (Homeomorph.refl T) hA'
      (image_id _)
    have hs' : ∀ w, φ (s w) = p' w := hs
    have hpi := Real.pi_gt_three
    have hcy : CircleCyclic (Circle.exp 0) (Circle.exp 1) (Circle.exp 2) := by
      refine ⟨1, 2, by norm_num, by norm_num, by linarith, ?_, ?_⟩ <;> simp
    have hab : Circle.exp 0 ≠ Circle.exp 1 := circle_exp_ne (by norm_num)
      (by rw [abs_lt]; constructor <;> linarith)
    have hbc : Circle.exp 1 ≠ Circle.exp 2 := circle_exp_ne (by norm_num)
      (by rw [abs_lt]; constructor <;> linarith)
    have hac : Circle.exp 0 ≠ Circle.exp 2 := circle_exp_ne (by norm_num)
      (by rw [abs_lt]; constructor <;> linarith)
    generalize Circle.exp 0 = a at hcy hab hac
    generalize Circle.exp 1 = b at hcy hab hbc
    generalize Circle.exp 2 = c at hcy hbc hac
    have hmem : ∀ w, p w ∈ discBd A := fun w => by rw [← hp.2.2]; exact mem_range_self w
    have h1 := circleCyclic_map_anti hLc hL hl hcy
    have h2 := hpres A hA (p a) (p b) (p c) (hmem a) (hmem b) (hmem c) (fun h => hab (hp.2.1 h))
      (fun h => hbc (hp.2.1 h)) (fun h => hac (hp.2.1 h))
    rw [he₀, ← hτ, ← hτ, ← hτ] at h2
    have h3 := h2.trans (hω a b c hab hbc hac)
    simp only [← hs'] at h3
    have hsτ : ∀ {x y : Circle}, x ≠ y → s (τ x) ≠ s (τ y) := fun h he => h (τ.injective
      (s.injective he))
    have hs1 : ∀ {x y : Circle}, x ≠ y → s x ≠ s y := fun h he => h (s.injective he)
    rw [hφ _ _ _ (hsτ hab) (hsτ hbc) (hsτ hac), hφ _ _ _ (hs1 hab) (hs1 hbc) (hs1 hac)] at h3
    have hτ1 : ∀ {x y : Circle}, x ≠ y → τ x ≠ τ y := fun h he => h (τ.injective he)
    rcases circle_map_or s with hf | hf
    · have h4 := (hf _ _ _ (hτ1 hab) (hτ1 hbc) (hτ1 hac)).trans (h3.trans
      (hf a b c hab hbc hac).symm)
      exact not_circleCyclic_both (h4.2 hcy) h1
    · have h4 : CircleCyclic (s (τ a)) (s (τ b)) (s (τ c)) := (hf _ _ _ (hτ1 hac) (hτ1 hbc).symm
      (hτ1 hab)).1 h1
      have h5 := (hf a c b hac hbc.symm hab).2 (h3.1 h4)
      exact not_circleCyclic_both hcy h5

/-- **A family of marked discs**, with some protected discs. -/
theorem exists_family_param_match [ConnectedSpace T] (hT : IsClosedSurface T) {κ : Type} [Finite κ]
  {Q : κ → Set T} (hQ : ∀ k, IsClosedDisc (Q k)) (hQQ : Pairwise fun i j => Disjoint (Q i)
    (Q j))
    {n : ℕ} {A A' : Fin n → Set T} (hA : ∀ i, IsClosedDisc (A i)) (hA' : ∀ i, IsClosedDisc (A' i))
      (hAA : Pairwise fun i j => Disjoint (A i) (A j)) (hAA' : Pairwise fun i j => Disjoint (A' i)
        (A' j))
    (hAQ : ∀ i k, Disjoint (A i) (Q k)) (hAQ' : ∀ i k, Disjoint (A' i) (Q k)) {p p' : Fin n
      → Circle → T} (hp : ∀ i, IsBdParam (A i) (p i)) (hp' : ∀ i, IsBdParam (A' i) (p' i))
    (H : ¬ IsOrientableSurface T ∨ ∃ (_ : κ) (ω : SurfaceOrientation T), ∀ i a b c, a ≠ b → b ≠ c
      → a ≠ c → (ω.pos (A i) (p i a) (p i b) (p i c) ↔ ω.pos (A' i) (p' i a) (p' i b) (p' i c))) :
    ∃ e : T ≃ₜ T, (∀ k, ∀ z ∈ Q k, e z = z) ∧ (∀ i, e '' A i = A' i) ∧ ∀ i w, e (p i w) = p' i w
      := by
  classical
  suffices S : ∀ m ≤ n, ∃ e : T ≃ₜ T, (∀ k, ∀ z ∈ Q k, e z = z) ∧ ∀ i : Fin n, i.1 < m → e '' A i
    = A' i ∧ ∀ w, e (p i w) = p' i w by
    obtain ⟨e, h1, h2⟩ := S n le_rfl
    exact ⟨e, h1, fun i => (h2 i i.2).1, fun i => (h2 i i.2).2⟩
  intro m
  induction m with
  | zero => exact fun _ => ⟨Homeomorph.refl T, fun _ _ _ => rfl, fun i h => absurd h
    (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨e, h1, h2⟩ := ih (by omega)
    let c : Fin n := ⟨m, by omega⟩
    let P : κ ⊕ {i : Fin n // i.1 < m} → Set T := fun x => match x with
      | .inl k => Q k
      | .inr i => A' i.1
    have hP : ∀ i, IsClosedDisc (P i) := by
      rintro (k | i)
      · exact hQ k
      · exact hA' i.1
    have hPP : Pairwise fun i j => Disjoint (P i) (P j) := by
      rintro (k | i) (l | j) hne
      · exact hQQ fun h => hne (by rw [h])
      · exact (hAQ' j.1 k).symm
      · exact hAQ' i.1 l
      · exact hAA' fun h => hne (by rw [Subtype.ext h])
    have hne : ∀ i : {i : Fin n // i.1 < m}, c ≠ i.1 := fun i h => by
      have := congrArg Fin.val h
      have hi := i.2
      simp only [c] at this
      omega
    have hmA : Disjoint (e '' A c) (⋃ i, P i) := by
      refine Set.disjoint_iUnion_right.mpr ?_
      rintro (k | i)
      · refine Set.disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ hy
        have hx' : x ∈ Q k := by
          have : x = e x := (e.injective (h1 k (e x) hy)).symm
          exact this ▸ hy
        exact Set.disjoint_left.mp (hAQ c k) hx hx'
      · change Disjoint (e '' A c) (A' i.1)
        rw [← (h2 i.1 i.2).1]
        exact (Set.disjoint_image_iff e.injective).mpr (hAA (hne i))
    have hmA' : Disjoint (A' c) (⋃ i, P i) := by
      refine Set.disjoint_iUnion_right.mpr ?_
      rintro (k | i)
      · exact hAQ' c k
      · exact hAA' (hne i)
    have hH : ¬ IsOrientableSurface T ∨ ∃ (_ : κ ⊕ {i : Fin n // i.1 < m})
      (ω : SurfaceOrientation T), ∀ a b c', a ≠ b → b ≠ c' → a ≠ c' →
        (ω.pos (e '' A c) (e (p c a)) (e (p c b)) (e (p c c')) ↔ ω.pos (A' c) (p' c a) (p' c b)
          (p' c c')) := by
      rcases H with h | ⟨k, ω, hω⟩
      · exact Or.inl h
      · refine Or.inr ⟨.inl k, ω, fun a b c' hab hbc hac =>
          ?_⟩
        have hpres := preserved_of_fix hT ω e (hQ k) (h1 k)
        have hmem : ∀ w, p c w ∈ discBd (A c) := by
          intro w
          rw [← (hp c).2.2]
          exact mem_range_self w
        exact (hpres _ (hA c) _ _ _ (hmem a) (hmem b) (hmem c') (fun h => hab ((hp c).2.1 h))
          (fun h => hbc ((hp c).2.1 h)) (fun h => hac ((hp c).2.1 h))).trans
            (hω c a b c' hab hbc hac)
    obtain ⟨f, hf, hfix, hfw⟩ := exists_param_match hT hP hPP (image_disc e (hA c)).1
      (hA' c) hmA hmA' ((hp c).image e (hA c)) (hp' c) hH
    have hQf : ∀ k, ∀ z ∈ Q k, f z = z := fun k => hfix (.inl k)
    have hAf : ∀ i : {i : Fin n // i.1 < m}, ∀ z ∈ A' i.1, f z = z := fun i => hfix (.inr i)
    refine ⟨e.trans f, fun k z hz => ?_, fun i hi => ?_⟩
    · change f (e z) = z
      rw [h1 k z hz, hQf k z hz]
    by_cases him : i.1 < m
    · obtain ⟨h3, h4⟩ := h2 i him
      constructor
      · change (fun x => f (e x)) '' A i = _
        rw [← image_image (g := f) (f := e), h3]
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hAf ⟨i, him⟩ y hy]
          exact hy
        · exact fun hx => ⟨x, hx, hAf ⟨i, him⟩ x hx⟩
      · intro w
        change f (e (p i w)) = _
        rw [h4, hAf ⟨i, him⟩]
        exact discBd_subset _ (by rw [← (hp' i).2.2]; exact mem_range_self w)
    · have hic : i = c := Fin.ext (by simp only [c]; omega)
      subst hic
      constructor
      · change (fun x => f (e x)) '' A _ = _
        rw [← image_image (g := f) (f := e), hf]
      · exact fun w => hfw w

/-- Finitely many disjoint closed discs do not cover a closed connected surface. -/
theorem nonempty_compl_iUnion [ConnectedSpace T] (hT : IsClosedSurface T) {ι : Type*} [Finite ι] {D
  : ι → Set T} (hD : ∀ i, IsClosedDisc (D i)) (hdd : Pairwise fun i j => Disjoint (D i) (D j)) :
    (⋃ i, D i)ᶜ.Nonempty := by
  classical
  by_contra hn
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hn
  obtain ⟨x⟩ : Nonempty T := inferInstance
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hn ▸ mem_univ x)
  have hop : IsOpen (D i) := by
    have : D i = (⋃ j : {j // j ≠ i}, D j.1)ᶜ := by
      ext y
      constructor
      · intro hy hu
        obtain ⟨j, hj⟩ := mem_iUnion.mp hu
        exact Set.disjoint_left.mp (hdd j.2.symm) hy hj
      · intro hy
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hn ▸ mem_univ y)
        by_cases hji : j = i
        · exact hji ▸ hj
        · exact absurd (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩) hy
    rw [this]
    exact (isClosed_iUnion_of_finite fun j : {j // j ≠ i} => (hD j.1).isClosed).isOpen_compl
  have := IsClopen.eq_univ ⟨(hD i).isClosed, hop⟩ ⟨x, hi⟩
  obtain ⟨y, hy⟩ := nonempty_compl_disc hT (hD i)
  exact hy (this ▸ mem_univ y)

/-- An open set that is not empty holds any number of disjoint closed discs. -/
theorem exists_disc_family_in (hT : IsClosedSurface T) (n : ℕ) {V : Set T} (hV : IsOpen V)
  (hne : V.Nonempty) :
    ∃ M : Fin n → Set T, (∀ i, IsClosedDisc (M i)) ∧ (Pairwise fun i j => Disjoint (M i) (M j))
      ∧ ∀ i, M i ⊆ V := by
  induction n generalizing V with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := hne
    obtain ⟨E, hE, hs⟩ := exists_test_disc hT hV ⟨y, hy⟩ (B := {y}) (finite_singleton y)
    have hyE : y ∉ E := fun h => (hs h).2 rfl
    obtain ⟨M, hM, hMM, hMV⟩ := ih (hV.sdiff hE.isClosed) ⟨y, hy, hyE⟩
    refine ⟨Fin.cons E M, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hE
      · simpa using hM j
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact Set.disjoint_left.mpr fun x hx hx' => (hMV j hx').2 hx
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact Set.disjoint_right.mpr fun x hx hx' => (hMV i hx').2 hx
        | succ j =>
          simp only [Fin.cons_succ]
          exact hMM fun h => hij (by rw [h])
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact fun x hx => (hs hx).1
      · simp only [Fin.cons_succ]
        exact fun x hx => (hMV j hx).1

/-- **Step (2) of the proof of Graph Minors XIX, (15.2)**, page 381. On a closed connected surface a
homeomorphism carries a family of
disjoint marked discs to another such family, with the same index, if the surface is not orientable,
or if an orientation agrees with the
parametrizations on each pair of discs. -/
theorem exists_marked_match [ConnectedSpace T] (hT : IsClosedSurface T) {n : ℕ} {A A' : Fin n
  → Set T} (hA : ∀ i, IsClosedDisc (A i)) (hA' : ∀ i, IsClosedDisc (A'
    i))
    (hAA : Pairwise fun i j => Disjoint (A i) (A j)) (hAA' : Pairwise fun i j => Disjoint (A' i)
      (A' j)) {p p' : Fin n → Circle → T} (hp : ∀ i, IsBdParam (A i) (p i)) (hp' : ∀ i, IsBdParam
        (A' i) (p' i))
    (H : ¬ IsOrientableSurface T ∨ ∃ ω : SurfaceOrientation T, ∀ i a b c, a ≠ b → b ≠ c → a ≠ c →
      (ω.pos (A i) (p i a) (p i b) (p i c) ↔ ω.pos (A' i) (p' i a) (p' i b) (p' i c))) :
    ∃ e : T ≃ₜ T, (∀ i, e '' A i = A' i) ∧ ∀ i w, e (p i w) = p' i w := by
  have hc₀ : IsClosed (⋃ i, A i) := isClosed_iUnion_of_finite fun i => (hA i).isClosed
  have hc₁ : IsClosed (⋃ i, A' i) := isClosed_iUnion_of_finite fun i => (hA' i).isClosed
  obtain ⟨y, hy⟩ := nonempty_compl_iUnion hT hA hAA
  obtain ⟨Q₁, hQ₁, hs₁⟩ := exists_test_disc hT hc₁.isOpen_compl (nonempty_compl_iUnion hT hA' hAA')
    (B := {y}) (finite_singleton y)
  have hyQ : y ∉ Q₁ := fun h => (hs₁ h).2 rfl
  obtain ⟨Q₀, hQ₀, -, hs₀⟩ := exists_small_disc (hT.2.2 y) (hc₀.isOpen_compl.sdiff hQ₁.isClosed)
    ⟨hy, hyQ⟩
  have hQ01 : Disjoint Q₀ Q₁ := Set.disjoint_left.mpr fun x hx hx' =>
    (hs₀ hx).2 hx'
  have hne : ((Q₀ ∪ Q₁)ᶜ).Nonempty := by
    have := nonempty_compl_iUnion hT (D := fun b : Bool => if b then Q₀ else Q₁) (fun b
      => by cases b <;> simpa)
      (by
        rintro (_ | _) (_ | _) h
        · exact absurd rfl h
        · simpa using hQ01.symm
        · simpa using hQ01
        · exact absurd rfl h)
    obtain ⟨z, hz⟩ := this
    refine ⟨z, fun hu => hz ?_⟩
    rcases hu with hu | hu
    · exact mem_iUnion.mpr ⟨true, by simpa using hu⟩
    · exact mem_iUnion.mpr ⟨false, by simpa using hu⟩
  obtain ⟨M, hM, hMM, hMV⟩ := exists_disc_family_in hT n (hQ₀.isClosed.union
    hQ₁.isClosed).isOpen_compl hne
  have hAQ₀ : ∀ i (_ : Unit), Disjoint (A i) Q₀ := fun i _ => Set.disjoint_right.mpr fun x hx hx'
    => (hs₀ hx).1 (mem_iUnion.mpr ⟨i, hx'⟩)
  have hMQ₀ : ∀ i (_ : Unit), Disjoint (M i) Q₀ := fun i _ => Set.disjoint_left.mpr fun x hx hx'
    => hMV i hx (Or.inl hx')
  have hMQ₁ : ∀ i, Disjoint (M i) Q₁ := fun i => Set.disjoint_left.mpr fun x hx hx' => hMV i hx
    (Or.inr hx')
  obtain ⟨e₁, he₁, hfix₁⟩ := exists_disc_family_match hT (fun _ : Unit => Q₀) (fun _ => hQ₀)
    (fun _ _ h => absurd rfl h) A M hA hM hAA hMM hAQ₀ hMQ₀
  have hpM : ∀ i, IsBdParam (e₁ '' A i) fun w => e₁ (p i w) := by
    intro i
    exact (hp i).image e₁ (hA i)
  have hMM_e : ∀ i j, i ≠ j → Disjoint (e₁ '' A i) (e₁ '' A j) := by
    intro i j hij
    rw [he₁, he₁]
    exact hMM hij
  have hMQ₁_e : ∀ i, Disjoint (e₁ '' A i) Q₁ := by
    intro i
    rw [he₁]
    exact hMQ₁ i
  obtain ⟨e₂, -, he₂, hw⟩ := exists_family_param_match hT (κ := Unit) (Q := fun _ => Q₁)
    (fun _ => hQ₁) (fun _ _ h => absurd rfl h) (A := fun i => e₁ '' A i) (A' := A')
    (fun i => (image_disc e₁ (hA i)).1) hA' hMM_e hAA' (fun i _ => hMQ₁_e i)
    (fun i _ => Set.disjoint_left.mpr fun x hx hx' => (hs₁ hx').1 (mem_iUnion.mpr ⟨i, hx⟩)) hpM hp'
    (by
      rcases H with h | ⟨ω, hω⟩
      · exact Or.inl h
      · refine Or.inr ⟨(), ω, fun i a b c hab hbc hac =>
          ?_⟩
        have hpres := preserved_of_fix hT ω e₁ hQ₀ (hfix₁ ())
        have hmem : ∀ w, p i w ∈ discBd (A i) := by
          intro w
          rw [← (hp i).2.2]
          exact mem_range_self w
        exact (hpres _ (hA i) _ _ _ (hmem a) (hmem b) (hmem c) (fun h => hab ((hp i).2.1 h)) (fun h
          => hbc ((hp i).2.1 h)) (fun h => hac ((hp i).2.1 h))).trans (hω i a b c hab hbc hac))
  refine ⟨e₁.trans e₂, fun i => ?_, hw⟩
  change (fun x => e₂ (e₁ x)) '' A i = _
  rw [← image_image (g := e₂) (f := e₁)]
  exact he₂ i

end GraphMinor.GM19
