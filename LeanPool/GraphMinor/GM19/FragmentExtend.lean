/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentDirection

/-!
# Extending an orientation over a finite set

We show that a partial orientation of a closed connected surface `T` off a finite set `A` extends to
a surface orientation of `T`
(`extend_orientation`), by induction on `A` using `extend_over_point`. Given a partial orientation
`pos` on closed discs in
`(insert p A₀)ᶜ` with `p ∉ A₀`, `extend_over_point` extends `pos` to closed discs in `A₀ᶜ`: a
homeomorphism supported in a closed disc
`D ⊆ A₀ᶜ` (`exists_inside_move`) moves a puncture inside `discInt D` while preserving the
orientation off both punctures
(`IsPunctureShift.move`, by `sameOn_const`), connectedness of `A₀ᶜ` shifts the puncture `p` to any
point `q ∈ A₀ᶜ`, and any two shifted
orientations agree on closed discs in `A₀ᶜ` avoiding their punctures (by `sameOn_const`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

variable {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

/-- The relation `pos` on `Y`, read on `X` through `j`. -/
def pullPos (j : X → Y) (pos : Set Y → Y → Y → Y → Prop) : Set X → X → X → X → Prop :=
  fun Δ a b c ↦ pos (j '' Δ) (j a) (j b) (j c)

theorem isCompact_of_isClosedDisc {T : Type*} [TopologicalSpace T] {D : Set T}
  (hD : IsClosedDisc D) : IsCompact D := by
  obtain ⟨e⟩ := hD
  have : D = range fun z ↦ (e z).1 := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨z, rfl⟩
      exact (e z).2
  rw [this]
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  exact isCompact_range (continuous_subtype_val.comp e.continuous)

theorem isPreconnected_of_isClosedDisc {T : Type*} [TopologicalSpace T] {D : Set T}
  (hD : IsClosedDisc D) : IsPreconnected D := by
  obtain ⟨e⟩ := hD
  have : D = range fun z ↦ (e z).1 := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨z, rfl⟩
      exact (e z).2
  rw [this]
  have : PreconnectedSpace ClosedUnitDisc :=
    isPreconnected_iff_preconnectedSpace.1 (convex_closedBall (0 : EuclideanPlane) 1).isPreconnected
  exact isPreconnected_range (continuous_subtype_val.comp e.continuous)

omit [T2Space X] in
theorem IsPartialOrientation.pull {𝓕 : Set (Set X)} {𝓖 : Set (Set Y)} {pos : Set Y → Y → Y → Y
  → Prop} (h : IsPartialOrientation 𝓖 pos)
    {j : X → Y} (hj : ∀ Δ ∈ 𝓕, ContinuousOn j Δ ∧ InjOn j Δ ∧ j '' Δ ∈ 𝓖) : IsPartialOrientation 𝓕
      (pullPos j pos) := by
  refine ⟨fun Δ hΔ hd ↦ ?_, fun Δ₁ h₁ Δ₂ h₂ hd₁ hd₂ hs a b c ha hb hc hab hbc hac ↦ ?_⟩
  · obtain ⟨hcj, hij, hG⟩ := hj Δ hΔ
    obtain ⟨hd', hb'⟩ := isClosedDisc_image_injOn hd hcj hij
    obtain ⟨φ', hc, hi, hr, hφ⟩ := h.dir _ hG hd'
    have hcpt : CompactSpace Δ := isCompact_iff_compactSpace.1 (isCompact_of_isClosedDisc hd)
    let f : Δ → j '' Δ := fun x ↦ ⟨j x.1, mem_image_of_mem _ x.2⟩
    have hf : Continuous f := Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.1 hcj)
      _
    have hbij : Function.Bijective f := ⟨fun x y he ↦ Subtype.ext (hij x.2 y.2
      (congrArg Subtype.val he)), fun ⟨_, x, hx, rfl⟩ ↦ ⟨⟨x, hx⟩, rfl⟩⟩
    let e : Δ ≃ₜ j '' Δ := hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    have hmem : ∀ z, φ' z ∈ j '' Δ := fun z ↦ Surface.discBd_subset _ (hr ▸ mem_range_self z)
    let φ : Circle → X := fun z ↦ (e.symm ⟨φ' z, hmem z⟩).1
    have hjφ : ∀ z, j (φ z) = φ' z := fun z ↦ by
      have : (e (e.symm ⟨φ' z, hmem z⟩)).1 = φ' z := by rw [e.apply_symm_apply]
      exact this
    have hφΔ : ∀ z, φ z ∈ Δ := fun z ↦ (e.symm _).2
    refine ⟨φ, continuous_subtype_val.comp (e.symm.continuous.comp (hc.subtype_mk hmem)),
      fun x y he ↦ hi (by rw [← hjφ, ← hjφ, he]), ?_,
      fun a b c hab hbc hac ↦ ?_⟩
    · ext x
      constructor
      · rintro ⟨z, rfl⟩
        have : j (φ z) ∈ j '' discBd Δ := by
          rw [← hb', ← hr, hjφ]
          exact mem_range_self z
        obtain ⟨y, hy, he⟩ := this
        exact hij (Surface.discBd_subset _ hy) (hφΔ z) he ▸ hy
      · intro hx
        have : j x ∈ range φ' := by
          rw [hr, hb']
          exact mem_image_of_mem _ hx
        obtain ⟨z, hz⟩ := this
        exact ⟨z, hij (hφΔ z) (Surface.discBd_subset _ hx) ((hjφ z).trans hz)⟩
    · change pos (j '' Δ) (j (φ a)) (j (φ b)) (j (φ c)) ↔ _
      rw [hjφ, hjφ, hjφ]
      exact hφ a b c hab hbc hac
  · obtain ⟨hcj₁, hij₁, hG₁⟩ := hj Δ₁ h₁
    obtain ⟨hcj₂, hij₂, hG₂⟩ := hj Δ₂ h₂
    obtain ⟨hd₁', hb₁⟩ := isClosedDisc_image_injOn hd₁ hcj₁ hij₁
    obtain ⟨hd₂', hb₂⟩ := isClosedDisc_image_injOn hd₂ hcj₂ hij₂
    have hmem : ∀ {x}, x ∈ discBd Δ₁ ∩ discBd Δ₂ → j x ∈ discBd (j '' Δ₁) ∩ discBd (j '' Δ₂)
      := fun hx ↦
      ⟨hb₁ ▸ mem_image_of_mem _ hx.1, hb₂ ▸ mem_image_of_mem _ hx.2⟩
    have hsub : ∀ {x}, x ∈ discBd Δ₁ ∩ discBd Δ₂ → x ∈ Δ₂ := fun hx ↦ Surface.discBd_subset _ hx.2
    exact h.agree _ hG₁ _ hG₂ hd₁' hd₂' (image_mono hs) _ _ _ (hmem ha) (hmem hb) (hmem hc)
      (fun e ↦ hab (hij₂ (hsub ha) (hsub hb) e)) (fun e ↦ hbc (hij₂ (hsub hb) (hsub hc) e))
        (fun e ↦ hac (hij₂ (hsub ha) (hsub hc) e))

omit [T2Space X] in
theorem sameOn_rev_left {pos pos' : Set X → X → X → X → Prop} {Δ : Set X} (h : SameOn pos
  (revPos pos') Δ) : SameOn (revPos pos) pos' Δ :=
  fun a b c ha hb hc hab hbc hac ↦ h a c b ha hc hb hac hbc.symm hab

omit [T2Space X] in
theorem SameOn.trans {pos₁ pos₂ pos₃ : Set X → X → X → X → Prop} {Δ : Set X}
  (h : SameOn pos₁ pos₂ Δ) (h' : SameOn pos₂ pos₃ Δ) :
    SameOn pos₁ pos₃ Δ := fun a b c ha hb hc hab hbc hac ↦ (h a b c ha hb hc hab hbc hac).trans
      (h' a b c ha hb hc hab hbc hac)

omit [T2Space X] in
theorem SameOn.symm {pos₁ pos₂ : Set X → X → X → X → Prop} {Δ : Set X}
  (h : SameOn pos₁ pos₂ Δ) : SameOn pos₂ pos₁ Δ :=
  fun a b c ha hb hc hab hbc hac ↦ (h a b c ha hb hc hab hbc hac).symm

omit [T2Space X] in
theorem IsDirectionOf.congr {F : Set X} {r r' : X → X → X → Prop} (h : IsDirectionOf F r)
    (he : ∀ a b c, a ∈ F → b ∈ F → c ∈ F → a ≠ b → b ≠ c → a ≠ c → (r a b c ↔ r' a b c)) :
      IsDirectionOf F r' := by
  obtain ⟨φ, hc, hi, rfl, hφ⟩ := h
  refine ⟨φ, hc, hi, rfl, fun a b c hab hbc hac ↦ ?_⟩
  rw [← he _ _ _ (mem_range_self a) (mem_range_self b) (mem_range_self c) (hi.ne hab) (hi.ne hbc)
    (hi.ne hac)]
  exact hφ a b c hab hbc hac

section Move

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- A homeomorphism of `T`, the identity off the closed disc `D`, that takes the centre of a chart
of `D` to a given inside point. -/
theorem exists_inside_push (hT : IsClosedSurface T) {D : Set T} {h : T → ℂ} {g : ℂ → T}
  (hD : IsClosedDisc D) (c : IsChart D h g) {x : T}
    (hx : x ∈ discInt D) : ∃ e : T ≃ₜ T, e (g 0) = x ∧ ∀ z ∉ D, e z = z := by
  classical
  have : CompactSpace T := hT.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  rw [c.discInt_eq] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hu' : ‖u‖ < 1 := by simpa using hu
  obtain ⟨θ, θc, θb, θ0, θe⟩ := exists_disc_push hu'
  let F : T → T := fun z ↦ if z ∈ D then g (θ (h z)) else z
  have hin : ∀ {z}, z ∈ D → F z = g (θ (h z)) := fun hz ↦ ite_eq_left hz
  have hout : ∀ {z}, z ∉ D → F z = z := fun hz ↦ ite_eq_right hz
  have hbd : ∀ {z}, z ∈ discBd D → g (θ (h z)) = z := fun {z} hz ↦ by
    have : h z ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem _ hz
    rw [θe _ this]
    exact c.gh (Surface.discBd_subset _ hz)
  have hmaps : MapsTo (fun z ↦ g (θ (h z))) D D := fun z hz ↦ c.gm (θb.mapsTo (c.hm hz))
  have hcont : Continuous F := by
    have h₁ : ContinuousOn F D := by
      refine ContinuousOn.congr ?_ fun z hz ↦ hin hz
      exact c.gc.comp (θc.comp_continuousOn c.hc) fun z hz ↦ θb.mapsTo (c.hm hz)
    have h₂ : ContinuousOn F (closure Dᶜ) := by
      refine continuousOn_id.congr fun z hz ↦ ?_
      by_cases hzD : z ∈ D
      · rw [hin hzD]
        refine hbd ?_
        by_contra hn
        have hzi : z ∈ discInt D := ⟨hzD, hn⟩
        obtain ⟨w, hw, hwn⟩ := _root_.mem_closure_iff.1 hz _ (hD.isOpen_discInt hman) hzi
        exact hwn (discInt_subset D hw)
      · exact hout hzD
    have hcov : D ∪ closure Dᶜ = univ := by
      refine eq_univ_of_forall fun z ↦ ?_
      by_cases hz : z ∈ D
      · exact Or.inl hz
      · exact Or.inr (subset_closure hz)
    have := h₁.union_of_isClosed h₂ hD.isClosed isClosed_closure
    rw [hcov] at this
    exact continuousOn_univ.1 this
  have hbij : Function.Bijective F := by
    constructor
    · intro z w he
      by_cases hz : z ∈ D <;> by_cases hw : w ∈ D
      · rw [hin hz, hin hw] at he
        have h₁ := c.hg.injOn (θb.mapsTo (c.hm hz)) (θb.mapsTo (c.hm hw)) he
        have h₂ := θb.injOn (c.hm hz) (c.hm hw) h₁
        exact c.gh.injOn hz hw h₂
      · rw [hin hz, hout hw] at he
        exact absurd (he ▸ hmaps hz) hw
      · rw [hout hz, hin hw] at he
        exact absurd (he.symm ▸ hmaps hw) hz
      · rwa [hout hz, hout hw] at he
    · intro w
      by_cases hw : w ∈ D
      · obtain ⟨v, hv, hve⟩ := θb.surjOn (c.hm hw)
        refine ⟨g v, ?_⟩
        rw [hin (c.gm hv), c.hg hv, hve]
        exact c.gh hw
      · exact ⟨w, hout hw⟩
  let e : T ≃ₜ T := hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hbij)
  refine ⟨e, ?_, fun z hz ↦ hout hz⟩
  change F (g 0) = _
  rw [hin (c.gm (by simp)), c.hg (by simp), θ0]

/-- Two inside points of a closed disc are moved one to the other by a homeomorphism that is the
identity off the disc. -/
theorem exists_inside_move (hT : IsClosedSurface T) {D : Set T} (hD : IsClosedDisc D) {x y : T}
  (hx : x ∈ discInt D) (hy : y ∈ discInt D) :
    ∃ e : T ≃ₜ T, e x = y ∧ ∀ z ∉ D, e z = z := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨e₁, h₁, h₂⟩ := exists_inside_push hT hD c hx
  obtain ⟨e₂, h₃, h₄⟩ := exists_inside_push hT hD c hy
  refine ⟨e₁.symm.trans e₂, ?_, fun z hz ↦ ?_⟩
  · simp [← h₁, h₃]
  · have : e₁.symm z = z := by
      rw [e₁.symm_apply_eq, h₂ z hz]
    simp [this, h₄ z hz]

theorem exists_test_disc (hT : IsClosedSurface T) {W : Set T} (hW : IsOpen W)
  (hne : W.Nonempty) {B : Set T} (hB : B.Finite) :
    ∃ E : Set T, IsClosedDisc E ∧ E ⊆ W ∩ Bᶜ := by
  obtain ⟨x, hxW, hxB⟩ := (dense_compl_finite hT.2.2 hB).inter_open_nonempty W hW hne
  obtain ⟨E, hE, -, hs⟩ := exists_small_disc (hT.2.2 x) (hW.inter hB.isClosed.isOpen_compl) ⟨hxW,
    hxB⟩
  exact ⟨E, hE, hs⟩

omit [T2Space T] in
theorem nonempty_compl_disc (hT : IsClosedSurface T) {D : Set T} (hD : IsClosedDisc D) :
  Dᶜ.Nonempty := by
  by_contra hn
  obtain ⟨y, hy⟩ := hD.nonempty_discInt
  obtain ⟨x, hx, -⟩ := hD.isOArc_discBd.exists_ne y
  have := discBd_subset_closure_compl hT hD hx
  rw [not_nonempty_iff_eq_empty.1 hn, closure_empty] at this
  exact this

end Move

section Extend

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

/-- `ρ` is an orientation off `q` and off `A₀`, and it is equal to `pos` off `p` and off `q`. -/
structure IsPunctureShift (A₀ : Set T) (p q : T) (pos ρ : Set T → T → T → T → Prop) : Prop where
  isPartial : IsPartialOrientation {Δ | Δ ⊆ (insert q A₀)ᶜ} ρ
  same : ∀ D, IsClosedDisc D → D ⊆ (insert p (insert q A₀))ᶜ → SameOn ρ pos D

omit [ConnectedSpace T] in
theorem isOpen_compl_finite (B : Set T) (hB : B.Finite) : IsOpen Bᶜ := hB.isClosed.isOpen_compl

theorem isPreconnected_compl_finite (hT : IsClosedSurface T) {B : Set T}
  (hB : B.Finite) : IsPreconnected Bᶜ := by
  have := isPreconnected_sdiff_finite hT isOpen_univ isPreconnected_univ hB
  rwa [show univ \ B = Bᶜ by ext; simp] at this

/-- A shift of the puncture from `q` to a point `q'` of the same closed disc. -/
theorem IsPunctureShift.move (hT : IsClosedSurface T) {A₀ : Set T} (hA : A₀.Finite) {p q q' : T}
  {pos ρ : Set T → T → T → T → Prop}
    (hpos : IsPartialOrientation {Δ | Δ ⊆ (insert p A₀)ᶜ} pos) (hρ : IsPunctureShift A₀ p q pos ρ)
      {D : Set T} (hD : IsClosedDisc D)
    (hDA : D ⊆ A₀ᶜ) (hq : q ∈ discInt D) (hq' : q' ∈ discInt D) : ∃ ρ', IsPunctureShift A₀ p q' pos
      ρ' := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  obtain ⟨e, he, hfix⟩ := exists_inside_move hT hD hq' hq
  have hP : IsPartialOrientation {Δ | Δ ⊆ (insert q' A₀)ᶜ} (pullPos e ρ) := by
    refine hρ.isPartial.pull fun Δ hΔ ↦ ⟨e.continuous.continuousOn, e.injective.injOn, ?_⟩
    rintro _ ⟨z, hz, rfl⟩ (h | h)
    · apply hΔ hz
      exact Or.inl (e.injective (h.trans he.symm))
    · have hn : e z ∉ D := fun hin ↦ hDA hin h
      have hzn : z ∉ D := fun hin ↦ by
        have h' : e z = z := e.injective (hfix (e z) hn)
        rw [h'] at hn
        exact hn hin
      apply hΔ hz
      exact Or.inr (hfix z hzn ▸ h)
  refine ⟨pullPos e ρ, hP, fun D₁ hD₁ hs ↦ ?_⟩
  have hfin : (insert p (insert q' A₀)).Finite := (hA.insert _).insert _
  have hG := isOpen_compl_finite _ hfin
  have hGc := isPreconnected_compl_finite hT hfin
  have h₁ : IsPartialOrientation {Δ | Δ ⊆ (insert p (insert q' A₀))ᶜ} (pullPos e ρ)
    := hP.mono fun Δ hΔ ↦
    hΔ.trans (compl_subset_compl.2 (subset_insert _ _))
  have h₂ : IsPartialOrientation {Δ | Δ ⊆ (insert p (insert q' A₀))ᶜ} pos := hpos.mono fun Δ hΔ ↦
    hΔ.trans (compl_subset_compl.2 (insert_subset_insert (subset_insert _ _)))
  obtain ⟨E, hE, hsE⟩ := exists_test_disc hT hD.isClosed.isOpen_compl (nonempty_compl_disc hT hD)
    (B := insert q (insert p (insert q' A₀))) (hfin.insert _)
  have hsG : E ⊆ (insert p (insert q' A₀))ᶜ := fun x hx hn ↦ (hsE hx).2 (Or.inr hn)
  have hE₁ : E ⊆ (insert p (insert q A₀))ᶜ := by
    intro x hx hn
    have h' := (hsE hx).2
    rcases hn with h | h | h
    · exact h' (Or.inr (Or.inl h))
    · exact h' (Or.inl h)
    · exact h' (Or.inr (Or.inr (Or.inr h)))
  have hfixE : ∀ x ∈ E, e x = x := fun x hx ↦ hfix x (hsE hx).1
  have himg : e '' E = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hfixE y hy]
    · intro hx
      exact ⟨x, hx, hfixE x hx⟩
  have hSameE : SameOn (pullPos e ρ) pos E := by
    intro a b c ha hb hc hab hbc hac
    change ρ (e '' E) (e a) (e b) (e c) ↔ _
    rw [himg, hfixE a (Surface.discBd_subset _ ha), hfixE b (Surface.discBd_subset _ hb),
      hfixE c (Surface.discBd_subset _ hc)]
    exact hρ.same E hE hE₁ a b c ha hb hc hab hbc hac
  exact (sameOn_const hman hG hGc (fun x _ ↦ hT.2.2 x) h₁ h₂ hE hD₁ hsG hs).1 hSameE

/-- An orientation off `A₀` and off one more point `p` extends to an orientation off `A₀`. -/
theorem extend_over_point (hT : IsClosedSurface T) {A₀ : Set T} (hA : A₀.Finite) {p : T}
  (hp : p ∉ A₀) {pos : Set T → T → T → T → Prop}
    (hpos : IsPartialOrientation {Δ | Δ ⊆ (insert p A₀)ᶜ} pos) :
    ∃ pos', IsPartialOrientation {Δ | Δ ⊆ A₀ᶜ} pos' ∧ ∀ D, IsClosedDisc D → D ⊆ (insert p A₀)ᶜ
      → SameOn pos' pos D := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  set Q : Set T := {q | ∃ ρ, IsPunctureShift A₀ p q pos ρ} with hQ
  have hstart : IsPunctureShift A₀ p p pos pos :=
    ⟨hpos, fun D _ _ a b c _ _ _ _ _ _ ↦ Iff.rfl⟩
  have hopenV : IsOpen A₀ᶜ := isOpen_compl_finite _ hA
  have hnear : ∀ x ∈ A₀ᶜ, ∃ D, IsClosedDisc D ∧ x ∈ discInt D ∧ D ⊆ A₀ᶜ
    := fun x hx ↦ exists_small_disc (hT.2.2 x) hopenV hx
  have hop₁ : IsOpen (Q ∩ A₀ᶜ) := by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro q ⟨⟨ρ, hρ⟩, hqV⟩
    obtain ⟨D, hD, hqD, hs⟩ := hnear q hqV
    refine Filter.mem_of_superset ((hD.isOpen_discInt hman).mem_nhds hqD) fun q' hq' ↦ ?_
    exact ⟨hρ.move hT hA hpos hD hs hqD hq', hs (discInt_subset D hq')⟩
  have hop₂ : IsOpen (Qᶜ ∩ A₀ᶜ) := by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro q ⟨hqn, hqV⟩
    obtain ⟨D, hD, hqD, hs⟩ := hnear q hqV
    refine Filter.mem_of_superset ((hD.isOpen_discInt hman).mem_nhds hqD) fun q' hq' ↦ ?_
    refine ⟨fun ⟨ρ, hρ⟩ ↦ hqn (hρ.move hT hA hpos hD hs hq' hqD), hs (discInt_subset D hq')⟩
  have hall : A₀ᶜ ⊆ Q := by
    have hd : Disjoint (Q ∩ A₀ᶜ) (Qᶜ ∩ A₀ᶜ) := disjoint_left.2 fun x hx hx' ↦ hx'.1 hx.1
    have hcov : A₀ᶜ ⊆ (Q ∩ A₀ᶜ) ∪ (Qᶜ ∩ A₀ᶜ) := fun x hx ↦ by
      by_cases h : x ∈ Q
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
    rcases (isPreconnected_compl_finite hT hA).subset_or_subset hop₁ hop₂ hd hcov with h | h
    · exact fun x hx ↦ (h hx).1
    · exact absurd ⟨pos, hstart⟩ (h hp).1
  have huniq : ∀ {q₁ q₂ ρ₁ ρ₂}, IsPunctureShift A₀ p q₁ pos ρ₁ → IsPunctureShift A₀ p q₂ pos ρ₂
    → ∀ {Δ}, IsClosedDisc Δ →
      Δ ⊆ A₀ᶜ → q₁ ∉ Δ → q₂ ∉ Δ → SameOn ρ₁ ρ₂ Δ := by
    intro q₁ q₂ ρ₁ ρ₂ h₁ h₂ Δ hΔ hs hn₁ hn₂
    have hfin : (insert q₁ (insert q₂ A₀)).Finite := (hA.insert _).insert _
    have hP₁ : IsPartialOrientation {Δ | Δ ⊆ (insert q₁ (insert q₂ A₀))ᶜ} ρ₁
      := h₁.isPartial.mono fun Δ hΔ ↦
      hΔ.trans (compl_subset_compl.2 (insert_subset_insert (subset_insert _ _)))
    have hP₂ : IsPartialOrientation {Δ | Δ ⊆ (insert q₁ (insert q₂ A₀))ᶜ} ρ₂
      := h₂.isPartial.mono fun Δ hΔ ↦
      hΔ.trans (compl_subset_compl.2 (subset_insert _ _))
    obtain ⟨E, hE, hsE⟩ := exists_test_disc hT isOpen_univ univ_nonempty (B := insert p (insert q₁
      (insert q₂ A₀))) (hfin.insert _)
    have hoff : ∀ {x}, x ∈ E → x ∉ insert p (insert q₁ (insert q₂ A₀)) := fun hx ↦ (hsE hx).2
    have hE₀ : E ⊆ (insert q₁ (insert q₂ A₀))ᶜ := fun x hx h ↦ hoff hx (Or.inr h)
    have hE₁ : E ⊆ (insert p (insert q₁ A₀))ᶜ := fun x hx h ↦ hoff hx (by
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h)))
    have hE₂ : E ⊆ (insert p (insert q₂ A₀))ᶜ := fun x hx h ↦ hoff hx (by
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    have hsΔ : Δ ⊆ (insert q₁ (insert q₂ A₀))ᶜ := by
      rintro x hx (h | h | h)
      · exact hn₁ (h ▸ hx)
      · exact hn₂ (h ▸ hx)
      · exact hs hx h
    exact (sameOn_const hman (isOpen_compl_finite _ hfin) (isPreconnected_compl_finite hT hfin)
      (fun x _ ↦ hT.2.2 x) hP₁ hP₂ hE hΔ hE₀ hsΔ).1
      ((h₁.same E hE hE₁).trans (h₂.same E hE hE₂).symm)
  have hex : ∀ {Δ}, IsClosedDisc Δ → Δ ⊆ A₀ᶜ → ∃ q ρ, q ∉ Δ ∧ IsPunctureShift A₀ p q pos ρ := by
    intro Δ hΔ hs
    obtain ⟨E, hE, hsE⟩ := exists_test_disc hT hΔ.isClosed.isOpen_compl
      (nonempty_compl_disc hT hΔ) hA
    obtain ⟨q, hq⟩ := hE.nonempty_discInt
    have hqE := hsE (discInt_subset E hq)
    obtain ⟨ρ, hρ⟩ := hall hqE.2
    exact ⟨q, ρ, hqE.1, hρ⟩
  let pos' : Set T → T → T → T → Prop := fun Δ a b c ↦ ∃ q ρ, q ∉ Δ ∧ IsPunctureShift A₀ p q pos ρ
    ∧ ρ Δ a b c
  have hval : ∀ {q ρ Δ}, IsClosedDisc Δ → Δ ⊆ A₀ᶜ → q ∉ Δ → IsPunctureShift A₀ p q pos ρ
    → SameOn pos' ρ Δ := by
    intro q ρ Δ hΔ hs hq hρ a b c ha hb hc hab hbc hac
    constructor
    · rintro ⟨q', ρ', hq', hρ', h⟩
      exact (huniq hρ' hρ hΔ hs hq' hq a b c ha hb hc hab hbc hac).1 h
    · exact fun h ↦ ⟨q, ρ, hq, hρ, h⟩
  have hsubq : ∀ {q Δ}, Δ ⊆ A₀ᶜ → q ∉ Δ → Δ ∈ {Δ | Δ ⊆ (insert q A₀)ᶜ} := fun hs hq x hx h ↦
    h.elim (fun he ↦ hq (he ▸ hx)) (hs hx)
  refine ⟨pos', ⟨fun Δ hs hΔ ↦ ?_, fun Δ₁ h₁ Δ₂ h₂ hd₁ hd₂ hsub a b c ha hb hc hab hbc hac ↦ ?_⟩,
    fun D hD hs ↦ ?_⟩
  · obtain ⟨q, ρ, hq, hρ⟩ := hex hΔ hs
    exact (hρ.isPartial.dir Δ (hsubq hs hq) hΔ).congr (fun a b c ha hb hc hab hbc hac ↦
      (hval hΔ hs hq hρ a b c ha hb hc hab hbc hac).symm)
  · obtain ⟨q, ρ, hq, hρ⟩ := hex hd₂ h₂
    have hq₁ : q ∉ Δ₁ := fun h ↦ hq (hsub h)
    rw [hval hd₁ h₁ hq₁ hρ a b c ha.1 hb.1 hc.1 hab hbc hac, hval hd₂ h₂ hq hρ a b c ha.2 hb.2 hc.2
      hab hbc hac]
    exact hρ.isPartial.agree _ (hsubq h₁ hq₁) _ (hsubq h₂ hq) hd₁ hd₂ hsub a b c ha hb hc hab hbc
      hac
  · have hsV : D ⊆ A₀ᶜ := hs.trans (compl_subset_compl.2 (subset_insert _ _))
    have hpD : p ∉ D := fun h ↦ hs h (Or.inl rfl)
    exact hval hD hsV hpD hstart

/-- **An orientation off a finite set extends to the closed surface.** -/
theorem extend_orientation (hT : IsClosedSurface T) {A : Set T} (hA : A.Finite) {pos : Set T → T
  → T → T → Prop}
    (hpos : IsPartialOrientation {Δ | Δ ⊆ Aᶜ} pos) :
    ∃ ω : SurfaceOrientation T, ∀ D, IsClosedDisc D → D ⊆ Aᶜ → SameOn ω.pos pos D := by
  have key : ∀ {A : Set T}, A.Finite → ∀ {pos : Set T → T → T → T → Prop}, IsPartialOrientation {Δ
    | Δ ⊆ Aᶜ} pos →
      ∃ pos', IsPartialOrientation {Δ | Δ ⊆ (∅ : Set T)ᶜ} pos' ∧ ∀ D, IsClosedDisc D → D ⊆ Aᶜ
        → SameOn pos' pos D := by
    intro A hA
    induction A, hA using Set.Finite.induction_on with
    | empty => exact fun {pos} h ↦ ⟨pos, h, fun _ _ _ _ _ _ _ _ _ _ _ _ ↦ Iff.rfl⟩
    | @insert p A₀ hp hA₀ ih =>
      intro pos h
      obtain ⟨pos₁, h₁, hs₁⟩ := extend_over_point hT hA₀ hp h
      obtain ⟨pos₂, h₂, hs₂⟩ := ih h₁
      exact ⟨pos₂, h₂, fun D hD hs ↦ (hs₂ D hD (hs.trans (compl_subset_compl.2
        (subset_insert _ _)))).trans (hs₁ D hD hs)⟩
  obtain ⟨pos', h', hs⟩ := key hA hpos
  have hall : ∀ Δ : Set T, Δ ∈ {Δ | Δ ⊆ (∅ : Set T)ᶜ} := fun Δ x _ h ↦ h
  exact ⟨⟨pos', fun Δ hΔ ↦ h'.dir Δ (hall Δ) hΔ, fun Δ₁ Δ₂ h₁ h₂ ↦ h'.agree Δ₁ (hall _) Δ₂
    (hall _) h₁ h₂⟩, hs⟩

end Extend

end GraphMinor.GM19
