/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualContractFix

/-!
# Lines for the contracted dual

We give `IsDualLines` data for `G = Γ₁ \ v` and `J` (`exists_lines`). The point on the edge `e*` of
`G` is
`m e`, and the two lines are the images under `f` of the two halves of `e`, with their ends. Each
image
misses `G ∪ J`, so it lies in one face of `G ∪ J`. The main step is `face_ne`, that the two faces
differ.
Near `m e` the map `f` is the identity. The dual edge cuts the region `s` of `K` around `e` into two
parts, and the image of each part stays in one face and meets a half of `e`. Near `m e` these two
parts
fill a neighbourhood of `m e`, so they meet both faces beside `e*`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

namespace IsContractSetting

variable {Γ K D₀ Γ₁ H J : Drawing S} {hrad : PreRad (PaintingOrDrawing.drawing Γ) K}
  {A B : Set S → Set S} {m x y : Set S → S} {φ : Set S × Bool → Set S} {h : Set S × Bool → S}
  {ℓ : Set S × Bool → I → S} {hL : IsDualLines hrad D₀ A B m x y φ h ℓ} {r r₂ D : Set S} {v : S}
  {f : C(S, S)} (C : IsContractSetting hL Γ₁ r v r₂ D f H J)

include C

omit [ConnectedSpace S] in
/-- In the region of `K` around `e`, the only points of `Γ₁` are those on the two lines of `e`. -/
theorem cut_off_dual {e s : Set S} (he : e ∈ Γ.E) (hs : s ∈ K.R)
    (hs' : s = φ (e, true) ∪ φ (e, false) ∪ e) {z : S} (hz : z ∈ s)
    (hzC : z ∉ range (ℓ (e, true)) ∪ range (ℓ (e, false))) : z ∉ Γ₁.U := by
  have hzK : z ∉ K.U := region_subset hs hz
  have hzC' : ∀ b, z ∉ range (ℓ (e, b)) := by
    intro b hb
    cases b
    · exact hzC (Or.inr hb)
    · exact hzC (Or.inl hb)
  have hzcases : (∃ b, z ∈ φ (e, b)) ∨ z ∈ e := by
    have hz₂ := hz
    rw [hs'] at hz₂
    rcases hz₂ with (h₁ | h₁) | h₁
    · exact Or.inl ⟨true, h₁⟩
    · exact Or.inl ⟨false, h₁⟩
    · exact Or.inr h₁
  rw [C.U₁]
  rintro (h' | h')
  · exact hzK (K.V_subset_U h'.1)
  obtain ⟨e', he', hz'⟩ := mem_iUnion₂.mp h'
  have key : ∀ b, z ∉ range (ℓ (e', b)) := by
    intro b hb
    rcases hL.mem_line he' b hb with h₁ | h₁ | h₁
    · rcases hzcases with ⟨b', hb'⟩ | h₂
      · obtain rfl := hL.face_unique e' he' e he b b'
          (region_eq_of_mem (hL.face e' he' b).1 (hL.face e he b').1 h₁ hb')
        exact hzC' b hb
      · exact (hL.face_off he' b h₁).1 (Γ.closure_subset_U he (subset_closure h₂))
    · rcases hzcases with ⟨b', hb'⟩ | h₂
      · exact (hL.face_off he b' hb').1 (h₁ ▸ hL.m_U he')
      · obtain rfl := Γ.edge_eq_of_mem he he' h₂ (h₁ ▸ hL.m_mem he')
        exact hzC' b hb
    · exact hzK (h₁ ▸ hL.hub_K he' b)
  rcases hz' with hz' | hz'
  · exact key true hz'
  · exact key false hz'

omit [ConnectedSpace S] in
/-- A part `T` of `s` that meets `e` has its image in the face of the image of a half of `e`. -/
theorem side {e s T P : Set S} (he : e ∈ Γ.E) (hs : s ∈ K.R)
    (hs' : s = φ (e, true) ∪ φ (e, false) ∪ e) (hTc : IsPreconnected T)
    (hTs : T ⊆ s \ (range (ℓ (e, true)) ∪ range (ℓ (e, false)))) (hTe : (T ∩ e).Nonempty)
    (hP : P ∈ (radialUnion C.hrad₂).R) (hhal : ∀ b, f '' hal A B e b ⊆ P) {y : S} (hy : y ∈ T)
    (hyD : y ∉ D) : y ∈ P := by
  obtain ⟨z, hzT, hze⟩ := hTe
  have hzm : z ≠ m e := fun h' => (hTs hzT).2 (Or.inl (h' ▸ hL.m_mem_line he true))
  obtain ⟨b, hb⟩ := hL.hal_cover he hze hzm
  have hoff : Disjoint (f '' T) (radialUnion C.hrad₂).U := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    exact C.image_off (C.cut_off_dual he hs hs' (hTs hw).1 (hTs hw).2)
      (region_subset hs (hTs hw).1)
  have hsub : f '' T ⊆ P := subset_region hP (hTc.image f f.continuous.continuousOn) hoff
    (mem_image_of_mem _ hzT) (hhal b ⟨z, hb, rfl⟩)
  have := hsub ⟨y, hy, rfl⟩
  rwa [C.fix_off hyD] at this

omit [T2Space S] [ConnectedSpace S] C in
/-- The image of the closure of a half lies in the closure of a face that holds the image of the
half. -/
theorem image_closure_hal {e P : Set S} {b : Bool} (hhal : f '' hal A B e b ⊆ P) {z : S}
    (hz : z ∈ closure (hal A B e b)) : f z ∈ closure P :=
  closure_mono hhal (image_closure_subset_closure_image f.continuous ⟨z, hz, rfl⟩)

omit [ConnectedSpace S] in
theorem dual_mem_W {e : Set S} (he : e ∈ Γ.E) (hn : ¬ e ⊆ closure r \ r) :
    dualEdge h ℓ e ∈ (radialUnion C.hrad₂).E := by
  rw [radialUnion_E]
  exact Or.inl (C.dual_mem he hn)

omit [ConnectedSpace S] in
theorem dual_sub_closure {e P : Set S} (he : e ∈ Γ.E) (hn : ¬ e ⊆ closure r \ r)
    (hP : P ∈ (radialUnion C.hrad₂).R) {b : Bool} (hhal : f '' hal A B e b ⊆ P) :
    dualEdge h ℓ e ⊆ closure P := by
  have hm : m e ∈ closure P := by
    have := image_closure_hal hhal (hL.m_mem_closure_hal he b)
    rwa [C.m_fix he hn] at this
  exact edge_subset_closure_of_incident C.hS (C.dual_mem_W he hn) hP
    ⟨m e, hL.m_mem_dualEdge he, hm⟩

/-- The images of the two halves of `e` are not in one face. See the module docstring. -/
theorem face_ne {e P : Set S} (he : e ∈ Γ.E) (hn : ¬ e ⊆ closure r \ r)
    (hP : P ∈ (radialUnion C.hrad₂).R) (hhal : ∀ b, f '' hal A B e b ⊆ P) : False := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace C.hS
  have hgP := C.dual_sub_closure he hn hP (hhal true)
  obtain ⟨p, hp, q, hq, hpq, hep, heq, hall⟩ :=
    exists_two_faces C.hrad₂ C.hS C.hJ.2.2 C.hE₂ (C.dual_mem he hn)
  obtain ⟨Q, hQ, hQne, hgQ⟩ : ∃ Q ∈ (radialUnion C.hrad₂).R, Q ≠ P ∧ dualEdge h ℓ e ⊆ closure Q
    := by
    rcases hall P hP hgP with rfl | rfl
    · exact ⟨q, hq, hpq.symm, heq⟩
    · exact ⟨p, hp, hpq, hep⟩
  obtain ⟨s, hs, T₁, T₂, hes, hs', hT₁, hT₂, -, hcov, hm₁, hm₂⟩ :=
    hL.exists_cut_region C.hS C.hmax C.hE he
  have hopen : IsOpen (s ∩ Dᶜ) := (region_isOpen hs).inter C.hc.disc.isClosed.isOpen_compl
  have hmem : m e ∈ s ∩ Dᶜ := ⟨hes (hL.m_mem he), fun h' =>
    region_subset C.hr₂ (C.hc.sub h') (C.dual_U he hn (hL.m_mem_dualEdge he))⟩
  obtain ⟨z, hzW, hzQ⟩ := mem_closure_iff.mp (hgQ (hL.m_mem_dualEdge he)) _ hopen hmem
  have hzC : z ∉ range (ℓ (e, true)) ∪ range (ℓ (e, false)) := by
    intro h'
    have hzg : z ∈ dualEdge h ℓ e := by
      refine ⟨h', ?_⟩
      rintro (h₁ | h₁)
      · exact region_subset hs hzW.1 (h₁ ▸ hL.hub_K he true)
      · exact region_subset hs hzW.1 (h₁ ▸ hL.hub_K he false)
    exact region_subset hQ hzQ (Or.inl (C.dual_U he hn hzg))
  have hzT : z ∈ s \ (range (ℓ (e, true)) ∪ range (ℓ (e, false))) := ⟨hzW.1, hzC⟩
  have hzP : z ∈ P := by
    rw [hcov] at hzT
    rcases hzT with h₁ | h₁
    · exact C.side he hs hs' (isPreconnected_of_isOpenDisc hT₁) (hcov ▸ subset_union_left) hm₁ hP
        hhal h₁ hzW.2
    · exact C.side he hs hs' (isPreconnected_of_isOpenDisc hT₂) (hcov ▸ subset_union_right) hm₂ hP
        hhal h₁ hzW.2
  exact hQne (region_eq_of_mem hQ hP hzQ hzP)

omit [ConnectedSpace S] in
/-- The image of a half lies in a face of `G ∪ J`. -/
theorem exists_face {e : Set S} (he : e ∈ Γ.E) (b : Bool) :
    ∃ p ∈ (radialUnion C.hrad₂).R, f '' hal A B e b ⊆ p := by
  obtain ⟨z, hz⟩ := hL.hal_nonempty he b
  have hoff : ∀ w ∈ hal A B e b, f w ∉ (radialUnion C.hrad₂).U := fun w hw =>
    C.image_off (hL.hal_off_dual C.U₁ he b hw) (hL.hal_off_K he b hw)
  obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem (hoff z hz)
  refine ⟨p, hp, subset_region hp ((hL.hal_conn he b).image f f.continuous.continuousOn) ?_
    (mem_image_of_mem _ hz) hzp⟩
  refine disjoint_left.mpr ?_
  rintro _ ⟨w, hw, rfl⟩
  exact hoff w hw

/-- See the module docstring. -/
theorem exists_lines : ∃ (D₂ : Drawing S) (A₂ B₂ : Set S → Set S) (m₂ x₂ y₂ : Set S → S)
    (φ₂ : Set S × Bool → Set S) (h₂ : Set S × Bool → S) (ℓ₂ : Set S × Bool → I → S),
    IsDualLines C.hrad₂ D₂ A₂ B₂ m₂ x₂ y₂ φ₂ h₂ ℓ₂ ∧
    ∀ e ∈ Γ.E, ¬ e ⊆ closure r \ r → ∀ b, f '' hal A B e b ⊆ φ₂ (dualEdge h ℓ e, b) ∧
      range (ℓ₂ (dualEdge h ℓ e, b)) = f '' closure (hal A B e b) ∧
      h₂ (dualEdge h ℓ e, b) = f (halEnd x y e b) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace C.hS
  have hne : Nonempty S := ⟨v⟩
  have hback := fun g (hg : g ∈ (deleteVertices Γ₁ {v}).E) => C.exists_of_mem hg
  choose! back hbE hbn hbg using hback
  have hbd : ∀ e ∈ Γ.E, ¬ e ⊆ closure r \ r → back (dualEdge h ℓ e) = e := fun e he hn =>
    hL.dualEdge_inj (hbE _ (C.dual_mem he hn)) he (hbg _ (C.dual_mem he hn)).symm
  have hm₂ : ∀ g ∈ (deleteVertices Γ₁ {v}).E, m (back g) ∈ g := by
    intro g hg
    have := hL.m_mem_dualEdge (hbE g hg)
    rwa [← hbg g hg] at this
  obtain ⟨D₂, A₂, B₂, x₂, y₂, hU, hV, hsplit, hall⟩ :=
    exists_split_at (deleteVertices Γ₁ {v}) (fun g => m (back g)) hm₂
  have hparam : ∀ i : Set S × Bool, i.1 ∈ Γ.E → ∃ p : I → S, Continuous p ∧ Function.Injective p ∧
      p 0 = m i.1 ∧ p 1 = halEnd x y i.1 i.2 ∧ range p = closure (hal A B i.1 i.2) :=
    fun i hi => exists_inj_param (hL.hal_line hi i.2)
  choose! par hpc hpi hp0 hp1 hpr using hparam
  have hface : ∀ i : Set S × Bool, i.1 ∈ Γ.E → ∃ p ∈ (radialUnion C.hrad₂).R,
      f '' hal A B i.1 i.2 ⊆ p := fun i hi => C.exists_face hi i.2
  choose! face hfR hfs using hface
  have hg₀ : ∀ {g}, g ∈ (deleteVertices Γ₁ {v}).E → ∀ b,
      g ⊆ closure (face (back g, b)) := by
    intro g hg b
    have := C.dual_sub_closure (hbE g hg) (hbn g hg) (hfR (back g, b) (hbE g hg))
      (hfs (back g, b) (hbE g hg))
    rwa [← hbg g hg] at this
  refine ⟨D₂, A₂, B₂, fun g => m (back g), x₂, y₂, fun i => face (back i.1, i.2),
    fun i => f (halEnd x y (back i.1) i.2), fun i => f ∘ par (back i.1, i.2), ?_, ?_⟩
  · refine ⟨hU, hV, hsplit, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun g hg b => ⟨hfR (back g, b) (hbE g hg), hg₀ hg b⟩
    · intro g hg heq
      refine C.face_ne (hbE g hg) (hbn g hg) (hfR (back g, true) (hbE g hg)) fun b => ?_
      cases b
      · have := hfs (back g, false) (hbE g hg)
        exact fun z hz => (show face (back g, true) = face (back g, false) from heq).symm ▸ this hz
      · exact hfs (back g, true) (hbE g hg)
    · intro g hg p hp hgp
      obtain ⟨p₀, -, q₀, -, -, -, -, hall₀⟩ :=
        exists_two_faces C.hrad₂ C.hS C.hJ.2.2 C.hE₂ hg
      have hT := hall₀ _ (hfR (back g, true) (hbE g hg)) (hg₀ hg true)
      have hF := hall₀ _ (hfR (back g, false) (hbE g hg)) (hg₀ hg false)
      have hP := hall₀ p hp hgp
      have hdis : face (back g, true) ≠ face (back g, false) := by
        intro heq
        refine C.face_ne (hbE g hg) (hbn g hg) (hfR (back g, true) (hbE g hg)) fun b => ?_
        cases b
        · exact fun z hz => heq.symm ▸ hfs (back g, false) (hbE g hg) hz
        · exact hfs (back g, true) (hbE g hg)
      have key : p = face (back g, true) ∨ p = face (back g, false) := by
        rcases hP with h₁ | h₁ <;> rcases hT with h₂ | h₂ <;> rcases hF with h₃ | h₃
        all_goals first
          | exact Or.inl (h₁.trans h₂.symm)
          | exact Or.inr (h₁.trans h₃.symm)
          | exact absurd (h₂.trans h₃.symm) hdis
      rcases key with h₁ | h₁
      · exact ⟨true, h₁⟩
      · exact ⟨false, h₁⟩
    · intro g hg g' hg' b b' heq
      obtain ⟨e₀, -, -, hu, -⟩ :=
        face_edge C.hrad₂ C.hS C.hJ.2.2 C.hE₂ (hfR (back g, b) (hbE g hg))
      have h₁ := hu g hg (hg₀ hg b)
      have heq' : face (back g, b) = face (back g', b') := heq
      have h₂ := hu g' hg' (heq' ▸ hg₀ hg' b')
      exact h₁.trans h₂.symm
    · intro g hg b
      obtain ⟨s, hs, hsub⟩ := exists_region_of_sub C.hrad₂ (hfR (back g, b) (hbE g hg))
      have he := hbE g hg
      have hmem : f (halEnd x y (back g) b) ∈ closure s :=
        closure_mono hsub (image_closure_hal (hfs (back g, b) he) (hL.end_mem_closure_hal he b))
      refine ⟨s, hs, hsub, ?_, ?_⟩
      · rcases closure_region_subset hs hmem with h₁ | h₁
        · exact h₁
        · exact absurd h₁ (C.end_off (hL.hal_end he b))
      · have : f (halEnd x y (back g) b) ∈ H.V := by
          rw [C.hc.H_V]
          exact ⟨_, radial_V hrad (hL.hal_end he b), rfl⟩
        rw [← C.hc.J_V] at this
        exact this
    · intro g hg b
      exact f.continuous.comp (hpc (back g, b) (hbE g hg))
    · intro g hg b t t' htt
      have he := hbE g hg
      have hmem : ∀ t, par (back g, b) t ∈ closure (hal A B (back g) b) := fun t => by
        have := hpr (back g, b) he
        rw [show closure (hal A B (back g) b) = range (par (back g, b)) from this.symm]
        exact ⟨t, rfl⟩
      refine hpi (back g, b) he ?_
      rcases C.fibre htt with h₁ | ⟨h₁, h₂⟩
      · exact h₁
      · exact (hL.closure_hal_K he (hmem t) (radialStar_subset C.hvK h₁)).trans
          (hL.closure_hal_K he (hmem t') (radialStar_subset C.hvK h₂)).symm
    · intro g hg b
      have h₀ : par (back g, b) 0 = m (back g) := hp0 (back g, b) (hbE g hg)
      change f (par (back g, b) 0) = m (back g)
      rw [h₀]
      exact C.m_fix (hbE g hg) (hbn g hg)
    · intro g hg b
      have h₀ : par (back g, b) 1 = halEnd x y (back g) b := hp1 (back g, b) (hbE g hg)
      change f (par (back g, b) 1) = _
      rw [h₀]
    · intro g hg b t ht₀ ht₁
      have he := hbE g hg
      have hinj := hpi (back g, b) he
      have h₀ : par (back g, b) 0 = m (back g) := hp0 (back g, b) he
      have h₁ : par (back g, b) 1 = halEnd x y (back g) b := hp1 (back g, b) he
      have hmem : par (back g, b) t ∈ closure (hal A B (back g) b) := by
        have := hpr (back g, b) he
        rw [show closure (hal A B (back g) b) = range (par (back g, b)) from this.symm]
        exact ⟨t, rfl⟩
      rcases hL.mem_closure_hal he hmem with h₂ | h₂ | h₂
      · exact hfs (back g, b) he ⟨_, h₂, rfl⟩
      · exact absurd (hinj (h₂.trans h₀.symm)) ht₀
      · exact absurd (hinj (h₂.trans h₁.symm)) ht₁
  · intro e he hn b
    have hb₀ := hbd e he hn
    refine ⟨?_, ?_, ?_⟩
    · have := hfs (e, b) he
      simpa only [hb₀] using this
    · have : range (f ∘ par (back (dualEdge h ℓ e), b)) =
          f '' closure (hal A B e b) := by
        rw [hb₀, range_comp, show range (par (e, b)) = _ from hpr (e, b) he]
      exact this
    · simp only [hb₀]

end IsContractSetting

end GraphMinor.GM12
