/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualDraw
public import LeanPool.GraphMinor.GM12.SurfaceDualCount

/-!
# The dual lines extend a radial drawing

Let `D` be `Γ` with a new vertex on each edge, as in `IsDualLines`, and let `N` be the drawing of
the
lines through the faces. Then `K ∪ N` is a radial drawing of `D` (`preRad_glue`, `radMax_glue`).
This
is the main step. It means that everything GM11 proves about a drawing and a radial drawing of it
applies
to `D` and `K ∪ N`. Conditions (i)-(iii) are direct. Condition (iv) needs an argument only for the
two
lines at `m e` when they end at the same hub (`no_bigon_lines`). Maximality is by count.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ K D : Drawing S}
  {hrad : PreRad (PaintingOrDrawing.drawing Γ) K} {A B : Set S → Set S} {m x y : Set S → S}
  {f : Set S × Bool → Set S} {h : Set S × Bool → S} {ℓ : Set S × Bool → I → S}

omit [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
theorem exists_mid : ∃ t : I, t ≠ 0 ∧ t ≠ 1 := by
  refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, fun h' => ?_, fun h' => ?_⟩
  · have := congrArg Subtype.val h'
    norm_num at this
  · have := congrArg Subtype.val h'
    norm_num at this

omit [T2Space S] [ConnectedSpace S] in
/-- An `O`-arc through `a` is the range of a loop at `a` that is injective off its ends. -/
theorem exists_oArc_loop {F : Set S} (hF : IsOArc F) {a₀ : S} (ha : a₀ ∈ F) :
    ∃ a : I → S, Continuous a ∧ InjOn a (Ioo 0 1) ∧ a 0 = a₀ ∧ a 1 = a₀ ∧ range a = F ∧
      ∀ t, t ≠ 0 → t ≠ 1 → a t ≠ a₀ := by
  obtain ⟨p, hp, h0, h2, hper, himg, hr⟩ := exists_oArc_par hF ha
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hint : ∀ n : ℤ, (-1 : ℝ) < n → (n : ℝ) < 1 → n = 0 := by
    intro n h₁ h₂
    have h₃ : -1 < n := by exact_mod_cast h₁
    have h₄ : n < 1 := by exact_mod_cast h₂
    omega
  have hIoo : ∀ {t : I}, t ≠ 0 → t ≠ 1 → (0 : ℝ) < t ∧ (t : ℝ) < 1 := by
    intro t h₁ h₂
    refine ⟨lt_of_le_of_ne t.2.1 fun h' => h₁ (Subtype.ext h'.symm), lt_of_le_of_ne t.2.2 fun h' =>
      h₂ (Subtype.ext h')⟩
  refine ⟨fun t => p (2 * Real.pi * t), by fun_prop, ?_, by simpa using h0, by simpa using h2,
    ?_, ?_⟩
  · intro s hs t ht hst
    obtain ⟨n, hn⟩ := hper _ _ hst
    have hs' := hIoo hs.1.ne' hs.2.ne
    have ht' := hIoo ht.1.ne' ht.2.ne
    have hsub : (s : ℝ) - t = n := by
      have : 2 * Real.pi * ((s : ℝ) - t - n) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hpos.ne'
      linarith
    have : n = 0 := hint n (by linarith) (by linarith)
    subst this
    refine Subtype.ext ?_
    simpa [sub_eq_zero] using hsub
  · apply subset_antisymm
    · rintro _ ⟨t, rfl⟩
      exact hr ⟨_, rfl⟩
    · rw [← himg]
      rintro _ ⟨u, hu, rfl⟩
      have h₁ : 0 ≤ u / (2 * Real.pi) := div_nonneg hu.1 hpos.le
      have h₂ : u / (2 * Real.pi) ≤ 1 := (div_le_one hpos).mpr hu.2.le
      refine ⟨⟨_, h₁, h₂⟩, ?_⟩
      change p (2 * Real.pi * (u / (2 * Real.pi))) = p u
      rw [mul_div_cancel₀ _ hpos.ne']
  · intro t h₁ h₂ h'
    have h'' : p (2 * Real.pi * t) = p 0 := by
      rw [h0]
      exact h'
    obtain ⟨n, hn⟩ := hper _ _ h''
    have ht' := hIoo h₁ h₂
    have hsub : (t : ℝ) = n := by
      have : 2 * Real.pi * ((t : ℝ) - n) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hpos.ne'
      linarith
    have : n = 0 := hint n (by linarith) (by linarith)
    subst this
    exact h₁ (Subtype.ext (by simpa using hsub))

namespace IsDualLines

variable (hL : IsDualLines hrad D A B m x y f h ℓ)

include hL

/-- The region of `K` around `e` is made of the two faces at `e` and `e` itself. -/
theorem exists_region (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing Γ) K)
    (hE : Γ.E.Nonempty) {e : Set S} (he : e ∈ Γ.E) :
    ∃ s ∈ K.R, e ⊆ s ∧ s = f (e, true) ∪ f (e, false) ∪ e := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨z, hz⟩ := he.1
  have hdis : Disjoint e K.U := edge_disjoint hrad he
  obtain ⟨s, hs, hzs⟩ := exists_region_of_notMem (disjoint_left.mp hdis hz)
  have hes : e ⊆ s :=
    subset_region hs he.2.2.1.isConnected.isPreconnected hdis hz hzs
  obtain ⟨p, hp, q, hq, hpq, hep, heq, hs'⟩ := region_eq_two_faces hrad hS hmax hE hs he hes
  refine ⟨s, hs, hes, ?_⟩
  obtain ⟨b, rfl⟩ := hL.face_all e he p hp hep
  obtain ⟨b', rfl⟩ := hL.face_all e he q hq heq
  have hbb : b ≠ b' := fun h' => hpq (h' ▸ rfl)
  rw [hs']
  cases b <;> cases b'
  · exact absurd rfl hbb
  · rw [union_comm (f (e, false)) (f (e, true))]
  · rfl
  · exact absurd rfl hbb

/-- The two lines at `m e` cut the region `s` of `K` around `e` into two open discs, by
`exists_crosscut_sides`. Each part meets `e`: a part that misses `e` lies in one of the two faces at
`e`, but the lines are in its closure, and they enter the other face. -/
theorem exists_cut_region (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing Γ) K)
    (hE : Γ.E.Nonempty) {e : Set S} (he : e ∈ Γ.E) :
    ∃ s ∈ K.R, ∃ T₁ T₂ : Set S, e ⊆ s ∧ s = f (e, true) ∪ f (e, false) ∪ e ∧ IsOpenDisc T₁ ∧
      IsOpenDisc T₂ ∧ Disjoint T₁ T₂ ∧
      s \ (range (ℓ (e, true)) ∪ range (ℓ (e, false))) = T₁ ∪ T₂ ∧ (T₁ ∩ e).Nonempty ∧
      (T₂ ∩ e).Nonempty := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨s, hs, hes, hs'⟩ := hL.exists_region hS hmax hE he
  have hsd : IsOpenDisc s := radial_region_isOpenDisc hrad hS hmax hs
  have hT := hL.isLine he true
  have hF := hL.isLine he false
  have hne : ((e, true) : Set S × Bool) ≠ (e, false) := by simp
  set C := range (ℓ (e, true)) ∪ range (ℓ (e, false)) with hC
  have hhs : ∀ b, h (e, b) ∉ s := fun b h' => region_subset hs h' (hL.hub_K he b)
  have hCs : ∀ z ∈ C, z ≠ h (e, true) → z ≠ h (e, false) → z ∈ s := by
    intro z hz hz₁ hz₂
    rw [hs']
    rcases hz with hz | hz
    · rcases hL.mem_line he true hz with h₁ | h₁ | h₁
      · exact Or.inl (Or.inl h₁)
      · exact Or.inr (h₁ ▸ hL.m_mem he)
      · exact absurd h₁ hz₁
    · rcases hL.mem_line he false hz with h₁ | h₁ | h₁
      · exact Or.inl (Or.inr h₁)
      · exact Or.inr (h₁ ▸ hL.m_mem he)
      · exact absurd h₁ hz₂
  -- A parametrization of the two lines, with its ends off `s`.
  obtain ⟨a, hac, hai, ha0, ha1, har, hin⟩ : ∃ a : I → S, Continuous a ∧ InjOn a (Ioo 0 1)
    ∧ a 0 ∉ s ∧
      a 1 ∉ s ∧ range a = C ∧ ∀ t, t ≠ 0 → t ≠ 1 → a t ∈ s := by
    by_cases hh : h (e, true) = h (e, false)
    · have hO : IsOArc C := by
        rw [hh] at hT
        refine isOArc_union hT hF fun z hz => ?_
        rcases hL.line_meet he he hne hz.1 hz.2 with h₁ | h₁
        · exact Or.inl h₁
        · exact Or.inr (hh ▸ h₁)
      obtain ⟨a, hac, hai, ha0, ha1, har, hane⟩ := exists_oArc_loop hO (a₀ := h (e, false))
        (Or.inr (line_right_mem hF))
      refine ⟨a, hac, hai, ha0 ▸ hhs false, ha1 ▸ hhs false, har, fun t h₁ h₂ => ?_⟩
      exact hCs _ (har ▸ ⟨t, rfl⟩) (hh ▸ hane t h₁ h₂) (hane t h₁ h₂)
    · have hcap : range (ℓ (e, true)) ∩ range (ℓ (e, false)) = {m e} := by
        apply subset_antisymm
        · rintro z ⟨h₁, h₂⟩
          rcases hL.line_meet he he hne h₁ h₂ with h₃ | h₃
          · exact h₃
          · exfalso
            rcases hL.mem_line he false h₂ with h₄ | h₄ | h₄
            · exact (hL.face_off he false h₄).2 (h₃ ▸ hL.hub_K he true)
            · exact hL.hub_ne_m he he true (h₃.symm.trans h₄)
            · exact hh (h₃.symm.trans h₄)
        · rintro z rfl
          exact ⟨line_left_mem hT, line_left_mem hF⟩
      obtain ⟨φ, h₀, h₁⟩ := IsLineWithEnds.union hT hF hcap
      have hinj : Function.Injective fun t : I => (φ t).1 :=
        fun t t' h' => φ.injective (Subtype.ext h')
      refine ⟨fun t => (φ t).1, by fun_prop, hinj.injOn, by
        change (φ 0).1 ∉ s
        rw [h₀]
        exact hhs true, by
        change (φ 1).1 ∉ s
        rw [h₁]
        exact hhs false, ?_, fun t h₂ h₃ => ?_⟩
      · ext z
        constructor
        · rintro ⟨t, rfl⟩
          exact (φ t).2
        · intro hz
          obtain ⟨t, ht⟩ := φ.surjective ⟨z, hz⟩
          exact ⟨t, congrArg Subtype.val ht⟩
      · refine hCs _ (φ t).2 ?_ ?_
        · exact fun h' => h₂ (hinj (h'.trans h₀.symm))
        · exact fun h' => h₃ (hinj (h'.trans h₁.symm))
  obtain ⟨T₁, T₂, hT₁, hT₂, hT₁₂, hcov, hcl₁, hcl₂⟩ := exists_crosscut_sides hS hsd hac hai ha0 ha1
    hin
  rw [har] at hcov hcl₁ hcl₂
  have hfaces : ∀ b, IsOpen (f (e, b)) := fun b => region_isOpen (hL.face e he b).1
  have hfdis : Disjoint (f (e, true)) (f (e, false)) := disjoint_left.mpr fun z h₁ h₂ =>
    hL.face_ne e he (region_eq_of_mem (hL.face e he true).1 (hL.face e he false).1 h₁ h₂)
  obtain ⟨t₀, ht₀, ht₁⟩ := exists_mid
  have hmeet : ∀ T : Set S, IsOpenDisc T → T ⊆ s \ C → C ⊆ closure T → (T ∩ e).Nonempty := by
    intro T hT' hTs hCT
    by_contra hno
    have hTf : T ⊆ f (e, true) ∪ f (e, false) := by
      intro z hz
      have hzs := (hTs hz).1
      rw [hs'] at hzs
      rcases hzs with h₁ | h₁
      · exact h₁
      · exact absurd ⟨z, hz, h₁⟩ hno
    have hTc : IsPreconnected T := isPreconnected_of_isOpenDisc hT'
    have hTne : T.Nonempty := by
      by_contra hn
      have hn' : T = ∅ := not_nonempty_iff_eq_empty.mp hn
      have := hCT (Or.inl (line_right_mem hT))
      rw [hn'] at this
      simp at this
    obtain ⟨z, hz⟩ := hTne
    rcases hTf hz with h₁ | h₁
    · have hsubT : T ⊆ f (e, true) := hTc.subset_left_of_subset_union (hfaces true) (hfaces false)
        hfdis hTf ⟨z, hz, h₁⟩
      have hp := hL.inside e he false t₀ ht₀ ht₁
      obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp (hCT (Or.inr ⟨t₀, rfl⟩)) _ (hfaces false) hp
      exact disjoint_left.mp hfdis (hsubT hw₂) hw₁
    · have hsubT : T ⊆ f (e, false) := hTc.subset_right_of_subset_union (hfaces true) (hfaces false)
        hfdis hTf ⟨z, hz, h₁⟩
      have hp := hL.inside e he true t₀ ht₀ ht₁
      obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp (hCT (Or.inl ⟨t₀, rfl⟩)) _ (hfaces true) hp
      exact disjoint_left.mp hfdis hw₁ (hsubT hw₂)
  exact ⟨s, hs, T₁, T₂, hes, hs', hT₁, hT₂, hT₁₂, hcov, hmeet T₁ hT₁ (hcov ▸ subset_union_left)
    hcl₁,
    hmeet T₂ hT₂ (hcov ▸ subset_union_right) hcl₂⟩

/-- **The two lines at `m e` do not bound a disc that misses the rest of `e`.** Let `C` be the union
of
the two lines, when they end at the same hub. Each part of `exists_cut_region` has a point of `e`
outside `Δ`, and it misses `C`, so it misses `Δ`. Then all of `s \ C` misses `Δ`. But a point of `C`
in
the open set `s` is in the closure of the interior of `Δ`, which misses `C`. -/
theorem no_bigon_lines (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing Γ) K)
    (hE : Γ.E.Nonempty) {e : Set S} (he : e ∈ Γ.E) {Δ r : Set S}
    (hr : r ∈ Γ.R) (hΔ : IsClosedDisc Δ) (hsub : Δ ⊆ r ∪ {m e})
    (hb : discBd Δ = range (ℓ (e, true)) ∪ range (ℓ (e, false))) : False := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨s, hs, T₁, T₂, -, hs', hT₁, hT₂, -, hcov, hm₁, hm₂⟩ := hL.exists_cut_region hS hmax hE he
  have hsd : IsOpenDisc s := radial_region_isOpenDisc hrad hS hmax hs
  have hmC : m e ∈ range (ℓ (e, true)) ∪ range (ℓ (e, false)) :=
    Or.inl (line_left_mem (hL.isLine he true))
  obtain ⟨t₀, ht₀, ht₁⟩ := exists_mid
  have hmiss : ∀ T : Set S, IsOpenDisc T → T ⊆ s \ (range (ℓ (e, true)) ∪ range (ℓ (e, false))) →
      (T ∩ e).Nonempty → Disjoint T Δ := by
    rintro T hT' hTs ⟨u, huT, hue⟩
    refine disjoint_disc_of_outside hman hΔ (isPreconnected_of_isOpenDisc hT') ?_ huT fun hu => ?_
    · rw [hb]
      exact disjoint_left.mpr fun z hz h' => (hTs hz).2 h'
    · rcases hsub hu with h₁ | h₁
      · exact region_subset hr h₁ (Γ.closure_subset_U he (subset_closure hue))
      · exact (hTs huT).2 (h₁ ▸ hmC)
  have hd₁ := hmiss T₁ hT₁ (hcov ▸ subset_union_left) hm₁
  have hd₂ := hmiss T₂ hT₂ (hcov ▸ subset_union_right) hm₂
  have hpt : ℓ (e, true) t₀ ∈ s := by
    rw [hs']
    exact Or.inl (Or.inl (hL.inside e he true t₀ ht₀ ht₁))
  have hpΔ : ℓ (e, true) t₀ ∈ Δ := by
    refine GraphMinor.Surface.discBd_subset Δ ?_
    rw [hb]
    exact Or.inl ⟨t₀, rfl⟩
  obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp (hΔ.subset_closure_discInt hpΔ) s hsd.1 hpt
  have hw : w ∈ s \ (range (ℓ (e, true)) ∪ range (ℓ (e, false))) := ⟨hw₁, fun h' => hw₂.2 (hb ▸ h')⟩
  rw [hcov] at hw
  rcases hw with h₁ | h₁
  · exact disjoint_left.mp hd₁ h₁ hw₂.1
  · exact disjoint_left.mp hd₂ h₁ hw₂.1

variable {N : Drawing S}
  (hNU : N.U = ((K.V \ Γ.V) ∪ m '' Γ.E) ∪ ⋃ i ∈ Γ.E ×ˢ (univ : Set Bool), range (ℓ i))
  (hNV : N.V = (K.V \ Γ.V) ∪ m '' Γ.E)
  (hNE : N.E = (fun i => range (ℓ i) \ {m i.1, h i}) '' (Γ.E ×ˢ (univ : Set Bool)))

include hNU in
omit [T2Space S] [ConnectedSpace S] in
/-- A point of `N` is a hub, a point `m e`, or a point of a face. -/
theorem mem_N {z : S} (hz : z ∈ N.U) :
    (z ∈ K.V ∧ z ∉ Γ.V) ∨ (∃ e ∈ Γ.E, z = m e) ∨ ∃ e ∈ Γ.E, ∃ b, z ∈ f (e, b) := by
  rw [hNU] at hz
  rcases hz with (hz | ⟨e, he, rfl⟩) | hz
  · exact Or.inl hz
  · exact Or.inr (Or.inl ⟨e, he, rfl⟩)
  · obtain ⟨⟨e, b⟩, ⟨he, -⟩, hzl⟩ := mem_iUnion₂.mp hz
    rcases hL.mem_line he b hzl with h₁ | h₁ | h₁
    · exact Or.inr (Or.inr ⟨e, he, b, h₁⟩)
    · exact Or.inr (Or.inl ⟨e, he, h₁⟩)
    · exact Or.inl ⟨h₁ ▸ hL.hub_V he b, fun h' => hL.hub_off he b (h₁ ▸ Γ.V_subset_U h')⟩

include hNU hNV in
omit [T2Space S] [ConnectedSpace S] in
theorem glue_compat : K.U ∩ N.U ⊆ K.V ∩ N.V := by
  rintro z ⟨h₁, h₂⟩
  rcases hL.mem_N hNU h₂ with hz | ⟨e, he, rfl⟩ | ⟨e, he, b, hz⟩
  · exact ⟨hz.1, hNV ▸ Or.inl hz⟩
  · exact absurd h₁ (hL.m_K he)
  · exact absurd h₁ (hL.face_off he b hz).2

omit [T2Space S] [ConnectedSpace S] in
theorem R_eq : D.R = Γ.R := by
  simp only [Drawing.R, hL.U_eq]

include hNE in
omit [ConnectedSpace S] in
/-- The closure of an edge of `N` is a line. -/
theorem N_edge {g : Set S} (hg : g ∈ N.E) :
    ∃ e ∈ Γ.E, ∃ b, g = range (ℓ (e, b)) \ {m e, h (e, b)} ∧ closure g = range (ℓ (e, b)) := by
  rw [hNE] at hg
  obtain ⟨⟨e, b⟩, ⟨he, -⟩, rfl⟩ := hg
  exact ⟨e, he, b, rfl, closure_sdiff_pair (hL.isLine he b)⟩

variable (hKN : K.U ∩ N.U ⊆ K.V ∩ N.V)

include hNU hNV in
omit [T2Space S] [ConnectedSpace S] hL hNU hNV in
theorem cap_spoke {g : Set S} (hg : g ∈ K.E) :
    closure g ∩ (K.glue N hKN).V = closure g ∩ K.V := by
  ext z
  refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, Or.inl hz.2⟩⟩
  rcases hz.2 with h₁ | h₁
  · exact h₁
  · exact (hKN ⟨K.closure_subset_U hg hz.1, N.V_subset_U h₁⟩).1

include hNU hNV in
omit hNU in
omit [ConnectedSpace S] in
theorem cap_line {e : Set S} (he : e ∈ Γ.E) (b : Bool) :
    range (ℓ (e, b)) ∩ (K.glue N hKN).V = {m e, h (e, b)} := by
  apply subset_antisymm
  · rintro z ⟨hz, hzV⟩
    rcases hL.mem_line he b hz with h₁ | h₁ | h₁
    · exfalso
      rcases hzV with hzV | hzV
      · exact (hL.face_off he b h₁).2 (K.V_subset_U hzV)
      · rw [hNV] at hzV
        rcases hzV with hzV | ⟨e', he', rfl⟩
        · exact (hL.face_off he b h₁).2 (K.V_subset_U hzV.1)
        · exact (hL.face_off he b h₁).1 (hL.m_U he')
    · exact Or.inl h₁
    · exact Or.inr h₁
  · rintro z (rfl | rfl)
    · exact ⟨line_left_mem (hL.isLine he b), Or.inr (hNV ▸ Or.inr ⟨e, he, rfl⟩)⟩
    · exact ⟨line_right_mem (hL.isLine he b), Or.inl (hL.hub_V he b)⟩

omit [T2Space S] [ConnectedSpace S] in
theorem hub_notMem_D {e : Set S} (he : e ∈ Γ.E) (b : Bool) : h (e, b) ∉ D.V := by
  intro h'
  rw [hL.V_eq] at h'
  rcases h' with h' | ⟨e', he', h'⟩
  · exact hL.hub_off he b (Γ.V_subset_U h')
  · exact hL.hub_ne_m he he' b h'.symm

omit [T2Space S] [ConnectedSpace S] in
theorem m_mem_D {e : Set S} (he : e ∈ Γ.E) : m e ∈ D.V := hL.V_eq ▸ Or.inr ⟨e, he, rfl⟩

include hNU hNV hNE in
/-- Conditions (i)-(iv) for `D` and `K ∪ N`. -/
theorem preRad_glue (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing Γ) K)
    (hE : Γ.E.Nonempty) : PreRad (PaintingOrDrawing.drawing D) (K.glue N hKN) := by
  have hR := hL.R_eq
  have hRm : ∀ {r}, r ∈ D.R → r ∈ Γ.R := fun h' => hR ▸ h'
  have hRm' : ∀ {r}, r ∈ Γ.R → r ∈ D.R := fun h' => hR.symm ▸ h'
  have hVm : ∀ {z}, z ∈ Γ.V → z ∈ D.V := fun h' => hL.V_eq.symm ▸ Or.inl h'
  refine ⟨⟨inferInstance, fun r hr => hrad.1.2 r (hRm hr)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change D.U ∩ (K.U ∪ N.U) = D.V
    rw [hL.U_eq, hL.V_eq]
    apply subset_antisymm
    · rintro z ⟨hz, hz' | hz'⟩
      · exact Or.inl (radial_inter hrad ▸ ⟨hz, hz'⟩)
      · rcases hL.mem_N hNU hz' with h₁ | ⟨e, he, rfl⟩ | ⟨e, he, b, h₁⟩
        · exact Or.inl (radial_inter hrad ▸ ⟨hz, K.V_subset_U h₁.1⟩)
        · exact Or.inr ⟨e, he, rfl⟩
        · exact absurd hz (hL.face_off he b h₁).1
    · rintro z (hz | ⟨e, he, rfl⟩)
      · exact ⟨Γ.V_subset_U hz, Or.inl (K.V_subset_U (radial_V hrad hz))⟩
      · exact ⟨hL.m_U he, Or.inr (N.V_subset_U (hNV ▸ Or.inr ⟨e, he, rfl⟩))⟩
  · change D.V ⊆ K.V ∪ N.V
    rw [hL.V_eq]
    rintro z (hz | ⟨e, he, rfl⟩)
    · exact Or.inl (radial_V hrad hz)
    · exact Or.inr (hNV ▸ Or.inr ⟨e, he, rfl⟩)
  · intro r hr
    have hr' : r ∈ Γ.R := hRm hr
    obtain ⟨w, ⟨hw, hwV⟩, huniq⟩ := hrad.2.2.2.1 r hr'
    refine ⟨w, ⟨hw, Or.inl hwV⟩, ?_⟩
    rintro z ⟨hz, hz' | hz'⟩
    · exact huniq z ⟨hz, hz'⟩
    · rw [hNV] at hz'
      rcases hz' with hz' | ⟨e, he, rfl⟩
      · exact huniq z ⟨hz, hz'.1⟩
      · exact absurd (hL.m_U he) (region_subset hr' hz)
  · rintro w ⟨hw, hwD⟩
    have hwΓ : w ∉ Γ.V := fun h' => hwD (hVm h')
    have hwK : w ∈ K.V := by
      rcases hw with hw | hw
      · exact hw
      · rw [hNV] at hw
        rcases hw with hw | ⟨e, he, rfl⟩
        · exact hw.1
        · exact absurd (hL.m_mem_D he) hwD
    obtain ⟨r, hr, hwr⟩ := hrad.2.2.2.2.1 w ⟨hwK, hwΓ⟩
    exact ⟨r, hRm' hr, hwr⟩
  · intro g hg
    rw [Drawing.glue_E] at hg
    rcases hg with hg | hg
    · obtain ⟨v, hv, w, hw, hcap⟩ := hrad.2.2.2.2.2.1 g hg
      have hw' : w ∉ D.V := fun h' => by
        rw [hL.V_eq] at h'
        rcases h' with h' | ⟨e, he, rfl⟩
        · exact hw.2 h'
        · exact hL.m_K he (K.V_subset_U hw.1)
      exact ⟨v, hVm hv, w, ⟨Or.inl hw.1, hw'⟩,
        (cap_spoke hKN hg).trans hcap⟩
    · obtain ⟨e, he, b, -, hcl⟩ := hL.N_edge hNE hg
      refine ⟨m e, hL.m_mem_D he, h (e, b), ⟨Or.inl (hL.hub_V he b), hL.hub_notMem_D he b⟩, ?_⟩
      rw [hcl]
      exact hL.cap_line hNV hKN he b
  · intro g hg g' hg' hne v hv r hr w ⟨hwr, hwV⟩ hc hc' ⟨Δ, hΔ, hsub, hb⟩
    have hr' : r ∈ Γ.R := hRm hr
    have hwK : w ∈ K.V := by
      rcases hwV with h₁ | h₁
      · exact h₁
      · rw [hNV] at h₁
        rcases h₁ with h₁ | ⟨e, he, rfl⟩
        · exact h₁.1
        · exact absurd (hL.m_U he) (region_subset hr' hwr)
    have hwU : w ∉ Γ.U := fun h' => region_subset hr' hwr h'
    -- An edge of `K ∪ N` with ends `v, w` that is a spoke has `v` in `K`.
    have hsp : ∀ {g}, g ∈ K.E → closure g ∩ (K.glue N hKN).V = {v, w} →
        closure g ∩ K.V = {v, w} ∧ v ∈ K.U := by
      intro g hg hc
      have h₁ := (cap_spoke hKN hg).symm.trans hc
      have h₂ : v ∈ closure g ∩ K.V := by rw [h₁]; simp
      exact ⟨h₁, K.closure_subset_U hg h₂.1⟩
    -- An edge of `N` with ends `v, w` is a line at `v`.
    have hln : ∀ {g}, g ∈ N.E → closure g ∩ (K.glue N hKN).V = {v, w} →
        ∃ e ∈ Γ.E, ∃ b, g = range (ℓ (e, b)) \ {m e, h (e, b)} ∧ closure g = range (ℓ (e, b)) ∧
          v = m e ∧ w = h (e, b) := by
      intro g hg hc
      obtain ⟨e, he, b, hge, hcl⟩ := hL.N_edge hNE hg
      have hcap := hL.cap_line hNV hKN he b
      rw [← hcl, hc] at hcap
      have h₁ : m e ∈ ({v, w} : Set S) := hcap ▸ Or.inl rfl
      have h₂ : h (e, b) ∈ ({v, w} : Set S) := hcap ▸ Or.inr rfl
      have hmw : m e = v := by
        rcases h₁ with h₁ | h₁
        · exact h₁
        · exact absurd (h₁ ▸ hL.m_U he) hwU
      have hhw : h (e, b) = w := by
        rcases h₂ with h₂ | h₂
        · exact absurd (h₂ ▸ hv) (hL.hub_notMem_D he b)
        · exact h₂
      exact ⟨e, he, b, hge, hcl, hmw.symm, hhw.symm⟩
    rw [Drawing.glue_E] at hg hg'
    have hdB : discBd Δ = closure g ∪ closure g' := by
      rw [← hb, subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hΔ]
    rcases hg with hg | hg <;> rcases hg' with hg' | hg'
    · obtain ⟨hc₁, hvK⟩ := hsp hg hc
      obtain ⟨hc₂, -⟩ := hsp hg' hc'
      have hvΓ : v ∈ Γ.V := by
        have hv' : v ∈ D.V := hv
        rw [hL.V_eq] at hv'
        rcases hv' with hv' | ⟨e, he, rfl⟩
        · exact hv'
        · exact absurd hvK (hL.m_K he)
      exact hrad.2.2.2.2.2.2 g hg g' hg' hne v hvΓ r hr' w ⟨hwr, hwK⟩ hc₁ hc₂ ⟨Δ, hΔ, hsub, hb⟩
    · obtain ⟨-, hvK⟩ := hsp hg hc
      obtain ⟨e, he, b, -, -, rfl, -⟩ := hln hg' hc'
      exact hL.m_K he hvK
    · obtain ⟨-, hvK⟩ := hsp hg' hc'
      obtain ⟨e, he, b, -, -, rfl, -⟩ := hln hg hc
      exact hL.m_K he hvK
    · obtain ⟨e, he, b, hge, hcl, hve, hwe⟩ := hln hg hc
      obtain ⟨e', he', b', hge', hcl', hve', hwe'⟩ := hln hg' hc'
      obtain rfl : e = e' := hL.m_inj he he' (hve.symm.trans hve')
      have hbb : b ≠ b' := fun h' => hne (by rw [hge, hge', h'])
      rw [hcl, hcl'] at hdB
      rw [hve] at hsub
      cases b <;> cases b'
      · exact hbb rfl
      · exact hL.no_bigon_lines hS hmax hE he hr' hΔ hsub (hdB.trans (union_comm _ _))
      · exact hL.no_bigon_lines hS hmax hE he hr' hΔ hsub hdB
      · exact hbb rfl

include hNE in
omit [T2Space S] [ConnectedSpace S] in
/-- `N` has at least two edges for each edge of `Γ`. -/
theorem two_mul_le_ncard_N : 2 * Γ.E.ncard ≤ N.E.ncard := by
  have hinj : InjOn (fun i : Set S × Bool => range (ℓ i) \ {m i.1, h i}) (Γ.E ×ˢ (univ : Set Bool))
    := by
    rintro ⟨e, b⟩ ⟨he, -⟩ ⟨e', b'⟩ ⟨he', -⟩ heq
    by_contra hne
    obtain ⟨t₀, h₀, h₁⟩ := exists_mid
    have hmem : ℓ (e, b) t₀ ∈ range (ℓ (e, b)) \ {m e, h (e, b)} := by
      refine ⟨⟨t₀, rfl⟩, ?_⟩
      have hin := hL.face_off he b (hL.inside e he b t₀ h₀ h₁)
      rintro (h₂ | h₂)
      · exact hin.1 (h₂ ▸ hL.m_U he)
      · exact hin.2 (h₂ ▸ hL.hub_K he b)
    have hmem' : ℓ (e, b) t₀ ∈ range (ℓ (e', b')) \ {m e', h (e', b')} := by
      have heq' : range (ℓ (e, b)) \ {m e, h (e, b)} = range (ℓ (e', b')) \ {m e', h (e', b')}
        := heq
      exact heq' ▸ hmem
    rcases hL.line_meet he he' hne hmem.1 hmem'.1 with h₂ | h₂
    · exact hmem.2 (Or.inl h₂)
    · exact hmem.2 (Or.inr h₂)
  rw [hNE, hinj.ncard_image, ncard_prod]
  simp [mul_comm]

include hNE in
omit [ConnectedSpace S] in
/-- An edge of `K` and an edge of `N` are different. -/
theorem disjoint_edges : Disjoint K.E N.E := by
  refine disjoint_left.mpr fun g hg hg' => ?_
  obtain ⟨e, he, b, rfl, -⟩ := hL.N_edge hNE hg'
  obtain ⟨t₀, h₀, h₁⟩ := exists_mid
  have hin := hL.face_off he b (hL.inside e he b t₀ h₀ h₁)
  refine hin.2 (K.closure_subset_U hg (subset_closure ⟨⟨t₀, rfl⟩, ?_⟩))
  rintro (h₂ | h₂)
  · exact hin.1 (h₂ ▸ hL.m_U he)
  · exact hin.2 (h₂ ▸ hL.hub_K he b)

omit [T2Space S] [ConnectedSpace S] in
/-- `D` has at most two edges for each edge of `Γ`. -/
theorem ncard_D_le : D.E.ncard ≤ 2 * Γ.E.ncard := by
  have hsub : D.E ⊆ (fun i : Set S × Bool => if i.2 then A i.1 else B i.1) '' (Γ.E ×ˢ
    (univ : Set Bool)) := by
    intro g hg
    obtain ⟨e, he, h' | h'⟩ := hL.all g hg
    · exact ⟨(e, true), ⟨he, mem_univ _⟩, by simp [h']⟩
    · exact ⟨(e, false), ⟨he, mem_univ _⟩, by simp [h']⟩
  have hfin := Γ.finite_edges.prod (finite_univ (α := Bool))
  have h₃ : (Γ.E ×ˢ (univ : Set Bool)).ncard = Γ.E.ncard * 2 := by
    rw [ncard_prod]
    simp
  exact (ncard_le_ncard hsub (hfin.image _)).trans ((ncard_image_le hfin).trans (h₃.le.trans
    (by omega)))

/-- Each vertex of `D` has an edge of `D`. -/
theorem D_all (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) :
    ∀ v ∈ D.V, ∃ g ∈ D.E, v ∈ closure g := by
  intro v hv
  rw [hL.V_eq] at hv
  rcases hv with hv | ⟨e, he, rfl⟩
  · obtain ⟨e, he, hve⟩ := exists_edge_at hrad hS hE hv
    obtain ⟨hA, hB, -, -, -, -, -, -, -, hcap, hcA, hcB⟩ := hL.split e he
    have hv' : v ∈ closure e ∩ Γ.V := ⟨hve, hv⟩
    rw [hcap] at hv'
    rcases hv' with rfl | rfl
    · have : x e ∈ closure (A e) ∩ D.V := by rw [hcA]; simp
      exact ⟨_, hA, this.1⟩
    · have : y e ∈ closure (B e) ∩ D.V := by rw [hcB]; simp
      exact ⟨_, hB, this.1⟩
  · obtain ⟨hA, -, -, -, -, -, -, -, -, -, hcA, -⟩ := hL.split e he
    have : m e ∈ closure (A e) ∩ D.V := by rw [hcA]; simp
    exact ⟨_, hA, this.1⟩

include hNU hNV hNE in
/-- Maximality for `D` and `K ∪ N`, by count. The edges of `K` number at least `2 |E(Γ)|`, and so do
the
edges of `N`. So `K ∪ N` has at least `4 |E(Γ)|`, which is at least `2 |E(D)|`. -/
theorem radMax_glue (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing Γ) K)
    (hE : Γ.E.Nonempty) : RadMax (PaintingOrDrawing.drawing D) (K.glue N hKN) := by
  have hpre := hL.preRad_glue hNU hNV hNE hKN hS hmax hE
  refine radMax_of_card hS hpre.1 hpre.2 (hL.D_all hS hE) ?_
  rw [Drawing.glue_E, ncard_union_eq (hL.disjoint_edges hNE) K.finite_edges N.finite_edges]
  have h₁ := two_mul_le_ncard_spokes hrad hS hmax hE
  have h₂ := hL.two_mul_le_ncard_N hNE
  have h₃ := hL.ncard_D_le
  omega

end IsDualLines

end GraphMinor.GM12
