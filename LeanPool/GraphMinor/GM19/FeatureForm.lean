/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureTile

/-!
# A word of a surface with given arcs on its cuffs

Let `Y` be a connected surface whose boundary is a union of arcs that meet only at their ends. The
classification gives `Y` the
word `ew a b c`, and each cuff is one free side of this word. We move each cuff along itself, so
that the free side runs through
the arcs of this cuff in their order around the cuff (`exists_form`). So `Y` with its arcs is
determined by `(a, b, c)` and the
list of arcs of each cuff (`homeo_of_form`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

/-- Arcs in the boundary of `Y` that cover it and meet only at their ends. -/
structure BoundaryArcs {Y : Type*} [TopologicalSpace Y] {J : Type*} (γ : J → ℝ → Y) : Prop where
  cont : ∀ s, ContinuousOn (γ s) (Icc 0 1)
  inj : ∀ s, InjOn (γ s) (Icc 0 1)
  bd : ∀ s, ∀ u ∈ Icc (0 : ℝ) 1, γ s u ∈ GraphMinor.Surface.bd Y
  disj : ∀ s s', ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, γ s u = γ s' v → s = s' ∧ u = v
  cover : ∀ y ∈ GraphMinor.Surface.bd Y, ∃ s, ∃ u ∈ Icc (0 : ℝ) 1, γ s u = y

/-- `f` is a word of `Y`, and the lists `L` say which arcs its free sides run through. -/
structure IsForm {Y : Type*} [TopologicalSpace Y] {J : Type*} (a b c : ℕ) (γ : J → ℝ → Y)
  (f : ℕ × ℂ → Y) (L : ℕ → List (J × Bool)) : Prop where
  pres : Presents (sW (ew a b c)) f
  side : ∀ i < c, ∀ (p : ℕ) (s : J) (e : Bool), (L i)[p]? = some (s, e) → ∀ u ∈ Icc
    (0 : ℝ) 1, holeP a b c f i (pos (L i).length p u) = γ s (ofs e u)
  all : ∀ s : J, ∃ i < c, ∃ (p : ℕ) (e : Bool), (L i)[p]? = some (s, e)

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] {J : Type*} {γ : J → ℝ
  → Y} {a b c : ℕ} {f : ℕ × ℂ → Y}

theorem lt_length_of_get {T : Type*} {l : List T} {p : ℕ} {x : T} (h : l[p]?
  = some x) : p < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

omit [T2Space Y] in
/-- An arc that has a point in a cuff lies in this cuff. -/
theorem arc_in_cuff (hγ : BoundaryArcs γ) {C : Set Y} (hC : C ∈ cuffs Y) {s : J} {u v : ℝ}
  (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (h : γ s u ∈ C) : γ s v ∈ C := by
  obtain ⟨y, hy, rfl⟩ := hC
  rw [connectedComponentIn_eq h]
  have hp : IsPreconnected (γ s '' Icc 0 1) := isPreconnected_Icc.image _ (hγ.cont s)
  have hsub : γ s '' Icc 0 1 ⊆ bd Y := by
    rintro _ ⟨w, hw, rfl⟩
    exact hγ.bd s w hw
  exact hp.subset_connectedComponentIn (mem_image_of_mem _ hu) hsub (mem_image_of_mem _ hv)

/-- **Moving the cuffs so that the free sides run through the arcs.** -/
theorem exists_form [Finite J] (hS : IsSurface Y) (e : Y ≃ₜ SurfaceModel a b c)
  (hγ : BoundaryArcs γ) :
    ∃ f L, IsForm a b c γ f L ∧ c ≤ Nat.card J ∧ ∀ i < c, (L i).length ≤ Nat.card J := by
  classical
  obtain ⟨-, f₀, hf₀⟩ := presents_ew a b c
  have hf : Presents (sW (ew a b c)) (e.symm ∘ f₀) := presents_comp hf₀ e.symm
  set f₁ := e.symm ∘ f₀ with hf₁
  have hcuff := cuffs_eq_holeC hf
  set C : ℕ → Set Y := holeC a b c f₁ with hCdef
  have hCc : ∀ {i}, i < c → C i ∈ cuffs Y := fun {i} hi ↦ by
    rw [hcuff]
    exact mem_image_of_mem _ hi
  have hloop := fun i (hi : i < c) ↦ hole_loop hf hi
  have hex : ∀ i, ∃ (L : List (J × Bool)) (m : ℕ → ℝ → ℝ), i < c → ∃ φ : Circle ≃ₜ
    (holeP a b c f₁ i '' Icc 0 1 : Set Y),
      (∀ u ∈ Icc (0 : ℝ) 1, (φ (ee u)).1 = holeP a b c f₁ i u) ∧
      0 < L.length ∧ L.length ≤ Nat.card J ∧ (∀ s, γ s 0 ∈ C i → ∃ p e, L[p]? = some (s, e)) ∧
        (∀ p s e, L[p]? = some (s, e) → γ s 0 ∈ C i) ∧
      (∀ p < L.length, ContinuousOn (m p) (Icc 0 1) ∧ StrictMonoOn (m p) (Icc 0 1)) ∧
      (∀ p s e, L[p]? = some (s, e) → ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m p u))).1 = γ s (ofs e u)) ∧
        (∀ p, p + 1 < L.length → m p 1 = m (p + 1) 0) ∧ m (L.length - 1) 1 = m 0 0 + 1 := fun i ↦ by
    by_cases hi : i < c
    · obtain ⟨h₁, h₂, h₃⟩ := hloop i hi
      obtain ⟨φ, hφ⟩ := exists_circle_param h₁ h₂ h₃
      let J' := {s : J // γ s 0 ∈ C i}
      have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
      have hin : ∀ s, γ s 0 ∈ C i → ∀ u ∈ Icc (0 : ℝ) 1, γ s u ∈ C i := fun s hs u hu ↦ arc_in_cuff
        hγ (hCc hi) h01 hu hs
      have hne : Nonempty J' := by
        obtain ⟨x, hx⟩ : (C i).Nonempty := ⟨_, 0, h01, rfl⟩
        have hbd : x ∈ bd Y := by
          rw [← sUnion_cuffs]
          exact ⟨_, hCc hi, hx⟩
        obtain ⟨s, u, hu, rfl⟩ := hγ.cover x hbd
        exact ⟨⟨s, arc_in_cuff hγ (hCc hi) hu h01 hx⟩⟩
      obtain ⟨k, sq, fl, m, hk, hsur, hinj, hm, hch, hlast⟩ := exists_cuff_order (J := J') (γ
        := fun s ↦ γ s.1) φ (fun s ↦ hγ.cont s.1) (fun s ↦ hγ.inj s.1)
        (fun s ↦ hin s.1 s.2) (fun s s' u hu v hv he ↦ by
          obtain ⟨h₄, h₅⟩ := hγ.disj s.1 s'.1 u hu v hv he
          exact ⟨Subtype.ext h₄, h₅⟩) (fun y hy ↦ by
          have hbd : y ∈ bd Y := by
            rw [← sUnion_cuffs]
            exact ⟨_, hCc hi, hy⟩
          obtain ⟨s, u, hu, rfl⟩ := hγ.cover y hbd
          exact ⟨⟨s, arc_in_cuff hγ (hCc hi) hu h01 hy⟩, u, hu, rfl⟩)
      have hget : ∀ p s e, ((List.range k).map fun p ↦ ((sq p).1, fl p))[p]? = some (s, e) → p < k
        ∧ (sq p).1 = s ∧ fl p = e := by
        intro p s e h
        rw [List.getElem?_map] at h
        by_cases hp : p < k
        · simp only [List.getElem?_range hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨hp, h⟩
        · rw [List.getElem?_eq_none (by simpa using hp)] at h
          simp at h
      refine ⟨(List.range k).map fun p ↦ ((sq p).1, fl p), m, fun _ ↦ ⟨φ, hφ, ?_, ?_, fun s hs ↦
        ?_, fun p s e h ↦ ?_, fun p hp ↦ ?_, fun p s e h u hu ↦ ?_, fun p hp ↦ ?_, ?_⟩⟩
      · simpa using hk
      · have h₄ : Injective fun p : Fin k ↦ (sq p).1 := fun p p' he ↦ Fin.ext (hinj p p.2 p' p'.2
        (Subtype.ext he))
        have h₅ := Nat.card_le_card_of_injective _ h₄
        simpa using h₅
      · obtain ⟨p, hp, hq⟩ := hsur ⟨s, hs⟩
        refine ⟨p, fl p, ?_⟩
        rw [List.getElem?_map, List.getElem?_range hp, Option.map_some, hq]
      · obtain ⟨-, rfl, -⟩ := hget p s e h
        exact (sq p).2
      · exact ⟨(hm p (by simpa using hp)).1, (hm p (by simpa using hp)).2.1⟩
      · obtain ⟨hp, rfl, rfl⟩ := hget p s e h
        exact (hm p hp).2.2 u hu
      · exact hch p (by simpa using hp)
      · simpa using hlast
    · exact ⟨[], fun _ _ ↦ 0, fun h ↦ absurd h hi⟩
  choose L m hex using hex
  choose φ hφ hL₀ hLc hL₁ hL₂ hm₁ hm₂ hm₃ hm₄ using hex
  set τ : ℕ → ℝ → ℝ := fun i ↦ cc (L i).length (m i) with hτ
  have hτc : ∀ i (hi : i < c), ContinuousOn (τ i) (Icc 0 1) ∧ StrictMonoOn (τ i) (Icc 0 1) ∧ τ i 1
    = τ i 0 + 1 := fun i hi ↦ by
    refine ⟨continuousOn_cc _ _ (hm₃ i hi) (fun p hp ↦ (hm₁ i hi p hp).1) (hL₀ i hi),
      strictMonoOn_cc _ _ (hm₃ i hi) (fun p hp ↦ (hm₁ i hi p hp).2) (hL₀ i hi), ?_⟩
    rw [hτ]
    simp only
    rw [cc_one _ _ (hm₃ i hi), cc_zero, hm₄ i hi]
  have hclosed : ∀ i, i < c → IsClosed (C i) := fun i _ ↦ (isCompact_Icc.image_of_continuousOn
    (continuousOn_hole hf i)).isClosed
  have hstep : ∀ n ≤ c, ∃ g : ℕ × ℂ → Y, Presents (sW (ew a b c)) g ∧ (∀ i (hi : i < c), i < n
    → ∀ u ∈ Icc (0 : ℝ) 1, holeP a b c g i u = (φ i hi (ee (τ i u))).1) ∧
      ∀ i, i < c → n ≤ i → ∀ u ∈ Icc (0 : ℝ) 1, holeP a b c g i u = holeP a b c f₁ i u := by
    intro n
    induction n with
    | zero => exact fun _ ↦ ⟨f₁, hf, fun i _ h ↦ absurd h (Nat.not_lt_zero i), fun _ _ _ _ _ ↦ rfl⟩
    | succ n ih =>
      intro hn
      obtain ⟨g, hg, h₁, h₂⟩ := ih (by omega)
      have hnc : n < c := hn
      let U : Set Y := (⋃ i ∈ {i | i < c ∧ i ≠ n}, C i)ᶜ
      have hU : IsOpen U := by
        refine isOpen_compl_iff.mpr ?_
        have hfinite : {i | i < c ∧ i ≠ n}.Finite :=
          (Set.finite_lt_nat c).subset fun _ hi => hi.1
        exact hfinite.isClosed_biUnion fun i hi => hclosed i hi.1
      have hCU : C n ⊆ U := by
        intro x hx hx'
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx'
        exact Set.disjoint_left.mp (disjoint_holeC hf hnc hi.1 hi.2.symm) hx hxi
      obtain ⟨hc₁, hc₂, hc₃⟩ := hτc n hnc
      obtain ⟨α, hα₁, hα₂⟩ := exists_move_loop hS (hCc hnc) hU hCU (φ n hnc) hc₁ hc₂ hc₃
      have hfix : ∀ i (hi : i < c), i ≠ n → ∀ x ∈ C i, α x = x := fun i hi hne x hx ↦ hα₂ x fun hxU
        ↦ hxU (mem_iUnion₂.mpr ⟨i, ⟨hi, hne⟩, hx⟩)
      refine ⟨α ∘ g, presents_comp hg α, fun i hi hin u hu ↦ ?_, fun i hi hin u hu ↦ ?_⟩
      · change α (holeP a b c g i u) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hin with h₃ | rfl
        · rw [h₁ i hi h₃ u hu]
          exact hfix i hi (by omega) _ (φ i hi _).2
        · rw [h₂ i hi le_rfl u hu, ← hφ i hi u hu]
          exact hα₁ u hu
      · change α (holeP a b c g i u) = _
        rw [h₂ i hi (by omega) u hu]
        exact hfix i hi (by omega) _ ⟨u, hu, rfl⟩
  obtain ⟨g, hg, h₁, -⟩ := hstep c le_rfl
  refine ⟨g, L, ⟨hg, fun i hi p s e' h u hu ↦ ?_, fun s ↦ ?_⟩, ?_, hLc⟩
  · have hp : p < (L i).length := lt_length_of_get h
    rw [h₁ i hi hi _ (pos_mem _ _ hu)]
    simp only [hτ]
    rw [cc_pos _ _ (hm₃ i hi) p hp u hu]
    exact hm₂ i hi p s e' h u hu
  · have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have hb := hγ.bd s 0 h01
    rw [← sUnion_cuffs, hcuff] at hb
    obtain ⟨_, ⟨i, hi, rfl⟩, hs⟩ := hb
    obtain ⟨p, e', h⟩ := hL₁ i hi s hs
    exact ⟨i, hi, p, e', h⟩
  · have hpick : ∀ i : Fin c, ∃ s : J, γ s 0 ∈ C i.1 := fun i ↦ by
      obtain ⟨l, t, ht⟩ := List.exists_cons_of_length_pos (hL₀ i.1 i.2)
      have h₃ : (L i.1)[0]? = some (l.1, l.2) := by simp [ht]
      exact ⟨l.1, hL₂ i.1 i.2 0 _ _ h₃⟩
    choose t ht using hpick
    have hinj : Injective t := fun i j he ↦ by
      by_contra hne
      have h₃ := ht i
      rw [he] at h₃
      exact Set.disjoint_left.mp (disjoint_holeC hf i.2 j.2 fun h ↦ hne (Fin.ext h)) h₃ (ht j)
    have h₃ := Nat.card_le_card_of_injective _ hinj
    simpa using h₃

/-- Two surfaces with the same form are homeomorphic, by a map that keeps the arcs. -/
theorem homeo_of_form {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] {γ' : J → ℝ → Y'} {f' : ℕ × ℂ
  → Y'} {L : ℕ → List (J × Bool)} (h : IsForm a b c γ f L) (h' : IsForm a b c γ' f' L) :
    ∃ e : Y ≃ₜ Y', ∀ s, ∀ u ∈ Icc (0 : ℝ) 1, e (γ s u) = γ' s u := by
  obtain ⟨e, he⟩ := presents_homeo (finW_sW _) h.pres h'.pres
  refine ⟨e, fun s v hv ↦ ?_⟩
  obtain ⟨i, hi, p, b', hg⟩ := h.all s
  have hu := ofs_mem (e := b') hv
  have h₁ := h.side i hi p s b' hg _ hu
  have h₂ := h'.side i hi p s b' hg _ hu
  rw [ofs_ofs] at h₁ h₂
  rw [← h₁, ← h₂]
  refine he _ ?_
  exact ⟨(ew_mem_dsk a b c).1, (norm_per _ _).le⟩

end GraphMinor.GM19
