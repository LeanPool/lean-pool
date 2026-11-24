/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutWord
public import LeanPool.GraphMinor.Surface.CutLift
public import LeanPool.GraphMinor.Surface.NormalWord
public import LeanPool.GraphMinor.Surface.CohPrim

/-!
# Cutting along edges of a dissection

Let `W` be the word of a dissection, and cut it along the labels of a set `D` of edges. This file
studies the resulting
space near the edges in `D`. The main results are `vertex_cut`, which tells what happens at an end
of an edge in `D`, and
`exists_cut_space`, which gives the cut surface with two lifts of each edge in `D`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

/-- `W` and `f` come from a dissection with the graph `V, E`: each side runs along the edge named by
its label. -/
structure WordEdges {S : Type u} [TopologicalSpace S] (W : ℕ → List Letter) (f : ℕ × ℂ → S)
  (V : Set S) (E : Set (Set S))
    (A : Set S → 𝕀 → S) (lab : Set S → ℕ) : Prop where
  fin : FinW W
  paired : IsPaired W
  pres : Presents W f
  graph : IsGraph V E
  arc : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1}
  lab_inj : InjOn lab E
  side : ∀ i p k e', (W i)[p]? = some (k, e') → ∃ e ∈ E, lab e = k ∧ ∀ u ∈ Icc (0 : ℝ) 1,
    f (spt W i p u) = extI (A e) (ofs e' u)
  circ : ∀ a ∈ Dsk W, f a ∈ ⋃₀ E → ‖a.2‖ = 1

variable {S : Type u} [TopologicalSpace S] [T2Space S] {W : ℕ → List Letter} {f : ℕ × ℂ
  → S} {V : Set S} {E : Set (Set S)}
  {A : Set S → 𝕀 → S} {lab : Set S → ℕ}

/-- The middle of an edge. -/
noncomputable def edgeMid (A : Set S → 𝕀 → S) (e : Set S) : S := extI (A e) (1 / 2)

theorem spe_mem (g : SE W) : spe W g ∈ Dsk W := by
  obtain ⟨⟨i, p, b⟩, h⟩ := g
  replace h : p < (W i).length := h
  have h1 : W i ≠ [] := fun he => by
    rw [he] at h
    simp at h
  exact ⟨h1, by simp [spe, spt, norm_per]⟩

theorem spt_mem {i p : ℕ} (h : p < (W i).length) (u : ℝ) : spt W i p u ∈ Dsk W :=
  ⟨fun he => by
    replace he : W i = [] := he
    rw [he] at h
    simp at h, by simp [spt, norm_per]⟩

namespace WordEdges

variable (h : WordEdges W f V E A lab)

include h

omit [T2Space S] in
theorem extI_mem {e : Set S} (he : e ∈ E) (t : ℝ) : extI (A e) t ∈ e :=
  (h.arc e he).2.1.subset ⟨_, rfl⟩

omit [T2Space S] in
theorem extI_notMem {e : Set S} (he : e ∈ E) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : extI (A e) t ∉ V
  := by
  intro hV
  have h1 : extI (A e) t ∈ e ∩ V := ⟨h.extI_mem he t, hV⟩
  rw [(h.arc e he).2.2] at h1
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hinj := extI_injOn (h.arc e he).1.2
  rcases h1 with h1 | h1
  · have h2 : extI (A e) t = extI (A e) 0 := h1.trans (extI_coe (A e) 0).symm
    exact ht.1.ne' (hinj ht' ⟨le_rfl, zero_le_one⟩ h2)
  · have h2 : extI (A e) t = extI (A e) 1 := h1.trans (extI_coe (A e) 1).symm
    exact ht.2.ne (hinj ht' ⟨zero_le_one, le_rfl⟩ h2)

omit [T2Space S] in
theorem extI_mem_V {e : Set S} (he : e ∈ E) (b : Bool) : extI (A e) (eo b) ∈ V := by
  have h1 : A e 0 ∈ e ∩ V := (h.arc e he).2.2 ▸ mem_insert _ _
  have h2 : A e 1 ∈ e ∩ V := (h.arc e he).2.2 ▸ mem_insert_of_mem _ rfl
  cases b
  · have : extI (A e) (eo false) = A e 0 := by
      simpa [eo] using extI_coe (A e) 0
    rw [this]
    exact h1.2
  · have : extI (A e) (eo true) = A e 1 := by
      simpa [eo] using extI_coe (A e) 1
    rw [this]
    exact h2.2

omit [T2Space S] in
theorem corner_of_side {i p k : ℕ} {e' : Bool} (h1 : (W i)[p]? = some (k, e')) {u : ℝ}
  (hu : u ∈ Icc (0 : ℝ) 1)
    (hV : f (spt W i p u) ∈ V) : ∃ b, eo b = u := by
  obtain ⟨e, he, -, h3⟩ := h.side _ _ _ _ h1
  by_contra hc
  push Not at hc
  have h4 : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (fun h0 => hc false (by simp [eo, h0])),
    lt_of_le_of_ne hu.2 (fun h0 => hc true (by simp [eo, h0]))⟩
  have h5 : ofs e' u ∈ Ioo (0 : ℝ) 1 := by
    cases e' <;> simp only [ofs, Bool.false_eq_true, ite_true, ite_false]
    · exact ⟨by linarith [h4.2], by linarith [h4.1]⟩
    · exact h4
  rw [h3 u hu] at hV
  exact h.extI_notMem he h5 hV

omit [T2Space S] in
theorem eo_inj {e : Set S} (he : e ∈ E) {a b : Bool} (he' : extI (A e) (eo a) = extI (A e)
  (eo b)) : a = b := by
  have h1 := extI_injOn (h.arc e he).1.2 (eo_mem a) (eo_mem b) he'
  cases a <;> cases b <;> simp [eo] at h1 ⊢

omit [T2Space S] in
/-- A point of the discs on an edge is on a side along an edge. -/
theorem exists_side {a : ℕ × ℂ} (ha : a ∈ Dsk W) (hE : f a ∈ ⋃₀ E) :
    ∃ p e', ∃ e ∈ E, ∃ u ∈ Icc (0 : ℝ) 1, (W a.1)[p]? = some (lab e, e') ∧ a = spt W a.1 p u ∧
      f a = extI (A e) (ofs e' u) := by
  obtain ⟨p, k, e', u, hu, h1, h2⟩ := exists_spt ha (h.circ a ha hE)
  obtain ⟨e, he, rfl, h3⟩ := h.side _ p k e' h1
  refine ⟨p, e', e, he, u, hu, h1, h2, ?_⟩
  rw [← h3 u hu, ← h2]

omit [T2Space S] in
theorem corner_of {a : ℕ × ℂ} (ha : a ∈ Dsk W) (hE : f a ∈ ⋃₀ E) (hV : f a ∈ V) : ∃ g : SE W, spe W
  g = a := by
  classical
  obtain ⟨p, e', e, he, u, hu, h1, h2, h3⟩ := h.exists_side ha hE
  have hend : u = 0 ∨ u = 1 := by
    by_contra hc
    push Not at hc
    have h4 : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hc.1), lt_of_le_of_ne hu.2 hc.2⟩
    have h5 : ofs e' u ∈ Ioo (0 : ℝ) 1 := by
      cases e' <;> simp only [ofs, Bool.false_eq_true, ite_true, ite_false]
      · exact ⟨by linarith [h4.2], by linarith [h4.1]⟩
      · exact h4
    exact h.extI_notMem he h5 (h3 ▸ hV)
  refine ⟨⟨(a.1, p, decide (u = 1)), lt_length h1⟩, ?_⟩
  have hx : eo (decide (u = 1)) = u := by
    rcases hend with rfl | rfl <;> simp [eo]
  simp only [spe, hx]
  exact h2.symm

theorem bd_eq : bd S = f '' freePts W := (surface_of_presents h.fin h.paired h.pres).2

/-- An edge with the middle off the boundary is on two sides. -/
theorem exists_sides {e : Set S} (he : e ∈ E) (hb : edgeMid A e ∉ bd S) : ∃ (i p j q : ℕ)
  (e₁ e₂ : Bool),
    (W i)[p]? = some (lab e, e₁) ∧ (W j)[q]? = some (lab e, e₂) ∧ (i, p) ≠ (j, q) := by
  obtain ⟨a, ha, hfa⟩ : edgeMid A e ∈ f '' Dsk W := h.pres.2.1 ▸ mem_univ _
  have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hE : f a ∈ ⋃₀ E := ⟨e, he, hfa ▸ h.extI_mem he _⟩
  obtain ⟨p, e', e'', he'', u, hu, h1, h2, h3⟩ := h.exists_side ha hE
  have hee : e'' = e := by
    by_contra hc
    have h4 : edgeMid A e ∈ V := h.graph.disj e'' he'' e he hc
      ⟨by rw [← hfa, h3]; exact h.extI_mem he'' _, h.extI_mem he _⟩
    exact h.extI_notMem he hmid h4
  subst hee
  by_contra hcon
  push Not at hcon
  have hfree : FreeSide W a.1 p := by
    intro j q k e₁ e₂ h4 h5
    have hk : (k, e₁) = (lab e'', e') := by
      rw [h1] at h4
      exact (Option.some.inj h4).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
    by_contra hne
    exact hne (hcon a.1 p j q _ _ h1 h5)
  refine hb ?_
  rw [h.bd_eq]
  exact ⟨a, ⟨a.1, p, u, lt_length h1, hfree, hu, h2⟩, hfa⟩

end WordEdges

/-- The end of a side in the direction of its letter. -/
def xn (e τ : Bool) : Bool := if e then τ else !τ

theorem eo_xn (e τ : Bool) : eo (xn e τ) = ofs e (eo τ) := by
  cases e <;> cases τ <;> simp [xn, eo, ofs]

theorem xn_xn (e τ : Bool) : xn e (xn e τ) = τ := by
  cases e <;> cases τ <;> rfl

/-- The two sides along an edge. -/
structure EdgeSides (W : ℕ → List Letter) (k : ℕ) (i p j q : ℕ) (e₁ e₂ : Bool) : Prop where
  one : (W i)[p]? = some (k, e₁)
  two : (W j)[q]? = some (k, e₂)
  ne : (i, p) ≠ (j, q)

variable {k i p j q : ℕ} {e₁ e₂ : Bool}

/-- The end of the first side at the end `τ` of the edge. -/
def EdgeSides.end₁ (s : EdgeSides W k i p j q e₁ e₂) (τ : Bool) : SE W
  := ⟨(i, p, xn e₁ τ), lt_length s.one⟩

/-- The end of the second side at the end `τ` of the edge. -/
def EdgeSides.end₂ (s : EdgeSides W k i p j q e₁ e₂) (τ : Bool) : SE W
  := ⟨(j, q, xn e₂ τ), lt_length s.two⟩

theorem EdgeSides.mate {L : Set ℕ} (s : EdgeSides W k i p j q e₁ e₂) (hk : k ∉ L) (τ : Bool) :
    MateL W L (s.end₁ τ) (s.end₂ τ) := by
  refine ⟨k, e₁, e₂, s.one, s.two, s.ne, hk, ?_⟩
  cases e₁ <;> cases e₂ <;> cases τ <;> rfl

theorem EdgeSides.mem (s : EdgeSides W k i p j q e₁ e₂) (hP : IsPaired W) (g : SE W) {e : Bool}
    (hg : (W g.1.1)[g.1.2.1]? = some (k, e)) : ∃ τ, g = s.end₁ τ ∨ g = s.end₂ τ := by
  obtain ⟨⟨i', p', b⟩, hb⟩ := g
  simp only at hg
  rcases hP.third s.one s.two hg s.ne with h1 | h1
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    have he : e = e₁ := by
      rw [s.one] at hg
      simpa using hg.symm
    subst he
    refine ⟨xn e b, .inl ?_⟩
    apply Subtype.ext
    simp [EdgeSides.end₁, xn_xn]
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    have he : e = e₂ := by
      rw [s.two] at hg
      simpa using hg.symm
    subst he
    refine ⟨xn e b, .inr ?_⟩
    apply Subtype.ext
    simp [EdgeSides.end₂, xn_xn]

omit [T2Space S] in
/-- The sides of the edges in `D`. -/
theorem WordEdges.f_end₁ (h : WordEdges W f V E A lab) {e : Set S} (he : e ∈ E)
    (s : EdgeSides W (lab e) i p j q e₁ e₂) (τ : Bool) : f (spe W (s.end₁ τ)) = extI (A e) (eo τ)
      := by
  obtain ⟨e', he', hl, h1⟩ := h.side _ _ _ _ s.one
  obtain rfl := h.lab_inj he' he hl
  have h2 := h1 (ofs e₁ (eo τ)) (ofs_mem (eo_mem τ))
  rw [ofs_ofs] at h2
  simp only [spe, EdgeSides.end₁, eo_xn]
  exact h2

omit [T2Space S] in
theorem WordEdges.f_end₂ (h : WordEdges W f V E A lab) {e : Set S} (he : e ∈ E)
    (s : EdgeSides W (lab e) i p j q e₁ e₂) (τ : Bool) : f (spe W (s.end₂ τ)) = extI (A e) (eo τ)
      := by
  obtain ⟨e', he', hl, h1⟩ := h.side _ _ _ _ s.two
  obtain rfl := h.lab_inj he' he hl
  have h2 := h1 (ofs e₂ (eo τ)) (ofs_mem (eo_mem τ))
  rw [ofs_ofs] at h2
  simp only [spe, EdgeSides.end₂, eo_xn]
  exact h2

/-- What happens at an end of an edge in `D`, when we cut along the labels `L` of `D`. There are two
cases. Either exactly
one other end of an edge in `D` lies at the same point, off the boundary, or no other end does and
the point is on
the boundary. -/
theorem WordEdges.vertex_cut (h : WordEdges W f V E A lab) {D : Set (Set S)}
  (hD : D ⊆ E) {e : Set S} (heD : e ∈ D)
    (hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂)
    (s : EdgeSides W (lab e) i p j q e₁ e₂) (τ : Bool)
    (hcase : (∃ e' ∈ D, ∃ τ', e' ≠ e ∧ extI (A e') (eo τ') = extI (A e) (eo τ) ∧ extI (A e)
      (eo τ) ∉ bd S ∧
        ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → (e'' = e ∧ τ'' = τ) ∨ (e''
          = e' ∧ τ'' = τ')) ∨
      (extI (A e) (eo τ) ∈ bd S ∧ ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → e''
        = e ∧ τ'' = τ)) :
    ¬ PRel (cutW W (lab '' D)) (spe W (s.end₁ τ)) (spe W (s.end₂ τ)) ∧ ∀ a ∈ Dsk W, f a = extI
      (A e) (eo τ) →
      PRel (cutW W (lab '' D)) (spe W (s.end₁ τ)) a ∨ PRel (cutW W (lab '' D)) (spe W (s.end₂ τ)) a
        := by
  classical
  set L := lab '' D with hL
  have heE := hD heD
  have hP := h.paired
  have hW := h.fin
  set c := s.end₁ τ with hc
  set c' := s.end₂ τ with hc'
  set v := extI (A e) (eo τ) with hv
  have hfc : f (spe W c) = v := h.f_end₁ heE s τ
  have hfc' : f (spe W c') = v := h.f_end₂ heE s τ
  have hcc : prtL W ∅ c = c' := prtL_of_mate hP (s.mate (notMem_empty _) τ)
  have hne : c ≠ c' := fun he => s.ne (by
    have := congrArg (fun x : SE W => (x.1.1, x.1.2.1)) he
    exact this)
  have hL0 : lab e ∈ L := ⟨e, heD, rfl⟩
  have hc1 : prtL W L c = c := (prtL_eq_iff hP c s.one).mpr (.inl hL0)
  have hc2 : prtL W L c' = c' := (prtL_eq_iff hP c' s.two).mpr (.inl hL0)
  have hrel : ∀ g : SE W, f (spe W g) = v → PRel W (spe W c) (spe W g) := fun g hg =>
    (h.pres.2.2 _ (spe_mem c) _ (spe_mem g)).mp (hfc.trans hg.symm)
  have hrelv : ∀ g : SE W, PRel W (spe W c) (spe W g) → f (spe W g) = v := fun g hg =>
    ((h.pres.2.2 _ (spe_mem c) _ (spe_mem g)).mpr hg).symm.trans hfc
  have hvE : v ∈ ⋃₀ E := ⟨e, heE, h.extI_mem heE _⟩
  have hvV : v ∈ V := h.extI_mem_V heE τ
  /- The letter at an end of a side. -/
  have hlet : ∀ g : SE W, ∃ k e', (W g.1.1)[g.1.2.1]? = some (k, e') := fun g =>
    ⟨_, _, List.getElem?_eq_getElem g.2⟩
  have hτinj : ∀ a b : Bool, extI (A e) (eo a) = extI (A e) (eo b) → a = b := fun a b he'
    => h.eo_inj heE he'
  /- An end at `v` fixed by crossing is an end of an edge in `D` or an end of a free side. -/
  have hfixes : ∀ g : SE W, f (spe W g) = v → prtL W L g = g → (∃ e'' ∈ D, ∃ τ'', extI (A e'')
    (eo τ'') = v ∧
      ∃ e', (W g.1.1)[g.1.2.1]? = some (lab e'', e')) ∨ prtL W ∅ g = g := by
    intro g hg hfix
    obtain ⟨k', e', hk⟩ := hlet g
    rcases (prtL_eq_iff hP g hk).mp hfix with ⟨e'', he'', rfl⟩ | hfr
    · obtain ⟨i', p', j', q', e₁', e₂', s'⟩ := hsd e'' he''
      obtain ⟨τ'', h5⟩ := s'.mem hP g hk
      refine .inl ⟨e'', he'', τ'', ?_, e', hk⟩
      rcases h5 with h5 | h5
      · rw [← h.f_end₁ (hD he'') s' τ'', ← h5, hg]
      · rw [← h.f_end₂ (hD he'') s' τ'', ← h5, hg]
    · exact .inr ((prtL_eq_iff hP g hk).mpr (.inr hfr))
  /- An end at `v` with the label of `e` is one of the two ends `c`, `c'`. -/
  have hone : ∀ g : SE W, f (spe W g) = v → ∀ e', (W g.1.1)[g.1.2.1]? = some (lab e, e') → g = c
    ∨ g = c' := by
    intro g hg e' hk
    obtain ⟨τ₃, h5⟩ := s.mem hP g hk
    rcases h5 with h5 | h5
    · have h6 : extI (A e) (eo τ₃) = v := by rw [← h.f_end₁ heE s τ₃, ← h5, hg]
      have h7 := hτinj _ _ h6
      subst h7
      exact .inl h5
    · have h6 : extI (A e) (eo τ₃) = v := by rw [← h.f_end₂ heE s τ₃, ← h5, hg]
      have h7 := hτinj _ _ h6
      subst h7
      exact .inr h5
  have hwrap : (∀ g : SE W, PRel W (spe W c) (spe W g) → PRel (cutW W L) (spe W c) (spe W g) ∨
      PRel (cutW W L) (spe W c') (spe W g)) → ∀ a ∈ Dsk W, f a = v → PRel (cutW W L) (spe W c) a ∨
        PRel (cutW W L) (spe W c') a := by
    intro h2 a ha hfa
    obtain ⟨g, rfl⟩ := h.corner_of ha (hfa ▸ hvE) (hfa ▸ hvV)
    exact h2 g (hrel g hfa)
  rcases hcase with ⟨e', he'D, τ', hee, hv', hvb, huniq⟩ | ⟨hvb, huniq⟩
  · have he'E := hD he'D
    obtain ⟨i', p', j', q', e₁', e₂', s'⟩ := hsd e' he'D
    set d := s'.end₁ τ' with hd
    set d' := s'.end₂ τ' with hd'
    have hfd : f (spe W d) = v := (h.f_end₁ he'E s' τ').trans hv'
    have hfd' : f (spe W d') = v := (h.f_end₂ he'E s' τ').trans hv'
    have hdd : prtL W ∅ d = d' := prtL_of_mate hP (s'.mate (notMem_empty _) τ')
    have hL1 : lab e' ∈ L := ⟨e', he'D, rfl⟩
    have hlabne : lab e' ≠ lab e := fun hl => hee (h.lab_inj he'E heE hl)
    have hnesame : ∀ {x y : SE W} {ex ey : Bool}, (W x.1.1)[x.1.2.1]? = some (lab e', ex) →
        (W y.1.1)[y.1.2.1]? = some (lab e, ey) → x ≠ y := by
      intro x y ex ey hx hy he'
      rw [he', hy] at hx
      have := congrArg (Option.map Prod.fst) hx
      simp at this
      exact hlabne this.symm
    have hdne : d ≠ d' := fun he' => s'.ne (by
      have := congrArg (fun x : SE W => (x.1.1, x.1.2.1)) he'
      exact this)
    have hτinj' : ∀ a b : Bool, extI (A e') (eo a) = extI (A e') (eo b) → a = b := fun a b he'
      => h.eo_inj he'E he'
    have hone' : ∀ g : SE W, f (spe W g) = v → ∀ e₃, (W g.1.1)[g.1.2.1]? = some (lab e', e₃) → g
      = d ∨ g = d' := by
      intro g hg e₃ hk
      obtain ⟨τ₃, h5⟩ := s'.mem hP g hk
      rcases h5 with h5 | h5
      · have h6 : extI (A e') (eo τ₃) = extI (A e') (eo τ') := by
          rw [← h.f_end₁ he'E s' τ₃, ← h5, hg, hv']
        have h7 := hτinj' _ _ h6
        subst h7
        exact .inl h5
      · have h6 : extI (A e') (eo τ₃) = extI (A e') (eo τ') := by
          rw [← h.f_end₂ he'E s' τ₃, ← h5, hg, hv']
        have h7 := hτinj' _ _ h6
        subst h7
        exact .inr h5
    obtain ⟨h1, h2⟩ := corner_cut hW hP hcc hc1 hc2 ((prtL_eq_iff hP d s'.one).mpr (.inl hL1))
      ((prtL_eq_iff hP d' s'.two).mpr (.inl hL1))
      hne (hnesame s'.one s.one) (hnesame s'.one s.two) (hnesame s'.two s.one)
        (hnesame s'.two s.two) hdne (hrel d hfd)
      (hrel d' hfd') (.inr hdd) (.inl (by rw [← hdd, prtL_invol hP])) (fun g hg hfix => by
        rcases hfixes g (hrelv g hg) hfix with ⟨e'', he'', τ'', h5, e₃, h6⟩ | hfr
        · rcases huniq e'' he'' τ'' h5 with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · rcases hone g (hrelv g hg) e₃ h6 with h7 | h7
            · exact .inl h7
            · exact .inr (.inl h7)
          · rcases hone' g (hrelv g hg) e₃ h6 with h7 | h7
            · exact .inr (.inr (.inl h7))
            · exact .inr (.inr (.inr h7))
        · exfalso
          obtain ⟨k', e₃, hk⟩ := hlet g
          rcases (prtL_eq_iff hP g hk).mp hfr with h5 | h5
          · exact h5
          · exact hvb (by
              rw [h.bd_eq, ← hrelv g hg]
              exact ⟨spe W g, ⟨_, _, _, g.2, h5, eo_mem _, rfl⟩, rfl⟩))
    exact ⟨h1, hwrap h2⟩
  · have hvb' := hvb
    rw [h.bd_eq] at hvb'
    obtain ⟨x, ⟨i₀, p₀, u, hp₀, hfree, hu, rfl⟩, hfx⟩ := hvb'
    obtain ⟨⟨k₀, e₀⟩, hk₀⟩ : ∃ l, (W i₀)[p₀]? = some l := ⟨_, List.getElem?_eq_getElem hp₀⟩
    obtain ⟨b₀, hb₀⟩ := h.corner_of_side hk₀ hu (hfx ▸ hvV)
    let d : SE W := ⟨(i₀, p₀, b₀), hp₀⟩
    have hspd : spe W d = spt W i₀ p₀ u := by simp only [spe, d, hb₀]
    have hfd : f (spe W d) = v := by rw [hspd, hfx]
    have hdfix : prtL W ∅ d = d := (prtL_eq_iff hP d hk₀).mpr (.inr hfree)
    obtain ⟨d', hd1, hd2, hd4, hd3⟩ := exists_free_end hW hP hdfix
    have hrd : ∀ g : SE W, f (spe W g) = v → PRel W (spe W d) (spe W g) := fun g hg =>
      (h.pres.2.2 _ (spe_mem d) _ (spe_mem g)).mp (hfd.trans hg.symm)
    have hfd' : f (spe W d') = v := ((h.pres.2.2 _ (spe_mem d) _ (spe_mem d')).mpr hd4).symm.trans
      hfd
    have hnfix : ∀ g : SE W, prtL W ∅ g = g → g ≠ c ∧ g ≠ c' := fun g hg => by
      constructor
      · rintro rfl
        exact hne (hg.symm.trans hcc)
      · rintro rfl
        have h5 : prtL W ∅ c' = c := by rw [← hcc, prtL_invol hP]
        exact hne (h5.symm.trans hg)
    have hL2 : ∀ g : SE W, prtL W ∅ g = g → prtL W L g = g := fun g hg => by
      rcases prtL_cases (L := L) hP g with h5 | h5
      · exact h5
      · exact h5.trans hg
    obtain ⟨h1, h2⟩ := corner_cut hW hP hcc hc1 hc2 (hL2 d hdfix) (hL2 d' hd2) hne
      (hnfix d hdfix).1 (hnfix d hdfix).2
      (hnfix d' hd2).1 (hnfix d' hd2).2 hd1.symm (hrel d hfd) (hrel d' hfd') (.inl hdfix)
        (.inr hd2) (fun g hg hfix => by
        rcases hfixes g (hrelv g hg) hfix with ⟨e'', he'', τ'', h5, e₃, h6⟩ | hfr
        · obtain ⟨rfl, -⟩ := huniq e'' he'' τ'' h5
          rcases hone g (hrelv g hg) e₃ h6 with h7 | h7
          · exact .inl h7
          · exact .inr (.inl h7)
        · rcases hd3 g (hrd g (hrelv g hg)) hfr with h5 | h5
          · exact .inr (.inr (.inl h5))
          · exact .inr (.inr (.inr h5)))
    exact ⟨h1, hwrap h2⟩

omit [T2Space S] in
theorem WordEdges.f_side (h : WordEdges W f V E A lab) {e : Set S} (he : e ∈ E) (hs : (W i)[p]?
  = some (lab e, e₁)) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : f (spt W i p u) = extI (A e) (ofs e₁ u) := by
  obtain ⟨e', he', hl, h1⟩ := h.side _ _ _ _ hs
  obtain rfl := h.lab_inj he' he hl
  exact h1 u hu

omit [TopologicalSpace S] [T2Space S] in
theorem image_extI (a : 𝕀 → S) : extI a '' Icc 0 1 = range a := by
  ext z
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.2, extI_coe a t⟩

theorem ofs_Ioo (e : Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : ofs e t ∈ Ioo (0 : ℝ) 1 := by
  cases e <;> simp only [ofs, Bool.false_eq_true, ite_true, ite_false]
  · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · exact ht

theorem continuous_spt_ofs (W : ℕ → List Letter) (i p : ℕ) (e : Bool) : Continuous fun t
  => spt W i p (ofs e t) := by
  have h1 : Continuous fun t : ℝ => ofs e t := by
    cases e <;> simp only [ofs, Bool.false_eq_true, ite_true, ite_false] <;> fun_prop
  exact continuous_const.prodMk ((continuous_per _).comp (continuous_const.add h1))

/-- A map that respects the pasting descends to the quotient. -/
theorem exists_descend {Y T : Type*} [TopologicalSpace Y] [TopologicalSpace T] [T2Space Y] {W' : ℕ
  → List Letter}
    (hW : FinW W') {g : ℕ × ℂ → Y} (hg : Presents W' g) {f : ℕ × ℂ → T} (hf : ContinuousOn f
      (Dsk W'))
    (hr : ∀ a ∈ Dsk W', ∀ b ∈ Dsk W', PRel W' a b → f a = f b) :
    ∃ ψ : Y → T, Continuous ψ ∧ ∀ a ∈ Dsk W', ψ (g a) = f a := by
  have : CompactSpace (Dsk W') := isCompact_iff_compactSpace.mp (isCompact_Dsk hW)
  let gr : Dsk W' → Y := fun a => g a.1
  have hc : Continuous gr := continuousOn_iff_continuous_domRestrict.mp hg.1
  have hs : Function.Surjective gr := fun y => by
    obtain ⟨a, ha, rfl⟩ : y ∈ g '' Dsk W' := hg.2.1 ▸ mem_univ y
    exact ⟨⟨a, ha⟩, rfl⟩
  have hq : IsQuotientMap gr := hc.isClosedMap.isQuotientMap hc hs
  let ψ : Y → T := fun y => f (Function.surjInv hs y).1
  have hψ : ∀ a ∈ Dsk W', ψ (g a) = f a := fun a ha => by
    have h1 : gr (Function.surjInv hs (g a)) = g a := Function.surjInv_eq hs _
    exact hr _ (Function.surjInv hs (g a)).2 _ ha ((hg.2.2 _ (Function.surjInv hs
      (g a)).2 _ ha).mp h1)
  refine ⟨ψ, ?_, hψ⟩
  rw [hq.continuous_iff]
  have e : ψ ∘ gr = fun a : Dsk W' => f a.1 := funext fun a => hψ a.1 a.2
  rw [e]
  exact continuousOn_iff_continuous_domRestrict.mp hf

/-- The cut surface over the union of a set `D` of edges, with two lifts of each edge. -/
theorem WordEdges.cut_space (h : WordEdges W f V E A lab) {D : Set (Set S)} (hD : D ⊆ E)
    (hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂)
    (hcase : ∀ e ∈ D, ∀ τ, (∃ e' ∈ D, ∃ τ', e' ≠ e ∧ extI (A e') (eo τ') = extI (A e) (eo τ) ∧ extI
      (A e) (eo τ) ∉ bd S ∧
        ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → (e'' = e ∧ τ'' = τ) ∨ (e''
          = e' ∧ τ'' = τ')) ∨
      (extI (A e) (eo τ) ∈ bd S ∧ ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → e''
        = e ∧ τ'' = τ))
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {g : ℕ × ℂ → Y} (hg : Presents (cutW W
      (lab '' D)) g) :
    ∃ ψ : Y → S, Continuous ψ ∧ Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' (⋃₀ D)ᶜ) ∧ ψ ⁻¹'
      (⋃₀ D) ⊆ bd Y ∧ IsSurface Y ∧
      ∀ e ∈ D, ∃ X X', LiftPair ψ e (extI (A e) 0) (extI (A e) 1) X X' := by
  classical
  set L := lab '' D with hL
  have hP := h.paired
  have hfW' : FinW (cutW W L) := finW_cut h.fin
  have hP' : IsPaired (cutW W L) := isPaired_cut hP
  obtain ⟨hsurf, hbdY⟩ := surface_of_presents hfW' hP' hg
  have hD' : Dsk (cutW W L) = Dsk W := dsk_cut
  obtain ⟨ψ, hψc, hψ⟩ := exists_descend hfW' hg (hD' ▸ h.pres.1) (fun a ha b hb hab =>
    (h.pres.2.2 a (hD' ▸ ha) b (hD' ▸ hb)).mpr (prel_of_prel_cut hab))
  rw [hD'] at hψ
  have hrep : ∀ z : Y, ∃ a ∈ Dsk W, g a = z := fun z => by
    have hz : z ∈ g '' Dsk (cutW W L) := hg.2.1 ▸ mem_univ z
    rwa [hD'] at hz
  have hgeq : ∀ {a b}, a ∈ Dsk W → b ∈ Dsk W → (g a = g b ↔ PRel (cutW W L) a b) := fun {a b} ha hb
    =>
    hg.2.2 a (hD' ▸ ha) b (hD' ▸ hb)
  have hkey : ∀ e ∈ D, ∃ X X', LiftPair ψ e (extI (A e) 0) (extI (A e) 1) X X' ∧ X ∪ X' ⊆ bd Y := by
    intro e heD
    have heE := hD heD
    obtain ⟨i, p, j, q, e₁, e₂, s⟩ := hsd e heD
    have hL0 : lab e ∈ L := ⟨e, heD, rfl⟩
    have hv := fun τ => h.vertex_cut hD heD hsd s τ (hcase e heD τ)
    have hp := lt_length s.one
    have hq := lt_length s.two
    let r : ℝ → Y := fun t => g (spt W i p (ofs e₁ t))
    let r' : ℝ → Y := fun t => g (spt W j q (ofs e₂ t))
    have hm1 : ∀ t, spt W i p (ofs e₁ t) ∈ Dsk W := fun t => spt_mem hp _
    have hm2 : ∀ t, spt W j q (ofs e₂ t) ∈ Dsk W := fun t => spt_mem hq _
    have hrc : ContinuousOn r (Icc 0 1) :=
      hg.1.comp (continuous_spt_ofs W i p e₁).continuousOn fun t _ => hD' ▸ hm1 t
    have hrc' : ContinuousOn r' (Icc 0 1) :=
      hg.1.comp (continuous_spt_ofs W j q e₂).continuousOn fun t _ => hD' ▸ hm2 t
    have hr : ∀ t ∈ Icc (0 : ℝ) 1, ψ (r t) = extI (A e) t := fun t ht => by
      simp only [r]
      rw [hψ _ (hm1 t), h.f_side heE s.one (ofs_mem ht), ofs_ofs]
    have hr' : ∀ t ∈ Icc (0 : ℝ) 1, ψ (r' t) = extI (A e) t := fun t ht => by
      simp only [r']
      rw [hψ _ (hm2 t), h.f_side heE s.two (ofs_mem ht), ofs_ofs]
    have hspe : ∀ τ, spe W (s.end₁ τ) = spt W i p (ofs e₁ (eo τ)) := fun τ
      => by simp only [spe, EdgeSides.end₁, eo_xn]
    have hspe' : ∀ τ, spe W (s.end₂ τ) = spt W j q (ofs e₂ (eo τ)) := fun τ
      => by simp only [spe, EdgeSides.end₂, eo_xn]
    have hne : ∀ t ∈ Icc (0 : ℝ) 1, r t ≠ r' t := by
      intro t ht he
      have hpr := (hgeq (hm1 t) (hm2 t)).mp he
      by_cases hend : ∃ τ, eo τ = t
      · obtain ⟨τ, rfl⟩ := hend
        rw [← hspe, ← hspe'] at hpr
        exact (hv τ).1 hpr
      · push Not at hend
        have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 fun h0 => hend false
          (by simp [eo, h0]),
          lt_of_le_of_ne ht.2 fun h0 => hend true (by simp [eo, h0])⟩
        have hu := ofs_Ioo e₁ ht'
        have hl' : (cutW W L i)[p]? = some (2 * Nat.pair i p + 1, e₁)
          := cut_get_iff.mpr ⟨_, s.one, .inl ⟨hL0, rfl⟩⟩
        have hpr' : PRel (cutW W L) (spt (cutW W L) i p (ofs e₁ t)) (spt W j q (ofs e₂ t)) := by
          rw [spt_cut]
          exact hpr
        have hfree := freeSide_cut (L := L) s.one hL0
        have heqs : spt W j q (ofs e₂ t) = spt W i p (ofs e₁ t) := by
          rcases hpr'.eq_or_stp hP' hl' hu with h1 | h1
          · rw [h1, spt_cut]
          · exfalso
            obtain ⟨j', q', e', h2, h3, -⟩ := stp_of_side hP' hl' hu h1
            exact h3 (hfree _ _ _ _ _ hl' h2)
        have h1 : j = i := congrArg Prod.fst heqs
        subst h1
        have h2 : per (W j).length (q + ofs e₂ t) = per (W j).length (p + ofs e₁ t)
          := congrArg Prod.snd heqs
        obtain ⟨h3, -⟩ := side_unique hq hp (ofs_Ioo e₂ ht') (ofs_mem ht) h2
        exact s.ne (by rw [h3])
    have hfill : ∀ z, ψ z ∈ extI (A e) '' Icc 0 1 → z ∈ r '' Icc 0 1 ∪ r' '' Icc 0 1 := by
      rintro z ⟨t, ht, hzt⟩
      obtain ⟨a, ha, rfl⟩ := hrep z
      rw [hψ a ha] at hzt
      by_cases hend : ∃ τ, eo τ = t
      · obtain ⟨τ, rfl⟩ := hend
        rcases (hv τ).2 a ha hzt.symm with h1 | h1
        · refine .inl ⟨eo τ, ht, ?_⟩
          have := (hgeq (spe_mem _) ha).mpr h1
          rw [hspe] at this
          exact this
        · refine .inr ⟨eo τ, ht, ?_⟩
          have := (hgeq (spe_mem _) ha).mpr h1
          rw [hspe'] at this
          exact this
      · push Not at hend
        have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 fun h0 => hend false
          (by simp [eo, h0]),
          lt_of_le_of_ne ht.2 fun h0 => hend true (by simp [eo, h0])⟩
        have hu := ofs_Ioo e₁ ht'
        have hfx : f (spt W i p (ofs e₁ t)) = f a := by
          rw [h.f_side heE s.one (ofs_mem ht), ofs_ofs, hzt]
        have hpr := (h.pres.2.2 _ (hm1 t) _ ha).mp hfx
        rcases hpr.eq_or_stp hP s.one hu with h1 | h1
        · exact .inl ⟨t, ht, by simp only [r]; rw [h1]⟩
        · obtain ⟨j', q', e', h2, h3, h4⟩ := stp_of_side hP s.one hu h1
          rcases hP.third s.one s.two h2 s.ne with h5 | h5
          · exact absurd h5.symm h3
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
            have he' : e' = e₂ := by
              rw [s.two] at h2
              simpa using h2.symm
            subst he'
            refine .inr ⟨t, ht, ?_⟩
            simp only [r']
            rw [h4, flp_ofs]
    have hrange : extI (A e) '' Icc 0 1 = e := by
      rw [image_extI, (h.arc e heE).2.1]
    have hpair := liftPair_of_maps (ψ := ψ) hrc hrc' hr hr' (extI_injOn (h.arc e heE).1.2) hne hfill
    rw [hrange] at hpair
    refine ⟨_, _, hpair, ?_⟩
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · rw [hbdY]
      refine ⟨spt W i p (ofs e₁ t), ⟨i, p, ofs e₁ t, ?_, freeSide_cut s.one hL0, ofs_mem ht,
        (spt_cut _ _ _).symm⟩, rfl⟩
      rw [cutW_length]
      exact hp
    · rw [hbdY]
      refine ⟨spt W j q (ofs e₂ t), ⟨j, q, ofs e₂ t, ?_, freeSide_cut s.two hL0, ofs_mem ht,
        (spt_cut _ _ _).symm⟩, rfl⟩
      rw [cutW_length]
      exact hq
  have hoff : ∀ a b, PRel W a b → f a = f b ∧ (f a ∉ ⋃₀ D → PRel (cutW W L) a b) := by
    intro a b hab
    induction hab with
    | rel a b hs =>
      have hfe := presents_eq_of_stp h.pres hs
      refine ⟨hfe, fun hF => ?_⟩
      obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp hs
      refine .rel _ _ (stp_to_cut h1 h2 h3 hu fun hk => ?_)
      obtain ⟨e'', he'', rfl⟩ := hk
      exact hF ⟨e'', he'', by
        rw [h.f_side (hD he'') h1 hu]
        exact h.extI_mem (hD he'') _⟩
    | refl _ => exact ⟨rfl, fun _ => .refl _⟩
    | symm a b _ ih => exact ⟨ih.1.symm, fun hF => .symm _ _ (ih.2 (ih.1 ▸ hF))⟩
    | trans a b c _ _ h1 h2 => exact ⟨h1.1.trans h2.1, fun hF => .trans _ _ _ (h1.2 hF) (h2.2
      (h1.1 ▸ hF))⟩
  refine ⟨ψ, hψc, ?_, ?_, ?_, hsurf, fun e he => ?_⟩
  · intro x
    obtain ⟨a, ha, rfl⟩ : x ∈ f '' Dsk W := h.pres.2.1 ▸ mem_univ x
    exact ⟨g a, hψ a ha⟩
  · intro z hz z' hz' he
    obtain ⟨a, ha, rfl⟩ := hrep z
    obtain ⟨b, hb, rfl⟩ := hrep z'
    have h1 : f a = f b := by rw [← hψ a ha, ← hψ b hb, he]
    have h2 : f a ∉ ⋃₀ D := fun h3 => hz (by
      show ψ (g a) ∈ ⋃₀ D
      rw [hψ a ha]
      exact h3)
    exact (hgeq ha hb).mpr ((hoff a b ((h.pres.2.2 a ha b hb).mp h1)).2 h2)
  · rintro z ⟨e, he, hz⟩
    obtain ⟨X, X', ⟨x0, x1, y0, y1, -, -, -, h4, -⟩, hsub⟩ := hkey e he
    exact hsub (h4 ▸ hz)
  · obtain ⟨X, X', hp, -⟩ := hkey e he
    exact ⟨X, X', hp⟩

end GraphMinor.Surface
