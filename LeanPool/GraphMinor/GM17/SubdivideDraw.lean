/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Subdivide
public import LeanPool.GraphMinor.GM17.AngleOrder
public import LeanPool.GraphMinor.Surface.ArcTools

/-!
# A drawing of `H` gives a drawing of its double subdivision

We cut each edge of a drawing of `H` at the points with parameters `1/3` and `2/3`
(`canBeDrawnIn_subdiv`).
-/

@[expose] public noncomputable section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Graph unitInterval

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- A path that is one to one, except that its two ends may agree. -/
def IsEdgePath (c : I → S) : Prop := Continuous c ∧ ∀ s t, c s = c t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s
  = 1 ∧ t = 0)

omit [T2Space S] in
theorem exists_path_of_line {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : ∃ c : I
  → S, IsEdgePath c ∧ c 0 = u ∧ c 1 = v ∧ range c = L := by
  obtain ⟨f, h0, h1⟩ := h
  refine ⟨fun t => (f t).1, ⟨continuous_subtype_val.comp f.continuous,
    fun s t he => Or.inl (f.injective (Subtype.ext he))⟩, h0, h1, ?_⟩
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (f t).2
  · intro hx
    exact ⟨f.symm ⟨x, hx⟩, by simp⟩

omit [T2Space S] in
theorem exists_path_of_oArc {L : Set S} {u : S} (h : IsOArc L) (hu : u ∈ L) : ∃ c : I
  → S, IsEdgePath c ∧ c 0 = u ∧ c 1 = u ∧ range c = L := by
  obtain ⟨g⟩ := h
  have hpi := Real.pi_pos
  let w₀ : Circle := g.symm ⟨u, hu⟩
  have hval : (g w₀).1 = u := by simp [w₀]
  refine ⟨fun t => (g (w₀ * Circle.exp (2 * Real.pi * t.1))).1, ⟨?_, fun s t he => ?_⟩, ?_, ?_, ?_⟩
  · refine continuous_subtype_val.comp (g.continuous.comp ?_)
    exact continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))
  · have h1 := g.injective (Subtype.ext he)
    have h2 := mul_left_cancel h1
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h2
    have h3 : (s.1 : ℝ) - t.1 = m := by
      have : 2 * Real.pi * ((s.1 : ℝ) - t.1 - m) = 0 := by linear_combination hm
      have h4 := (mul_eq_zero.mp this).resolve_left (by positivity)
      linarith
    have hs := s.2
    have ht := t.2
    have h5 : (m : ℝ) ≤ 1 := by linarith [hs.2, ht.1]
    have h6 : (-1 : ℝ) ≤ m := by linarith [hs.1, ht.2]
    have h7 : m ≤ 1 := by exact_mod_cast h5
    have h8 : -1 ≤ m := by exact_mod_cast h6
    have hcases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    rcases hcases with rfl | rfl | rfl
    · right; left
      push_cast at h3
      exact ⟨Subtype.ext (show (s.1 : ℝ) = 0 by linarith [hs.1, ht.2]),
        Subtype.ext (show (t.1 : ℝ) = 1 by linarith [hs.1, ht.2])⟩
    · left
      push_cast at h3
      exact Subtype.ext (by linarith)
    · right; right
      push_cast at h3
      exact ⟨Subtype.ext (show (s.1 : ℝ) = 1 by linarith [hs.2, ht.1]),
        Subtype.ext (show (t.1 : ℝ) = 0 by linarith [hs.2, ht.1])⟩
  · simp [hval]
  · have : Circle.exp (2 * Real.pi) = 1 := Circle.exp_two_pi
    simp [this, hval]
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (g _).2
    · intro hx
      obtain ⟨θ, hθ, he⟩ := exists_angle_mem 0 (w₀⁻¹ * g.symm ⟨x, hx⟩)
      have h1 : 0 ≤ θ / (2 * Real.pi) := div_nonneg hθ.1 (by positivity)
      have h2 : θ / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [hθ.2]
      refine ⟨⟨θ / (2 * Real.pi), h1, h2⟩, ?_⟩
      change (g (w₀ * Circle.exp (2 * Real.pi * (θ / (2 * Real.pi))))).1 = x
      rw [show 2 * Real.pi * (θ / (2 * Real.pi)) = θ by field_simp, he, mul_inv_cancel_left,
        g.apply_symm_apply]

/-- A piece of the unit interval. -/
def pc (x y : ℝ) : Set I := {t | x ≤ t.1 ∧ t.1 ≤ y}

theorem IsEdgePath.line {c : I → S} (hc : IsEdgePath c) {x y : I} (hxy : x.1 < y.1) (hne : ¬ (x = 0
  ∧ y = 1)) : IsLineWithEnds (c '' pc x.1 y.1) (c x) (c y) := by
  have hx := x.2
  have hy := y.2
  let φ : I → I := fun t => ⟨x.1 + t.1 * (y.1 - x.1), by nlinarith [t.2.1, t.2.2, hx.1], by
    nlinarith [t.2.1, t.2.2, hy.2]⟩
  let e : I → S := fun t => c (φ t)
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hec : Continuous e := hc.1.comp hφ
  have hφi : Function.Injective φ := fun s t he => by
    have h1 : x.1 + s.1 * (y.1 - x.1) = x.1 + t.1 * (y.1 - x.1) := congrArg Subtype.val he
    have h2 : (s.1 - t.1) * (y.1 - x.1) = 0 := by linarith
    have h3 := (mul_eq_zero.mp h2).resolve_right (by linarith)
    exact Subtype.ext (by linarith)
  have hbd : ∀ t, x.1 ≤ (φ t).1 ∧ (φ t).1 ≤ y.1 := fun t => by
    change x.1 ≤ x.1 + t.1 * (y.1 - x.1) ∧ x.1 + t.1 * (y.1 - x.1) ≤ y.1
    constructor <;> nlinarith [t.2.1, t.2.2]
  have hei : Function.Injective e := fun s t he => by
    rcases hc.2 _ _ he with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hφi h
    · exfalso
      apply hne
      have h3 := hbd s
      have h4 := hbd t
      rw [h1] at h3
      rw [h2] at h4
      exact ⟨Subtype.ext (le_antisymm h3.1 hx.1), Subtype.ext (le_antisymm hy.2 h4.2)⟩
    · exfalso
      apply hne
      have h3 := hbd s
      have h4 := hbd t
      rw [h1] at h3
      rw [h2] at h4
      exact ⟨Subtype.ext (le_antisymm h4.1 hx.1), Subtype.ext (le_antisymm hy.2 h3.2)⟩
  have hr : range e = c '' pc x.1 y.1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨φ t, hbd t, rfl⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      have hd : 0 < y.1 - x.1 := by linarith
      refine ⟨⟨(t.1 - x.1) / (y.1 - x.1), div_nonneg (by linarith) hd.le, ?_⟩, ?_⟩
      · rw [div_le_one hd]
        linarith
      change c (φ _) = c t
      congr 1
      apply Subtype.ext
      change x.1 + (t.1 - x.1) / (y.1 - x.1) * (y.1 - x.1) = t.1
      field_simp
      ring
  have hem := hec.isClosedEmbedding hei
  refine ⟨hem.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr), ?_, ?_⟩
  · change e 0 = c x
    change c (φ 0) = c x
    congr 1
    apply Subtype.ext
    simp [φ]
  · change e 1 = c y
    change c (φ 1) = c y
    congr 1
    apply Subtype.ext
    simp [φ]

/-- The point of the path at one third. -/
def t₁ : I := ⟨1 / 3, by norm_num, by norm_num⟩

/-- The point of the path at two thirds. -/
def t₂ : I := ⟨2 / 3, by norm_num, by norm_num⟩

/-- The two ends of the `i`-th piece of the path. -/
def pts : Fin 3 → I × I
  | 0 => (0, t₁)
  | 1 => (t₁, t₂)
  | 2 => (t₂, 1)

theorem t₁_ne_zero : t₁ ≠ 0 := fun h => by
  have := congrArg Subtype.val h
  norm_num [t₁] at this

theorem t₁_ne_one : t₁ ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  norm_num [t₁] at this

theorem t₂_ne_zero : t₂ ≠ 0 := fun h => by
  have := congrArg Subtype.val h
  norm_num [t₂] at this

theorem t₂_ne_one : t₂ ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  norm_num [t₂] at this

theorem t₁_ne_t₂ : t₁ ≠ t₂ := fun h => by
  have := congrArg Subtype.val h
  norm_num [t₁, t₂] at this

/-- The piece of the unit interval with index `i`. -/
abbrev piece (i : Fin 3) : Set I := pc (pts i).1.1 (pts i).2.1

theorem mem_piece_of_ne {i j : Fin 3} (hij : i ≠ j) {t : I} (hi : t ∈ piece i)
  (hj : t ∈ piece j) : t = t₁ ∨ t = t₂ := by
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨h3, h4⟩ := hj
  have hz : ((0 : I) : ℝ) = 0 := rfl
  have ho : ((1 : I) : ℝ) = 1 := rfl
  have ht1 : (t₁ : ℝ) = 1 / 3 := rfl
  have ht2 : (t₂ : ℝ) = 2 / 3 := rfl
  fin_cases i <;> fin_cases j <;> simp only [pts, hz, ho, ht1, ht2] at h1 h2 h3 h4
  · exact absurd rfl hij
  · exact Or.inl (Subtype.ext (le_antisymm (by rw [ht1]; exact h2) (by rw [ht1]; exact h3)))
  · linarith
  · exact Or.inl (Subtype.ext (le_antisymm (by rw [ht1]; exact h4) (by rw [ht1]; exact h1)))
  · exact absurd rfl hij
  · exact Or.inr (Subtype.ext (le_antisymm (by rw [ht2]; exact h2) (by rw [ht2]; exact h3)))
  · linarith
  · exact Or.inr (Subtype.ext (le_antisymm (by rw [ht2]; exact h4) (by rw [ht2]; exact h1)))
  · exact absurd rfl hij

theorem piece_of_zero {i : Fin 3} (h : (0 : I) ∈ piece i) : i = 0 := by
  obtain ⟨h1, -⟩ := h
  have hz : ((0 : I) : ℝ) = 0 := rfl
  have ht1 : (t₁ : ℝ) = 1 / 3 := rfl
  have ht2 : (t₂ : ℝ) = 2 / 3 := rfl
  fin_cases i
  · rfl
  · simp only [pts, hz, ht1] at h1
    linarith
  · simp only [pts, hz, ht2] at h1
    linarith

theorem piece_of_one {i : Fin 3} (h : (1 : I) ∈ piece i) : i = 2 := by
  obtain ⟨-, h1⟩ := h
  have ho : ((1 : I) : ℝ) = 1 := rfl
  have ht1 : (t₁ : ℝ) = 1 / 3 := rfl
  have ht2 : (t₂ : ℝ) = 2 / 3 := rfl
  fin_cases i
  · simp only [pts, ho, ht1] at h1
    linarith
  · simp only [pts, ho, ht2] at h1
    linarith
  · rfl

theorem piece_of_t₁ {i : Fin 3} (h : t₁ ∈ piece i) : i = 0 ∨ i = 1 := by
  obtain ⟨h1, -⟩ := h
  have ht1 : (t₁ : ℝ) = 1 / 3 := rfl
  have ht2 : (t₂ : ℝ) = 2 / 3 := rfl
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl
  · simp only [pts, ht1, ht2] at h1
    linarith

theorem piece_of_t₂ {i : Fin 3} (h : t₂ ∈ piece i) : i = 1 ∨ i = 2 := by
  obtain ⟨-, h1⟩ := h
  have ho : ((0 : I) : ℝ) = 0 := rfl
  have ht1 : (t₁ : ℝ) = 1 / 3 := rfl
  have ht2 : (t₂ : ℝ) = 2 / 3 := rfl
  fin_cases i
  · simp only [pts, ht1, ht2] at h1
    linarith
  · exact Or.inl rfl
  · exact Or.inr rfl

variable {α' β' : Type} {H : Hypergraph α' β'} {a b : ↥H.edgeSet → α'}

/-- A drawing of `H` gives a drawing of its double subdivision. We cut each edge at the points at
one third and two thirds of its path. -/
theorem canBeDrawnIn_subdiv (hab : ∀ e : ↥H.edgeSet, H.ends e.1 = {a e, b e})
  (ha : ∀ e, a e ∈ H.vertexSet) (hb : ∀ e, b e ∈ H.vertexSet) (h : CanBeDrawn S H) :
    GM16.CanBeDrawnIn S (subdiv H a b ha hb) := by
  classical
  obtain ⟨ν, F, h1, h2, h3, h4, h5⟩ := h
  have hpath : ∀ e : ↥H.edgeSet, ∃ c : I → S, IsEdgePath c ∧ c 0 = ν (a e) ∧ c 1 = ν (b e)
    ∧ range c = F e.1 := by
    intro e
    have hia : H.Inc e.1 (a e) := by
      change a e ∈ H.ends e.1
      rw [hab]
      exact Or.inl rfl
    have hib : H.Inc e.1 (b e) := by
      change b e ∈ H.ends e.1
      rw [hab]
      exact Or.inr rfl
    by_cases hne : a e = b e
    · have hend : H.ends e.1 = {a e} := by rw [hab, ← hne]; simp
      obtain ⟨ho, hm⟩ := h3 e.1 e.2 _ hend
      obtain ⟨c, hc, h0, h1', hr⟩ := exists_path_of_oArc ho hm
      exact ⟨c, hc, h0, by rw [h1', hne], hr⟩
    · exact exists_path_of_line (h2 e.1 e.2 _ _ hia hib hne)
  choose c hc hc0 hc1 hcr using hpath
  have hmemF : ∀ e t, c e t ∈ F e.1 := fun e t => hcr e ▸ mem_range_self t
  have hint : ∀ e t, t ≠ 0 → t ≠ 1 → ∀ v ∈ H.vertexSet, c e t ≠ ν v := by
    intro e t ht0 ht1 v hv he
    have hi : v ∈ H.ends e.1 := h5 e.1 e.2 v hv (he ▸ hmemF e t)
    rw [hab] at hi
    rcases hi with rfl | rfl
    · rcases (hc e).2 t 0 (he.trans (hc0 e).symm) with h' | ⟨h', -⟩ | ⟨h', -⟩
      · exact ht0 h'
      · exact ht0 h'
      · exact ht1 h'
    · rcases (hc e).2 t 1 (he.trans (hc1 e).symm) with h' | ⟨h', -⟩ | ⟨h', -⟩
      · exact ht1 h'
      · exact ht0 h'
      · exact ht1 h'
  have hcross : ∀ {e e' : ↥H.edgeSet}, e ≠ e' → ∀ {t t'}, c e t = c e' t'
    → ∃ v ∈ H.vertexSet, c e t = ν v := by
    intro e e' hne t t' he
    obtain ⟨v, hv, hx⟩ := h4 e.1 e.2 e'.1 e'.2 (fun h => hne (Subtype.ext h)) ⟨hmemF e t, he ▸
      hmemF e' t'⟩
    exact ⟨v, hv, hx.symm⟩
  let ν' : SV H → S := fun w => match w with
    | .inl v => ν v
    | .inr (e, false) => c e t₁
    | .inr (e, true) => c e t₂
  let F' : SE H → Set S := fun f => c f.1 '' piece f.2
  have hends : ∀ f : SE H, ν' (lnk H a b f).1 = c f.1 (pts f.2).1 ∧ ν' (lnk H a b f).2 = c f.1
    (pts f.2).2 := by
    rintro ⟨e, i⟩
    fin_cases i
    · exact ⟨(hc0 e).symm, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, (hc1 e).symm⟩
  have hline : ∀ f : SE H, IsLineWithEnds (F' f) (ν' (lnk H a b f).1) (ν' (lnk H a b f).2) := by
    intro f
    rw [(hends f).1, (hends f).2]
    obtain ⟨e, i⟩ := f
    have hz : ((0 : I) : ℝ) = 0 := rfl
    have ho : ((1 : I) : ℝ) = 1 := rfl
    have ht1 : (t₁ : ℝ) = 1 / 3 := rfl
    have ht2 : (t₂ : ℝ) = 2 / 3 := rfl
    fin_cases i
    · exact (hc e).line (by change ((0 : I) : ℝ) < t₁; rw [hz, ht1]; norm_num) fun h
      => t₁_ne_one h.2
    · exact (hc e).line (by change (t₁ : ℝ) < t₂; rw [ht1, ht2]; norm_num) fun h => t₁_ne_zero h.1
    · exact (hc e).line (by change (t₂ : ℝ) < ((1 : I) : ℝ); rw [ho, ht2]; norm_num) fun h
      => t₂_ne_zero h.1
  have hlnk : ∀ f : SE H, (lnk H a b f).1 ≠ (lnk H a b f).2 := by
    rintro ⟨e, i⟩
    fin_cases i <;> simp [lnk]
  have hmem : ∀ f : SE H, (lnk H a b f).1 ∈ V(subdiv H a b ha hb) ∧ (lnk H a b f).2 ∈ V(subdiv H a
    b ha hb) := by
    rintro ⟨e, i⟩
    fin_cases i
    · exact ⟨subdiv_inl (ha e), subdiv_inr _⟩
    · exact ⟨subdiv_inr _, subdiv_inr _⟩
    · exact ⟨subdiv_inr _, subdiv_inl (hb e)⟩
  have hincl : ∀ (f : SE H), (subdiv H a b ha hb).Inc f (lnk H a b f).1 := fun f => ⟨_, Or.inl rfl⟩
  have hincr : ∀ (f : SE H), (subdiv H a b ha hb).Inc f (lnk H a b f).2 := fun f => ⟨_, Or.inr rfl⟩
  have htstar : ∀ (e : ↥H.edgeSet) (t t' : I), t ≠ 0 → t ≠ 1 → c e t = c e t' → t = t' := by
    intro e t t' h0 h1' he
    rcases (hc e).2 _ _ he with h' | ⟨h', -⟩ | ⟨h', -⟩
    · exact h'
    · exact absurd h' h0
    · exact absurd h' h1'
  refine ⟨ν', F', ?_, ?_, ?_, ?_, ?_⟩
  · rintro (u | ⟨e, _ | _⟩) hu (w | ⟨e', _ | _⟩) hw he
    · have hu' : u ∈ H.vertexSet := by simpa [subdiv] using hu
      have hw' : w ∈ H.vertexSet := by simpa [subdiv] using hw
      rw [h1 hu' hw' he]
    · have hu' : u ∈ H.vertexSet := by simpa [subdiv] using hu
      exact absurd he.symm (hint e' _ t₁_ne_zero t₁_ne_one u hu')
    · have hu' : u ∈ H.vertexSet := by simpa [subdiv] using hu
      exact absurd he.symm (hint e' _ t₂_ne_zero t₂_ne_one u hu')
    · have hw' : w ∈ H.vertexSet := by simpa [subdiv] using hw
      exact absurd he (hint e _ t₁_ne_zero t₁_ne_one w hw')
    · by_cases hee : e = e'
      · rw [hee]
      · obtain ⟨v, hv, hx⟩ := hcross hee he
        exact absurd hx (hint e _ t₁_ne_zero t₁_ne_one v hv)
    · by_cases hee : e = e'
      · subst hee
        exact absurd (htstar e _ _ t₁_ne_zero t₁_ne_one he) t₁_ne_t₂
      · obtain ⟨v, hv, hx⟩ := hcross hee he
        exact absurd hx (hint e _ t₁_ne_zero t₁_ne_one v hv)
    · have hw' : w ∈ H.vertexSet := by simpa [subdiv] using hw
      exact absurd he (hint e _ t₂_ne_zero t₂_ne_one w hw')
    · by_cases hee : e = e'
      · subst hee
        exact absurd (htstar e _ _ t₂_ne_zero t₂_ne_one he).symm t₁_ne_t₂
      · obtain ⟨v, hv, hx⟩ := hcross hee he
        exact absurd hx (hint e _ t₂_ne_zero t₂_ne_one v hv)
    · by_cases hee : e = e'
      · rw [hee]
      · obtain ⟨v, hv, hx⟩ := hcross hee he
        exact absurd hx (hint e _ t₂_ne_zero t₂_ne_one v hv)
  · intro f _ u v hl _
    rcases hl with hl | hl
    · have := hline f
      rw [hl] at this
      exact this
    · have hl' : IsLineWithEnds (F' f) (ν' v) (ν' u) := by
        have := hline f
        rwa [hl] at this
      exact hl'.symm
  · intro f _ v hl
    have hl' : (subdiv H a b ha hb).IsLink f v v := hl
    rcases hl' with hl' | hl' <;> · have := hlnk f; rw [hl'] at this; exact absurd rfl this
  · rintro ⟨e, i⟩ _ ⟨e', j⟩ _ hne x ⟨⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
    by_cases hee : e = e'
    · subst hee
      have hij : i ≠ j := fun h => hne (by rw [h])
      rcases (hc e).2 _ _ he with h' | ⟨-, h'⟩ | ⟨-, h'⟩
      · subst h'
        rcases mem_piece_of_ne hij ht ht' with rfl | rfl
        · exact ⟨_, subdiv_inr (e, false), rfl⟩
        · exact ⟨_, subdiv_inr (e, true), rfl⟩
      · subst h'
        exact ⟨_, subdiv_inl (hb e), (hc1 e).symm⟩
      · subst h'
        exact ⟨_, subdiv_inl (ha e), (hc0 e).symm⟩
    · obtain ⟨v, hv, hx⟩ := hcross (Ne.symm hee) he
      exact ⟨_, subdiv_inl hv, by rw [← he, hx]⟩
  · rintro ⟨e, i⟩ _ w hw ⟨t, ht, he⟩
    rcases w with v | ⟨e', _ | _⟩
    · have hv : v ∈ H.vertexSet := by simpa [subdiv] using hw
      by_cases ht0 : t = 0
      · subst ht0
        obtain rfl := piece_of_zero ht
        have : v = a e := h1 hv (ha e) (he.symm.trans (hc0 e))
        rw [this]
        exact hincl (e, 0)
      · by_cases ht1 : t = 1
        · subst ht1
          obtain rfl := piece_of_one ht
          have : v = b e := h1 hv (hb e) (he.symm.trans (hc1 e))
          rw [this]
          exact hincr (e, 2)
        · exact absurd he (hint e t ht0 ht1 v hv)
    · by_cases hee : e' = e
      · subst hee
        have : t₁ = t := htstar e' _ _ t₁_ne_zero t₁_ne_one he.symm
        subst this
        rcases piece_of_t₁ ht with rfl | rfl
        · exact hincr (e', 0)
        · exact hincl (e', 1)
      · obtain ⟨v, hv, hx⟩ := hcross hee he.symm
        exact absurd hx (hint e' _ t₁_ne_zero t₁_ne_one v hv)
    · by_cases hee : e' = e
      · subst hee
        have : t₂ = t := htstar e' _ _ t₂_ne_zero t₂_ne_one he.symm
        subst this
        rcases piece_of_t₂ ht with rfl | rfl
        · exact hincr (e', 1)
        · exact hincl (e', 2)
      · obtain ⟨v, hv, hx⟩ := hcross hee he.symm
        exact absurd hx (hint e' _ t₂_ne_zero t₂_ne_one v hv)

end GraphMinor.GM17
