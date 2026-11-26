/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Drawings on a line and on an `O`-arc

A line with finitely many marked points that include its ends, and an `O`-arc with a non-empty
finite
set of marked points, each carry a drawing whose vertices are the marked points
(`exists_drawing_on_line`, `exists_drawing_on_oArc`). They are used to turn a painting into a
drawing.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A curve that is injective on `[a, b]` runs along a line. -/
theorem isLine_of_injOn {p : ℝ → S} (hp : Continuous p) {a b : ℝ} (hab : a < b)
    (hi : InjOn p (Icc a b)) : IsLineWithEnds (p '' Icc a b) (p a) (p b) := by
  let m : I → ℝ := fun t => a + t * (b - a)
  have hm : ∀ t, m t ∈ Icc a b := fun t => by
    have h0 := t.2.1
    have h1 := t.2.2
    constructor
    · change a ≤ a + (t : ℝ) * (b - a)
      nlinarith
    · change a + (t : ℝ) * (b - a) ≤ b
      nlinarith
  have hg : Continuous fun t : I => p (m t) := hp.comp (by fun_prop)
  have hinj : Function.Injective fun t : I => p (m t) := by
    intro s t h
    have := hi (hm s) (hm t) h
    have h' : (s : ℝ) * (b - a) = t * (b - a) := by
      change a + (s : ℝ) * (b - a) = a + (t : ℝ) * (b - a) at this
      linarith
    exact Subtype.ext (mul_right_cancel₀ (by linarith : b - a ≠ 0) h')
  have hL := isLine_range hg hinj
  have hr : range (fun t : I => p (m t)) = p '' Icc a b := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨m t, hm t, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      have hd : 0 < b - a := by linarith
      refine ⟨⟨(s - a) / (b - a), div_nonneg (by linarith [hs.1]) hd.le,
        (div_le_one hd).mpr (by linarith [hs.2])⟩, ?_⟩
      change p (a + (s - a) / (b - a) * (b - a)) = p s
      rw [div_mul_cancel₀ _ hd.ne']
      congr 1
      ring
  have h0 : p (m 0) = p a := by
    change p (a + ((0 : I) : ℝ) * (b - a)) = p a
    simp
  have h1 : p (m 1) = p b := by
    change p (a + ((1 : I) : ℝ) * (b - a)) = p b
    simp
  simpa only [hr, h0, h1] using hL

/-- A line with finitely many marked points, among them its ends, carries a drawing whose vertices
are the marked points. -/
theorem exists_drawing_on_line (n : ℕ) : ∀ {L A : Set S} {x y : S}, IsLineWithEnds L x y → x ≠ y →
    A.Finite → x ∈ A → y ∈ A → A ⊆ L → A.ncard ≤ n → ∃ D : Drawing S, D.U = L ∧ D.V = A := by
  induction n with
  | zero =>
    intro L A x y _ _ hA hx _ _ hn
    have : A = ∅ := (ncard_eq_zero hA).mp (by omega)
    simp [this] at hx
  | succ n ih =>
    intro L A x y hL hxy hA hx hy hAL hn
    by_cases hb : ∃ b ∈ A, b ≠ x ∧ b ≠ y
    · obtain ⟨b, hbA, hbx, hby⟩ := hb
      obtain ⟨f, hf0, hf1⟩ := id hL
      let g : I → S := fun t => (f t).1
      have hgc : Continuous g := continuous_subtype_val.comp f.continuous
      have hgi : Function.Injective g := Subtype.val_injective.comp f.injective
      have hrange : range g = L := by
        ext z
        constructor
        · rintro ⟨t, rfl⟩
          exact (f t).2
        · intro hz
          obtain ⟨t, ht⟩ := f.surjective ⟨z, hz⟩
          exact ⟨t, by simp [g, ht]⟩
      obtain ⟨τ, hτ⟩ : b ∈ range g := hrange ▸ hAL hbA
      have hτ0 : (0 : I) < τ := by
        refine bot_lt_iff_ne_bot.mpr fun h => hbx ?_
        rw [← hτ, ← hf0]
        exact congrArg g h
      have hτ1 : τ < 1 := by
        refine lt_top_iff_ne_top.mpr fun h => hby ?_
        rw [← hτ, ← hf1]
        exact congrArg g h
      have hL₁ : IsLineWithEnds (g '' Icc 0 τ) x b := by
        have := isLine_piece hgc hgi hτ0
        rwa [hτ, show g 0 = x from hf0] at this
      have hL₂ : IsLineWithEnds (g '' Icc τ 1) b y := by
        have := isLine_piece hgc hgi hτ1
        rwa [hτ, show g 1 = y from hf1] at this
      have hyn : y ∉ g '' Icc 0 τ := by
        rintro ⟨t, ht, h⟩
        have : t = 1 := hgi (h.trans (show g 1 = y from hf1).symm)
        exact absurd ht.2 (by rw [this]; exact not_le.mpr hτ1)
      have hxn : x ∉ g '' Icc τ 1 := by
        rintro ⟨t, ht, h⟩
        have : t = 0 := hgi (h.trans (show g 0 = x from hf0).symm)
        exact absurd ht.1 (by rw [this]; exact not_le.mpr hτ0)
      have hc₁ : (A ∩ g '' Icc 0 τ).ncard ≤ n := by
        have : (A ∩ g '' Icc 0 τ).ncard < A.ncard :=
          ncard_lt_ncard ⟨inter_subset_left, fun h => hyn (h hy).2⟩ hA
        omega
      have hc₂ : (A ∩ g '' Icc τ 1).ncard ≤ n := by
        have : (A ∩ g '' Icc τ 1).ncard < A.ncard :=
          ncard_lt_ncard ⟨inter_subset_left, fun h => hxn (h hx).2⟩ hA
        omega
      have hb₁ : b ∈ g '' Icc 0 τ := ⟨τ, ⟨hτ0.le, le_rfl⟩, hτ⟩
      have hb₂ : b ∈ g '' Icc τ 1 := ⟨τ, ⟨le_rfl, hτ1.le⟩, hτ⟩
      have hx₁ : x ∈ g '' Icc 0 τ := ⟨0, ⟨le_rfl, hτ0.le⟩, hf0⟩
      have hy₂ : y ∈ g '' Icc τ 1 := ⟨1, ⟨hτ1.le, le_rfl⟩, hf1⟩
      obtain ⟨D₁, hU₁, hV₁⟩ := ih hL₁ hbx.symm (hA.inter_of_left _) ⟨hx, hx₁⟩ ⟨hbA, hb₁⟩
        inter_subset_right hc₁
      obtain ⟨D₂, hU₂, hV₂⟩ := ih hL₂ hby (hA.inter_of_left _) ⟨hbA, hb₂⟩ ⟨hy, hy₂⟩
        inter_subset_right hc₂
      have hmeet : D₁.U ∩ D₂.U ⊆ D₁.V ∩ D₂.V := by
        rw [hU₁, hU₂, hV₁, hV₂]
        rintro z ⟨⟨s, hs, rfl⟩, ⟨t, ht, ht'⟩⟩
        have hst : t = s := hgi ht'
        have hs' : s = τ := le_antisymm hs.2 (hst ▸ ht.1)
        subst hs'
        rw [hτ]
        exact ⟨⟨hbA, hb₁⟩, ⟨hbA, hb₂⟩⟩
      refine ⟨D₁.glue D₂ hmeet, ?_, ?_⟩
      · change D₁.U ∪ D₂.U = L
        rw [hU₁, hU₂, ← image_union, ← hrange, ← image_univ]
        congr 1
        ext t
        simp only [mem_union, mem_Icc, mem_univ, iff_true]
        rcases le_total t τ with h | h
        · exact Or.inl ⟨t.2.1, h⟩
        · exact Or.inr ⟨h, t.2.2⟩
      · change D₁.V ∪ D₂.V = A
        rw [hV₁, hV₂, ← inter_union_distrib_left, inter_eq_left]
        intro z hz
        obtain ⟨t, rfl⟩ : z ∈ range g := hrange ▸ hAL hz
        rcases le_total t τ with h | h
        · exact Or.inl ⟨t, ⟨t.2.1, h⟩, rfl⟩
        · exact Or.inr ⟨t, ⟨h, t.2.2⟩, rfl⟩
    · refine ⟨lineDrawing hL hxy, rfl, ?_⟩
      apply subset_antisymm
      · rintro z (rfl | rfl)
        · exact hx
        · exact hy
      · intro z hz
        by_contra h
        exact hb ⟨z, hz, fun e => h (Or.inl e), fun e => h (Or.inr e)⟩

omit [T2Space S] in
/-- A parametrization of an `O`-arc from a given point. -/
theorem exists_oArc_par {F : Set S} (hF : IsOArc F) {a : S} (ha : a ∈ F) :
    ∃ p : ℝ → S, Continuous p ∧ p 0 = a ∧ p (2 * Real.pi) = a ∧
      (∀ s t, p s = p t → ∃ m : ℤ, s = t + m * (2 * Real.pi)) ∧
      p '' Ico 0 (2 * Real.pi) = F ∧ range p ⊆ F := by
  obtain ⟨f⟩ := hF
  obtain ⟨z, hz⟩ := f.surjective ⟨a, ha⟩
  let θ₀ : ℝ := Complex.arg (z : ℂ)
  have hθ : Circle.exp θ₀ = z := Circle.exp_arg z
  let p : ℝ → S := fun s => (f (Circle.exp (θ₀ + s))).1
  have hp : Continuous p :=
    continuous_subtype_val.comp (f.continuous.comp (Circle.exp.continuous.comp (by fun_prop)))
  have h0 : p 0 = a := by simp [p, hθ, hz]
  refine ⟨p, hp, h0, ?_, ?_, ?_, ?_⟩
  · have : Circle.exp (θ₀ + 2 * Real.pi) = Circle.exp θ₀ := by
      rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
    simp only [p, this, hθ, hz]
  · intro s t h
    have h₁ := f.injective (Subtype.ext h)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h₁
    exact ⟨m, by linarith⟩
  · apply subset_antisymm
    · rintro _ ⟨s, -, rfl⟩
      exact (f _).2
    · intro y hy
      obtain ⟨w, hw⟩ := f.surjective ⟨y, hy⟩
      have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
      let s := toIcoMod hpos 0 (Complex.arg (w : ℂ) - θ₀)
      have hs : s ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico hpos 0 _
      rw [zero_add] at hs
      refine ⟨s, hs, ?_⟩
      have hk : (Complex.arg (w : ℂ) - θ₀) - toIcoDiv hpos 0 (Complex.arg (w : ℂ) - θ₀) •
        (2 * Real.pi) = s :=
        self_sub_toIcoDiv_zsmul hpos 0 _
      have he : Circle.exp (θ₀ + s) = w := by
        rw [← Circle.exp_arg w]
        refine Circle.exp_eq_exp.mpr ⟨- toIcoDiv hpos 0 (Complex.arg (w : ℂ) - θ₀), ?_⟩
        rw [← hk, zsmul_eq_mul]
        push_cast
        ring
      simp only [p, he, hw]
  · rintro _ ⟨s, rfl⟩
    exact (f _).2

/-- An `O`-arc with one marked point is a loop. -/
theorem exists_loop_drawing {F : Set S} (hF : IsOArc F) {a : S} (ha : a ∈ F) :
    ∃ D : Drawing S, D.U = F ∧ D.V = {a} := by
  obtain ⟨p, hp, h0, h2, hper, himg, hr⟩ := exists_oArc_par hF ha
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hsd : F \ {a} = p '' Ioo 0 (2 * Real.pi) := by
    ext y
    constructor
    · rintro ⟨hy, hya⟩
      rw [← himg] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun h => hya ?_, hs.2⟩, rfl⟩
      rw [← h, h0]
      rfl
    · rintro ⟨s, hs, rfl⟩
      refine ⟨hr ⟨s, rfl⟩, fun h => ?_⟩
      have h' : p s = p 0 := h.trans h0.symm
      obtain ⟨m, hm⟩ := hper s 0 h'
      rw [zero_add] at hm
      have h₁ : (0 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith [hs.1]
      have h₂ : (m : ℝ) < 1 := by
        by_contra hc
        push Not at hc
        nlinarith [hs.2]
      have h₃ : (0 : ℤ) < m := by exact_mod_cast h₁
      have h₄ : m < (1 : ℤ) := by exact_mod_cast h₂
      omega
  have hpc : IsPathConnected (F \ {a}) := by
    rw [hsd]
    exact ((convex_Ioo _ _).isPathConnected (nonempty_Ioo.mpr hpos)).image hp
  have hFc : IsClosed F := by
    rw [← himg]
    have : p '' Ico 0 (2 * Real.pi) = p '' Icc 0 (2 * Real.pi) := by
      apply subset_antisymm (image_mono Ico_subset_Icc_self)
      rintro _ ⟨s, hs, rfl⟩
      rcases hs.2.lt_or_eq with h | h
      · exact ⟨s, ⟨hs.1, h⟩, rfl⟩
      · exact ⟨0, ⟨le_rfl, hpos⟩, by rw [h, h0, h2]⟩
    rw [this]
    exact (isCompact_Icc.image hp).isClosed
  have hcl : closure (F \ {a}) = F := by
    apply subset_antisymm (closure_minimal sdiff_subset hFc)
    rw [hsd]
    intro y hy
    rw [← himg] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have : s ∈ closure (Ioo 0 (2 * Real.pi)) := by
      rw [closure_Ioo hpos.ne]
      exact Ico_subset_Icc_self hs
    exact map_mem_closure hp this fun t ht => ⟨t, ht, rfl⟩
  have huniq : ∀ C ∈ arcComponentsIn (F \ {a}), C = F \ {a} := by
    rintro C ⟨-, hsub, -, hmax⟩
    exact (hmax _ Subset.rfl hpc hsub).symm
  refine ⟨{ U := F, V := {a}, V_subset_U := singleton_subset_iff.mpr ha, isClosed_U := hFc,
            finite_V := finite_singleton a, finite_edges := ?_, edge_cond := ?_ }, rfl, rfl⟩
  · exact (finite_singleton _).subset fun C hC => huniq C hC
  · intro e he
    obtain rfl := huniq e he
    rw [hcl]
    exact Or.inr ⟨a, inter_eq_right.mpr (singleton_subset_iff.mpr ha), hF⟩

/-- An `O`-arc with a non-empty finite set of marked points carries a drawing whose vertices are the
marked points. -/
theorem exists_drawing_on_oArc {F A : Set S} (hF : IsOArc F) (hA : A.Finite) (hne : A.Nonempty)
    (hAF : A ⊆ F) : ∃ D : Drawing S, D.U = F ∧ D.V = A := by
  by_cases hs : ∃ a, A = {a}
  · obtain ⟨a, rfl⟩ := hs
    exact exists_loop_drawing hF (hAF rfl)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ A, y ≠ x := by
    by_contra h
    push Not at h
    exact hs ⟨x, eq_singleton_iff_unique_mem.mpr ⟨hx, h⟩⟩
  obtain ⟨p, hp, h0, h2, hper, himg, hr⟩ := exists_oArc_par hF (hAF hx)
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  obtain ⟨α, hα, rfl⟩ : y ∈ p '' Ico 0 (2 * Real.pi) := himg ▸ hAF hy
  have hα0 : 0 < α := by
    refine lt_of_le_of_ne hα.1 fun h => hxy ?_
    rw [← h, h0]
  have hclose : ∀ {s t : ℝ}, p s = p t → |s - t| < 2 * Real.pi → s = t := by
    intro s t h hd
    obtain ⟨m, hm⟩ := hper s t h
    have hm0 : m = 0 := by
      by_contra hc
      have h₁ : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hc
      have h₂ : |s - t| = |(m : ℝ)| * (2 * Real.pi) := by
        rw [hm, add_sub_cancel_left, abs_mul, abs_of_pos hpos]
      nlinarith
    rw [hm, hm0]
    simp
  have hi₁ : InjOn p (Icc 0 α) := fun s hs t ht h => hclose h (by
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2, hα.2])
  have hi₂ : InjOn p (Icc α (2 * Real.pi)) := fun s hs t ht h => hclose h (by
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2, hα0])
  have hL₁ := isLine_of_injOn hp hα0 hi₁
  have hL₂ := isLine_of_injOn hp hα.2 hi₂
  rw [h0] at hL₁
  rw [h2] at hL₂
  have hx₁ : x ∈ p '' Icc 0 α := ⟨0, ⟨le_rfl, hα0.le⟩, h0⟩
  have hx₂ : x ∈ p '' Icc α (2 * Real.pi) := ⟨2 * Real.pi, ⟨hα.2.le, le_rfl⟩, h2⟩
  have hy₁ : p α ∈ p '' Icc 0 α := ⟨α, ⟨hα0.le, le_rfl⟩, rfl⟩
  have hy₂ : p α ∈ p '' Icc α (2 * Real.pi) := ⟨α, ⟨le_rfl, hα.2.le⟩, rfl⟩
  have hFeq : p '' Icc 0 α ∪ p '' Icc α (2 * Real.pi) = F := by
    apply subset_antisymm
    · rintro _ (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> exact hr ⟨s, rfl⟩
    · rw [← himg]
      rintro _ ⟨s, hs, rfl⟩
      rcases le_total s α with h | h
      · exact Or.inl ⟨s, ⟨hs.1, h⟩, rfl⟩
      · exact Or.inr ⟨s, ⟨h, hs.2.le⟩, rfl⟩
  obtain ⟨D₁, hU₁, hV₁⟩ := exists_drawing_on_line _ hL₁ hxy.symm (hA.inter_of_left _) ⟨hx, hx₁⟩
    ⟨hy, hy₁⟩ inter_subset_right le_rfl
  obtain ⟨D₂, hU₂, hV₂⟩ := exists_drawing_on_line _ hL₂ hxy (hA.inter_of_left _) ⟨hy, hy₂⟩
    ⟨hx, hx₂⟩ inter_subset_right le_rfl
  have hmeet : D₁.U ∩ D₂.U ⊆ D₁.V ∩ D₂.V := by
    rw [hU₁, hU₂, hV₁, hV₂]
    rintro _ ⟨⟨s, hs, rfl⟩, ⟨t, ht, ht'⟩⟩
    obtain ⟨m, hm⟩ := hper t s ht'
    by_cases hst : s = α
    · subst hst
      exact ⟨⟨hy, hy₁⟩, ⟨hy, hy₂⟩⟩
    have hs' : s < α := lt_of_le_of_ne hs.2 hst
    by_cases hs0 : s = 0
    · subst hs0
      rw [h0]
      exact ⟨⟨hx, hx₁⟩, ⟨hx, hx₂⟩⟩
    have hs0' : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hmm : (0 : ℝ) < m ∧ (m : ℝ) < 1 := by
      constructor <;> nlinarith [ht.1, ht.2, Real.two_pi_pos]
    have h₃ : (0 : ℤ) < m := by exact_mod_cast hmm.1
    have h₄ : m < (1 : ℤ) := by exact_mod_cast hmm.2
    omega
  refine ⟨D₁.glue D₂ hmeet, ?_, ?_⟩
  · change D₁.U ∪ D₂.U = F
    rw [hU₁, hU₂, hFeq]
  · change D₁.V ∪ D₂.V = A
    rw [hV₁, hV₂, ← inter_union_distrib_left, hFeq]
    exact inter_eq_left.mpr hAF

end GraphMinor.GM11
