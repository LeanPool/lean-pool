/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs3
public import LeanPool.GraphMinor.Surface.PushOff

/-!
# Angles on a cuff

To speak of the order of edges around a cuff we read the cuff through the angle map `cuffPoint f`
for a homeomorphism `f` from the circle.
`exists_angle_of_line` picks `f` so that a given line in the cuff has the angles from `0` to `π`.
The result on connected sets is
`arc_of_preconnected`: a connected subset of the cuff holds one of the two arcs between two of its
points.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface Real

variable {T : Type*} [TopologicalSpace T]

theorem continuous_cuffAngle {c : Set T} (f : Circle ≃ₜ c) : Continuous (cuffPoint f) :=
  continuous_subtype_val.comp (f.continuous.comp Circle.exp.continuous)

theorem cuffAngle_mem {c : Set T} (f : Circle ≃ₜ c) (t : ℝ) : cuffPoint f t ∈ c := (f _).2

theorem cuffAngle_add_two_pi {c : Set T} (f : Circle ≃ₜ c) (t : ℝ) : cuffPoint f (t + 2 * π)
  = cuffPoint f t := by
  unfold cuffPoint
  rw [Circle.periodic_exp t]

theorem cuffAngle_sub_two_pi {c : Set T} (f : Circle ≃ₜ c) (t : ℝ) : cuffPoint f (t - 2 * π)
  = cuffPoint f t := by
  rw [← cuffAngle_add_two_pi f (t - 2 * π), sub_add_cancel]

/-- Two angles of one point differ by a multiple of `2π`. -/
theorem cuffAngle_eq_iff {c : Set T} (f : Circle ≃ₜ c) {x y : ℝ} : cuffPoint f x
  = cuffPoint f y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [← Circle.exp_eq_exp]
  exact ⟨fun h ↦ f.injective (Subtype.ext h), fun h ↦ by unfold cuffPoint; rw [h]⟩

theorem cuffAngle_injOn {c : Set T} (f : Circle ≃ₜ c) {a x y : ℝ} (hx : x ∈ Ico a (a + 2 * π))
  (hy : y ∈ Ico a (a + 2 * π))
    (h : cuffPoint f x = cuffPoint f y) : x = y := by
  obtain ⟨m, hm⟩ := (cuffAngle_eq_iff f).1 h
  have hpi := Real.pi_pos
  have h₁ : (m : ℝ) * (2 * π) < 2 * π := by linarith [hx.1, hx.2, hy.1, hy.2]
  have h₂ : -(2 * π) < (m : ℝ) * (2 * π) := by linarith [hx.1, hx.2, hy.1, hy.2]
  have h₃ : (m : ℝ) < 1 := by nlinarith
  have h₄ : (-1 : ℝ) < m := by nlinarith
  have h₅ : m = 0 := by
    have : m < 1 := by exact_mod_cast h₃
    have : -1 < m := by exact_mod_cast h₄
    omega
  rw [hm, h₅]
  simp

theorem exists_cuffAngle_eq {c : Set T} (f : Circle ≃ₜ c) (a : ℝ) {z : T}
  (hz : z ∈ c) : ∃ t ∈ Ico a (a + 2 * π), cuffPoint f t = z := by
  obtain ⟨w, hw⟩ := f.surjective ⟨z, hz⟩
  obtain ⟨t, rfl⟩ := Circle.exp_surjective w
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := existsUnique_add_zsmul_mem_Ico (mul_pos two_pos hpi) t a |>.exists
  refine ⟨t + n • (2 * π), by simpa using hn, ?_⟩
  have : cuffPoint f (t + n • (2 * π)) = cuffPoint f t := (cuffAngle_eq_iff f).2 ⟨n, by simp⟩
  rw [this]
  unfold cuffPoint
  rw [hw]

/-- **A connected subset of a cuff holds one of the two arcs between two of its points.** -/
theorem arc_of_preconnected [T2Space T] {c J : Set T} (f : Circle ≃ₜ c) (hJ : IsPreconnected J)
  (hJc : J ⊆ c) {x₁ x₂ : ℝ} (h₁₂ : x₁ ≤ x₂) (h₂₁ : x₂ ≤ x₁ + 2 * π)
    (h₁ : cuffPoint f x₁ ∈ J) (h₂ : cuffPoint f x₂ ∈ J) :
    (∀ y ∈ Icc x₁ x₂, cuffPoint f y ∈ J) ∨ ∀ y ∈ Icc x₂ (x₁ + 2 * π), cuffPoint f y ∈ J := by
  by_contra hno
  push Not at hno
  obtain ⟨⟨y, hy, hyJ⟩, y', hy', hyJ'⟩ := hno
  have hg := continuous_cuffAngle f
  have hy₁ : x₁ < y := lt_of_le_of_ne hy.1 (by rintro rfl; exact hyJ h₁)
  have hy₂ : y < x₂ := lt_of_le_of_ne hy.2 (by rintro rfl; exact hyJ h₂)
  have hy'₁ : x₂ < y' := lt_of_le_of_ne hy'.1 (by rintro rfl; exact hyJ' h₂)
  have hy'₂ : y' < x₁ + 2 * π := lt_of_le_of_ne hy'.2 (by
    rintro rfl
    rw [cuffAngle_add_two_pi] at hyJ'
    exact hyJ' h₁)
  set C₁ := cuffPoint f '' Icc y y' with hC₁
  set C₂ := cuffPoint f '' Icc y' (y + 2 * π) with hC₂
  have hcl₁ : IsClosed C₁ := (isCompact_Icc.image hg).isClosed
  have hcl₂ : IsClosed C₂ := (isCompact_Icc.image hg).isClosed
  have hsame : ∀ {z}, z ∈ Icc y y' → ∀ {z'}, z' ∈ Icc y' (y + 2 * π) → cuffPoint f z
    = cuffPoint f z' → cuffPoint f z ∉ J := by
    intro z hz z' hz' he hzJ
    by_cases hzy : z = y
    · exact hyJ (hzy ▸ hzJ)
    by_cases hzy' : z = y'
    · exact hyJ' (hzy' ▸ hzJ)
    have hzo : z ∈ Ico y (y + 2 * π) := ⟨hz.1, by linarith [hz.2]⟩
    by_cases hz'e : z' = y + 2 * π
    · rw [hz'e, cuffAngle_add_two_pi] at he
      exact hzy (cuffAngle_injOn f hzo ⟨le_rfl, by linarith [Real.pi_pos]⟩ he)
    · have hz'o : z' ∈ Ico y (y + 2 * π) := ⟨by linarith [hz'.1, hz.1, hz.2], lt_of_le_of_ne hz'.2
      hz'e⟩
      have := cuffAngle_injOn f hzo hz'o he
      exact hzy' (le_antisymm hz.2 (this ▸ hz'.1))
  have hcov : J ⊆ C₁ ∪ C₂ := fun z hz ↦ by
    obtain ⟨t, ht, rfl⟩ := exists_cuffAngle_eq f y (hJc hz)
    by_cases hle : t ≤ y'
    · exact Or.inl ⟨t, ⟨ht.1, hle⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨(not_le.1 hle).le, ht.2.le⟩, rfl⟩
  have hsplit : J ⊆ C₁ ∨ J ⊆ C₂ := by
    have hdis : Disjoint (J ∩ C₁) (J ∩ C₂) := disjoint_left.2 fun z hz hz' ↦ by
      obtain ⟨t, ht, rfl⟩ := hz.2
      obtain ⟨t', ht', he⟩ := hz'.2
      exact hsame ht ht' he.symm hz.1
    have h := (isPreconnected_iff_subset_of_disjoint_closed.1 hJ) C₁ C₂ hcl₁ hcl₂ hcov (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzJ, hz₁, hz₂⟩
      exact disjoint_left.1 hdis ⟨hzJ, hz₁⟩ ⟨hzJ, hz₂⟩)
    exact h
  rcases hsplit with h | h
  · obtain ⟨t, ht, he⟩ := h h₁
    have hto : t ∈ Ico y (y + 2 * π) := ⟨ht.1, by linarith [ht.2]⟩
    have hx : x₁ + 2 * π ∈ Ico y (y + 2 * π) := ⟨by linarith [Real.pi_pos], by linarith⟩
    rw [← cuffAngle_add_two_pi f x₁] at he
    have := cuffAngle_injOn f hto hx he
    linarith [ht.2]
  · obtain ⟨t, ht, he⟩ := h h₂
    have hto : t ∈ Ico y' (y' + 2 * π) := by
      by_cases hte : t = y + 2 * π
      · exfalso
        rw [hte, cuffAngle_add_two_pi] at he
        have := cuffAngle_injOn f (a := y) ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hy₂.le, by
          linarith⟩ he
        linarith
      · exact ⟨ht.1, by linarith [ht.2]⟩
    have hx : x₂ + 2 * π ∈ Ico y' (y' + 2 * π) := ⟨by linarith, by linarith⟩
    rw [← cuffAngle_add_two_pi f x₂] at he
    have := cuffAngle_injOn f hto hx he
    linarith [ht.2]

private theorem continuous_paired_cuff_arcs {u v : unitInterval → T}
    (hu : Continuous u) (hv : Continuous v) (hends : u 1 = v 1) :
    let cl₁ : ℝ → unitInterval := fun t ↦ Set.projIcc 0 1 zero_le_one (t / π)
    let cl₂ : ℝ → unitInterval := fun t ↦ Set.projIcc 0 1 zero_le_one (2 - t / π)
    Continuous (fun t ↦ if t ≤ π then u (cl₁ t) else v (cl₂ t)) := by
  intro cl₁ cl₂
  have hpi' := Real.pi_ne_zero
  have hcl₁ : Continuous cl₁ := continuous_projIcc.comp (continuous_id.div_const _)
  have hcl₂ : Continuous cl₂ := continuous_projIcc.comp (continuous_const.sub
  (continuous_id.div_const _))
  refine Continuous.if_le (hu.comp hcl₁) (hv.comp hcl₂) continuous_id
    continuous_const ?_
  rintro x rfl
  have h₁ : cl₁ π = 1 := by simp [cl₁, hpi']
  have h₂ : cl₂ π = 1 := by
    have : (2 : ℝ) - π / π = 1 := by rw [div_self hpi']; norm_num
    simp only [cl₂, this]
    simp
  change u (cl₁ π) = v (cl₂ π)
  rw [h₁, h₂, hends]

/-- **A homeomorphism from the circle that gives a line in `c` the angles from `0` to `π`.** -/
theorem exists_angle_of_line [T2Space T] {c L : Set T} {a b : T} (hc : IsOArc c)
  (hl : IsLineWithEnds L a b) (hLc : L ⊆ c) :
    ∃ f : Circle ≃ₜ c, cuffPoint f 0 = a ∧ cuffPoint f π = b ∧ cuffPoint f '' Icc 0 π = L := by
  classical
  obtain ⟨u, v, h2, hru, hu0, hu1, hun⟩ := exists_arcs_of_line hc hl hLc
  have hpi := Real.pi_pos
  have hpi' : π ≠ 0 := hpi.ne'
  let cl₁ : ℝ → unitInterval := fun t ↦ Set.projIcc 0 1 zero_le_one (t / π)
  let cl₂ : ℝ → unitInterval := fun t ↦ Set.projIcc 0 1 zero_le_one (2 - t / π)
  let p : ℝ → T := fun t ↦ if t ≤ π then u (cl₁ t) else v (cl₂ t)
  have hpc : Continuous p := continuous_paired_cuff_arcs h2.arc_left.1 h2.arc_right.1 h2.one.symm
  have hp₁ : ∀ t (ht : t ∈ Icc 0 π), p t = u ⟨t / π, div_nonneg ht.1 hpi.le,
    (div_le_one hpi).2 ht.2⟩ := by
    intro t ht
    have : p t = u (cl₁ t) := ite_eq_left ht.2
    rw [this]
    congr 1
    exact Set.projIcc_of_mem _ ⟨div_nonneg ht.1 hpi.le, (div_le_one hpi).2 ht.2⟩
  have hp₂ : ∀ t (ht : t ∈ Ioc π (2 * π)), p t = v ⟨2 - t / π, by
      have : t / π ≤ 2 := (div_le_iff₀ hpi).2 ht.2
      linarith, by
      have : 1 ≤ t / π := (one_le_div hpi).2 ht.1.le
      linarith⟩ := by
    intro t ht
    have : p t = v (cl₂ t) := ite_eq_right (not_le.2 ht.1)
    rw [this]
    congr 1
    refine Set.projIcc_of_mem _ ⟨?_, ?_⟩
    · have : t / π ≤ 2 := (div_le_iff₀ hpi).2 ht.2
      linarith
    · have : 1 ≤ t / π := (one_le_div hpi).2 ht.1.le
      linarith
  have hp0 : p 0 = a := by
    rw [hp₁ 0 ⟨le_rfl, hpi.le⟩, ← hu0]
    congr 1
    ext
    simp
  have hppi : p π = b := by
    rw [hp₁ π ⟨hpi.le, le_rfl⟩, ← hu1]
    congr 1
    ext
    simp [hpi']
  have hp2 : p (2 * π) = a := by
    rw [hp₂ (2 * π) ⟨by linarith, le_rfl⟩, ← hu0, ← h2.zero]
    congr 1
    ext
    simp [hpi']
  have hmem : ∀ t ∈ Icc 0 (2 * π), p t ∈ c := fun t ht ↦ by
    rw [← hun]
    by_cases h : t ≤ π
    · rw [hp₁ t ⟨ht.1, h⟩]
      exact Or.inl (mem_range_self _)
    · rw [hp₂ t ⟨not_le.1 h, ht.2⟩]
      exact Or.inr (mem_range_self _)
  -- `p` is one to one on `[0, 2π)`.
  have hinj : ∀ {s t}, s ∈ Ico 0 (2 * π) → t ∈ Ico 0 (2 * π) → p s = p t → s = t := by
    have key₁ : ∀ {s t}, s ∈ Icc 0 π → t ∈ Icc 0 π → p s = p t → s = t := fun {s t} hs ht h ↦ by
      rw [hp₁ s hs, hp₁ t ht] at h
      have := Subtype.ext_iff.1 (h2.arc_left.2 h)
      field_simp at this
      exact this
    have key₂ : ∀ {s t}, s ∈ Ioc π (2 * π) → t ∈ Ioc π (2 * π) → p s = p t → s = t
      := fun {s t} hs ht h ↦ by
      rw [hp₂ s hs, hp₂ t ht] at h
      have := Subtype.ext_iff.1 (h2.arc_right.2 h)
      have h' : s / π = t / π := by
        simp only at this
        linarith
      field_simp at h'
      exact h'
    have key₃ : ∀ {s t}, s ∈ Icc 0 π → t ∈ Ioo π (2 * π) → p s ≠ p t := fun {s t} hs ht h ↦ by
      rw [hp₁ s hs, hp₂ t ⟨ht.1, ht.2.le⟩] at h
      have hlt₁ : 1 < t / π := (one_lt_div hpi).2 ht.1
      have hlt₂ : t / π < 2 := (div_lt_iff₀ hpi).2 ht.2
      rcases h2.meet _ _ h with ⟨-, h'⟩ | ⟨-, h'⟩
      · have := Subtype.ext_iff.1 h'
        simp only [Set.Icc.coe_zero] at this
        linarith
      · have := Subtype.ext_iff.1 h'
        simp only [Set.Icc.coe_one] at this
        linarith
    intro s t hs ht h
    by_cases h₁ : s ≤ π
    · by_cases h₂ : t ≤ π
      · exact key₁ ⟨hs.1, h₁⟩ ⟨ht.1, h₂⟩ h
      · exact absurd h (key₃ ⟨hs.1, h₁⟩ ⟨not_le.1 h₂, ht.2⟩)
    · by_cases h₂ : t ≤ π
      · exact absurd h.symm (key₃ ⟨ht.1, h₂⟩ ⟨not_le.1 h₁, hs.2⟩)
      · exact key₂ ⟨not_le.1 h₁, hs.2.le⟩ ⟨not_le.1 h₂, ht.2.le⟩ h
  -- The circle as a quotient of `[0, 2π]`.
  let q : Icc 0 (2 * π) → Circle := fun t ↦ Circle.exp t.1
  have hqc : Continuous q := Circle.exp.continuous.comp continuous_subtype_val
  have hqs : Function.Surjective q := fun z ↦ by
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    obtain ⟨n, hn⟩ := (existsUnique_add_zsmul_mem_Ico (mul_pos two_pos hpi) t 0).exists
    rw [zero_add] at hn
    refine ⟨⟨t + n • (2 * π), hn.1, hn.2.le⟩, ?_⟩
    exact Circle.exp_eq_exp.2 ⟨n, by simp⟩
  have : CompactSpace (Icc (0 : ℝ) (2 * π)) := isCompact_iff_compactSpace.1 isCompact_Icc
  let qc : C(Icc (0 : ℝ) (2 * π), Circle) := ⟨q, hqc⟩
  have hq : Topology.IsQuotientMap qc := hqc.isClosedMap.isQuotientMap hqc hqs
  have hpq : ∀ s t : Icc 0 (2 * π), q s = q t → p s.1 = p t.1 := fun s t h ↦ by
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h
    have hs := s.2
    have ht := t.2
    have h₁ : (m : ℝ) * (2 * π) ≤ 2 * π := by linarith [hs.1, hs.2, ht.1, ht.2]
    have h₂ : -(2 * π) ≤ (m : ℝ) * (2 * π) := by linarith [hs.1, hs.2, ht.1, ht.2]
    have h₃ : (m : ℝ) ≤ 1 := by nlinarith
    have h₄ : (-1 : ℝ) ≤ m := by nlinarith
    have h₃' : m ≤ 1 := by exact_mod_cast h₃
    have h₄' : -1 ≤ m := by exact_mod_cast h₄
    obtain rfl | rfl | rfl : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    · have hs0 : s.1 = 0 := by push_cast at hm; linarith [hs.1, ht.2]
      have ht1 : t.1 = 2 * π := by push_cast at hm; linarith [hs.1, ht.2]
      rw [hs0, ht1, hp0, hp2]
    · congr 1
      simpa using hm
    · have hs1 : s.1 = 2 * π := by push_cast at hm; linarith [hs.2, ht.1]
      have ht0 : t.1 = 0 := by push_cast at hm; linarith [hs.2, ht.1]
      rw [hs1, ht0, hp0, hp2]
  let Gc : C(Icc (0 : ℝ) (2 * π), c) := ⟨fun t ↦ ⟨p t.1, hmem t.1 t.2⟩, by
    exact (hpc.comp continuous_subtype_val).subtype_mk _⟩
  have hfac : Function.FactorsThrough Gc qc := fun s t h ↦ Subtype.ext (hpq s t h)
  let G : C(Circle, c) := hq.lift Gc hfac
  have hG : ∀ t : Icc (0 : ℝ) (2 * π), G (q t) = ⟨p t.1, hmem t.1 t.2⟩ := fun t ↦ by
    have := DFunLike.congr_fun (hq.lift_comp Gc hfac) t
    exact this
  have hGb : Function.Bijective G := by
    constructor
    · intro x y hxy
      obtain ⟨s', hs'⟩ := Circle.exp_surjective x
      obtain ⟨n, hn⟩ := (existsUnique_add_zsmul_mem_Ico (mul_pos two_pos hpi) s' 0).exists
      rw [zero_add] at hn
      obtain ⟨t', ht'⟩ := Circle.exp_surjective y
      obtain ⟨n', hn'⟩ := (existsUnique_add_zsmul_mem_Ico (mul_pos two_pos hpi) t' 0).exists
      rw [zero_add] at hn'
      have hx : x = q ⟨_, hn.1, hn.2.le⟩ := by
        rw [← hs']
        exact Circle.exp_eq_exp.2 ⟨-n, by simp⟩
      have hy : y = q ⟨_, hn'.1, hn'.2.le⟩ := by
        rw [← ht']
        exact Circle.exp_eq_exp.2 ⟨-n', by simp⟩
      rw [hx, hy] at hxy ⊢
      rw [hG, hG] at hxy
      have := hinj hn hn' (Subtype.ext_iff.1 hxy)
      exact congrArg Circle.exp this
    · rintro ⟨z, hz⟩
      rw [← hun] at hz
      have hsur₁ : ∀ r : unitInterval, ∃ t : Icc (0 : ℝ) (2 * π), p t.1 = u r := fun r ↦ by
        have hm : r.1 * π ∈ Icc 0 π := ⟨mul_nonneg r.2.1 hpi.le, by nlinarith [r.2.2]⟩
        refine ⟨⟨r.1 * π, hm.1, by linarith [hm.2]⟩, ?_⟩
        rw [hp₁ _ hm]
        congr 1
        ext
        simp [hpi']
      have hsur₂ : ∀ r : unitInterval, ∃ t : Icc (0 : ℝ) (2 * π), p t.1 = v r := fun r ↦ by
        rcases eq_or_lt_of_le r.2.2 with h | h
        · have hr : r = 1 := Subtype.ext h
          obtain ⟨t, ht⟩ := hsur₁ 1
          exact ⟨t, by rw [hr, ht, h2.one]⟩
        · have hm : (2 - r.1) * π ∈ Ioc π (2 * π) := ⟨by nlinarith, by nlinarith [r.2.1]⟩
          refine ⟨⟨(2 - r.1) * π, by linarith [hm.1], hm.2⟩, ?_⟩
          rw [hp₂ _ hm]
          congr 1
          ext
          simp [hpi']
      rcases hz with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · obtain ⟨t, ht⟩ := hsur₁ r
        exact ⟨q t, by rw [hG]; exact Subtype.ext ht⟩
      · obtain ⟨t, ht⟩ := hsur₂ r
        exact ⟨q t, by rw [hG]; exact Subtype.ext ht⟩
  have : CompactSpace c := by
    obtain ⟨f₀⟩ := hc
    exact f₀.surjective.compactSpace f₀.continuous
  let f : Circle ≃ₜ c := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hGb)
    G.continuous
  have hf : ∀ t ∈ Icc 0 (2 * π), cuffPoint f t = p t := fun t ht ↦ by
    have := hG ⟨t, ht⟩
    exact congrArg Subtype.val this
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hf 0 ⟨le_rfl, by linarith⟩, hp0]
  · rw [hf π ⟨hpi.le, by linarith⟩, hppi]
  · rw [← hru]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hf t ⟨ht.1, by linarith [ht.2]⟩, hp₁ t ht]
      exact mem_range_self _
    · rintro ⟨r, rfl⟩
      have hm : r.1 * π ∈ Icc 0 π := ⟨mul_nonneg r.2.1 hpi.le, by nlinarith [r.2.2]⟩
      refine ⟨_, hm, ?_⟩
      rw [hf _ ⟨hm.1, by linarith [hm.2]⟩, hp₁ _ hm]
      congr 1
      ext
      simp [hpi']

end GraphMinor.GM19
