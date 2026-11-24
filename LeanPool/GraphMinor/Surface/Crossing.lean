/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Janiszewski's theorem and crossing sets in a disc

* `janiszewski`: if the compact sets `K₁, K₂` have a preconnected intersection and neither separates
  `a` from `b`, then their union does not separate `a` from `b`. The two logarithms given by
  Eilenberg's criterion differ by a constant on the intersection, so they paste.
* `IsClosedDisc.exists_chart`: coordinates on a closed disc, with values in the closed unit disc of
  `ℂ`.
* `disc_crossing : DiscCrossingStatement`: compact connected sets in a closed disc whose ends cross
  on the boundary meet. Rotate so that the two ends of `A` lie on a vertical line, with `b` to its
  right and `d` to its left. Let `F` be the frontier of a large half disc to the right of the line,
  so `F` is the chord together with an outer part `R`. Suppose `A` and `B` are disjoint. Then `B`
  joins `b` to `d` off the compact set `A ∪ R`, so `(z - d) / (z - b)` has a logarithm there by
  Eilenberg's criterion. On the closed unit disc minus `{b, d}` this function has an explicit
  logarithm, as both factors lie in a half plane. The two logarithms differ by a constant on the
  connected set `A`, so they paste along `a` and `c` to a logarithm on `F`. So `b` and `d` lie in
  one component of the complement of `F`, which is false since `b` lies in the half disc and `d`
  outside it. The connected set `A` replaces the chord, and no path in `A` is needed.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

universe u

/-- Two logarithms on closed sets with a preconnected intersection differ by a constant there, so
they paste to a logarithm on the union. -/
theorem HasLogOn.union_of_isPreconnected {T : Type u} [TopologicalSpace T] {A B : Set T}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : IsPreconnected (A ∩ B)) {f : T → ℂ}
    (h₁ : HasLogOn A f) (h₂ : HasLogOn B f) : HasLogOn (A ∪ B) f := by
  obtain ⟨gA, cA, eA⟩ := h₁
  obtain ⟨gB, cB, eB⟩ := h₂
  by_cases hne : (A ∩ B).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let c := gA x₀ - gB x₀
    have hexp : ∀ x ∈ A ∩ B, exp (gA x - gB x) = 1 := fun x hx => by
      rw [exp_sub, ← eA x hx.1, ← eB x hx.2]
      have : exp (gB x) ≠ 0 := exp_ne_zero _
      rw [← eB x hx.2] at this
      exact div_self this
    have hc : exp c = 1 := hexp x₀ hx₀
    refine hasLogOn_union (gA := gA) (gB := fun x => gB x + c) hA hB cA
      (cB.add continuousOn_const) eA (fun x hx => ?_) fun x hx => ?_
    · simp only [exp_add, hc, mul_one]
      exact eB x hx
    · have := eq_of_exp_eq_one (g := fun x => gA x - gB x) hAB
        ((cA.mono inter_subset_left).sub (cB.mono inter_subset_right)) hexp hx hx₀
      simp only [c]
      linear_combination this
  · exact hasLogOn_union hA hB cA cB eA eB fun x hx => absurd ⟨x, hx⟩ hne

/-- **Janiszewski's theorem.** If the compact sets `K₁, K₂` have a preconnected intersection and
neither of them separates `a` from `b`, then their union does not separate `a` from `b`. -/
theorem janiszewski {K₁ K₂ : Set ℂ} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hK : IsPreconnected (K₁ ∩ K₂)) {a b : ℂ} (ha : a ∉ K₁ ∪ K₂) (hb : b ∉ K₁ ∪ K₂)
    (hab₁ : b ∈ connectedComponentIn K₁ᶜ a) (hab₂ : b ∈ connectedComponentIn K₂ᶜ a) :
    b ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ a := by
  have l₁ := hasLogOn_div_of_same_component h₁.isClosed (fun h => ha (Or.inl h)) hab₁
  have l₂ := hasLogOn_div_of_same_component h₂.isClosed (fun h => ha (Or.inr h)) hab₂
  have l := (l₁.union_of_isPreconnected h₁.isClosed h₂.isClosed hK (h₂ := l₂)).inv
  have heq := component_eq_of_hasLogOn (h₁.union h₂) ha hb (l.congr fun z _ => by rw [inv_div])
  rw [heq]
  exact mem_connectedComponentIn hb

/-- Coordinates on a closed disc. -/
theorem IsClosedDisc.exists_chart {S : Type u} [TopologicalSpace S] {D : Set S}
    (hD : IsClosedDisc D) : ∃ (h : S → ℂ) (g : ℂ → S),
      ContinuousOn h D ∧ ContinuousOn g (closedBall 0 1) ∧
      MapsTo h D (closedBall 0 1) ∧ MapsTo g (closedBall 0 1) D ∧
      LeftInvOn g h D ∧ RightInvOn g h (closedBall 0 1) ∧ h '' discBd D = sphere 0 1 := by
  classical
  obtain ⟨φ⟩ := id hD
  have hin₀ : complexPlane 0 ∈ ClosedUnitDisc := by
    refine mem_closedBall_zero_iff.mpr ?_
    simp
  have hz₀ : complexPlane 0 ∈ ClosedUnitDisc := hin₀
  have hin : ∀ z : ℂ, z ∈ closedBall (0 : ℂ) 1 → complexPlane z ∈ ClosedUnitDisc := fun z hz => by
    refine mem_closedBall_zero_iff.mpr ?_
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp hz
  have hout : ∀ x : ClosedUnitDisc, complexPlane.symm x.1 ∈ closedBall (0 : ℂ) 1 := fun x => by
    refine mem_closedBall_zero_iff.mpr ?_
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp x.2
  let h : S → ℂ := fun x => if hx : x ∈ D then complexPlane.symm (φ.symm ⟨x, hx⟩).1 else 0
  let g : ℂ → S := fun z => if hz : z ∈ closedBall (0 : ℂ) 1 then (φ ⟨complexPlane z, hin z hz⟩).1
    else (φ ⟨complexPlane 0, hz₀⟩).1
  have hh : ∀ x (hx : x ∈ D), h x = complexPlane.symm (φ.symm ⟨x, hx⟩).1 := fun x hx => by
    simp only [h, hx, dite_true]
  have hgz : ∀ z (hz : z ∈ closedBall (0 : ℂ) 1), g z = (φ ⟨complexPlane z, hin z hz⟩).1 :=
    fun z hz => by simp only [g, hz, dite_true]
  refine ⟨h, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : D.domRestrict h = fun x : D => complexPlane.symm (φ.symm x).1 := by
      ext x
      exact hh x.1 x.2
    rw [this]
    exact complexPlane.symm.continuous.comp (continuous_subtype_val.comp φ.symm.continuous)
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (closedBall (0 : ℂ) 1).domRestrict g =
        fun z : closedBall (0 : ℂ) 1 => (φ ⟨complexPlane z.1, hin z.1 z.2⟩).1 := by
      ext z
      exact hgz z.1 z.2
    rw [this]
    refine continuous_subtype_val.comp (φ.continuous.comp ?_)
    exact Continuous.subtype_mk (complexPlane.continuous.comp continuous_subtype_val) _
  · intro x hx
    rw [hh x hx]
    exact hout _
  · intro z hz
    rw [hgz z hz]
    exact (φ _).2
  · intro x hx
    show g (h x) = x
    rw [hgz _ (by rw [hh x hx]; exact hout _)]
    simp [hh x hx]
  · intro z hz
    show h (g z) = z
    rw [hgz z hz, hh _ (φ _).2]
    simp
  · rw [disc_boundary D φ]
    ext w
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hh _ (φ x).2]
      simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply]
      rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx
    · intro hw
      have hwn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hwb : w ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hw
      refine ⟨_, ⟨⟨complexPlane w, hin w hwb⟩, ?_, rfl⟩, ?_⟩
      · change complexPlane w ∈ UnitCircle
        rw [UnitCircle, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, hwn]
      · rw [hh _ (φ _).2]
        simp

private theorem one_sub_div_mem_slitPlane {z w : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ ≤ 1) (hne : z ≠ w) :
    1 - z / w ∈ slitPlane := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  set q := z / w with hq
  have hqn : ‖q‖ ≤ 1 := by rw [hq, norm_div, hw, div_one]; exact hz
  have hq1 : q ≠ 1 := fun h => hne (by rw [hq, div_eq_one_iff_eq hw0] at h; exact h)
  left
  rw [sub_re, one_re, sub_pos]
  by_contra hge
  rw [not_lt] at hge
  have hsq : q.re * q.re + q.im * q.im ≤ 1 := by
    have h := Complex.sq_norm q
    rw [normSq_apply] at h
    have h2 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg q) hqn
    linarith
  have hre : q.re = 1 := by nlinarith [mul_self_nonneg q.im]
  have him : q.im = 0 := by
    rw [hre] at hsq
    nlinarith [mul_self_nonneg q.im]
  exact hq1 (Complex.ext hre him)

/-- The crossing lemma for a vertical line: compact connected sets in the closed unit disc meet if
the line through the ends of `A` meets the circle only in those ends, and has one end of `B` on
each side. -/
theorem crossing_of_vertical_line {A B : Set ℂ} {a c b d : ℂ} {r : ℝ} (hA : IsCompact A)
    (hAc : IsPreconnected A) (hBc : IsPreconnected B) (hAD : A ⊆ closedBall 0 1)
    (hBD : B ⊆ closedBall 0 1) (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) (hd : d ∈ B)
    (hbn : ‖b‖ = 1) (hdn : ‖d‖ = 1) (hline : ∀ z : ℂ, ‖z‖ = 1 → z.re = r → z = a ∨ z = c)
    (hbr : r < b.re) (hdr : d.re < r) : (A ∩ B).Nonempty := by
  by_contra hcon
  have hdisj : ∀ x ∈ A, x ∉ B := fun x hxA hxB => hcon ⟨x, hxA, hxB⟩
  -- The half disc and its frontier.
  set H : Set ℂ := closedBall 0 2 ∩ {z | r ≤ z.re} with hH
  set F := frontier H with hF
  have hHc : IsClosed H := isClosed_closedBall.inter (isClosed_le continuous_const continuous_re)
  have hHcomp : IsCompact H := (isCompact_closedBall 0 2).inter_right
    (isClosed_le continuous_const continuous_re)
  have hFc : IsCompact F := hHcomp.of_isClosed_subset isClosed_frontier hHc.frontier_subset
  have hFH : F ⊆ H := hHc.frontier_subset
  have hFcase : ∀ z ∈ F, ‖z‖ = 2 ∨ z.re = r := by
    intro z hz
    rcases frontier_inter_subset _ _ hz with h | h
    · left
      have := h.1
      rw [frontier_closedBall (0 : ℂ) (two_ne_zero)] at this
      exact mem_sphere_zero_iff_norm.mp this
    · right
      exact (frontier_le_subset_eq continuous_const continuous_re h.2).symm
  set P := F ∩ closedBall 0 1 with hP
  set R := F ∩ (ball 0 1)ᶜ with hR
  have hPc : IsClosed P := hFc.isClosed.inter isClosed_closedBall
  have hRc : IsCompact R := hFc.inter_right isOpen_ball.isClosed_compl
  have hPR : P ∪ R = F := by
    ext z
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hz : ‖z‖ ≤ 1
      · exact Or.inl ⟨h, mem_closedBall_zero_iff.mpr hz⟩
      · exact Or.inr ⟨h, fun hb => hz (mem_ball_zero_iff.mp hb).le⟩
  have hunit : ∀ z ∈ F, ‖z‖ = 1 → z = a ∨ z = c := by
    intro z hz hn
    rcases hFcase z hz with h | h
    · rw [hn] at h
      norm_num at h
    · exact hline z hn h
  have hPRmeet : ∀ z ∈ P ∩ R, z = a ∨ z = c := by
    rintro z ⟨⟨hzF, hz1⟩, -, hz2⟩
    refine hunit z hzF (le_antisymm (mem_closedBall_zero_iff.mp hz1) ?_)
    exact not_lt.mp fun h => hz2 (mem_ball_zero_iff.mpr h)
  have hRB : ∀ z ∈ R, z ∉ B := by
    rintro z ⟨hzF, hz2⟩ hzB
    have hn : ‖z‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp (hBD hzB))
      (not_lt.mp fun h => hz2 (mem_ball_zero_iff.mpr h))
    rcases hunit z hzF hn with rfl | rfl
    · exact hdisj _ ha hzB
    · exact hdisj _ hc hzB
  -- `B` joins `b` to `d` off `A ∪ R`.
  have hTc : IsCompact (A ∪ R) := hA.union hRc
  have hBT : B ⊆ (A ∪ R)ᶜ := by
    rintro z hz (h | h)
    · exact hdisj z h hz
    · exact hRB z h hz
  have hdcomp : d ∈ connectedComponentIn (A ∪ R)ᶜ b :=
    hBc.subset_connectedComponentIn hb hBT hd
  obtain ⟨g₁, hg₁c, hg₁⟩ := hasLogOn_div_of_same_component hTc.isClosed (hBT hb) hdcomp
  -- The explicit logarithm on the closed disc minus `{b, d}`.
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbn
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hdn
  set D' := closedBall (0 : ℂ) 1 \ {b, d} with hD'
  have hu : HasLogOn D' fun z => 1 - z / d := by
    refine hasLogOn_of_slitPlane (by fun_prop) fun z hz => ?_
    exact one_sub_div_mem_slitPlane hdn (mem_closedBall_zero_iff.mp hz.1)
      fun h => hz.2 (Or.inr h)
  have hv : HasLogOn D' fun z => 1 - z / b := by
    refine hasLogOn_of_slitPlane (by fun_prop) fun z hz => ?_
    exact one_sub_div_mem_slitPlane hbn (mem_closedBall_zero_iff.mp hz.1)
      fun h => hz.2 (Or.inl h)
  have hconst : HasLogOn D' fun _ => b / d := hasLogOn_const (div_ne_zero hb0 hd0)
  have hL : HasLogOn D' fun z => (z - d) / (z - b) := by
    refine ((hu.div hv).mul ((hconst.inv))).congr fun z hz => ?_
    have h1 : z - b ≠ 0 := fun h => hz.2 (Or.inl (sub_eq_zero.mp h))
    have e1 : 1 - z / d = -(z - d) / d := by field_simp; ring
    have e2 : 1 - z / b = -(z - b) / b := by field_simp; ring
    simp only [e1, e2]
    field_simp
  obtain ⟨g₂, hg₂c, hg₂⟩ := hL
  have hAD' : A ⊆ D' := fun x hx => ⟨hAD hx, by
    rintro (h | h)
    · exact hdisj x hx (h ▸ hb)
    · exact hdisj x hx (h ▸ hd)⟩
  have hPD' : P ⊆ D' := by
    refine fun z hz => ⟨hz.2, ?_⟩
    rintro (h | h)
    · rcases hFcase z hz.1 with h' | h'
      · rw [h, hbn] at h'
        norm_num at h'
      · rw [h] at h'
        linarith
    · have := (hFH hz.1).2
      rw [h] at this
      exact absurd this (not_le.mpr hdr)
  -- The two logarithms differ by a constant on `A`.
  have hnz : ∀ x ∈ A, (x - d) / (x - b) ≠ 0 := by
    intro x hx
    have := hg₂ x (hAD' hx)
    simp only at this
    rw [this]
    exact exp_ne_zero _
  have hexp : ∀ x ∈ A, exp (g₁ x - g₂ x) = 1 := by
    intro x hx
    rw [exp_sub, ← hg₁ x (Or.inl hx), ← hg₂ x (hAD' hx)]
    exact div_self (hnz x hx)
  have hdiffc : ContinuousOn (fun x => g₁ x - g₂ x) A :=
    (hg₁c.mono subset_union_left).sub (hg₂c.mono hAD')
  have hconstant : ∀ x ∈ A, g₁ x - g₂ x = g₁ a - g₂ a := fun x hx =>
    eq_of_exp_eq_one hAc hdiffc hexp hx ha
  set k := g₁ a - g₂ a with hk
  have hkexp : exp k = 1 := hexp a ha
  have hlogF : HasLogOn F fun z => (z - d) / (z - b) := by
    rw [← hPR]
    refine hasLogOn_union (gA := fun z => g₂ z + k) (gB := g₁) hPc hRc.isClosed
      ((hg₂c.mono hPD').add continuousOn_const) (hg₁c.mono subset_union_right) (fun z hz => ?_)
      (fun z hz => hg₁ z (Or.inr hz)) fun z hz => ?_
    · rw [exp_add, hkexp, mul_one]
      exact hg₂ z (hPD' hz)
    · have hzA : z ∈ A := by
        rcases hPRmeet z hz with rfl | rfl
        · exact ha
        · exact hc
      have := hconstant z hzA
      linear_combination -this
  have hbH : b ∈ H := ⟨mem_closedBall_zero_iff.mpr (by rw [hbn]; norm_num), hbr.le⟩
  have hdH : d ∉ H := fun h => absurd h.2 (not_le.mpr hdr)
  have hbF : b ∉ F := by
    intro h
    rcases hFcase b h with h' | h'
    · rw [hbn] at h'
      norm_num at h'
    · linarith
  have hdF : d ∉ F := fun h => hdH (hFH h)
  have heq := component_eq_of_hasLogOn hFc hdF hbF hlogF
  have hbin : b ∈ connectedComponentIn Fᶜ d := heq ▸ mem_connectedComponentIn hbF
  have hmeet := inter_frontier_nonempty_of_isPreconnected (U := H)
    (isPreconnected_connectedComponentIn (F := Fᶜ) (x := d)) ⟨b, hbin, hbH⟩
    ⟨d, mem_connectedComponentIn hdF, hdH⟩
  obtain ⟨z, hz1, hz2⟩ := hmeet
  exact connectedComponentIn_subset _ _ hz1 hz2

/-- Every unit complex number is `exp (θ i)` for some `θ` in `[0, 2π)`. -/
private theorem exists_angle {w : ℂ} (hw : ‖w‖ = 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧ w = exp (θ * I) := by
  have hrep : w = exp (w.arg * I) := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at this
    simpa using this.symm
  by_cases h : 0 ≤ w.arg
  · exact ⟨w.arg, h, by linarith [arg_le_pi w, Real.pi_pos], hrep⟩
  · rw [not_le] at h
    refine ⟨w.arg + 2 * Real.pi, by linarith [neg_pi_lt_arg w], by linarith, ?_⟩
    push_cast
    rw [add_mul, exp_add, exp_two_pi_mul_I, mul_one]
    exact hrep

private theorem cos_lt_of_inside {θ δ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * δ) (hδ : δ < Real.pi) :
    Real.cos δ < Real.cos (θ - δ) := by
  rw [← Real.cos_abs (θ - δ)]
  refine Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hδ.le ?_
  rw [abs_lt]
  constructor <;> linarith

private theorem cos_lt_of_outside {θ δ : ℝ} (hδ0 : 0 < δ) (_hδ : δ < Real.pi) (h1 : 2 * δ < θ)
    (h2 : θ < 2 * Real.pi) : Real.cos (θ - δ) < Real.cos δ := by
  by_cases hx : θ - δ ≤ Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hδ0.le hx (by linarith)
  · have : Real.cos (θ - δ) = Real.cos (2 * Real.pi - (θ - δ)) := by
      rw [Real.cos_two_pi_sub]
    rw [this]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hδ0.le (by linarith) (by linarith)

/-- The crossing lemma on the unit circle of `ℂ`. -/
theorem crossing_unit {A B : Set ℂ} {a c b d : ℂ} (hA : IsCompact A)
    (hAc : IsPreconnected A) (hBc : IsPreconnected B) (hAD : A ⊆ closedBall 0 1)
    (hBD : B ⊆ closedBall 0 1) (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) (hd : d ∈ B)
    (han : ‖a‖ = 1) (hcn : ‖c‖ = 1) (hbn : ‖b‖ = 1) (hdn : ‖d‖ = 1) (hac : a ≠ c)
    (hba : b ≠ a) (hbc : b ≠ c) (hda : d ≠ a) (hdc : d ≠ c)
    (hcomp : connectedComponentIn (sphere 0 1 \ {a, c}) b ≠
      connectedComponentIn (sphere 0 1 \ {a, c}) d) : (A ∩ B).Nonempty := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at han
  have hdiv : ∀ {w : ℂ}, ‖w‖ = 1 → ‖w / a‖ = 1 := fun hw => by rw [norm_div, hw, han, div_one]
  -- The angle `2 δ` from `a` to `c`.
  obtain ⟨θc, hθ0, hθ1, hθc⟩ := exists_angle (hdiv hcn)
  let e : ℝ → ℂ := fun θ => a * exp (θ * I)
  have hee : ∀ {w : ℂ}, w / a = exp (0 : ℂ) → w = a := fun {w} h => by
    rw [exp_zero, div_eq_one_iff_eq ha0] at h
    exact h
  have hθpos : 0 < θc := by
    refine lt_of_le_of_ne hθ0 fun h => hac ?_
    rw [← h] at hθc
    exact (hee (by simpa using hθc)).symm
  set δ := θc / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδπ : δ < Real.pi := by rw [hδ]; linarith
  have hce : c = e (2 * δ) := by
    have : (2 * δ : ℝ) = θc := by rw [hδ]; ring
    simp only [e, this, ← hθc]
    field_simp
  have hae : a = e 0 := by simp [e]
  let u : ℂ := a⁻¹ * exp (((-δ : ℝ) : ℂ) * I)
  have hun : ‖u‖ = 1 := by
    rw [norm_mul, norm_inv, han, Complex.norm_exp_ofReal_mul_I]
    simp
  let ρ : ℂ → ℂ := fun z => z * u
  have hρc : Continuous ρ := by fun_prop
  have hρn : ∀ z, ‖ρ z‖ = ‖z‖ := fun z => by simp only [ρ, norm_mul, hun, mul_one]
  have hρe : ∀ θ : ℝ, ρ (e θ) = exp (((θ - δ : ℝ) : ℂ) * I) := by
    intro θ
    simp only [ρ, e, u]
    push_cast
    rw [show ((θ : ℂ) - δ) * I = (θ : ℂ) * I + (-δ : ℂ) * I by ring, exp_add]
    field_simp
  have hρre : ∀ θ : ℝ, (ρ (e θ)).re = Real.cos (θ - δ) := fun θ => by
    rw [hρe, exp_ofReal_mul_I_re]
  have hρa : (ρ a).re = Real.cos δ := by
    rw [hae, hρre, zero_sub, Real.cos_neg]
  have hρc' : (ρ c).re = Real.cos δ := by
    rw [hce, hρre]
    congr 1
    ring
  have hρimage : ∀ {K : Set ℂ}, K ⊆ closedBall 0 1 → ρ '' K ⊆ closedBall 0 1 := by
    rintro K hK _ ⟨z, hz, rfl⟩
    rw [mem_closedBall_zero_iff, hρn]
    exact mem_closedBall_zero_iff.mp (hK hz)
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have hu0 : u ≠ 0 := by
      intro h
      simp [h] at hun
    exact mul_right_cancel₀ hu0 hxy
  -- Points of the two open arcs.
  have hcase : ∀ {z : ℂ}, ‖z‖ = 1 → z ≠ a → z ≠ c →
      ∃ θ : ℝ, z = e θ ∧ ((0 < θ ∧ θ < 2 * δ) ∨ (2 * δ < θ ∧ θ < 2 * Real.pi)) := by
    intro z hz hza hzc
    obtain ⟨θ, h0, h1, hθ⟩ := exists_angle (hdiv hz)
    have hze : z = e θ := by
      simp only [e, ← hθ]
      field_simp
    refine ⟨θ, hze, ?_⟩
    have hne0 : θ ≠ 0 := fun h => hza (by rw [hze, h, ← hae])
    have hne1 : θ ≠ 2 * δ := fun h => hzc (by rw [hze, h, ← hce])
    rcases lt_or_gt_of_ne hne1 with h | h
    · exact Or.inl ⟨lt_of_le_of_ne h0 hne0.symm, h⟩
    · exact Or.inr ⟨h, h1⟩
  have hen : ∀ θ : ℝ, ‖e θ‖ = 1 := fun θ => by
    simp only [e, norm_mul, han, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hmem : ∀ θ : ℝ, Real.cos (θ - δ) ≠ Real.cos δ → e θ ∈ sphere (0 : ℂ) 1 \ {a, c} := by
    intro θ hθ
    refine ⟨mem_sphere_zero_iff_norm.mpr (hen θ), ?_⟩
    rintro (h | h)
    · exact hθ (by rw [← hρre, h, hρa])
    · exact hθ (by rw [← hρre, h, hρc'])
  have heq_of_mem : ∀ {C : Set ℂ}, IsPreconnected C → C ⊆ sphere (0 : ℂ) 1 \ {a, c} → b ∈ C →
      d ∈ C → False := by
    intro C hC hsub hbC hdC
    apply hcomp
    have h1 := hC.subset_connectedComponentIn hbC hsub hdC
    exact (connectedComponentIn_eq h1)
  have heC : Continuous e := by fun_prop
  have hcpre : ∀ x y : ℝ, IsPreconnected (e '' Ioo x y) := fun x y =>
    isPreconnected_Ioo.image _ heC.continuousOn
  -- The line through the images of the ends of `A`.
  have hline : ∀ z : ℂ, ‖z‖ = 1 → z.re = Real.cos δ → z = ρ a ∨ z = ρ c := by
    intro z hz hre
    have hρa' : ρ a = exp (((-δ : ℝ) : ℂ) * I) := by
      rw [hae, hρe]
      congr 3
      ring
    have hρc'' : ρ c = exp ((δ : ℂ) * I) := by
      rw [hce, hρe]
      congr 3
      ring_nf
    have hsq : z.im * z.im = Real.sin δ * Real.sin δ := by
      have h1 := Complex.sq_norm z
      rw [normSq_apply, hz, hre] at h1
      have h2 := Real.sin_sq_add_cos_sq δ
      nlinarith
    have hfac : (z.im - Real.sin δ) * (z.im + Real.sin δ) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · right
      rw [hρc'']
      refine Complex.ext ?_ ?_
      · rw [hre, exp_ofReal_mul_I_re]
      · rw [exp_ofReal_mul_I_im]
        linarith
    · left
      rw [hρa']
      refine Complex.ext ?_ ?_
      · rw [hre, exp_ofReal_mul_I_re, Real.cos_neg]
      · rw [exp_ofReal_mul_I_im, Real.sin_neg]
        linarith
  have hfinal : ∀ {b' d' : ℂ}, b' ∈ B → d' ∈ B → ‖b'‖ = 1 → ‖d'‖ = 1 →
      Real.cos δ < (ρ b').re → (ρ d').re < Real.cos δ → (A ∩ B).Nonempty := by
    intro b' d' hb' hd' hb'n hd'n h1 h2
    have := crossing_of_vertical_line (hA.image hρc) (hAc.image _ hρc.continuousOn)
      (hBc.image _ hρc.continuousOn) (hρimage hAD) (hρimage hBD)
      (mem_image_of_mem ρ ha) (mem_image_of_mem ρ hc) (mem_image_of_mem ρ hb')
      (mem_image_of_mem ρ hd') (by rw [hρn, hb'n]) (by rw [hρn, hd'n]) hline h1 h2
    obtain ⟨_, ⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := this
    exact ⟨x, hx, hρinj hxy ▸ hy⟩
  obtain ⟨θb, hbe, hθb⟩ := hcase hbn hba hbc
  obtain ⟨θd, hde, hθd⟩ := hcase hdn hda hdc
  rcases hθb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> rcases hθd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
  · exfalso
    refine heq_of_mem (hcpre 0 (2 * δ)) ?_ ⟨θb, ⟨hb1, hb2⟩, hbe.symm⟩ ⟨θd, ⟨hd1, hd2⟩, hde.symm⟩
    rintro _ ⟨θ, hθ, rfl⟩
    exact hmem θ (cos_lt_of_inside hθ.1 hθ.2 hδπ).ne'
  · refine hfinal hb hd hbn hdn ?_ ?_
    · rw [hbe, hρre]
      exact cos_lt_of_inside hb1 hb2 hδπ
    · rw [hde, hρre]
      exact cos_lt_of_outside hδ0 hδπ hd1 hd2
  · refine hfinal hd hb hdn hbn ?_ ?_
    · rw [hde, hρre]
      exact cos_lt_of_inside hd1 hd2 hδπ
    · rw [hbe, hρre]
      exact cos_lt_of_outside hδ0 hδπ hb1 hb2
  · exfalso
    refine heq_of_mem (hcpre (2 * δ) (2 * Real.pi)) ?_ ⟨θb, ⟨hb1, hb2⟩, hbe.symm⟩
      ⟨θd, ⟨hd1, hd2⟩, hde.symm⟩
    rintro _ ⟨θ, hθ, rfl⟩
    exact hmem θ (cos_lt_of_outside hδ0 hδπ hθ.1 hθ.2).ne

/-- **Crossing sets in a disc.** Two compact connected sets in a closed disc meet if their ends
cross on the boundary. Graph Minors VI, Sections 2 and 3; Graph Minors IX, Section 1. The route is
Eilenberg's criterion, as described in the module docstring. -/
theorem disc_crossing : DiscCrossingStatement.{u} := by
  intro S _ D A B a c b d hD hAD hBD hA _ hAc hBc ha hc hb hd hcross
  obtain ⟨ha', hb', hc', hd', hac, hbd, hab, had, hcb, hcd, hcomp⟩ := hcross
  obtain ⟨h, g, hh, hg, hhm, hgm, hgh, hhg, hbdh⟩ := hD.exists_chart
  have hsub : discBd D ⊆ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcirc : ∀ {x}, x ∈ discBd D → ‖h x‖ = 1 := fun hx =>
    mem_sphere_zero_iff_norm.mp (hbdh ▸ mem_image_of_mem h hx)
  have hhinj : InjOn h D := fun x hx y hy hxy => by
    rw [← hgh hx, ← hgh hy]
    show g (h x) = g (h y)
    rw [hxy]
  have hne : ∀ {x y}, x ∈ discBd D → y ∈ discBd D → x ≠ y → h x ≠ h y := fun hx hy hxy e =>
    hxy (hhinj (hsub hx) (hsub hy) e)
  have himage : ∀ {K : Set S}, K ⊆ D → h '' K ⊆ closedBall 0 1 := by
    rintro K hK _ ⟨x, hx, rfl⟩
    exact hhm (hK hx)
  have hmain := crossing_unit (hA.image_of_continuousOn (hh.mono hAD))
    (hAc.isPreconnected.image _ (hh.mono hAD))
    (hBc.isPreconnected.image _ (hh.mono hBD)) (himage hAD) (himage hBD)
    (mem_image_of_mem h ha) (mem_image_of_mem h hc) (mem_image_of_mem h hb)
    (mem_image_of_mem h hd) (hcirc ha') (hcirc hc') (hcirc hb') (hcirc hd') (hne ha' hc' hac)
    (hne hb' ha' hab.symm) (hne hb' hc' hcb.symm) (hne hd' ha' had.symm) (hne hd' hc' hcd.symm)
    ?_
  · obtain ⟨_, ⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := hmain
    exact ⟨x, hx, hhinj (hBD hy) (hAD hx) hxy ▸ hy⟩
  · intro heq
    apply hcomp
    set C := sphere (0 : ℂ) 1 \ {h a, h c} with hC
    have hhbC : h b ∈ C := ⟨mem_sphere_zero_iff_norm.mpr (hcirc hb'), by
      rintro (e | e)
      · exact hne hb' ha' hab.symm e
      · exact hne hb' hc' hcb.symm e⟩
    have hhdC : h d ∈ C := ⟨mem_sphere_zero_iff_norm.mpr (hcirc hd'), by
      rintro (e | e)
      · exact hne hd' ha' had.symm e
      · exact hne hd' hc' hcd.symm e⟩
    have hdin : h d ∈ connectedComponentIn C (h b) := heq ▸ mem_connectedComponentIn hhdC
    have hgC : ∀ z ∈ C, g z ∈ discBd D \ {a, c} := by
      rintro z ⟨hz, hzne⟩
      obtain ⟨y, hy, rfl⟩ : z ∈ h '' discBd D := hbdh ▸ hz
      rw [hgh (hsub hy)]
      refine ⟨hy, ?_⟩
      rintro (e | e)
      · exact hzne (Or.inl (by rw [e]))
      · exact hzne (Or.inr (by rw [e]; exact mem_singleton _))
    have hgcont : ContinuousOn g C :=
      hg.mono (sdiff_subset.trans sphere_subset_closedBall)
    have hpre : IsPreconnected (g '' connectedComponentIn C (h b)) :=
      isPreconnected_connectedComponentIn.image _ (hgcont.mono (connectedComponentIn_subset _ _))
    have hsubC : g '' connectedComponentIn C (h b) ⊆ discBd D \ {a, c} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hgC z (connectedComponentIn_subset _ _ hz)
    have hbin : b ∈ g '' connectedComponentIn C (h b) :=
      ⟨h b, mem_connectedComponentIn hhbC, hgh (hsub hb')⟩
    have hdin' : d ∈ g '' connectedComponentIn C (h b) := ⟨h d, hdin, hgh (hsub hd')⟩
    exact connectedComponentIn_eq (hpre.subset_connectedComponentIn hbin hsubC hdin')

end GraphMinor.Surface
