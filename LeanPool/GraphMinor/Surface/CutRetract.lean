/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutNull
public import LeanPool.GraphMinor.Surface.PlaneLog
public import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# Pushing a disc minus a point onto its boundary

If a homotopy misses a point of a disc, then we can push it out of the disc onto the boundary. We
use this when an `O`-arc bounds
a disc on one side, to move a null-homotopy to the other side of the `O`-arc. If that side is also a
disc and the homotopy misses
a point of it, then the identity of the circle would be null-homotopic, which is false.

The map that pushes the disc onto the circle is a Möbius map that moves the point to the centre,
then the radial projection, then
the inverse Möbius map.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric
open scoped ComplexConjugate

universe u v

section mobius

/-- A Möbius map of the disc. The map `mob (-a)` moves `a` to `0`, and `mob a` is its inverse. -/
noncomputable def mob (a w : ℂ) : ℂ := (w + a) / (1 + conj a * w)

theorem mob_den_ne {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) : 1 + conj a * w ≠ 0 := by
  intro h
  have h1 : conj a * w = -1 := by linear_combination h
  have h2 : ‖conj a * w‖ = 1 := by
    rw [h1]
    simp
  rw [norm_mul, Complex.norm_conj] at h2
  nlinarith [norm_nonneg a, norm_nonneg w]

theorem norm_mob {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) : ‖mob a w‖ = 1 := by
  have hd := mob_den_ne ha hw.le
  have hww : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    simp
  have e : 1 + conj a * w = w * conj (w + a) := by
    rw [map_add]
    linear_combination -hww
  have h3 : ‖w + a‖ ≠ 0 := by
    intro h
    rw [norm_eq_zero] at h
    rw [e, h, map_zero, mul_zero] at hd
    exact hd rfl
  rw [mob, norm_div, e, norm_mul, hw, one_mul, Complex.norm_conj, div_self h3]

theorem mob_mob {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) : mob a (mob (-a) w) = w := by
  have hd := mob_den_ne (a := -a) (by simpa using ha) hw
  rw [map_neg] at hd
  have h2 : 1 - conj a * a ≠ 0 := by
    have := mob_den_ne (a := -a) (w := a) (by simpa using ha) ha.le
    rwa [map_neg, neg_mul, ← sub_eq_add_neg] at this
  unfold mob
  rw [map_neg]
  generalize conj a = b at *
  have e1 : (w + -a) / (1 + -b * w) + a = w * ((1 - b * a) / (1 + -b * w)) := by
    rw [← mul_div_assoc, eq_div_iff hd, add_mul, div_mul_cancel₀ _ hd]
    ring
  have e2 : 1 + b * ((w + -a) / (1 + -b * w)) = (1 - b * a) / (1 + -b * w) := by
    rw [eq_div_iff hd, add_mul, mul_assoc, div_mul_cancel₀ _ hd]
    ring
  rw [e1, e2, mul_div_assoc, div_self (div_ne_zero h2 hd), mul_one]

theorem contOn_mob {a : ℂ} (ha : ‖a‖ < 1) : ContinuousOn (mob a) (closedBall 0 1) :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => mob_den_ne ha
    (mem_closedBall_zero_iff.mp hw)

theorem mob_neg_ne {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ a) : mob (-a) w ≠ 0 :=
  div_ne_zero (fun h => hne (by linear_combination h)) (mob_den_ne (by simpa using ha) hw)

/-- The map that pushes the disc minus the point `a` onto the circle. -/
noncomputable def retC (a w : ℂ) : ℂ := mob a (mob (-a) w / ‖mob (-a) w‖)

theorem norm_retC {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ a) : ‖retC a w‖ = 1 := by
  refine norm_mob ha ?_
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr
    (mob_neg_ne ha hw hne))]

theorem retC_fix {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) : retC a w = w := by
  have ha' : ‖-a‖ < 1 := by simpa using ha
  rw [retC, norm_mob ha' hw]
  simp only [Complex.ofReal_one, div_one]
  exact mob_mob ha hw.le

theorem contOn_retC {a : ℂ} (ha : ‖a‖ < 1) : ContinuousOn (retC a) (closedBall 0 1 \ {a}) := by
  have ha' : ‖-a‖ < 1 := by simpa using ha
  have h1 : ContinuousOn (mob (-a)) (closedBall 0 1 \ {a}) := (contOn_mob ha').mono sdiff_subset
  have h2 : ContinuousOn (fun w => mob (-a) w / ‖mob (-a) w‖) (closedBall 0 1 \ {a}) := by
    refine h1.div (Complex.continuous_ofReal.comp_continuousOn h1.norm) fun w hw => ?_
    have := mob_neg_ne ha (mem_closedBall_zero_iff.mp hw.1) hw.2
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr this)
  refine (contOn_mob ha).comp h2 fun w hw => ?_
  have := mob_neg_ne ha (mem_closedBall_zero_iff.mp hw.1) hw.2
  rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.mpr this)]

/-- A disc minus an inner point can be pushed onto the boundary. -/
theorem exists_ret {T : Type u} [TopologicalSpace T] (e : T ≃ₜ closedBall (0 : ℂ) 1) {t : T}
  (ht : t ∉ bd T) :
    ∃ R : T → T, ContinuousOn R {t}ᶜ ∧ (∀ x, x ≠ t → R x ∈ bd T) ∧ ∀ x ∈ bd T, R x = x := by
  have hb : ∀ x : T, x ∈ bd T ↔ ‖(e x).1‖ = 1 := by
    intro x
    have h1 := image_bd_homeomorph e
    have h2 := isClosedDisc_closedBall.2
    rw [discBd] at h2
    constructor
    · intro hx
      have h3 : (e x) ∈ bd (closedBall (0 : ℂ) 1) := h1 ▸ mem_image_of_mem _ hx
      have h4 : (e x).1 ∈ sphere (0 : ℂ) 1 := h2 ▸ mem_image_of_mem _ h3
      simpa using h4
    · intro hx
      have h4 : (e x).1 ∈ Subtype.val '' bd (closedBall (0 : ℂ) 1) := h2 ▸ (by simpa using hx)
      obtain ⟨y, hy, he⟩ := h4
      rw [← h1] at hy
      obtain ⟨x', hx', rfl⟩ := hy
      rwa [← e.injective (Subtype.ext he)]
  classical
  have ha : ‖(e t).1‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp (e t).2) (mt (hb t).mpr ht)
  have hne : ∀ x, x ≠ t → (e x).1 ≠ (e t).1 := fun x hx he => hx (e.injective (Subtype.ext he))
  have hn : ∀ x, ‖(e x).1‖ ≤ 1 := fun x => mem_closedBall_zero_iff.mp (e x).2
  have hm : ∀ x (h : x ≠ t), retC (e t).1 (e x).1 ∈ closedBall (0 : ℂ) 1 := fun x h =>
    mem_closedBall_zero_iff.mpr (norm_retC ha (hn x) (hne x h)).le
  let r : T → closedBall (0 : ℂ) 1 := fun x => if h : x = t then e t else ⟨retC (e t).1
    (e x).1, hm x h⟩
  have hr : ∀ x (h : x ≠ t), r x = ⟨retC (e t).1 (e x).1, hm x h⟩ := fun x h
    => by simp only [r, h, dite_false]
  refine ⟨fun x => e.symm (r x), ?_, fun x hx => ?_, fun x hx => ?_⟩
  · refine e.symm.continuous.comp_continuousOn ?_
    rw [IsInducing.subtypeVal.continuousOn_iff]
    have h1 : ContinuousOn (fun x : T => retC (e t).1 (e x).1) {t}ᶜ :=
      (contOn_retC ha).comp (continuous_subtype_val.comp e.continuous).continuousOn fun x hx
        => ⟨(e x).2, hne x hx⟩
    exact h1.congr fun x hx => by
      change (r x).1 = _
      rw [hr x hx]
  · rw [hb, e.apply_symm_apply, hr x hx]
    exact norm_retC ha (hn x) (hne x hx)
  · have hxt : x ≠ t := fun he => ht (he ▸ hx)
    change e.symm (r x) = x
    rw [e.symm_apply_eq, hr x hxt]
    exact Subtype.ext (retC_fix ha ((hb x).mp hx))

end mobius

section circle

/-- The identity map of the circle is not null-homotopic. -/
theorem circle_not_null (G : C(Circle × unitInterval, Circle)) {c : Circle} (h0 : ∀ x, G (x, 0)
  = x) (h1 : ∀ x, G (x, 1) = c) : False := by
  have hc : (c : ℂ) ≠ 0 := Circle.coe_ne_zero c
  let H' : C(unitInterval × Circle, ℂ) := ⟨fun p => (G (p.2, unitInterval.symm p.1) : ℂ) / c, by
    fun_prop⟩
  obtain ⟨g, hg, -⟩ := exists_log_of_homotopy H' (fun a => by simp [H', h1, hc])
    (fun p => div_ne_zero (Circle.coe_ne_zero _) hc)
  let k : sphere (0 : ℂ) 1 → Circle := fun z => ⟨z.1, z.2⟩
  have ck : Continuous k := Continuous.subtype_mk continuous_subtype_val _
  have hL : HasLogOn (sphere (0 : ℂ) 1) fun z => (z - 0) ^ (1 : ℤ) := by
    rw [hasLogOn_iff_subtype]
    refine ⟨⟨fun z => g (1, k z) + Complex.log c, by fun_prop⟩, fun z => ?_⟩
    change _ = Complex.exp (g (1, k z) + Complex.log c)
    rw [Complex.exp_add, hg, Complex.exp_log hc]
    change _ = (G ((k z), unitInterval.symm 1) : ℂ) / c * c
    rw [unitInterval.symm_one, h0, div_mul_cancel₀ _ hc]
    simp [k]
  have := eq_zero_of_hasLogOn_sphere (by norm_num) hL
  omega

end circle

section glue

theorem exists_sec {A : Type u} {S : Type v} [TopologicalSpace A] [CompactSpace A] [Nonempty A]
  [TopologicalSpace S] [T2Space S] {j : A → S}
    (hj : Continuous j) (hi : Function.Injective j) : ∃ s : S → A, ContinuousOn s (range j)
      ∧ ∀ y, s (j y) = y := by
  refine ⟨Function.invFun j, ?_, Function.leftInverse_invFun hi⟩
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨j '' t, (ht.isCompact.image hj).isClosed, ?_⟩
  ext x
  constructor
  · rintro ⟨h1, y, rfl⟩
    rw [mem_preimage, Function.leftInverse_invFun hi] at h1
    exact ⟨mem_image_of_mem _ h1, mem_range_self _⟩
  · rintro ⟨⟨y, h1, rfl⟩, h2⟩
    exact ⟨by rw [mem_preimage, Function.leftInverse_invFun hi]; exact h1, h2⟩

/-- A space is the union of `A₁` and `A₂`, and `A₁` retracts to the common part except at a point.
Then a homotopy that misses the point
moves to `A₂`. -/
theorem retract_two {S : Type u} {A₁ A₂ : Type v} [TopologicalSpace S] [T2Space S]
  [TopologicalSpace A₁] [TopologicalSpace A₂] [CompactSpace A₁] [CompactSpace A₂]
    [Nonempty A₁] [Nonempty A₂] {j₁ : A₁ → S} {j₂ : A₂ → S} (c₁ : Continuous j₁)
      (c₂ : Continuous j₂) (i₁ : Function.Injective j₁) (i₂ : Function.Injective j₂)
    (hu : range j₁ ∪ range j₂ = univ) {B : Set A₁} (hB : ∀ x ∈ B, j₁ x ∈ range j₂)
      (hB' : ∀ x y, j₁ x = j₂ y → x ∈ B) {w : A₁} {R : A₁ → A₁}
    (cR : ContinuousOn R {w}ᶜ) (hR : ∀ x, x ≠ w → R x ∈ B) (hfix : ∀ x ∈ B, R x = x) :
    ∃ g : S → A₂, (∀ y, g (j₂ y) = y) ∧ (∀ x, x ∉ range j₂ → x ≠ j₁ w → j₂ (g x) ∈ j₁ '' B) ∧
      ∀ H : Circle × unitInterval → S, Continuous H → (∀ p, H p ≠ j₁ w) → Continuous (g ∘ H) := by
  classical
  obtain ⟨s₁, cs₁, hs₁⟩ := exists_sec c₁ i₁
  obtain ⟨s₂, cs₂, hs₂⟩ := exists_sec c₂ i₂
  let g : S → A₂ := fun x => if x ∈ range j₂ then s₂ x else s₂ (j₁ (R (s₁ x)))
  have hg₂ : ∀ x ∈ range j₂, g x = s₂ x := fun x hx => ite_eq_left_iff.mpr fun h => absurd hx h
  have hg₁ : ∀ x, x ≠ j₁ w → x ∈ range j₁ → g x = s₂ (j₁ (R (s₁ x))) := by
    rintro _ hne ⟨y, rfl⟩
    by_cases h : j₁ y ∈ range j₂
    · obtain ⟨y', hy'⟩ := h
      rw [hg₂ _ ⟨y', hy'⟩, hs₁, hfix y (hB' y y' hy'.symm)]
    · exact ite_eq_right_iff.mpr fun h' => absurd h' h
  have hns : ∀ x, x ≠ j₁ w → x ∈ range j₁ → s₁ x ≠ w := by
    rintro _ hne ⟨y, rfl⟩ he
    rw [hs₁] at he
    exact hne (he ▸ rfl)
  refine ⟨g, fun y => ?_, fun x h1 h2 => ?_, fun H cH hH => ?_⟩
  · rw [hg₂ _ (mem_range_self y), hs₂]
  · have h3 : x ∈ range j₁ := by
      have : x ∈ range j₁ ∪ range j₂ := hu ▸ mem_univ x
      exact this.resolve_right h1
    have h4 := hR _ (hns x h2 h3)
    obtain ⟨y, hy⟩ := hB _ h4
    rw [hg₁ x h2 h3, ← hy, hs₂, hy]
    exact mem_image_of_mem _ h4
  · have hcl₁ : IsClosed (H ⁻¹' range j₁) := (isCompact_range c₁).isClosed.preimage cH
    have hcl₂ : IsClosed (H ⁻¹' range j₂) := (isCompact_range c₂).isClosed.preimage cH
    have hun : H ⁻¹' range j₁ ∪ H ⁻¹' range j₂ = univ := by
      rw [← preimage_union, hu, preimage_univ]
    rw [← continuousOn_univ, ← hun]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hcl₁ hcl₂
    · have h1 : ContinuousOn (fun p => s₁ (H p)) (H ⁻¹' range j₁) := cs₁.comp cH.continuousOn fun p
        hp => hp
      have h2 : ContinuousOn (fun p => R (s₁ (H p))) (H ⁻¹' range j₁) :=
        cR.comp h1 fun p hp => hns _ (hH p) hp
      have h3 : ContinuousOn (fun p => s₂ (j₁ (R (s₁ (H p))))) (H ⁻¹' range j₁) :=
        cs₂.comp (c₁.comp_continuousOn h2) fun p hp => hB _ (hR _ (hns _ (hH p) hp))
      exact h3.congr fun p hp => hg₁ _ (hH p) hp
    · have h3 : ContinuousOn (fun p => s₂ (H p)) (H ⁻¹' range j₂) := cs₂.comp cH.continuousOn fun p
        hp => hp
      exact h3.congr fun p hp => hg₂ _ hp

end glue

end GraphMinor.Surface
