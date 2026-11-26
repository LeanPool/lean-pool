/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.MoveCuff
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Loops on a cuff

We write the circle as the real line modulo the integers, through `ee`. A strictly increasing map
`τ` of `[0, 1]` with
`τ 1 = τ 0 + 1` is a homeomorphism of the circle that preserves the orientation
(`exists_circle_homeo`). So, by
`move_cuff`, a cuff can be moved along such a map (`exists_move_loop`). A loop that goes once around
a cuff gives a
homeomorphism from the circle (`exists_circle_param`), and any line in the cuff lifts to a monotone
map into the real
line (`exists_lift`, `lift_mono`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe u

/-- The real line onto the circle, with period one. -/
noncomputable def ee (x : ℝ) : Circle := Circle.exp (2 * Real.pi * x)

theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

theorem ee_eq_iff {x y : ℝ} : ee x = ee y ↔ ∃ m : ℤ, x = y + m := by
  have hpi := Real.pi_pos
  unfold ee
  rw [Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have : 2 * Real.pi * x = 2 * Real.pi * (y + m) := by rw [hm]; ring
    exact mul_left_cancel₀ (by positivity) this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

theorem ee_add_int (x : ℝ) (m : ℤ) : ee (x + m) = ee x := ee_eq_iff.mpr ⟨m, rfl⟩

theorem ee_add_one (x : ℝ) : ee (x + 1) = ee x := by
  simpa using ee_add_int x 1

theorem ee_surjective : Surjective ee := fun z => by
  have hpi := Real.pi_pos
  refine ⟨Complex.arg z / (2 * Real.pi), ?_⟩
  unfold ee
  rw [mul_div_cancel₀ _ (by positivity)]
  exact Circle.exp_arg z

theorem isQuotientMap_ee : IsQuotientMap ee := by
  have hpi := Real.pi_pos
  have h1 : IsQuotientMap Circle.exp := Circle.isCoveringMap_exp.isQuotientMap fun z
    => ⟨_, Circle.exp_arg z⟩
  have h2 : IsQuotientMap fun x : ℝ => 2 * Real.pi * x :=
    (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity)).isQuotientMap
  exact h1.comp h2

/-- A continuous map of period one factors through the circle. -/
theorem exists_circle_descend {Y : Type*} [TopologicalSpace Y] {g : ℝ → Y} (hc : Continuous g)
    (hp : ∀ x, g (x + 1) = g x) : ∃ G : Circle → Y, Continuous G ∧ ∀ x, G (ee x) = g x := by
  have hn : ∀ (m : ℤ) x, g (x + m) = g x := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ n ih =>
      intro x
      have := hp (x + n)
      push_cast at ih ⊢
      rw [← add_assoc, this, ih]
    | pred n ih =>
      intro x
      have := hp (x - n - 1)
      push_cast at ih ⊢
      rw [sub_add_cancel] at this
      have e : x + (-(n : ℝ) - 1) = x - n - 1 := by ring
      rw [e, ← this]
      have e2 := ih x
      rw [← sub_eq_add_neg] at e2
      exact e2
  let G' : C(ℝ, Y) := ⟨g, hc⟩
  let E : C(ℝ, Circle) := ⟨ee, continuous_ee⟩
  have hq : IsQuotientMap E := isQuotientMap_ee
  have hf : Function.FactorsThrough G' E := fun a b he => by
    obtain ⟨m, rfl⟩ := ee_eq_iff.mp he
    exact hn m b
  refine ⟨hq.lift G' hf, (hq.lift G' hf).continuous, fun x => ?_⟩
  exact congrArg (fun h : C(ℝ, Y) => h x) (hq.lift_comp G' hf)

theorem fract_of_mem_Ico {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) : Int.fract u = u
  := Int.fract_eq_iff.mpr ⟨hu.1, hu.2, 0, by simp⟩

/-- A loop that goes once around a set gives a homeomorphism from the circle. -/
theorem exists_circle_param {T : Type*} [TopologicalSpace T] [T2Space T] {ρ : ℝ → T}
  (hc : ContinuousOn ρ (Icc 0 1))
    (hi : InjOn ρ (Ico 0 1)) (h01 : ρ 0 = ρ 1) :
    ∃ φ : Circle ≃ₜ (ρ '' Icc 0 1 : Set T), ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee u)).1 = ρ u := by
  classical
  have hg : Continuous (ρ ∘ Int.fract) := ContinuousOn.comp_fract'' hc h01
  obtain ⟨G, hG, hval⟩ := exists_circle_descend hg fun x => by simp
  have hfr : ∀ u ∈ Icc (0 : ℝ) 1, ρ (Int.fract u) = ρ u := fun u hu => by
    rcases eq_or_lt_of_le hu.2 with rfl | h
    · simpa using h01
    · rw [fract_of_mem_Ico ⟨hu.1, h⟩]
  have hmem : ∀ z, G z ∈ ρ '' Icc 0 1 := fun z => by
    obtain ⟨x, rfl⟩ := ee_surjective z
    rw [hval]
    exact ⟨Int.fract x, ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, rfl⟩
  let G₁ : Circle → (ρ '' Icc 0 1 : Set T) := fun z => ⟨G z, hmem z⟩
  have hG₁ : Continuous G₁ := hG.subtype_mk hmem
  have hinj : Injective G₁ := fun z w he => by
    obtain ⟨x, rfl⟩ := ee_surjective z
    obtain ⟨y, rfl⟩ := ee_surjective w
    have h1 : G (ee x) = G (ee y) := congrArg Subtype.val he
    rw [hval, hval] at h1
    have h2 := hi ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
      h1
    refine ee_eq_iff.mpr ⟨⌊x⌋ - ⌊y⌋, ?_⟩
    have h3 := Int.floor_add_fract x
    have h4 := Int.floor_add_fract y
    push_cast
    linarith
  have hsurj : Surjective G₁ := by
    rintro ⟨_, u, hu, rfl⟩
    refine ⟨ee u, Subtype.ext ?_⟩
    change G (ee u) = ρ u
    rw [hval]
    exact hfr u hu
  refine ⟨hG₁.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G₁ ⟨hinj, hsurj⟩), fun u hu => ?_⟩
  change G (ee u) = ρ u
  rw [hval]
  exact hfr u hu

/-- A strictly increasing map of `[0, 1]` that gains one is a homeomorphism of the circle that
preserves the orientation. -/
theorem exists_circle_homeo {τ : ℝ → ℝ} (hc : ContinuousOn τ (Icc 0 1)) (hm : StrictMonoOn τ
  (Icc 0 1)) (h1 : τ 1 = τ 0 + 1) :
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧ ∀ u ∈ Icc (0 : ℝ) 1, h (ee u) = ee (τ u)
      := by
  have hpi := Real.pi_pos
  let g : ℝ → ℝ := fun y => τ y - y
  have hgc : Continuous (g ∘ Int.fract) := ContinuousOn.comp_fract'' (hc.sub continuousOn_id)
    (by simp [g, h1])
  let t : ℝ → ℝ := fun x => x + g (Int.fract x)
  have ht : Continuous t := continuous_id.add hgc
  have ht1 : ∀ x, t (x + 1) = t x + 1 := fun x => by simp [t]; ring
  have hform : ∀ x, t x = ⌊x⌋ + τ (Int.fract x) := fun x => by
    simp only [t, g]
    have := Int.floor_add_fract x
    linarith
  have hfm : ∀ x, Int.fract x ∈ Icc (0 : ℝ) 1 := fun x => ⟨Int.fract_nonneg x,
    (Int.fract_lt_one x).le⟩
  have hmono : StrictMono t := by
    intro x y hxy
    rw [hform, hform]
    have hle : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy.le
    rcases eq_or_lt_of_le hle with he | hl
    · have h2 : Int.fract x < Int.fract y := by
        have h3 := Int.floor_add_fract x
        have h4 := Int.floor_add_fract y
        rw [he] at h3
        linarith
      rw [he]
      have := hm (hfm x) (hfm y) h2
      linarith
    · have h2 : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ ⌊y⌋ := by exact_mod_cast hl
      push_cast at h2
      have h3 := hm (hfm x) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (Int.fract_lt_one x)
      have h4 := hm.monotoneOn (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (hfm y) (Int.fract_nonneg y)
      linarith
  have hint : ∀ m : ℤ, t m = m + τ 0 := fun m => by
    rw [hform]
    simp
  have hsurj : Surjective t := fun y => by
    set k := ⌊y - τ 0⌋ with hk
    have h2 : (k : ℝ) ≤ y - τ 0 := Int.floor_le _
    have h3 : y - τ 0 < k + 1 := Int.lt_floor_add_one _
    have h4 := hint k
    have h5 := ht1 (k : ℝ)
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc (show (k : ℝ) ≤ k + 1 by linarith) ht.continuousOn
      (show y ∈ Icc (t k) (t (k + 1)) by
        rw [h5, h4]
        exact ⟨by linarith, by linarith⟩)
    exact ⟨x, hx⟩
  let e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective t hsurj
  have he : ∀ x, e x = t x := fun _ => rfl
  have hs1 : ∀ x, e.symm (x + 1) = e.symm x + 1 := fun x => by
    apply e.injective
    rw [e.apply_symm_apply, he (e.symm x + 1), ht1, ← he, e.apply_symm_apply]
  obtain ⟨H, hH, hH1⟩ := exists_circle_descend (g := fun x => ee (t x))
    (continuous_ee.comp ht) fun x => by
    simp only [ht1, ee_add_one]
  obtain ⟨H', hH', hH1'⟩ := exists_circle_descend (g := fun x => ee (e.symm x))
    (continuous_ee.comp e.symm.continuous) fun x => by simp only [hs1, ee_add_one]
  let h : Circle ≃ₜ Circle :=
    { toFun := H
      invFun := H'
      left_inv := fun z => by
        obtain ⟨x, rfl⟩ := ee_surjective z
        simp only [hH1, hH1']
        rw [← he, e.symm_apply_apply]
      right_inv := fun z => by
        obtain ⟨x, rfl⟩ := ee_surjective z
        simp only [hH1, hH1']
        rw [← he, e.apply_symm_apply]
      continuous_toFun := hH
      continuous_invFun := hH' }
  refine ⟨h, ⟨fun x => 2 * Real.pi * t (x / (2 * Real.pi)), by fun_prop, ?_, ?_⟩, fun u hu => ?_⟩
  · intro x y hxy
    have := hmono (div_lt_div_of_pos_right hxy (show 0 < 2 * Real.pi by positivity))
    simp only
    nlinarith
  · intro x
    have h2 : H (Circle.exp x) = ee (t (x / (2 * Real.pi))) := by
      have h3 : Circle.exp x = ee (x / (2 * Real.pi)) := by
        unfold ee
        rw [mul_div_cancel₀ _ (by positivity)]
      rw [h3, hH1]
    exact h2
  · change H (ee u) = ee (τ u)
    rw [hH1]
    rcases eq_or_lt_of_le hu.2 with rfl | h2
    · have := hform 1
      simp only [Int.floor_one, Int.fract_one, Int.cast_one] at this
      rw [this, h1, add_comm]
    · have := hform u
      rw [fract_of_mem_Ico ⟨hu.1, h2⟩, Int.floor_eq_zero_iff.mpr ⟨hu.1, h2⟩] at this
      simp only [Int.cast_zero, zero_add] at this
      rw [this]

/-- A cuff moves along a strictly increasing map of `[0, 1]` that gains one. -/
theorem exists_move_loop {S : Type u} [TopologicalSpace S] (hS : IsSurface S) {C U : Set S}
  (hC : IsCuff C) (hU : IsOpen U)
    (hCU : C ⊆ U) (φ : Circle ≃ₜ C) {τ : ℝ → ℝ} (hc : ContinuousOn τ (Icc 0 1))
      (hm : StrictMonoOn τ (Icc 0 1))
    (h1 : τ 1 = τ 0 + 1) :
    ∃ α : S ≃ₜ S, (∀ u ∈ Icc (0 : ℝ) 1, α (φ (ee u)).1 = (φ (ee (τ u))).1) ∧ ∀ x ∉ U, α x = x := by
  obtain ⟨h, h2, h3⟩ := exists_circle_homeo hc hm h1
  obtain ⟨α, h4, h5⟩ := move_cuff S C U φ h hS hC hU hCU h2
  exact ⟨α, fun u hu => by rw [h4, h3 u hu], h5⟩

/-- A path in a circle lifts to the real line. -/
theorem exists_lift {T : Type*} [TopologicalSpace T] {C : Set T} (φ : Circle ≃ₜ C) {η : ℝ → T}
    (hc : ContinuousOn η (Icc 0 1)) (hη : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ C) :
    ∃ m : ℝ → ℝ, ContinuousOn m (Icc 0 1) ∧ ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee (m u))).1 = η u := by
  have hpi := Real.pi_pos
  let γ : C(unitInterval, Circle) := ⟨fun u => φ.symm ⟨η u.1, hη u.1 u.2⟩, by
    refine φ.symm.continuous.comp (Continuous.subtype_mk ?_ _)
    exact hc.comp_continuous continuous_subtype_val fun u => u.2⟩
  obtain ⟨Γ, h1, -⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ (Complex.arg (γ 0))
    (Circle.exp_arg _).symm
  let P : ℝ → unitInterval := projIcc 0 1 zero_le_one
  have hP : Continuous P := continuous_projIcc
  refine ⟨fun u => Γ (P u) / (2 * Real.pi), ((Γ.continuous.comp hP).div_const _).continuousOn,
    fun u hu => ?_⟩
  have h2 : ee (Γ (P u) / (2 * Real.pi)) = γ (P u) := by
    unfold ee
    rw [mul_div_cancel₀ _ (by positivity)]
    exact congrFun h1 (P u)
  have hPu : (P u).1 = u := by simp [P, projIcc_of_mem zero_le_one hu]
  change (φ (ee (Γ (P u) / (2 * Real.pi)))).1 = η u
  rw [h2]
  simp only [γ, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply, hPu]

/-- A lift of a line is strictly monotone. -/
theorem lift_mono {m : ℝ → ℝ} (hc : ContinuousOn m (Icc 0 1)) (hi : InjOn (fun u => ee (m u))
  (Icc 0 1)) :
    StrictMonoOn m (Icc 0 1) ∨ StrictAntiOn m (Icc 0 1) :=
  hc.strictMonoOn_of_injOn_Icc' zero_le_one fun _ hx _ hy he => hi hx hy (by simp only [he])

/-- A lift of a closed loop is strictly monotone. -/
theorem lift_mono_loop {m : ℝ → ℝ} (hc : ContinuousOn m (Icc 0 1)) (hi : InjOn (fun u => ee (m u))
  (Ico 0 1)) :
    StrictMonoOn m (Icc 0 1) ∨ StrictAntiOn m (Icc 0 1) := by
  have key : ∀ {n : ℝ → ℝ}, ContinuousOn n (Icc 0 1) → InjOn n (Ico 0 1) → StrictMonoOn n (Icc 0
    (1 / 2)) →
      StrictMonoOn n (Icc 0 1) := by
    intro n hn hin hm
    have hsub : ∀ b ∈ Ico (0 : ℝ) 1, Icc 0 b ⊆ Ico (0 : ℝ) 1 := fun b hb z hz
      => ⟨hz.1, hz.2.trans_lt hb.2⟩
    have hIco : StrictMonoOn n (Ico 0 1) := by
      intro x hx y hy hxy
      set b := max y (1 / 2) with hb
      have hb1 : b ∈ Ico (0 : ℝ) 1 := ⟨hy.1.trans (le_max_left _ _), max_lt hy.2 (by norm_num)⟩
      have hb2 : (1 / 2 : ℝ) ≤ b := le_max_right _ _
      have hxb : x ∈ Icc 0 b := ⟨hx.1, hxy.le.trans (le_max_left _ _)⟩
      have hyb : y ∈ Icc 0 b := ⟨hy.1, le_max_left _ _⟩
      rcases (hn.mono (Icc_subset_Icc_right hb1.2.le)).strictMonoOn_of_injOn_Icc' hb1.1 (hin.mono
        (hsub b hb1)) with h | h
      · exact h hxb hyb hxy
      · have h1 := h (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb1.1⟩) (show
        (1 / 2 : ℝ) ∈ Icc 0 b from ⟨by norm_num, hb2⟩)
          (by norm_num)
        have h2 := hm (show (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) by norm_num) (show (1 / 2 : ℝ) ∈ Icc
          (0 : ℝ) (1 / 2) by norm_num)
          (by norm_num)
        exact absurd h1 (not_lt.mpr h2.le)
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hy.2 with rfl | hy1
    · have hx1 : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1, hxy⟩
      have hmid : (x + 1) / 2 ∈ Ioo x 1 := ⟨by linarith, by linarith⟩
      have h1 : n x < n ((x + 1) / 2) := hIco hx1 ⟨by linarith [hx.1], hmid.2⟩ hmid.1
      refine h1.trans_le ?_
      have hw : ContinuousWithinAt n (Ioo ((x + 1) / 2) 1) 1 :=
        (hn 1 (by simp)).mono fun z hz => ⟨by linarith [hz.1, hx.1], hz.2.le⟩
      have hne : (nhdsWithin (1 : ℝ) (Ioo ((x + 1) / 2) 1)).NeBot := right_nhdsWithin_Ioo_neBot
        hmid.2
      refine ge_of_tendsto hw (Filter.eventually_of_mem self_mem_nhdsWithin fun z hz => ?_)
      exact (hIco ⟨by linarith [hx.1], hmid.2⟩ ⟨by linarith [hz.1, hx.1], hz.2⟩ hz.1).le
    · exact hIco ⟨hx.1, hxy.trans hy1⟩ ⟨hy.1, hy1⟩ hxy
  have hin : InjOn m (Ico 0 1) := fun _ hx _ hy he => hi hx hy (by simp only [he])
  have h12 : Icc (0 : ℝ) (1 / 2) ⊆ Ico (0 : ℝ) 1 := fun z hz => ⟨hz.1, hz.2.trans_lt (by norm_num)⟩
  rcases (hc.mono (Icc_subset_Icc_right (by norm_num))).strictMonoOn_of_injOn_Icc' (by norm_num)
    (hin.mono h12) with h | h
  · exact .inl (key hc hin h)
  · have h2 := key (n := fun u => - m u) hc.neg (fun x hx y hy he => hin hx hy (neg_injective he))
      (fun x hx y hy hxy => neg_lt_neg (h hx hy hxy))
    exact .inr fun x hx y hy hxy => neg_lt_neg_iff.mp (h2 hx hy hxy)

end GraphMinor.Surface
