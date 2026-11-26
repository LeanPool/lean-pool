/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.MoveCuff
public import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Pushing a closed set off discs

`push_off : PushOffStatement`. Cap all cuffs, so that the boundary of a disc `D` consists of
interior points. A
larger disc around `D` with `D` as the unit disc (`exists_disc_collar`) lets us work in the plane.
If the line
`L` is the lower half of the unit circle, then near each point of the upper half circle there is
room outside
`D`, which is as thin as we like and goes to zero at the two ends. Vertical stretching maps a thin
lens along `L`
that misses the set onto `D` (`exists_vertical_push`). A chord splits `D` into two discs, which we
treat one
after the other.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

local notation "𝕀" => unitInterval

universe u

/-- The tent function with peak `1` at `l`, that is zero outside `(β, t)`. -/
noncomputable def tent (β l t y : ℝ) : ℝ := max 0 (min ((y - β) / (l - β)) ((t - y) / (t - l)))

/-- The piecewise linear map that fixes `β` and `t`, and moves `l` to `w`. -/
noncomputable def tentMap (β l w t y : ℝ) : ℝ := y + (w - l) * tent β l t y

theorem tent_left {β l t y : ℝ} (h1 : β < l) (h2 : l < t) (h3 : β ≤ y) (h4 : y ≤ l) :
    tent β l t y = (y - β) / (l - β) := by
  have h5 : 0 < l - β := by linarith
  have h6 : 0 < t - l := by linarith
  have h7 : (y - β) / (l - β) ≤ 1 := (div_le_one h5).mpr (by linarith)
  have h8 : 1 ≤ (t - y) / (t - l) := (one_le_div h6).mpr (by linarith)
  have h9 : 0 ≤ (y - β) / (l - β) := div_nonneg (by linarith) h5.le
  rw [tent, min_eq_left (h7.trans h8), max_eq_right h9]

theorem tent_right {β l t y : ℝ} (h1 : β < l) (h2 : l < t) (h3 : l ≤ y) (h4 : y ≤ t) :
    tent β l t y = (t - y) / (t - l) := by
  have h5 : 0 < l - β := by linarith
  have h6 : 0 < t - l := by linarith
  have h7 : (t - y) / (t - l) ≤ 1 := (div_le_one h6).mpr (by linarith)
  have h8 : 1 ≤ (y - β) / (l - β) := (one_le_div h5).mpr (by linarith)
  have h9 : 0 ≤ (t - y) / (t - l) := div_nonneg (by linarith) h6.le
  rw [tent, min_eq_right (h7.trans h8), max_eq_right h9]

theorem tent_low {β l t y : ℝ} (h1 : β < l) (_h2 : l < t) (h3 : y ≤ β) : tent β l t y = 0 := by
  have h5 : 0 < l - β := by linarith
  have h9 : (y - β) / (l - β) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h5.le
  rw [tent, max_eq_left ((min_le_left _ _).trans h9)]

theorem tent_high {β l t y : ℝ} (_h1 : β < l) (h2 : l < t) (h3 : t ≤ y) : tent β l t y = 0 := by
  have h5 : 0 < t - l := by linarith
  have h9 : (t - y) / (t - l) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h5.le
  rw [tent, max_eq_left ((min_le_right _ _).trans h9)]

theorem tent_nonneg (β l t y : ℝ) : 0 ≤ tent β l t y := le_max_left _ _

theorem tent_le_one {β l t y : ℝ} (h1 : β < l) (h2 : l < t) : tent β l t y ≤ 1 := by
  rcases le_total y β with h | h
  · rw [tent_low h1 h2 h]
    exact zero_le_one
  rcases le_total y l with h' | h'
  · rw [tent_left h1 h2 h h']
    exact (div_le_one (by linarith)).mpr (by linarith)
  rcases le_total y t with h'' | h''
  · rw [tent_right h1 h2 h' h'']
    exact (div_le_one (by linarith)).mpr (by linarith)
  · rw [tent_high h1 h2 h'']
    exact zero_le_one

theorem tentMap_inv {β l w t y : ℝ} (h1 : β < l) (h2 : l < t) (h3 : β < w) (h4 : w < t) :
    tentMap β w l t (tentMap β l w t y) = y := by
  rcases le_total y β with h | h
  · have e1 : tentMap β l w t y = y := by
      rw [tentMap, tent_low h1 h2 h, mul_zero, add_zero]
    rw [e1, tentMap, tent_low h3 h4 h, mul_zero, add_zero]
  rcases le_total y l with h' | h'
  · have e1 : tentMap β l w t y = β + (y - β) * (w - β) / (l - β) := by
      rw [tentMap, tent_left h1 h2 h h']
      field_simp [show l - β ≠ 0 by linarith]
      ring
    have h5 : 0 < l - β := by linarith
    have h6 : 0 ≤ (y - β) / (l - β) := div_nonneg (by linarith) h5.le
    have h7 : (y - β) / (l - β) ≤ 1 := (div_le_one h5).mpr (by linarith)
    have e2 : β + (y - β) * (w - β) / (l - β) = β + (y - β) / (l - β) * (w - β) := by ring
    have h8 : β ≤ tentMap β l w t y := by
      rw [e1, e2]
      nlinarith
    have h9 : tentMap β l w t y ≤ w := by
      rw [e1, e2]
      nlinarith
    rw [tentMap, tent_left h3 h4 h8 h9, e1]
    field_simp [show l - β ≠ 0 by linarith, show w - β ≠ 0 by linarith]
    ring
  rcases le_total y t with h'' | h''
  · have e1 : tentMap β l w t y = t - (t - y) * (t - w) / (t - l) := by
      rw [tentMap, tent_right h1 h2 h' h'']
      field_simp [show t - l ≠ 0 by linarith]
      ring
    have h5 : 0 < t - l := by linarith
    have h6 : 0 ≤ (t - y) / (t - l) := div_nonneg (by linarith) h5.le
    have h7 : (t - y) / (t - l) ≤ 1 := (div_le_one h5).mpr (by linarith)
    have e2 : t - (t - y) * (t - w) / (t - l) = t - (t - y) / (t - l) * (t - w) := by ring
    have h8 : w ≤ tentMap β l w t y := by
      rw [e1, e2]
      nlinarith
    have h9 : tentMap β l w t y ≤ t := by
      rw [e1, e2]
      nlinarith
    rw [tentMap, tent_right h3 h4 h8 h9, e1]
    field_simp [show t - l ≠ 0 by linarith, show t - w ≠ 0 by linarith]
    ring
  · have e1 : tentMap β l w t y = y := by
      rw [tentMap, tent_high h1 h2 h'', mul_zero, add_zero]
    rw [e1, tentMap, tent_high h3 h4 h'', mul_zero, add_zero]

theorem w_lt_tentMap {β l w t y : ℝ} (h1 : β < l) (h2 : l < t) (h4 : w < t) (h5 : l < y) :
    w < tentMap β l w t y := by
  rcases le_total y t with h | h
  · have e1 : tentMap β l w t y = t - (t - y) / (t - l) * (t - w) := by
      rw [tentMap, tent_right h1 h2 h5.le h]
      field_simp [show t - l ≠ 0 by linarith]
      ring
    have h6 : 0 < t - l := by linarith
    have h7 : (t - y) / (t - l) < 1 := (div_lt_one h6).mpr (by linarith)
    rw [e1]
    nlinarith
  · rw [tentMap, tent_high h1 h2 h, mul_zero, add_zero]
    linarith

/-- The pattern of the four functions of a vertical push: `β < l, w < t` over `(-1, 1)`, all equal
elsewhere. -/
def IsPushData (β l w t : ℝ → ℝ) : Prop :=
  Continuous β ∧ Continuous l ∧ Continuous w ∧ Continuous t ∧
    (∀ x, |x| < 1 → β x < l x ∧ l x < t x ∧ β x < w x ∧ w x < t x) ∧
    ∀ x, 1 ≤ |x| → β x = l x ∧ l x = w x ∧ w x = t x

theorem IsPushData.symm {β l w t : ℝ → ℝ} (h : IsPushData β l w t) : IsPushData β w l t := by
  obtain ⟨hβ, hl, hw, ht, h5, h6⟩ := h
  refine ⟨hβ, hw, hl, ht, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h5 x hx
    exact ⟨a3, a4, a1, a2⟩
  · obtain ⟨a1, a2, a3⟩ := h6 x hx
    exact ⟨a1.trans a2, a2.symm, a2.trans a3⟩

theorem IsPushData.continuous_tent {β l w t : ℝ → ℝ} (h : IsPushData β l w t) :
    Continuous fun z : ℂ => (z.im + (w z.re - l z.re) * tent (β z.re) (l z.re) (t z.re) z.im) := by
  obtain ⟨hβ, hl, hw, ht, h5, h6⟩ := h
  rw [continuous_iff_continuousAt]
  intro z
  have hre : Continuous Complex.re := Complex.continuous_re
  have him : Continuous Complex.im := Complex.continuous_im
  refine him.continuousAt.add ?_
  rcases lt_or_ge |z.re| 1 with hz | hz
  · obtain ⟨a1, a2, -, -⟩ := h5 _ hz
    have hc1 : ContinuousAt (fun z : ℂ => l z.re - β z.re) z :=
      ((hl.comp hre).sub (hβ.comp hre)).continuousAt
    have hc2 : ContinuousAt (fun z : ℂ => t z.re - l z.re) z :=
      ((ht.comp hre).sub (hl.comp hre)).continuousAt
    have hc3 : ContinuousAt (fun z : ℂ => z.im - β z.re) z :=
      (him.sub (hβ.comp hre)).continuousAt
    have hc4 : ContinuousAt (fun z : ℂ => t z.re - z.im) z :=
      ((ht.comp hre).sub him).continuousAt
    have hm : ContinuousAt (fun z : ℂ => tent (β z.re) (l z.re) (t z.re) z.im) z :=
      continuousAt_const.max
        ((hc3.div hc1 (sub_ne_zero.mpr a1.ne')).min
          (hc4.div hc2 (sub_ne_zero.mpr a2.ne')))
    exact ((hw.comp hre).sub (hl.comp hre)).continuousAt.mul hm
  · have h0 := h6 _ hz
    have hv : (w z.re - l z.re) * tent (β z.re) (l z.re) (t z.re) z.im = 0 := by
      rw [h0.2.1.symm]
      ring
    rw [ContinuousAt, hv]
    have hb : ∀ u : ℂ, ‖(w u.re - l u.re) * tent (β u.re) (l u.re) (t u.re) u.im‖
      ≤ |w u.re - l u.re| := by
      intro u
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _ _ _)]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rcases lt_or_ge |u.re| 1 with hu | hu
      · obtain ⟨a1, a2, -, -⟩ := h5 _ hu
        exact tent_le_one a1 a2
      · obtain ⟨a1, a2, a3⟩ := h6 _ hu
        have a4 : t u.re = l u.re := by rw [← a3, a2]
        rw [a1, a4]
        simp [tent]
    refine squeeze_zero_norm hb ?_
    have : Continuous fun u : ℂ => |w u.re - l u.re| := ((hw.comp hre).sub (hl.comp hre)).abs
    have h7 := this.tendsto z
    simpa [h0.2.1] using h7

/-- A push of the plane along vertical lines. -/
theorem exists_vertical_push {β l w t : ℝ → ℝ} (h : IsPushData β l w t) :
    ∃ Θ : ℂ ≃ₜ ℂ, (∀ z, (Θ z).re = z.re) ∧
      ∀ z, (Θ z).im = tentMap (β z.re) (l z.re) (w z.re) (t z.re) z.im := by
  have key : ∀ {β l w t : ℝ → ℝ}, IsPushData β l w t → Continuous fun z : ℂ =>
      (⟨z.re, tentMap (β z.re) (l z.re) (w z.re) (t z.re) z.im⟩ : ℂ) := fun {β l w t} h =>
    Complex.equivRealProdCLM.symm.continuous.comp (Complex.continuous_re.prodMk h.continuous_tent)
  have hinv : ∀ {β l w t : ℝ → ℝ}, IsPushData β l w t → ∀ x y : ℝ,
      tentMap (β x) (w x) (l x) (t x) (tentMap (β x) (l x) (w x) (t x) y) = y := by
    intro β l w t h x y
    obtain ⟨-, -, -, -, h5, h6⟩ := h
    rcases lt_or_ge |x| 1 with hx | hx
    · obtain ⟨a1, a2, a3, a4⟩ := h5 x hx
      exact tentMap_inv a1 a2 a3 a4
    · obtain ⟨a1, a2, a3⟩ := h6 x hx
      simp [tentMap, a2]
  refine ⟨{ toFun := fun z => ⟨z.re, tentMap (β z.re) (l z.re) (w z.re) (t z.re) z.im⟩
            invFun := fun z => ⟨z.re, tentMap (β z.re) (w z.re) (l z.re) (t z.re) z.im⟩
            left_inv := fun z => Complex.ext rfl (hinv h z.re z.im)
            right_inv := fun z => Complex.ext rfl (hinv h.symm z.re z.im)
            continuous_toFun := key h
            continuous_invFun := key h.symm }, fun z => rfl, fun z => rfl⟩

section extend

variable {T : Type u} [TopologicalSpace T] [T2Space T]

/-- A homeomorphism of the plane that is the identity on the sphere of radius `2` moves over to the
disc
`c` parametrizes, and to the identity outside. -/
theorem exists_homeomorph_of_collar (hman : ∀ x : T, IsManifoldPoint x) {E : Set T}
  (hE : IsClosedDisc E)
    {c : ℂ → T} {c' : T → ℂ} (hcc : ContinuousOn c (closedBall 0 2)) (hcc' : ContinuousOn c' E)
    (hcm : MapsTo c (closedBall 0 2) E) (hcm' : MapsTo c' E (closedBall 0 2))
    (hl : LeftInvOn c' c (closedBall 0 2)) (hr : RightInvOn c' c E) (hs : c '' sphere 0 2
      = discBd E)
    (Θ : ℂ ≃ₜ ℂ) (hΘ : ∀ z, 3 / 2 ≤ ‖z‖ → Θ z = z) :
    ∃ h : T ≃ₜ T, (∀ z ∈ closedBall (0 : ℂ) 2, h (c z) = c (Θ z)) ∧ ∀ x ∉ E, h x = x := by
  classical
  have hmap : ∀ {Θ : ℂ ≃ₜ ℂ}, (∀ z, 3 / 2 ≤ ‖z‖ → Θ z = z) → MapsTo Θ (closedBall 0 2)
    (closedBall 0 2) := by
    intro Θ hΘ z hz
    by_contra hcon
    have h1 : 2 < ‖Θ z‖ := by
      rw [mem_closedBall_zero_iff, not_le] at hcon
      exact hcon
    have h2 := hΘ (Θ z) (by linarith)
    have h3 := Θ.injective h2
    rw [h3] at h1
    linarith [mem_closedBall_zero_iff.mp hz]
  have hsym : ∀ z, 3 / 2 ≤ ‖z‖ → Θ.symm z = z := fun z hz => by
    rw [Homeomorph.symm_apply_eq, hΘ z hz]
  have hEc := hE.isClosed
  have hIo := hE.isOpen_discInt hman
  have key : ∀ {Θ : ℂ ≃ₜ ℂ}, (∀ z, 3 / 2 ≤ ‖z‖ → Θ z = z) →
      Continuous fun x => if x ∈ E then c (Θ (c' x)) else x := by
    intro Θ hΘ
    rw [← continuousOn_univ]
    have huniv : E ∪ (discInt E)ᶜ = univ := by
      rw [eq_univ_iff_forall]
      intro x
      by_cases hx : x ∈ discInt E
      · exact .inl (discInt_subset E hx)
      · exact .inr hx
    rw [← huniv]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hEc hIo.isClosed_compl
    · refine ContinuousOn.congr (f := fun x => c (Θ (c' x))) ?_ fun x hx => ite_eq_left hx
      exact hcc.comp (Θ.continuous.comp_continuousOn hcc') fun x hx => hmap hΘ (hcm' hx)
    · refine continuousOn_id.congr fun x hx => ?_
      by_cases hxE : x ∈ E
      · have hxb : x ∈ discBd E := by
          by_contra hcon
          exact hx ⟨hxE, hcon⟩
        rw [← hs] at hxb
        obtain ⟨z, hz, rfl⟩ := hxb
        have hz2 : z ∈ closedBall (0 : ℂ) 2 := sphere_subset_closedBall hz
        have hn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
        change (if c z ∈ E then c (Θ (c' (c z))) else c z) = c z
        rw [ite_eq_left (hcm hz2), hl hz2, hΘ z (by linarith)]
      · exact ite_eq_right hxE
  have hinv : ∀ {Θ₁ Θ₂ : ℂ ≃ₜ ℂ}, (∀ z, Θ₂ (Θ₁ z) = z) → (∀ z, 3 / 2 ≤ ‖z‖ → Θ₁ z = z) → ∀ x,
      (if (if x ∈ E then c (Θ₁ (c' x)) else x) ∈ E then
        c (Θ₂ (c' (if x ∈ E then c (Θ₁ (c' x)) else x))) else
        (if x ∈ E then c (Θ₁ (c' x)) else x)) = x := by
    intro Θ₁ Θ₂ h12 h1 x
    by_cases hx : x ∈ E
    · have h2 := hmap h1 (hcm' hx)
      simp only [ite_eq_left hx, ite_eq_left (hcm h2), hl h2, h12]
      exact hr hx
    · simp only [ite_eq_right hx]
  refine ⟨{ toFun := fun x => if x ∈ E then c (Θ (c' x)) else x
            invFun := fun x => if x ∈ E then c (Θ.symm (c' x)) else x
            left_inv := fun x => hinv (fun z => Θ.symm_apply_apply z) hΘ x
            right_inv := fun x => hinv (fun z => Θ.apply_symm_apply z) hsym x
            continuous_toFun := key hΘ
            continuous_invFun := key hsym }, fun z hz => ?_, fun x hx => ite_eq_right hx⟩
  change (if c z ∈ E then c (Θ (c' (c z))) else c z) = c (Θ z)
  rw [ite_eq_left (hcm hz), hl hz]

end extend

/-- The height of the unit circle over `x`. -/
noncomputable def capH (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

theorem continuous_capH : Continuous capH := by
  unfold capH
  fun_prop

theorem capH_sq {x : ℝ} (h : |x| ≤ 1) : capH x ^ 2 = 1 - x ^ 2 := by
  have : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) h
  exact Real.sq_sqrt (by linarith)

theorem capH_pos {x : ℝ} (h : |x| < 1) : 0 < capH x := by
  have : x ^ 2 < 1 := by
    rw [← sq_abs]
    exact pow_lt_one₀ (abs_nonneg _) h (by norm_num)
  exact Real.sqrt_pos.mpr (by linarith)

theorem capH_eq_zero {x : ℝ} (h : 1 ≤ |x|) : capH x = 0 := by
  have : 1 ≤ x ^ 2 := by
    rw [← sq_abs]
    exact one_le_pow₀ h
  exact Real.sqrt_eq_zero'.mpr (by linarith)

/-- The lower half of the unit circle, from `-1` to `1`. -/
noncomputable def lowArc (t : 𝕀) : ℂ := ⟨2 * t.1 - 1, - capH (2 * t.1 - 1)⟩

/-- The upper half of the unit circle, from `-1` to `1`. -/
noncomputable def highArc (t : 𝕀) : ℂ := ⟨2 * t.1 - 1, capH (2 * t.1 - 1)⟩

theorem abs_two_sub_one_le (t : 𝕀) : |2 * t.1 - 1| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [t.2.1, t.2.2]

theorem norm_of_capH {x y : ℝ} (hx : |x| ≤ 1) (hy : y ^ 2 = capH x ^ 2) : ‖(⟨x, y⟩ : ℂ)‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_mk]
  rw [show x * x + y * y = x ^ 2 + y ^ 2 by ring, hy, capH_sq hx]
  simp

theorem isTwoArcs_low_high : IsTwoArcs lowArc highArc := by
  have hre : ∀ (f : 𝕀 → ℂ), (∀ t, (f t).re = 2 * t.1 - 1) → Function.Injective f := fun f hf s t h
    => by
    have := congrArg Complex.re h
    rw [hf, hf] at this
    exact Subtype.ext (by linarith)
  have hc : Continuous fun t : 𝕀 => capH (2 * t.1 - 1) :=
    continuous_capH.comp (by fun_prop)
  refine ⟨⟨?_, hre _ fun _ => rfl⟩, ⟨?_, hre _ fun _ => rfl⟩, ?_, ?_, ?_⟩
  · exact Complex.equivRealProdCLM.symm.continuous.comp ((by fun_prop : Continuous fun t : 𝕀
    => 2 * t.1 - 1).prodMk hc.neg)
  · exact Complex.equivRealProdCLM.symm.continuous.comp ((by fun_prop : Continuous fun t : 𝕀
    => 2 * t.1 - 1).prodMk hc)
  · simp [lowArc, highArc, capH]
  · simp [lowArc, highArc, capH]
    norm_num
  · intro s t h
    have h1 : s = t := Subtype.ext (by
      have := congrArg Complex.re h
      simp only [lowArc, highArc] at this
      linarith)
    subst h1
    have h2 := congrArg Complex.im h
    simp only [lowArc, highArc] at h2
    have h3 : capH (2 * s.1 - 1) = 0 := by linarith
    have h4 : |2 * s.1 - 1| = 1 := by
      by_contra hne
      have := capH_pos (lt_of_le_of_ne (abs_two_sub_one_le s) hne)
      linarith
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp h4 with h5 | h5
    · have h6 : s = 1 := Subtype.ext (show s.1 = 1 by linarith)
      exact Or.inr ⟨h6, h6⟩
    · have h6 : s = 0 := Subtype.ext (show s.1 = 0 by linarith)
      exact Or.inl ⟨h6, h6⟩

theorem range_low_union_high : range lowArc ∪ range highArc = sphere 0 1 := by
  ext z
  constructor
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact mem_sphere_zero_iff_norm.mpr (norm_of_capH (abs_two_sub_one_le t) (by ring))
    · exact mem_sphere_zero_iff_norm.mpr (norm_of_capH (abs_two_sub_one_le t) rfl)
  · intro hz
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have h1 := Complex.abs_re_le_norm z
    rw [hn] at h1
    have h2 := abs_le.mp h1
    have ht : (z.re + 1) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
      have := Complex.sq_norm z
      rw [hn, Complex.normSq_apply] at this
      nlinarith
    have hc : capH z.re = |z.im| := by
      rw [capH, show 1 - z.re ^ 2 = z.im ^ 2 by linarith, Real.sqrt_sq_eq_abs]
    have he : 2 * ((z.re + 1) / 2) - 1 = z.re := by ring
    rcases le_total 0 z.im with h3 | h3
    · refine .inr ⟨⟨_, ht⟩, Complex.ext ?_ ?_⟩
      · simp only [highArc, he]
      · simp only [highArc, he, hc, abs_of_nonneg h3]
    · refine .inl ⟨⟨_, ht⟩, Complex.ext ?_ ?_⟩
      · simp only [lowArc, he]
      · simp only [lowArc, he, hc, abs_of_nonpos h3, neg_neg]

section side

variable {T : Type u} [TopologicalSpace T] [CompactSpace T] [T2Space T]

omit [CompactSpace T] in
/-- Disc `D` and an arc of its boundary as the lower half: coordinates around `D` where `D` is the
unit disc. -/
theorem exists_chart_two_arcs (hman : ∀ x : T, IsManifoldPoint x) {D : Set T} {u v : 𝕀 → T}
    (hD : IsClosedDisc D) (hint : ∀ x ∈ discBd D, IsInteriorPoint x) (huv : IsTwoArcs u v)
    (hbd : range u ∪ range v = discBd D) :
    ∃ (E : Set T) (c : ℂ → T) (c' : T → ℂ), IsClosedDisc E ∧ ContinuousOn c (closedBall 0 2) ∧
      ContinuousOn c' E ∧ MapsTo c (closedBall 0 2) E ∧ MapsTo c' E (closedBall 0 2) ∧
      LeftInvOn c' c (closedBall 0 2) ∧ RightInvOn c' c E ∧ c '' closedBall 0 1 = D ∧
      c '' sphere 0 2 = discBd E ∧ (∀ t, c (lowArc t) = u t) ∧ ∀ t, c (highArc t) = v t := by
  classical
  obtain ⟨E, hE, h2, -⟩ := exists_disc_around hman hD hint isOpen_univ (subset_univ _)
  obtain ⟨h₀, g₀, cD⟩ := hD.exists_isChart
  have hbdD : discBd D ⊆ D := discBd_subset D
  have hu : ∀ t, u t ∈ D := fun t => hbdD (hbd ▸ Or.inl ⟨t, rfl⟩)
  have hv : ∀ t, v t ∈ D := fun t => hbdD (hbd ▸ Or.inr ⟨t, rfl⟩)
  have harc : ∀ {a : 𝕀 → T}, IsArcMap a → (∀ t, a t ∈ D) → IsArcMap fun t => h₀ (a t) := fun ha hm
    =>
    ⟨cD.hc.comp_continuous ha.1 hm, fun s t hst => ha.2 (cD.gh.injOn (hm s) (hm t) hst)⟩
  obtain ⟨hl₁, hh₁, h01, h11, hm₁⟩ := id isTwoArcs_low_high
  have hinjh := cD.gh.injOn
  obtain ⟨b, k, m, hb1, hb2⟩ := exists_bdMatch_of_arcs (c := lowArc) (d := highArc)
    (c' := fun t => h₀ (u t)) (d' := fun t => h₀ (v t)) hl₁ hh₁ (harc huv.1 hu)
      (harc huv.2 hv) h01 h11
    (by simp only [huv.3]) (by simp only [huv.4]) hm₁ (fun s t hst => huv.5 s t
      (hinjh (hu s) (hv t) hst))
  have hsr : range (fun t => h₀ (u t)) ∪ range (fun t => h₀ (v t)) = sphere 0 1 := by
    rw [← cD.bd, ← hbd, image_union, ← range_comp, ← range_comp]
    rfl
  rw [range_low_union_high, hsr] at m
  obtain ⟨G, hG⟩ := exists_homeomorph_of_bdMatch oArc_sphere m
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := id m
  have hsph : ∀ w : Circle, (w : ℂ) ∈ sphere (0 : ℂ) 1 := fun w =>
    mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
  have hb0 : ∀ w : Circle, g₀ (G w) ∈ discBd D := fun w => by
    rw [← cD.g_sphere, hG (hsph w)]
    exact mem_image_of_mem _ (m1 (hsph w))
  let P : Circle → discBd D := fun w => ⟨g₀ (G w), hb0 w⟩
  have hPc : Continuous P := by
    refine Continuous.subtype_mk ?_ _
    have hcoe : Continuous fun w : Circle => (w : ℂ) := by fun_prop
    refine (cD.gc.comp_continuous (G.continuous.comp hcoe) fun w => ?_)
    rw [hG (hsph w)]
    exact sphere_subset_closedBall (m1 (hsph w))
  have hPi : Function.Injective P := fun w w' he => by
    have h3 : g₀ (G w) = g₀ (G w') := congrArg Subtype.val he
    have h4 : ∀ w : Circle, G w ∈ closedBall (0 : ℂ) 1 := fun w => by
      rw [hG (hsph w)]
      exact sphere_subset_closedBall (m1 (hsph w))
    have h5 : G w = G w' := cD.hg.injOn (h4 w) (h4 w') h3
    exact Circle.ext (G.injective h5)
  have hPs : Function.Surjective P := by
    rintro ⟨x, hx⟩
    have hx' : h₀ x ∈ sphere (0 : ℂ) 1 := by
      rw [← cD.bd]
      exact mem_image_of_mem _ hx
    have hk := m2 hx'
    refine ⟨⟨k (h₀ x), by
      simpa [Submonoid.unitSphere] using mem_sphere_zero_iff_norm.mp hk⟩, Subtype.ext ?_⟩
    change g₀ (G (k (h₀ x))) = x
    rw [hG hk, m4 hx']
    exact cD.gh (hbdD hx)
  let p : Circle ≃ₜ discBd D := hPc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective P ⟨hPi, hPs⟩)
  obtain ⟨c, c', q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := exists_disc_collar hD hE h2 p
  have hval : ∀ t : 𝕀, ∀ z (hz : z = lowArc t ∨ z = highArc t), ‖z‖ = 1 := by
    rintro t _ (rfl | rfl)
    · exact norm_of_capH (abs_two_sub_one_le t) (by ring)
    · exact norm_of_capH (abs_two_sub_one_le t) rfl
  have hcall : ∀ z, (hz : ‖z‖ = 1) → c z = g₀ (b z) := fun z hz => by
    have hw := q9 ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
    have hzs : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hz
    rw [show ((⟨z, by simpa [Submonoid.unitSphere] using hz⟩ : Circle) : ℂ) = z from rfl] at hw
    rw [hw]
    change g₀ (G z) = _
    rw [hG hzs]
  refine ⟨E, c, c', hE, q1, q2, q3, q4, q5, q6, q7, q8, fun t => ?_, fun t => ?_⟩
  · rw [hcall _ (hval t _ (.inl rfl)), hb1, cD.gh (hu t)]
  · rw [hcall _ (hval t _ (.inr rfl)), hb2, cD.gh (hv t)]

private theorem exists_collar_push {e lam : ℝ → ℝ} (hele : ∀ x, e x ≤ 1 / 2)
    (hdata : IsPushData (fun x => -capH x) (fun x => -capH x + lam x) capH
      (fun x => capH x + e x)) :
    ∃ Θ : ℂ ≃ₜ ℂ, (∀ z, (Θ z).re = z.re) ∧
      (∀ z, (Θ z).im = tentMap (-capH z.re) (-capH z.re + lam z.re) (capH z.re)
        (capH z.re + e z.re) z.im) ∧
      (∀ z : ℂ, (1 ≤ |z.re| ∨ z.im ≤ -capH z.re ∨ capH z.re + e z.re ≤ z.im) → Θ z = z) ∧
      (∀ z, 3 / 2 ≤ ‖z‖ → Θ z = z) ∧ MapsTo Θ (closedBall 0 2) (closedBall 0 2) := by
  obtain ⟨Θ, hre, him⟩ := exists_vertical_push hdata
  have hfix : ∀ z : ℂ, (1 ≤ |z.re| ∨ z.im ≤ - capH z.re ∨ capH z.re + e z.re ≤ z.im) → Θ z = z := by
    intro z hz
    refine Complex.ext (hre z) ?_
    rw [him]
    rcases lt_or_ge |z.re| 1 with hx | hx
    · obtain ⟨a1, a2, -, -⟩ := hdata.2.2.2.2.1 _ hx
      rcases hz with hz | hz | hz
      · exact absurd hx (not_lt.mpr hz)
      · rw [tentMap, tent_low a1 a2 hz, mul_zero, add_zero]
      · rw [tentMap, tent_high a1 a2 hz, mul_zero, add_zero]
    · have a1 := (hdata.2.2.2.2.2 _ hx).2.1
      simp only at a1
      rw [tentMap, show capH z.re - (- capH z.re + lam z.re) = 0 by linarith, zero_mul, add_zero]
  have hHle : ∀ x, capH x ≤ 1 := fun x => by
    rw [capH]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])
  have hHnn : ∀ x, 0 ≤ capH x := fun x => Real.sqrt_nonneg _
  have hfar : ∀ z : ℂ, 3 / 2 ≤ ‖z‖ → Θ z = z := by
    intro z hz
    refine hfix z ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨a1, a2, a3⟩ := hcon
    have a4 := capH_sq a1.le
    have a5 := hele z.re
    have a6 := hHle z.re
    have a7 := hHnn z.re
    have a8 : z.im ^ 2 < (capH z.re + 1 / 2) ^ 2 := sq_lt_sq' (by linarith) (by linarith)
    have a9 := Complex.sq_norm z
    rw [Complex.normSq_apply] at a9
    nlinarith
  have hmap2 : ∀ z ∈ closedBall (0 : ℂ) 2, Θ z ∈ closedBall (0 : ℂ) 2 := by
    intro z hz
    by_contra hcon
    have h3 : 2 < ‖Θ z‖ := by
      rw [mem_closedBall_zero_iff, not_le] at hcon
      exact hcon
    have h4 := Θ.injective (hfar (Θ z) (by linarith))
    rw [h4] at h3
    linarith [mem_closedBall_zero_iff.mp hz]
  exact ⟨Θ, hre, him, hfix, hfar, hmap2⟩

omit [CompactSpace T] in
/-- **Pushing a closed set off a disc.** Here `u` is an arc of the boundary of `D`, and `Y` meets
`D` only in `u`.
A homeomorphism that fixes `Y` moves `C` off `D`, except for the ends of `u`. -/
theorem push_side (hman : ∀ x : T, IsManifoldPoint x) {D Y C : Set T} {u v : 𝕀 → T}
    (hD : IsClosedDisc D) (hint : ∀ x ∈ discBd D, IsInteriorPoint x) (huv : IsTwoArcs u v)
    (hbd : range u ∪ range v = discBd D) (hY : IsClosed Y) (hYD : Y ∩ D ⊆ range u) (h0 : u 0 ∈ Y)
    (_h1 : u 1 ∈ Y) (hC : IsClosed C) (hCu : C ∩ range u ⊆ {u 0, u 1}) :
    ∃ h : T ≃ₜ T, (∀ y ∈ Y, h y = y) ∧ h '' C ∩ D ⊆ {u 0, u 1} := by
  classical
  obtain ⟨E, c, c', hE, q1, q2, q3, q4, q5, q6, q7, q8, cl, ch⟩ :=
    exists_chart_two_arcs hman hD hint huv hbd
  have hb12 : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 := closedBall_subset_closedBall (by norm_num)
  have hinj : InjOn c (closedBall 0 2) := q5.injOn
  have hDE : D ⊆ E := by
    rw [← q7]
    exact (image_mono hb12).trans q3.image_subset
  have hlow : ∀ t, lowArc t ∈ closedBall (0 : ℂ) 1 := fun t => by
    rw [mem_closedBall_zero_iff]
    exact (norm_of_capH (y := - capH _) (abs_two_sub_one_le t) (by ring)).le
  have hhigh : ∀ t, highArc t ∈ closedBall (0 : ℂ) 1 := fun t => by
    rw [mem_closedBall_zero_iff]
    exact (norm_of_capH (abs_two_sub_one_le t) rfl).le
  have hend0 : (⟨-1, 0⟩ : ℂ) = lowArc 0 := by simp [lowArc, capH]
  have hend1 : (⟨1, 0⟩ : ℂ) = lowArc 1 := by simp [lowArc, capH]; norm_num
  have hnsq : ∀ z : ℂ, z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hle1 (z : ℂ) (hz : ‖z‖ ≤ 1) : z.re ^ 2 + z.im ^ 2 ≤ 1 :=
    (hnsq z).trans_le (pow_le_one₀ (norm_nonneg z) hz)
  have hpt : ∀ x : ℝ, |x| < 1 → ∃ t : 𝕀, t ≠ 0 ∧ t ≠ 1 ∧ 2 * t.1 - 1 = x := fun x hx => by
    obtain ⟨h3, h4⟩ := abs_lt.mp hx
    refine ⟨⟨(x + 1) / 2, by linarith, by linarith⟩, fun he => ?_, fun he => ?_, by simp; ring⟩
    · have := congrArg Subtype.val he
      simp only [Set.Icc.coe_zero] at this
      linarith
    · have := congrArg Subtype.val he
      simp only [Set.Icc.coe_one] at this
      linarith
  let Yc : Set ℂ := closedBall 0 2 ∩ c ⁻¹' Y
  let Cc : Set ℂ := (closedBall 0 2 ∩ c ⁻¹' C) ∪ {lowArc 0, lowArc 1}
  have hbdD : discBd D ⊆ D := discBd_subset D
  have hYc : IsClosed Yc := q1.preimage_isClosed_of_isClosed isClosed_closedBall hY
  have hCc : IsClosed Cc := (q1.preimage_isClosed_of_isClosed isClosed_closedBall hC).union
    (Set.toFinite _).isClosed
  have hYne : Yc.Nonempty := ⟨lowArc 0, hb12 (hlow 0), by
    change c _ ∈ Y
    rw [cl]
    exact h0⟩
  have hCne : Cc.Nonempty := ⟨lowArc 0, Or.inr (Or.inl rfl)⟩
  let d : ℝ → ℝ := fun x => infDist (⟨x, capH x⟩ : ℂ) Yc
  let d₂ : ℝ → ℝ := fun x => infDist (⟨x, - capH x⟩ : ℂ) Cc
  have hpc : ∀ {f : ℝ → ℝ}, Continuous f → Continuous fun x : ℝ => (⟨x, f x⟩ : ℂ) := fun hf =>
    Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk hf)
  have hdc : Continuous d := (continuous_infDist_pt Yc).comp (hpc continuous_capH)
  have hd₂c : Continuous d₂ := (continuous_infDist_pt Cc).comp (hpc continuous_capH.neg)
  have hdpos : ∀ x, |x| < 1 → 0 < d x := fun x hx => by
    refine (hYc.notMem_iff_infDist_pos hYne).mp fun hmem => ?_
    obtain ⟨t, ht0, ht1, ht⟩ := hpt x hx
    have he : highArc t = ⟨x, capH x⟩ := by simp only [highArc, ht]
    have h3 : v t ∈ Y := by
      have := hmem.2
      rwa [mem_preimage, ← he, ch] at this
    obtain ⟨s, hs⟩ := hYD ⟨h3, hbdD (hbd ▸ Or.inr ⟨t, rfl⟩)⟩
    rcases huv.5 s t hs with h4 | h4
    · exact ht0 h4.2
    · exact ht1 h4.2
  have hd₂pos : ∀ x, |x| < 1 → 0 < d₂ x := fun x hx => by
    refine (hCc.notMem_iff_infDist_pos hCne).mp fun hmem => ?_
    obtain ⟨t, ht0, ht1, ht⟩ := hpt x hx
    have he : lowArc t = ⟨x, - capH x⟩ := by simp only [lowArc, ht]
    rcases hmem with hmem | hmem
    · have h3 : u t ∈ C := by
        have := hmem.2
        rwa [mem_preimage, ← he, cl] at this
      rcases hCu ⟨h3, t, rfl⟩ with h4 | h4
      · exact ht0 (huv.1.2 h4)
      · exact ht1 (huv.1.2 h4)
    · obtain ⟨h3, h4⟩ := abs_lt.mp hx
      rcases hmem with h5 | h5
      · have := congrArg Complex.re h5
        simp only [lowArc, Set.Icc.coe_zero] at this
        linarith
      · have := congrArg Complex.re h5
        simp only [lowArc, Set.Icc.coe_one] at this
        linarith
  let e : ℝ → ℝ := fun x => min (d x / 2) (min (1 / 2) (capH x))
  let lam : ℝ → ℝ := fun x => min (d₂ x / 2) (capH x)
  have hHc := continuous_capH
  have hec : Continuous e := (hdc.div_const 2).min (continuous_const.min hHc)
  have hlc : Continuous lam := (hd₂c.div_const 2).min hHc
  have hepos : ∀ x, |x| < 1 → 0 < e x := fun x hx =>
    lt_min (half_pos (hdpos x hx)) (lt_min (by norm_num) (capH_pos hx))
  have hlpos : ∀ x, |x| < 1 → 0 < lam x := fun x hx =>
    lt_min (half_pos (hd₂pos x hx)) (capH_pos hx)
  have hele : ∀ x, e x ≤ 1 / 2 := fun x => (min_le_right _ _).trans (min_le_left _ _)
  have hlle : ∀ x, lam x ≤ capH x := fun x => min_le_right _ _
  have hdata : IsPushData (fun x => - capH x) (fun x => - capH x + lam x) capH
      (fun x => capH x + e x) := by
    refine ⟨hHc.neg, hHc.neg.add hlc, hHc, hHc.add hec, fun x hx => ?_, fun x hx => ?_⟩
    · have a1 := capH_pos hx
      have a2 := hepos x hx
      have a3 := hlpos x hx
      have a4 := hlle x
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> linarith
    · have a1 := capH_eq_zero hx
      have a2 : e x = 0 := by
        simp only [e, a1]
        rw [min_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact min_eq_right (div_nonneg infDist_nonneg (by norm_num))
      have a3 : lam x = 0 := by
        simp only [lam, a1]
        exact min_eq_right (div_nonneg infDist_nonneg (by norm_num))
      simp [a1, a2, a3]
  obtain ⟨Θ, hre, him, hfix, hfar, hmap2⟩ := exists_collar_push hele hdata
  obtain ⟨h, hh1, hh2⟩ := exists_homeomorph_of_collar hman hE q1 q2 q3 q4 q5 q6 q8 Θ hfar
  refine ⟨h, fun y hy => ?_, ?_⟩
  · by_cases hyE : y ∈ E
    · have hz := q4 hyE
      have hcz : c (c' y) = y := q6 hyE
      set z := c' y with hzdef
      have hzY : z ∈ Yc := ⟨hz, by rw [mem_preimage, hcz]; exact hy⟩
      have hfixz : Θ z = z := by
        refine hfix z ?_
        by_contra hcon
        push Not at hcon
        obtain ⟨a1, a2, a3⟩ := hcon
        rcases le_or_gt z.im (capH z.re) with a4 | a4
        · have a5 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
            have := capH_sq a1.le
            have a6 : z.im ^ 2 ≤ capH z.re ^ 2 := sq_le_sq' (by linarith) a4
            linarith
          have a6 : ‖z‖ ≤ 1 := by
            have := hnsq z
            nlinarith [norm_nonneg z]
          have a7 : c z ∈ D := q7 ▸ mem_image_of_mem c (mem_closedBall_zero_iff.mpr a6)
          obtain ⟨s, hs⟩ := hYD ⟨hcz ▸ hy, a7⟩
          have a8 : lowArc s = z := hinj (hb12 (hlow s)) hz (by rw [cl, hs])
          have a9 := congrArg Complex.re a8
          have a10 := congrArg Complex.im a8
          simp only [lowArc] at a9 a10
          rw [a9] at a10
          linarith
        · have a5 : d z.re ≤ dist (⟨z.re, capH z.re⟩ : ℂ) z := infDist_le_dist_of_mem hzY
          rw [Complex.dist_of_re_eq (show (⟨z.re, capH z.re⟩ : ℂ).re = z.re from rfl), Real.dist_eq,
            abs_sub_comm, abs_of_pos (by simpa using a4)] at a5
          have a6 : e z.re ≤ d z.re / 2 := min_le_left _ _
          simp only at a5
          linarith [hdpos z.re a1, hepos z.re a1]
      rw [← hcz, hh1 z hz, hfixz]
    · exact hh2 y hyE
  · rintro _ ⟨⟨x, hx, rfl⟩, hxD⟩
    by_cases hxE : x ∈ E
    · have hz := q4 hxE
      have hcz : c (c' x) = x := q6 hxE
      set z := c' x with hzdef
      have hzC : z ∈ Cc := Or.inl ⟨hz, by rw [mem_preimage, hcz]; exact hx⟩
      rw [← hcz, hh1 z hz] at hxD ⊢
      obtain ⟨ζ, hζ, he⟩ : c (Θ z) ∈ c '' closedBall 0 1 := q7 ▸ hxD
      have hΘz : ζ = Θ z := hinj (hb12 hζ) (hmap2 hz) he
      have hn1 : ‖Θ z‖ ≤ 1 := mem_closedBall_zero_iff.mp (hΘz ▸ hζ)
      have hn2 := hle1 _ hn1
      rw [hre] at hn2
      rcases lt_or_ge |z.re| 1 with a1 | a1
      · exfalso
        obtain ⟨a2, a3, -, a5⟩ := hdata.2.2.2.2.1 _ a1
        simp only at a2 a3 a5
        have a4 := capH_sq a1.le
        have a7 := capH_pos a1
        rcases lt_or_ge z.im (- capH z.re) with a8 | a8
        · have a9 : Θ z = z := hfix z (.inr (.inl a8.le))
          rw [a9] at hn2
          nlinarith
        rcases le_or_gt z.im (- capH z.re + lam z.re) with a9 | a9
        · have a10 : d₂ z.re ≤ dist (⟨z.re, - capH z.re⟩ : ℂ) z := infDist_le_dist_of_mem hzC
          rw [Complex.dist_of_re_eq (show (⟨z.re, - capH z.re⟩ : ℂ).re = z.re from rfl),
            Real.dist_eq,
            abs_sub_comm, abs_of_nonneg (by change 0 ≤ z.im - - capH z.re; linarith)] at a10
          have a11 : lam z.re ≤ d₂ z.re / 2 := min_le_left _ _
          simp only at a10
          linarith [hd₂pos z.re a1]
        · have a10 := w_lt_tentMap a2 a3 a5 a9
          rw [← him] at a10
          nlinarith
      · have a9 : Θ z = z := hfix z (.inl a1)
        rw [a9] at hn2 ⊢
        have a10 : z.re ^ 2 = 1 ∧ z.im = 0 := by
          have a11 : 1 ≤ z.re ^ 2 := by
            rw [← sq_abs]
            exact one_le_pow₀ a1
          have a12 : z.im ^ 2 ≤ 0 := by linarith
          have a13 : z.im = 0 := by nlinarith [sq_nonneg z.im]
          rw [a13] at hn2
          exact ⟨by nlinarith, a13⟩
        have a14 : z.re = 1 ∨ z.re = -1 := by
          have : (z.re - 1) * (z.re + 1) = 0 := by nlinarith [a10.1]
          rcases mul_eq_zero.mp this with h3 | h3
          · exact .inl (by linarith)
          · exact .inr (by linarith)
        rcases a14 with a14 | a14
        · right
          rw [show z = lowArc 1 from Complex.ext (by simp [lowArc, a14]; norm_num)
            (by simp [lowArc, capH, a10.2]; norm_num), cl]
          rfl
        · left
          rw [show z = lowArc 0 from Complex.ext (by simp [lowArc, a14])
            (by simp [lowArc, capH, a10.2]), cl]
    · exact absurd (hDE (by rwa [hh2 x hxE] at hxD)) hxE

end side

/-- A line in an `O`-arc is one of the two arcs between its ends. -/
theorem exists_arcs_of_line {X : Type u} [TopologicalSpace X] [T2Space X] {F L : Set X} {a b : X}
    (hF : IsOArc F) (hL : IsLineWithEnds L a b) (hLF : L ⊆ F) :
    ∃ u v : 𝕀 → X, IsTwoArcs u v ∧ range u = L ∧ u 0 = a ∧ u 1 = b ∧ range u ∪ range v = F := by
  obtain ⟨f, hf0, hf1⟩ := hL
  let u : 𝕀 → X := fun t => (f t).1
  have hu : IsArcMap u := ⟨continuous_subtype_val.comp f.continuous,
    fun s t h => f.injective (Subtype.ext h)⟩
  have hru : range u = L := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp [u]⟩
  have hab : a ≠ b := fun he => by
    have : u 0 = u 1 := by simp only [u, hf0, hf1, he]
    exact zero_ne_one (hu.2 this)
  have ha : a ∈ F := hLF (hru ▸ ⟨0, hf0⟩)
  have hb : b ∈ F := hLF (hru ▸ ⟨1, hf1⟩)
  obtain ⟨p, q, hpq, hp0, hp1, hun⟩ := hF.exists_arcs ha hb hab
  have key : ∀ {p q : 𝕀 → X}, IsTwoArcs p q → p 0 = a → p 1 = b → range p ∪ range q = F →
      u '' Ioo 0 1 ⊆ range p → ∃ u' v : 𝕀 → X, IsTwoArcs u' v ∧ range u' = L ∧ u' 0 = a ∧ u' 1 = b ∧
        range u' ∪ range v = F := by
    intro p q hpq hp0 hp1 hun hsub
    have h1 : range u ⊆ range p := by
      rintro _ ⟨t, rfl⟩
      rcases eq_or_ne t 0 with rfl | h0
      · exact ⟨0, hp0.trans hf0.symm⟩
      rcases eq_or_ne t 1 with rfl | h1
      · exact ⟨1, hp1.trans hf1.symm⟩
      exact hsub ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩,
        rfl⟩
    have h2 : range p ⊆ range u := by
      rintro _ ⟨r, rfl⟩
      by_contra hcon
      have hA : IsClosed (p '' Iic r) := (isClosed_Iic.isCompact.image hpq.1.1).isClosed
      have hB : IsClosed (p '' Ici r) := (isClosed_Ici.isCompact.image hpq.1.1).isClosed
      have hcov : range u ⊆ p '' Iic r ∪ p '' Ici r := fun x hx => by
        obtain ⟨y, rfl⟩ := h1 hx
        rcases le_total y r with h | h
        · exact .inl ⟨y, h, rfl⟩
        · exact .inr ⟨y, h, rfl⟩
      obtain ⟨x, hx, hxA, hxB⟩ := isPreconnected_closed_iff.mp (isPreconnected_range hu.1) _ _ hA
        hB hcov
        ⟨a, ⟨0, hf0⟩, 0, unitInterval.nonneg', hp0⟩ ⟨b, ⟨1, hf1⟩, 1, unitInterval.le_one', hp1⟩
      obtain ⟨y, hy, rfl⟩ := hxA
      obtain ⟨y', hy', he⟩ := hxB
      have h3 : y' = y := hpq.1.2 he
      subst h3
      have h4 : y' = r := le_antisymm hy hy'
      subst h4
      exact hcon hx
    have hre : range u = range p := Subset.antisymm h1 h2
    refine ⟨u, q, ⟨hu, hpq.2, ?_, ?_, ?_⟩, hru, hf0, hf1, by rw [hre]; exact hun⟩
    · rw [hpq.3, hp0]
      exact hf0.symm
    · rw [hpq.4, hp1]
      exact hf1.symm
    · intro s t hst
      obtain ⟨r, hr⟩ := h1 ⟨s, rfl⟩
      have h3 := hpq.5 r t (hr.trans hst)
      rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · subst h3
        refine .inl ⟨hu.2 (?_ : u s = u 0), h4⟩
        rw [← hr, hp0]
        exact hf0.symm
      · subst h3
        refine .inr ⟨hu.2 (?_ : u s = u 1), h4⟩
        rw [← hr, hp1]
        exact hf1.symm
  have hswap : IsTwoArcs q p := ⟨hpq.2, hpq.1, hpq.3.symm, hpq.4.symm,
    fun s t h => (hpq.5 t s h.symm).imp And.symm And.symm⟩
  have hq0 : q 0 = a := hpq.3.trans hp0
  have hq1 : q 1 = b := hpq.4.trans hp1
  have hconn : IsPreconnected (u '' Ioo 0 1) := isPreconnected_Ioo.image _ hu.1.continuousOn
  have hAc : IsClosed (range p) := (isCompact_range hpq.1.1).isClosed
  have hBc : IsClosed (range q) := (isCompact_range hpq.2.1).isClosed
  have hcov : u '' Ioo 0 1 ⊆ range p ∪ range q := by
    rintro _ ⟨t, -, rfl⟩
    rw [hun]
    exact hLF (hru ▸ ⟨t, rfl⟩)
  by_cases hm : u '' Ioo 0 1 ⊆ range p
  · exact key hpq hp0 hp1 hun hm
  by_cases hm' : u '' Ioo 0 1 ⊆ range q
  · exact key hswap hq0 hq1 (by rw [union_comm]; exact hun) hm'
  exfalso
  obtain ⟨x, hx, hxp⟩ := not_subset.mp hm
  obtain ⟨y, hy, hyq⟩ := not_subset.mp hm'
  obtain ⟨z, ⟨t, ht, rfl⟩, ⟨r, hr⟩, ⟨r', hr'⟩⟩ := isPreconnected_closed_iff.mp hconn _ _ hAc hBc
    hcov
    ⟨y, hy, (hcov hy).resolve_right hyq⟩ ⟨x, hx, (hcov hx).resolve_left hxp⟩
  rcases hpq.5 r r' (hr.trans hr'.symm) with ⟨h1, -⟩ | ⟨h1, -⟩
  · subst h1
    have : t = 0 := hu.2 (hr.symm.trans (hp0.trans hf0.symm))
    exact ht.1.ne' this
  · subst h1
    have : t = 1 := hu.2 (hr.symm.trans (hp1.trans hf1.symm))
    exact ht.2.ne this

section disc

variable {T : Type u} [TopologicalSpace T] [CompactSpace T] [T2Space T]

omit [CompactSpace T] in
/-- `push_side` for a line `L` of a disc: the line lies in the boundary of the disc, or it is a
chord. -/
theorem push_disc (hT : ∀ x : T, IsInteriorPoint x) {D L Y C : Set T} {a b : T}
  (hD : IsClosedDisc D)
    (hL : IsLineWithEnds L a b) (hLD : L ⊆ D)
    (hcase : (L ⊆ discBd D ∧ Y ∩ D ⊆ L) ∨ (L \ {a, b} ⊆ D \ discBd D ∧ Y ∩ D ⊆ {a, b}))
    (ha : a ∈ discBd D) (hb : b ∈ discBd D)
    (hY : IsClosed Y) (haY : a ∈ Y) (hbY : b ∈ Y) (hC : IsClosed C) (hCL : C ∩ L ⊆ {a, b}) :
    ∃ h : T ≃ₜ T, (∀ y ∈ Y, h y = y) ∧ h '' C ∩ D ⊆ {a, b} := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT x).isManifoldPoint
  have one : ∀ {D Y C : Set T}, IsClosedDisc D → L ⊆ discBd D → IsClosed Y → Y ∩ D ⊆ L → a ∈ Y
    → b ∈ Y →
      IsClosed C → C ∩ L ⊆ {a, b} → ∃ h : T ≃ₜ T, (∀ y ∈ Y, h y = y) ∧ h '' C ∩ D ⊆ {a, b} := by
    intro D Y C hD hLb hY hYD haY hbY hC hCL
    obtain ⟨u, v, huv, hr, h0, h1, hun⟩ := exists_arcs_of_line hD.isOArc_discBd hL hLb
    subst h0 h1
    exact push_side hman hD (fun x _ => hT x) huv hun hY (hr ▸ hYD) haY hbY hC (hr ▸ hCL)
  rcases hcase with ⟨hLb, hYD⟩ | ⟨hLi, hYD⟩
  · exact one hD hLb hY hYD haY hbY hC hCL
  · have hab : a ≠ b := by
      obtain ⟨f, rfl, rfl⟩ := hL
      intro he
      exact zero_ne_one (f.injective (Subtype.ext he))
    have haL : a ∈ L := by
      obtain ⟨f, h0, -⟩ := hL
      exact h0 ▸ (f 0).2
    have hbL : b ∈ L := by
      obtain ⟨f, -, h1⟩ := hL
      exact h1 ▸ (f 1).2
    have hmeet : L ∩ discBd D = {a, b} := by
      ext x
      constructor
      · rintro ⟨hx, hxb⟩
        by_contra hcon
        exact (hLi ⟨hx, hcon⟩).2 hxb
      · rintro (rfl | rfl)
        · exact ⟨haL, ha⟩
        · exact ⟨hbL, hb⟩
    obtain ⟨A₁, A₂, Δ₁, Δ₂, -, -, d1, d2, hun, hint, b1, b2, -⟩ := disc_iArc D L a b hD hLD hab hL
      hmeet
    have hL1 : L ⊆ Δ₁ := fun x hx => (hint ▸ hx : x ∈ Δ₁ ∩ Δ₂).1
    have hL2 : L ⊆ Δ₂ := fun x hx => (hint ▸ hx : x ∈ Δ₁ ∩ Δ₂).2
    obtain ⟨h₁, g1, g2⟩ := one (Y := Y ∪ Δ₂) d1 (b1 ▸ subset_union_right)
      (hY.union d2.isClosed)
      (by
        rintro x ⟨hx | hx, hx'⟩
        · rcases hYD ⟨hx, hun ▸ Or.inl hx'⟩ with rfl | rfl
          · exact haL
          · exact hbL
        · exact hint ▸ ⟨hx', hx⟩)
      (.inl haY) (.inl hbY) hC hCL
    have hC' : IsClosed (h₁ '' C) := h₁.isClosed_image.mpr hC
    obtain ⟨h₂, g3, g4⟩ := one (Y := Y ∪ Δ₁) (C := h₁ '' C) d2 (b2 ▸ subset_union_right)
      (hY.union d1.isClosed)
      (by
        rintro x ⟨hx | hx, hx'⟩
        · rcases hYD ⟨hx, hun ▸ Or.inr hx'⟩ with rfl | rfl
          · exact haL
          · exact hbL
        · exact hint ▸ ⟨hx, hx'⟩)
      (.inl haY) (.inl hbY) hC'
      (by
        rintro _ ⟨⟨y, hy, rfl⟩, hyL⟩
        have h3 : h₁ (h₁ y) = h₁ y := g1 _ (.inr (hL2 hyL))
        have h4 : h₁ y = y := h₁.injective h3
        rw [h4] at hyL ⊢
        exact hCL ⟨hy, hyL⟩)
    refine ⟨h₁.trans h₂, fun y hy => ?_, ?_⟩
    · change h₂ (h₁ y) = y
      rw [g1 y (.inl hy), g3 y (.inl hy)]
    · rintro _ ⟨⟨y, hy, rfl⟩, hyD⟩
      change h₂ (h₁ y) ∈ _
      change h₂ (h₁ y) ∈ D at hyD
      rw [← hun] at hyD
      rcases hyD with hy1 | hy2
      · have h3 : h₂ (h₂ (h₁ y)) = h₂ (h₁ y) := g3 _ (.inr hy1)
        have h4 : h₂ (h₁ y) = h₁ y := h₂.injective h3
        rw [h4] at hy1 ⊢
        exact g2 ⟨mem_image_of_mem _ hy, hy1⟩
      · exact g4 ⟨mem_image_of_mem _ (mem_image_of_mem _ hy), hy2⟩

end disc

theorem exists_capAll_aux (n : ℕ) : ∀ (S : Type u) [TopologicalSpace S] (l : List (Set S)),
    l.length = n → IsSurface S → (∀ F ∈ l, IsPreconnected F ∧ F ⊆ bd S) → bd S ⊆ ⋃ F ∈ l, F →
    ∃ (T : Type u) (_ : TopologicalSpace T) (j : S → T) (K : Set T), IsClosedSurface T ∧
      IsClosedEmbedding j ∧ IsClosed K ∧ range j ∪ K = univ ∧ range j ∩ K = j '' bd S ∧
      (ConnectedSpace S → ConnectedSpace T) ∧
      ∃ 𝓓 : Set (Set T), 𝓓.Finite ∧ ⋃₀ 𝓓 = K ∧ (∀ D ∈ 𝓓, IsClosedDisc D ∧ IsPreconnected
        (D ∩ range j) ∧ (D ∩ range j).Nonempty) ∧
        ∀ D ∈ 𝓓, ∀ D' ∈ 𝓓, D ≠ D' → Disjoint D D' := by
  classical
  induction n with
  | zero =>
    intro S _ l hl hS _ hcov
    have hb : ∀ x : S, x ∉ bd S := fun x hx => by
      have := hcov hx
      rw [List.length_eq_zero_iff.mp hl] at this
      simp at this
    refine ⟨S, _, id, ∅, ⟨hS.1, hS.2.1, fun x => ?_⟩, IsClosedEmbedding.id, isClosed_empty, by simp,
      by simp [Set.eq_empty_iff_forall_notMem.mpr hb], id, ∅, by simp, by simp, by simp, by simp⟩
    by_contra hcon
    exact hb x hcon
  | succ n ih =>
    intro S _ l hl hS hl1 hcov
    obtain ⟨F, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    have hl' : l'.length = n := by simpa using hl
    rcases F.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · refine ih S l' hl' hS (fun F' h => hl1 F' (.tail _ h)) fun y hy => ?_
      have := hcov hy
      simpa using this
    have hxb : x ∈ bd S := (hl1 F (.head _)).2 hx
    let C := connectedComponentIn (bd S) x
    have hC : IsCuff C := ⟨x, hxb, rfl⟩
    have hCb : C ⊆ bd S := connectedComponentIn_subset _ _
    have hFC : F ⊆ C := (hl1 F (.head _)).1.subset_connectedComponentIn hx (hl1 F (.head _)).2
    obtain ⟨S', _, ι, Δ, hS', hι, hΔ, hcov', hmeet, -, hbdS⟩ := paste_disc.{u} S C hS hC
    have hιi := hι.injective
    have : T2Space S' := hS'.2.1
    obtain ⟨T, _, j, K, hT, hj, hK, hu, hi, hconn, 𝓓, h𝓓f, h𝓓u, h𝓓d, h𝓓j⟩ := ih S' (l'.map fun F'
      => ι '' (F' \ C)) (by simpa using hl') hS'
      (by
        intro G hG
        obtain ⟨F', hF', rfl⟩ := List.mem_map.mp hG
        obtain ⟨h1, h2⟩ := hl1 F' (.tail _ hF')
        constructor
        · by_cases hne : (F' ∩ C).Nonempty
          · obtain ⟨y, hy, hyC⟩ := hne
            have h3 : F' ⊆ C := by
              have h4 := h1.subset_connectedComponentIn hy h2
              rwa [← connectedComponentIn_eq hyC] at h4
            rw [sdiff_eq_empty.mpr h3, image_empty]
            exact isPreconnected_empty
          · have h3 : F' \ C = F' := by
              ext z
              exact ⟨fun h => h.1, fun h => ⟨h, fun hc => hne ⟨z, h, hc⟩⟩⟩
            rw [h3]
            exact h1.image _ hι.continuous.continuousOn
        · rw [hbdS]
          exact image_mono (sdiff_subset_sdiff_left h2))
      (by
        rw [hbdS]
        rintro _ ⟨y, ⟨hy, hyC⟩, rfl⟩
        have h1 := hcov hy
        simp only [List.mem_cons, iUnion_iUnion_eq_or_left, mem_union, mem_iUnion,
          exists_prop] at h1
        rcases h1 with h1 | ⟨F', hF', h1⟩
        · exact absurd (hFC h1) hyC
        · exact Set.mem_iUnion₂.mpr ⟨_, List.mem_map.mpr ⟨F', hF', rfl⟩, y, ⟨h1, hyC⟩, rfl⟩)
    have hΔK : Disjoint (j '' Δ) K := Set.disjoint_left.mpr fun y hy hyK => by
      obtain ⟨z, hz, rfl⟩ := hy
      have h2 : j z ∈ j '' bd S' := hi ▸ ⟨⟨z, rfl⟩, hyK⟩
      obtain ⟨z', hz', he⟩ := h2
      have h3 : z' = z := hj.injective he
      subst h3
      rw [hbdS] at hz'
      obtain ⟨w, hw, rfl⟩ := hz'
      have h4 : ι w ∈ ι '' C := hmeet ▸ ⟨⟨w, rfl⟩, hz⟩
      obtain ⟨v, hv, he'⟩ := h4
      have h5 : v = w := hιi he'
      exact hw.2 (h5 ▸ hv)
    have hrange : ∀ D ∈ 𝓓, D ∩ range (j ∘ ι) = D ∩ range j := fun D hD => by
      ext y
      constructor
      · rintro ⟨h1, w, rfl⟩
        exact ⟨h1, _, rfl⟩
      · rintro ⟨h1, z, rfl⟩
        refine ⟨h1, ?_⟩
        have h2 : z ∈ range ι ∪ Δ := hcov' ▸ mem_univ z
        rcases h2 with ⟨w, rfl⟩ | h2
        · exact ⟨w, rfl⟩
        · exact absurd (h𝓓u ▸ (⟨D, hD, h1⟩ : j z ∈ ⋃₀ 𝓓)) (Set.disjoint_left.mp hΔK ⟨z, h2, rfl⟩)
    have hΔj : IsClosedDisc (j '' Δ) := by
      obtain ⟨φ⟩ := id hΔ
      exact ⟨φ.trans (hj.isEmbedding.homeomorphImage Δ)⟩
    have hΔr : j '' Δ ∩ range (j ∘ ι) = (j ∘ ι) '' C := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, w, he⟩
        have he' : ι w = z := hj.injective he
        have h4 : ι w ∈ ι '' C := hmeet ▸ ⟨⟨w, rfl⟩, he' ▸ hz⟩
        obtain ⟨v, hv, h5⟩ := h4
        exact ⟨v, hv, by simp only [Function.comp, h5, he']⟩
      · rintro ⟨w, hw, rfl⟩
        have h1 : ι w ∈ range ι ∩ Δ := hmeet ▸ mem_image_of_mem ι hw
        exact ⟨⟨_, h1.2, rfl⟩, w, rfl⟩
    have hnotin : j '' Δ ∉ 𝓓 := fun h' => by
      obtain ⟨y, hy⟩ := hΔ.nonempty_discInt
      exact Set.disjoint_left.mp hΔK ⟨y, hy.1, rfl⟩ (h𝓓u ▸ (⟨_, h', ⟨y, hy.1, rfl⟩⟩ : j y ∈ ⋃₀ 𝓓))
    refine ⟨T, _, j ∘ ι, K ∪ j '' Δ, hT, hj.comp hι, hK.union (hj.isClosedMap _ hΔ.isClosed), ?_,
      ?_, fun hc => hconn ?_,
      insert (j '' Δ) 𝓓, h𝓓f.insert _, ?_, ?_, ?_⟩
    rotate_left 3
    · rw [sUnion_insert, h𝓓u, union_comm]
    · rintro D (rfl | hD)
      · refine ⟨hΔj, ?_, ?_⟩
        · rw [hΔr]
          exact (isPreconnected_connectedComponentIn).image _ (hj.comp hι).continuous.continuousOn
        · rw [hΔr]
          exact ⟨_, x, mem_connectedComponentIn hxb, rfl⟩
      · rw [hrange D hD]
        exact h𝓓d D hD
    · have hdK : ∀ D ∈ 𝓓, Disjoint (j '' Δ) D := fun D hD =>
        hΔK.mono_right (h𝓓u ▸ subset_sUnion_of_mem hD)
      rintro D (rfl | hD) D' (rfl | hD') hne
      · exact absurd rfl hne
      · exact hdK D' hD'
      · exact (hdK D hD).symm
      · exact h𝓓j D hD D' hD' hne
    rotate_left 2
    · have hCne : (ι '' C).Nonempty := ⟨ι x, x, mem_connectedComponentIn hxb, rfl⟩
      obtain ⟨y, hy⟩ := hCne
      have hy' : y ∈ range ι ∩ Δ := hmeet ▸ hy
      have h1 : IsPreconnected (range ι) := isPreconnected_range hι.continuous
      have h2 : IsPreconnected Δ := by
        obtain ⟨φ⟩ := id hΔ
        have : Δ = range fun t => (φ t).1 := by
          ext z
          constructor
          · intro hz
            exact ⟨φ.symm ⟨z, hz⟩, by simp⟩
          · rintro ⟨t, rfl⟩
            exact (φ t).2
        rw [this]
        have : PreconnectedSpace ClosedUnitDisc := Subtype.preconnectedSpace
          (convex_closedBall _ _).isPreconnected
        exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
      have h3 := h1.union' ⟨y, hy'.1, hy'.2⟩ h2
      rw [hcov'] at h3
      exact { toPreconnectedSpace := ⟨h3⟩, toNonempty := ⟨y⟩ }
    · rw [eq_univ_iff_forall]
      intro y
      have h1 : y ∈ range j ∪ K := hu ▸ mem_univ y
      rcases h1 with ⟨z, rfl⟩ | h1
      · have h2 : z ∈ range ι ∪ Δ := hcov' ▸ mem_univ z
        rcases h2 with ⟨w, rfl⟩ | h2
        · exact .inl ⟨w, rfl⟩
        · exact .inr (.inr ⟨z, h2, rfl⟩)
      · exact .inr (.inl h1)
    · ext y
      constructor
      · rintro ⟨⟨w, rfl⟩, h1 | ⟨z, hz, he⟩⟩
        · have h2 : (j ∘ ι) w ∈ j '' bd S' := hi ▸ ⟨⟨_, rfl⟩, h1⟩
          obtain ⟨z, hz, he⟩ := h2
          rw [hbdS] at hz
          obtain ⟨v, hv, rfl⟩ := hz
          have : v = w := hιi (hj.injective he)
          subst this
          exact ⟨v, hv.1, rfl⟩
        · have h3 : ι w = z := hj.injective he.symm
          have h4 : ι w ∈ ι '' C := hmeet ▸ ⟨⟨w, rfl⟩, h3 ▸ hz⟩
          obtain ⟨v, hv, he'⟩ := h4
          have : v = w := hιi he'
          subst this
          exact ⟨v, hCb hv, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨⟨w, rfl⟩, ?_⟩
        by_cases hwC : w ∈ C
        · have h1 : ι w ∈ range ι ∩ Δ := hmeet ▸ mem_image_of_mem ι hwC
          exact .inr ⟨_, h1.2, rfl⟩
        · have h1 : j (ι w) ∈ range j ∩ K := hi ▸ mem_image_of_mem j (hbdS ▸ ⟨w, ⟨hw, hwC⟩, rfl⟩)
          exact .inl h1.2

/-- Capping all the cuffs of a surface gives a surface without boundary, and the caps are disjoint
closed discs. -/
theorem exists_capAll_discs (S : Type u) [TopologicalSpace S] (hS : IsSurface S) :
    ∃ (T : Type u) (_ : TopologicalSpace T) (j : S → T) (K : Set T), IsClosedSurface T ∧
      IsClosedEmbedding j ∧ IsClosed K ∧ range j ∪ K = univ ∧ range j ∩ K = j '' bd S ∧
      (ConnectedSpace S → ConnectedSpace T) ∧
      ∃ 𝓓 : Set (Set T), 𝓓.Finite ∧ ⋃₀ 𝓓 = K ∧ (∀ D ∈ 𝓓, IsClosedDisc D ∧ IsPreconnected
        (D ∩ range j) ∧ (D ∩ range j).Nonempty) ∧
        ∀ D ∈ 𝓓, ∀ D' ∈ 𝓓, D ≠ D' → Disjoint D D' := by
  classical
  have hf := (cuff_statement.{u} S hS).2.1
  refine exists_capAll_aux _ S hf.toFinset.toList rfl hS (fun F hF => ?_) fun x hx => ?_
  · have hF' : F ∈ cuffs S := by simpa using hF
    obtain ⟨x, hx, rfl⟩ := hF'
    exact ⟨isPreconnected_connectedComponentIn, connectedComponentIn_subset _ _⟩
  · have hm : connectedComponentIn (bd S) x ∈ hf.toFinset.toList := by
      rw [Finset.mem_toList, Set.Finite.mem_toFinset]
      exact ⟨x, hx, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨_, hm, mem_connectedComponentIn hx⟩

/-- Capping all the cuffs of a surface gives a surface without boundary. -/
theorem exists_capAll (S : Type u) [TopologicalSpace S] (hS : IsSurface S) :
    ∃ (T : Type u) (_ : TopologicalSpace T) (j : S → T) (K : Set T), IsClosedSurface T ∧
      IsClosedEmbedding j ∧ IsClosed K ∧ range j ∪ K = univ ∧ range j ∩ K = j '' bd S ∧
      (ConnectedSpace S → ConnectedSpace T) := by
  obtain ⟨T, t, j, K, h1, h2, h3, h4, h5, h6, -⟩ := exists_capAll_discs S hS
  exact ⟨T, t, j, K, h1, h2, h3, h4, h5, h6⟩

/-- Push a curve off finitely many discs by moving each disc independently. The line in a disc is
either an interior chord or a boundary arc containing the part of the fixed set in that disc. -/
theorem push_off_discs {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {ι : Type} [Finite ι] {N Z : Set S} {D L : ι → Set S}
    (hN : N.Finite) (hZ : IsClosed Z) (hD : ∀ i, IsClosedDisc (D i))
    (hL : ∀ i, ∃ a b, IsLineWithEnds (L i) a b ∧ D i ∩ N = {a, b} ∧
      a ∈ discBd (D i) ∧ b ∈ discBd (D i) ∧ L i ⊆ D i ∧
      ((L i \ {a, b} ⊆ D i \ discBd (D i) ∧ D i ∩ bd S ⊆ N ∧ D i ∩ Z ⊆ N) ∨
        (L i ⊆ discBd (D i) ∧ D i ∩ bd S ⊆ L i ∧ D i ∩ Z ⊆ L i)))
    (hDD : ∀ i j, i ≠ j → D i ∩ D j ⊆ N) {F : Set S}
    (hF : IsOArc F) (hFZ : F ∩ Z ⊆ N) (hFL : ∀ i, F ∩ L i ⊆ N) :
    ∃ h : S ≃ₜ S, (∀ n ∈ N, h n = n) ∧ (h '' F) ∩ Z ⊆ N ∧ ∀ i, (h '' F) ∩ D i ⊆ N := by
  classical
  obtain ⟨hcpt, ht2, _⟩ := id hS
  obtain ⟨T, _, j, K, hT, hj, hK, hu, hi, -⟩ := exists_capAll S hS
  obtain ⟨hTc, hTt, hTi⟩ := id hT
  obtain ⟨φ⟩ := id hF
  have : Nonempty S := ⟨(φ 1).1⟩
  have := Fintype.ofFinite ι
  have hji := hj.injective
  obtain ⟨j', hjc, hjl⟩ := exists_inv_of_compactOn isCompact_univ hj.continuous.continuousOn
    hji.injOn
  have hdisc : ∀ {E : Set S}, IsClosedDisc E → IsClosedDisc (j '' E) ∧ discBd (j '' E)
    = j '' discBd E :=
    fun hE => hE.image hj.continuous.continuousOn (hjc.mono (image_mono (subset_univ _)))
      (hjl.mono (subset_univ _))
  let Z' : Set T := K ∪ (j '' N ∪ j '' Z)
  have hZ' : IsClosed Z' := hK.union ((hj.isClosedMap _ hN.isClosed).union (hj.isClosedMap _ hZ))
  have hFc : IsClosed (j '' F) := hj.isClosedMap _ hF.isCompact.isClosed
  have main : ∀ s : Finset ι, ∃ h : T ≃ₜ T, (∀ y ∈ Z', h y = y) ∧ (∀ k, k ∉ s → ∀ y ∈ j '' D k, h y
    = y) ∧
      ∀ k ∈ s, h '' (j '' F) ∩ j '' D k ⊆ j '' N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨Homeomorph.refl T, fun _ _ => rfl, fun _ _ _ _ => rfl, fun k hk => absurd hk (by simp)⟩
    | insert i s his ih =>
      obtain ⟨h, h1, h2, h3⟩ := ih
      obtain ⟨a, b, hLi, hDN, ha, hb, hLD, hcase⟩ := hL i
      have haL : a ∈ L i := by
        obtain ⟨f, h4, -⟩ := hLi
        exact h4 ▸ (f 0).2
      have hbL : b ∈ L i := by
        obtain ⟨f, -, h4⟩ := hLi
        exact h4 ▸ (f 1).2
      have haN : a ∈ D i ∩ N := hDN ▸ Or.inl rfl
      have hbN : b ∈ D i ∩ N := hDN ▸ Or.inr rfl
      let Y : Set T := Z' ∪ ⋃ k ∈ {k | k ≠ i}, j '' D k
      have hY : IsClosed Y := hZ'.union ((Set.toFinite _).isClosed_biUnion fun k _ =>
        hj.isClosedMap _ (hD k).isClosed)
      obtain ⟨d1, d2⟩ := hdisc (hD i)
      have hYN : ∀ x ∈ Y, ∀ y ∈ D i, x = j y → y ∈ N ∨ y ∈ bd S ∨ y ∈ Z := by
        rintro x (hx | hx) y hy rfl
        · rcases hx with hx | ⟨w, hw, he⟩ | ⟨w, hw, he⟩
          · obtain ⟨w, hw, he⟩ : j y ∈ j '' bd S := hi ▸ ⟨⟨y, rfl⟩, hx⟩
            exact .inr (.inl (hji he ▸ hw))
          · exact .inl (hji he ▸ hw)
          · exact .inr (.inr (hji he ▸ hw))
        · obtain ⟨k, hk, w, hw, he⟩ := mem_iUnion₂.mp hx
          exact .inl (hDD i k hk.symm ⟨hy, hji he ▸ hw⟩)
      have hline : IsLineWithEnds (j '' L i) (j a) (j b) := by
        obtain ⟨f, h4, h5⟩ := hLi
        refine ⟨f.trans (hj.isEmbedding.homeomorphImage (L i)), ?_, ?_⟩
        · exact congrArg j h4
        · exact congrArg j h5
      have hC : IsClosed (h '' (j '' F)) := h.isClosed_image.mpr hFc
      obtain ⟨h₂, g1, g2⟩ := push_disc (T := T) hTi (D := j '' D i) (L := j '' L i) (Y := Y)
        (C := h '' (j '' F)) d1 hline (image_mono hLD)
        (by
          rcases hcase with ⟨hinside, hbdN, hZN⟩ | ⟨hLb, hbdL, hZL⟩
          · right
            refine ⟨?_, ?_⟩
            · rintro _ ⟨⟨y, hy, rfl⟩, hne⟩
              have hy' : y ∉ ({a, b} : Set S) := fun hm => hne (by
                rcases hm with rfl | rfl
                · exact .inl rfl
                · exact .inr rfl)
              obtain ⟨hd, hnotBd⟩ := hinside ⟨hy, hy'⟩
              refine ⟨mem_image_of_mem j hd, ?_⟩
              rw [d2]
              rintro ⟨w, hw, he⟩
              exact hnotBd (hji he ▸ hw)
            · rintro x ⟨hx, y, hy, rfl⟩
              have hyN : y ∈ N := by
                rcases hYN _ hx y hy rfl with hN | hbd | hZ
                · exact hN
                · exact hbdN ⟨hy, hbd⟩
                · exact hZN ⟨hy, hZ⟩
              have hyEnds : y ∈ ({a, b} : Set S) := hDN ▸ ⟨hy, hyN⟩
              rcases hyEnds with rfl | rfl
              · exact .inl rfl
              · exact .inr rfl
          · left
            refine ⟨?_, ?_⟩
            · rw [d2]
              exact image_mono hLb
            · rintro x ⟨hx, y, hy, rfl⟩
              refine mem_image_of_mem j ?_
              rcases hYN _ hx y hy rfl with hN | hbd | hZ
              · have hyEnds : y ∈ ({a, b} : Set S) := hDN ▸ ⟨hy, hN⟩
                rcases hyEnds with rfl | rfl
                · exact haL
                · exact hbL
              · exact hbdL ⟨hy, hbd⟩
              · exact hZL ⟨hy, hZ⟩)
        (by rw [d2]; exact mem_image_of_mem j ha) (by rw [d2]; exact mem_image_of_mem j hb)
        hY (.inl (.inr (.inl (mem_image_of_mem j haN.2)))) (.inl (.inr (.inl
          (mem_image_of_mem j hbN.2))))
        hC
        (by
          rintro _ ⟨⟨_, ⟨y, hy, rfl⟩, rfl⟩, w, hw, he⟩
          have h4 : h (j w) = j w := h2 i (by simpa using his) _ (mem_image_of_mem j (hLD hw))
          have h5 : j w = j y := h.injective (h4.trans he)
          have h6 : w = y := hji h5
          subst h6
          have h7 : w ∈ D i ∩ N := ⟨hLD hw, hFL i ⟨hy, hw⟩⟩
          rw [hDN] at h7
          rw [← he]
          rcases h7 with rfl | rfl
          · exact .inl rfl
          · exact .inr rfl)
      refine ⟨h.trans h₂, fun y hy => ?_, fun k hk y hy => ?_, fun k hk => ?_⟩
      · change h₂ (h y) = y
        rw [h1 y hy, g1 y (.inl hy)]
      · have hk1 : k ≠ i := fun he => hk (by simp [he])
        have hk2 : k ∉ s := fun he => hk (by simp [he])
        change h₂ (h y) = y
        rw [h2 k hk2 y hy, g1 y (.inr (mem_iUnion₂.mpr ⟨k, hk1, hy⟩))]
      · rintro _ ⟨⟨_, ⟨y, hy, rfl⟩, rfl⟩, hx⟩
        by_cases hki : k = i
        · subst hki
          have h4 : (h.trans h₂) (j y) ∈ h₂ '' (h '' (j '' F)) ∩ j '' D k :=
            ⟨⟨_, ⟨_, mem_image_of_mem j hy, rfl⟩, rfl⟩, hx⟩
          rcases g2 h4 with h5 | h5
          · rw [h5]
            exact mem_image_of_mem j haN.2
          · rw [h5]
            exact mem_image_of_mem j hbN.2
        · have hks : k ∈ s := by simpa [hki] using hk
          have h4 : h₂ (h₂ (h (j y))) = h₂ (h (j y)) := g1 _ (.inr (mem_iUnion₂.mpr ⟨k, hki, hx⟩))
          have h5 : h₂ (h (j y)) = h (j y) := h₂.injective h4
          change h₂ (h (j y)) ∈ _ at hx
          change h₂ (h (j y)) ∈ _
          rw [h5] at hx ⊢
          exact h3 k hks ⟨⟨_, mem_image_of_mem j hy, rfl⟩, hx⟩
  obtain ⟨H, f1, -, f3⟩ := main Finset.univ
  have hfixK : ∀ y ∈ K, H y = y := fun y hy => f1 y (.inl hy)
  have hran : ∀ x, x ∈ range j ↔ H x ∈ range j := by
    intro x
    constructor
    · intro hx
      by_contra hcon
      have h1 : H x ∈ K := (hu ▸ mem_univ (H x) : H x ∈ range j ∪ K).resolve_left hcon
      have h2 := H.injective (hfixK _ h1)
      exact hcon (by rw [h2]; exact hx)
    · intro hx
      by_contra hcon
      have h1 : x ∈ K := (hu ▸ mem_univ x : x ∈ range j ∪ K).resolve_left hcon
      exact hcon (hfixK x h1 ▸ hx)
  let e : S ≃ₜ range j := hj.isEmbedding.toHomeomorph
  let h : S ≃ₜ S := e.trans ((H.subtype hran).trans e.symm)
  have hjh : ∀ x, j (h x) = H (j x) := fun x => by
    have h1 : e (h x) = (H.subtype hran) (e x) := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hfixN : ∀ n ∈ N, h n = n := fun n hn =>
    hji ((hjh n).trans (f1 _ (.inr (.inl (mem_image_of_mem j hn)))))
  refine ⟨h, hfixN, ?_, fun i => ?_⟩
  · rintro _ ⟨⟨y, hy, rfl⟩, hz⟩
    have h1 : H (j (h y)) = j (h y) := f1 _ (.inr (.inr (mem_image_of_mem j hz)))
    rw [hjh] at h1
    have h2 : H (j y) = j y := H.injective h1
    have h3 : h y = y := hji ((hjh y).trans h2)
    rw [h3] at hz ⊢
    exact hFZ ⟨hy, hz⟩
  · rintro _ ⟨⟨y, hy, rfl⟩, hz⟩
    obtain ⟨w, hw, he⟩ := f3 i (Finset.mem_univ i)
      ⟨⟨j y, mem_image_of_mem j hy, (hjh y).symm⟩, mem_image_of_mem j hz⟩
    exact hji he ▸ hw

/-- **Pushing a closed set off discs.** See the module docstring. -/
theorem push_off : PushOffStatement := by
  intro S _ hS ι _ N Z D L hN hZ hD hL hDD hDZ F hF hFZ hFL
  refine push_off_discs hS hN hZ hD ?_ hDD hF hFZ hFL
  intro i
  obtain ⟨a, b, hLi, hDN, ha, hb, hLD, hcase⟩ := hL i
  refine ⟨a, b, hLi, hDN, ha, hb, hLD, ?_⟩
  rcases hcase with ⟨hinside, hbdN⟩ | hboundary
  · exact .inl ⟨hinside, hbdN, hDZ i⟩
  · have hLb : L i ⊆ discBd (D i) := by
      rw [hboundary]
      rintro y ⟨hyD, hybd⟩
      by_contra hy_not
      exact hybd (isInteriorPoint_of_mem_discInt hS.2.2 (hD i) ⟨hyD, hy_not⟩)
    refine .inr ⟨hLb, hboundary.symm.subset, ?_⟩
    intro y hy
    have hyEnds : y ∈ ({a, b} : Set S) := hDN ▸ ⟨hy.1, hDZ i hy⟩
    rcases hyEnds with rfl | rfl
    · obtain ⟨f, h0, _⟩ := hLi
      exact h0 ▸ (f 0).2
    · obtain ⟨f, _, h1⟩ := hLi
      exact h1 ▸ (f 1).2

end GraphMinor.Surface
