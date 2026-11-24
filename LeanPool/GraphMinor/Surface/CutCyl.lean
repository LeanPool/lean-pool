/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutLoop

/-!
# The model with two holes is a cylinder

The unit disc with four sides is mapped onto the closed cylinder as follows. The radial map `nu`
sends the unit disc to the
square `|x| + |y| ≤ 1`, and sends the four arcs of the unit circle to the four sides of this square.
Two opposite sides are
pasted to give a cylinder. This shows that the word `t r t⁻¹ r'` presents the cylinder
(`presents_cyl`), and its normal form
is `Σ(0, 0, 2)` (`nonempty_cyl_homeo`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

/-- The `ℓ¹` norm. -/
noncomputable def nn (z : ℂ) : ℝ := |z.re| + |z.im|

theorem nn_nonneg (z : ℂ) : 0 ≤ nn z := by
  unfold nn
  positivity

theorem norm_le_nn (z : ℂ) : ‖z‖ ≤ nn z := Complex.norm_le_abs_re_add_abs_im z

theorem nn_pos {z : ℂ} (h : z ≠ 0) : 0 < nn z := (norm_pos_iff.mpr h).trans_le (norm_le_nn z)

theorem continuous_nn : Continuous nn := by
  unfold nn
  fun_prop

theorem nn_smul {c : ℝ} (hc : 0 ≤ c) (z : ℂ) : nn ((c : ℂ) * z) = c * nn z := by
  simp only [nn, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.mul_im, add_zero, abs_mul, abs_of_nonneg hc]
  ring

theorem norm_smul' {c : ℝ} (hc : 0 ≤ c) (z : ℂ) : ‖(c : ℂ) * z‖ = c * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]

/-- The radial map from the round disc to the square. -/
noncomputable def nu (z : ℂ) : ℂ := ((‖z‖ / nn z : ℝ) : ℂ) * z

/-- The radial map from the square to the round disc. -/
noncomputable def mu (w : ℂ) : ℂ := ((nn w / ‖w‖ : ℝ) : ℂ) * w

theorem nu_zero : nu 0 = 0 := by simp [nu]

theorem nn_nu (z : ℂ) : nn (nu z) = ‖z‖ := by
  by_cases h : z = 0
  · subst h
    simp [nu_zero, nn]
  · have h1 := nn_pos h
    rw [nu, nn_smul (by positivity)]
    field_simp

theorem mu_nu (z : ℂ) : mu (nu z) = z := by
  by_cases h : z = 0
  · subst h
    simp [nu_zero, mu]
  · have h1 := nn_pos h
    have h2 := norm_pos_iff.mpr h
    have hc : 0 < ‖z‖ / nn z := by positivity
    rw [mu, nn_nu, nu, norm_smul' hc.le, ← mul_assoc, ← Complex.ofReal_mul]
    have e : ‖z‖ / (‖z‖ / nn z * ‖z‖) * (‖z‖ / nn z) = 1 := by field_simp
    rw [e]
    simp

theorem nu_mu (w : ℂ) : nu (mu w) = w := by
  by_cases h : w = 0
  · subst h
    simp [nu_zero, mu]
  · have h1 := nn_pos h
    have h2 := norm_pos_iff.mpr h
    have hc : 0 < nn w / ‖w‖ := by positivity
    rw [nu, mu, norm_smul' hc.le, nn_smul hc.le, ← mul_assoc, ← Complex.ofReal_mul]
    have e : nn w / ‖w‖ * ‖w‖ / (nn w / ‖w‖ * nn w) * (nn w / ‖w‖) = 1 := by field_simp
    rw [e]
    simp

theorem norm_mu (w : ℂ) : ‖mu w‖ = nn w := by
  by_cases h : w = 0
  · subst h
    simp [mu, nn]
  · have h1 := nn_pos h
    have h2 := norm_pos_iff.mpr h
    rw [mu, norm_smul' (by positivity)]
    field_simp

theorem nu_injective : Injective nu := fun z z' he => by
  rw [← mu_nu z, he, mu_nu]

theorem continuous_nu : Continuous nu := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases h : z = 0
  · subst h
    have h1 : Filter.Tendsto nu (𝓝 0) (𝓝 0) := by
      have hnorm : Filter.Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) := by
        simpa only [norm_zero] using (continuous_norm (E := ℂ)).tendsto (0 : ℂ)
      refine squeeze_zero_norm (a := fun z : ℂ => ‖z‖) (fun z => ?_) hnorm
      by_cases hz : z = 0
      · subst hz
        simp [nu_zero]
      · have h2 := nn_pos hz
        have h3 := norm_pos_iff.mpr hz
        rw [nu, norm_smul' (by positivity), div_mul_eq_mul_div, div_le_iff₀ h2]
        exact mul_le_mul_of_nonneg_left (norm_le_nn z) h3.le
    unfold ContinuousAt
    rwa [nu_zero]
  · have h1 := (nn_pos h).ne'
    unfold nu
    have h2 : ContinuousAt (fun z : ℂ => ‖z‖ / nn z) z := continuous_norm.continuousAt.div
      continuous_nn.continuousAt h1
    exact (Complex.continuous_ofReal.continuousAt.comp h2).mul continuousAt_id

/-- The reflection that swaps two sides of the square. -/
def refl' (z : ℂ) : ℂ := ⟨-z.im, -z.re⟩

theorem nn_refl (z : ℂ) : nn (refl' z) = nn z := by
  simp only [nn, refl', abs_neg]
  ring

theorem norm_refl (z : ℂ) : ‖refl' z‖ = ‖z‖ := by
  rw [Complex.norm_def, Complex.norm_def, Complex.normSq_apply, Complex.normSq_apply]
  simp only [refl']
  congr 1
  ring

theorem nu_refl (z : ℂ) : nu (refl' z) = refl' (nu z) := by
  simp only [nu, norm_refl, nn_refl]
  apply Complex.ext <;> simp [refl']

/-- The cylinder coordinate along the axis. -/
noncomputable def cylR (z : ℂ) : ℝ := 3 / 2 + ((nu z).re - (nu z).im) / 2

/-- The cylinder coordinate around the axis. -/
noncomputable def cylS (z : ℂ) : ℝ := (nu z).re + (nu z).im

theorem abs_add_le_nn (w : ℂ) : |w.re + w.im| ≤ nn w := abs_add_le _ _

theorem abs_sub_le_nn (w : ℂ) : |w.re - w.im| ≤ nn w := abs_sub _ _

theorem cylR_mem {z : ℂ} (hz : ‖z‖ ≤ 1) : cylR z ∈ Icc (1 : ℝ) 2 := by
  have h1 := abs_sub_le_nn (nu z)
  rw [nn_nu] at h1
  have h2 := abs_le.mp (h1.trans hz)
  unfold cylR
  constructor <;> linarith [h2.1, h2.2]

theorem cylS_mem {z : ℂ} (hz : ‖z‖ ≤ 1) : cylS z ∈ Icc (-1 : ℝ) 1 := by
  have h1 := abs_add_le_nn (nu z)
  rw [nn_nu] at h1
  exact abs_le.mp (h1.trans hz)

/-- The map from the plane onto the cylinder. -/
noncomputable def cylG (z : ℂ) : ClosedCylinder :=
  ⟨(max 1 (min 2 (cylR z)), ee (cylS z / 2)), ⟨le_max_left _ _, max_le (by norm_num)
    (min_le_left _ _)⟩, mem_univ _⟩

theorem cylG_fst {z : ℂ} (hz : ‖z‖ ≤ 1) : (cylG z).1.1 = cylR z := by
  have := cylR_mem hz
  simp only [cylG]
  rw [min_eq_right this.2, max_eq_right this.1]

theorem cylG_snd (z : ℂ) : (cylG z).1.2 = ee (cylS z / 2) := rfl

theorem continuous_cylG : Continuous cylG := by
  have h1 : Continuous cylR := by
    unfold cylR
    have := continuous_nu
    fun_prop
  have h2 : Continuous cylS := by
    unfold cylS
    have := continuous_nu
    fun_prop
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.max (continuous_const.min h1)).prodMk (continuous_ee.comp
    (h2.div_const 2))

theorem cylG_surj (y : ClosedCylinder) : ∃ z : ℂ, ‖z‖ ≤ 1 ∧ cylG z = y := by
  obtain ⟨⟨r, θ⟩, hr, -⟩ := y
  obtain ⟨x, rfl⟩ := ee_surjective θ
  /- Choose `x` so that the coordinate `s = 2 * x` lies in `[-1, 1]`. -/
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x - k ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    refine ⟨⌊x + 1 / 2⌋, ?_, ?_⟩
    · linarith [Int.floor_le (x + 1 / 2)]
    · linarith [Int.lt_floor_add_one (x + 1 / 2)]
  set s := 2 * (x - k) with hs
  have hs1 : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  set d := 2 * r - 3 with hd
  have hd1 : d ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let w : ℂ := ⟨(s + d) / 2, (s - d) / 2⟩
  have hw : nn w ≤ 1 := by
    simp only [nn, w]
    rcases abs_cases ((s + d) / 2) with h1 | h1 <;> rcases abs_cases ((s - d) / 2) with h2 | h2 <;>
      linarith [hs1.1, hs1.2, hd1.1, hd1.2]
  refine ⟨mu w, by rw [norm_mu]; exact hw, ?_⟩
  have hz : ‖mu w‖ ≤ 1 := by rw [norm_mu]; exact hw
  apply Subtype.ext
  apply Prod.ext
  · rw [cylG_fst hz]
    simp only [cylR, nu_mu, w]
    linarith
  · rw [cylG_snd]
    simp only [cylS, nu_mu, w]
    rw [← ee_add_int x (-k), show (s + d) / 2 + (s - d) / 2 = s by ring]
    congr 1
    rw [hs]
    push_cast
    ring

theorem cylS_refl (z : ℂ) : cylS (refl' z) = - cylS z := by
  unfold cylS
  rw [nu_refl]
  simp only [refl']
  ring

theorem cylR_refl (z : ℂ) : cylR (refl' z) = cylR z := by
  unfold cylR
  rw [nu_refl]
  simp only [refl']
  ring

theorem refl_refl (z : ℂ) : refl' (refl' z) = z := by
  apply Complex.ext <;> simp [refl']

/-- The two sides of the square that are pasted. -/
theorem per_refl {t : ℝ} : per 4 (3 - t) = refl' (per 4 t) := by
  have e : (2 : ℝ) * Real.pi * (3 - t) / (4 : ℕ) = 3 * Real.pi / 2 - Real.pi * t / 2 := by
    push_cast
    ring
  have e' : (2 : ℝ) * Real.pi * t / (4 : ℕ) = Real.pi * t / 2 := by
    push_cast
    ring
  simp only [per, cis', refl', e, e']
  have hc : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi, Real.cos_pi_div_two]
    simp
  have hs : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi, Real.sin_pi_div_two]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_sub, hc, hs]
    ring
  · rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_sub, hc, hs]
    ring

theorem per_quad {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ (per 4 t).re ∧ 0 ≤ (per 4 t).im := by
  have e' : (2 : ℝ) * Real.pi * t / (4 : ℕ) = Real.pi * t / 2 := by
    push_cast
    ring
  have hpi := Real.pi_pos
  have h1 : 0 ≤ Real.pi * t / 2 := by
    have := ht.1
    positivity
  have h2 : Real.pi * t / 2 ≤ Real.pi / 2 := by nlinarith [ht.2]
  simp only [per, cis', e']
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h2,
    Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)⟩

theorem norm_per4 (t : ℝ) : ‖per 4 t‖ = 1 := by
  simp only [per, cis']
  exact Complex.norm_exp_ofReal_mul_I _

theorem cylS_quad {z : ℂ} (h1 : 0 ≤ z.re) (h2 : 0 ≤ z.im) : cylS z = ‖z‖ := by
  by_cases hz : z = 0
  · subst hz
    simp [cylS, nu_zero]
  have h3 := nn_pos hz
  simp only [cylS, nu, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.mul_im, add_zero]
  have h4 : nn z = z.re + z.im := by simp only [nn, abs_of_nonneg h1, abs_of_nonneg h2]
  rw [← mul_add, ← h4]
  field_simp

/-- A point of the disc that goes to the first side of the square is on the first arc. -/
theorem exists_side {z : ℂ} (hz : ‖z‖ ≤ 1) (hs : cylS z = 1) : ∃ t ∈ Icc (0 : ℝ) 1, z = per 4 t
  := by
  have h1 := nn_nu z
  have h2 : (nu z).re + (nu z).im = 1 := hs
  have h3 : |(nu z).re| + |(nu z).im| = ‖z‖ := h1
  have h4 := le_abs_self (nu z).re
  have h5 := le_abs_self (nu z).im
  have hn : ‖z‖ = 1 := le_antisymm hz (by linarith)
  have h6 : 0 ≤ (nu z).re := by
    rcases abs_cases (nu z).re with h7 | h7 <;> rcases abs_cases (nu z).im with h8 | h8 <;> linarith
  have h7 : 0 ≤ (nu z).im := by
    rcases abs_cases (nu z).re with h7 | h7 <;> rcases abs_cases (nu z).im with h8 | h8 <;> linarith
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hn
  have hc : 0 < ‖z‖ / nn z := div_pos (norm_pos_iff.mpr hz0) (nn_pos hz0)
  have h8 : 0 ≤ z.re := by
    have : (nu z).re = ‖z‖ / nn z * z.re := by simp [nu]
    rw [this] at h6
    exact nonneg_of_mul_nonneg_right h6 hc
  have h9 : 0 ≤ z.im := by
    have : (nu z).im = ‖z‖ / nn z * z.im := by simp [nu]
    rw [this] at h7
    exact nonneg_of_mul_nonneg_right h7 hc
  have hpi := Real.pi_pos
  have ha0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr h9
  have ha1 : Complex.arg z ≤ Real.pi / 2 := (abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr h8)).2
  refine ⟨2 * Complex.arg z / Real.pi, ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one hpi]
    linarith
  · have e : (2 : ℝ) * Real.pi * (2 * Complex.arg z / Real.pi) / (4 : ℕ) = Complex.arg z := by
      push_cast
      field_simp
      ring
    simp only [per, cis', e]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hn] at this
    simpa using this.symm

/-- The word of the cylinder. -/
def cylW : List Letter := [(0, true), (1, true), (0, false), (2, true)]

theorem sdPt_zero {t : ℝ} : sdPt 4 0 true t = per 4 t := by simp [sdPt]

theorem sdPt_two {t : ℝ} : sdPt 4 2 false t = per 4 (3 - t) := by
  simp only [sdPt]
  congr 1
  simp only [Bool.false_eq_true, ite_false]
  push_cast
  ring

theorem cylG_side {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : cylG (per 4 t) = cylG (per 4 (3 - t)) := by
  obtain ⟨h1, h2⟩ := per_quad ht
  have h3 := cylS_quad h1 h2
  rw [norm_per4] at h3
  apply Subtype.ext
  apply Prod.ext
  · rw [cylG_fst (norm_per4 t).le, cylG_fst (norm_per4 _).le, per_refl, cylR_refl]
  · rw [cylG_snd, cylG_snd, per_refl, cylS_refl, h3]
    exact ee_eq_iff.mpr ⟨1, by norm_num⟩

theorem cylG_fib {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1) (he : cylG z = cylG z') :
    z = z' ∨ ∃ t ∈ Icc (0 : ℝ) 1, (z = per 4 t ∧ z' = per 4 (3 - t)) ∨ (z' = per 4 t ∧ z = per 4
      (3 - t)) := by
  have h1 : cylR z = cylR z' := by
    rw [← cylG_fst hz, ← cylG_fst hz', he]
  have h2 : ee (cylS z / 2) = ee (cylS z' / 2) := by
    rw [← cylG_snd, ← cylG_snd, he]
  obtain ⟨m, hm⟩ := ee_eq_iff.mp h2
  have s1 := cylS_mem hz
  have s2 := cylS_mem hz'
  have r1 : (nu z).re - (nu z).im = (nu z').re - (nu z').im := by
    simp only [cylR] at h1
    linarith
  have m1 : (m : ℝ) < 2 := by linarith [s1.2, s2.1]
  have m2 : (-2 : ℝ) < m := by linarith [s1.1, s2.2]
  have m3 : m < 2 := by exact_mod_cast m1
  have m4 : -2 < m := by exact_mod_cast m2
  have key : ∀ {x y : ℂ}, ‖x‖ ≤ 1 → cylS x = 1 → cylS y = -1 → (nu x).re - (nu x).im = (nu y).re -
    (nu y).im →
      ∃ t ∈ Icc (0 : ℝ) 1, x = per 4 t ∧ y = per 4 (3 - t) := by
    intro x y hx hsx hsy hd
    obtain ⟨t, ht, rfl⟩ := exists_side hx hsx
    refine ⟨t, ht, rfl, ?_⟩
    rw [per_refl]
    apply nu_injective
    rw [nu_refl]
    have e1 : (nu (per 4 t)).re + (nu (per 4 t)).im = 1 := hsx
    have e2 : (nu y).re + (nu y).im = -1 := hsy
    apply Complex.ext
    · simp only [refl']
      linarith
    · simp only [refl']
      linarith
  have hm5 : m = 0 ∨ m = 1 ∨ m = -1 := by omega
  rcases hm5 with rfl | rfl | rfl
  · left
    apply nu_injective
    have e : cylS z = cylS z' := by
      push_cast at hm
      linarith
    have e' : (nu z).re + (nu z).im = (nu z').re + (nu z').im := e
    apply Complex.ext <;> linarith
  · right
    push_cast at hm
    have e1 : cylS z = 1 := by linarith [s1.2, s2.1]
    have e2 : cylS z' = -1 := by linarith [s1.2, s2.1]
    obtain ⟨t, ht, h3, h4⟩ := key hz e1 e2 r1
    exact ⟨t, ht, .inl ⟨h3, h4⟩⟩
  · right
    push_cast at hm
    have e1 : cylS z' = 1 := by linarith [s1.1, s2.2]
    have e2 : cylS z = -1 := by linarith [s1.1, s2.2]
    obtain ⟨t, ht, h3, h4⟩ := key hz' e1 e2 r1.symm
    exact ⟨t, ht, .inr ⟨h3, h4⟩⟩

theorem cylW_stp {a b : ℕ × ℂ} (h : Stp (sW cylW) a b) : cylG a.2 = cylG b.2 := by
  obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩ := h
  obtain ⟨rfl, h4⟩ := sW_get h1
  obtain ⟨rfl, h5⟩ := sW_get h2
  rw [sW_zero]
  have hlen : cylW.length = 4 := rfl
  simp only [hlen]
  have key : cylG (sdPt 4 0 true t) = cylG (sdPt 4 2 false t) := by
    rw [sdPt_zero, sdPt_two]
    exact cylG_side ht
  rcases p with _ | _ | _ | _ | p <;> rcases q with _ | _ | _ | _ | q <;>
    simp only [cylW, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, reduceCtorEq, Prod.mk.injEq, zero_add, Nat.reduceAdd] at h4 h5 h3
  all_goals obtain ⟨e1, e2⟩ := h4
  all_goals obtain ⟨e3, e4⟩ := h5
  all_goals subst e2 e4
  all_goals first
    | rfl
    | omega
    | exact key.symm

/-- The word `t r t⁻¹ r'` presents the cylinder. -/
theorem presents_cyl : Presents (sW cylW) fun a => cylG a.2 := by
  have hD : ∀ a, a ∈ Dsk (sW cylW) ↔ a.1 = 0 ∧ ‖a.2‖ ≤ 1 := fun a => by
    constructor
    · intro h
      have := mem_Dsk_sW h
      exact ⟨this.1, this.2.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h1, sW_zero]
      simp [cylW]
  refine ⟨(continuous_cylG.comp continuous_snd).continuousOn, ?_, ?_⟩
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨z, hz, rfl⟩ := cylG_surj y
    exact ⟨(0, z), (hD _).mpr ⟨rfl, hz⟩, rfl⟩
  · intro a ha b hb
    obtain ⟨h1, h2⟩ := (hD _).mp ha
    obtain ⟨h3, h4⟩ := (hD _).mp hb
    have ea : a = (0, a.2) := Prod.ext h1 rfl
    have eb : b = (0, b.2) := Prod.ext h3 rfl
    constructor
    · intro he
      rcases cylG_fib h2 h4 he with h5 | ⟨t, ht, ⟨h5, h6⟩ | ⟨h5, h6⟩⟩
      · rw [show a = b from Prod.ext (h1.trans h3.symm) h5]
        exact .refl _
      · rw [ea, eb, h5, h6]
        refine .rel _ _ ⟨0, 0, 0, 2, 0, true, false, t, rfl, rfl, by simp, ht, ?_, ?_⟩
        · simp [sW_zero, cylW, sdPt_zero]
        · simp [sW_zero, cylW, sdPt_two]
      · rw [ea, eb, h5, h6]
        refine .symm _ _ (.rel _ _ ⟨0, 0, 0, 2, 0, true, false, t, rfl, rfl, by simp, ht, ?_, ?_⟩)
        · simp [sW_zero, cylW, sdPt_zero]
        · simp [sW_zero, cylW, sdPt_two]
    · intro hp
      clear ha hb h1 h2 h3 h4 ea eb
      induction hp with
      | rel x y hs => exact cylW_stp hs
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ h1 h2 => exact h1.trans h2

/-- The model with two holes is the closed cylinder. -/
theorem nonempty_cyl_homeo : Nonempty (SurfaceModel 0 0 2 ≃ₜ ClosedCylinder) := by
  have hI : Inv cylW [] [] [] 0 0 0 := by
    refine ⟨.nil, .nil, .nil, by simp [DisjL], by simp [DisjL], by simp [DisjL], by simp [DisjL],
      by simp [DisjL], by simp [DisjL], ?_⟩
    intro k
    simp only [cylW, cnt_cons, cnt_nil]
    split_ifs <;> omega
  have s1 := step_hole.{0} (P := []) (x := (0, true)) (q := (1, true)) (Q := []) (V
    := [(2, true)]) hI rfl (by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [hl]
    simp [cylW, cnt_cons, cnt_nil])
  obtain ⟨u, s2, s3⟩ := step_last.{0} (R := [] ++ [(2, true)]) (q := (2, true)) (Q := []) s1.1 rfl
    (by
    intro l hl
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [hl]
    simp [cnt_cons, cnt_nil])
  have : Nonempty ClosedCylinder := ⟨⟨(1, 1), by simp [ClosedCylinder]⟩⟩
  obtain ⟨e⟩ := homeo_of_nf presents_cyl s2.isNF (s1.2.trans (by simpa using s3))
  exact ⟨e.symm⟩

end GraphMinor.Surface
