/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
public import LeanPool.GraphMinor.Surface.PasteDisc
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Collars of cuffs and moving a cuff

`exists_collar`: every cuff of a surface has a collar inside any neighbourhood of it. We paste a
closed
disc onto the cuff (`paste_disc`), find a larger disc around this disc (`exists_disc_around`) and
use
the annulus between them (`exists_disc_collar`).

`move_cuff : MoveCuffStatement`: a homeomorphism `h` of the circle that preserves the orientation is
joined to the identity by the straight homotopy of its lift to the line. We run this homotopy across
the
collar, so the result is `h` on the cuff and the identity on the far end of the collar.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

local notation "𝕀" => unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- **Collars of cuffs.** -/
theorem exists_collar (hS : IsSurface S) {C U : Set S} (hC : IsCuff C) (φ : Circle ≃ₜ C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ b : Circle × 𝕀 → S, Continuous b ∧ Function.Injective b ∧ range b ⊆ U ∧
      (∀ w, b (w, 0) = (φ w).1) ∧ IsOpen (range b \ b '' {x | x.2 = 1}) := by
  classical
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  obtain ⟨S', _, ι, Δ, hS', hι, hΔ, hcov, hmeet, hbd, hbdS⟩ := paste_disc.{u} S C hS hC
  obtain ⟨hcpt', ht2', hman'⟩ := hS'
  have hιi : Function.Injective ι := hι.injective
  let W : Set S' := (ι '' Uᶜ)ᶜ
  have hW : IsOpen W := (hι.isClosedMap _ hU.isClosed_compl).isOpen_compl
  have hWi : ∀ x, ι x ∈ W → x ∈ U := fun x hx => by
    by_contra hcon
    exact hx ⟨x, hcon, rfl⟩
  have hsubW : discBd Δ ⊆ W := by
    rw [hbd]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact hy (hCU (hιi he ▸ hx))
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := by
    rw [hbd]
    rintro _ ⟨x, hx, rfl⟩
    by_contra hcon
    have h1 : ι x ∈ bd S' := hcon
    rw [hbdS] at h1
    obtain ⟨y, hy, he⟩ := h1
    exact hy.2 (hιi he ▸ hx)
  obtain ⟨Δ', hΔ', h2, h3⟩ := exists_disc_around hman' hΔ hint hW hsubW
  have hemb := hι.isEmbedding
  let p : Circle ≃ₜ discBd Δ := (φ.trans (hemb.homeomorphImage C)).trans
    (Homeomorph.setCongr hbd.symm)
  have hp : ∀ w, (p w).1 = ι (φ w).1 := fun _ => rfl
  obtain ⟨c, c', hcc, hcc', hcm, hcm', hl, hr, hc1, hc2, hcw⟩ := exists_disc_collar hΔ hΔ' h2 p
  have : Nonempty S := ⟨(φ 1).1⟩
  obtain ⟨j, hjc, hjl⟩ := exists_inv_of_compactOn isCompact_univ hι.continuous.continuousOn
    hιi.injOn
  rw [image_univ] at hjc
  let Λ : Set ℂ := closedBall 0 2 \ ball 0 1
  have hΛ2 : Λ ⊆ closedBall 0 2 := sdiff_subset
  have hcw' : ∀ w : Circle, c w = ι (φ w).1 := fun w => (hcw w).trans (hp w)
  have hsph : ∀ w : Circle, (w : ℂ) ∈ closedBall (0 : ℂ) 2 := fun w => by
    rw [mem_closedBall_zero_iff, Circle.norm_coe]
    norm_num
  -- a point of `Δ` that is not in the small disc's inside
  have hrange : ∀ z ∈ Λ, c z ∈ range ι := by
    intro z hz
    by_contra hcon
    have h4 : c z ∈ Δ := by
      have h5 : c z ∈ range ι ∪ Δ := hcov ▸ mem_univ _
      exact h5.resolve_left hcon
    obtain ⟨z₁, hz₁, he⟩ : c z ∈ c '' closedBall 0 1 := hc1 ▸ h4
    have h6 : z₁ = z := hl.injOn (closedBall_subset_closedBall (by norm_num) hz₁) (hΛ2 hz) he
    subst h6
    have h7 : ‖z₁‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hz₁) (by
      have := hz.2
      rwa [mem_ball_zero_iff, not_lt] at this)
    exact hcon ⟨(φ ⟨z₁, by simpa [Submonoid.unitSphere] using h7⟩).1,
      (hcw' ⟨z₁, by simpa [Submonoid.unitSphere] using h7⟩).symm⟩
  have hιj : ∀ x ∈ range ι, ι (j x) = x := by
    rintro _ ⟨x, rfl⟩
    rw [hjl (mem_univ x)]
  let P : Circle × 𝕀 → ℂ := fun x => ((1 + x.2.1 : ℝ) : ℂ) * x.1
  have hPc : Continuous P := by fun_prop
  have hPn : ∀ x, ‖P x‖ = 1 + x.2.1 := fun x => by
    simp only [P, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by linarith [x.2.2.1])
  have hPΛ : ∀ x, P x ∈ Λ := fun x => by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, hPn]
      linarith [x.2.2.2]
    · rw [mem_ball_zero_iff, hPn]
      linarith [x.2.2.1]
  have hPi : Function.Injective P := by
    rintro x y he
    have h4 := congrArg norm he
    rw [hPn, hPn] at h4
    have h5 : x.2 = y.2 := Subtype.ext (by linarith)
    have h6 : ((1 + x.2.1 : ℝ) : ℂ) ≠ 0 := by
      have : (1 + x.2.1 : ℝ) ≠ 0 := by linarith [x.2.2.1]
      exact_mod_cast this
    have h7 : ((1 + x.2.1 : ℝ) : ℂ) * x.1 = ((1 + x.2.1 : ℝ) : ℂ) * y.1 := by
      have : P x = P y := he
      simp only [P] at this
      rwa [← h5] at this
    exact Prod.ext (Circle.ext (mul_left_cancel₀ h6 h7)) h5
  have hPs : ∀ z ∈ Λ, ∃ x, P x = z := fun z hz => by
    have h4 : 1 ≤ ‖z‖ := by
      have := hz.2
      rwa [mem_ball_zero_iff, not_lt] at this
    have h5 : ‖z‖ ≤ 2 := mem_closedBall_zero_iff.mp hz.1
    have h6 : ‖z‖ ≠ 0 := by linarith
    refine ⟨(⟨z / ‖z‖, ?_⟩, ⟨‖z‖ - 1, by linarith, by linarith⟩), ?_⟩
    · simp [Submonoid.unitSphere, h6]
    · change (((1 + (‖z‖ - 1) : ℝ)) : ℂ) * (z / ‖z‖) = z
      have h7 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast h6
      rw [add_sub_cancel]
      field_simp
  let b : Circle × 𝕀 → S := fun x => j (c (P x))
  have hιb : ∀ x, ι (b x) = c (P x) := fun x => hιj _ (hrange _ (hPΛ x))
  have hbc : Continuous b :=
    hjc.comp_continuous (hcc.comp_continuous hPc fun x => hΛ2 (hPΛ x)) fun x => hrange _ (hPΛ x)
  have hbi : Function.Injective b := fun x y he => by
    have h4 : c (P x) = c (P y) := by rw [← hιb, ← hιb, he]
    exact hPi (hl.injOn (hΛ2 (hPΛ x)) (hΛ2 (hPΛ y)) h4)
  have hbU : range b ⊆ U := by
    rintro _ ⟨x, rfl⟩
    have h4 : ι (b x) ∈ Δ ∪ W := h3 (by rw [hιb]; exact hcm (hΛ2 (hPΛ x)))
    rcases h4 with h4 | h4
    · have h5 : ι (b x) ∈ ι '' C := hmeet ▸ ⟨⟨_, rfl⟩, h4⟩
      obtain ⟨y, hy, he⟩ := h5
      exact hCU (hιi he ▸ hy)
    · exact hWi _ h4
  have hb0 : ∀ w, b (w, 0) = (φ w).1 := fun w => by
    apply hιi
    rw [hιb, ← hcw' w]
    congr 1
    simp [P]
  have hopen : range b \ b '' {x | x.2 = 1} = ι ⁻¹' (Δ' \ discBd Δ') := by
    ext x
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      refine ⟨by rw [hιb]; exact hcm (hΛ2 (hPΛ y)), ?_⟩
      show ι (b y) ∉ _
      rw [hιb, ← hc2]
      rintro ⟨z, hz, he⟩
      have h4 : z = P y := hl.injOn (sphere_subset_closedBall hz) (hΛ2 (hPΛ y)) he
      have h5 := mem_sphere_zero_iff_norm.mp hz
      rw [h4, hPn] at h5
      exact hy ⟨y, Subtype.ext (by simp only [Set.Icc.coe_one]; linarith), rfl⟩
    · rintro ⟨h4, h5⟩
      set z := c' (ι x) with hz
      have hcz : c z = ι x := hr h4
      have hz2 : z ∈ closedBall (0 : ℂ) 2 := hcm' h4
      have hzΛ : z ∈ Λ := by
        refine ⟨hz2, fun hzb => ?_⟩
        have h6 : c z ∈ Δ := hc1 ▸ mem_image_of_mem c (ball_subset_closedBall hzb)
        have h7 : c z ∈ ι '' C := hmeet ▸ ⟨hcz ▸ mem_range_self x, h6⟩
        obtain ⟨y, hy, he⟩ := h7
        have h8 : c ((φ.symm ⟨y, hy⟩ : Circle) : ℂ) = c z := by
          rw [hcw', ← he]
          simp
        have h9 := hl.injOn (hsph _) hz2 h8
        have h10 := mem_ball_zero_iff.mp hzb
        rw [← h9, Circle.norm_coe] at h10
        exact lt_irrefl _ h10
      obtain ⟨y, hy⟩ := hPs z hzΛ
      have hxb : b y = x := hιi (by rw [hιb, hy, hcz])
      refine ⟨⟨y, hxb⟩, ?_⟩
      rintro ⟨y', hy', he⟩
      apply h5
      rw [← hc2, ← he, hιb]
      refine ⟨P y', ?_, rfl⟩
      rw [mem_sphere_zero_iff_norm, hPn, show y'.2 = 1 from hy']
      norm_num
  refine ⟨b, hbc, hbi, hbU, hb0, ?_⟩
  rw [hopen]
  exact (hΔ'.isOpen_discInt hman').preimage hι.continuous

/-- The lift of an orientation preserving homeomorphism of the circle moves `t + 2π` to `l t + 2π`.
-/
theorem lift_period {h : Circle ≃ₜ Circle} {l : ℝ → ℝ} (hl : Continuous l) (hm : StrictMono l)
    (he : ∀ t : ℝ, h (Circle.exp t) = Circle.exp (l t)) (t : ℝ) :
    l (t + 2 * Real.pi) = l t + 2 * Real.pi := by
  have hpi := Real.pi_pos
  let k : ℝ → ℝ := fun t => (l (t + 2 * Real.pi) - l t) / (2 * Real.pi)
  have hkc : Continuous k := by fun_prop
  have hexp : ∀ t, Circle.exp (t + 2 * Real.pi) = Circle.exp t := fun t => by
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
  have hint : ∀ t, k t ∈ range ((↑) : ℤ → ℝ) := fun t => by
    have h1 : Circle.exp (l (t + 2 * Real.pi)) = Circle.exp (l t) := by
      rw [← he, ← he, hexp]
    obtain ⟨m, hm'⟩ := Circle.exp_eq_exp.mp h1
    refine ⟨m, ?_⟩
    change (m : ℝ) = (l (t + 2 * Real.pi) - l t) / (2 * Real.pi)
    rw [hm']
    field_simp
    ring
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isEmbedding.isDiscrete_range
  obtain ⟨y, hy, hconst⟩ := isPreconnected_univ.eqOn_const_of_mapsTo hdisc hkc.continuousOn
    (fun t _ => hint t) ⟨0, 0, by simp⟩
  obtain ⟨d, rfl⟩ := hy
  have hk : ∀ t, l (t + 2 * Real.pi) = l t + (d : ℝ) * (2 * Real.pi) := fun t => by
    have h1 : k t = d := hconst (mem_univ t)
    have h2 : (l (t + 2 * Real.pi) - l t) / (2 * Real.pi) = d := h1
    rw [div_eq_iff (by positivity)] at h2
    linarith
  have hd1 : 1 ≤ d := by
    have h1 := hm (show (0 : ℝ) < 0 + 2 * Real.pi by linarith)
    rw [hk] at h1
    have h2 : (0 : ℝ) < (d : ℝ) := by
      by_contra hcon
      have : (d : ℝ) * (2 * Real.pi) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) (by positivity)
      linarith
    exact_mod_cast h2
  have hd2 : d = 1 := by
    by_contra hne
    have hd : (2 : ℝ) ≤ d := by
      have : 2 ≤ d := by omega
      exact_mod_cast this
    have h0 := hk 0
    rw [zero_add] at h0
    obtain ⟨u, hu, hul⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
      hl.continuousOn (show l 0 + 2 * Real.pi ∈ Icc (l 0) (l (2 * Real.pi)) from
        ⟨by linarith, by rw [h0]; nlinarith⟩)
    have h1 : Circle.exp (l u) = Circle.exp (l 0) := by
      rw [hul, Circle.exp_add, Circle.exp_two_pi, mul_one]
    rw [← he, ← he] at h1
    have h2 := h.injective h1
    obtain ⟨m, hm'⟩ := Circle.exp_eq_exp.mp h2
    have h3 : u ≠ 0 := fun h4 => by
      rw [h4] at hul
      linarith
    have h4 : u ≠ 2 * Real.pi := fun h5 => by
      rw [h5, h0] at hul
      nlinarith
    have h5 : 0 < u := lt_of_le_of_ne hu.1 h3.symm
    have h6 : u < 2 * Real.pi := lt_of_le_of_ne hu.2 h4
    rw [zero_add] at hm'
    have h7 : (0 : ℝ) < m := by
      by_contra hcon
      have : (m : ℝ) * (2 * Real.pi) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) (by positivity)
      linarith
    have h8 : (m : ℝ) < 1 := by
      by_contra hcon
      have : (1 : ℝ) * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right (not_lt.mp hcon) (by positivity)
      linarith
    have h9 : 0 < m := by exact_mod_cast h7
    have h10 : m < 1 := by exact_mod_cast h8
    omega
  rw [hk, hd2]
  simp

/-- The straight homotopy from `h` to the identity. -/
theorem exists_circle_homotopy {h : Circle ≃ₜ Circle} (hh : PreservesCircleOrientation h) :
    ∃ μ : 𝕀 × Circle → Circle, Continuous μ ∧ (∀ w, μ (0, w) = h w) ∧ (∀ w, μ (1, w) = w) ∧
      ∀ s, Function.Bijective fun w => μ (s, w) := by
  obtain ⟨l, hlc, hlm, hle⟩ := hh
  have hpi := Real.pi_pos
  have hper := lift_period hlc hlm hle
  have hsurj : Function.Surjective Circle.exp := fun w => by
    obtain ⟨θ, -, hθ⟩ := exists_circle_angle 1 w
    exact ⟨θ, by rw [hθ, one_mul]⟩
  have hq : IsQuotientMap Circle.exp :=
    isLocalHomeomorph_circleExp.isOpenMap.isQuotientMap Circle.exp.continuous hsurj
  let D : ℝ → ℝ := fun t => t - l t
  have hDp : Function.Periodic D (2 * Real.pi) := fun t => by
    change t + 2 * Real.pi - l (t + 2 * Real.pi) = t - l t
    rw [hper]
    ring
  let δ : Circle → ℝ := fun w => D (Function.surjInv hsurj w)
  have hδ : ∀ t, δ (Circle.exp t) = D t := fun t => by
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Function.surjInv_eq hsurj (Circle.exp t))
    change D (Function.surjInv hsurj (Circle.exp t)) = D t
    rw [hm]
    exact (hDp.int_mul m) t
  have hδc : Continuous δ := by
    rw [hq.continuous_iff]
    have : δ ∘ Circle.exp = D := funext hδ
    rw [this]
    exact continuous_id.sub hlc
  let μ : 𝕀 × Circle → Circle := fun x => h x.2 * Circle.exp (x.1.1 * δ x.2)
  let L : 𝕀 → ℝ → ℝ := fun s t => l t + s.1 * (t - l t)
  have hμ : ∀ s t, μ (s, Circle.exp t) = Circle.exp (L s t) := fun s t => by
    change h (Circle.exp t) * Circle.exp (s.1 * δ (Circle.exp t)) = _
    rw [hle, hδ, ← Circle.exp_add]
  have hLm : ∀ s, StrictMono (L s) := fun s a b hab => by
    have h1 := hlm hab
    have h2 := s.2.1
    have h3 := s.2.2
    change l a + s.1 * (a - l a) < l b + s.1 * (b - l b)
    nlinarith [mul_nonneg h2 (sub_nonneg.mpr hab.le), mul_nonneg (sub_nonneg.mpr h3)
      (sub_pos.mpr h1).le]
  have hLp : ∀ s t, L s (t + 2 * Real.pi) = L s t + 2 * Real.pi := fun s t => by
    change l (t + 2 * Real.pi) + s.1 * (t + 2 * Real.pi - l (t + 2 * Real.pi)) = _
    rw [hper]
    change _ = l t + s.1 * (t - l t) + 2 * Real.pi
    ring
  have hLc : ∀ s, Continuous (L s) := fun s => by
    change Continuous fun t => l t + s.1 * (t - l t)
    fun_prop
  refine ⟨μ, by fun_prop, fun w => ?_, fun w => ?_, fun s => ⟨?_, ?_⟩⟩
  · simp [μ]
  · obtain ⟨t, rfl⟩ := hsurj w
    rw [hμ]
    congr 1
    change l t + (1 : ℝ) * (t - l t) = t
    ring
  · intro w w' he
    obtain ⟨t, rfl⟩ := hsurj w
    obtain ⟨θ, hθ, hw'⟩ := exists_circle_angle (Circle.exp t) w'
    subst hw'
    rw [← Circle.exp_add] at he ⊢
    have he' : Circle.exp (L s t) = Circle.exp (L s (t + θ)) := by
      rw [← hμ, ← hμ]
      exact he
    by_cases h0 : θ = 0
    · rw [h0, add_zero]
    · exfalso
      have hθ0 : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h0)
      have h1 := hLm s (show t < t + θ by linarith)
      have h2 := hLm s (show t + θ < t + 2 * Real.pi by linarith [hθ.2])
      rw [hLp] at h2
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he'
      have h3 : (0 : ℝ) < -(m : ℝ) * (2 * Real.pi) := by linarith
      have h4 : -(m : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by linarith
      have h5 : 0 < -(m : ℝ) := (pos_iff_pos_of_mul_pos h3).mpr (by positivity)
      have h6 : -(m : ℝ) < 1 := lt_of_mul_lt_mul_right h4 (by positivity)
      have h7 : 0 < -m := by exact_mod_cast h5
      have h8 : -m < 1 := by exact_mod_cast h6
      omega
  · intro v
    obtain ⟨θ, hθ, hv⟩ := exists_circle_angle (Circle.exp (L s 0)) v
    obtain ⟨u, -, hu⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
      (hLc s).continuousOn (show L s 0 + θ ∈ Icc (L s 0) (L s (2 * Real.pi)) by
        have := hLp s 0
        rw [zero_add] at this
        rw [this]
        exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    refine ⟨Circle.exp u, ?_⟩
    change μ (s, Circle.exp u) = v
    rw [hμ, hu, hv, Circle.exp_add]

/-- **Moving a cuff.** See the module docstring. -/
theorem move_cuff : MoveCuffStatement.{u} := by
  classical
  intro S _ C U φ h hS hC hU hCU hh
  obtain ⟨hcpt, ht2, hman⟩ := id hS
  obtain ⟨μ, hμc, hμ0, hμ1, hμb⟩ := exists_circle_homotopy hh
  obtain ⟨b, hbc, hbi, hbU, hb0, hopen⟩ := exists_collar hS hC φ hU hCU
  let K := Circle × 𝕀
  let M : K → K := fun x => (μ (x.2, x.1), x.2)
  have hMc : Continuous M := by fun_prop
  have hMi : Function.Injective M := fun x y (he : M x = M y) => by
    have h1 : x.2 = y.2 := (Prod.ext_iff.mp he).2
    have h2 : μ (x.2, x.1) = μ (y.2, y.1) := (Prod.ext_iff.mp he).1
    rw [← h1] at h2
    exact Prod.ext ((hμb x.2).1 h2) h1
  have hMs : Function.Surjective M := fun y => by
    obtain ⟨w, hw⟩ := (hμb y.2).2 y.1
    exact ⟨(w, y.2), Prod.ext hw rfl⟩
  have hemb := hbc.isClosedEmbedding hbi
  let e : K ≃ₜ range b := hemb.isEmbedding.toHomeomorph
  have hee : ∀ k, (e k).1 = b k := fun _ => rfl
  let A := range b
  let α : S → S := fun x => if hx : x ∈ A then b (M (e.symm ⟨x, hx⟩)) else x
  have hαb : ∀ k, α (b k) = b (M k) := fun k => by
    have hx : b k ∈ A := ⟨k, rfl⟩
    change (if hx : b k ∈ A then b (M (e.symm ⟨b k, hx⟩)) else b k) = _
    rw [dite_eq_left hx]
    congr 2
    exact e.symm_apply_apply k
  have hαn : ∀ x, x ∉ A → α x = x := fun x hx => dite_eq_right hx
  let V : Set S := A \ b '' {x | x.2 = 1}
  have hAc : IsClosed A := hemb.isClosed_range
  have hVo : IsOpen V := hopen
  have hcA : ContinuousOn α A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : A.domRestrict α = fun x : A => b (M (e.symm x)) := by
      ext x
      change (if hx : x.1 ∈ A then b (M (e.symm ⟨x.1, hx⟩)) else x.1) = _
      rw [dite_eq_left x.2]
    rw [this]
    exact hbc.comp (hMc.comp e.symm.continuous)
  have hcV : ContinuousOn α Vᶜ := by
    refine continuousOn_id.congr fun x hx => ?_
    by_cases hxA : x ∈ A
    · have hxT : x ∈ b '' {x | x.2 = 1} := by
        by_contra hcon
        exact hx ⟨hxA, hcon⟩
      obtain ⟨k, hk, rfl⟩ := hxT
      rw [hαb]
      have h1 : M k = k := by
        apply Prod.ext
        · change μ (k.2, k.1) = k.1
          rw [show k.2 = 1 from hk]
          exact hμ1 _
        · rfl
      rw [h1]
      rfl
    · exact hαn x hxA
  have hc : Continuous α := by
    rw [← continuousOn_univ]
    have huniv : A ∪ Vᶜ = univ := by
      rw [eq_univ_iff_forall]
      intro x
      by_cases hx : x ∈ V
      · exact .inl hx.1
      · exact .inr hx
    rw [← huniv]
    exact hcA.union_of_isClosed hcV hAc hVo.isClosed_compl
  have hαi : Function.Injective α := by
    intro x y he
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · obtain ⟨k, rfl⟩ := hx
      obtain ⟨k', rfl⟩ := hy
      rw [hαb, hαb] at he
      rw [hMi (hbi he)]
    · obtain ⟨k, rfl⟩ := hx
      rw [hαb, hαn y hy] at he
      exact absurd ⟨_, he⟩ hy
    · obtain ⟨k, rfl⟩ := hy
      rw [hαb, hαn x hx] at he
      exact absurd ⟨_, he.symm⟩ hx
    · rwa [hαn x hx, hαn y hy] at he
  have hαs : Function.Surjective α := by
    intro y
    by_cases hy : y ∈ A
    · obtain ⟨k, rfl⟩ := hy
      obtain ⟨k₀, rfl⟩ := hMs k
      exact ⟨b k₀, hαb k₀⟩
    · exact ⟨y, hαn y hy⟩
  let E : S ≃ S := Equiv.ofBijective α ⟨hαi, hαs⟩
  have hEc : Continuous E := hc
  refine ⟨hEc.homeoOfEquivCompactToT2, fun x => ?_, fun x hx => ?_⟩
  · change α (φ x).1 = _
    rw [← hb0 x, hαb, ← hb0]
    change b (μ (0, x), 0) = _
    rw [hμ0]
  · exact hαn x fun hxA => hx (hbU hxA)

end GraphMinor.Surface
