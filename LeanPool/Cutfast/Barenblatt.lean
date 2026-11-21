/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Moments

/-!
# The Barenblatt profile, the equilibrium and the solution

Normalization of the Barenblatt profile, identification of `v_∞` with the profiles of
Lemmas 3.1 and 4.1, and the description of `v(t,·)` as the image of `v_∞` under the
affine map `y ↦ a(t) y + e^{-t} x₀` with `a(t) = (1 - e^{-t/α})^α`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

/-- Admissible parameters: `d ≥ 1`, `m > 0`, `m ≠ 1`, `m > (d-2)/d`. -/
def Admissible (d : ℕ) (m : ℝ) : Prop := 1 ≤ d ∧ 0 < m ∧ m ≠ 1 ∧ ((d : ℝ) - 2) / d < m

/-- The scale factor `a(t) = (1 - e^{-t/α})^α`. -/
noncomputable def scaleFactor (d : ℕ) (m t : ℝ) : ℝ := (1 - exp (-t / alpha d m)) ^ alpha d m

/-- The constant `C = α^{2α-1} c` of `v_∞(x) = (C + (1-m)/(2m)|x|²)₊^{1/(m-1)}`. -/
noncomputable def equilibriumConst (d : ℕ) (m : ℝ) : ℝ :=
  alpha d m ^ (2 * alpha d m - 1) * barenblattConst d m

/-- The second moment `∫ |x|² v_∞(x) dx` of the equilibrium. -/
noncomputable def eqSecondMoment (d : ℕ) (m : ℝ) : ℝ := ∫ x, ‖x‖ ^ 2 * equilibrium d m x

variable {d : ℕ} {m : ℝ}


namespace Barenblatt

/-! ### Elementary facts on the exponents -/

theorem two_sub_pos (h : Admissible d m) : 0 < 2 - d * (1 - m) := by
  obtain ⟨hd, -, -, hmd⟩ := h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hd'] at hmd
  linarith

theorem alpha_mul (h : Admissible d m) : alpha d m * (2 - d * (1 - m)) = 1 := by
  unfold alpha
  have := two_sub_pos h
  field_simp

/-- `α d (m - 1) = 1 - 2α`. -/
theorem alpha_mul_d_mul (h : Admissible d m) : alpha d m * d * (m - 1) = 1 - 2 * alpha d m := by
  linear_combination alpha_mul h

/-- `(1 - 2α)/(m - 1) = α d`. -/
theorem exponent_eq (h : Admissible d m) : (1 - 2 * alpha d m) * (1 / (m - 1)) = alpha d m * d := by
  have hm : m - 1 ≠ 0 := sub_ne_zero.2 h.2.2.1
  rw [← alpha_mul_d_mul h]
  field_simp

/-! ### Change of variables `x = a • y + h` in `ℝᵈ` -/

theorem lintegral_comp_smul_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (G : V → ℝ≥0∞) {a : ℝ} (ha : 0 < a) (h : V) :
    ∫⁻ y, G (a • y + h) ∂μ = ENNReal.ofReal ((a ^ Module.finrank ℝ V)⁻¹) * ∫⁻ x, G x ∂μ := by
  let e : V ≃ᵐ V := (Homeomorph.smul (isUnit_iff_ne_zero.2 ha.ne').unit).toMeasurableEquiv
  have he : ∀ y, e y = a • y := fun y => rfl
  have hmap : Measure.map e μ = ENNReal.ofReal |(a ^ Module.finrank ℝ V)⁻¹| • μ :=
    Measure.map_addHaar_smul μ ha.ne'
  calc ∫⁻ y, G (a • y + h) ∂μ = ∫⁻ y, (fun z => G (z + h)) (e y) ∂μ := by simp only [he]
    _ = ∫⁻ z, G (z + h) ∂(Measure.map e μ) := by rw [lintegral_map_equiv]
    _ = _ := by
      rw [hmap, lintegral_smul_measure, lintegral_add_right_eq_self, abs_of_pos (by positivity),
        smul_eq_mul]

theorem lintegral_comp_affine (G : E d → ℝ≥0∞) {a : ℝ} (ha : 0 < a) (h : E d) :
    ∫⁻ y, G (a • y + h) = ENNReal.ofReal ((a ^ d)⁻¹) * ∫⁻ x, G x := by
  rw [lintegral_comp_smul_add volume G ha h, finrank_euclideanSpace_fin]

theorem integral_comp_affine (F : E d → ℝ) {a : ℝ} (ha : 0 < a) (h : E d) :
    ∫ y, F (a • y + h) = (a ^ d)⁻¹ * ∫ x, F x := by
  have := Measure.integral_comp_smul volume (fun z => F (z + h)) a
  rw [this, integral_add_right_eq_self, finrank_euclideanSpace_fin, abs_of_pos (by positivity),
    smul_eq_mul]

theorem integrable_comp_affine_iff (F : E d → ℝ) {a : ℝ} (ha : 0 < a) (h : E d) :
    Integrable (fun y => F (a • y + h)) ↔ Integrable F :=
  (integrable_comp_smul_iff volume (fun z => F (z + h)) ha.ne').trans
    ⟨fun H => by simpa using H.comp_add_right (-h), fun H => H.comp_add_right h⟩

theorem affine_inv (f : E d → ℝ) {a : ℝ} (ha : 0 < a) (h y : E d) :
    (a ^ d)⁻¹ * f (a⁻¹ • (a • y + h - h)) = (a ^ d)⁻¹ * f y := by
  rw [add_sub_cancel_right, inv_smul_smul₀ ha.ne']

theorem integral_scaled (f : E d → ℝ) {a : ℝ} (ha : 0 < a) (h : E d) :
    ∫ x, (a ^ d)⁻¹ * f (a⁻¹ • (x - h)) = ∫ x, f x := by
  have hA : a ^ d ≠ 0 := by positivity
  calc ∫ x, (a ^ d)⁻¹ * f (a⁻¹ • (x - h))
      = a ^ d * ∫ y, (a ^ d)⁻¹ * f (a⁻¹ • (a • y + h - h)) := by
        rw [integral_comp_affine (fun x => (a ^ d)⁻¹ * f (a⁻¹ • (x - h))) ha h, ← mul_assoc,
          mul_inv_cancel₀ hA, one_mul]
    _ = a ^ d * ∫ y, (a ^ d)⁻¹ * f y := by simp only [affine_inv f ha]
    _ = ∫ x, f x := by rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]

theorem integrable_scaled {f : E d → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) (h : E d) :
    Integrable (fun x => (a ^ d)⁻¹ * f (a⁻¹ • (x - h))) := by
  rw [← integrable_comp_affine_iff _ ha h]
  simp only [affine_inv f ha]
  exact hf.const_mul _

/-! ### The two families of profiles -/

theorem one_div_sub_one : 1 / (m - 1) = -(1 / (1 - m)) := by
  rw [← neg_sub, div_neg]

theorem max_rpow_eq_full {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b) (x : E d) :
    (max (C + b * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) = (C + b * ‖x‖ ^ 2) ^ (-(1 / (1 - m))) := by
  rw [max_eq_left (by positivity), one_div_sub_one]

theorem max_rpow_eq_compact {C b : ℝ} (x : E d) :
    (max (C + -b * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) = (max (C - b * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) := by
  ring_nf

theorem integral_full (hd : 1 ≤ d) {p b C : ℝ} (hp : (d : ℝ) / 2 < p) (hb : 0 < b) (hC : 0 < C) :
    ∫ x : E d, (C + b * ‖x‖ ^ 2) ^ (-p) =
      C ^ ((d : ℝ) / 2 - p) * (b ^ (-((d : ℝ) / 2)) *
        (π ^ ((d : ℝ) / 2) * Gamma (d / 2) * Gamma (p - d / 2) / (Gamma (d / 2) * Gamma p))) := by
  have := integral_rpow_norm_mul_add_sq_rpow_neg (d := d) hd (a := 0) (p := p)
    (by have : (0 : ℝ) < d := by exact_mod_cast hd
        linarith) (by linarith) hC hb
  simp only [Real.rpow_zero, one_mul, add_zero] at this
  rw [this, mul_assoc]

theorem integral_compact (hd : 1 ≤ d) {p b C : ℝ} (hp : 0 < p) (hb : 0 < b) (hC : 0 < C) :
    ∫ x : E d, (max (C - b * ‖x‖ ^ 2) 0) ^ p =
      C ^ ((d : ℝ) / 2 + p) * (b ^ (-((d : ℝ) / 2)) *
        (π ^ ((d : ℝ) / 2) * Gamma (d / 2) * Gamma (p + 1) /
          (Gamma (d / 2) * Gamma (p + 1 + d / 2)))) := by
  have := integral_rpow_norm_mul_sub_sq_rpow (d := d) hd (a := 0) (hp := hp)
    (ha := by have : (0 : ℝ) < d := by exact_mod_cast hd
              linarith) (hC := hC) (hβ := hb)
  simp only [Real.rpow_zero, one_mul, add_zero] at this
  rw [this, mul_assoc]

theorem rpow_inj {C C' e : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (he : e ≠ 0) (h : C ^ e = C' ^ e) :
    C = C' :=
  Real.rpow_left_injOn he hC hC' h

/-- Uniqueness of the constant of a full-space profile with a given mass. -/
theorem full_unique (hd : 1 ≤ d) {p b C C' : ℝ} (hp : (d : ℝ) / 2 < p) (hb : 0 < b) (hC : 0 < C)
    (hC' : 0 < C')
    (h : ∫ x : E d, (C + b * ‖x‖ ^ 2) ^ (-p) = ∫ x : E d, (C' + b * ‖x‖ ^ 2) ^ (-p)) :
    C = C' := by
  rw [integral_full hd hp hb hC, integral_full hd hp hb hC'] at h
  have hd2 : (0 : ℝ) < d / 2 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                   positivity
  have hK : b ^ (-((d : ℝ) / 2)) * (π ^ ((d : ℝ) / 2) * Gamma (d / 2) * Gamma (p - d / 2) /
      (Gamma (d / 2) * Gamma p)) ≠ 0 := by
    have := Real.Gamma_pos_of_pos hd2
    have := Real.Gamma_pos_of_pos (show 0 < p - d / 2 by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < p by linarith)
    positivity
  exact rpow_inj hC.le hC'.le (by linarith) (mul_right_cancel₀ hK h)

/-- Uniqueness of the constant of a compactly supported profile with a given mass. -/
theorem compact_unique (hd : 1 ≤ d) {p b C C' : ℝ} (hp : 0 < p) (hb : 0 < b) (hC : 0 < C)
    (hC' : 0 < C')
    (h : ∫ x : E d, (max (C - b * ‖x‖ ^ 2) 0) ^ p = ∫ x : E d, (max (C' - b * ‖x‖ ^ 2) 0) ^ p) :
    C = C' := by
  rw [integral_compact hd hp hb hC, integral_compact hd hp hb hC'] at h
  have hd2 : (0 : ℝ) < d / 2 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                   positivity
  have hK : b ^ (-((d : ℝ) / 2)) * (π ^ ((d : ℝ) / 2) * Gamma (d / 2) * Gamma (p + 1) /
      (Gamma (d / 2) * Gamma (p + 1 + d / 2))) ≠ 0 := by
    have := Real.Gamma_pos_of_pos hd2
    have := Real.Gamma_pos_of_pos (show 0 < p + 1 by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < p + 1 + d / 2 by linarith)
    positivity
  exact rpow_inj hC.le hC'.le (by linarith) (mul_right_cancel₀ hK h)

theorem integrable_fullBarenblatt (hd : 1 ≤ d) {p b : ℝ} (hp : (d : ℝ) / 2 < p) (hb : 0 < b) :
    Integrable (fullBarenblatt d p b) := by
  have := integrable_fullBarenblatt_moment hd hp hb (a := 0)
    (by have : (0 : ℝ) < d := by exact_mod_cast hd
        linarith) (by linarith)
  simpa only [Real.rpow_zero, one_mul] using this

theorem integral_fullBarenblatt (hd : 1 ≤ d) {p b : ℝ} (hp : (d : ℝ) / 2 < p) (hb : 0 < b) :
    ∫ x, fullBarenblatt d p b x = 1 := by
  have := fullBarenblatt_moment' hd hp hb (a := 0)
    (by have : (0 : ℝ) < d := by exact_mod_cast hd
        linarith) (by linarith)
  have hd2 : (0 : ℝ) < d / 2 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                   positivity
  have h1 := Real.Gamma_pos_of_pos hd2
  have h2 := Real.Gamma_pos_of_pos (show 0 < p - d / 2 by linarith)
  simp only [Real.rpow_zero, one_mul, zero_div, add_zero] at this
  rw [this, div_self (by positivity)]

theorem integrable_compactBarenblatt (hd : 1 ≤ d) {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    Integrable (compactBarenblatt d p b) := by
  have := integrable_compactBarenblatt_moment hd hp hb (a := 0)
    (by have : (0 : ℝ) < d := by exact_mod_cast hd
        linarith)
  simpa only [Real.rpow_zero, one_mul] using this

theorem integral_compactBarenblatt (hd : 1 ≤ d) {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    ∫ x, compactBarenblatt d p b x = 1 := by
  have := compactBarenblatt_moment' hd hp hb (a := 0)
    (by have : (0 : ℝ) < d := by exact_mod_cast hd
        linarith)
  have hd2 : (0 : ℝ) < d / 2 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                   positivity
  have h1 := Real.Gamma_pos_of_pos hd2
  have h2 := Real.Gamma_pos_of_pos (show 0 < p + 1 + d / 2 by linarith)
  simp only [Real.rpow_zero, one_mul, zero_div, add_zero] at this
  rw [this, mul_comm (Gamma _), div_self (by positivity)]

end Barenblatt

open Barenblatt

theorem alpha_pos (h : Admissible d m) : 0 < alpha d m := by
  unfold alpha
  have := two_sub_pos h
  positivity

namespace Barenblatt

theorem half_lt_p_full (h : Admissible d m) (hm : m < 1) : (d : ℝ) / 2 < 1 / (1 - m) := by
  have := two_sub_pos h
  rw [div_lt_div_iff₀ two_pos (by linarith)]
  linarith

theorem p_compact_pos (hm : 1 < m) : 0 < 1 / (m - 1) := by
  have : 0 < m - 1 := by linarith
  positivity

theorem max_mul_rpow {K Y q : ℝ} (hK : 0 < K) : (max (K * Y) 0) ^ q = K ^ q * (max Y 0) ^ q := by
  rw [show max (K * Y) 0 = K * max Y 0 by rw [mul_max_of_nonneg _ _ hK.le, mul_zero],
    Real.mul_rpow hK.le (le_max_right _ _)]

/-- Existence and uniqueness of a normalizing constant. -/
theorem exists_unique_const (h : Admissible d m) :
    (∃ c : ℝ, 0 < c ∧ Integrable (barenblattWith d m c) ∧ ∫ x, barenblattWith d m c x = 1) ∧
      ∀ c c', 0 < c → 0 < c' → ∫ x, barenblattWith d m c x = 1 →
        ∫ x, barenblattWith d m c' x = 1 → c = c' := by
  have hd := h.1
  have hα := alpha_pos h
  have hm0 := h.2.1
  rcases lt_or_gt_of_ne h.2.2.1 with hm | hm
  · set κ := alpha d m * (1 - m) / (2 * m) with hκ
    have hκpos : 0 < κ := by
      have : 0 < 1 - m := by linarith
      positivity
    have hp := half_lt_p_full h hm
    have hbw : ∀ c, 0 ≤ c → barenblattWith d m c = fun x => (c + κ * ‖x‖ ^ 2) ^ (-(1 / (1 - m))) :=
      fun c hc => funext fun x => max_rpow_eq_full hc hκpos.le x
    have hc0 := fullBarenblattConst_pos hp hκpos
    refine ⟨⟨fullBarenblattConst d (1 / (1 - m)) κ, hc0, ?_, ?_⟩, ?_⟩
    · rw [hbw _ hc0.le]
      exact integrable_fullBarenblatt hd hp hκpos
    · rw [hbw _ hc0.le]
      exact integral_fullBarenblatt hd hp hκpos
    · intro c c' hc hc' h1 h1'
      rw [hbw c hc.le] at h1
      rw [hbw c' hc'.le] at h1'
      exact full_unique hd hp hκpos hc hc' (h1.trans h1'.symm)
  · set κ := alpha d m * (m - 1) / (2 * m) with hκ
    have hκpos : 0 < κ := by
      have : 0 < m - 1 := by linarith
      positivity
    have hp := p_compact_pos hm
    have hbw : ∀ c, barenblattWith d m c = fun x => (max (c - κ * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) := by
      intro c
      funext x
      unfold barenblattWith
      rw [show c + alpha d m * (1 - m) / (2 * m) * ‖x‖ ^ 2 = c - κ * ‖x‖ ^ 2 by rw [hκ]; ring]
    have hc0 := compactBarenblattConst_pos (d := d) hp hκpos
    refine ⟨⟨compactBarenblattConst d (1 / (m - 1)) κ, hc0, ?_, ?_⟩, ?_⟩
    · rw [hbw]
      exact integrable_compactBarenblatt hd hp hκpos
    · rw [hbw]
      exact integral_compactBarenblatt hd hp hκpos
    · intro c c' hc hc' h1 h1'
      rw [hbw c] at h1
      rw [hbw c'] at h1'
      exact compact_unique hd hp hκpos hc hc' (h1.trans h1'.symm)

end Barenblatt

/-- The normalizing constant exists, is positive and is the unique one. -/
theorem barenblattConst_spec' (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) :
    0 < barenblattConst d m ∧ Integrable (barenblattWith d m (barenblattConst d m)) ∧
      ∫ x, barenblattWith d m (barenblattConst d m) x = 1 ∧
      ∀ c : ℝ, 0 < c → Integrable (barenblattWith d m c) →
        ∫ x, barenblattWith d m c x = 1 → c = barenblattConst d m := by
  obtain ⟨hex, huniq⟩ := exists_unique_const (d := d) (m := m) ⟨hd, hm0, hm1, hmd⟩
  have hc : barenblattConst d m = hex.choose := by
    unfold barenblattConst
    simp only [hex, ↓reduceDIte]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  rw [hc]
  exact ⟨h1, h2, h3, fun c hc' _ hci => huniq c _ hc' h1 hci h3⟩

theorem Barenblatt.barenblattConst_pos (h : Admissible d m) : 0 < barenblattConst d m :=
  (barenblattConst_spec' h.1 h.2.1 h.2.2.1 h.2.2.2).1

theorem equilibriumConst_pos (h : Admissible d m) : 0 < equilibriumConst d m := by
  unfold equilibriumConst
  have := alpha_pos h
  have := barenblattConst_pos h
  positivity

theorem equilibrium_eq (h : Admissible d m) (x : E d) :
    equilibrium d m x =
      (max (equilibriumConst d m + (1 - m) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) := by
  have hα := alpha_pos h
  have hex := exponent_eq h
  unfold equilibrium barenblatt barenblattWith equilibriumConst
  set α := alpha d m
  set c := barenblattConst d m
  have hA : 0 < α ^ α := Real.rpow_pos_of_pos hα _
  have hnorm : ‖(α ^ α)⁻¹ • x‖ ^ 2 = α ^ (-2 * α) * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hA), mul_pow, ← Real.rpow_neg hα.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hα.le]
    ring_nf
  have hK : α ^ (1 - 2 * α) * α ^ (2 * α - 1) = 1 := by
    rw [← Real.rpow_add hα]
    simp
  have hK2 : α * α ^ (-2 * α) = α ^ (1 - 2 * α) := by
    rw [sub_eq_add_neg, Real.rpow_add hα, Real.rpow_one]
    ring_nf
  have hin : c + α * (1 - m) / (2 * m) * ‖(α ^ α)⁻¹ • x‖ ^ 2 =
      α ^ (1 - 2 * α) * (α ^ (2 * α - 1) * c + (1 - m) / (2 * m) * ‖x‖ ^ 2) := by
    have hK' : α * α ^ (-2 * α) * α ^ (2 * α - 1) = 1 := by rw [hK2, hK]
    rw [hnorm, ← hK2]
    linear_combination (-c) * hK'
  rw [hin, max_mul_rpow (Real.rpow_pos_of_pos hα _), ← Real.rpow_mul hα.le, hex, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hα _).ne', one_mul]

theorem equilibrium_nonneg (h : Admissible d m) (x : E d) : 0 ≤ equilibrium d m x := by
  rw [equilibrium_eq h]
  exact Real.rpow_nonneg (le_max_right _ _) _

theorem equilibrium_pos (h : Admissible d m) (hm : m < 1) (x : E d) :
    0 < equilibrium d m x := by
  rw [equilibrium_eq h]
  apply Real.rpow_pos_of_pos
  apply lt_max_of_lt_left
  have := equilibriumConst_pos h
  have h1 : 0 < 1 - m := by linarith
  have := h.2.1
  have : 0 ≤ (1 - m) / (2 * m) * ‖x‖ ^ 2 := by positivity
  linarith

namespace Barenblatt

theorem equilibrium_scaled (h : Admissible d m) (x : E d) :
    equilibrium d m x =
      ((alpha d m ^ alpha d m) ^ d)⁻¹ * barenblatt d m ((alpha d m ^ alpha d m)⁻¹ • (x - 0)) := by
  unfold equilibrium
  rw [sub_zero, ← Real.rpow_natCast, ← Real.rpow_mul (alpha_pos h).le]

end Barenblatt

theorem integrable_equilibrium (h : Admissible d m) : Integrable (equilibrium d m) := by
  have hB : Integrable (barenblatt d m) := (barenblattConst_spec' h.1 h.2.1 h.2.2.1 h.2.2.2).2.1
  rw [show equilibrium d m = _ from funext (equilibrium_scaled h)]
  exact integrable_scaled hB (Real.rpow_pos_of_pos (alpha_pos h) _) 0

theorem integral_equilibrium (h : Admissible d m) : ∫ x, equilibrium d m x = 1 := by
  have hB : ∫ x, barenblatt d m x = 1 := (barenblattConst_spec' h.1 h.2.1 h.2.2.1 h.2.2.2).2.2.1
  simp only [equilibrium_scaled h]
  rw [integral_scaled _ (Real.rpow_pos_of_pos (alpha_pos h) _) 0, hB]

theorem equilibrium_eq_fullBarenblatt (h : Admissible d m) (hm : m < 1) :
    equilibrium d m = fullBarenblatt d (1 / (1 - m)) ((1 - m) / (2 * m)) := by
  have hC := equilibriumConst_pos h
  have hb : 0 < (1 - m) / (2 * m) := by
    have : 0 < 1 - m := by linarith
    have := h.2.1
    positivity
  have hp := half_lt_p_full h hm
  have hfun : equilibrium d m =
      fun x => (equilibriumConst d m + (1 - m) / (2 * m) * ‖x‖ ^ 2) ^ (-(1 / (1 - m))) :=
    funext fun x => by rw [equilibrium_eq h, max_rpow_eq_full hC.le hb.le]
  have hCeq : equilibriumConst d m = fullBarenblattConst d (1 / (1 - m)) ((1 - m) / (2 * m)) :=
    full_unique h.1 hp hb hC (fullBarenblattConst_pos hp hb) (by
      rw [← hfun, integral_equilibrium h]
      exact (integral_fullBarenblatt h.1 hp hb).symm)
  rw [hfun, hCeq]
  rfl

theorem equilibrium_eq_compactBarenblatt (h : Admissible d m) (hm : 1 < m) :
    equilibrium d m = compactBarenblatt d (1 / (m - 1)) ((m - 1) / (2 * m)) := by
  have hC := equilibriumConst_pos h
  have hb : 0 < (m - 1) / (2 * m) := by
    have : 0 < m - 1 := by linarith
    have := h.2.1
    positivity
  have hp := p_compact_pos hm
  have hfun : equilibrium d m =
      fun x => (max (equilibriumConst d m - (m - 1) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) :=
    funext fun x => by
      rw [equilibrium_eq h, show equilibriumConst d m + (1 - m) / (2 * m) * ‖x‖ ^ 2 =
        equilibriumConst d m - (m - 1) / (2 * m) * ‖x‖ ^ 2 by ring]
  have hCeq : equilibriumConst d m = compactBarenblattConst d (1 / (m - 1)) ((m - 1) / (2 * m)) :=
    compact_unique h.1 hp hb hC (compactBarenblattConst_pos hp hb) (by
      rw [← hfun, integral_equilibrium h]
      exact (integral_compactBarenblatt h.1 hp hb).symm)
  rw [hfun, hCeq]
  rfl

namespace Barenblatt

theorem isProbabilityMeasure_densityMeasure {f : E d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) (h1 : ∫ x, f x = 1) : IsProbabilityMeasure (densityMeasure f) := by
  constructor
  unfold densityMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0), h1, ENNReal.ofReal_one]

end Barenblatt

theorem equilibrium_isProbabilityDensity' (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) :
    (∀ x, 0 ≤ equilibrium d m x) ∧ IsProbabilityMeasure (densityMeasure (equilibrium d m)) := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  exact ⟨equilibrium_nonneg h, isProbabilityMeasure_densityMeasure (equilibrium_nonneg h)
    (integrable_equilibrium h) (integral_equilibrium h)⟩

namespace Barenblatt

theorem one_sub_exp_pos (h : Admissible d m) {t : ℝ} (ht : 0 < t) :
    0 < 1 - exp (-t / alpha d m) := by
  have : -t / alpha d m < 0 := div_neg_of_neg_of_pos (by linarith) (alpha_pos h)
  have := Real.exp_lt_one_iff.2 this
  linarith

end Barenblatt

theorem scaleFactor_pos (h : Admissible d m) {t : ℝ} (ht : 0 < t) : 0 < scaleFactor d m t :=
  Real.rpow_pos_of_pos (one_sub_exp_pos h ht) _

theorem scaleFactor_lt_one (h : Admissible d m) {t : ℝ} (ht : 0 < t) :
    scaleFactor d m t < 1 :=
  Real.rpow_lt_one (one_sub_exp_pos h ht).le (by have := exp_pos (-t / alpha d m); linarith)
    (alpha_pos h)

/-- `v(t,x) = a(t)^{-d} v_∞((x - e^{-t}x₀)/a(t))`. -/
theorem solution_eq (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t) (x : E d) :
    solution d m x₀ t x =
      (scaleFactor d m t ^ d)⁻¹ * equilibrium d m ((scaleFactor d m t)⁻¹ • (x - exp (-t) • x₀))
        := by
  have hα := alpha_pos h
  have hu := one_sub_exp_pos h ht
  simp only [solution, equilibrium, scaleFactor]
  rw [Real.mul_rpow hα.le hu.le, Real.mul_rpow hα.le hu.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hu.le, smul_smul, mul_inv, mul_inv, mul_assoc]
  exact mul_left_comm _ _ _

namespace Barenblatt

theorem solution_affine' (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t) (y : E d) :
    solution d m x₀ t (scaleFactor d m t • y + exp (-t) • x₀) =
      (scaleFactor d m t ^ d)⁻¹ * equilibrium d m y := by
  rw [solution_eq h x₀ ht, add_sub_cancel_right, inv_smul_smul₀ (scaleFactor_pos h ht).ne']

end Barenblatt

/-- Change of variables `x = a(t) y + e^{-t} x₀`. -/
theorem integral_mul_solution (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t)
    (g : E d → ℝ) :
    ∫ x, g x * solution d m x₀ t x =
      ∫ y, g (scaleFactor d m t • y + exp (-t) • x₀) * equilibrium d m y := by
  have ha := scaleFactor_pos h ht
  have e : ∀ y, g (scaleFactor d m t • y + exp (-t) • x₀) *
      solution d m x₀ t (scaleFactor d m t • y + exp (-t) • x₀) =
      (scaleFactor d m t ^ d)⁻¹ *
        (g (scaleFactor d m t • y + exp (-t) • x₀) * equilibrium d m y) := by
    intro y
    rw [solution_affine' h x₀ ht]
    ring
  have := integral_comp_affine (fun x => g x * solution d m x₀ t x) ha (exp (-t) • x₀)
  simp only [e, integral_const_mul] at this
  exact (mul_left_cancel₀ (by positivity) this).symm

theorem integrable_mul_solution_iff (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t)
    (g : E d → ℝ) :
    Integrable (fun x => g x * solution d m x₀ t x) ↔
      Integrable (fun y => g (scaleFactor d m t • y + exp (-t) • x₀) * equilibrium d m y) := by
  have ha := scaleFactor_pos h ht
  rw [← integrable_comp_affine_iff _ ha (exp (-t) • x₀)]
  simp only [solution_affine' h x₀ ht, mul_left_comm (g _)]
  exact integrable_const_mul_iff (IsUnit.mk0 _ (by positivity)) _

theorem solution_isProbabilityDensity' (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    (∀ x, 0 ≤ solution d m x₀ t x) ∧ IsProbabilityMeasure (densityMeasure (solution d m x₀ t)) := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  have ha := scaleFactor_pos h ht
  have h0 : ∀ x, 0 ≤ solution d m x₀ t x := fun x => by
    rw [solution_eq h x₀ ht]
    exact mul_nonneg (by positivity) (equilibrium_nonneg h _)
  refine ⟨h0, isProbabilityMeasure_densityMeasure h0 ?_ ?_⟩
  · have := (integrable_mul_solution_iff h x₀ ht (fun _ => 1)).2
      (by simpa using integrable_equilibrium h)
    simpa using this
  · have := integral_mul_solution h x₀ ht (fun _ => 1)
    simpa [integral_equilibrium h] using this

/-- The law `v(t,·)` is the image of `v_∞` under `y ↦ a(t) y + e^{-t} x₀`. -/
theorem densityMeasure_solution (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    densityMeasure (solution d m x₀ t) =
      (densityMeasure (equilibrium d m)).map (fun y => scaleFactor d m t • y + exp (-t) • x₀) := by
  have ha := scaleFactor_pos h ht
  set a := scaleFactor d m t
  set h0 := exp (-t) • x₀
  have hT : Measurable (fun y : E d => a • y + h0) := by fun_prop
  ext s hs
  rw [Measure.map_apply hT hs]
  unfold densityMeasure
  rw [withDensity_apply _ hs, withDensity_apply _ (hT hs), ← lintegral_indicator hs,
    ← lintegral_indicator (hT hs)]
  set F := fun x => ENNReal.ofReal (solution d m x₀ t x)
  have had : (0 : ℝ) < a ^ d := by positivity
  calc ∫⁻ x, s.indicator F x
      = ENNReal.ofReal (a ^ d) * ∫⁻ y, s.indicator F (a • y + h0) := by
        rw [lintegral_comp_affine _ ha, ← mul_assoc, ← ENNReal.ofReal_mul had.le,
          mul_inv_cancel₀ had.ne', ENNReal.ofReal_one, one_mul]
    _ = ∫⁻ y, ENNReal.ofReal (a ^ d) * s.indicator F (a • y + h0) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = _ := by
        congr 1
        funext y
        by_cases hy : a • y + h0 ∈ s
        · rw [Set.indicator_of_mem hy,
            Set.indicator_of_mem (show y ∈ (fun y => a • y + h0) ⁻¹' s from hy)]
          simp only [F]
          rw [solution_affine' h x₀ ht, ← ENNReal.ofReal_mul had.le, ← mul_assoc,
            mul_inv_cancel₀ had.ne', one_mul]
        · rw [Set.indicator_of_notMem hy,
            Set.indicator_of_notMem (show y ∉ (fun y => a • y + h0) ⁻¹' s from hy), mul_zero]

/-! ### Moments of the equilibrium (finite second moment: `m > d/(d+2)`) -/

namespace Barenblatt

theorem two_lt_full (hm : m < 1) (h2 : (d : ℝ) / (d + 2) < m) :
    2 < 2 * (1 / (1 - m)) - d := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_lt_iff₀ (by linarith)] at h2
  have h1 : 0 < 1 - m := by linarith
  have : (2 + d) * (1 - m) < 2 := by nlinarith
  have := (lt_div_iff₀ h1).2 this
  have e : 2 * (1 / (1 - m)) = 2 / (1 - m) := by ring
  linarith

theorem pm_full (hm : m < 1) (hm0 : 0 < m) (h2 : (d : ℝ) / (d + 2) < m) :
    (d : ℝ) / (2 * m) < 1 / (1 - m) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_lt_iff₀ (by linarith)] at h2
  rw [div_lt_div_iff₀ (by positivity) (by linarith)]
  nlinarith

theorem b_full_pos (hm : m < 1) (hm0 : 0 < m) : 0 < (1 - m) / (2 * m) := by
  have : 0 < 1 - m := by linarith
  positivity

theorem b_compact_pos (hm : 1 < m) : 0 < (m - 1) / (2 * m) := by
  have : 0 < m - 1 := by linarith
  have : 0 < m := by linarith
  positivity

end Barenblatt

theorem integrable_sq_mul_equilibrium (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) :
    Integrable (fun x => ‖x‖ ^ 2 * equilibrium d m x) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h.1
  rcases lt_or_gt_of_ne h.2.2.1 with hm | hm
  · rw [equilibrium_eq_fullBarenblatt h hm]
    simpa only [Real.rpow_two] using integrable_fullBarenblatt_moment h.1
      (half_lt_p_full h hm) (b_full_pos hm h.2.1) (a := 2) (by linarith) (two_lt_full hm h2)
  · rw [equilibrium_eq_compactBarenblatt h hm]
    simpa only [Real.rpow_two] using integrable_compactBarenblatt_moment h.1
      (p_compact_pos hm) (b_compact_pos hm) (a := 2) (by linarith)

theorem integrable_norm_mul_equilibrium (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) :
    Integrable (fun x => ‖x‖ * equilibrium d m x) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h.1
  rcases lt_or_gt_of_ne h.2.2.1 with hm | hm
  · rw [equilibrium_eq_fullBarenblatt h hm]
    have := two_lt_full hm h2
    simpa only [Real.rpow_one] using integrable_fullBarenblatt_moment h.1
      (half_lt_p_full h hm) (b_full_pos hm h.2.1) (a := 1) (by linarith) (by linarith)
  · rw [equilibrium_eq_compactBarenblatt h hm]
    simpa only [Real.rpow_one] using integrable_compactBarenblatt_moment h.1
      (p_compact_pos hm) (b_compact_pos hm) (a := 1) (by linarith)

/-- The equilibrium has zero barycenter by symmetry. -/
theorem integral_smul_equilibrium (h : Admissible d m) :
    ∫ x, equilibrium d m x • x = 0 := by
  have hsym : ∀ x, equilibrium d m (-x) = equilibrium d m x := by
    intro x
    rw [equilibrium_eq h, equilibrium_eq h, norm_neg]
  have := integral_neg_eq_self (fun x => equilibrium d m x • x) volume
  simp only [hsym, smul_neg, integral_neg] at this
  have h2 : (2 : ℝ) • ∫ x, equilibrium d m x • x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← this]
    exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem integrable_equilibrium_rpow (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) :
    Integrable (fun x => equilibrium d m x ^ m) := by
  rcases lt_or_gt_of_ne h.2.2.1 with hm | hm
  · rw [equilibrium_eq_fullBarenblatt h hm]
    exact integrable_fullBarenblatt_rpow h.1 h.2.1 (half_lt_p_full h hm) (pm_full hm h.2.1 h2)
      (b_full_pos hm h.2.1)
  · rw [equilibrium_eq_compactBarenblatt h hm]
    exact integrable_compactBarenblatt_rpow h.1 (p_compact_pos hm) (b_compact_pos hm) h.2.1

/-- The exact identity `∫ v_∞ᵐ = (1/d) ∫ |x|² v_∞` (`= O(1)` difference in the paper). -/
theorem integral_equilibrium_rpow (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) :
    ∫ x, equilibrium d m x ^ m = eqSecondMoment d m / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h.1
  unfold eqSecondMoment
  rcases lt_or_gt_of_ne h.2.2.1 with hm | hm
  · rw [equilibrium_eq_fullBarenblatt h hm, fullBarenblatt_secondMoment_eq h.1 hm h2,
      mul_div_cancel_left₀ _ hd0.ne']
  · rw [equilibrium_eq_compactBarenblatt h hm, compactBarenblatt_secondMoment_eq h.1 hm,
      mul_div_cancel_left₀ _ hd0.ne']

theorem eqSecondMoment_pos (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) :
    0 < eqSecondMoment d m := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast h.1
  have hd2 : (0 : ℝ) < d / 2 := by positivity
  unfold eqSecondMoment
  rcases lt_or_gt_of_ne h.2.2.1 with hm | hm
  · rw [equilibrium_eq_fullBarenblatt h hm]
    have hp := half_lt_p_full h hm
    have hb := b_full_pos hm h.2.1
    have hp2 := two_lt_full hm h2
    simp_rw [← Real.rpow_two]
    rw [fullBarenblatt_moment' h.1 hp hb (by linarith) hp2]
    set p := 1 / (1 - m)
    set b := (1 - m) / (2 * m)
    have := Real.Gamma_pos_of_pos (show 0 < p - d / 2 by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < p by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < p - (d + 2) / 2 by linarith)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (d + 2) / 2 by positivity)
    have := Real.Gamma_pos_of_pos hd2
    positivity
  · rw [equilibrium_eq_compactBarenblatt h hm]
    have hp := p_compact_pos hm
    have hb := b_compact_pos hm
    simp_rw [← Real.rpow_two]
    rw [compactBarenblatt_moment' h.1 hp hb (by linarith)]
    set p := 1 / (m - 1)
    set b := (m - 1) / (2 * m)
    have := Real.Gamma_pos_of_pos (show 0 < p + 1 + d / 2 by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < p + 1 by linarith)
    have := Real.Gamma_pos_of_pos (show 0 < p + 1 + (d + 2) / 2 by linarith)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (d + 2) / 2 by positivity)
    have := Real.Gamma_pos_of_pos hd2
    positivity

/-- The normalizing constant of the Barenblatt profile exists and is unique: for `d ≥ 1`,
`m > 0`, `m ≠ 1` and `m > (d-2)/d`, `c_{d,m}` is the unique `c > 0` making `B_c` a
probability density function. -/
alias barenblattConst_spec := barenblattConst_spec'

/-- For every time `t > 0`, `v(t,·)` is a probability density function. -/
alias solution_isProbabilityDensity := solution_isProbabilityDensity'

/-- `v_∞` is a probability density function. -/
alias equilibrium_isProbabilityDensity := equilibrium_isProbabilityDensity'

end Cutfast
