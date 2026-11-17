/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Siegel.Goldfeld2
public import LeanPool.Siegel.Euler
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Siegel's theorem

`∀ ε > 0, ∃ c > 0`, `‖L(1, χ)‖ ≥ c N^{-ε}` for every real non-principal character `χ` mod `N`.
Goldfeld's dichotomy on the existence of a real zero in `[1 - ε/16, 1)`.
-/

@[expose] public section

open Complex DirichletCharacter Set

open scoped ComplexOrder LSeries.notation

namespace SiegelThmLib

/-! ### From a witness `(χ₁, β)` to the bound -/

lemma natCast_one_le (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

lemma siegel_of_witness {ε : ℝ} (hε1 : ε ≤ 1) {N₁ : ℕ} [NeZero N₁]
    {χ₁ : DirichletCharacter ℂ N₁} (hχ₁ : χ₁ ≠ 1) (h₁ : χ₁ ^ 2 = 1) {β : ℝ}
    (hβ1 : 1 - ε / 16 ≤ β) (hβ2 : β < 1)
    (hF : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      prodChar χ₁ χ ≠ 1 → (F χ₁ χ β).re ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖LFunction χ 1‖ := by
  have hu0 : 0 < 1 - β := sub_pos.mpr hβ2
  have hu1 : 8 * (1 - β) ≤ ε / 2 := by linarith only [hβ1]
  have hβ78 : 7 / 8 ≤ β := by linarith only [hβ1, hε1]
  have hεhalf : 0 < ε / 2 := by linarith only [hβ1, hβ2]
  have hL1 : 0 < ‖LFunction χ₁ 1‖ := norm_pos_iff.mpr (LFunction_apply_one_ne_zero hχ₁)
  have hn1 : (1 : ℝ) ≤ N₁ := natCast_one_le N₁
  have hn0 : (0 : ℝ) < N₁ := zero_lt_one.trans_le hn1
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℝ,
      a0 = (1 - β) / 2 * (50000 * (N₁ : ℝ) ^ 2) ^ (-(4 * (1 - β))) := ⟨_, rfl⟩
  have ha0' : 0 < a0 := by
    rw [ha0]
    exact mul_pos (div_pos hu0 (by norm_num)) (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℝ, b0 = (N₁ : ℝ) ^ (ε / 2) / (ε / 2) := ⟨_, rfl⟩
  have hb0' : 0 < b0 := by
    rw [hb0]
    exact div_pos (Real.rpow_pos_of_pos hn0 _) hεhalf
  obtain ⟨cE, hcE, hE⟩ := prod_one_sub_inv_ge hεhalf
  obtain ⟨cA, hcA⟩ : ∃ c : ℝ, c = a0 / (‖LFunction χ₁ 1‖ * b0) := ⟨_, rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ c : ℝ,
      c = ‖LFunction χ₁ 1‖ * (cE * (N₁ : ℝ) ^ (-(ε / 2))) ^ 2 := ⟨_, rfl⟩
  have hcA' : 0 < cA := by rw [hcA]; exact div_pos ha0' (mul_pos hL1 hb0')
  have hcB' : 0 < cB := by
    rw [hcB]; exact mul_pos hL1 (pow_pos (mul_pos hcE (Real.rpow_pos_of_pos hn0 _)) 2)
  refine ⟨min cA cB, lt_min hcA' hcB', fun N _ χ hχ hsq => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := natCast_one_le N
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hNε : 0 ≤ (N : ℝ) ^ (-ε) := Real.rpow_nonneg hN0.le _
  -- `N^{-ε/2}` squared
  have hsq2 : ((N : ℝ) ^ (-(ε / 2))) ^ 2 = (N : ℝ) ^ (-ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  by_cases hψ : prodChar χ₁ χ = 1
  · -- equivalent characters
    have h1 := equiv_case hχ₁ hχ hsq hψ
    have h2 := hE (N₁ * N) (Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne N))
    have h3 : ((N₁ * N : ℕ) : ℝ) ^ (-(ε / 2)) =
        (N₁ : ℝ) ^ (-(ε / 2)) * (N : ℝ) ^ (-(ε / 2)) := by
      push_cast; exact Real.mul_rpow hn0.le hN0.le
    rw [h3] at h2
    have h4 : 0 ≤ cE * ((N₁ : ℝ) ^ (-(ε / 2)) * (N : ℝ) ^ (-(ε / 2))) :=
      mul_nonneg hcE.le (mul_nonneg (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hN0.le _))
    have h5 := pow_le_pow_left₀ h4 h2 2
    calc min cA cB * (N : ℝ) ^ (-ε) ≤ cB * (N : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hNε
      _ = ‖LFunction χ₁ 1‖ * (cE * ((N₁ : ℝ) ^ (-(ε / 2)) * (N : ℝ) ^ (-(ε / 2)))) ^ 2 := by
          rw [hcB, ← hsq2]; ring
      _ ≤ ‖LFunction χ₁ 1‖ * (∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹)) ^ 2 :=
          mul_le_mul_of_nonneg_left h5 hL1.le
      _ ≤ ‖LFunction χ 1‖ := h1
  · -- Goldfeld's lemma
    have hG := goldfeld hχ₁ hχ hψ h₁ hsq hβ78 hβ2 (hF N χ hχ hsq hψ)
    have hP : ‖P χ₁ χ 1‖ =
        ‖LFunction χ₁ 1‖ * ‖LFunction χ 1‖ * ‖LFunction (prodChar χ₁ χ) 1‖ := by
      unfold P; rw [norm_mul, norm_mul]
    rw [hP] at hG
    have hY := norm_LFunction_one_le hψ hεhalf (by linarith only [hε1])
    have hY' : ‖LFunction (prodChar χ₁ χ) 1‖ ≤ b0 * (N : ℝ) ^ (ε / 2) := by
      refine hY.trans (le_of_eq ?_)
      rw [hb0]; push_cast
      rw [Real.mul_rpow hn0.le hN0.le]; ring
    -- lower bound for the Goldfeld constant
    have hlow : a0 * (N : ℝ) ^ (-(ε / 2)) ≤
        (1 - β) / 2 * (50000 * ((N₁ : ℝ) * (N : ℝ)) ^ 2) ^ (-(4 * (1 - β))) := by
      have e1 : (50000 * ((N₁ : ℝ) * (N : ℝ)) ^ 2) = (50000 * (N₁ : ℝ) ^ 2) * ((N : ℝ) ^ 2) := by
        ring
      rw [e1, Real.mul_rpow (by positivity) (by positivity), ha0]
      have e2 : ((N : ℝ) ^ 2) ^ (-(4 * (1 - β))) = (N : ℝ) ^ (-(8 * (1 - β))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      rw [e2]
      have e3 : (N : ℝ) ^ (-(ε / 2)) ≤ (N : ℝ) ^ (-(8 * (1 - β))) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hu1])
      have : 0 ≤ (1 - β) / 2 * (50000 * (N₁ : ℝ) ^ 2) ^ (-(4 * (1 - β))) :=
        mul_nonneg (div_nonneg hu0.le (by norm_num)) (Real.rpow_nonneg (by positivity) _)
      calc (1 - β) / 2 * (50000 * (N₁ : ℝ) ^ 2) ^ (-(4 * (1 - β))) * (N : ℝ) ^ (-(ε / 2))
          ≤ (1 - β) / 2 * (50000 * (N₁ : ℝ) ^ 2) ^ (-(4 * (1 - β))) *
              (N : ℝ) ^ (-(8 * (1 - β))) :=
            mul_le_mul_of_nonneg_left e3 this
        _ = _ := by ring
    have hX : 0 ≤ ‖LFunction χ 1‖ := norm_nonneg _
    have hchain : a0 * (N : ℝ) ^ (-(ε / 2)) ≤
        ‖LFunction χ₁ 1‖ * ‖LFunction χ 1‖ * (b0 * (N : ℝ) ^ (ε / 2)) := by
      have : ‖LFunction χ₁ 1‖ * ‖LFunction χ 1‖ * ‖LFunction (prodChar χ₁ χ) 1‖ ≤
          ‖LFunction χ₁ 1‖ * ‖LFunction χ 1‖ * (b0 * (N : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left hY' (mul_nonneg hL1.le hX)
      exact hlow.trans (hG.trans this)
    have hNh : 0 < (N : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hN0 _
    have hexp : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-ε) = (N : ℝ) ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hpos : 0 < ‖LFunction χ₁ 1‖ * b0 * (N : ℝ) ^ (ε / 2) :=
      mul_pos (mul_pos hL1 hb0') hNh
    have hL1ne := hL1.ne'
    have hb0ne := hb0'.ne'
    have hgoal : cA * (N : ℝ) ^ (-ε) ≤ ‖LFunction χ 1‖ := by
      refine le_of_mul_le_mul_left ?_ hpos
      calc ‖LFunction χ₁ 1‖ * b0 * (N : ℝ) ^ (ε / 2) * (cA * (N : ℝ) ^ (-ε))
          = a0 * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-ε)) := by
            rw [hcA]; field_simp
        _ = a0 * (N : ℝ) ^ (-(ε / 2)) := by rw [hexp]
        _ ≤ ‖LFunction χ₁ 1‖ * ‖LFunction χ 1‖ * (b0 * (N : ℝ) ^ (ε / 2)) := hchain
        _ = ‖LFunction χ₁ 1‖ * b0 * (N : ℝ) ^ (ε / 2) * ‖LFunction χ 1‖ := by ring
    calc min cA cB * (N : ℝ) ^ (-ε) ≤ cA * (N : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hNε
      _ ≤ _ := hgoal

/-! ### The case without exceptional zeros -/

/-- The non-principal character modulo `4`. -/
noncomputable def chi4 : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma chi4_sq : chi4 ^ 2 = 1 := (ZMod.isQuadratic_χ₄.comp _).sq_eq_one

lemma chi4_ne : chi4 ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := by
    have := (ZMod.isUnit_iff_coprime 3 4).mpr (by decide)
    simpa using this
  have h1 : chi4 (3 : ZMod 4) = 1 := by rw [h]; exact MulChar.one_apply hu
  have h2 : chi4 (3 : ZMod 4) = -1 := by
    simp only [chi4, MulChar.ringHomComp_apply]
    have : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
    rw [this]; simp
  rw [h1] at h2
  norm_num at h2

variable {N₁ N : ℕ} [NeZero N₁] [NeZero N]

lemma P_real {χ₁ : DirichletCharacter ℂ N₁} {χ : DirichletCharacter ℂ N} (hχ₁ : χ₁ ≠ 1)
    (hχ : χ ≠ 1) (hψ : prodChar χ₁ χ ≠ 1) (h₁ : χ₁ ^ 2 = 1) (h : χ ^ 2 = 1) {t : ℝ}
    (ht : 0 < t) : ∃ x : ℝ, P χ₁ χ t = x := by
  obtain ⟨a, ha⟩ := LFunction_real hχ₁ h₁ ht
  obtain ⟨b, hb⟩ := LFunction_real hχ h ht
  obtain ⟨c, hc⟩ := LFunction_real hψ (prodChar_sq h₁ h) ht
  exact ⟨a * b * c, by unfold P; rw [ha, hb, hc]; push_cast; ring⟩

/-- `P` is positive on `[β, 1)` when no `L`-factor vanishes on `[β, 1)`. -/
lemma P_pos_of_no_zero {χ₁ : DirichletCharacter ℂ N₁} {χ : DirichletCharacter ℂ N}
    (hχ₁ : χ₁ ≠ 1) (hχ : χ ≠ 1) (hψ : prodChar χ₁ χ ≠ 1) (h₁ : χ₁ ^ 2 = 1) (h : χ ^ 2 = 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hnz : ∀ t : ℝ, β ≤ t → t < 1 → LFunction χ₁ t ≠ 0 ∧ LFunction χ t ≠ 0 ∧
      LFunction (prodChar χ₁ χ) t ≠ 0) :
    ∃ p : ℝ, 0 < p ∧ P χ₁ χ β = p := by
  set f : ℝ → ℝ := fun t => (P χ₁ χ t).re with hf
  have hfc : Continuous f :=
    continuous_re.comp ((differentiable_P hχ₁ hχ hψ).continuous.comp continuous_ofReal)
  have hreal : ∀ t : ℝ, 0 < t → P χ₁ χ t = (f t : ℂ) := by
    intro t ht
    obtain ⟨x, hx⟩ := P_real hχ₁ hχ hψ h₁ h ht
    simp only [hf, hx, ofReal_re]
  have hne : ∀ t : ℝ, β ≤ t → P χ₁ χ t ≠ 0 := by
    intro t ht
    unfold P
    by_cases ht1 : t < 1
    · obtain ⟨a, b, c⟩ := hnz t ht ht1
      exact mul_ne_zero (mul_ne_zero a b) c
    · push Not at ht1
      have hre : 1 ≤ (t : ℂ).re := by simpa using ht1
      exact mul_ne_zero (mul_ne_zero (LFunction_ne_zero_of_one_le_re χ₁ (.inl hχ₁) hre)
        (LFunction_ne_zero_of_one_le_re χ (.inl hχ) hre))
        (LFunction_ne_zero_of_one_le_re _ (.inl hψ) hre)
  -- positivity at `2`
  have hf2 : 0 < f 2 := by
    have hA : 0 < LSeries ↗(coeff χ₁ χ) ((2 : ℝ) : ℂ) :=
      LSeries.positive (fun k => coeff_nonneg h₁ h k) (by simp [coeff_one])
        (two_mem_abscissa χ₁ χ)
    have hab1 : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < ((2 : ℝ) : EReal) := by
      refine (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        (x := 1) fun y hy => LSeriesSummable_one_iff.mpr (by simpa using hy)).trans_lt
        (EReal.coe_lt_coe_iff.mpr (by norm_num))
    have hZ : 0 < LSeries 1 ((2 : ℝ) : ℂ) :=
      LSeries.positive (fun _ => zero_le_one) zero_lt_one hab1
    have hco := LSeries_coeff χ₁ χ (s := ((2 : ℝ) : ℂ)) (by simp)
    have hP2 := hreal 2 two_pos
    rw [show LFunction χ₁ ((2 : ℝ) : ℂ) * LFunction χ ((2 : ℝ) : ℂ) *
        LFunction (prodChar χ₁ χ) ((2 : ℝ) : ℂ) = P χ₁ χ ((2 : ℝ) : ℂ) from rfl, hP2] at hco
    rw [hco] at hA
    have hZre : LSeries 1 ((2 : ℝ) : ℂ) = ((LSeries 1 ((2 : ℝ) : ℂ)).re : ℂ) := by
      have him : (LSeries 1 ((2 : ℝ) : ℂ)).im = 0 := by
        have := (Complex.lt_def.mp hZ).2
        rw [← this]; rfl
      apply Complex.ext
      · rw [ofReal_re]
      · rw [ofReal_im]; exact him
    rw [hZre, ← ofReal_mul, zero_lt_real] at hA
    have hZ' : 0 < (LSeries 1 ((2 : ℝ) : ℂ)).re := by
      have := (Complex.lt_def.mp hZ).1; simpa using this
    exact pos_of_mul_pos_right hA hZ'.le
  refine ⟨f β, ?_, hreal β hβ0⟩
  by_contra hneg
  push Not at hneg
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (show β ≤ 2 by linarith) hfc.continuousOn
    ⟨hneg, hf2.le⟩
  apply hne t ht.1
  rw [hreal t (by linarith [ht.1]), hft, ofReal_zero]

lemma F_nonpos_of_P_pos {χ₁ : DirichletCharacter ℂ N₁} {χ : DirichletCharacter ℂ N}
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p : ℝ} (hp : 0 < p) (hP : P χ₁ χ β = p) :
    (F χ₁ χ β).re ≤ 0 := by
  obtain ⟨h, hH, hh⟩ := Hz_real hβ0
  have hb : (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
  have hF : F χ₁ χ β = ((1 / (β - 1) + h) * p : ℝ) := by
    unfold F; rw [hH, hP, hb]; push_cast; ring
  rw [hF, ofReal_re]
  have h1 : 1 / (β - 1) < -1 := by
    rw [div_lt_iff_of_neg (by linarith)]; linarith
  nlinarith

/-! ### Siegel's theorem -/

lemma siegel_aux {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖LFunction χ 1‖ := by
  by_cases ha : ∃ (N₁ : ℕ) (_ : NeZero N₁) (χ₁ : DirichletCharacter ℂ N₁) (β : ℝ),
      χ₁ ≠ 1 ∧ χ₁ ^ 2 = 1 ∧ 1 - ε / 16 ≤ β ∧ β < 1 ∧ LFunction χ₁ β = 0
  · obtain ⟨N₁, hN₁, χ₁, β, hne, hsq, hβ1, hβ2, hz⟩ := ha
    refine siegel_of_witness hε1 hne hsq hβ1 hβ2 fun N _ χ _ _ _ => ?_
    have : F χ₁ χ β = 0 := by unfold F P; rw [hz]; ring
    rw [this, zero_re]
  · push Not at ha
    have hδ : 0 < 1 - ε / 16 := by linarith
    refine siegel_of_witness hε1 chi4_ne chi4_sq (β := 1 - ε / 16) le_rfl (by linarith)
      fun N _ χ hχ hsq hψ => ?_
    obtain ⟨p, hp, hPp⟩ := P_pos_of_no_zero chi4_ne hχ hψ chi4_sq hsq hδ (by linarith)
      fun t ht1 ht2 => ⟨ha 4 inferInstance chi4 t chi4_ne chi4_sq ht1 ht2,
        ha N inferInstance χ t hχ hsq ht1 ht2,
        ha (4 * N) inferInstance (prodChar chi4 χ) t hψ (prodChar_sq chi4_sq hsq) ht1 ht2⟩
    exact F_nonpos_of_P_pos hδ (by linarith) hp hPp

/-- **Siegel's theorem** (target 1). -/
theorem siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  intro ε hε
  rcases le_or_gt ε 1 with h | h
  · exact siegel_aux hε h
  · obtain ⟨c, hc, H⟩ := siegel_aux one_pos le_rfl
    refine ⟨c, hc, fun N _ χ hχ hsq => le_trans ?_ (H N χ hχ hsq)⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (natCast_one_le N) (by linarith)) hc.le

end SiegelThmLib
