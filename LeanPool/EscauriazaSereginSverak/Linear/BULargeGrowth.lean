/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUFullSlab

/-!
# Finite time-slab rescaling for large Gaussian growth

Equal short slabs give a finite covering of every time below one while
keeping the rescaled growth exponent below the small-growth threshold.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The large-growth case follows by a finite number of rescaled
small-growth applications. -/
theorem bu_large_growth_from_small
    (c₁ M : ℝ) (hc₁ : 0 < c₁)
    (hM : (1 / (10 : ℝ) ^ 12) < M)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    (hsmall : ∀ (v : ParabolicPoint → Vec3)
      (Dv : ParabolicPoint → Fin 3 → Vec3)
      (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
      (Dtv : ParabolicPoint → Vec3),
      ContinuousOn v ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) →
      (∀ x : Vec3, 0 < x 2 → v (x, 0) = 0) →
      HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
        v Dv D2v Dtv →
      (∀ S : Set ParabolicPoint,
        S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
        Bornology.IsBounded S →
        (∫⁻ z in S, ‖Dv z‖ₑ ^ (2 : ℝ) +
          ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) →
      (∀ᵐ z ∂(volume.restrict
        (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
        vec3EuclideanNorm (fun i => Dtv z i + ∑ j, D2v z i j j) ≤
          c₁ * (Real.sqrt (spatialGradientSq v Dv z) +
            vec3EuclideanNorm (v z))) →
      (∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        vec3EuclideanNorm (v z) ≤
          Real.exp (((1 / (10 : ℝ) ^ 12) / 2) *
            vec3EuclideanNorm z.1 ^ 2)) →
      ∀ x : Vec3, 0 < x 2 → ∀ s : ℝ,
        0 < s → s < 1 → v (x, s) = 0) :
    ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      0 < t → t < 1 → w (x, t) = 0 := by
  let A₀ : ℝ := 1 / (10 : ℝ) ^ 12
  have hA₀pos : 0 < A₀ := by dsimp [A₀]; positivity
  have hMpos : 0 < M := hA₀pos.trans hM
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M / A₀)
  have hNpos : 0 < (N : ℝ) := by
    have hquot : 0 < 2 * M / A₀ := div_pos (mul_pos (by norm_num) hMpos) hA₀pos
    linarith only [hN, hquot]
  let δ : ℝ := (N : ℝ)⁻¹
  have hδpos : 0 < δ := inv_pos.mpr hNpos
  have hNδ : (N : ℝ) * δ = 1 := by
    dsimp [δ]
    field_simp [hNpos.ne']
  have hMδ : M * δ ≤ A₀ / 2 := by
    have hprod : 2 * M < (N : ℝ) * A₀ :=
      (div_lt_iff₀ hA₀pos).1 hN
    dsimp [δ]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hNpos).2
    calc
      M ≤ (N : ℝ) * A₀ / 2 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        nlinarith only [hprod]
      _ = A₀ / 2 * N := by ring
  have hδle : δ ≤ 1 := by
    have hNge : (1 : ℝ) ≤ N := by
      have hNnat : 0 < N := by exact_mod_cast hNpos
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNnat))
    exact (inv_le_one₀ hNpos).2 hNge
  let scale : ℝ := Real.sqrt δ
  have hscale : 0 < scale := Real.sqrt_pos.2 hδpos
  have hscaleSq : scale ^ 2 = δ := Real.sq_sqrt hδpos.le
  have hAres : M * scale ^ 2 ≤ A₀ / 2 := by rw [hscaleSq]; exact hMδ
  have hzero (k : ℕ) (hk : k ≤ N) :
      ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
        0 < t → t < (k : ℝ) * δ → w (x, t) = 0 := by
    induction k with
    | zero =>
        intro x hx t ht0 ht
        simp only [Nat.cast_zero, zero_mul] at ht
        exact (False.elim ((not_lt_of_ge ht0.le) ht))
    | succ k ih =>
        have hklt : k < N := Nat.lt_of_succ_le hk
        have hkle : k ≤ N := hklt.le
        have hτle : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδpos.le
        have hτlt : (k : ℝ) * δ < 1 := by
          have hkc : (k : ℝ) < N := by exact_mod_cast hklt
          have hmul := mul_lt_mul_of_pos_right hkc hδpos
          rwa [hNδ] at hmul
        have hupper : (k : ℝ) * δ + scale ^ 2 ≤ 1 := by
          rw [hscaleSq]
          have hkc : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
          have hmul := mul_le_mul_of_nonneg_right hkc hδpos.le
          rw [hNδ] at hmul
          push_cast at hmul
          nlinarith only [hmul]
        have hzeroτ : ∀ x : Vec3, 0 < x 2 →
            w (x, (k : ℝ) * δ) = 0 := by
          intro x hx
          by_cases hk0 : k = 0
          · subst k
            simp only [Nat.cast_zero, zero_mul]
            exact hinit x hx
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
            have hτpos : 0 < (k : ℝ) * δ :=
              mul_pos (by exact_mod_cast hkpos) hδpos
            exact bu_zero_at_time_of_left w hcont ((k : ℝ) * δ)
              hτpos hτlt (ih hkle) x hx
        have hslab := bu_affine_full_slab c₁ M (A₀ / 2)
          ((k : ℝ) * δ) scale hc₁ hτle hscale hupper hAres
          w Dw D2w Dtw hcont hzeroτ hderiv hL2 hineq hgrowth hsmall
        intro x hx t ht0 ht
        by_cases htk : t < (k : ℝ) * δ
        · exact ih hkle x hx t ht0 htk
        by_cases hteq : t = (k : ℝ) * δ
        · rw [hteq]
          exact hzeroτ x hx
        have htgt : (k : ℝ) * δ < t :=
          lt_of_le_of_ne (le_of_not_gt htk) (Ne.symm hteq)
        apply hslab x hx t htgt
        rw [hscaleSq]
        push_cast at ht
        nlinarith only [ht]
  intro x hx t ht0 ht1
  have hNzero := hzero N le_rfl
  exact hNzero x hx t ht0 (by rw [hNδ]; exact ht1)

end ESS
