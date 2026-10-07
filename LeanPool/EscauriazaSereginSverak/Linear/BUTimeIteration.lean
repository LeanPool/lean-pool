/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUTimeStep

/-!
# Time iteration for backward uniqueness

The short-time conclusion extends to every time below one by the geometric
sequence in `lem:bu-iterate`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Repeated affine rescaling turns a uniform short-time result into
vanishing throughout the positive-time half-space cylinder. -/
theorem bu_time_iteration_from_short
    (c₁ A γ₁ : ℝ) (hc₁ : 0 < c₁) (hA : 0 ≤ A)
    (hγ₁ : 0 < γ₁) (hγ₁one : γ₁ < 1)
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
        Real.exp (A * vec3EuclideanNorm z.1 ^ 2))
    (hshort : ∀ (v : ParabolicPoint → Vec3)
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
          Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) →
      ∀ x : Vec3, 0 < x 2 → ∀ s : ℝ,
        0 < s → s < γ₁ → v (x, s) = 0) :
    ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      0 < t → t < 1 → w (x, t) = 0 := by
  let q : ℝ := 1 - γ₁
  have hq0 : 0 < q := by dsimp [q]; linarith only [hγ₁one]
  have hq1 : q < 1 := by dsimp [q]; linarith only [hγ₁]
  let τk : ℕ → ℝ := fun k => 1 - q ^ k
  have hτk0 (k : ℕ) : 0 ≤ τk k := by
    dsimp [τk]
    have hpow : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
    linarith only [hpow]
  have hτk1 (k : ℕ) : τk k < 1 := by
    dsimp [τk]
    have hpow : 0 < q ^ k := pow_pos hq0 _
    linarith only [hpow]
  have hτsucc (k : ℕ) : τk (k + 1) = τk k + (1 - τk k) * γ₁ := by
    dsimp [τk, q]
    rw [pow_succ]
    ring
  have hzero (k : ℕ) :
      ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
        0 < t → t < τk k → w (x, t) = 0 := by
    induction k with
    | zero =>
        intro x hx t ht0 ht
        have : τk 0 = 0 := by simp [τk]
        rw [this] at ht
        exact (False.elim ((not_lt_of_ge ht0.le) ht))
    | succ k ih =>
        have hstep := bu_time_extension_step c₁ A γ₁ (τk k) hc₁ hA
          (hτk0 k) (hτk1 k) w Dw D2w Dtw hcont hinit hderiv
          hL2 hineq hgrowth ih hshort
        intro x hx t ht0 ht
        exact hstep x hx t ht0 (by rw [← hτsucc k]; exact ht)
  intro x hx t ht0 ht1
  obtain ⟨k, hk⟩ := bu_iteration_time_coverage hγ₁ hγ₁one ht1
  exact hzero k x hx t ht0 (by simpa only [τk, q] using hk)

end ESS
