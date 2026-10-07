/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGeometry

/-!
# Energy at a bad point

Failure of the good-point criterion gives the quantitative lower bound at
each admissible past radius (`prop:blowup-limit`).
-/

public section


open Set CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A small past cylinder centered in the blow-up region is admissible for the
good-point criterion. -/
theorem blowupSmallRadius_admissible
    (x₀ : Vec3) (t₀ r : ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : 0 < r) (hrsmall : r < 1 / 4) :
    (x₀, t₀) ∈ goodPointClosedTopDomain ∧
      goodPointPastCylinder x₀ t₀ r ⊆ goodPointDomain ∧
      closure (parabolicCylinder x₀ t₀ r) ⊆
        goodPointClosedTopDomain := by
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hr2 : r ^ 2 < 3 / 4 := by
    nlinarith only [hr, hrsmall]
  have hball : {y : Vec3 | vec3EuclideanNorm (y - x₀) ≤ r} ⊆
      vec3Ball 0 1 := by
    intro y hy
    have htri := vec3EuclideanNorm_add_le (y - x₀) x₀
    have heq : y - x₀ + x₀ = y := by abel
    rw [heq] at htri
    have hy' : vec3EuclideanNorm (y - x₀) ≤ r := hy
    apply mem_vec3Ball.mpr
    simpa only [sub_zero] using (by
      linarith only [hy', htri, hxnorm, hrsmall] : vec3EuclideanNorm y < 1)
  have hbase : (x₀, t₀) ∈ goodPointClosedTopDomain := by
    constructor
    · apply mem_vec3Ball.mpr
      simpa only [sub_zero] using (by
        linarith only [hxnorm] : vec3EuclideanNorm x₀ < 1)
    · exact ⟨by linarith only [ht₀.1], ht₀.2⟩
  have hopen : goodPointPastCylinder x₀ t₀ r ⊆ goodPointDomain := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    constructor
    · apply hball
      exact (mem_vec3Ball.mp hy).le
    · exact ⟨by linarith only [ht₀.1, hr2, hs.1],
        by linarith only [ht₀.2, hs.2]⟩
  have hclosed : closure (parabolicCylinder x₀ t₀ r) ⊆
      goodPointClosedTopDomain := by
    rw [closure_parabolicCylinder hr]
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    exact ⟨hball hy,
      ⟨by linarith only [ht₀.1, hr2, hs.1], hs.2.trans ht₀.2⟩⟩
  exact ⟨hbase, hopen, hclosed⟩

/-- The negation of the good-point criterion supplies the fixed energy
threshold at every admissible past radius. -/
theorem blowupBadPointEnergy_lower
    (ε₀ : ℝ) (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (z₀ : ParabolicPoint) (r : ℝ)
    (hbad : ¬ IsGoodPoint ε₀ u p z₀)
    (hbase : z₀ ∈ goodPointClosedTopDomain)
    (hr : 0 < r)
    (hopen : goodPointPastCylinder z₀.1 z₀.2 r ⊆ goodPointDomain)
    (hclosed : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆
      goodPointClosedTopDomain) :
    ENNReal.ofReal (ε₀ / 8) ≤
      ENNReal.ofReal (r⁻¹ ^ 2) *
        goodPointEnergy u p z₀.1 z₀.2 r := by
  apply le_of_not_gt
  intro hsmall
  exact hbad ⟨hbase, r, hr, hopen, hclosed, hsmall⟩

end ESS
