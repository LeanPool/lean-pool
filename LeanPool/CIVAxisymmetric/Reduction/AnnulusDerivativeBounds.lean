/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial

/-! ### Elementary real-number lemmas -/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- Given `Rm < Rp`, there exist two reals strictly between them. -/
theorem exists_two_lt_of_lt {Rm Rp : ℝ} (h : Rm < Rp) :
    ∃ Rm' Rp' : ℝ, Rm < Rm' ∧ Rm' < Rp' ∧ Rp' < Rp := by
  refine ⟨(2 * Rm + Rp) / 3, (Rm + 2 * Rp) / 3, ?_, ?_, ?_⟩
  · nlinarith only [h]
  · nlinarith only [h]
  · nlinarith only [h]

/-- Given `t₀ ∈ (-1, 0)`, there exists `varrho > 0` such that `varrho² < -t₀`,
`t₀ + varrho²` is still in `(-1, 0)`, and `t₀ + varrho² > t₀`. -/
theorem exists_sq_lt_neg_and_mem_Ioo {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0) :
    ∃ varrho : ℝ, 0 < varrho ∧ varrho ^ 2 < -t₀ ∧ t₀ < t₀ + varrho ^ 2 ∧ t₀ + varrho ^ 2 < 0 := by
  set varrho := Real.sqrt (-t₀ / 2) with hvarrho
  have hpos : 0 < varrho := by
    rw [hvarrho]
    refine Real.sqrt_pos.2 ?_
    have ht0_neg : t₀ < 0 := ht₀.2
    linarith only [ht0_neg]
  have hsq : varrho ^ 2 = -t₀ / 2 := by
    rw [hvarrho]
    refine Real.sq_sqrt ?_
    have ht0_neg : t₀ < 0 := ht₀.2
    linarith only [ht0_neg]
  have h_lt_neg_t0 : varrho ^ 2 < -t₀ := by
    rw [hsq]
    have ht0_neg : t₀ < 0 := ht₀.2
    linarith only [ht0_neg]
  have h_t0_lt : t₀ < t₀ + varrho ^ 2 := by
    nlinarith only [hpos]
  have h_sum_lt : t₀ + varrho ^ 2 < 0 := by
    rw [hsq]
    have ht0_neg : t₀ < 0 := ht₀.2
    linarith only [ht₀.1, ht0_neg]
  exact ⟨varrho, hpos, h_lt_neg_t0, h_t0_lt, h_sum_lt⟩

/-- Reduction step for annulus derivative bounds: fix `varrho` and shrink the
annulus radii so that Serrin's interior estimates (assumed as hypothesis
`hserrin`) produce bounds on `u`, `∇u`, `∇²u` on a compactly contained
sub-annulus over `(t₀, 0)`, uniformly up to the blow-up time.

This is `lem:aniso:annulus`: the Serrin-type hypothesis
`hserrin` states that whenever `u` is bounded on a slightly larger annulus
and time interval, it and its first two spatial derivatives are bounded on any
strictly smaller concentric sub-annulus over any strictly earlier time
interval `(t₀', 0)` with `t₀' > t₀`.  The conclusion produces such a
sub-annulus and time interval where the derivative bounds hold. -/
theorem step_annulus_derivative_bounds (u : ParabolicPoint → Vec3)
    (Rm Rp t₀ : ℝ) (hR : 0 ≤ Rm ∧ Rm < Rp ∧ Rp ≤ 1) (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (Mu : ℝ) (hbdd : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ 0, vec3EuclideanNorm (u (x, t)) ≤ Mu)
    (hserrin : (∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ 0, vec3EuclideanNorm (u (x, t)) ≤ Mu) →
      ∀ Rm' Rp' t₀' : ℝ, Rm < Rm' → Rm' < Rp' → Rp' < Rp → t₀ < t₀' → t₀' < 0 →
      ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
        ∀ t ∈ Ioo t₀' 0, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K) :
    ∃ Rm' Rp' t₀' : ℝ, Rm < Rm' ∧ Rm' < Rp' ∧ Rp' < Rp ∧ t₀ < t₀' ∧ t₀' < 0 ∧
      ∃ K : ℝ, ∀ x : Vec3, Rm' < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp' →
        ∀ t ∈ Ioo t₀' 0, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ K := by
  obtain ⟨Rm', Rp', hRm'lt, hRp'lt, hRp'lt2⟩ := exists_two_lt_of_lt hR.2.1
  obtain ⟨varrho, _, hvsq, ht0'gt, ht0'lt⟩ := exists_sq_lt_neg_and_mem_Ioo ht₀
  refine ⟨Rm', Rp', t₀ + varrho ^ 2, hRm'lt, hRp'lt, hRp'lt2, ht0'gt, ht0'lt, ?_⟩
  exact hserrin hbdd Rm' Rp' (t₀ + varrho ^ 2) hRm'lt hRp'lt hRp'lt2 ht0'gt ht0'lt

end CIV
