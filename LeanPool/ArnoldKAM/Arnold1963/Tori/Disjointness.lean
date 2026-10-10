/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Tori.FrequencyInjectivity
public import LeanPool.ArnoldKAM.Arnold1963.Tori.AngleBounds
public import LeanPool.ArnoldKAM.Arnold1963.Dynamics.OrbitUniqueness

/-!
Disjointness of invariant tori from ODE uniqueness, bounded angle corrections, and frequency
injectivity within a single chart.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

theorem eq_zero_of_bounded_affine_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u v : E} {C : ℝ}
    (hb : ∀ t : ℝ, ‖u + t • v‖ ≤ C) : v = 0 := by
  by_contra hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  let t : ℝ := (C + ‖u‖ + 1) / ‖v‖
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hh := norm_sub_le (u + t • v) u
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hh
  have he : t * ‖v‖ = C + ‖u‖ + 1 := div_mul_cancel₀ _ hn.ne'
  rw [he] at hh
  linarith [hb t]

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem frequency_eq_of_orbit_eq {p p' : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) (hp' : p' ∈ realSlice (h.limitDomain b))
    (q q' : RealSpace n) (he : h.orbit b p q = h.orbit b p' q') :
    h.limitFrequency b (complexify p) = h.limitFrequency b (complexify p') := by
  apply sub_eq_zero.mp
  apply eq_zero_of_bounded_affine_line
    (u := complexify q - complexify q') (C := 4 * (beta δ₁ 0 : ℝ))
  intro t
  let x : ComplexPhaseSpace n := (complexify p,
    complexify q + (t : ℂ) • h.limitFrequency b (complexify p))
  let y : ComplexPhaseSpace n := (complexify p',
    complexify q' + (t : ℂ) • h.limitFrequency b (complexify p'))
  have hx : x ∈ h.limitPhase b := by
    rw [show x = complexifyPhase
      (p, q + t • realPart (h.limitFrequency b (complexify p))) by
        apply Prod.ext
        · rfl
        change complexify q + (t : ℂ) • h.limitFrequency b (complexify p) = _
        rw [← h.limitFrequency_real_value b hp]
        ext j
        simp [complexifyPhase, complexify, smul_eq_mul]]
    exact h.commonPhase_subset b ⟨hp, complexify_mem_angleStrip _ _⟩
  have hy : y ∈ h.limitPhase b := by
    rw [show y = complexifyPhase
      (p', q' + t • realPart (h.limitFrequency b (complexify p'))) by
        apply Prod.ext
        · rfl
        change complexify q' + (t : ℂ) • h.limitFrequency b (complexify p') = _
        rw [← h.limitFrequency_real_value b hp']
        ext j
        simp [complexifyPhase, complexify, smul_eq_mul]]
    exact h.commonPhase_subset b ⟨hp', complexify_mem_angleStrip _ _⟩
  have hxy : h.limitMap b x = h.limitMap b y := congrFun he t
  have ht := norm_sub_le_norm_sub_add_norm_sub x (h.limitMap b x) y
  rw [norm_sub_rev x (h.limitMap b x), hxy] at ht
  have hd : ‖x - y‖ < 4 * (beta δ₁ 0 : ℝ) := by
    have hxB := h.limitMap_displacement b hx
    have hyB := h.limitMap_displacement b hy
    rw [hxy] at hxB
    linarith
  have ha := (norm_snd_le (x - y)).trans hd.le
  have heq : complexify q - complexify q' +
      t • (h.limitFrequency b (complexify p) - h.limitFrequency b (complexify p')) =
      (x - y).2 := by
    ext j
    simp [x, y, Complex.real_smul]
    ring
  rw [heq]
  exact ha

theorem realLimitMap_injOn : InjOn (h.realLimitMap b)
    (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealSpace n))) := by
  intro x hx y hy he
  have hei : h.orbit b x.1 x.2 0 = h.orbit b y.1 y.2 0 := by
    rw [h.orbit_initial, h.orbit_initial]
    have hc := congrArg complexifyPhase he
    change complexifyPhase (realPartPhase (h.limitMap b (complexifyPhase x))) =
      complexifyPhase (realPartPhase (h.limitMap b (complexifyPhase y))) at hc
    simpa only [h.limitMap_real_value b hx.1, h.limitMap_real_value b hy.1] using hc
  have heo := h.orbit_eq_of_initial_eq b hx.1 hy.1 x.2 y.2 hei
  have hep := h.limitFrequency_injOn b hx.1 hy.1
    (h.frequency_eq_of_orbit_eq b hx.1 hy.1 x.2 y.2 heo)
  have hp : x.1 = y.1 := (isometry_complexify n).injective hep
  apply Prod.ext hp
  apply (isometry_complexify n).injective
  apply h.angleMap_injOn b hx.1 (complexify_mem_angleStrip _ _) (complexify_mem_angleStrip _ _)
  have hh := congrArg Prod.snd hei
  simpa only [h.orbit_initial, complexifyPhase, ← hp, angleMap] using hh

theorem torusLimitMap_injOn : InjOn (h.torusLimitMap b)
    (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n))) := by
  intro x hx y hy he
  obtain ⟨k, hk⟩ := (torusProjection_eq_iff
    (h.realLimitMap b (torusRepresentative x))
    (h.realLimitMap b (torusRepresentative y))).mp he
  rw [← h.realLimitMap_shift b (x := torusRepresentative y) hy.1 k] at hk
  have hh := h.realLimitMap_injOn b ⟨hx.1, mem_univ _⟩ ⟨hy.1, mem_univ _⟩ hk
  have hq := congrArg torusProjection hh
  simpa only [torusProjection_shift, torusProjection_representative] using hq

/-- The image of one retained action label and the full real angle torus. -/
def invariantTorus (p : RealSpace n) : Set (RealPhaseSpace n) :=
  h.torusLimitMap b '' ({p} ×ˢ (univ : Set (RealTorus n)))

theorem invariantTorus_disjoint {p p' : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) (hp' : p' ∈ realSlice (h.limitDomain b))
    (hne : p ≠ p') : Disjoint (h.invariantTorus b p) (h.invariantTorus b p') := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxp : x.1 = p := hx.1
  have hyp : y.1 = p' := hy.1
  have hh := h.torusLimitMap_injOn b
    (x₁ := x) ⟨hxp ▸ hp, mem_univ _⟩ (x₂ := y) ⟨hyp ▸ hp', mem_univ _⟩
    (hxz.trans hyz.symm)
  exact hne (hxp.symm.trans ((congrArg Prod.fst hh).trans hyp))

end Iteration.InitialData
end KamProject.Arnold1963
