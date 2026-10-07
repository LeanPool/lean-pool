/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessFiniteRank
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessCover

/-!
# Compactness Approximation

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The local slice and integrated gradient bounds give finite-rank spatial
approximations with uniformly small space-time error. -/
theorem exists_finite_rank_average_approximation_of_mixed_bounds
    {K W Kc : Set Vec3} {J : Set ℝ}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hWKc : W ⊆ Kc) (hJ : MeasurableSet J)
    [IsFiniteMeasure (volume.restrict J)]
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (hDuMeas : ∀ n, Measurable (Du n))
    (hweak : ∀ n, ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn W (fun y => u n (y,t) i)
        (fun y => Du n (y,t) i))
    (M G : ℝ≥0∞) (hM : M < ⊤) (hG : G < ⊤)
    (huBound : ∀ n t, t ∈ J → ∫⁻ x in Kc,
      ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^ (2 : ℝ) ∂volume ≤ M)
    (hDuBound : ∀ n, (∫⁻ t in J, ∫⁻ x in Kc,
      ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t)) ∂volume) ≤ G) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ m : ℕ, ∃ N : ℕ,
      ∃ s : Fin N → Set {x : Vec3 // x ∈ K},
      ∃ t : Finset (Σ i : Fin N,
        {x : {x : Vec3 // x ∈ K} // x ∈ s i}),
      ∃ φ : {p : Σ i : Fin N,
        {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t} → Vec3 → ℝ,
        (∀ p, Measurable (φ p)) ∧
        (∀ p y, 0 ≤ φ p y ∧ φ p y ≤ 1) ∧
        (∀ p : {p : Σ i : Fin N,
          {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t},
          CKN.euclideanBall p.1.2.1.1 (1 / (m + 1)) ⊆ W) ∧
        ∀ n,
          (∫⁻ z in K ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
            (u n z - ∑ p, φ p z.1 • (fun j => average
              (volume.restrict (CKN.euclideanBall p.1.2.1.1 (1 / (m + 1))))
                (fun y => u n (y,z.2) j))) ^ 2)
            ∂(volume : Measure ParabolicPoint)) ≤ ε := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hballδ⟩ := exists_uniform_euclidean_ball_subset_open hK hW hKW
  obtain ⟨N, hcover⟩ := exists_weighted_colored_finite_vec3_ball_cover hK
  have hsmall := eventually_small_colored_ball_energy_factor (N := N) G hG ε hε
  have hradius : ∀ᶠ m : ℕ in atTop, (1 / (m + 1) : ℝ) < δ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Iio δ from hδ))
  obtain ⟨m, hm⟩ := (hsmall.and hradius).exists
  have hr : 0 < (1 / (m + 1) : ℝ) := by positivity
  obtain ⟨s, t, φ, hsDisjoint, hsCover, hφ, hweight, hsum, hsupport,
    hzero, hdisjoint⟩ := hcover (1 / (m + 1)) hr
  have hball (p : {p : Σ i : Fin N,
      {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t}) :
      CKN.euclideanBall p.1.2.1.1 (1 / (m + 1)) ⊆ W := by
    apply Set.Subset.trans ?_ (hballδ p.1.2.1.1 p.1.2.1.2)
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr,
      CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hδ]
    exact CKN.Foundation.Parabolic.vec3Ball_mono (le_of_lt hm.2)
  refine ⟨m, N, s, t, φ, hφ, hweight, hball, ?_⟩
  intro n
  have hsupport' (p : {p : Σ i : Fin N,
      {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t})
      (y : Vec3) (hp : φ p y ≠ 0) :
      y ∈ CKN.euclideanBall p.1.2.1.1 (1 / (m + 1)) := by
    by_cases hy : y ∈ K
    · rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
      exact hsupport p y hy hp
    · exact False.elim (hp (hzero p y hy))
  have hdisjoint' (p q : {p : Σ i : Fin N,
      {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t})
      (hpq : p ≠ q) (hcolor : p.1.1 = q.1.1) :
      Disjoint (CKN.euclideanBall p.1.2.1.1 (1 / (m + 1)))
        (CKN.euclideanBall q.1.2.1.1 (1 / (m + 1))) := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr,
      CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
    exact hdisjoint p q hpq hcolor
  have hbound :=
    lintegral_vec3_finite_rank_average_error_le_of_mixed_bounds
      (W := W) (Kc := Kc) (K := K) (J := J) hr (u n) (Du n)
      (huMeas n) (hDuMeas n) (hweak n) hJ M G hM hG hWKc
      (huBound n) (hDuBound n) hK.measurableSet
      (fun p => p.1.2.1.1) (fun p => p.1.1) φ hφ hweight hsum hball
      hsupport' hdisjoint'
  calc
    (∫⁻ z in K ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
      (u n z - ∑ p, φ p z.1 • (fun j => average
        (volume.restrict (CKN.euclideanBall p.1.2.1.1 (1 / (m + 1))))
          (fun y => u n (y,z.2) j))) ^ 2)
      ∂(volume : Measure ParabolicPoint)) ≤
      3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) (1 / (m + 1)))) ^
          (1 / 3 : ℝ)) ^ (2 : ℕ) *
        (∑ _j : Fin N, ∫⁻ t in J, ∫⁻ y in W,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (y,t))
            ∂volume) := hbound
    _ ≤ 3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) (1 / (m + 1)))) ^
          (1 / 3 : ℝ)) ^ (2 : ℕ) * (∑ _j : Fin N, G) := by
        gcongr with j
        calc
          (∫⁻ t in J, ∫⁻ y in W,
            ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (y,t))
              ∂volume) ≤
            (∫⁻ t in J, ∫⁻ y in Kc,
              ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (y,t))
                ∂volume) := by
                  apply lintegral_mono
                  intro t
                  exact lintegral_mono_set hWKc
          _ ≤ G := hDuBound n
    _ ≤ ε := hm.1

end CKN.Leray
