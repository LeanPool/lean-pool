/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalStrong
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessBallPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessTimeGlue
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTermTime

/-!
# Compactness Fixed Rank

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- At a fixed finite spatial rank, weak convergence of cutoff slices makes
the ball-average approximants converge strongly on a compact rectangle. -/
theorem tendsto_finite_rank_ball_average_approximation
    {ι : Type*} [Fintype ι] {I J : Set ℝ} {K : Set Vec3}
    (hJI : J ⊆ I) (hK : MeasurableSet K) (hJ : MeasurableSet J)
    [IsFiniteMeasure (volume.restrict K)] [IsFiniteMeasure (volume.restrict J)]
    (B : ι → Set Vec3)
    (hB : ∀ i, MeasurableSet (B i))
    (hBfinite : ∀ i, volume (B i) < ⊤)
    (u : ℕ → ParabolicPoint → Vec3) (huMeas : ∀ n, Measurable (u n))
    (χ : Vec3 → ℝ) (hχone : ∀ i x, x ∈ B i → χ x = 1)
    (hmem : ∀ n (t : I), MemLp
      (fun x => χ x • WithLp.toLp 2 (u n (x, t.1)))
      2 (volume : Measure Vec3))
    (V : I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ t x, Tendsto
      (fun n => inner ℝ ((hmem n t).toLp
        (fun y => χ y • WithLp.toLp 2 (u n (y, t.1)))) x) atTop
      (nhds (inner ℝ (V t) x)))
    (hVcont : ∀ x, Continuous (fun t => inner ℝ (V t) x))
    (huniform : ∀ x ε, 0 < ε → ∀ᶠ n in atTop, ∀ t, (ht : t ∈ J) →
      dist (inner ℝ ((hmem n ⟨t, hJI ht⟩).toLp
        (fun y => χ y • WithLp.toLp 2 (u n (y, t)))) x)
        (inner ℝ (V ⟨t, hJI ht⟩) x) < ε)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n t, (ht : t ∈ J) →
      ‖(hmem n ⟨t, hJI ht⟩).toLp
        (fun y => χ y • WithLp.toLp 2 (u n (y, t)))‖ ≤ C)
    (φ : ι → Vec3 → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφbound : ∀ i x, |φ i x| ≤ 1) :
    ∃ hP : ∀ n, MemLp
      (fun z : Vec3 × ℝ => WithLp.toLp 2
        (∑ i, φ i z.1 • (fun j => average (volume.restrict (B i))
          (fun y => u n (y,z.2) j)))) 2
      ((volume.restrict K).prod (volume.restrict J)),
      ∃ Q : Vec3 × ℝ → L2Vec3,
        ∃ hQ : MemLp Q 2 ((volume.restrict K).prod (volume.restrict J)),
          Tendsto (fun n => (hP n).toLp (fun z : Vec3 × ℝ =>
            WithLp.toLp 2 (∑ i, φ i z.1 •
              (fun j => average (volume.restrict (B i))
                (fun y => u n (y,z.2) j))))) atTop (nhds (hQ.toLp Q)) := by
  classical
  let ψ : ι → Fin 3 → Lp L2Vec3 2 (volume : Measure Vec3) :=
    fun i j => indicatorConstLp (2 : ℝ≥0∞) (hB i) (hBfinite i).ne
      (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
  let c : ι → ℝ := fun i => (volume (B i)).toReal⁻¹
  have hc (i : ι) : 0 ≤ c i := inv_nonneg.mpr ENNReal.toReal_nonneg
  let a : ℕ → ι → ℝ → Vec3 := fun n i t j =>
    average (volume.restrict (B i)) (fun y => u n (y, t) j)
  let b : ι → ℝ → Vec3 := fun i t =>
    if ht : t ∈ J then
      fun j => c i * inner ℝ (V ⟨t, hJI ht⟩) (ψ i j)
    else 0
  have hcoef (i : ι) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ t ∈ J,
        vec3EuclideanNorm (a n i t - b i t) ≤ ε := by
    have h := eventually_uniform_vec3_ball_averages hJI (hB i)
      (hBfinite i) u χ (hχone i) hmem V huniform ε hε
    filter_upwards [h] with n hn t ht
    simpa only [a, b, c, ψ, dite_eq_left ht] using hn t ht
  have haMeas (n : ℕ) (i : ι) :
      AEMeasurable (a n i) (volume.restrict J) := by
    apply AEMeasurable.of_eval
    intro j
    have hu : AEStronglyMeasurable (fun z : Vec3 × ℝ => u n z)
        ((volume.restrict (B i)).prod (volume.restrict J)) :=
      (huMeas n).aestronglyMeasurable
    exact (CKN.Core.Step4.origin_velocity_average_aestronglyMeasurable
      hu j).aemeasurable
  have hbMeas (i : ι) : AEMeasurable (b i) (volume.restrict J) := by
    apply AEMeasurable.of_eval
    intro j
    apply aemeasurable_restrict_of_measurable_subtype hJ
    have hcont : Continuous
        (fun t : J => c i * inner ℝ (V ⟨t.1, hJI t.property⟩) (ψ i j)) :=
      ((hVcont (ψ i j)).comp (continuous_inclusion hJI)).const_mul _
    have heq : (fun t : J => b i t.1 j) =
        (fun t : J => c i * inner ℝ (V ⟨t.1, hJI t.property⟩) (ψ i j)) := by
      funext t
      simp [b, t.property]
    rw [heq]
    exact hcont.measurable
  have hVnorm (t : ℝ) (ht : t ∈ J) : ‖V ⟨t, hJI ht⟩‖ ≤ C := by
    exact norm_le_of_weak_tendsto_of_uniform_bound hC
      (fun n => hbound n t ht) (hweak ⟨t, hJI ht⟩)
  let D : ι → ℝ := fun i => c i * C * ∑ j : Fin 3, ‖ψ i j‖
  have haBound (n : ℕ) (i : ι) (t : ℝ) (ht : t ∈ J) :
      vec3EuclideanNorm (a n i t) ≤ D i := by
    have hAvg (j : Fin 3) : a n i t j =
        c i * inner ℝ ((hmem n ⟨t, hJI ht⟩).toLp
          (fun y => χ y • WithLp.toLp 2 (u n (y, t)))) (ψ i j) := by
      simpa only [a, c, ψ] using
        average_vec3_component_eq_cutoff_pairing (hB i) (hBfinite i)
          (fun y => u n (y, t)) χ (hχone i)
          (hmem n ⟨t, hJI ht⟩) j
    have heq : a n i t = fun j => c i * inner ℝ
        ((hmem n ⟨t, hJI ht⟩).toLp
          (fun y => χ y • WithLp.toLp 2 (u n (y, t)))) (ψ i j) :=
      funext hAvg
    rw [heq]
    exact vec3_norm_pairings_le _ (ψ i) (c i) C (hc i) (hbound n t ht)
  have hbBound (i : ι) (t : ℝ) (ht : t ∈ J) :
      vec3EuclideanNorm (b i t) ≤ D i := by
    have heq : b i t = fun j => c i * inner ℝ (V ⟨t, hJI ht⟩) (ψ i j) := by
      simp [b, ht]
    rw [heq]
    exact vec3_norm_pairings_le _ (ψ i) (c i) C (hc i) (hVnorm t ht)
  have hP (n : ℕ) : MemLp
      (fun z : Vec3 × ℝ => WithLp.toLp 2 (∑ i, φ i z.1 • a n i z.2)) 2
      ((volume.restrict K).prod (volume.restrict J)) :=
    memLp_two_finite_rank_of_bounded_coefficients hK hJ φ hφ hφbound
      (a n) (haMeas n) D (haBound n)
  have hQ : MemLp
      (fun z : Vec3 × ℝ => WithLp.toLp 2 (∑ i, φ i z.1 • b i z.2)) 2
      ((volume.restrict K).prod (volume.restrict J)) :=
    memLp_two_finite_rank_of_bounded_coefficients hK hJ φ hφ hφbound
      b hbMeas D hbBound
  have hφ' : ∀ i x, |φ i x| ≤ 1 := hφbound
  have hconv := tendsto_toLp_finite_rank_of_uniform_coefficients
    hK hJ φ hφ' a b hcoef hP hQ
  exact ⟨hP, _, hQ, hconv⟩

end CKN.Leray
