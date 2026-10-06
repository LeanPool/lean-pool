/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessApproximation
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessFixedRank

/-!
# Compactness Strong Field

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

namespace CKN.Leray

/-- A uniform spatial slice bound puts the field in space-time `L²` on a
smaller spatial rectangle. -/
theorem memLp_two_vec3_on_rectangle_of_slice_bound
    {K Kc : Set Vec3} {J : Set ℝ}
    (hKKc : K ⊆ Kc) (hJ : MeasurableSet J)
    [IsFiniteMeasure (volume.restrict J)]
    (u : (Vec3 × ℝ) → Vec3) (hu : Measurable u)
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hbound : ∀ t ∈ J, (∫⁻ x in Kc,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (2 : ℝ)
      ∂volume) ≤ M) :
    MemLp (fun z : Vec3 × ℝ => (WithLp.toLp 2 (u z) : L2Vec3)) 2
      ((volume.restrict K).prod (volume.restrict J)) := by
  let F : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ)
  have hF : Measurable F := by
    have hnorm : Measurable (fun z : ParabolicPoint =>
        vec3EuclideanNorm (u z)) := by
      unfold vec3EuclideanNorm
      fun_prop
    fun_prop
  have hfiniteC : (∫⁻ t in J, ∫⁻ x in Kc, F (x, t) ∂volume ∂volume) < ⊤ :=
    finite_lintegral_prod_of_uniform_slice_bound F hF hJ M hM hbound
  have hfiniteK : (∫⁻ t in J, ∫⁻ x in K, F (x, t) ∂volume ∂volume) < ⊤ := by
    apply lt_of_le_of_lt ?_ hfiniteC
    apply lintegral_mono
    intro t
    exact lintegral_mono_set hKKc
  have hμeq : (volume.restrict K).prod (volume.restrict J) =
      (volume : Measure ParabolicPoint).restrict (K ×ˢ J) := by
    change (volume.restrict K).prod (volume.restrict J) =
      ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (K ×ˢ J)
    rw [Measure.prod_restrict]
  have hfinite : (∫⁻ z : Vec3 × ℝ, F z
      ∂((volume.restrict K).prod (volume.restrict J))) < ⊤ := by
    rw [hμeq]
    change (∫⁻ z in K ×ˢ J, F z ∂(volume : Measure ParabolicPoint)) < ⊤
    rw [lintegral_parabolic_rectangle_eq_iterated F hF]
    exact hfiniteK
  exact CKN.Foundation.memLp_two_vec3_of_lintegral_sq_lt_top
    ((volume.restrict K).prod (volume.restrict J)) u hu hfinite

/-- Squared `L²` distance on a restricted product is the squared Euclidean
field error on the corresponding space-time rectangle. -/
theorem lintegral_withLp_vec3_error_eq_rectangle
    {K : Set Vec3} {J : Set ℝ}
    (u v : (Vec3 × ℝ) → Vec3) :
    (∫⁻ z : Vec3 × ℝ,
      ‖(WithLp.toLp 2 (u z) : L2Vec3) -
        (WithLp.toLp 2 (v z) : L2Vec3)‖ₑ ^ (2 : ℝ)
      ∂((volume.restrict K).prod (volume.restrict J))) =
    (∫⁻ z in K ×ˢ J,
      ENNReal.ofReal (vec3EuclideanNorm (u z - v z) ^ 2)
      ∂(volume : Measure ParabolicPoint)) := by
  change (∫⁻ z : Vec3 × ℝ,
      ‖(WithLp.toLp 2 (u z) : L2Vec3) -
        (WithLp.toLp 2 (v z) : L2Vec3)‖ₑ ^ (2 : ℝ)
      ∂((volume.restrict K).prod (volume.restrict J))) =
    (∫⁻ z in K ×ˢ J,
      ENNReal.ofReal (vec3EuclideanNorm (u z - v z) ^ 2)
      ∂((volume : Measure Vec3).prod (volume : Measure ℝ)))
  rw [← Measure.prod_restrict K J]
  apply lintegral_congr
  intro z
  rw [← WithLp.toLp_sub, ← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
  calc
    ENNReal.ofReal (vec3EuclideanNorm (u z - v z)) ^ (2 : ℝ) =
        ENNReal.ofReal (vec3EuclideanNorm (u z - v z)) ^ (2 : ℕ) :=
      ENNReal.rpow_natCast _ 2
    _ = _ :=
      (ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg (u z - v z)) 2).symm

/-- The ball-average error and fixed-rank convergence give strong `L²`
convergence on one compact space-time rectangle. -/
theorem exists_strong_l2_limit_on_compact_rectangle
    {K W Kc : Set Vec3} {I J : Set ℝ}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hWKc : W ⊆ Kc) (hJ : IsCompact J) (hJI : J ⊆ I)
    [IsFiniteMeasure (volume.restrict K)]
    [IsFiniteMeasure (volume.restrict J)]
    (u : ℕ → (Vec3 × ℝ) → Vec3)
    (Du : ℕ → (Vec3 × ℝ) → Fin 3 → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (hDuMeas : ∀ n, Measurable (Du n))
    (hweakW : ∀ n, ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn W (fun y => u n (y, t) i)
        (fun y => Du n (y, t) i))
    (M G : ℝ≥0∞) (hM : M < ⊤) (hG : G < ⊤)
    (huBound : ∀ n t, t ∈ J →
      (∫⁻ x in Kc, ENNReal.ofReal (vec3EuclideanNorm (u n (x, t))) ^
        (2 : ℝ) ∂volume) ≤ M)
    (hDuBound : ∀ n,
      (∫⁻ t in J, ∫⁻ x in Kc,
        ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x, t))
          ∂volume) ≤ G)
    (χ : Vec3 → ℝ) (hχone : ∀ x ∈ W, χ x = 1)
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
    (hcutBound : ∀ n t, (ht : t ∈ J) →
      ‖(hmem n ⟨t, hJI ht⟩).toLp
        (fun y => χ y • WithLp.toLp 2 (u n (y, t)))‖ ≤ C) :
    ∃ hf : ∀ n, MemLp (fun z : Vec3 × ℝ =>
      (WithLp.toLp 2 (u n z) : L2Vec3)) 2
      ((volume.restrict K).prod (volume.restrict J)),
      ∃ g : Lp L2Vec3 2 ((volume.restrict K).prod (volume.restrict J)),
        Tendsto (fun n => (hf n).toLp
          (fun z => (WithLp.toLp 2 (u n z) : L2Vec3))) atTop (nhds g) := by
  classical
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict K).prod (volume.restrict J)
  let f : ℕ → (Vec3 × ℝ) → L2Vec3 := fun n z => WithLp.toLp 2 (u n z)
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hJmeas : MeasurableSet J := hJ.measurableSet
  let : IsFiniteMeasure (volume.restrict J) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hJ.measure_lt_top⟩
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  let : IsFiniteMeasure μ := by
    change IsFiniteMeasure ((volume.restrict K).prod (volume.restrict J))
    infer_instance
  have hf (n : ℕ) : MemLp (f n) 2 μ :=
    memLp_two_vec3_on_rectangle_of_slice_bound
      (hKW.trans hWKc) hJmeas (u n) (huMeas n) M hM (huBound n)
  let η : ℕ → ℝ≥0∞ := fun m =>
    ENNReal.ofReal (1 / (m + 1) : ℝ) ^ (2 : ℕ)
  have hscale (m : ℕ) :
      ∃ P : ℕ → (Vec3 × ℝ) → L2Vec3,
        ∃ hP : ∀ n, MemLp (P n) 2 μ,
        ∃ g : Lp L2Vec3 2 μ,
          Tendsto (fun n => (hP n).toLp (P n)) atTop (nhds g) ∧
          ∀ n, (∫⁻ z, ‖f n z - P n z‖ₑ ^ (2 : ℝ) ∂μ) ≤ η m := by
    have hη : 0 < η m := by
      dsimp [η]
      rw [← ENNReal.rpow_natCast]
      exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity))
        ENNReal.ofReal_ne_top
    obtain ⟨r, N, s, t, φ, hφ, hweight, hball, herror⟩ :=
      exists_finite_rank_average_approximation_of_mixed_bounds
        hK hW hKW hWKc hJmeas u Du huMeas hDuMeas hweakW
        M G hM hG huBound hDuBound (η m) hη
    let ι := {p : Σ i : Fin N,
      {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t}
    let B : ι → Set Vec3 := fun p =>
      CKN.euclideanBall p.1.2.1.1 (1 / (r + 1))
    have hr : 0 < (1 / (r + 1) : ℝ) := by positivity
    have hB (p : ι) : MeasurableSet (B p) :=
      (CKN.isOpen_euclideanBall p.1.2.1.1 (1 / (r + 1))).measurableSet
    have hBfinite (p : ι) : volume (B p) < ⊤ :=
      CKN.volume_euclideanBall_lt_top p.1.2.1.1 hr
    have hχoneB (p : ι) (x : Vec3) (hx : x ∈ B p) : χ x = 1 :=
      hχone x (hball p hx)
    have hφbound (p : ι) (x : Vec3) : |φ p x| ≤ 1 := by
      have hx := hweight p x
      rw [abs_of_nonneg hx.1]
      exact hx.2
    obtain ⟨hP, Q, hQ, hconv⟩ :=
      tendsto_finite_rank_ball_average_approximation hJI hKmeas hJmeas
        B hB hBfinite u huMeas χ hχoneB hmem V hweak hVcont
        huniform C hC hcutBound φ hφ hφbound
    let P : ℕ → (Vec3 × ℝ) → L2Vec3 := fun n z =>
      (WithLp.toLp 2 (∑ p : ι, φ p z.1 •
        (fun j => average (volume.restrict (B p))
          (fun y => u n (y,z.2) j))) : L2Vec3)
    refine ⟨P, hP, hQ.toLp Q, ?_, ?_⟩
    · simpa only [P, B, μ, ParabolicPoint, L2Vec3, PiLp] using hconv
    · intro n
      have hraw := herror n
      have hbridge := lintegral_withLp_vec3_error_eq_rectangle
        (K := K) (J := J) (u n)
        (fun z => ∑ p : ι, φ p z.1 •
          (fun j => average (volume.restrict (B p))
            (fun y => u n (y,z.2) j)))
      dsimp [B] at hbridge
      simpa only [f, P, μ, ParabolicPoint, L2Vec3, PiLp] using
        hbridge.le.trans hraw
  choose P hP g hconv herror using hscale
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ m, ∀ n,
      (∫⁻ z, ‖f n z - P m n z‖ₑ ^ (2 : ℝ) ∂μ) ≤
        ENNReal.ofReal ε ^ (2 : ℕ) := by
    intro ε hε
    have hsmall : ∀ᶠ m : ℕ in atTop, (1 / (m + 1) : ℝ) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually
        (isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Iio ε from hε))
    obtain ⟨m, hm⟩ := hsmall.exists
    refine ⟨m, fun n => (herror m n).trans ?_⟩
    dsimp [η]
    gcongr
  obtain ⟨g', hg'⟩ := exists_strong_l2_limit_of_lintegral_approximations
    f hf P hP (fun m => ⟨g m, hconv m⟩) happrox
  exact ⟨hf, g', hg'⟩

end CKN.Leray
