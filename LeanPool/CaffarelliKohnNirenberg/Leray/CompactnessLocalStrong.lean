/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessFiniteRank
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLp
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Compactness Local Strong

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Bounded measurable time coefficients yield an `L²` finite-rank field on
a finite space-time rectangle. -/
theorem memLp_two_finite_rank_of_bounded_coefficients
    {ι : Type*} [Fintype ι] {K : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict K)] [IsFiniteMeasure (volume.restrict J)]
    (hK : MeasurableSet K) (hJ : MeasurableSet J)
    (φ : ι → Vec3 → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφbound : ∀ i x, |φ i x| ≤ 1)
    (a : ι → ℝ → Vec3)
    (haMeas : ∀ i, AEMeasurable (a i) (volume.restrict J))
    (C : ι → ℝ)
    (haBound : ∀ i t, t ∈ J → vec3EuclideanNorm (a i t) ≤ C i) :
    MemLp (fun z : Vec3 × ℝ => WithLp.toLp 2
      (∑ i, φ i z.1 • a i z.2)) 2
      ((volume.restrict K).prod (volume.restrict J)) := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict K).prod (volume.restrict J)
  have hμfinite : IsFiniteMeasure μ := inferInstance
  have hsumMeas : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => ∑ i, φ i z.1 • a i z.2) μ := by
    have hsum := Finset.aestronglyMeasurable_sum Finset.univ
      (fun i (_hi : i ∈ Finset.univ) => by
        have hfirst : AEStronglyMeasurable
            (fun z : Vec3 × ℝ => φ i z.1) μ :=
          ((hφ i).aestronglyMeasurable).comp_fst
        have hsecond : AEStronglyMeasurable
            (fun z : Vec3 × ℝ => a i z.2) μ :=
          (haMeas i).aestronglyMeasurable.comp_snd
        exact hfirst.smul hsecond)
    have heq :
        (∑ i : ι, (fun z : Vec3 × ℝ => φ i z.1) •
          (fun z : Vec3 × ℝ => a i z.2)) =
          (fun z : Vec3 × ℝ => ∑ i : ι, φ i z.1 • a i z.2) := by
      funext z
      simp only [Finset.sum_apply]
      congr 1
    rw [heq] at hsum
    exact hsum
  have hfieldMeas : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => WithLp.toLp 2
        (∑ i, φ i z.1 • a i z.2)) μ :=
    ((WithLp.measurable_toLp (p := (2 : ℝ≥0∞)) (X := Vec3)).comp_aemeasurable
      hsumMeas.aemeasurable).aestronglyMeasurable
  have hμeq : μ = (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ J) := by
    dsimp [μ]
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hbound : ∀ᵐ z ∂μ, ‖WithLp.toLp 2
      (∑ i, φ i z.1 • a i z.2)‖ ≤ ∑ i, C i := by
    rw [hμeq]
    filter_upwards [ae_restrict_mem (hK.prod hJ)] with z hz
    have hnorm : ‖WithLp.toLp 2
        (∑ i, φ i z.1 • a i z.2)‖ ≤
        ∑ i, ‖φ i z.1 • WithLp.toLp 2 (a i z.2)‖ := by
      rw [WithLp.toLp_sum]
      simp only [WithLp.toLp_smul]
      exact norm_sum_le _ _
    exact hnorm.trans (Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs, ← vec3EuclideanNorm_eq_l2]
      calc
        |φ i z.1| * vec3EuclideanNorm (a i z.2) ≤
            1 * vec3EuclideanNorm (a i z.2) :=
          mul_le_mul_of_nonneg_right (hφbound i z.1)
            (vec3EuclideanNorm_nonneg _)
        _ ≤ C i := by simpa using haBound i z.2 hz.2)
  exact MemLp.of_bound hfieldMeas (∑ i, C i) hbound

private theorem eLpNorm_two_rpow_eq_lintegral
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (2 : ℝ≥0∞) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  have h : eLpNorm f (2 : ℝ≥0∞) μ ^ (2 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
    convert (eLpNorm_nnreal_pow_eq_lintegral
      (p := (2 : NNReal)) (by norm_num : (2 : NNReal) ≠ 0) hf) using 1 <;> norm_num
  exact h

/-- The space-time squared-integral error controls distance in `L²`. -/
theorem l2_distance_le_of_lintegral_sq_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {f g : α → E} {δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hδ : 0 ≤ δ)
    (herror : ∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal δ ^ (2 : ℕ)) :
    dist (hf.toLp f) (hg.toLp g) ≤ δ := by
  have hfg : MemLp (f - g) 2 μ := hf.sub hg
  have hLpEq : hf.toLp f - hg.toLp g = hfg.toLp (f - g) :=
    (hf.toLp_sub hg).symm
  have hnormSq : ‖hfg.toLp (f - g)‖ ^ 2 =
      (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal := by
    rw [Lp.norm_toLp]
    calc
      (eLpNorm (f - g) 2 μ).toReal ^ 2 =
          (eLpNorm (f - g) 2 μ).toReal ^ (2 : ℝ) := by
        exact (Real.rpow_natCast _ _).symm
      _ = (eLpNorm (f - g) 2 μ ^ (2 : ℝ)).toReal := by
        exact ENNReal.toReal_rpow _ _
      _ = (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal := by
        rw [eLpNorm_two_rpow_eq_lintegral hfg.aestronglyMeasurable]
        simp only [Pi.sub_apply]
  have hreal :
      (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal ≤ δ ^ 2 := by
    calc
      (∫⁻ x, ‖f x - g x‖ₑ ^ (2 : ℝ) ∂μ).toReal ≤
          (ENNReal.ofReal δ ^ (2 : ℕ)).toReal :=
        ENNReal.toReal_mono (by simp) herror
      _ = δ ^ 2 := by simp [ENNReal.toReal_pow, hδ]
  rw [dist_eq_norm_sub, hLpEq]
  nlinarith only [hnormSq, hreal, norm_nonneg (hfg.toLp (f - g)), hδ]

/-- Convergence of the squared-integral errors gives strong convergence in
`L²` on a finite-measure region. -/
theorem tendsto_toLp_of_tendsto_lintegral_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (herror : Tendsto
      (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (nhds (hg.toLp g)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let η : ℝ≥0∞ := ENNReal.ofReal (δ ^ 2)
  have hη : 0 < η := by
    dsimp [η]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hsmall : ∀ᶠ n in atTop,
      ∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂μ ≤ η :=
    (ENNReal.tendsto_nhds_zero.mp herror) η hη
  filter_upwards [hsmall] with n hn
  have hpow : eLpNorm (f n - g) 2 μ ^ (2 : ℝ) ≤
      ENNReal.ofReal δ ^ (2 : ℝ) := by
    calc
      eLpNorm (f n - g) 2 μ ^ (2 : ℝ) =
          ∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂μ := by
        rw [eLpNorm_two_rpow_eq_lintegral (MemLp.sub (hf n) hg).aestronglyMeasurable]
        simp only [Pi.sub_apply]
      _ ≤ η := hn
      _ = ENNReal.ofReal δ ^ (2 : ℝ) := by
        dsimp [η]
        rw [ENNReal.ofReal_rpow_of_nonneg hδ.le (by norm_num)]
        simp
  have hroot : eLpNorm (f n - g) 2 μ ≤ ENNReal.ofReal δ :=
    (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hpow
  have hdist : dist ((hf n).toLp (f n)) (hg.toLp g) ≤ δ := by
    rw [Lp.dist_def]
    have hae :
        (((hf n).toLp (f n) : Lp E 2 μ) : α → E) -
          (((hg.toLp g : Lp E 2 μ) : α → E)) =ᵐ[μ] f n - g :=
      (hf n).coeFn_toLp.sub hg.coeFn_toLp
    rw [eLpNorm_congr_ae hae]
    calc
      (eLpNorm (f n - g) 2 μ).toReal ≤ (ENNReal.ofReal δ).toReal :=
        ENNReal.toReal_mono (by simp) hroot
      _ = δ := ENNReal.toReal_ofReal hδ.le
  have hstrict : δ < ε := by dsimp [δ]; linarith only [hε]
  exact hdist.trans_lt hstrict

/-- Uniformly accurate finite-rank approximations that converge at each fixed
rank make the original `L²` sequence converge. -/
theorem exists_strong_l2_limit_of_lintegral_approximations
    {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
    [NormedAddCommGroup E] [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure α} [IsFiniteMeasure μ]
    (f : ℕ → α → E) (hf : ∀ n, MemLp (f n) 2 μ)
    (P : ℕ → ℕ → α → E) (hPmem : ∀ m n, MemLp (P m n) 2 μ)
    (hP : ∀ m, ∃ g : Lp E 2 μ,
      Tendsto (fun n => (hPmem m n).toLp (P m n)) atTop (nhds g))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ m, ∀ n,
      ∫⁻ x, ‖f n x - P m n x‖ₑ ^ (2 : ℝ) ∂μ ≤
        ENNReal.ofReal ε ^ (2 : ℕ)) :
    ∃ g : Lp E 2 μ,
      Tendsto (fun n => (hf n).toLp (f n)) atTop (nhds g) := by
  have hdist : ∀ ε : ℝ, 0 < ε → ∃ m, ∀ n,
      dist ((hf n).toLp (f n)) ((hPmem m n).toLp (P m n)) < ε := by
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨m, hm⟩ := happrox δ hδ
    refine ⟨m, fun n => ?_⟩
    have hle := l2_distance_le_of_lintegral_sq_le (hf n) (hPmem m n)
      hδ.le (hm n)
    have hstrict : δ < ε := by dsimp [δ]; linarith only [hε]
    exact hle.trans_lt hstrict
  have hCauchy : ∀ m, CauchySeq
      (fun n => (hPmem m n).toLp (P m n)) := by
    intro m
    obtain ⟨g, hg⟩ := hP m
    exact hg.cauchySeq
  obtain ⟨g, hg⟩ := exists_limit_of_cauchy_uniform_approximations
    (fun n => (hf n).toLp (f n))
    (fun m n => (hPmem m n).toLp (P m n)) hCauchy hdist
  exact ⟨g, hg⟩

/-- Uniform convergence of finitely many time coefficients implies convergence
of the corresponding finite-rank fields in space-time squared integral. -/
theorem tendsto_lintegral_prod_sq_finite_rank_of_uniform_coefficients
    {ι : Type*} [Fintype ι] {K : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict K)] [IsFiniteMeasure (volume.restrict J)]
    (hK : MeasurableSet K) (hJ : MeasurableSet J)
    (φ : ι → Vec3 → ℝ) (hφ : ∀ i x, |φ i x| ≤ 1)
    (a : ℕ → ι → ℝ → Vec3) (b : ι → ℝ → Vec3)
    (hcoef : ∀ i ε, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ∈ J, vec3EuclideanNorm (a n i t - b i t) ≤ ε) :
    Tendsto
      (fun n => ∫⁻ z : Vec3 × ℝ,
        ‖WithLp.toLp 2 ((∑ i, φ i z.1 • a n i z.2) -
          (∑ i, φ i z.1 • b i z.2))‖ₑ ^ (2 : ℝ)
          ∂((volume.restrict K).prod (volume.restrict J))) atTop (nhds 0) := by
  classical
  let f : ℕ → Vec3 × ℝ → L2Vec3 := fun n z =>
    WithLp.toLp 2 (if z.2 ∈ J then ∑ i, φ i z.1 • a n i z.2 else 0)
  let g : Vec3 × ℝ → L2Vec3 := fun z =>
    WithLp.toLp 2 (if z.2 ∈ J then ∑ i, φ i z.1 • b i z.2 else 0)
  have hcoef' : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i t, t ∈ J → vec3EuclideanNorm (a n i t - b i t) ≤ ε := by
    intro ε hε
    have hevents : ∀ i, ∀ᶠ n in atTop,
        ∀ t, t ∈ J → vec3EuclideanNorm (a n i t - b i t) ≤ ε :=
      fun i => hcoef i ε hε
    have hevent : ∀ᶠ n in atTop, ∀ i t, t ∈ J →
        vec3EuclideanNorm (a n i t - b i t) ≤ ε := by
      rw [Filter.eventually_all]
      exact hevents
    exact hevent
  have hconv : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop,
      ∀ z, ‖f n z - g z‖ₑ ≤ ε := by
    intro ε hε
    by_cases htop : ε = ⊤
    · simp [htop]
    have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    let q : ℝ := (Fintype.card ι : ℝ)
    let η : ℝ := ε.toReal / (q + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hsmall : q * η ≤ ε.toReal := by
      calc
        q * η = ε.toReal * (q / (q + 1)) := by dsimp [η]; ring
        _ ≤ ε.toReal * 1 := by
          apply mul_le_mul_of_nonneg_left
          · apply (div_le_iff₀ (by positivity)).2
            nlinarith only [hq]
          · exact hεreal.le
        _ = ε.toReal := by ring
    have hevent : ∀ᶠ n in atTop, ∀ i t, t ∈ J →
        vec3EuclideanNorm (a n i t - b i t) ≤ η := hcoef' η hη
    filter_upwards [hevent] with n hn z
    by_cases hJz : z.2 ∈ J
    · have hsumEq : (∑ i, φ i z.1 • a n i z.2) -
          (∑ i, φ i z.1 • b i z.2) =
          ∑ i, φ i z.1 • (a n i z.2 - b i z.2) := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        ext i
        rw [smul_sub]
      have hsumNorm : ∀ s : Finset ι,
          vec3EuclideanNorm (∑ i ∈ s, φ i z.1 • (a n i z.2 - b i z.2)) ≤
            ∑ i ∈ s, vec3EuclideanNorm (φ i z.1 • (a n i z.2 - b i z.2)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [vec3EuclideanNorm]
        | @insert i s hi ih =>
            simp only [Finset.sum_insert hi]
            exact (vec3EuclideanNorm_add_le _ _).trans
              (add_le_add le_rfl ih)
      have hsum : vec3EuclideanNorm
          ((∑ i, φ i z.1 • a n i z.2) - (∑ i, φ i z.1 • b i z.2)) ≤
          q * η := by
        rw [hsumEq]
        calc
          vec3EuclideanNorm (∑ i, φ i z.1 • (a n i z.2 - b i z.2)) ≤
              ∑ i, vec3EuclideanNorm (φ i z.1 • (a n i z.2 - b i z.2)) := by
            simpa using hsumNorm Finset.univ
          _ ≤ ∑ i, η := by
            apply Finset.sum_le_sum
            intro i hi
            rw [vec3EuclideanNorm_smul]
            calc
              |φ i z.1| * vec3EuclideanNorm (a n i z.2 - b i z.2) ≤ 1 * η :=
                mul_le_mul (hφ i z.1) (hn i z.2 hJz)
                  (by rw [vec3EuclideanNorm_eq_l2]; exact norm_nonneg _)
                  (by norm_num)
              _ = η := one_mul _
          _ = q * η := by simp [q]
      have hreal : vec3EuclideanNorm
          ((∑ i, φ i z.1 • a n i z.2) - (∑ i, φ i z.1 • b i z.2)) ≤ ε.toReal :=
        hsum.trans hsmall
      have hnorm : ‖f n z - g z‖ₑ =
          ENNReal.ofReal (vec3EuclideanNorm
            ((∑ i, φ i z.1 • a n i z.2) - (∑ i, φ i z.1 • b i z.2))) := by
        simp only [f, g, ite_eq_left hJz, WithLp.toLp_sub, ofReal_norm,
          vec3EuclideanNorm_eq_l2]
      rw [hnorm]
      calc
        ENNReal.ofReal (vec3EuclideanNorm
          ((∑ i, φ i z.1 • a n i z.2) - (∑ i, φ i z.1 • b i z.2))) ≤
            ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hreal
        _ = ε := ENNReal.ofReal_toReal htop
    · simp [f, g, hJz]
  have hmasked := tendsto_lintegral_prod_sq_of_uniform
    (μ := volume.restrict K) (ν := volume.restrict J) hconv
  have hJprod : ∀ᵐ z ∂((volume.restrict K).prod (volume.restrict J)), z.2 ∈ J := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hK.prod hJ)] with z hz
    exact hz.2
  have hEq (n : ℕ) :
      (∫⁻ z : Vec3 × ℝ, ‖f n z - g z‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict K).prod (volume.restrict J))) =
      (∫⁻ z : Vec3 × ℝ,
        ‖WithLp.toLp 2 ((∑ i, φ i z.1 • a n i z.2) -
          (∑ i, φ i z.1 • b i z.2))‖ₑ ^ (2 : ℝ)
          ∂((volume.restrict K).prod (volume.restrict J))) := by
    apply lintegral_congr_ae
    filter_upwards [hJprod] with z hz
    simp only [f, g, ite_eq_left hz, WithLp.toLp_sub]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hsmall' : ∀ᶠ n in atTop,
      ∫⁻ z : Vec3 × ℝ, ‖f n z - g z‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict K).prod (volume.restrict J)) ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hmasked) ε hε
  filter_upwards [hsmall'] with n hn
  rw [← hEq n]
  exact hn

/-- Finite-rank fields with uniformly convergent time coefficients converge
strongly in `L²` on a finite space-time rectangle. -/
theorem tendsto_toLp_finite_rank_of_uniform_coefficients
    {ι : Type*} [Fintype ι] {K : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict K)] [IsFiniteMeasure (volume.restrict J)]
    (hK : MeasurableSet K) (hJ : MeasurableSet J)
    (φ : ι → Vec3 → ℝ) (hφ : ∀ i x, |φ i x| ≤ 1)
    (a : ℕ → ι → ℝ → Vec3) (b : ι → ℝ → Vec3)
    (hcoef : ∀ i ε, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ∈ J, vec3EuclideanNorm (a n i t - b i t) ≤ ε)
    (hf : ∀ n, MemLp
      (fun z : Vec3 × ℝ => WithLp.toLp 2
        (∑ i, φ i z.1 • a n i z.2)) 2
      ((volume.restrict K).prod (volume.restrict J)))
    (hg : MemLp
      (fun z : Vec3 × ℝ => WithLp.toLp 2
        (∑ i, φ i z.1 • b i z.2)) 2
      ((volume.restrict K).prod (volume.restrict J))) :
    Tendsto
      (fun n => (hf n).toLp (fun z : Vec3 × ℝ => WithLp.toLp 2
        (∑ i, φ i z.1 • a n i z.2))) atTop
      (nhds (hg.toLp (fun z : Vec3 × ℝ => WithLp.toLp 2
        (∑ i, φ i z.1 • b i z.2)))) := by
  let f : ℕ → Vec3 × ℝ → L2Vec3 := fun n z =>
    WithLp.toLp 2 (∑ i, φ i z.1 • a n i z.2)
  let g : Vec3 × ℝ → L2Vec3 := fun z =>
    WithLp.toLp 2 (∑ i, φ i z.1 • b i z.2)
  have hsq := tendsto_lintegral_prod_sq_finite_rank_of_uniform_coefficients
    hK hJ φ hφ a b hcoef
  have hident (n : ℕ) :
      (∫⁻ z : Vec3 × ℝ, ‖f n z - g z‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict K).prod (volume.restrict J))) =
      (∫⁻ z : Vec3 × ℝ,
        ‖WithLp.toLp 2 ((∑ i, φ i z.1 • a n i z.2) -
          (∑ i, φ i z.1 • b i z.2))‖ₑ ^ (2 : ℝ)
          ∂((volume.restrict K).prod (volume.restrict J))) := by
    apply lintegral_congr
    intro z
    simp only [f, g, WithLp.toLp_sub]
  have herror : Tendsto
      (fun n => ∫⁻ z : Vec3 × ℝ, ‖f n z - g z‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict K).prod (volume.restrict J))) atTop (nhds 0) := by
    have heq :
        (fun n => ∫⁻ z : Vec3 × ℝ, ‖f n z - g z‖ₑ ^ (2 : ℝ)
          ∂((volume.restrict K).prod (volume.restrict J))) =
        (fun n => ∫⁻ z : Vec3 × ℝ,
          ‖WithLp.toLp 2 ((∑ i, φ i z.1 • a n i z.2) -
            (∑ i, φ i z.1 • b i z.2))‖ₑ ^ (2 : ℝ)
            ∂((volume.restrict K).prod (volume.restrict J))) := by
      funext n
      exact hident n
    rw [heq]
    exact hsq
  exact tendsto_toLp_of_tendsto_lintegral_sq hf hg herror

end CKN.Leray
