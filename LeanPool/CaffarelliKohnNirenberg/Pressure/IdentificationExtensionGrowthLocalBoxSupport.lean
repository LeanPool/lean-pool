/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairing
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderForceTerms
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayPotentials
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpGrowth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Setting.UTensor

/-!
# Identification Extension Growth Local Box Support

Supporting estimates for the Navier–Stokes development.
-/

public section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN
open CKN.Foundation.Euclidean
/-- Extend local `L^(3/2)` membership to the whole space when the function's
topological support lies inside the finite-measure carrier. -/
theorem lift_ball_memLp_growth_sws {g : Vec3 → ℝ} {B : Set Vec3}
    [IsFiniteMeasure (volume.restrict B)]
    (hB : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B))
    (hBsupport : tsupport g ⊆ B) :
    MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hsupport : Function.support g ⊆ B :=
    (subset_tsupport (f := g)).trans hBsupport
  have hgint : Integrable g volume := decomposition_full_of_on_sws
    (hB.integrable (by norm_num)) hBsupport
  exact memLp_volume_of_memLp_restrict_of_support
    hgint.aestronglyMeasurable hsupport hB
/-- Compare the Euclidean norm on `Fin 3 → ℝ` with the coordinatewise
supremum norm. -/
theorem vec3_norm_le_sqrt_three_sws (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      _ ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) (by positivity)).mp hsq
/-- The Euclidean norm on `Vec3` satisfies the triangle inequality. -/
theorem vec3_norm_add_le_sws (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _
/-- A velocity slice with square-integrable weak gradient has its Euclidean
norm in `L^6` on each interior ball. -/
theorem velocity_norm_memLp_six_on_ball
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x₀ : Vec3} {ρ t : ℝ} {Ω' : Set Vec3}
    (hρ : 0 < ρ) (hball : vec3Ball x₀ ρ ⊆ Ω')
    (hts : MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω'))
    (hDu : MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω'))
    (hgrad : ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x : Vec3 => u (x, t) i)
        (fun x => Du (x, t) i)) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 6
      (volume.restrict (vec3Ball x₀ ρ)) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ)
  have hμtop : μ Set.univ < ∞ := by simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball x₀ ρ) < ∞)
    letI : IsFiniteMeasure μ := ⟨hμtop⟩
  have huB : MemLp (fun x : Vec3 => u (x, t)) 2 μ := by
    simpa [μ] using hts.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEMeasurable (fun x : Vec3 => u (x, t)) μ :=
    huB.aestronglyMeasurable.aemeasurable
  have humeasNorm : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) μ :=
    (continuous_vec3EuclideanNorm.measurable.comp_aemeasurable humeas).aestronglyMeasurable
  have hu2 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 μ := by
    apply huB.of_le_mul humeasNorm
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact vec3_norm_le_sqrt_three_sws (u (y, t))
  have hopen : IsOpen (euclideanBall x₀ ρ) := by
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < ρ ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hballEq : euclideanBall x₀ ρ = vec3Ball x₀ ρ := by
    ext x
    change (x ∈ euclideanBall x₀ ρ) ↔ vec3EuclideanNorm (x - x₀) < ρ
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ)
  have hballE : euclideanBall x₀ ρ ⊆ Ω' := by
    rw [hballEq]
    exact hball
  let hH1 : ∀ i : Fin 3, H1Function (euclideanBall x₀ ρ) := fun i =>
    { toFun := fun x => u (x, t) i
      grad := fun x => Du (x, t) i
      memL2 := (MemLp.eval hts i).mono_measure
        (Measure.restrict_mono_set volume hballE)
      gradMemL2 := fun j => (MemLp.eval (MemLp.eval hDu i) j).mono_measure
        (Measure.restrict_mono_set volume hballE)
      hasWeakGradient := (hgrad i).restrict hopen hballE }
  have hcomp : ∀ i : Fin 3, (hH1 i).toFun = fun x => u (x, t) i := by
    intro i
    simp [hH1]
  have hgrad' : ∀ i : Fin 3, (hH1 i).grad = fun x => Du (x, t) i := by
    intro i
    simp [hH1]
  have hbridge := vector_h1_sobolev_ball_integral hρ (fun x => u (x, t))
    (fun x i => Du (x, t) i) hH1 hcomp hgrad'
  have hW : MemLp (fun y : Vec3 => vec3EuclideanNorm (fun i : Fin 3 =>
      u (y, t) i - average μ (fun z => u (z, t) i))) 6 μ := by
    simpa [μ] using hbridge.1
  let cvec : Vec3 := fun j => average μ (fun z => u (z, t) j)
  let gw : Vec3 → ℝ := fun y => vec3EuclideanNorm (fun i : Fin 3 =>
    u (y, t) i - cvec i)
  let gu : Vec3 → ℝ := fun y => vec3EuclideanNorm (u (y, t))
  have hgw : MemLp gw 6 μ := by
    simpa [gw] using hW
  have hgu6 : MemLp gu 6 μ := by
    have hsum : MemLp (fun y => gw y + vec3EuclideanNorm cvec) 6 μ :=
      hgw.add (memLp_const _)
    apply hsum.of_le humeasNorm
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _),
      Real.norm_of_nonneg (add_nonneg (vec3EuclideanNorm_nonneg _)
        (vec3EuclideanNorm_nonneg _))]
    change vec3EuclideanNorm (u (y, t)) ≤
      vec3EuclideanNorm (fun i : Fin 3 => u (y, t) i - cvec i) +
        vec3EuclideanNorm cvec
    have hdecomp : u (y, t) = (fun i => u (y, t) i - cvec i) + cvec := by
      funext i
      dsimp [cvec]
      ring
    calc
      vec3EuclideanNorm (u (y, t)) = vec3EuclideanNorm
          ((fun i => u (y, t) i - cvec i) + cvec) := congrArg vec3EuclideanNorm hdecomp
      _ ≤ vec3EuclideanNorm (fun i => u (y, t) i - cvec i) +
          vec3EuclideanNorm cvec := vec3_norm_add_le_sws _ _
  exact hgu6
/-- Bound the Laplacian of the fixed mollified ball cutoff by its scale. -/
theorem cutoff_laplacian_bound_sws {η : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) (hη : η = mollifiedBallCutoff x₀ hρ) :
    ∀ y, |spatialLaplacian η y| ≤
      (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
  intro y
  rw [hη, spatialLaplacian]
  calc
    |∑ i : Fin 3, mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| ≤
        ∑ i : Fin 3, |mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
      gcongr with i hi
      exact pressure_cutoff_mixedSecond_bound x₀ hρ y i i
    _ = (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
/-- Transfer a spacetime `L^q` estimate on a local box to almost every
spatial slice of a sub-ball. -/
theorem memLp_slice_ae_of_localBox
    {Ω' B : Set Vec3} {J : Set ℝ} {q : ℝ}
    {E : Type} [NormedAddCommGroup E] {g : ParabolicPoint → E}
    (hq : 0 < q) (hB : B ⊆ Ω')
    (hgmeas : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet Ω' J)))
    (hg : MemLp g (ENNReal.ofReal q)
      (volume.restrict (spaceTimeSet Ω' J))) :
    ∀ᵐ s ∂volume.restrict J,
      MemLp (fun x : Vec3 => g (x, s)) (ENNReal.ofReal q)
        (volume.restrict B) := by
  have hprodMeas : AEStronglyMeasurable g
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hgmeas
  have hprodMem : MemLp g (ENNReal.ofReal q)
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hg
  have hBMeas : AEStronglyMeasurable g
      ((volume.restrict B).prod (volume.restrict J)) :=
    hprodMeas.mono_measure
      (Measure.prod_mono (Measure.restrict_mono_set volume hB)
        (Measure.restrict_mono_set volume subset_rfl))
  have hBMem : MemLp g (ENNReal.ofReal q)
      ((volume.restrict B).prod (volume.restrict J)) :=
    hprodMem.mono_measure
      (Measure.prod_mono (Measure.restrict_mono_set volume hB)
        (Measure.restrict_mono_set volume subset_rfl))
  have hpow := hBMem.integrable_norm_rpow
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
  have hpowSlice := hpow.prod_left_ae
  have hmeasSlice := hBMeas.prodMk_right
  filter_upwards [hpowSlice, hmeasSlice] with s hs hms
  have hs' : Integrable (fun x : Vec3 =>
      ‖g (x, s)‖ ^ (ENNReal.ofReal q).toReal)
      (volume.restrict B) := by
    simpa only [ENNReal.toReal_ofReal hq.le] using hs
  exact (integrable_norm_rpow_iff hms
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top).mp hs'

/-- Extend local `L^q` membership to the whole space for a function supported
inside the local carrier. -/
theorem memLp_volume_of_memLp_restrict_of_support_local
    {g : Vec3 → ℝ} {B : Set Vec3} {q : ℝ}
    (hgmeas : AEStronglyMeasurable g volume)
    (hsupport : Function.support g ⊆ B)
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict B)) :
    MemLp g (ENNReal.ofReal q) volume := by
  rw [memLp_iff] at hg ⊢
  rwa [eLpNorm_restrict_eq_of_support_subset hgmeas hsupport] at hg

/-- On almost every time slice of a local box, the localized force terms have
global `L^(3/2)` membership and linear growth. -/
theorem pressure_force_growth_ae_of_localBox
    {Ω : Set Vec3} {T : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω T q u Du p f)
    {Ω' : Set Vec3} {Jt : Set ℝ}
    (hbox : localBox Ω T Ω' Jt)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : vec3Ball x₀ ρ ⊆ Ω') :
    ∀ᵐ s ∂volume.restrict Jt,
      (∀ R : ℝ, 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
          pressureP8 (mollifiedBallCutoff x₀ hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      0 ≤ pressureP7GrowthConstant (mollifiedBallCutoff x₀ hρ) f s
          (vec3EuclideanNorm x₀ + ρ) +
        pressureP8GrowthConstant (mollifiedBallCutoff x₀ hρ) f s
          (vec3EuclideanNorm x₀ + ρ) ∧
      ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
          pressureP8 (mollifiedBallCutoff x₀ hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤
        (pressureP7GrowthConstant (mollifiedBallCutoff x₀ hρ) f s
            (vec3EuclideanNorm x₀ + ρ) +
          pressureP8GrowthConstant (mollifiedBallCutoff x₀ hρ) f s
            (vec3EuclideanNorm x₀ + ρ)) * (1 + R) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff x₀ hρ
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by simpa [η] using mollifiedBallCutoff_smooth x₀ hρ
  have hηmeas : AEStronglyMeasurable η volume := hηsmooth.continuous.aestronglyMeasurable
  have hηsupport : tsupport η ⊆ vec3Ball x₀ ρ := by
    simpa [η] using pressure_cutoff_support_subset_ball x₀ hρ
  have hηbound : ∀ y, |η y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x₀ hρ y)]
    exact mollifiedBallCutoff_le_one x₀ hρ y
  have hηderiv : ∀ j y, |spatialDeriv η j y| ≤ cutoffGradientConstant / ρ := by
    intro j y
    simpa [η] using pressure_cutoff_spatialDeriv_bound x₀ hρ y j
  obtain ⟨_, _, _, hfmeas, _, _, _, hfmem, _⟩ :=
    hsol.2.2.2.2.2.1 Ω' Jt hbox
  have hfs := memLp_slice_ae_of_localBox (q := q)
    (by linarith only [hsol.2.2.2.1]) hball hfmeas hfmem
  let R₀ : ℝ := vec3EuclideanNorm x₀ + ρ
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith only [vec3EuclideanNorm_nonneg x₀, hρ]
  have hball₀ : vec3Ball x₀ ρ ⊆ closedBall (0 : Vec3) R₀ := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    have hy' : vec3EuclideanNorm (y - x₀) < ρ := (mem_vec3Ball).1 hy
    have htri : vec3EuclideanNorm y ≤
        vec3EuclideanNorm (y - x₀) + vec3EuclideanNorm x₀ := by
      calc
        vec3EuclideanNorm y = vec3EuclideanNorm ((y - x₀) + x₀) := by congr 1; abel
        _ ≤ vec3EuclideanNorm (y - x₀) + vec3EuclideanNorm x₀ :=
          vec3_norm_add_le_sws _ _
    have hyNorm : ‖y‖ ≤ vec3EuclideanNorm y := by
      rw [Pi.norm_def]
      have hnn : Finset.univ.sup (fun i => ‖y i‖₊) ≤
          ⟨vec3EuclideanNorm y, vec3EuclideanNorm_nonneg y⟩ := by
        apply Finset.sup_le
        intro i hi
        have hi' : |y i| ≤ vec3EuclideanNorm y := by
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using abs_apply_le_vecEuclideanNorm y i
        exact_mod_cast hi'
      exact_mod_cast hnn
    linarith only [hy', htri, hyNorm]
  filter_upwards [hfs] with s hF
  let B : Set Vec3 := vec3Ball x₀ ρ
  let μ : Measure Vec3 := volume.restrict B
  have hμtop : μ Set.univ < ⊤ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      (by
        rw [volume_vec3Ball_eq]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top : volume (vec3Ball x₀ ρ) < ⊤)
    letI : IsFiniteMeasure μ := ⟨hμtop⟩
  have hq : 1 ≤ q := by linarith only [hsol.2.2.2.1]
  have hsource₇support (j : Fin 3) :
      tsupport (fun y : Vec3 => η y * f (y, s) j) ⊆ B :=
    (tsupport_mul_subset_left (f := η)
      (g := fun y : Vec3 => f (y, s) j)).trans hηsupport
  have hsource₈support (j : Fin 3) :
      tsupport (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) ⊆ B :=
    (tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := fun y : Vec3 => f (y, s) j)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport)
  have hsource₇ (j : Fin 3) :
      MemLp (fun y : Vec3 => η y * f (y, s) j)
        (ENNReal.ofReal q) (volume.restrict B) := by
    have hcomp : MemLp (fun y : Vec3 => f (y, s) j)
        (ENNReal.ofReal q) μ := by simpa [μ, B] using MemLp.eval hF j
    have hηmB : AEStronglyMeasurable η μ :=
      hηmeas.mono_measure Measure.restrict_le_self
    have hmeas := hηmB.mul hcomp.aestronglyMeasurable
    apply hcomp.of_le hmeas
    filter_upwards [] with y
    change |η y * f (y, s) j| ≤ |f (y, s) j|
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hηbound y)
      (abs_nonneg (f (y, s) j))
  have hsource₇global (j : Fin 3) :
      MemLp (fun y : Vec3 => η y * f (y, s) j) (ENNReal.ofReal q) volume := by
    have htsupport := hsource₇support j
    have hsupport : Function.support (fun y : Vec3 => η y * f (y, s) j) ⊆ B :=
      (subset_tsupport (f := fun y : Vec3 => η y * f (y, s) j)).trans htsupport
    have hintB : Integrable (fun y : Vec3 => η y * f (y, s) j) μ := by
      have hfint := (MemLp.eval hF j).integrable (ENNReal.one_le_ofReal.mpr hq)
      have hηmB : AEStronglyMeasurable η μ := hηmeas.mono_measure Measure.restrict_le_self
      have hm := hfint.mul_bdd hηmB
        (Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hηbound y))
      simpa only [μ, mul_comm] using hm
    have hgint := decomposition_full_of_on_sws hintB htsupport
    exact memLp_volume_of_memLp_restrict_of_support_local
      hgint.aestronglyMeasurable hsupport (hsource₇ j)
  have hsource₈ (j : Fin 3) :
      MemLp (fun y : Vec3 => spatialDeriv η j y * f (y, s) j)
        (ENNReal.ofReal q) (volume.restrict B) := by
    let K : ℝ := max (cutoffGradientConstant / ρ) 0
    have hK : 0 ≤ K := le_max_right _ _
    have hcomp : MemLp (fun y : Vec3 => f (y, s) j)
        (ENNReal.ofReal q) μ := by simpa [μ, B] using MemLp.eval hF j
    have hKm : MemLp (fun y : Vec3 => K * f (y, s) j)
        (ENNReal.ofReal q) μ := hcomp.const_mul K
    have hmeas : AEStronglyMeasurable
        (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) μ := by
      exact (contDiff_spatialDeriv_smooth hηsmooth j).continuous.aestronglyMeasurable
        |>.mono_measure Measure.restrict_le_self |>.mul hcomp.aestronglyMeasurable
    apply hKm.of_le hmeas
    filter_upwards [] with y
    change |spatialDeriv η j y * f (y, s) j| ≤ |K * f (y, s) j|
    rw [abs_mul, abs_mul, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_right
      (le_trans (hηderiv j y) (le_max_left _ _)) (abs_nonneg _)
  have hsource₈global (j : Fin 3) :
      MemLp (fun y : Vec3 => spatialDeriv η j y * f (y, s) j)
        (ENNReal.ofReal q) volume := by
    have htsupport := hsource₈support j
    have hsupport : Function.support
        (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) ⊆ B :=
      (subset_tsupport (f := fun y : Vec3 => spatialDeriv η j y * f (y, s) j)).trans
        htsupport
    have hμtop : μ Set.univ < ⊤ := by
      simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
        (by
          rw [volume_vec3Ball_eq]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top : volume (vec3Ball x₀ ρ) < ⊤)
      letI : IsFiniteMeasure μ := ⟨hμtop⟩
    have hηd : AEStronglyMeasurable (spatialDeriv η j) μ :=
      (contDiff_spatialDeriv_smooth hηsmooth j).continuous.aestronglyMeasurable
        |>.mono_measure Measure.restrict_le_self
    have hfint := (MemLp.eval hF j).integrable (ENNReal.one_le_ofReal.mpr hq)
    have hintB := hfint.mul_bdd hηd
      (Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hηderiv j y))
    have hintB' : Integrable
        (fun y : Vec3 => spatialDeriv η j y * f (y, s) j) μ := by
      simpa only [μ, mul_comm] using hintB
    have hgint := decomposition_full_of_on_sws hintB' htsupport
    exact memLp_volume_of_memLp_restrict_of_support_local
      hgint.aestronglyMeasurable hsupport (hsource₈ j)
  have hsupp₇ : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R₀ →
      η y * f (y, s) j = 0 := by
    intro j y hy
    have hyB : y ∉ B := fun hyB => hy (hball₀ hyB)
    have hzero : η y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB (hηsupport hηy))
    rw [hzero, zero_mul]
  have hsupp₈ : ∀ (j : Fin 3) (y : Vec3), y ∉ closedBall (0 : Vec3) R₀ →
      spatialDeriv η j y * f (y, s) j = 0 := by
    intro j y hy
    have hyB : y ∉ B := fun hyB => hy (hball₀ hyB)
    have hzero : spatialDeriv η j y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hηy => hyB
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupport hηy))
    rw [hzero, zero_mul]
  obtain ⟨hmem, hbound⟩ := pressureP7_add_pressureP8_memLp_and_lpNorm_growth
    hR₀ (by linarith only [hsol.2.2.2.1])
    hsource₇global hsupp₇ hsource₈global hsupp₈
  have hnonneg := pressureP7_add_pressureP8_growthConstant_nonneg η f s hR₀
  exact ⟨hmem, hnonneg, by simpa [R₀] using hbound⟩


end CKN
