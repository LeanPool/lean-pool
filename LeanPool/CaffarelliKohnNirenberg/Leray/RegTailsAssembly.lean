/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsSliceEstimates
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsTimeBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsTimeEnergyContract
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsSliceFlux
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHilbertEnergyBridge

/-!
# Reg Tails Assembly

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regTails_localizedSource_le_flux_density
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (J : ParabolicPoint → Vec3)
    (q : Vec3 → ℝ) (hq0 : ∀ x, 0 ≤ q x) (x : Vec3) (t : ℝ) :
    regTailsLocalizedSource u D p J q (x, t) ≤
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| +
      ∑ j : Fin 3,
        ((vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * |J (x, t) j| +
          2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x|) := by
  let A : Fin 3 → Fin 3 → ℝ := fun i j =>
    u (x, t) i * D (x, t) i j * spatialDeriv q j x
  let V : ℝ := vec3EuclideanNorm (u (x, t))
  have hgrad : 0 ≤ spatialGradientSq u D (x, t) := by
    unfold spatialGradientSq
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg (D (x, t) i j)
  have hfirst : -2 * spatialGradientSq u D (x, t) * q x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hgrad) (hq0 x)
  have hsum : -(∑ i : Fin 3, ∑ j : Fin 3, A i j) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, |A i j| := by
    calc
      -(∑ i : Fin 3, ∑ j : Fin 3, A i j) =
          ∑ i : Fin 3, ∑ j : Fin 3, -A i j := by simp
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |A i j| :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => neg_le_abs (A i j)
  have hsumAbs :
      (∑ i : Fin 3, ∑ j : Fin 3, |A i j|) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [A, abs_mul, mul_assoc]
  have hsecond : -(2 * ∑ i : Fin 3, ∑ j : Fin 3, A i j) ≤
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| := by
    calc
      -(2 * ∑ i : Fin 3, ∑ j : Fin 3, A i j) =
          2 * (-(∑ i : Fin 3, ∑ j : Fin 3, A i j)) := by ring
      _ ≤ 2 * (∑ i : Fin 3, ∑ j : Fin 3, |A i j|) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| := by
        rw [hsumAbs]
  have hthirdTerm (j : Fin 3) :
      (V ^ (2 : ℕ) * J (x, t) j +
        2 * p (x, t) * u (x, t) j) * spatialDeriv q j x ≤
      (V ^ (2 : ℕ) * |J (x, t) j| +
        2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x| := by
    have habs :
        |V ^ (2 : ℕ) * J (x, t) j +
          2 * p (x, t) * u (x, t) j| ≤
        V ^ (2 : ℕ) * |J (x, t) j| +
          2 * |p (x, t)| * |u (x, t) j| := by
      calc
        _ ≤ |V ^ (2 : ℕ) * J (x, t) j| +
            |2 * p (x, t) * u (x, t) j| := abs_add_le _ _
        _ = _ := by
          simp [abs_mul, abs_of_nonneg (sq_nonneg V)]
    calc
      _ ≤ |(V ^ (2 : ℕ) * J (x, t) j +
          2 * p (x, t) * u (x, t) j) * spatialDeriv q j x| := le_abs_self _
      _ = |V ^ (2 : ℕ) * J (x, t) j +
          2 * p (x, t) * u (x, t) j| * |spatialDeriv q j x| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
  have hthird :
      ∑ j : Fin 3,
        ((V ^ (2 : ℕ) * J (x, t) j +
          2 * p (x, t) * u (x, t) j) * spatialDeriv q j x) ≤
      ∑ j : Fin 3,
        ((V ^ (2 : ℕ) * |J (x, t) j| +
          2 * |p (x, t)| * |u (x, t) j|) * |spatialDeriv q j x|) :=
    Finset.sum_le_sum fun j _ => hthirdTerm j
  have hpartial (j : Fin 3) :
      spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t) =
        spatialDeriv q j x := rfl
  unfold regTailsLocalizedSource
  simp_rw [hpartial]
  dsimp [V] at hthird
  linarith only [hfirst, hsecond, hthird]

/-- A compact spatial weight has the integrated localized energy identity on
every positive-time interval, as in `lem:reg-tails`. -/
theorem regTails_compact_weight_interval_increment
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (J : ParabolicPoint → Vec3)
    (hLE : ∀ (ψ : ParabolicPoint → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq u
            (fun z i j => spatialPartial (fun y : ParabolicPoint => u y i) j z) z * ψ z =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
                2 * p z * u z i) * spatialPartial ψ i z)
    (hUcont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => u (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hDcont : ∀ i j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ =>
        spatialPartial (fun y : ParabolicPoint => u y i) j z)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hPcont : ContinuousOn (fun z : Vec3 × ℝ => p (z.1, z.2))
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hJcont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => J (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hUdiff : ∀ i : Fin 3, ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => u (z.1, z.2) i)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    regTailsEnergyWeight u q t - regTailsEnergyWeight u q s =
      ∫ τ in s..t,
        (∫ x : Vec3,
          regTailsLocalizedSource u
            (fun z i j => spatialPartial (fun y : ParabolicPoint => u y i) j z)
            p J q (x, τ) ∂volume) ∂volume := by
  have hweak := regTails_localized_weak_time_identity u p J
    hLE hUcont hDcont hPcont hJcont hUdiff q hq hqc
  have hprofiles := regTails_localized_profiles_continuous u
    (fun z i j => spatialPartial (fun y : ParabolicPoint => u y i) j z)
    p J q hq hqc hUcont hDcont hPcont hJcont
  exact regTails_intervalIntegral_eq_sub_of_weak_identity
    (regTailsEnergyWeight u q)
    (fun τ => ∫ x : Vec3,
      regTailsLocalizedSource u
        (fun z i j => spatialPartial (fun y : ParabolicPoint => u y i) j z)
        p J q (x, τ) ∂volume)
    hprofiles.1 hprofiles.2 hweak hs hst

private theorem regTails_localized_source_integrable
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (J : ParabolicPoint → Vec3)
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q) (t : ℝ)
    (hUcont : ∀ i : Fin 3, Continuous (fun x : Vec3 => u (x, t) i))
    (hDcont : ∀ i j : Fin 3,
      Continuous (fun x : Vec3 => D (x, t) i j))
    (hPcont : Continuous (fun x : Vec3 => p (x, t)))
    (hJcont : ∀ j : Fin 3,
      Continuous (fun x : Vec3 => J (x, t) j)) :
    Integrable (fun x : Vec3 =>
      regTailsLocalizedSource u D p J q (x, t)) volume := by
  let F : Vec3 → ℝ := fun x => regTailsLocalizedSource u D p J q (x, t)
  have hu : Continuous (fun x : Vec3 => u (x, t)) := continuous_pi_iff.2 hUcont
  have hV : Continuous (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp hu
  have hD (i j : Fin 3) : Continuous (fun x : Vec3 => D (x, t) i j) := hDcont i j
  have hp : Continuous (fun x : Vec3 => p (x, t)) := hPcont
  have hJ (j : Fin 3) : Continuous (fun x : Vec3 => J (x, t) j) := hJcont j
  have hgrad : Continuous (fun x : Vec3 => spatialGradientSq u D (x, t)) := by
    unfold spatialGradientSq
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    exact (hD i j).pow 2
  have hqcont : Continuous q := hq.continuous
  have hqpart (j : Fin 3) : Continuous
      (fun x : Vec3 => spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t)) := by
    have h := (CKN.contDiff_spatialDeriv_smooth hq j).continuous
    convert h using 1
    rfl
  have hFcont : Continuous F := by
    unfold F regTailsLocalizedSource
    have hfirst : Continuous (fun x : Vec3 =>
        -2 * spatialGradientSq u D (x, t) * q x) := by
      exact (continuous_const.mul hgrad).mul hqcont
    have hsecond : Continuous (fun x : Vec3 =>
        -(2 * ∑ i : Fin 3, ∑ j : Fin 3,
          u (x, t) i * D (x, t) i j *
            spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t))) := by
      have hsum : Continuous (fun x : Vec3 =>
          ∑ i : Fin 3, ∑ j : Fin 3,
            u (x, t) i * D (x, t) i j *
              spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t)) := by
        apply continuous_finsetSum
        intro i hi
        apply continuous_finsetSum
        intro j hj
        exact (((continuous_apply i).comp hu).mul (hD i j)).mul (hqpart j)
      exact (continuous_const.mul hsum).neg
    have hthird : Continuous (fun x : Vec3 =>
        ∑ j : Fin 3,
          ((vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * J (x, t) j +
            2 * p (x, t) * u (x, t) j) *
            spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t))) := by
      apply continuous_finsetSum
      intro j hj
      exact ((hV.pow 2).mul (hJ j)).add
        ((continuous_const.mul hp).mul ((continuous_apply j).comp hu)) |>.mul (hqpart j)
    exact (hfirst.add hsecond).add hthird
  have hqZero (x : Vec3) (hx : x ∉ tsupport q) : q x = 0 := by
    by_contra hne
    exact hx (subset_tsupport q (Function.mem_support.mpr hne))
  have hderivSupport (j : Fin 3) :
      tsupport (fun x : Vec3 => spatialDeriv q j x) ⊆ tsupport q := by
    change tsupport (fun x : Vec3 => (fderiv ℝ q x) (basisVec j)) ⊆ tsupport q
    exact tsupport_fderiv_apply_subset ℝ (basisVec j)
  have hFcompact : HasCompactSupport F := by
    apply HasCompactSupport.intro hqc.isCompact
    intro x hx
    have hderivZero (j : Fin 3) : spatialDeriv q j x = 0 := by
      by_contra hne
      exact hx (hderivSupport j
        (subset_tsupport _ (Function.mem_support.mpr hne)))
    have hpartial (j : Fin 3) :
        spatialPartial (fun y : ParabolicPoint => q y.1) j (x, t) =
          spatialDeriv q j x := rfl
    simp [F, regTailsLocalizedSource, hqZero x hx, hderivZero, hpartial]
  exact hFcont.integrable_of_hasCompactSupport hFcompact

/-- The localized source integral is bounded by the absolute flux density. -/
theorem regTails_localized_source_integral_le_flux
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (J : ParabolicPoint → Vec3)
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q) (hq0 : ∀ x, 0 ≤ q x) (t : ℝ)
    (hUcont : ∀ i : Fin 3, Continuous (fun x : Vec3 => u (x, t) i))
    (hDcont : ∀ i j : Fin 3,
      Continuous (fun x : Vec3 => D (x, t) i j))
    (hPcont : Continuous (fun x : Vec3 => p (x, t)))
    (hJcont : ∀ j : Fin 3,
      Continuous (fun x : Vec3 => J (x, t) j)) :
    ∫ x : Vec3, regTailsLocalizedSource u D p J q (x, t) ∂volume ≤
      ∫ x : Vec3,
        2 * ∑ i : Fin 3, ∑ j : Fin 3,
          |u (x, t) i| * |D (x, t) i j| * |spatialDeriv q j x| +
        ∑ j : Fin 3,
          ((vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * |J (x, t) j| +
            2 * |p (x, t)| * |u (x, t) j|) *
            |spatialDeriv q j x|) ∂volume := by
  have hsource := regTails_localized_source_integrable u D p J q hq hqc t
    hUcont hDcont hPcont hJcont
  have hflux := regTails_slice_flux_density_integrable u D p J t q hq hqc
    hUcont hDcont hPcont hJcont
  refine integral_mono hsource hflux ?_
  intro x
  exact regTails_localizedSource_le_flux_density u D p J q hq0 x t

private theorem regTails_time_flux_error_bound
    {t B M Q : ℝ} (ht : 0 < t) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hQ : 0 ≤ Q) (G : ℝ → ℝ)
    (hG : MemLp G 2 (volume.restrict (Ioo (0 : ℝ) t)))
    (hG0 : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) t)), 0 ≤ G τ)
    (hGenergy : ∫ τ in Ioo (0 : ℝ) t, G τ ^ (2 : ℕ) ∂volume ≤
      B ^ (2 : ℕ) / 2) :
    IntegrableOn (fun τ : ℝ =>
      18 * M * B * G τ +
        Q * M * B ^ (3 / 2 : ℝ) * G τ ^ (3 / 2 : ℝ))
      (Ioo (0 : ℝ) t) volume ∧
    ∫ τ in Ioo (0 : ℝ) t,
      18 * M * B * G τ +
        Q * M * B ^ (3 / 2 : ℝ) * G τ ^ (3 / 2 : ℝ) ∂volume ≤
      18 * M * B ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
        Q * M * B ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) t)
  let H : ℝ → ℝ := fun τ =>
    18 * M * B * G τ + Q * M * B ^ (3 / 2 : ℝ) * G τ ^ (3 / 2 : ℝ)
  have hG' : MemLp G (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa [μ] using hG
  have hPowAbs : MemLp (fun τ : ℝ => |G τ| ^ (3 / 2 : ℝ))
      (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
    have h := hG'.norm_rpow_div (ENNReal.ofReal (3 / 2 : ℝ))
    have hexp : ENNReal.ofReal (4 / 3 : ℝ) =
        ENNReal.ofReal 2 / ENNReal.ofReal (3 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      congr 1
      norm_num
    simpa only [hexp, Real.norm_eq_abs,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using h
  have hPow : MemLp (fun τ : ℝ => G τ ^ (3 / 2 : ℝ))
      (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
    apply (memLp_congr_ae ?_).mp hPowAbs
    filter_upwards [hG0] with τ hτ
    rw [abs_of_nonneg hτ]
  have hG1 : MemLp G (1 : ℝ≥0∞) μ :=
    hG'.mono_exponent (by norm_num)
  have hPow1 : MemLp (fun τ : ℝ => G τ ^ (3 / 2 : ℝ))
      (1 : ℝ≥0∞) μ := hPow.mono_exponent (by norm_num)
  have hGint : IntegrableOn G (Ioo (0 : ℝ) t) volume := by
    change Integrable G μ
    exact memLp_one_iff_integrable.mp hG1
  have hPowint : IntegrableOn (fun τ : ℝ => G τ ^ (3 / 2 : ℝ))
      (Ioo (0 : ℝ) t) volume := by
    change Integrable (fun τ : ℝ => G τ ^ (3 / 2 : ℝ)) μ
    exact memLp_one_iff_integrable.mp hPow1
  have hHint : IntegrableOn H (Ioo (0 : ℝ) t) volume := by
    dsimp [H]
    exact (hGint.const_mul (18 * M * B)).add
      (hPowint.const_mul (Q * M * B ^ (3 / 2 : ℝ)))
  have hT1 := regTails_time_integral_le_of_sq_integral ht hB G hG hG0 hGenergy
  have hT2 := regTails_time_rpow_three_halves_le_of_sq_integral
    ht hB G hG hG0 hGenergy
  have hEval : ∫ τ in Ioo (0 : ℝ) t, H τ ∂volume =
      18 * M * B * (∫ τ in Ioo (0 : ℝ) t, G τ ∂volume) +
        Q * M * B ^ (3 / 2 : ℝ) *
          (∫ τ in Ioo (0 : ℝ) t, G τ ^ (3 / 2 : ℝ) ∂volume) := by
    dsimp [H]
    rw [integral_add (hGint.const_mul (18 * M * B))
      (hPowint.const_mul (Q * M * B ^ (3 / 2 : ℝ))), integral_const_mul,
      integral_const_mul]
  have hBcube : B ^ (3 / 2 : ℝ) * B ^ (3 / 2 : ℝ) = B ^ (3 : ℕ) := by
    calc
      _ = (B ^ (3 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        ring
      _ = B ^ ((3 / 2 : ℝ) * 2) := (Real.rpow_mul hB _ _).symm
      _ = B ^ (3 : ℝ) := by congr 1; norm_num
      _ = B ^ (3 : ℕ) := Real.rpow_natCast _ _
  refine ⟨hHint, ?_⟩
  rw [hEval]
  calc
    _ ≤ 18 * M * B * (B * t ^ (1 / 2 : ℝ)) +
        Q * M * B ^ (3 / 2 : ℝ) *
          (B ^ (3 / 2 : ℝ) * t ^ (1 / 4 : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hT1 (by positivity))
        (mul_le_mul_of_nonneg_left hT2 (by positivity))
    _ = 18 * M * (B * B) * t ^ (1 / 2 : ℝ) +
        Q * M * (B ^ (3 / 2 : ℝ) * B ^ (3 / 2 : ℝ)) *
          t ^ (1 / 4 : ℝ) := by ring
    _ = 18 * M * B ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
        Q * M * B ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) := by
      rw [hBcube]
      ring

/-- A positive-time source increment is bounded by the global flux profile. -/
theorem regTails_open_interval_flux_bound
    {s t B M Q : ℝ} (hs : 0 < s) (hst : s < t)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (G A : ℝ → ℝ)
    (hG : MemLp G 2 (volume.restrict (Ioo (0 : ℝ) t)))
    (hG0 : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) t)), 0 ≤ G τ)
    (hGenergy : ∫ τ in Ioo (0 : ℝ) t, G τ ^ (2 : ℕ) ∂volume ≤
      B ^ (2 : ℕ) / 2)
    (hAcont : ContinuousOn A (Ioi (0 : ℝ)))
    (hAprofile : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) t)),
      A τ ≤ 18 * M * B * G τ +
        Q * M * B ^ (3 / 2 : ℝ) * G τ ^ (3 / 2 : ℝ)) :
    ∫ τ in s..t, A τ ∂volume ≤
      18 * M * B ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
        Q * M * B ^ (3 : ℕ) * t ^ (1 / 4 : ℝ) := by
  let H : ℝ → ℝ := fun τ =>
    18 * M * B * G τ + Q * M * B ^ (3 / 2 : ℝ) * G τ ^ (3 / 2 : ℝ)
  have hError := regTails_time_flux_error_bound (t := t) (hs.trans hst)
    hB hM hQ G hG hG0 hGenergy
  have hAinterval : IntervalIntegrable A volume s t := by
    have hsubset : Icc s t ⊆ Ioi (0 : ℝ) := by
      intro τ hτ
      exact lt_of_lt_of_le hs hτ.1
    exact (hAcont.mono hsubset).intervalIntegrable_of_Icc hst.le
  have hHinterval : IntervalIntegrable H volume s t := by
    have hHst : IntegrableOn H (Ioo s t) volume := by
      exact hError.1.mono_set (Ioo_subset_Ioo hs.le le_rfl)
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hst.le).2 hHst
  have hAprofileGlobal : ∀ᵐ τ ∂volume,
      τ ∈ Ioo (0 : ℝ) t → A τ ≤ H τ := by
    exact (ae_restrict_iff' measurableSet_Ioo).1 (by simpa [H] using hAprofile)
  have hAprofileIcc : A ≤ᵐ[volume.restrict (Icc s t)] H := by
    change ∀ᵐ τ ∂(volume.restrict (Icc s t)), A τ ≤ H τ
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hAprofileGlobal, Measure.ae_ne volume t] with τ hprofile hτne
    intro hτ
    apply hprofile
    refine ⟨lt_of_lt_of_le hs hτ.1, ?_⟩
    exact lt_of_le_of_ne hτ.2 hτne
  have hmono : ∫ τ in s..t, A τ ∂volume ≤ ∫ τ in s..t, H τ ∂volume :=
    intervalIntegral.integral_mono_ae_restrict hst.le hAinterval hHinterval
      hAprofileIcc
  have hHnonneg : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) t)), 0 ≤ H τ := by
    filter_upwards [hG0] with τ hτ
    dsimp [H]
    positivity
  have hsetsub : Ioo s t ≤ᵐ[volume] Ioo (0 : ℝ) t :=
    Filter.Eventually.of_forall fun τ hτ =>
      ⟨lt_trans hs hτ.1, hτ.2⟩
  have hsetmono := setIntegral_mono_set hError.1 hHnonneg hsetsub
  have hintervalEq : (∫ τ in s..t, H τ ∂volume) =
      ∫ τ in Ioo s t, H τ ∂volume := by
    rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo]
  calc
    ∫ τ in s..t, A τ ∂volume ≤ ∫ τ in s..t, H τ ∂volume := hmono
    _ = ∫ τ in Ioo s t, H τ ∂volume := hintervalEq
    _ ≤ ∫ τ in Ioo (0 : ℝ) t, H τ ∂volume := hsetmono
    _ ≤ _ := hError.2

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


variable (hregLocalEnergy : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
    (ε : ℝ) (hε : 0 < ε) (ψ : ParabolicPoint → ℝ),
    ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ (Ioi 0) →
    2 * ∫ z in spaceTimeSet Set.univ (Ioi 0),
        spatialGradientSq (uε a ha ε)
          (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z) z * ψ z =
      ∫ z in spaceTimeSet Set.univ (Ioi 0),
        (vec3EuclideanNorm (uε a ha ε z)) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            ((vec3EuclideanNorm (uε a ha ε z)) ^ (2 : ℕ) *
                regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z i +
              2 * pε a ha ε z * uε a ha ε z i) * spatialPartial ψ i z)


end CKN.Leray

end
