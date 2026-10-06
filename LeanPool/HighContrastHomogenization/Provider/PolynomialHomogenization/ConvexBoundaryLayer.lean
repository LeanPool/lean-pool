/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Consistency.ConvexDilation
public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NormScaling

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryLayer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary layers of convex domains

An interior Euclidean ball controls the volume of every inner boundary layer
of a convex domain.  The proof places a homothetic copy of the domain inside
the complementary inner core and compares its volume with the original one.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

variable {d : ℕ}

private theorem one_sub_pow_le_nat_mul_one_sub {lam : ℝ}
    (hlam0 : 0 ≤ lam) :
    1 - lam ^ d ≤ (d : ℝ) * (1 - lam) := by
  have h := one_add_mul_sub_le_pow (n := d) (a := lam) (by linarith only [hlam0])
  linarith only [h]

private theorem euclideanBallAt_dilate_subset_of_convex
    {U : Set (Vec d)} (hconv : Convex ℝ U) {c : Vec d} {rho lam : ℝ}
    (hrho : 0 < rho) (hball : euclideanBallAt c rho ⊆ U)
    (hlam : lam ∈ Set.Ico (0 : ℝ) 1) {x : Vec d} (hx : x ∈ U) :
    euclideanBallAt (c + lam • (x - c)) ((1 - lam) * rho) ⊆ U := by
  have hgap : 0 < 1 - lam := sub_pos.mpr hlam.2
  intro z hz
  let b : Vec d := c + (1 - lam)⁻¹ • (z - (c + lam • (x - c)))
  have hbc : b - c = (1 - lam)⁻¹ • (z - (c + lam • (x - c))) := by
    dsimp [b]
    abel
  have hscale : (0 : ℝ) < (1 - lam)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hgap)
  have hcancel : (1 - lam)⁻¹ ^ 2 * (((1 - lam) * rho) ^ 2) = rho ^ 2 := by
    field_simp [hgap.ne']
  have hbball : b ∈ euclideanBallAt c rho := by
    rw [mem_euclideanBallAt_iff, hbc, vecNormSq_smul]
    calc
      (1 - lam)⁻¹ ^ 2 * vecNormSq (z - (c + lam • (x - c))) <
          (1 - lam)⁻¹ ^ 2 * (((1 - lam) * rho) ^ 2) :=
        mul_lt_mul_of_pos_left hz hscale
      _ = rho ^ 2 := hcancel
  have hb : b ∈ U := hball hbball
  have hzU : (1 - lam) • b + lam • x ∈ U :=
    hconv hb hx (sub_nonneg.mpr hlam.2.le) hlam.1 (by ring)
  have heq : (1 - lam) • b + lam • x = z := by
    dsimp [b]
    have hgapne : 1 - lam ≠ 0 := hgap.ne'
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hgapne]
    ring
  rwa [heq] at hzU

private theorem dilate_image_eq_translate_smul (c : Vec d) (lam : ℝ)
    (U : Set (Vec d)) :
    (fun x : Vec d => c + lam • (x - c)) '' U =
      translateSet ((1 - lam) • c) (lam • U) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨lam • x, Set.smul_mem_smul_set hx, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The volume within Euclidean distance `t` of the inside boundary of a
bounded open convex domain is at most `d t / rho` times the domain volume,
when the domain contains a concentric Euclidean ball of radius `rho`. -/
theorem volume_innerBoundaryLayer_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {rho Rad t : ℝ}
    (hsand : HasBallSandwich U rho Rad) (ht : 0 ≤ t) :
    volume {x : Vec d | x ∈ U ∧ ¬ euclideanBallAt x t ⊆ U} ≤
      ENNReal.ofReal ((d : ℝ) * t / rho) * volume U := by
  obtain ⟨hrho, _hRad, c, hball, _hout⟩ := hsand
  have hUtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp only [mul_zero, zero_div, ENNReal.ofReal_zero, zero_mul]
    have hempty : {x : Vec d | x ∈ U ∧ ¬ euclideanBallAt x 0 ⊆ U} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _hx
      push Not
      intro z hz
      have hz' := (mem_euclideanBallAt_iff z).mp hz
      norm_num at hz'
      exact False.elim ((not_lt_of_ge (vecNormSq_nonneg (z - x))) hz')
    rw [hempty, measure_empty]
  · by_cases htrho : t < rho
    · let lam : ℝ := 1 - t / rho
      have hdivpos : 0 < t / rho := div_pos htpos hrho
      have hdivlt : t / rho < 1 := (div_lt_one hrho).mpr htrho
      have hlampos : 0 < lam := by dsimp [lam]; linarith only [hdivlt]
      have hlam0 : 0 ≤ lam := hlampos.le
      have hlam1 : lam < 1 := by dsimp [lam]; linarith only [hdivpos]
      have hgap : (1 - lam) * rho = t := by
        dsimp [lam]
        field_simp [hrho.ne']
        ring
      let V : Set (Vec d) := (fun x : Vec d => c + lam • (x - c)) '' U
      have hVsub : V ⊆ U := by
        rintro y ⟨x, hx, rfl⟩
        have hinner := euclideanBallAt_dilate_subset_of_convex hU.convex hrho hball
          ⟨hlam0, hlam1⟩ hx
        exact hinner (center_mem_euclideanBallAt _ (by rw [hgap]; exact htpos))
      have hVeq : V = translateSet ((1 - lam) • c) (lam • U) := by
        exact dilate_image_eq_translate_smul c lam U
      have hVmeas : MeasurableSet V := by
        rw [hVeq, ← preimage_subRight_eq_translateSet]
        exact (hU.isOpen.measurableSet.const_smul_of_ne_zero hlampos.ne').preimage
          (continuous_id.sub continuous_const).measurable
      have hVvol : volume V = ENNReal.ofReal (lam ^ d) * volume U := by
        rw [hVeq, volume_translateSet_eq]
        simpa [Vec] using
          (MeasureTheory.Measure.addHaar_smul_of_nonneg
            (μ := (volume : Measure (Vec d))) hlam0 U)
      have hlayer : {x : Vec d | x ∈ U ∧ ¬ euclideanBallAt x t ⊆ U} ⊆ U \ V := by
        rintro x ⟨hxU, hxball⟩
        refine ⟨hxU, fun hxV => ?_⟩
        obtain ⟨y, hy, rfl⟩ := hxV
        apply hxball
        rw [← hgap]
        exact euclideanBallAt_dilate_subset_of_convex hU.convex hrho hball
          ⟨hlam0, hlam1⟩ hy
      have hVtop : volume V ≠ ⊤ := ne_top_of_le_ne_top hUtop (measure_mono hVsub)
      have hfactor0 : 0 ≤ (d : ℝ) * t / rho := by positivity
      have hRtop : ENNReal.ofReal ((d : ℝ) * t / rho) * volume U ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUtop
      refine (measure_mono hlayer).trans ?_
      rw [measure_sdiff hVsub hVmeas.nullMeasurableSet hVtop]
      rw [← ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top hUtop tsub_le_self) hRtop]
      rw [ENNReal.toReal_sub_of_le (measure_mono hVsub) hUtop, hVvol,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hlam0 d),
        ENNReal.toReal_ofReal_mul _ _ hfactor0]
      have hpow := one_sub_pow_le_nat_mul_one_sub (d := d) hlam0
      have hfactor : (d : ℝ) * (1 - lam) = (d : ℝ) * t / rho := by
        rw [← hgap]
        field_simp [hrho.ne']
      rw [← hfactor]
      rw [show (volume U).toReal - lam ^ d * (volume U).toReal =
        (1 - lam ^ d) * (volume U).toReal by ring]
      exact mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg
    · have hrhot : rho ≤ t := le_of_not_gt htrho
      have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hfactor : (1 : ℝ) ≤ (d : ℝ) * t / rho := by
        have htdiv : 1 ≤ t / rho :=
          (le_div_iff₀ hrho).mpr (by simpa only [one_mul] using hrhot)
        calc
          1 ≤ (d : ℝ) * 1 := by simpa using hdreal
          _ ≤ (d : ℝ) * (t / rho) :=
            mul_le_mul_of_nonneg_left htdiv (Nat.cast_nonneg d)
          _ = (d : ℝ) * t / rho := by ring
      calc
        volume {x : Vec d | x ∈ U ∧ ¬ euclideanBallAt x t ⊆ U} ≤ volume U :=
          measure_mono fun _ hx => hx.1
        _ = ENNReal.ofReal 1 * volume U := by rw [ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal ((d : ℝ) * t / rho) * volume U := by
          gcongr

end

end HighContrast
end HCPolySupport
