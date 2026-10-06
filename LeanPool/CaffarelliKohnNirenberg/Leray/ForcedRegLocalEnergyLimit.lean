/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyDelta
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorRegularity

/-!
# Mollifier limits for the local energy inequality

Along the mollification radii `1/(n+1)`, mollifications of square-integrable
functions converge in `L²`, are bounded by the original `L²` norm, and commute
with weak derivatives; `L²` convergence is preserved by multiplication with
bounded continuous functions and by sums. These are the static limits of the
local energy inequality `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution Topology

noncomputable section

namespace CKN.Leray

/-- The mollification radii. -/
@[expose]
def leRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem leRadius_pos (n : ℕ) : 0 < leRadius n := by
  unfold leRadius
  positivity

theorem tendsto_leRadius : Tendsto leRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The mollifiers of radius `1/(n+1)`. -/
@[expose]
def leMol (n : ℕ) : Vec3 → ℝ := CKN.mollifier (d := 3) (leRadius n) (leRadius_pos n)

theorem leMol_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (leMol n) :=
  CKN.mollifier_contDiff (leRadius_pos n)

theorem leMol_hasCompactSupport (n : ℕ) : HasCompactSupport (leMol n) :=
  CKN.mollifier_hasCompactSupport (leRadius_pos n)

theorem tendsto_leConv_leMol {g : Vec3 → ℝ} (hg : MemLp g 2 volume) :
    Tendsto (fun n => eLpNorm (leConv (leMol n) g - g) 2 volume) atTop (𝓝 0) :=
  (CKN.tendsto_eLpNorm_sub_zero_mollify (by norm_num) (by norm_num) hg tendsto_leRadius
    leRadius_pos).congr fun n => rfl

theorem memLp_leConv_leMol {g : Vec3 → ℝ} (hg : MemLp g 2 volume) (n : ℕ) :
    MemLp (leConv (leMol n) g) 2 volume :=
  CKN.Foundation.Heat.mollify_memLp_of_memLp (by norm_num) (by norm_num) hg (leRadius_pos n)

theorem eLpNorm_leConv_leMol_le {g : Vec3 → ℝ} (hg : MemLp g 2 volume) (n : ℕ) :
    eLpNorm (leConv (leMol n) g) 2 volume ≤ eLpNorm g 2 volume :=
  CKN.young_convolution_nonneg_integral_one_of_aemeasurable (by norm_num) (by norm_num)
    (CKN.mollifier_nonneg (leRadius_pos n))
    (integrable_of_integral_eq_one (CKN.mollifier_integral_one (leRadius_pos n)))
    (CKN.mollifier_integral_one (leRadius_pos n))
    (CKN.mollifier_contDiff (leRadius_pos n) (n := 0)).continuous.measurable
    hg.aestronglyMeasurable.aemeasurable

/-- Mollification commutes with a weak partial derivative. -/
theorem leConv_spatialDeriv_leMol {u g : Vec3 → ℝ} (hu : MemLp u 2 volume)
    (hg : MemLp g 2 volume) {j : Fin 3}
    (hweak : CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j u g) (n : ℕ) (x : Vec3) :
    leConv (CKN.spatialDeriv (leMol n) j) u x = leConv (leMol n) g x := by
  rw [← fderiv_leConv (leMol_contDiff n) (leMol_hasCompactSupport n) hu x j]
  exact CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
    (hu.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num)) hweak
    (leRadius_pos n) (subset_univ _)

/-- `L²` convergence is preserved by multiplication with a bounded function. -/
theorem tendsto_eLpNorm_mul_bounded {X : ℕ → Vec3 → ℝ} {X0 h : Vec3 → ℝ}
    (hX : Tendsto (fun n => eLpNorm (X n - X0) 2 volume) atTop (𝓝 0))
    (hm : ∀ n, AEStronglyMeasurable (X n - X0) volume) (hh : AEStronglyMeasurable h volume)
    {M : ℝ} (hM : ∀ x, ‖h x‖ ≤ M) :
    Tendsto (fun n => eLpNorm ((fun x => X n x * h x) - fun x => X0 x * h x) 2 volume) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun n => ENNReal.ofReal M * eLpNorm (X n - X0) 2 volume) atTop
      (𝓝 (ENNReal.ofReal M * 0)) :=
    ENNReal.Tendsto.const_mul hX (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    fun n => ?_
  have e : (fun x => X n x * h x) - (fun x => X0 x * h x) = (X n - X0) * h := by
    funext x
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [e]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hm n).mul hh) (Eventually.of_forall fun x => ?_) 2
  rw [Pi.mul_apply, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

/-- `L²` convergence is preserved by sums. -/
theorem tendsto_eLpNorm_add {X Y : ℕ → Vec3 → ℝ} {X0 Y0 : Vec3 → ℝ}
    (hX : Tendsto (fun n => eLpNorm (X n - X0) 2 volume) atTop (𝓝 0))
    (hY : Tendsto (fun n => eLpNorm (Y n - Y0) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((X n + Y n) - (X0 + Y0)) 2 volume) atTop (𝓝 0) := by
  have hlim := hX.add hY
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    fun n => ?_
  have heq : (X n + Y n) - (X0 + Y0) = (X n - X0) + (Y n - Y0) := by abel
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

theorem memLp_mul_bounded {g h : Vec3 → ℝ} (hg : MemLp g 2 volume)
    (hh : AEStronglyMeasurable h volume) {M : ℝ} (hM : ∀ x, ‖h x‖ ≤ M) :
    MemLp (fun x => g x * h x) 2 volume :=
  hg.of_le_mul (c := M) (hg.aestronglyMeasurable.mul hh) (Eventually.of_forall fun x => by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

/-- The limit of a pairing of a mollification with a mollified product. -/
theorem tendsto_integral_leConv_mul {A : Vec3 → ℝ} (hA : MemLp A 2 volume) {Y : ℕ → Vec3 → ℝ}
    {Y0 : Vec3 → ℝ} (hY : ∀ n, MemLp (Y n) 2 volume) (hY0 : MemLp Y0 2 volume)
    (hYc : Tendsto (fun n => eLpNorm (Y n - Y0) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, leConv (leMol n) A x * Y n x) atTop (𝓝 (∫ x, A x * Y0 x)) :=
  tendsto_integral_mul_of_tendsto_eLpNorm_two (fun n => leConv (leMol n) A) Y A Y0
    (fun n => memLp_leConv_leMol hA n) hY hA hY0 (tendsto_leConv_leMol hA) hYc

/-- The mollified product derivative converges to the weak product derivative. -/
theorem tendsto_mollified_productDeriv {uk Dj : Vec3 → ℝ} (hu : MemLp uk 2 volume)
    (hD : MemLp Dj 2 volume) {j : Fin 3}
    (hweak : CKN.HasWeakPartialDerivOn (Set.univ : Set Vec3) j uk Dj) {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun n => eLpNorm ((fun x => leConv (CKN.spatialDeriv (leMol n) j) uk x * ψ x +
        leConv (leMol n) uk x * fderiv ℝ ψ x (CKN.basisVec j)) -
      fun x => Dj x * ψ x + uk x * fderiv ℝ ψ x (CKN.basisVec j)) 2 volume) atTop (𝓝 0) := by
  obtain ⟨M1, hM1⟩ := Continuous.bounded_above_of_compact_support hψ.continuous hψc
  have hdψ : Continuous fun x => fderiv ℝ ψ x (CKN.basisVec j) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨M2, hM2⟩ := Continuous.bounded_above_of_compact_support hdψ
    (hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j))
  have h1 := tendsto_eLpNorm_mul_bounded (X := fun n => leConv (leMol n) Dj) (X0 := Dj)
    (tendsto_leConv_leMol hD) (fun n => ((memLp_leConv_leMol hD n).sub hD).aestronglyMeasurable)
    hψ.continuous.aestronglyMeasurable hM1
  have h2 := tendsto_eLpNorm_mul_bounded (X := fun n => leConv (leMol n) uk) (X0 := uk)
    (tendsto_leConv_leMol hu) (fun n => ((memLp_leConv_leMol hu n).sub hu).aestronglyMeasurable)
    hdψ.aestronglyMeasurable hM2
  have h := tendsto_eLpNorm_add h1 h2
  refine h.congr fun n => ?_
  congr 1
  funext x
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [leConv_spatialDeriv_leMol hu hD hweak n x]

end CKN.Leray

end
