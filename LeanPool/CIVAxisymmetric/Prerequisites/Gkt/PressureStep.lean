/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.TopCylinderContainment
public import LeanPool.CIVAxisymmetric.Regularity.UniformCrudeBounds
public import LeanPool.CIVAxisymmetric.Regularity.EnergyIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Lin34Faithful
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExcessComparisonCore
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CIVAxisymmetric.Setting.SuitableWeakSolutionClass

/-!
# One step of the pressure decay at interior base points below the top slice

The pressure quantity `D(z, r) = r⁻² ∫_{Q_r(z)} |π|^{3/2}` obeys the integrated Lin estimate of
CKN (general force clause): for `r = θρ` with `θ ≤ 1/2`,
`D(θρ) ≤ A θ D(ρ) + A (8 θ⁻² γ(ρ)³ + θ^{3/2} λ(ρ)^{3/2})`, where the mean-free velocity quantity
has been bounded by `8 γ³`. This file states that inequality at base points `(0, s)`, `s < 0`,
together with the auxiliary facts used to iterate it uniformly in `s`: the containment of the
closed cylinders in `Q`, the comparison of an interior cylinder with a backward cylinder of twice
the radius at the origin, the conversion between the `L³` integral and `γ³`, between the
pressure integral and `D`, and the crude bound on `D` by the global `L^{3/2}` norm of `π`.
This is Lemma 3.4 of Gustafson, Kang and Tsai 2007 in the form used for the criterion of
`lem:aniso:closure`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The closed parabolic cylinder of radius `r < 1` based at `(0, s)`, `s < 0`, lies in the unit
cylinder when its bottom time `s - r²` exceeds `-1`. -/
theorem gkt_closure_parabolicCylinder_subset {s r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hs : s < 0) (hlow : -1 < s - r ^ 2) :
    closure (parabolicCylinder (0 : Vec3) s r) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) :=
  closure_parabolicCylinder_subset_unitCylinder 0 s r hr hs hlow
    (fun _ hy => lt_of_le_of_lt hy hr1)

/-- An interior cylinder `Q_ρ(0, s)` with `-3ρ² ≤ s < 0` lies in the backward cylinder of radius
`2ρ` at the origin, so an `L³` bound `η (2ρ)²` there gives the bound `4ηρ²` on `Q_ρ(0, s)`. -/
theorem gkt_lintegral_cube_parabolicCylinder_le {u : ParabolicPoint → Vec3} {s ρ η : ℝ}
    (hρ : 0 < ρ) (hs : s < 0) (hs3 : -(3 * ρ ^ 2) ≤ s)
    (htop : (∫⁻ z in vec3Ball (0 : Vec3) (2 * ρ) ×ˢ Ioo (-((2 * ρ) ^ 2)) 0,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤
          ENNReal.ofReal (η * (2 * ρ) ^ 2)) :
    (∫⁻ z in parabolicCylinder (0 : Vec3) s ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (4 * η * ρ ^ 2) := by
  have hsub : parabolicCylinder (0 : Vec3) s ρ ⊆
      vec3Ball (0 : Vec3) (2 * ρ) ×ˢ Ioo (-((2 * ρ) ^ 2)) 0 :=
    parabolicCylinder_subset_topCylinder hs (by linarith only [hρ]) (by nlinarith only [hs3])
  refine le_trans (lintegral_mono_set hsub) (le_of_le_of_eq htop ?_)
  congr 1
  ring

/-- An `L³` bound `c ρ²` on `Q_ρ(z)` is the bound `γ(z, ρ)³ ≤ c`. -/
theorem gkt_gamma_cube_le_of_lintegral {u : ParabolicPoint → Vec3} {z : ParabolicPoint}
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c)
    (h : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (c * ρ ^ 2)) :
    gamma u z ρ ^ 3 ≤ c := by
  rw [CKN.gamma_cube_eq u z ρ hρ]
  have ht : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤ c * ρ ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hrp : ρ ^ (-2 : ℝ) * ρ ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hρ]; norm_num
  have hpos : 0 ≤ ρ ^ (-2 : ℝ) := by positivity
  calc ρ ^ (-2 : ℝ) * (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal
      ≤ ρ ^ (-2 : ℝ) * (c * ρ ^ 2) := mul_le_mul_of_nonneg_left ht hpos
    _ = c * (ρ ^ (-2 : ℝ) * ρ ^ 2) := by ring
    _ = c := by rw [hrp, mul_one]

/-- For a suitable weak solution on a cylinder with closure in the domain, the pressure integral
`∫_{Q_r(z)} |π|^{3/2}` equals `r² D(z, r)`. -/
theorem gkt_lintegral_pressure_eq {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal (r ^ 2 * pressureD p z r) := by
  rw [sws_lintegral_abs_pow_eq_ofReal_delta_cube
    (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) z hr hsub]
  congr 1
  unfold pressureD
  rw [sws_integral_abs_pow_eq_delta_cube
    (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) z hr hsub]
  field_simp

/-- The pressure quantity `D` is nonnegative. -/
theorem gkt_pressureD_nonneg (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ) :
    0 ≤ pressureD p z r := by
  unfold pressureD
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)

/-- One step of the integrated Lin pressure estimate with a general force at ratio `θ ≤ 1/2`,
with the mean-free velocity quantity bounded by `8 γ³`. -/
theorem gkt_pressureD_step {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {z : ParabolicPoint} {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0)) :
    pressureD p z (θ * ρ) ≤
      CKN.Core.Endgame.theoremALin34Constant q * θ * pressureD p z ρ +
        CKN.Core.Endgame.theoremALin34Constant q *
          (8 * θ⁻¹ ^ 2 * gamma u z ρ ^ 3 + θ ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hA := CKN.Core.Endgame.theoremALin34Constant_nonneg q hq
  have hr : 0 < θ * ρ := mul_pos hθ hρ
  have hhalf : θ * ρ ≤ ρ / 2 := by nlinarith only [hθ2, hρ]
  have hmain := (CKN.pressure_lin34_of_sws q
    (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) (z := z) hρ hr hhalf
    hsub).2
  have hChat := pressureChat_le_eight_gamma_cube
    (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) hρ hsub
  have h1 : ρ / (θ * ρ) = θ⁻¹ := by field_simp
  have h2 : θ * ρ / ρ = θ := by field_simp
  rw [h1, h2] at hmain
  have hmono : θ⁻¹ ^ 2 * pressureChat u z ρ ≤ θ⁻¹ ^ 2 * (8 * gamma u z ρ ^ 3) :=
    mul_le_mul_of_nonneg_left hChat (by positivity)
  refine le_trans hmain ?_
  have hlam : 0 ≤ θ ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ) := by
    have := lambda_nonneg q f z hρ.le
    positivity
  nlinarith only [hmono, hA, hlam]

/-- The crude bound `D((0, s), ρ) ≤ ρ⁻² ‖π‖_{L^{3/2}(Q)}^{3/2}`, uniform in the base time `s`. -/
theorem gkt_pressureD_le_crude {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (henergy : GlobalEnergyClass u Du p) {s ρ : ℝ} (hρ : 0 < ρ)
    (hs : s < 0) (hlow : -1 < s - ρ ^ 2) (hρ1 : ρ ≤ 1) :
    pressureD p ((0 : Vec3), s) ρ ≤
      ρ⁻¹ ^ 2 * (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := by
  have hsub : parabolicCylinder (0 : Vec3) s ρ ⊆ unitCylinder :=
    parabolicCylinder_subset_unitCylinder hs hlow (vec3Ball_mono hρ1)
  have hpm : AEStronglyMeasurable p (volume.restrict (parabolicCylinder (0 : Vec3) s ρ)) :=
    henergy.2.2.aestronglyMeasurable.mono_set hsub
  have hfm : AEStronglyMeasurable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder (0 : Vec3) s ρ)) :=
    (continuous_abs.comp_aestronglyMeasurable hpm).aemeasurable.pow_const _ |>.aestronglyMeasurable
  have hint : ∫ w in parabolicCylinder (0 : Vec3) s ρ, |p w| ^ (3 / 2 : ℝ) =
      (∫⁻ w in parabolicCylinder (0 : Vec3) s ρ, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity) hfm]
    congr 1
    refine lintegral_congr fun w => ?_
    exact (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)).symm
  have hfin := (lintegral_pressure_lt_top u Du p henergy).ne
  have hle := ENNReal.toReal_mono hfin (lintegral_mono_set hsub (f := fun w =>
    ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)))
  unfold pressureD
  rw [show (((0 : Vec3), s) : ParabolicPoint).1 = 0 from rfl,
    show (((0 : Vec3), s) : ParabolicPoint).2 = s from rfl, hint]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end CIV
