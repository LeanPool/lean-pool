/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# The transport velocity `J_ε u` of a continuous field

The transport velocity of `thm:regularised` is the spatial convolution of the
velocity with a smooth compactly supported kernel. When the velocity is
continuous on `ℝ³ × (0,∞)` and has square-integrable slices, the transport
velocity is continuous there, and it is bounded by the integral of the kernel
times any bound of the velocity slice.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- A spatial convolution in a space-time field with a continuous compactly
supported kernel is continuous on every translation-invariant set. -/
theorem regR12_convolution_continuousOn {κ : Vec3 → ℝ} {S : Set (Vec3 × ℝ)}
    {F : Vec3 × ℝ → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hF : ContinuousOn F S) (hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S) :
    ContinuousOn (fun z : Vec3 × ℝ => ∫ y : Vec3, F (z.1 - y, z.2) * κ y) S := by
  let G : (Vec3 × ℝ) → Vec3 → ℝ := fun z y => F (z.1 - y, z.2) * κ y
  have hG : ContinuousOn G.uncurry (S ×ˢ Set.univ) := by
    have hshift : Continuous (fun q : (Vec3 × ℝ) × Vec3 => (q.1.1 - q.2, q.1.2)) := by
      fun_prop
    have hshiftS : Set.MapsTo (fun q : (Vec3 × ℝ) × Vec3 => (q.1.1 - q.2, q.1.2))
        (S ×ˢ Set.univ) S := by
      rintro ⟨z, y⟩ ⟨hz, -⟩
      exact hSshift z hz y
    change ContinuousOn (fun q : (Vec3 × ℝ) × Vec3 => F (q.1.1 - q.2, q.1.2) * κ q.2)
      (S ×ˢ Set.univ)
    exact (hF.comp hshift.continuousOn hshiftS).mul (hκ.comp continuous_snd).continuousOn
  have hGzero : ∀ z : Vec3 × ℝ, ∀ y : Vec3, z ∈ S → y ∉ tsupport κ → G z y = 0 := by
    intro z y _ hy
    simp [G, image_eq_zero_of_notMem_tsupport hy]
  exact continuousOn_integral_of_compact_support hκc hG hGzero

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)

theorem regR12Kernel_mollifier_continuous :
    Continuous (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) := by
  change Continuous (fun y : Vec3 => (ε ^ 3)⁻¹ * ρ.rho (ε⁻¹ • WithLp.toLp 2 y))
  exact continuous_const.mul (ρ.smooth.continuous.comp
    ((continuous_const_smul ε⁻¹).comp (PiLp.continuous_toLp 2 _)))

theorem regR12Kernel_mollifier_compact :
    HasCompactSupport (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) := by
  have hscaleNe : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
  let hhomeo : Vec3 ≃ₜ L2Vec3 := CKN.Foundation.Parabolic.vec3Homeomorph
  let hscale : L2Vec3 ≃ₜ L2Vec3 := Homeomorph.smulOfNeZero ε⁻¹ hscaleNe
  have hcompact : HasCompactSupport (fun x : Vec3 => ρ.rho (hscale (hhomeo x))) :=
    ρ.compact.comp_homeomorph (hhomeo.trans hscale)
  change HasCompactSupport (fun x : Vec3 => (ε ^ 3)⁻¹ * ρ.rho (hscale (hhomeo x)))
  exact hcompact.mul_left

/-- The transport velocity as a spatial convolution. -/
theorem regR12_mollifiedVelocity_eq_integral (u : ParabolicPoint → Vec3) (t : ℝ)
    (hSlice : MemLp (fun x : Vec3 => u (x, t)) 2 volume) (x : Vec3) (i : Fin 3) :
    regUniformMollifiedVelocity ρ ε hε u (x, t) i =
      ∫ y : Vec3, u (x - y, t) i * regMollifierKernel ρ ε hε (WithLp.toLp 2 y) := by
  have h := regUniformMollifiedInitial_component_convolution ρ ε hε
    (a := fun y : Vec3 => u (y, t)) hSlice x i
  change WithLp.ofLp (regMollifyVector ρ ε hε
    (regUniformSpatialField (fun y : Vec3 => u (y, t))) (WithLp.toLp 2 x)) i = _
  change regUniformMollifiedInitial ρ ε hε (fun y : Vec3 => u (y, t)) x i = _
  rw [h, MeasureTheory.convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- The transport velocity of a velocity continuous on `ℝ³ × (0,∞)` with
square-integrable slices is continuous there. -/
theorem regR12_mollifiedVelocity_continuousOn (u : ParabolicPoint → Vec3)
    (hSlice : ∀ t : ℝ, 0 < t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hU : ∀ i : Fin 3, ContinuousOn (fun z : Vec3 × ℝ => u z i) (Set.univ ×ˢ Ioi 0))
    (i : Fin 3) :
    ContinuousOn (fun z : Vec3 × ℝ => regUniformMollifiedVelocity ρ ε hε u z i)
      (Set.univ ×ˢ Ioi 0) := by
  have h := regR12_convolution_continuousOn (regR12Kernel_mollifier_continuous ρ ε hε)
    (regR12Kernel_mollifier_compact ρ ε hε) (hU i) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  refine h.congr fun z hz => ?_
  exact regR12_mollifiedVelocity_eq_integral ρ ε hε u z.2 (hSlice z.2 hz.2) z.1 i

/-- The transport velocity is bounded by the integral of the kernel times a
bound of the velocity slice. -/
theorem regR12_mollifiedVelocity_abs_le (u : ParabolicPoint → Vec3) (t : ℝ)
    (hSlice : MemLp (fun x : Vec3 => u (x, t)) 2 volume) (B : ℝ)
    (hB : ∀ x : Vec3, ∀ i : Fin 3, |u (x, t) i| ≤ B) (x : Vec3) (i : Fin 3) :
    |regUniformMollifiedVelocity ρ ε hε u (x, t) i| ≤
      B * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)| := by
  rw [regR12_mollifiedVelocity_eq_integral ρ ε hε u t hSlice x i, ← Real.norm_eq_abs]
  have hκint : Integrable (fun y : Vec3 => regMollifierKernel ρ ε hε (WithLp.toLp 2 y)) :=
    (regR12Kernel_mollifier_continuous ρ ε hε).integrable_of_hasCompactSupport
      (regR12Kernel_mollifier_compact ρ ε hε)
  calc ‖∫ y : Vec3, u (x - y, t) i * regMollifierKernel ρ ε hε (WithLp.toLp 2 y)‖
      ≤ ∫ y : Vec3, ‖u (x - y, t) i * regMollifierKernel ρ ε hε (WithLp.toLp 2 y)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : Vec3, B * |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hκint.abs.const_mul B) (Filter.Eventually.of_forall fun y => ?_)
        change ‖u (x - y, t) i * regMollifierKernel ρ ε hε (WithLp.toLp 2 y)‖ ≤
          B * |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)|
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hB _ i) (abs_nonneg _)
    _ = B * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)| := integral_const_mul _ _

end CKN.Leray
