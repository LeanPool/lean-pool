/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportNorms

/-!
# CubeTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Moving the cube quantities between `y + □_m` and the origin cube

The oscillation family of the regularity theorem is stated on the origin cube
`□_m`, while the localized estimates are read on the translated cube
`y + □_m`.  Lebesgue measure is translation invariant, so the volume average
and the volume-normalized `L²` seminorm move between the two frames with no
constant; this file records those two identities, the two elementary volume
facts about `y + □_m`, and the exponent monotonicity of the normalized Hölder
seminorm on a cube.

## Main results

* `volumeAverage_cubeSetAt`, `normalizedL2On_cubeSetAt` — the two transports.
* `ofReal_rpow_mul_holderSeminormOn_mono` — the normalized seminorm
  `3 ^ (alpha m) [f]_{C^{0,alpha}(y + □_m)}` increases with the exponent, since
  two points of the cube are less than `3 ^ m` apart.
* `ofReal_normalizedL2On_le_eLpNorm` — the dictionary between the seminorm
  `‖·‖_{L²(y + □_m)}` and the `eLpNorm` against the normalized volume measure.
-/

namespace Algsuperdiff.Section4.Provider.Holder

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section5.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube at the origin, and its volume -/

/-- The cube centred at the origin is the origin cube. -/
theorem cubeSetAt_zero_eq (m : ℤ) :
    cubeSetAt (0 : Vec d) m = openCubeSet (originCube d m) :=
  Algsuperdiff.Section5.Support.cubeSetAt_zero_eq_openCubeSet m

theorem volume_cubeSetAt_ne_top (y : Vec d) (m : ℤ) : volume (cubeSetAt y m) ≠ ⊤ :=
  (isOpenBoundedConvexDomain_cubeSetAt y m).volume_lt_top.ne

theorem volume_cubeSetAt_pos (y : Vec d) (m : ℤ) : 0 < volume (cubeSetAt y m) :=
  (isOpen_cubeSetAt y m).measure_pos volume (cubeSetAt_nonempty y m)

/-! ## 2. The two transports -/

/-- The volume average over `y + □_m` is the volume average over `□_m` of the
recentred integrand. -/
theorem volumeAverage_cubeSetAt (y : Vec d) (m : ℤ) (f : Vec d → ℝ) :
    volumeAverage (cubeSetAt y m) f =
      volumeAverage (openCubeSet (originCube d m)) (fun x => f (x + y)) := by
  rw [cubeSetAt_eq_translateSet]
  exact HCPolySupport.Book.Ch01.volumeAverage_translateSet_eq_comp_addRight y _ f

/-- The volume-normalized `L²` seminorm over `y + □_m` is the seminorm over
`□_m` of the recentred integrand. -/
theorem normalizedL2On_cubeSetAt (y : Vec d) (m : ℤ) (f : Vec d → ℝ) :
    normalizedL2On (cubeSetAt y m) f =
      normalizedL2On (openCubeSet (originCube d m)) (fun x => f (x + y)) := by
  unfold normalizedL2On
  rw [cubeSetAt_eq_translateSet]
  rw [HCPolySupport.Book.Ch01.volumeAverage_translateSet_eq_comp_addRight y _
    (fun x => f x ^ 2)]

/-! ## 3. Exponent monotonicity of the normalized Hölder seminorm -/

/-- **The Hölder seminorm on a cube decreases with the exponent, up to the
diameter weight.**  Two points of `y + □_m` are less than `3 ^ m` apart, so a
difference quotient at exponent `alpha` is at most `3 ^ ((beta - alpha) m)`
times the quotient at the larger exponent `beta`. -/
theorem holderSeminormOn_le_rpow_mul {E : Type*} [NormedAddCommGroup E]
    (y : Vec d) (m : ℤ) {alpha beta : ℝ} (hab : alpha ≤ beta) (f : Vec d → E) :
    holderSeminormOn (cubeSetAt y m) alpha f ≤
      ENNReal.ofReal (Real.rpow 3 ((beta - alpha) * (m : ℝ))) *
        holderSeminormOn (cubeSetAt y m) beta f := by
  have hrfl : ∀ a b : ℝ, Real.rpow a b = a ^ b := fun _ _ => rfl
  have hT : Real.rpow 3 ((beta - alpha) * (m : ℝ)) = ((3 : ℝ) ^ m) ^ (beta - alpha) := by
    simp only [hrfl]
    rw [show ((3 : ℝ) ^ m) = (3 : ℝ) ^ (m : ℝ) from (Real.rpow_intCast 3 m).symm,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hTnn : (0 : ℝ) ≤ Real.rpow 3 ((beta - alpha) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  simp only [holderSeminormOn, iSup_le_iff]
  intro x hx z hz hne
  have hnorm : ‖x - z‖ < (3 : ℝ) ^ m := norm_sub_lt_of_mem_cubeSetAt hx hz
  have hpos : (0 : ℝ) < ‖x - z‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.2 hne
  have hba : (0 : ℝ) ≤ beta - alpha := by linarith only [hab]
  have hstep : ‖x - z‖ ^ (beta - alpha) ≤ Real.rpow 3 ((beta - alpha) * (m : ℝ)) := by
    rw [hT]
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm.le hba
  have hpa : (0 : ℝ) < ‖x - z‖ ^ alpha := Real.rpow_pos_of_pos hpos alpha
  have hpb : (0 : ℝ) < ‖x - z‖ ^ beta := Real.rpow_pos_of_pos hpos beta
  have hsplit : ‖x - z‖ ^ beta = ‖x - z‖ ^ alpha * ‖x - z‖ ^ (beta - alpha) := by
    rw [← Real.rpow_add hpos]
    ring_nf
  have hquot : ‖f x - f z‖ / ‖x - z‖ ^ alpha ≤
      Real.rpow 3 ((beta - alpha) * (m : ℝ)) * (‖f x - f z‖ / ‖x - z‖ ^ beta) := by
    have hid : Real.rpow 3 ((beta - alpha) * (m : ℝ)) * (‖f x - f z‖ / ‖x - z‖ ^ beta)
        = (‖f x - f z‖ * Real.rpow 3 ((beta - alpha) * (m : ℝ))) /
            (‖x - z‖ ^ alpha * ‖x - z‖ ^ (beta - alpha)) := by
      rw [← hsplit]; ring
    have hkey : ‖f x - f z‖ * ‖x - z‖ ^ (beta - alpha) ≤
        ‖f x - f z‖ * Real.rpow 3 ((beta - alpha) * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
    rw [hid, div_le_div_iff₀ hpa (by positivity)]
    have h := mul_le_mul_of_nonneg_right hkey hpa.le
    linarith only [h]
  calc ENNReal.ofReal (‖f x - f z‖ / ‖x - z‖ ^ alpha)
      ≤ ENNReal.ofReal (Real.rpow 3 ((beta - alpha) * (m : ℝ)) *
          (‖f x - f z‖ / ‖x - z‖ ^ beta)) := ENNReal.ofReal_le_ofReal hquot
    _ = ENNReal.ofReal (Real.rpow 3 ((beta - alpha) * (m : ℝ))) *
          ENNReal.ofReal (‖f x - f z‖ / ‖x - z‖ ^ beta) := ENNReal.ofReal_mul hTnn
    _ ≤ ENNReal.ofReal (Real.rpow 3 ((beta - alpha) * (m : ℝ))) *
          holderSeminormOn (cubeSetAt y m) beta f :=
        mul_le_mul' le_rfl (le_holderSeminormOn hx hz hne)

/-- **The normalized seminorm `3 ^ (alpha m) [f]_{C^{0,alpha}(y + □_m)}` is
monotone in the exponent.** -/
theorem ofReal_rpow_mul_holderSeminormOn_mono {E : Type*} [NormedAddCommGroup E]
    (y : Vec d) (m : ℤ) {alpha beta : ℝ} (hab : alpha ≤ beta) (f : Vec d → E) :
    ENNReal.ofReal (Real.rpow 3 (alpha * (m : ℝ))) *
        holderSeminormOn (cubeSetAt y m) alpha f ≤
      ENNReal.ofReal (Real.rpow 3 (beta * (m : ℝ))) *
        holderSeminormOn (cubeSetAt y m) beta f := by
  have hrfl : ∀ a b : ℝ, Real.rpow a b = a ^ b := fun _ _ => rfl
  have hsplit : Real.rpow 3 (beta * (m : ℝ)) =
      Real.rpow 3 (alpha * (m : ℝ)) * Real.rpow 3 ((beta - alpha) * (m : ℝ)) := by
    simp only [hrfl]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc ENNReal.ofReal (Real.rpow 3 (alpha * (m : ℝ))) *
        holderSeminormOn (cubeSetAt y m) alpha f
      ≤ ENNReal.ofReal (Real.rpow 3 (alpha * (m : ℝ))) *
          (ENNReal.ofReal (Real.rpow 3 ((beta - alpha) * (m : ℝ))) *
            holderSeminormOn (cubeSetAt y m) beta f) :=
        mul_le_mul' le_rfl (holderSeminormOn_le_rpow_mul y m hab f)
    _ = ENNReal.ofReal (Real.rpow 3 (beta * (m : ℝ))) *
          holderSeminormOn (cubeSetAt y m) beta f := by
        have hnn : (0 : ℝ) ≤ Real.rpow 3 (alpha * (m : ℝ)) :=
          Real.rpow_nonneg (by norm_num) _
        rw [hsplit, ENNReal.ofReal_mul hnn, mul_assoc]

/-! ## 4. The seed dictionary -/

instance isFiniteMeasure_volume_restrict_cubeSetAt (y : Vec d) (m : ℤ) :
    IsFiniteMeasure (volume.restrict (cubeSetAt y m)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_cubeSetAt_ne_top y m)⟩

/-- The mean-subtracted solution is square integrable on the cube. -/
theorem memLp_sub_volumeAverage_cubeSetAt (y : Vec d) (m : ℤ)
    (u : H1Function (cubeSetAt y m)) :
    MemLp (fun x => u.toFun x - volumeAverage (cubeSetAt y m) u.toFun) 2
      (volume.restrict (cubeSetAt y m)) :=
  u.memL2.sub (memLp_const _)

/-- **The seed dictionary.**  The volume-normalized `L²` seminorm on the cube is
bounded by the `eLpNorm` against the normalized volume measure, the form the
localized estimate is written in. -/
theorem ofReal_normalizedL2On_le_eLpNorm (y : Vec d) (m : ℤ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (cubeSetAt y m))) :
    ENNReal.ofReal (normalizedL2On (cubeSetAt y m) f) ≤
      eLpNorm f 2 (normalizedVolumeMeasureOn (cubeSetAt y m)) := by
  rw [normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
    (volume_cubeSetAt_pos y m) (volume_cubeSetAt_ne_top y m) hf]
  exact ENNReal.ofReal_toReal_le

end

end Algsuperdiff.Section4.Provider.Holder
