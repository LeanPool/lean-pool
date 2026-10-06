/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildIntegral
public import Mathlib.Analysis.Convex.Integral

/-!
# Divergence free range of the mild Stokes integral

The closed Leray data space is preserved by the time-integrated Stokes term
in lem:reg-local-mild.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
@[expose]
def mildIntegralCoordinateEquiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

theorem mildIntegralWeakPairing_integrable (a : Vec3 → Vec3)
    (ha : CKN.IsWeakDivFreeL2 a)
    (ψ : CKN.WeakTestFunction (Set.univ : Set Vec3)) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, a x i * ψ.partialDeriv i x) volume := by
  have haCoord (i : Fin 3) : MemLp (fun x : Vec3 => a x i) 2 volume := by
    have hmeas := (continuous_apply i).comp_aestronglyMeasurable ha.1.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂volume, ‖a x i‖ ≤ (1 : ℝ) * ‖a x‖ := by
      filter_upwards [] with x
      simpa using norm_le_pi_norm (a x) i
    exact ha.1.of_le_mul (c := 1) hmeas hbound
  have htestCoord (i : Fin 3) :
      MemLp (fun x : Vec3 => ψ.partialDeriv i x) 2 volume := by
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => ψ.partialDeriv i x) := by
      change ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ.toFun i)
      exact contDiff_spatialDeriv_smooth ψ.contDiff i
    have hcompact : HasCompactSupport (fun x : Vec3 => ψ.partialDeriv i x) := by
      change HasCompactSupport (fun x =>
        (fderiv ℝ ψ.toFun x) (CKN.basisVec i))
      exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)
    exact hsmooth.continuous.memLp_of_hasCompactSupport hcompact
  have hprod (i : Fin 3) :
      Integrable (fun x : Vec3 => a x i * ψ.partialDeriv i x) volume :=
    (haCoord i).integrable_mul (htestCoord i)
  exact integrable_finsetSum Finset.univ
    (f := fun i x => a x i * ψ.partialDeriv i x) (by
      intro i hi
      exact hprod i)

@[expose]
def mildIntegralJSubmodule : Submodule ℝ RealVectorL2 where
  carrier := {u | RegularizedMildJData u}
  zero_mem' := by
    change CKN.IsInJ (realVectorL2Representative (0 : RealVectorL2))
    apply CKN.weakDivFreeL2_isInJ
    refine ⟨?_, ?_⟩
    · have hcomp : MemLp
          (fun x : Vec3 => (0 : RealVectorL2) (WithLp.toLp 2 x)) 2 volume :=
        (Lp.memLp (0 : RealVectorL2)).comp_measurePreserving
          vec3ToL2Vec3_measurePreserving
      change MemLp (fun x : Vec3 => mildIntegralCoordinateEquiv
        ((0 : RealVectorL2) (WithLp.toLp 2 x))) 2 volume
      exact hcomp.continuousLinearMap_comp
        mildIntegralCoordinateEquiv.toContinuousLinearMap
    · intro ψ
      simp [realVectorL2Representative]
  add_mem' := by
    intro u v hu hv
    change CKN.IsInJ (realVectorL2Representative u) at hu
    change CKN.IsInJ (realVectorL2Representative v) at hv
    change CKN.IsInJ (realVectorL2Representative (u + v))
    apply CKN.weakDivFreeL2_isInJ
    rcases (CKN.isInJ_iff_weakDivFree).1 hu with ⟨hLu, hPu⟩
    rcases (CKN.isInJ_iff_weakDivFree).1 hv with ⟨hLv, hPv⟩
    have hrep : realVectorL2Representative (u + v) =ᵐ[volume]
        realVectorL2Representative u + realVectorL2Representative v := by
      have hLp : (fun x : L2Vec3 => (u + v) x) =ᵐ[volume]
          fun x => u x + v x := Lp.coeFn_add u v
      have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hLp
      filter_upwards [htransport] with x hx
      change mildIntegralCoordinateEquiv ((u + v) (WithLp.toLp 2 x)) =
        mildIntegralCoordinateEquiv (u (WithLp.toLp 2 x)) +
          mildIntegralCoordinateEquiv (v (WithLp.toLp 2 x))
      rw [hx, mildIntegralCoordinateEquiv.map_add]
    have htargetLp : MemLp (realVectorL2Representative (u + v)) 2 volume := by
      have hcomp : MemLp
          (fun x : Vec3 => (u + v) (WithLp.toLp 2 x)) 2 volume :=
        (Lp.memLp (u + v)).comp_measurePreserving vec3ToL2Vec3_measurePreserving
      change MemLp
        (fun x : Vec3 => mildIntegralCoordinateEquiv ((u + v) (WithLp.toLp 2 x)))
        2 volume
      exact hcomp.continuousLinearMap_comp
        mildIntegralCoordinateEquiv.toContinuousLinearMap
    have hsumLp : MemLp
        (fun x : Vec3 => realVectorL2Representative u x +
          realVectorL2Representative v x) 2 volume := hLu.add hLv
    have hLp := hsumLp.congr_norm htargetLp.aestronglyMeasurable
      (hrep.mono fun x hx => by simp [hx])
    refine ⟨hLp, ?_⟩
    intro ψ
    have hIntu := mildIntegralWeakPairing_integrable
      (realVectorL2Representative u) ⟨hLu, hPu⟩ ψ
    have hIntv := mildIntegralWeakPairing_integrable
      (realVectorL2Representative v) ⟨hLv, hPv⟩ ψ
    calc
      ∫ x : Vec3, ∑ i : Fin 3,
          realVectorL2Representative (u + v) x i * ψ.partialDeriv i x =
        ∫ x : Vec3, (∑ i : Fin 3,
            realVectorL2Representative u x i * ψ.partialDeriv i x) +
          (∑ i : Fin 3,
            realVectorL2Representative v x i * ψ.partialDeriv i x) := by
              apply integral_congr_ae
              filter_upwards [hrep] with x hx
              rw [hx]
              simp [Finset.sum_add_distrib, add_mul]
      _ = 0 := by rw [integral_add hIntu hIntv, hPu ψ, hPv ψ]; simp
  smul_mem' := by
    intro c u hu
    change CKN.IsInJ (realVectorL2Representative u) at hu
    change CKN.IsInJ (realVectorL2Representative (c • u))
    apply CKN.weakDivFreeL2_isInJ
    rcases (CKN.isInJ_iff_weakDivFree).1 hu with ⟨hLu, hPu⟩
    have hrep : realVectorL2Representative (c • u) =ᵐ[volume]
        c • realVectorL2Representative u := by
      have hLp : (fun x : L2Vec3 => (c • u) x) =ᵐ[volume]
          fun x => c • u x := Lp.coeFn_smul c u
      have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hLp
      filter_upwards [htransport] with x hx
      change mildIntegralCoordinateEquiv ((c • u) (WithLp.toLp 2 x)) =
        c • mildIntegralCoordinateEquiv (u (WithLp.toLp 2 x))
      rw [hx, mildIntegralCoordinateEquiv.map_smul]
    have htargetLp : MemLp (realVectorL2Representative (c • u)) 2 volume := by
      have hcomp : MemLp
          (fun x : Vec3 => (c • u) (WithLp.toLp 2 x)) 2 volume :=
        (Lp.memLp (c • u)).comp_measurePreserving vec3ToL2Vec3_measurePreserving
      change MemLp
        (fun x : Vec3 => mildIntegralCoordinateEquiv ((c • u) (WithLp.toLp 2 x)))
        2 volume
      exact hcomp.continuousLinearMap_comp
        mildIntegralCoordinateEquiv.toContinuousLinearMap
    have hsmulLp : MemLp
        (fun x : Vec3 => c • realVectorL2Representative u x) 2 volume :=
      hLu.const_smul c
    have hLp := hsmulLp.congr_norm htargetLp.aestronglyMeasurable
      (hrep.mono fun x hx => by simp [hx])
    refine ⟨hLp, ?_⟩
    intro ψ
    have hInt := mildIntegralWeakPairing_integrable
      (realVectorL2Representative u) ⟨hLu, hPu⟩ ψ
    calc
      ∫ x : Vec3, ∑ i : Fin 3,
          realVectorL2Representative (c • u) x i * ψ.partialDeriv i x =
        ∫ x : Vec3, c *
          (∑ i : Fin 3,
            realVectorL2Representative u x i * ψ.partialDeriv i x) := by
              apply integral_congr_ae
              filter_upwards [hrep] with x hx
              rw [hx]
              calc
                ∑ i : Fin 3, (c • realVectorL2Representative u x) i *
                    ψ.partialDeriv i x =
                  ∑ i : Fin 3, c *
                    (realVectorL2Representative u x i * ψ.partialDeriv i x) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      simp only [Pi.smul_apply, smul_eq_mul]
                      ring
                _ = c * ∑ i : Fin 3,
                    realVectorL2Representative u x i * ψ.partialDeriv i x :=
                  (Finset.mul_sum Finset.univ _ c).symm
      _ = 0 := by rw [integral_const_mul, hPu ψ, mul_zero]

/-- The real Leray data used in the regularized mild flow are closed under
subtraction. -/
theorem regularizedMildJData_sub {u v : RealVectorL2}
    (hu : RegularizedMildJData u) (hv : RegularizedMildJData v) :
    RegularizedMildJData (u - v) := by
  have hu' : u ∈ mildIntegralJSubmodule := hu
  have hv' : v ∈ mildIntegralJSubmodule := hv
  exact mildIntegralJSubmodule.sub_mem hu' hv'

/-- The Stokes time integral takes values in the closed divergence free
space used for trajectories in lem:reg-local-mild. -/
theorem regularizedMildStokesIntegral_isInJ
    (F : ℝ → RealTensorL2) (hF : Continuous F) (C T t : ℝ)
    (hFC : ∀ s, ‖F s‖ ≤ C) (hC : 0 ≤ C)
    (hT : 0 ≤ T) (hTpos : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    RegularizedMildJData (regularizedMildStokesIntegral F t) := by
  let G : ℝ → RealVectorL2 := fun τ =>
    mildShiftedStokesIntegrand F t τ
  have hGint : IntervalIntegrable G volume 0 T :=
    mildShiftedStokesIntegrand_intervalIntegrable F hF C hFC hC T t hT
  have hGOn : IntegrableOn G (Set.Ioc 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hGint
  have hmember : ∀ᵐ τ ∂(volume.restrict (Set.Ioc 0 T)),
      G τ ∈ mildIntegralJSubmodule.carrier := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ _hτ
    change RegularizedMildJData (G τ)
    by_cases h : 0 < τ ∧ τ < t
    · simpa [G, mildShiftedStokesIntegrand, h, RegularizedMildJData] using
        realStokesOperator_isInJ h.1 (F (t - τ))
    · have hz : RegularizedMildJData (0 : RealVectorL2) := by
        change (0 : RealVectorL2) ∈ mildIntegralJSubmodule
        exact mildIntegralJSubmodule.zero_mem
      simpa [G, mildShiftedStokesIntegrand, h] using hz
  have hmassReal : volume.real (Set.Ioc (0 : ℝ) T) = T := by
    rw [Real.volume_real_Ioc_of_le hT]
    simp
  have hmassNeZero : volume (Set.Ioc (0 : ℝ) T) ≠ 0 := by
    rw [Real.volume_Ioc]
    simp only [sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr hTpos
  have hmassNeTop : volume (Set.Ioc (0 : ℝ) T) ≠ ∞ := by
    rw [Real.volume_Ioc]
    simp only [sub_zero]
    exact ENNReal.ofReal_ne_top
  have havg :
      (⨍ τ in Set.Ioc (0 : ℝ) T, G τ ∂volume) ∈
        mildIntegralJSubmodule.carrier :=
    mildIntegralJSubmodule.convex.set_average_mem
      regularizedMildJData_isClosed hmassNeZero hmassNeTop hmember hGOn
  have havgEq :
      (⨍ τ in Set.Ioc (0 : ℝ) T, G τ ∂volume) =
        (T⁻¹) • ∫ τ in Set.Ioc (0 : ℝ) T, G τ ∂volume := by
    rw [setAverage_eq, hmassReal]
  have hscaled := mildIntegralJSubmodule.smul_mem T havg
  rw [havgEq] at hscaled
  have hsetInt :
      (∫ τ in Set.Ioc (0 : ℝ) T, G τ ∂volume) ∈
        mildIntegralJSubmodule.carrier := by
    have hcancel :
        T • (T⁻¹ • ∫ τ in Set.Ioc (0 : ℝ) T, G τ ∂volume) =
          ∫ τ in Set.Ioc (0 : ℝ) T, G τ ∂volume := by
      rw [smul_smul]
      simp [hTpos.ne']
    rw [hcancel] at hscaled
    exact hscaled
  have hintervalInt :
      (∫ τ in (0 : ℝ)..T, G τ) ∈ mildIntegralJSubmodule.carrier := by
    rw [intervalIntegral.integral_of_le hT]
    exact hsetInt
  have hshift := regularizedMildStokesIntegral_eq_shifted
    T t hT ht htT hF C hFC hC
  change regularizedMildStokesIntegral F t ∈
    mildIntegralJSubmodule.carrier
  rw [hshift]
  exact hintervalInt

end CKN.Leray

end
