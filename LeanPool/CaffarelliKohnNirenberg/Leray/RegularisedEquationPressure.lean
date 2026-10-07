/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureLp
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Pressure pairing for the regularized equation

The canonical spatial pressure has the distributional Laplacian required in
(R4) of `thm:regularised`.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

local instance : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩

local instance : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
    (ENNReal.ofReal (2 : ℝ)) 1 := by
  have h : (2 : ℝ).HolderTriple 2 1 := by
    constructor <;> norm_num
  simpa using h.ennrealOfReal

private theorem regularisedPressure_derivative_compactSupport
    {f : Vec3 → ℝ} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (spatialDeriv f i) :=
  hf.fderiv_apply (𝕜 := ℝ) (basisVec i)

private theorem regularisedPressure_laplacian_compactSupport
    {ψ : Vec3 → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (spatialLaplacian ψ) := by
  change HasCompactSupport (fun x => ∑ k : Fin 3,
    spatialDeriv (spatialDeriv ψ k) k x)
  convert
    ((regularisedPressure_derivative_compactSupport
        (regularisedPressure_derivative_compactSupport hψc 0) 0).add
      ((regularisedPressure_derivative_compactSupport
          (regularisedPressure_derivative_compactSupport hψc 1) 1).add
        (regularisedPressure_derivative_compactSupport
          (regularisedPressure_derivative_compactSupport hψc 2) 2))) using 1
  funext x
  simp [Fin.sum_univ_succ, Pi.add_apply]

private theorem regularisedPressure_mixedSecond_compactSupport
    {ψ : Vec3 → ℝ} (hψc : HasCompactSupport ψ) (i j : Fin 3) :
    HasCompactSupport (mixedSecond ψ i j) :=
  regularisedPressure_derivative_compactSupport
    (regularisedPressure_derivative_compactSupport hψc j) i

private theorem regularisedPressure_lp_finset_sum_ae
    (s : Finset (Fin 3))
    (f : Fin 3 → Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) :
    ((∑ i ∈ s, f i : Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) : Vec3 → ℝ) =ᵐ[volume]
      fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => filter_upwards [] with x; simp
  | @insert a s ha hs =>
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), hs] with x hAdd hSum
      calc
        ((∑ i ∈ insert a s, f i : Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) : Vec3 → ℝ) x =
            f a x + (∑ i ∈ s, f i : Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) x := by
          rw [Finset.sum_insert ha]
          exact hAdd
        _ = f a x + ∑ i ∈ s, f i x := by rw [hSum]
        _ = ∑ i ∈ insert a s, f i x := by rw [Finset.sum_insert ha]

/-- The canonical regularized pressure slice has the signed Laplacian pairing
in (R4) of `thm:regularised`. -/
theorem regularisedPressureSlice_riesz_laplacian_pairing
    (F : Fin 3 → Fin 3 → Vec3 → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (2 : ℝ)) volume)
    (ψ : Vec3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x : Vec3,
      rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
        (fun i j => (hF i j).toLp (F i j)) x * spatialLaplacian ψ x =
      -∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : Vec3, F i j x * mixedSecond ψ i j x := by
  have hrep := rieszPressureSliceRepresentative_ae_eq (2 : ℝ)
    (by norm_num) (fun i j => (hF i j).toLp (F i j))
  have hLap : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (2 : ℝ)) volume :=
    (contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport
      (regularisedPressure_laplacian_compactSupport hψc)
  have hMixed (i j : Fin 3) :
      MemLp (mixedSecond ψ i j) (ENNReal.ofReal (2 : ℝ)) volume :=
    (contDiff_mixedSecond_smooth hψ i j).continuous.memLp_of_hasCompactSupport
      (regularisedPressure_mixedSecond_compactSupport hψc i j)
  have hLeft (i j : Fin 3) :
      Integrable (fun x : Vec3 =>
        rieszPressureOperator (2 : ℝ) (by norm_num) i j
          ((hF i j).toLp (F i j)) x * spatialLaplacian ψ x) :=
    (Lp.memLp _).integrable_mul hLap
  have hRight (i j : Fin 3) :
      Integrable (fun x : Vec3 => F i j x * mixedSecond ψ i j x) :=
    (hF i j).integrable_mul (hMixed i j)
  let R (i j : Fin 3) : Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume :=
    rieszPressureOperator (2 : ℝ) (by norm_num) i j
      ((hF i j).toLp (F i j))
  have hInner (i : Fin 3) :
      ((∑ j : Fin 3, R i j : Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) : Vec3 → ℝ) =ᵐ[volume]
        fun x => ∑ j : Fin 3, R i j x :=
    regularisedPressure_lp_finset_sum_ae Finset.univ (fun j => R i j)
  have hInnerAll : ∀ᵐ x ∂volume, ∀ i : Fin 3,
      (∑ j : Fin 3, R i j : Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) x =
        ∑ j : Fin 3, R i j x := by
    exact ae_all_iff.mpr (fun i => hInner i)
  have hOuter :
      ((∑ i : Fin 3, ∑ j : Fin 3, R i j :
          Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) : Vec3 → ℝ) =ᵐ[volume]
        fun x => ∑ i : Fin 3, ∑ j : Fin 3, R i j x := by
    have hrows := regularisedPressure_lp_finset_sum_ae Finset.univ
      (fun i => ∑ j : Fin 3, R i j)
    filter_upwards [hrows, hInnerAll] with x hxRows hxInner
    rw [hxRows]
    apply Finset.sum_congr rfl
    intro i hi
    exact hxInner i
  have hClass :
      (rieszPressureSlice (2 : ℝ) (by norm_num)
        (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) =ᵐ[volume]
        fun x => ∑ i : Fin 3, ∑ j : Fin 3, R i j x := by
    change ((∑ i : Fin 3, ∑ j : Fin 3, R i j :
      Lp ℝ (ENNReal.ofReal (2 : ℝ)) volume) : Vec3 → ℝ) =ᵐ[volume] _
    exact hOuter
  have hF2 (i j : Fin 3) : MemLp (F i j) 2 volume := by
    simpa using hF i j
  calc
    ∫ x : Vec3,
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp (F i j)) x * spatialLaplacian ψ x =
        ∫ x : Vec3,
          (rieszPressureSlice (2 : ℝ) (by norm_num)
            (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) x *
            spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      exact congrArg (fun y : ℝ => y * spatialLaplacian ψ x) hx.symm
    _ = ∫ x : Vec3,
          (∑ i : Fin 3, ∑ j : Fin 3, R i j x) * spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [hClass] with x hx
      exact congrArg (fun y : ℝ => y * spatialLaplacian ψ x) hx
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Vec3, R i j x * spatialLaplacian ψ x := by
      simp_rw [Finset.sum_mul]
      calc
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
            R i j x * spatialLaplacian ψ x) =
            ∑ i : Fin 3, ∫ x : Vec3, ∑ j : Fin 3,
              R i j x * spatialLaplacian ψ x :=
          integral_finsetSum Finset.univ (fun i _ =>
            integrable_finsetSum Finset.univ (fun j _ => hLeft i j))
        _ = ∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, R i j x * spatialLaplacian ψ x := by
          congr 1
          ext i
          exact integral_finsetSum Finset.univ (fun j _ => hLeft i j)
    _ = -∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Vec3, F i j x * mixedSecond ψ i j x := by
      calc
        (∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x : Vec3, R i j x * spatialLaplacian ψ x) =
            ∑ i : Fin 3, ∑ j : Fin 3,
              -(∫ x : Vec3, F i j x * mixedSecond ψ i j x) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact rieszPressureOperator_laplacian_pairing (2 : ℝ)
            (by norm_num) i j (F i j) (hF i j) (hF2 i j) ψ hψ hψc
        _ = -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, F i j x * mixedSecond ψ i j x := by simp

end CKN.Leray

end
