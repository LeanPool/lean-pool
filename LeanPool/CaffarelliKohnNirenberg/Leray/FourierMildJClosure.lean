/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildJSpace
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Topology.Sequences

/-!
# Closedness of the regularized mild data space

The divergence-free carrier used in `lem:reg-local-mild` is closed in the
real spatial `L²` norm.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The continuous coordinate identification for the Hilbert vector space used by mild
solutions. -/
@[expose]
def mildCoordinateEquiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

private theorem realVectorL2Representative_memLp (u : RealVectorL2) :
    MemLp (realVectorL2Representative u) 2 volume := by
  have hcomp : MemLp (fun x : Vec3 => u (WithLp.toLp 2 x)) 2 volume :=
    (Lp.memLp u).comp_measurePreserving vec3ToL2Vec3_measurePreserving
  change MemLp (fun x : Vec3 => mildCoordinateEquiv (u (WithLp.toLp 2 x))) 2 volume
  exact hcomp.continuousLinearMap_comp mildCoordinateEquiv.toContinuousLinearMap

private theorem realVectorL2Representative_sub_norm_le_ae (u v : RealVectorL2) :
    ∀ᵐ x : Vec3 ∂volume,
      ‖realVectorL2Representative u x - realVectorL2Representative v x‖ ≤
        ‖(u - v) (WithLp.toLp 2 x)‖ := by
  have hsub := Lp.coeFn_sub u v
  have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hsub
  filter_upwards [htransport] with x hx
  change ‖mildCoordinateEquiv (u (WithLp.toLp 2 x)) -
      mildCoordinateEquiv (v (WithLp.toLp 2 x))‖ ≤
    ‖(u - v) (WithLp.toLp 2 x)‖
  calc
    ‖mildCoordinateEquiv (u (WithLp.toLp 2 x)) -
        mildCoordinateEquiv (v (WithLp.toLp 2 x))‖ =
      ‖mildCoordinateEquiv (u (WithLp.toLp 2 x) - v (WithLp.toLp 2 x))‖ := by
        rw [← mildCoordinateEquiv.map_sub]
    _ = ‖mildCoordinateEquiv ((u - v) (WithLp.toLp 2 x))‖ := by
      congr 1
      exact congrArg mildCoordinateEquiv hx.symm
    _ ≤ vec3EuclideanNorm
        (mildCoordinateEquiv ((u - v) (WithLp.toLp 2 x))) :=
      norm_le_vec3EuclideanNorm _
    _ = ‖(u - v) (WithLp.toLp 2 x)‖ := by
      rw [mildCoordinateEquiv, vec3EuclideanNorm_eq_l2]
      change ‖WithLp.toLp 2 (WithLp.ofLp ((u - v) (WithLp.toLp 2 x)))‖ =
        ‖(u - v) (WithLp.toLp 2 x)‖
      simp

/-- The coordinate representative is controlled by the `L²` distance used
for the closed divergence-free carrier in `lem:reg-local-mild`. -/
theorem realVectorL2Representative_sub_eLpNorm_le (u v : RealVectorL2) :
    eLpNorm (realVectorL2Representative u - realVectorL2Representative v)
        (2 : ℝ≥0∞) volume ≤ eLpNorm (u - v) 2 volume := by
  have hrep : AEStronglyMeasurable
      (fun x : Vec3 => realVectorL2Representative u x -
        realVectorL2Representative v x) volume :=
    (realVectorL2Representative_memLp u).sub
      (realVectorL2Representative_memLp v) |>.aestronglyMeasurable
  have hnorm := realVectorL2Representative_sub_norm_le_ae u v
  have hbound : ∀ᵐ x ∂volume,
      ‖realVectorL2Representative u x - realVectorL2Representative v x‖ₑ ≤
        (1 : ℝ≥0∞) * ‖(u - v) (WithLp.toLp 2 x)‖ₑ := by
    filter_upwards [hnorm] with x hx
    have hnn : ‖realVectorL2Representative u x - realVectorL2Representative v x‖₊ ≤
        ‖(u - v) (WithLp.toLp 2 x)‖₊ := by exact_mod_cast hx
    simpa [enorm] using (ENNReal.coe_le_coe.mpr hnn)
  calc
    eLpNorm (realVectorL2Representative u - realVectorL2Representative v) 2 volume ≤
        eLpNorm (fun x : Vec3 => (u - v) (WithLp.toLp 2 x)) 2 volume := by
      change eLpNorm (fun x : Vec3 => realVectorL2Representative u x -
          realVectorL2Representative v x) 2 volume ≤ _
      simpa only [one_smul] using eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
        (c := 1) hrep hbound (2 : ℝ≥0∞)
    _ = eLpNorm (u - v) 2 volume := by
      exact eLpNorm_comp_measurePreserving
        ((Lp.memLp (u - v)).aestronglyMeasurable)
        vec3ToL2Vec3_measurePreserving

theorem mildWeakPairing_integrable (a : Vec3 → Vec3)
    (ha : MemLp a (2 : ℝ≥0∞) volume)
    (ψ : CKN.WeakTestFunction (Set.univ : Set Vec3)) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, a x i * ψ.partialDeriv i x) volume := by
  have haCoord (i : Fin 3) : MemLp (fun x : Vec3 => a x i) 2 volume := by
    have hmeas := (continuous_apply i).comp_aestronglyMeasurable ha.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂volume, ‖a x i‖ ≤ (1 : ℝ) * ‖a x‖ := by
      filter_upwards [] with x
      simpa using norm_le_pi_norm (a x) i
    exact ha.of_le_mul (c := 1) hmeas hbound
  have htestCoord (i : Fin 3) : MemLp (fun x : Vec3 => ψ.partialDeriv i x) 2 volume := by
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => ψ.partialDeriv i x) := by
      change ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ.toFun i)
      exact contDiff_spatialDeriv_smooth ψ.contDiff i
    have hcompact : HasCompactSupport (fun x : Vec3 => ψ.partialDeriv i x) := by
      change HasCompactSupport (fun x => (fderiv ℝ ψ.toFun x) (CKN.basisVec i))
      exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)
    exact hsmooth.continuous.memLp_of_hasCompactSupport hcompact
  have hprod (i : Fin 3) :
      Integrable (fun x : Vec3 => a x i * ψ.partialDeriv i x) volume :=
    (haCoord i).integrable_mul (htestCoord i)
  exact integrable_finsetSum Finset.univ (f := fun i x => a x i * ψ.partialDeriv i x) (by
      intro i hi
      exact hprod i)

/-- The subspace of real `L²` velocities satisfying the regularized mild-solution `J` condition. -/
@[expose]
def regularizedMildJSubmodule : Submodule ℝ RealVectorL2 where
  carrier := {u | RegularizedMildJData u}
  zero_mem' := by
    change RegularizedMildJData (0 : RealVectorL2)
    change CKN.IsInJ (realVectorL2Representative (0 : RealVectorL2))
    refine (CKN.isInJ_iff_weakDivFree).2 ⟨
      realVectorL2Representative_memLp (0 : RealVectorL2), ?_⟩
    intro ψ
    simp [realVectorL2Representative]
  add_mem' := by
    intro u v hu hv
    change CKN.IsInJ (realVectorL2Representative u) at hu
    change CKN.IsInJ (realVectorL2Representative v) at hv
    change CKN.IsInJ (realVectorL2Representative (u + v))
    apply (CKN.isInJ_iff_weakDivFree).2
    rcases (CKN.isInJ_iff_weakDivFree).1 hu with ⟨hLu, hPu⟩
    rcases (CKN.isInJ_iff_weakDivFree).1 hv with ⟨hLv, hPv⟩
    have hrep : realVectorL2Representative (u + v) =ᵐ[volume]
        realVectorL2Representative u + realVectorL2Representative v := by
      have hLp : (fun x : L2Vec3 => (u + v) x) =ᵐ[volume]
          fun x => u x + v x := Lp.coeFn_add u v
      have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hLp
      filter_upwards [htransport] with x hx
      change mildCoordinateEquiv ((u + v) (WithLp.toLp 2 x)) =
        mildCoordinateEquiv (u (WithLp.toLp 2 x)) +
          mildCoordinateEquiv (v (WithLp.toLp 2 x))
      rw [hx, mildCoordinateEquiv.map_add]
    have htargetLp : MemLp (realVectorL2Representative (u + v)) 2 volume :=
      realVectorL2Representative_memLp (u + v)
    have hsumLp : MemLp
        (fun x : Vec3 => realVectorL2Representative u x +
          realVectorL2Representative v x) 2 volume := hLu.add hLv
    have hLp := hsumLp.congr_norm htargetLp.aestronglyMeasurable
      (hrep.mono fun x hx => by simp [hx])
    refine ⟨hLp, ?_⟩
    · intro ψ
      have hIntu := mildWeakPairing_integrable (realVectorL2Representative u) hLu ψ
      have hIntv := mildWeakPairing_integrable (realVectorL2Representative v) hLv ψ
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
        _ = _ := by rw [integral_add hIntu hIntv, hPu ψ, hPv ψ]; simp
  smul_mem' := by
    intro c u hu
    change CKN.IsInJ (realVectorL2Representative u) at hu
    change CKN.IsInJ (realVectorL2Representative (c • u))
    apply (CKN.isInJ_iff_weakDivFree).2
    rcases (CKN.isInJ_iff_weakDivFree).1 hu with ⟨hLu, hPu⟩
    have hrep : realVectorL2Representative (c • u) =ᵐ[volume]
        c • realVectorL2Representative u := by
      have hLp : (fun x : L2Vec3 => (c • u) x) =ᵐ[volume]
          fun x => c • u x := Lp.coeFn_smul c u
      have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hLp
      filter_upwards [htransport] with x hx
      change mildCoordinateEquiv ((c • u) (WithLp.toLp 2 x)) =
        c • mildCoordinateEquiv (u (WithLp.toLp 2 x))
      rw [hx, mildCoordinateEquiv.map_smul]
    have htargetLp : MemLp (realVectorL2Representative (c • u)) 2 volume :=
      realVectorL2Representative_memLp (c • u)
    have hsmulLp : MemLp
        (fun x : Vec3 => c • realVectorL2Representative u x) 2 volume := hLu.const_smul c
    have hLp := hsmulLp.congr_norm htargetLp.aestronglyMeasurable
      (hrep.mono fun x hx => by simp [hx])
    refine ⟨hLp, ?_⟩
    · intro ψ
      have hInt := mildWeakPairing_integrable (realVectorL2Representative u) hLu ψ
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
        _ = _ := by rw [integral_const_mul, hPu ψ, mul_zero]

/-- The set of real `L²` fields in `J` is a closed linear subspace, as needed
for the fixed-point space in `lem:reg-local-mild`. -/
theorem regularizedMildJData_isClosed :
    IsClosed {u : RealVectorL2 | RegularizedMildJData u} := by
  rw [← isSeqClosed_iff_isClosed]
  intro x u hseq hlim
  apply CKN.isInJ_closed_under_L2_limit
    (realVectorL2Representative_memLp u)
    (fun n => by simpa [RegularizedMildJData] using hseq n)
  have hnorm : Tendsto (fun n : ℕ => ‖x n - u‖) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
    have hsub : Tendsto (fun n : ℕ => x n - u) atTop (𝓝 (u - u)) := hlim.sub hconst
    have hsub' : Tendsto (fun n : ℕ => x n - u) atTop (𝓝 0) := by simpa using hsub
    have hn := continuous_norm.continuousAt.tendsto.comp hsub'
    convert hn using 1 <;> ext n <;> simp
  have hofReal : Tendsto (fun n : ℕ => ENNReal.ofReal ‖x n - u‖)
      atTop (𝓝 0) := by simpa using ENNReal.tendsto_ofReal hnorm
  have hcoord : Tendsto (fun n : ℕ =>
      eLpNorm (realVectorL2Representative (x n) -
        realVectorL2Representative u) 2 volume) atTop (𝓝 0) := by
    have hzero : (fun _ : ℕ => (0 : ℝ≥0∞)) ≤ fun n =>
        eLpNorm (realVectorL2Representative (x n) -
          realVectorL2Representative u) 2 volume := by
      intro n
      exact zero_le
    have hupper : (fun n => eLpNorm (realVectorL2Representative (x n) -
        realVectorL2Representative u) 2 volume) ≤
        fun n => ENNReal.ofReal ‖x n - u‖ := by
      intro n
      have hle := realVectorL2Representative_sub_eLpNorm_le (x n) u
      have hfinite : eLpNorm (x n - u) 2 volume ≠ ∞ :=
        (Lp.memLp (x n - u)).eLpNorm_ne_top
      have hEq : eLpNorm (x n - u) 2 volume = ENNReal.ofReal ‖x n - u‖ := by
        calc
          eLpNorm (x n - u) 2 volume =
              ENNReal.ofReal (ENNReal.toReal (eLpNorm (x n - u) 2 volume)) :=
            (ENNReal.ofReal_toReal hfinite).symm
          _ = ENNReal.ofReal ‖x n - u‖ := by rw [Lp.norm_def]
      rw [hEq] at hle
      exact hle
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hofReal hzero hupper
  exact hcoord

end CKN.Leray

end
