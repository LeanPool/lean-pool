/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyPrim

/-!
# Mollifier limits for the localized vorticity energy

The standard mollifiers `ρₙ` of radius `1/(n+1)` are smooth compact kernels of
unit `L¹` norm. For a square-integrable spatial field `h`,
`∫ (ρₙ ⋆ h - h)² → 0`. For a square-integrable field on the slab, the
time-integrated version holds by dominated convergence
(`lem:localized-vorticity-energy` of the Escauriaza–Seregin–Šverák manuscript).
-/

public section

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

/-- The squared `L²` integral is the square of the `L²` seminorm. -/
theorem vl_integral_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : MemLp g 2 μ) : ∫ x, (g x) ^ 2 ∂μ = (eLpNorm g 2 μ).toReal ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have hI : ∫ x, ‖g x‖ ^ (ENNReal.toReal 2) ∂μ = ∫ x, (g x) ^ 2 ∂μ := by
    congr 1
    funext x
    rw [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two, sq_abs]
  rw [hI, ENNReal.toReal_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul
    (integral_nonneg fun x => sq_nonneg _)]
  norm_num

/-- The `L²` norm of a representative, squared. -/
theorem vl_norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : MemLp g 2 μ) : ‖hg.toLp g‖ ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
  rw [Lp.norm_toLp, vl_integral_sq_eq hg]

/-- The mollifier of radius `1 / (n + 1)`. -/
@[expose]
def vlMoll (n : ℕ) : Vec3 → ℝ :=
  CKN.mollifier (d := 3) (1 / ((n : ℝ) + 1)) (by positivity)

theorem vlMoll_kernel (n : ℕ) : IsVlKernel (vlMoll n) :=
  ⟨CKN.mollifier_contDiff (d := 3) _, CKN.mollifier_hasCompactSupport (d := 3) _⟩

theorem vlMoll_abs_integral (n : ℕ) : ∫ y, |vlMoll n y| = 1 := by
  have h : (fun y => |vlMoll n y|) = vlMoll n := by
    funext y
    exact abs_of_nonneg (CKN.mollifier_nonneg (d := 3) _ y)
  rw [h]
  exact CKN.mollifier_integral_one (d := 3) _

theorem vlMoll_sq_le (n : ℕ) {h : Vec3 → ℝ} (hh : MemLp h 2 volume) :
    ∫ x, (vlConv (vlMoll n) h x) ^ 2 ≤ ∫ x, (h x) ^ 2 := by
  have := vlConv_integral_sq_le (vlMoll_kernel n) hh
  rwa [vlMoll_abs_integral, one_pow, one_mul] at this

theorem vlMoll_tendsto {h : Vec3 → ℝ} (hh : MemLp h 2 volume) :
    Tendsto (fun n => ∫ x, (vlConv (vlMoll n) h x - h x) ^ 2) atTop (𝓝 0) := by
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmoll := CKN.tendsto_eLpNorm_sub_zero_mollify (p := 2) (by norm_num) (by norm_num) hh
    hε (fun n => by positivity)
  have hmem : ∀ n : ℕ, MemLp (fun x => vlConv (vlMoll n) h x - h x) 2 volume :=
    fun n => (vlConv_memLp (vlMoll_kernel n) hh).sub hh
  have heq : (fun n => ∫ x, (vlConv (vlMoll n) h x - h x) ^ 2) =
      fun n : ℕ => (eLpNorm (fun x => CKN.mollify h (1 / ((n : ℝ) + 1))
        (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) x - h x) 2 volume).toReal ^ 2 := by
    funext n
    exact vl_integral_sq_eq (hmem n)
  rw [heq]
  have hlim := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmoll).pow 2
  simpa using hlim

/-- The time-integrated mollifier limit on a slab. -/
theorem vlMoll_slab_tendsto {a τ : ℝ} {g : Vec3 × ℝ → ℝ} (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) :
    Tendsto (fun n => ∫ s in Ioo a τ, ∫ x, (vlConvT (vlMoll n) g x s - g (x, s)) ^ 2)
      atTop (𝓝 0) := by
  have hzero : (0 : ℝ) = ∫ s in Ioo a τ, (0 : ℝ) := by simp
  rw [hzero]
  refine tendsto_integral_of_dominated_convergence (fun s => 4 * ∫ x, (g (x, s)) ^ 2) ?_ ?_ ?_ ?_
  · intro n
    have hm : StronglyMeasurable (fun p : Vec3 × ℝ =>
        (vlConvT (vlMoll n) g p.1 p.2 - g p) ^ 2) :=
      ((vlConvT_stronglyMeasurable (vlMoll_kernel n).continuous hgm).sub hgm).pow 2
    exact (hm.integral_prod_left' (μ := (volume : Measure Vec3))).aestronglyMeasurable
  · exact (vlSlab_sliceSq_integrableOn hg).const_mul 4
  · intro n
    filter_upwards [vlSlab_slice_memLp hgm hg] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
    have hc := vlConv_memLp (vlMoll_kernel n) hs
    have hpt : ∀ x, (vlConvT (vlMoll n) g x s - g (x, s)) ^ 2 ≤
        2 * (vlConvT (vlMoll n) g x s) ^ 2 + 2 * (g (x, s)) ^ 2 := fun x => by
      nlinarith only [sq_nonneg (vlConvT (vlMoll n) g x s + g (x, s))]
    have hA2 : Integrable (fun x => 2 * (vlConvT (vlMoll n) g x s) ^ 2) volume :=
      hc.integrable_sq.const_mul 2
    have hB2 : Integrable (fun x => 2 * (g (x, s)) ^ 2) volume :=
      hs.integrable_sq.const_mul 2
    have hdiff : Integrable (fun x => (vlConvT (vlMoll n) g x s - g (x, s)) ^ 2) volume :=
      (hc.sub hs).integrable_sq
    calc
      ∫ x, (vlConvT (vlMoll n) g x s - g (x, s)) ^ 2 ≤
          ∫ x, (2 * (vlConvT (vlMoll n) g x s) ^ 2 + 2 * (g (x, s)) ^ 2) :=
        integral_mono hdiff (hA2.add hB2) hpt
      _ = 2 * (∫ x, (vlConvT (vlMoll n) g x s) ^ 2) + 2 * ∫ x, (g (x, s)) ^ 2 := by
        rw [integral_add hA2 hB2, integral_const_mul, integral_const_mul]
      _ ≤ 2 * (∫ x, (g (x, s)) ^ 2) + 2 * ∫ x, (g (x, s)) ^ 2 := by
        have hle : ∫ x, (vlConvT (vlMoll n) g x s) ^ 2 ≤ ∫ x, (g (x, s)) ^ 2 :=
          vlMoll_sq_le n hs
        linarith only [hle]
      _ = 4 * ∫ x, (g (x, s)) ^ 2 := by ring
  · filter_upwards [vlSlab_slice_memLp hgm hg] with s hs
    exact vlMoll_tendsto hs

/-- A difference of two mollifications is controlled by the two mollifier
errors. -/
theorem vlMoll_sub_sq_le (n m : ℕ) {h : Vec3 → ℝ} (hh : MemLp h 2 volume) :
    ∫ x, (vlConv (vlMoll n - vlMoll m) h x) ^ 2 ≤
      2 * (∫ x, (vlConv (vlMoll n) h x - h x) ^ 2) +
        2 * ∫ x, (vlConv (vlMoll m) h x - h x) ^ 2 := by
  have hloc : LocallyIntegrable h volume := hh.locallyIntegrable (by norm_num)
  rw [vlConv_sub_kernel (vlMoll_kernel n) (vlMoll_kernel m) hloc]
  have hn : MemLp (fun x => vlConv (vlMoll n) h x - h x) 2 volume :=
    (vlConv_memLp (vlMoll_kernel n) hh).sub hh
  have hm : MemLp (fun x => vlConv (vlMoll m) h x - h x) 2 volume :=
    (vlConv_memLp (vlMoll_kernel m) hh).sub hh
  have hn2 : Integrable (fun x => 2 * (vlConv (vlMoll n) h x - h x) ^ 2) volume :=
    hn.integrable_sq.const_mul 2
  have hm2 : Integrable (fun x => 2 * (vlConv (vlMoll m) h x - h x) ^ 2) volume :=
    hm.integrable_sq.const_mul 2
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hn2 hm2]
  refine integral_mono ((hn.sub hm).integrable_sq.congr (Eventually.of_forall fun x => ?_))
    (hn2.add hm2) (fun x => ?_)
  · simp only [Pi.sub_apply]
    ring
  · simp only [Pi.sub_apply]
    nlinarith only [sq_nonneg (vlConv (vlMoll n) h x - h x + (vlConv (vlMoll m) h x - h x))]

/-- The slice mollifier error of a slab field. -/
@[expose]
def vlMollErr (n : ℕ) (g : Vec3 × ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x, (vlConvT (vlMoll n) g x s - g (x, s)) ^ 2


theorem vlMollErr_integrableOn {a τ : ℝ} (n : ℕ) {g : Vec3 × ℝ → ℝ}
    (hgm : StronglyMeasurable g) (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) :
    IntegrableOn (fun s => vlMollErr n g s) (Ioo a τ) volume := by
  have hdiff : MemLp (fun p : Vec3 × ℝ => vlConvT (vlMoll n) g p.1 p.2 - g p) 2
      (volume.restrict (vlSlab a τ)) := (vlConvT_memLp (vlMoll_kernel n) hgm hg).sub hg
  have h := vlSlab_sliceSq_integrableOn hdiff
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioo
  rfl

end CKN

end
