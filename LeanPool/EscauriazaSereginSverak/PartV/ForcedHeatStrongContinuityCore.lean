/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionPairing
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Identifying `Lᵖ`-continuous limits with the rough forced response

For `lem:pv-stokes`: if a curve `L : [0, τ] → Lᵖ` is continuous and agrees with
the slices of the forced heat response `Z = forcedHeat G` at almost every time,
then it agrees with them at every time of `[0, τ]`. Both pairings with a smooth
compactly supported test are continuous on `[0, τ]`, the pairing of `Z` by
`forcedHeat_pairing_continuous`, and they agree at almost every time, hence at
every time; the slices of `Z` are locally integrable, so the pairings determine
them. The strong continuity of the response in `L²` and `L³` with every-time
bounds follows.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic

local instance forcedHeatCore_factTwo : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
local instance forcedHeatCore_factThree : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩


noncomputable section

namespace ESS

/-- The slices of the rough forced heat response are locally integrable at every
time of `[0, τ]`. -/
theorem forcedHeat_slice_locallyIntegrable {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    {t : ℝ} (ht : t ∈ Icc 0 τ) (i : Fin 3) :
    LocallyIntegrable (fun x : Vec3 => forcedHeat G (x, t) i) volume := by
  have hball (R : ℝ) (hR : 0 < R) :
      IntegrableOn (fun x : Vec3 => forcedHeat G (x, t) i) (Metric.closedBall 0 R) volume := by
    let b : ContDiffBump (0 : Vec3) := ⟨R, R + 1, hR, by linarith only⟩
    let ψ : Vec3 → Vec3 := fun x => b x • (Pi.single i (1 : ℝ) : Vec3)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := b.contDiff.smul contDiff_const
    have hψc : HasCompactSupport ψ := b.hasCompactSupport.smul_right
    have hint := (forcedHeat_pairing_continuous hτ hG hsupp hψ hψc).1 t ht
    have hsum (x : Vec3) : ∑ k : Fin 3, forcedHeat G (x, t) k * ψ x k =
        forcedHeat G (x, t) i * b x := by
      simp [ψ, Pi.single_apply, mul_comm]
    simp only [hsum] at hint
    refine (hint.integrableOn (s := Metric.closedBall 0 R)).congr_fun (fun x hx => ?_)
      Metric.isClosed_closedBall.measurableSet
    simp only [b.one_of_mem_closedBall hx, mul_one]
  intro x
  refine ⟨Metric.closedBall 0 (‖x‖ + 1), ?_, hball _ (by positivity)⟩
  refine mem_of_superset (Metric.isOpen_ball.mem_nhds ?_) Metric.ball_subset_closedBall
  simp

/-- A curve in `Lᵖ`, continuous on `[0, τ]` and equal to the slices of the rough
forced heat response at almost every time, equals them at every time of
`[0, τ]`. -/
theorem forcedHeat_lp_everyTime {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (L : ℝ → Lp Vec3 p volume) (hLc : ContinuousOn L (Icc 0 τ))
    (hLae : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
      (L t : Vec3 → Vec3) =ᵐ[volume] fun x => forcedHeat G (x, t)) :
    ∀ t ∈ Icc 0 τ, (L t : Vec3 → Vec3) =ᵐ[volume] fun x => forcedHeat G (x, t) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  -- componentwise pairings agree at every time
  have hpair (i : Fin 3) (φ : Vec3 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
      (t : ℝ) (ht : t ∈ Icc 0 τ) :
      ∫ x, (L t : Vec3 → Vec3) x i * φ x = ∫ x, forcedHeat G (x, t) i * φ x := by
    have hφq : MemLp φ q volume := hφ.continuous.memLp_of_hasCompactSupport hφc
    let T : Lp Vec3 p volume →L[ℝ] ℝ :=
      ((ContinuousLinearMap.apply ℝ (E := Lp ℝ q volume) ℝ (hφq.toLp φ)).comp
        (ContinuousLinearMap.lpPairing (volume : Measure Vec3) p q
          (ContinuousLinearMap.mul ℝ ℝ))).comp
        ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).compLpL p volume)
    have hT (u : Lp Vec3 p volume) : T u = ∫ x, (u : Vec3 → Vec3) x i * φ x := by
      simp only [T, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.apply_apply]
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [ContinuousLinearMap.coeFn_compLpL
          (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ) u, MemLp.coeFn_toLp hφq] with x hx hy
      simp [hx, hy]
    let ψ : Vec3 → Vec3 := fun x => φ x • (Pi.single i (1 : ℝ) : Vec3)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.smul contDiff_const
    have hψc : HasCompactSupport ψ := hφc.smul_right
    have hsum (s : ℝ) (x : Vec3) : ∑ k : Fin 3, forcedHeat G (x, s) k * ψ x k =
        forcedHeat G (x, s) i * φ x := by
      simp [ψ, Pi.single_apply, mul_comm]
    obtain ⟨-, hZc, -⟩ := forcedHeat_pairing_continuous hτ hG hsupp hψ hψc
    simp only [hsum] at hZc
    have hAc : ContinuousOn (fun s => ∫ x, (L s : Vec3 → Vec3) x i * φ x) (Icc 0 τ) := by
      have h := T.continuous.comp_continuousOn hLc
      refine h.congr fun s _ => ?_
      simp only [Function.comp_apply, hT]
    have hae : (fun s => ∫ x, (L s : Vec3 → Vec3) x i * φ x) =ᵐ[volume.restrict (Icc 0 τ)]
        fun s => ∫ x, forcedHeat G (x, s) i * φ x := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      filter_upwards [hLae] with s hs
      exact integral_congr_ae (hs.mono fun x hx => congrArg (fun v : Vec3 => v i * φ x) hx)
    exact Measure.eqOn_Icc_of_ae_eq (μ := volume) hτ.ne hae hAc hZc ht
  intro t ht
  have hcomp (i : Fin 3) : (fun x => (L t : Vec3 → Vec3) x i) =ᵐ[volume]
      fun x => forcedHeat G (x, t) i := by
    have hLi : LocallyIntegrable (fun x => (L t : Vec3 → Vec3) x i) volume :=
      (memLp_pi_iff.1 (Lp.memLp (L t)) i).locallyIntegrable hp1
    have hZi := forcedHeat_slice_locallyIntegrable hτ hG hsupp ht i
    have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hLi.sub hZi) fun φ hφ hφc => by
      have hI1 : Integrable (fun x => φ x * (L t : Vec3 → Vec3) x i) volume := by
        simpa only [smul_eq_mul] using
          hLi.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
      have hI2 : Integrable (fun x => φ x * forcedHeat G (x, t) i) volume := by
        simpa only [smul_eq_mul] using
          hZi.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
      have hpt : (fun x => φ x • ((fun x => (L t : Vec3 → Vec3) x i) -
          fun x => forcedHeat G (x, t) i) x) =
          fun x => φ x * (L t : Vec3 → Vec3) x i - φ x * forcedHeat G (x, t) i := by
        funext x
        simp only [Pi.sub_apply, smul_eq_mul]
        ring
      rw [hpt, integral_sub hI1 hI2]
      have h := hpair i φ hφ hφc t ht
      simp only [mul_comm (φ _)]
      rw [h, sub_self]
    filter_upwards [h0] with x hx
    exact sub_eq_zero.1 hx
  filter_upwards [hcomp 0, hcomp 1, hcomp 2] with x h0 h1 h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The strong continuity of the rough forced heat response in `L²` and `L³`,
with every-time bounds, from continuous `L²` and `L³` curves identified with its
slices at almost every time. -/
theorem forcedHeat_strong_of_limits {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    (L2 : ℝ → Lp Vec3 (ENNReal.ofReal 2) volume) (L3 : ℝ → Lp Vec3 (ENNReal.ofReal 3) volume)
    (hL2c : ContinuousOn L2 (Icc 0 τ)) (hL3c : ContinuousOn L3 (Icc 0 τ))
    (hL2ae : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
      (L2 t : Vec3 → Vec3) =ᵐ[volume] fun x => forcedHeat G (x, t))
    (hL3ae : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
      (L3 t : Vec3 → Vec3) =ᵐ[volume] fun x => forcedHeat G (x, t))
    {B2 B3 : ℝ≥0∞}
    (hB2 : ∀ t ∈ Icc 0 τ, eLpNorm (L2 t) (ENNReal.ofReal 2) volume ≤ B2)
    (hB3 : ∀ t ∈ Icc 0 τ, eLpNorm (L3 t) (ENNReal.ofReal 3) volume ≤ B3) :
    (∀ t ∈ Icc 0 τ,
      MemLp (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ∧
      MemLp (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ∧
      eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ≤ B2 ∧
      eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ≤ B3) ∧
    (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
        forcedHeat G (x, s) - forcedHeat G (x, t)) 2 volume) (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
    (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
        forcedHeat G (x, s) - forcedHeat G (x, t)) 3 volume) (𝓝[Icc 0 τ] t) (𝓝 0)) := by
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have e3 : ENNReal.ofReal 3 = 3 := by simp
  have : Fact (1 ≤ ENNReal.ofReal (3 / 2)) := ⟨by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  have h22 : (ENNReal.ofReal 2).HolderConjugate (ENNReal.ofReal 2) := ⟨by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_add (by norm_num)
      (by norm_num)]
    norm_num⟩
  have h33 : (ENNReal.ofReal 3).HolderConjugate (ENNReal.ofReal (3 / 2)) := ⟨by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num⟩
  have hid2 := forcedHeat_lp_everyTime hτ hG hsupp (q := ENNReal.ofReal 2) L2 hL2c hL2ae
  have hid3 := forcedHeat_lp_everyTime hτ hG hsupp (q := ENNReal.ofReal (3 / 2)) L3 hL3c hL3ae
  have hcont (r : ℝ≥0∞) [Fact (1 ≤ r)] (L : ℝ → Lp Vec3 r volume)
      (hLc : ContinuousOn L (Icc 0 τ))
      (hid : ∀ t ∈ Icc 0 τ, (L t : Vec3 → Vec3) =ᵐ[volume] fun x => forcedHeat G (x, t))
      (t : ℝ) (ht : t ∈ Icc 0 τ) :
      Tendsto (fun s => eLpNorm (fun x : Vec3 =>
        forcedHeat G (x, s) - forcedHeat G (x, t)) r volume) (𝓝[Icc 0 τ] t) (𝓝 0) := by
    have hdist : Tendsto (fun s => dist (L s) (L t)) (𝓝[Icc 0 τ] t) (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 (hLc t ht)
    have hofReal := ENNReal.tendsto_ofReal hdist
    rw [ENNReal.ofReal_zero] at hofReal
    refine hofReal.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have e : ENNReal.ofReal (dist (L s) (L t)) =
        eLpNorm ((L s : Vec3 → Vec3) - (L t : Vec3 → Vec3)) r volume := by
      rw [Lp.dist_def, ENNReal.ofReal_toReal
        ((Lp.memLp (L s)).sub (Lp.memLp (L t))).eLpNorm_ne_top]
    refine e.trans (eLpNorm_congr_ae ?_)
    filter_upwards [hid s hs, hid t ht] with x h2 h3
    exact congrArg₂ (· - ·) h2 h3
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have hm2 : MemLp (fun x : Vec3 => forcedHeat G (x, t)) (ENNReal.ofReal 2) volume :=
      (memLp_congr_ae (hid2 t ht)).1 (Lp.memLp (L2 t))
    have hm3 : MemLp (fun x : Vec3 => forcedHeat G (x, t)) (ENNReal.ofReal 3) volume :=
      (memLp_congr_ae (hid3 t ht)).1 (Lp.memLp (L3 t))
    have hn2 : eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) (ENNReal.ofReal 2) volume ≤ B2 := by
      rw [← eLpNorm_congr_ae (hid2 t ht)]
      exact hB2 t ht
    have hn3 : eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) (ENNReal.ofReal 3) volume ≤ B3 := by
      rw [← eLpNorm_congr_ae (hid3 t ht)]
      exact hB3 t ht
    rw [e2] at hm2 hn2
    rw [e3] at hm3 hn3
    exact ⟨hm2, hm3, hn2, hn3⟩
  · have h := hcont (ENNReal.ofReal 2) L2 hL2c hid2 t ht
    rw [e2] at h
    exact h
  · have h := hcont (ENNReal.ofReal 3) L3 hL3c hid3 t ht
    rw [e3] at h
    exact h

end ESS

end
