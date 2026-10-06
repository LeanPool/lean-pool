/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatStrongContinuitySmooth
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughApprox
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughSlices
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionPairing
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatStrongContinuityCore
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Strong continuity for rough forced responses

The smooth-data bounds extend to rough tensors at every time. The proof takes a
uniform-in-time limit of smooth responses in `L²` and `L³`, then identifies each
limit with the kernel response by its pairings against compactly supported
smooth tests.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic

local instance : IsFiniteMeasureOnCompacts (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

local instance factOfRealTwo : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
local instance factOfRealThree : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩


noncomputable section

namespace ESS

/-- The strong-continuity theorem for a generic smooth-data slice estimate. -/
private theorem forcedHeat_lp_approx_limit {τ : ℝ}
    {r : ℝ} (hr : 2 ≤ r) [Fact (1 ≤ ENNReal.ofReal r)]
    {q : ℝ≥0∞} (hq : 1 ≤ q) (C : ℝ) (hC : 0 ≤ C)
    (Gn : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (hGn : ∀ n i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => Gn n i j p))
    (hGnc : ∀ n i j, HasCompactSupport (fun p : Vec3 × ℝ => Gn n i j p))
    (hGnpos : ∀ n i j, tsupport (fun p : Vec3 × ℝ => Gn n i j p) ⊆ {p | 0 < p.2})
    (G : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (hGq : ∀ i j, MemLp (G i j) q volume)
    (hErr : ∀ i j, Tendsto (fun n => eLpNorm
      (fun z : ParabolicPoint => Gn n i j z - G i j z) q volume) atTop (𝓝 0))
    (hEstimate : ∀ H : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => H i j z)) →
      (∀ i j, HasCompactSupport (fun z : Vec3 × ℝ => H i j z)) →
      (∀ i j, tsupport (fun z : Vec3 × ℝ => H i j z) ⊆ {p | 0 < p.2}) →
      ∀ t ∈ Icc 0 τ,
        eLpNorm (fun x : Vec3 => forcedHeat H (x, t)) (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal C * eLpNorm (fun z : ParabolicPoint => fun i j => H i j z) q
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) :
    ∃ L : ℝ → Lp Vec3 (ENNReal.ofReal r) volume,
      ContinuousOn L (Icc 0 τ) ∧
      (∀ t ∈ Icc 0 τ, Tendsto (fun n =>
        (forcedHeat_smooth_slice_memLp (hGn n) (hGnc n) hr t).toLp
          (fun x : Vec3 => forcedHeat (Gn n) (x, t))) atTop (𝓝 (L t))) ∧
      (∀ t ∈ Icc 0 τ,
        eLpNorm (L t) (ENNReal.ofReal r) volume ≤ ENNReal.ofReal C *
          eLpNorm (fun z : ParabolicPoint => fun i j => G i j z) q
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) := by
  set p : ℝ≥0∞ := ENNReal.ofReal r
  let Q : Set ParabolicPoint := CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  let μQ : Measure ParabolicPoint := volume.restrict Q
  let Gt : ParabolicPoint → Fin 3 → Fin 3 → ℝ := fun z i j => G i j z
  let err : ℕ → ℝ≥0∞ := fun n => ∑ i : Fin 3, ∑ j : Fin 3,
    eLpNorm (fun z : ParabolicPoint => Gn n i j z - G i j z) q volume
  have hErr' : Tendsto err atTop (𝓝 0) := by
    have h := tendsto_finsetSum (s := Finset.univ) fun i _ =>
      tendsto_finsetSum (s := Finset.univ) fun j _ => hErr i j
    simpa [err] using h
  have hvol : (volume : Measure ParabolicPoint) = (volume : Measure (Vec3 × ℝ)) := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod,
      Measure.volume_eq_prod]
  have hGnMem (n : ℕ) (i j : Fin 3) : MemLp (Gn n i j) q volume := by
    rw [hvol]
    exact (hGn n i j).continuous.memLp_of_hasCompactSupport (hGnc n i j)
  have herrMem (n : ℕ) (i j : Fin 3) :
      MemLp (fun z : ParabolicPoint => Gn n i j z - G i j z) q volume :=
    (hGnMem n i j).sub (hGq i j)
  have herrTop (n : ℕ) (i j : Fin 3) :
      eLpNorm (fun z : ParabolicPoint => Gn n i j z - G i j z) q volume < ⊤ :=
    (herrMem n i j).eLpNorm_lt_top
  have herrTop' (n : ℕ) : err n < ⊤ := by
    simpa [err] using
      (ENNReal.sum_lt_top.mpr fun i (_ : i ∈ Finset.univ) =>
        ENNReal.sum_lt_top.mpr fun j (_ : j ∈ Finset.univ) => herrTop n i j)
  have herrToReal : Tendsto (fun n => (err n).toReal) atTop (𝓝 0) := by
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.tendsto_toReal_iff (fun n => (herrTop' n).ne) ENNReal.zero_ne_top).2 hErr'
  have hGtensor : MemLp Gt q μQ := by
    rw [memLp_pi_iff]
    intro i
    rw [memLp_pi_iff]
    intro j
    exact (hGq i j).restrict Q
  have hGtensorTop : eLpNorm Gt q μQ < ⊤ := hGtensor.eLpNorm_lt_top
  have hErrTensor (n : ℕ) :
      eLpNorm (fun z : ParabolicPoint => fun i j => Gn n i j z - G i j z) q μQ ≤ err n := by
    have hEm (i j : Fin 3) : AEStronglyMeasurable
        (fun z : ParabolicPoint => Gn n i j z - G i j z) volume :=
      (hGn n i j).continuous.aestronglyMeasurable.sub (hGq i j).aestronglyMeasurable
    calc
      _ ≤ eLpNorm (fun z : ParabolicPoint => fun i j => Gn n i j z - G i j z) q volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (fun z : ParabolicPoint => Gn n i j z - G i j z) q volume :=
        eLpNorm_tensor_le_sum hq _ fun i j => hEm i j
      _ = err n := by simp [err]
  have hApproxTensor (n : ℕ) :
      eLpNorm (fun z : ParabolicPoint => fun i j => Gn n i j z) q μQ ≤
        eLpNorm Gt q μQ + err n := by
    let En : ParabolicPoint → Fin 3 → Fin 3 → ℝ :=
      fun z i j => Gn n i j z - G i j z
    have hsplit : (fun z : ParabolicPoint => fun i j => Gn n i j z) = Gt + En := by
      funext z i j
      simp [Gt, En]
    rw [hsplit]
    refine (eLpNorm_add_le hq).trans (add_le_add le_rfl ?_)
    exact hErrTensor n
  have hErrorSq (n m : ℕ) (i j : Fin 3) :
      eLpNorm (fun z : ParabolicPoint => Gn n i j z - Gn m i j z) q volume ≤
        eLpNorm (fun z : ParabolicPoint => Gn n i j z - G i j z) q volume +
        eLpNorm (fun z : ParabolicPoint => Gn m i j z - G i j z) q volume := by
    have heq : (fun z : ParabolicPoint => Gn n i j z - Gn m i j z) =
        (fun z => (Gn n i j z - G i j z) - (Gn m i j z - G i j z)) := by
      funext z
      ring
    rw [heq]
    exact eLpNorm_sub_le hq
  let H : ℕ → ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ :=
    fun n m i j z => Gn n i j z - Gn m i j z
  let Hprod : ℕ → ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n m i j z => H n m i j z
  have hHs (n m : ℕ) (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Hprod n m i j z) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Gn n i j z - Gn m i j z)
    exact (hGn n i j).sub (hGn m i j)
  have hHc (n m : ℕ) (i j : Fin 3) :
      HasCompactSupport (fun z : Vec3 × ℝ => Hprod n m i j z) := by
    change HasCompactSupport (fun z : Vec3 × ℝ => Gn n i j z - Gn m i j z)
    exact (hGnc n i j).sub (hGnc m i j)
  have hHpos (n m : ℕ) (i j : Fin 3) :
      tsupport (fun z : Vec3 × ℝ => Hprod n m i j z) ⊆ {z | 0 < z.2} := by
    have hsub := tsupport_sub (fun z : Vec3 × ℝ => Gn n i j z)
      (fun z : Vec3 × ℝ => Gn m i j z)
    change tsupport (fun z : Vec3 × ℝ => Gn n i j z - Gn m i j z) ⊆ _
    exact hsub.trans (union_subset (hGnpos n i j) (hGnpos m i j))
  have hHtensor (n m : ℕ) :
      eLpNorm (fun z : ParabolicPoint => fun i j => H n m i j z) q μQ ≤ err n + err m := by
    have hEntryMeas (i j : Fin 3) : AEStronglyMeasurable
        (fun z : ParabolicPoint => H n m i j z) volume :=
      ((hGn n i j).continuous.sub (hGn m i j).continuous).aestronglyMeasurable
    calc
      _ ≤ eLpNorm (fun z : ParabolicPoint => fun i j => H n m i j z) q volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (fun z : ParabolicPoint => H n m i j z) q volume :=
        eLpNorm_tensor_le_sum hq _ hEntryMeas
      _ ≤ err n + err m := by
        calc
          _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
              (eLpNorm (fun z : ParabolicPoint => Gn n i j z - G i j z) q volume +
                eLpNorm (fun z : ParabolicPoint => Gn m i j z - G i j z) q volume) := by
            exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              simpa [H] using hErrorSq n m i j
          _ = err n + err m := by simp [err, Finset.sum_add_distrib]
  have hHrep (n m : ℕ) (z : ParabolicPoint) :
      forcedHeat (H n m) z = forcedHeat (Gn n) z - forcedHeat (Gn m) z := by
    have hsource : H n m + Gn m = Gn n := by
      funext i j w
      dsimp [H]
      ring
    have hadd : forcedHeat (H n m + Gn m) z =
        forcedHeat (H n m) z + forcedHeat (Gn m) z := by
      simpa [Hprod] using forcedHeat_add (z := z)
        (fun i j => forcedHeat_integrand_integrable (hHs n m) (hHc n m) z i j)
        (fun i j => forcedHeat_integrand_integrable (hGn m) (hGnc m) z i j)
    rw [← hsource, hadd]
    ext i
    simp
  let F : ℕ → ℝ → Lp Vec3 p volume := fun n t =>
    (forcedHeat_smooth_slice_memLp (hGn n) (hGnc n) hr t).toLp
      (fun x : Vec3 => forcedHeat (Gn n) (x, t))
  have hFcontinuous (n : ℕ) : Continuous (F n) := by
    exact forcedHeat_smooth_lp_path_continuous (hGn n) (hGnc n) hr
  have hFdist (n m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) :
      dist (F n t) (F m t) ≤ C * ((err n).toReal + (err m).toReal) := by
    have hmemn := forcedHeat_smooth_slice_memLp (hGn n) (hGnc n) hr t
    have hmemm := forcedHeat_smooth_slice_memLp (hGn m) (hGnc m) hr t
    have hcoen := MemLp.coeFn_toLp hmemn
    have hcoem := MemLp.coeFn_toLp hmemm
    have hdiff : (fun x : Vec3 => (F n t) x - (F m t) x) =ᵐ[volume]
        fun x => forcedHeat (H n m) (x, t) := by
      filter_upwards [hcoen, hcoem] with x h1 h2
      rw [h1, h2, ← hHrep n m (x, t)]
    have hest := hEstimate (H n m) (hHs n m) (hHc n m) (hHpos n m) t ht
    have hbound := hest.trans
      (mul_le_mul_of_nonneg_left (hHtensor n m) (by positivity))
    have htop : ENNReal.ofReal C * (err n + err m) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨herrTop' n, herrTop' m⟩)
    have hreal := ENNReal.toReal_mono htop.ne hbound
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ENNReal.toReal_add (herrTop' n).ne (herrTop' m).ne] at hreal
    rw [Lp.dist_def]
    change (eLpNorm (fun x : Vec3 => (F n t) x - (F m t) x) p volume).toReal ≤ _
    rw [eLpNorm_congr_ae hdiff]
    exact hreal
  have hUniformCauchy : UniformCauchySeqOn F atTop (Icc 0 τ) := by
    apply Metric.uniformCauchySeqOn_iff.2
    intro ε hε
    let δ : ℝ := ε / (2 * (C + 1))
    have hden : 0 < 2 * (C + 1) := by positivity
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hsmall : ∀ᶠ n in atTop, (err n).toReal < δ :=
      herrToReal.eventually (isOpen_Iio.mem_nhds hδ)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
    refine ⟨N, fun n hn m hm t ht => ?_⟩
    have hn' := hN n hn
    have hm' := hN m hm
    have hdist := hFdist n m t ht
    have hcoeff : C * (δ + δ) < ε := by
      have hfrac : C / (C + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith only)
      calc
        C * (δ + δ) = ε * (C / (C + 1)) := by
          dsimp [δ]
          field_simp [ne_of_gt hden]
          ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
        _ = ε := by ring
    calc
      dist (F n t) (F m t) ≤ C * ((err n).toReal + (err m).toReal) := hdist
      _ ≤ C * (δ + δ) := mul_le_mul_of_nonneg_left
        (add_le_add hn'.le hm'.le) hC
      _ < ε := hcoeff
  have hPointCauchy (t : ℝ) (ht : t ∈ Icc 0 τ) : CauchySeq (fun n => F n t) := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hUniformCauchy) ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    exact hN m hm n hn t ht
  let L : ℝ → Lp Vec3 p volume := fun t =>
    if ht : t ∈ Icc 0 τ then
      Classical.choose (cauchySeq_tendsto_of_complete (hPointCauchy t ht))
    else 0
  have hLpoint (t : ℝ) (ht : t ∈ Icc 0 τ) :
      Tendsto (fun n => F n t) atTop (𝓝 (L t)) := by
    dsimp [L]
    rw [dite_eq_left ht]
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hPointCauchy t ht))
  have hUniform : TendstoUniformlyOn F L atTop (Icc 0 τ) :=
    hUniformCauchy.tendstoUniformlyOn_of_tendsto hLpoint
  have hLcontinuous : ContinuousOn L (Icc 0 τ) :=
    hUniform.continuousOn (Filter.Frequently.of_forall fun n =>
      (hFcontinuous n).continuousOn.mono (subset_univ _))
  have hLbound (t : ℝ) (ht : t ∈ Icc 0 τ) :
      eLpNorm (L t) p volume ≤ ENNReal.ofReal C * eLpNorm Gt q μQ := by
    have hFtoL : Tendsto (fun n => F n t) atTop (𝓝 (L t)) := hLpoint t ht
    have hnormlim : Tendsto (fun n => ‖F n t‖) atTop (𝓝 ‖L t‖) :=
      continuous_norm.continuousAt.tendsto.comp hFtoL
    have hsourceBound (n : ℕ) :
        eLpNorm (fun z : ParabolicPoint => fun i j => Gn n i j z) q μQ ≤
          eLpNorm Gt q μQ + err n := hApproxTensor n
    have hrespBound (n : ℕ) :
        eLpNorm (fun x : Vec3 => forcedHeat (Gn n) (x, t)) p volume ≤
          ENNReal.ofReal C * (eLpNorm Gt q μQ + err n) := by
      have hsmooth := hEstimate (Gn n) (hGn n) (hGnc n) (hGnpos n) t ht
      exact hsmooth.trans
        (mul_le_mul_of_nonneg_left (hsourceBound n) (by positivity))
    have hsourceTop (n : ℕ) : eLpNorm (fun z : ParabolicPoint => fun i j => Gn n i j z) q μQ < ⊤ := by
      exact lt_of_le_of_lt (hsourceBound n) (ENNReal.add_lt_top.2 ⟨hGtensorTop, herrTop' n⟩)
    have hrespTop (n : ℕ) : eLpNorm (fun x : Vec3 => forcedHeat (Gn n) (x, t)) p volume < ⊤ :=
      lt_of_le_of_lt (hrespBound n) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨hGtensorTop, herrTop' n⟩))
    have hFnorm (n : ℕ) : ‖F n t‖ =
        (eLpNorm (fun x : Vec3 => forcedHeat (Gn n) (x, t)) p volume).toReal := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae (MemLp.coeFn_toLp
        (forcedHeat_smooth_slice_memLp (hGn n) (hGnc n) hr t))
    have hrealBound (n : ℕ) : ‖F n t‖ ≤ C *
        ((eLpNorm Gt q μQ).toReal + (err n).toReal) := by
      rw [hFnorm n]
      have h := ENNReal.toReal_mono
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.add_lt_top.2 ⟨hGtensorTop, herrTop' n⟩)).ne (hrespBound n)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
        ENNReal.toReal_add hGtensorTop.ne (herrTop' n).ne] at h
      exact h
    have hrhs : Tendsto (fun n => C *
        ((eLpNorm Gt q μQ).toReal + (err n).toReal)) atTop
        (𝓝 (C * (eLpNorm Gt q μQ).toReal)) := by
      simpa only [add_zero, mul_zero] using
        ((tendsto_const_nhds.add herrToReal).const_mul C)
    have hnormBound : ‖L t‖ ≤ C * (eLpNorm Gt q μQ).toReal :=
      le_of_tendsto_of_tendsto hnormlim hrhs (Eventually.of_forall hrealBound)
    have hLnorm : eLpNorm (L t) p volume = ENNReal.ofReal ‖L t‖ := by
      rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (L t)), Lp.norm_def]
    rw [hLnorm, ← ENNReal.ofReal_toReal hGtensorTop.ne, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hnormBound
  exact ⟨L, hLcontinuous, fun t ht => hLpoint t ht, hLbound⟩

/-- The forced heat response is strongly continuous in both spatial `L²` and
`L³` on the closed time slab, with every-time bounds inherited from the smooth
response estimates. -/
theorem forcedHeat_strong_continuity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      (∀ t ∈ Icc 0 τ,
        MemLp (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ∧
        MemLp (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ∧
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
          forcedHeat G (x, s) - forcedHeat G (x, t)) 2 volume) (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
      (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
          forcedHeat G (x, s) - forcedHeat G (x, t)) 3 volume) (𝓝[Icc 0 τ] t) (𝓝 0)) := by
  obtain ⟨C, hC, hSmooth⟩ := forcedHeat_smooth_estimates
  refine ⟨C, hC, fun τ hτ G hG52 hG2 hGsupp => ?_⟩
  obtain ⟨Gn, hGn, hGnc, hGnpos, h52, h2, hae⟩ :=
    forcedHeat_rough_approx hτ hG52 hG2 hGsupp
  have hvol : (volume : Measure ParabolicPoint) = (volume : Measure (Vec3 × ℝ)) := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod,
      Measure.volume_eq_prod]
  have hErr2 (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : ParabolicPoint => Gn n i j z - G i j z) 2 volume) atTop (𝓝 0) := by
    rw [hvol]
    change Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => Gn n i j z - G i j z) 2 volume) atTop (𝓝 0)
    exact h2 i j
  have hErr52 (i j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun z : ParabolicPoint => Gn n i j z - G i j z)
      (ENNReal.ofReal (5 / 2)) volume) atTop (𝓝 0) := by
    rw [hvol]
    change Tendsto (fun n => eLpNorm
      (fun z : Vec3 × ℝ => Gn n i j z - G i j z)
      (ENNReal.ofReal (5 / 2)) volume) atTop (𝓝 0)
    exact h52 i j
  have hEstimate2 : ∀ H : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => H i j z)) →
      (∀ i j, HasCompactSupport (fun z : Vec3 × ℝ => H i j z)) →
      (∀ i j, tsupport (fun z : Vec3 × ℝ => H i j z) ⊆ {z | 0 < z.2}) →
      ∀ t ∈ Icc 0 τ,
        eLpNorm (fun x : Vec3 => forcedHeat H (x, t)) (ENNReal.ofReal (2 : ℝ)) volume ≤
          ENNReal.ofReal C * eLpNorm (fun z : ParabolicPoint => fun i j => H i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
    intro H hH hHc hHp t ht
    simpa using (hSmooth H hH hHc hHp τ hτ).1 t ht
  have hEstimate3 : ∀ H : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => H i j z)) →
      (∀ i j, HasCompactSupport (fun z : Vec3 × ℝ => H i j z)) →
      (∀ i j, tsupport (fun z : Vec3 × ℝ => H i j z) ⊆ {z | 0 < z.2}) →
      ∀ t ∈ Icc 0 τ,
        eLpNorm (fun x : Vec3 => forcedHeat H (x, t)) (ENNReal.ofReal (3 : ℝ)) volume ≤
          ENNReal.ofReal C * eLpNorm (fun z : ParabolicPoint => fun i j => H i j z)
            (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
    intro H hH hHc hHp t ht
    simpa using (hSmooth H hH hHc hHp τ hτ).2.2.1 t ht
  have hLimit2 := forcedHeat_lp_approx_limit (τ := τ) (r := 2) (by norm_num)
    (q := 2) (by norm_num) C hC Gn hGn hGnc hGnpos G hG2 hErr2 hEstimate2
  have hLimit3 := forcedHeat_lp_approx_limit (τ := τ) (r := 3) (by norm_num)
    (q := ENNReal.ofReal (5 / 2)) (by norm_num) C hC Gn hGn hGnc hGnpos G hG52 hErr52 hEstimate3
  obtain ⟨L2, hL2continuous, hL2point, hL2bound⟩ := hLimit2
  obtain ⟨L3, hL3continuous, hL3point, hL3bound⟩ := hLimit3
  let F2 : ℕ → ℝ → Lp Vec3 (ENNReal.ofReal (2 : ℝ)) volume := fun n t =>
    (forcedHeat_smooth_slice_memLp (hGn n) (hGnc n) (by norm_num) t).toLp
      (fun x : Vec3 => forcedHeat (Gn n) (x, t))
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict
      ((Set.univ : Set Vec3) ×ˢ Ioo 0 τ) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo 0 τ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have haeProduct : ∀ᵐ z ∂((volume : Measure Vec3).prod
      (volume.restrict (Ioo 0 τ))),
      Tendsto (fun n => forcedHeat (Gn n) z) atTop (𝓝 (forcedHeat G z)) := by
    rw [← hprod]
    exact hae
  have haeSlices := ae_slice_of_ae haeProduct
  have hL2rough : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
      L2 t =ᵐ[volume] fun x : Vec3 => forcedHeat G (x, t) := by
    have htIoo : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), t ∈ Ioo 0 τ :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [haeSlices, htIoo] with t hroughSlice htIoo
    have ht : t ∈ Icc 0 τ := Ioo_subset_Icc_self htIoo
    have hL2measure : TendstoInMeasure volume (fun n => F2 n t) atTop (L2 t) :=
      tendstoInMeasure_of_tendsto_Lp (by simpa [F2] using hL2point t ht)
    obtain ⟨m, hm, hL2ae⟩ := hL2measure.exists_seq_tendsto_ae'
    have hrepresentatives : ∀ᵐ x ∂(volume : Measure Vec3), ∀ n,
        F2 (m n) t x = forcedHeat (Gn (m n)) (x, t) := by
      apply ae_all_iff.2
      intro n
      exact MemLp.coeFn_toLp
        (forcedHeat_smooth_slice_memLp (hGn (m n)) (hGnc (m n)) (by norm_num) t)
    filter_upwards [hL2ae, hrepresentatives, hroughSlice] with x hlim hrep hrough
    have hlim' : Tendsto (fun n => forcedHeat (Gn (m n)) (x, t)) atTop (𝓝 (L2 t x)) :=
      hlim.congr' (Eventually.of_forall fun n => hrep n)
    have hrough' : Tendsto (fun n => forcedHeat (Gn (m n)) (x, t)) atTop
        (𝓝 (forcedHeat G (x, t))) := hrough.comp hm
    exact tendsto_nhds_unique hlim' hrough'
  let F3 : ℕ → ℝ → Lp Vec3 (ENNReal.ofReal (3 : ℝ)) volume := fun n t =>
    (forcedHeat_smooth_slice_memLp (hGn n) (hGnc n) (by norm_num) t).toLp
      (fun x : Vec3 => forcedHeat (Gn n) (x, t))
  have hL3rough : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
      L3 t =ᵐ[volume] fun x : Vec3 => forcedHeat G (x, t) := by
    have htIoo : ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), t ∈ Ioo 0 τ :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [haeSlices, htIoo] with t hroughSlice htIoo
    have ht : t ∈ Icc 0 τ := Ioo_subset_Icc_self htIoo
    have hL3measure : TendstoInMeasure volume (fun n => F3 n t) atTop (L3 t) :=
      tendstoInMeasure_of_tendsto_Lp (by simpa [F3] using hL3point t ht)
    obtain ⟨m, hm, hL3ae⟩ := hL3measure.exists_seq_tendsto_ae'
    have hrepresentatives : ∀ᵐ x ∂(volume : Measure Vec3), ∀ n,
        F3 (m n) t x = forcedHeat (Gn (m n)) (x, t) := by
      apply ae_all_iff.2
      intro n
      exact MemLp.coeFn_toLp
        (forcedHeat_smooth_slice_memLp (hGn (m n)) (hGnc (m n)) (by norm_num) t)
    filter_upwards [hL3ae, hrepresentatives, hroughSlice] with x hlim hrep hrough
    have hlim' : Tendsto (fun n => forcedHeat (Gn (m n)) (x, t)) atTop (𝓝 (L3 t x)) :=
      hlim.congr' (Eventually.of_forall fun n => hrep n)
    have hrough' : Tendsto (fun n => forcedHeat (Gn (m n)) (x, t)) atTop
        (𝓝 (forcedHeat G (x, t))) := hrough.comp hm
    exact tendsto_nhds_unique hlim' hrough'
  exact forcedHeat_strong_of_limits hτ hG52 hGsupp L2 L3 hL2continuous hL3continuous
    hL2rough hL3rough hL2bound hL3bound

end ESS

end
