/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.AnomalousRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.CutoffLimitDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStability
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderData

/-!
# AnomalousRegularityLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Anomalous regularity for the stream coefficient field

The excess-decay estimate of the anomalous regularity theorem is available for
the truncated coefficient fields `a_L = nu I + k_L`, uniformly in the truncation
scale `L` above the cube scale `m`, on the cutoff sample space.  This file
carries it to the full stream field `a = nu I + k` on the full-sample carrier,
by the limit `L -> infinity`.

Two mechanisms are combined.

* The probabilistic half is a transport along `Subtype.val`: the law of the
  full-sample carrier pushes forward to the cutoff-sample law, so the minimal
  scale, its tail bound and the almost-sure clause move to the new carrier with
  no loss.  The minimal scale is the *same* random variable, read along the
  inclusion; in particular the estimate for the truncated fields is available at
  every truncation scale with one and the same exceptional set.

* The analytic half is the closedness of the display under `L^2` convergence of
  the gradients.  For a datum `h` and a force `g` fixed once and for all, the
  Dirichlet problem for `a_L` is solvable on the cube for every `L`, and the
  gradients of its solutions converge in `L^2` to the gradient of the given
  solution for `a`.  Each of the two inequalities of the display is a bound
  between two `L^2` magnitudes of the gradient against normalized window
  measures, and the reverse triangle inequality bounds the defect of each side
  by the `L^2` norm of the gradient difference over the window, at the cost of
  the inverse square root of the window's volume.  Both windows have positive
  volume, so those amplitudes are finite, the defects vanish along the limit,
  and the inequality passes to it.

## Main results

* `sqrt_vecNormSq_le_sqrt_card_mul_norm`, `continuous_sqrt_vecNormSq` — the
  Euclidean magnitude against the ambient sup norm.
* `eLpNorm_sqrt_vecNormSq_normalized_le`, `eLpNorm_sqrt_vecNormSq_restrict_le` —
  the two `L^2` atoms for the normalized window measure.
* `excess_display_closed` — the closedness of the display under `L^2`
  convergence of the gradients.
* `exists_isDirichletSolutionOn_cutoff` — the truncated Dirichlet problems with
  the given datum and force.
* `tendsto_sqrt_integral_grad_sub` — the gradients of the truncated solutions
  converge in `L^2` to the gradient of the full-field solution.
* `anomalous_regularity_provider` — the anomalous regularity estimate for the
  stream coefficient field.

## References

* ABK26, Theorem C and the passage from the truncated fields `a_L` to `a`.
-/

namespace Algsuperdiff.Section4.Provider.Introduction.AnomalousLimit

open Filter HCPolySupport MeasureTheory Topology
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support Algsuperdiff.Section4.Provider.Holder
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.Schauder
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open Algsuperdiff.Section5.Provider
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Euclidean magnitude against the ambient norm -/

/-- The squared Euclidean magnitude is continuous on `Vec d`. -/
theorem continuous_vecNormSq : Continuous fun v : Vec d => vecNormSq v := by
  change Continuous fun v : Vec d => ∑ i, v i * v i
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

/-- The Euclidean magnitude is continuous on `Vec d`. -/
theorem continuous_sqrt_vecNormSq :
    Continuous fun v : Vec d => Real.sqrt (vecNormSq v) :=
  Real.continuous_sqrt.comp continuous_vecNormSq

/-- **`sqrt (sum x i ^ 2) <= sqrt d * sup |x i|`.**  `Vec d` carries the product
norm; the display of the regularity theorem is written in the Euclidean
magnitude.  This is the only constant the comparison of the two costs. -/
theorem sqrt_vecNormSq_le_sqrt_card_mul_norm (x : Vec d) :
    Real.sqrt (vecNormSq x) ≤ Real.sqrt d * ‖x‖ := by
  exact Section24.Sensitivity.Provider.PairingConstants.sqrt_vecNormSq_le_sqrt_dimension_mul_norm
    x

/-- The Euclidean magnitude of a square-integrable field is almost everywhere
strongly measurable on the domain. -/
theorem aestronglyMeasurable_sqrt_vecNormSq {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 W F) :
    AEStronglyMeasurable (fun y => Real.sqrt (vecNormSq (F y))) (volume.restrict W) :=
  continuous_sqrt_vecNormSq.comp_aestronglyMeasurable hF.aestronglyMeasurable

/-- The Euclidean magnitude of a square-integrable field is almost everywhere
strongly measurable against the normalized measure of any subwindow. -/
theorem aestronglyMeasurable_sqrt_vecNormSq_normalized {W A : Set (Vec d)} (hAW : A ⊆ W)
    {F : Vec d → Vec d} (hF : MemVectorL2 W F) :
    AEStronglyMeasurable (fun y => Real.sqrt (vecNormSq (F y)))
      (normalizedVolumeMeasureOn A) := by
  rw [normalizedVolumeMeasureOn_def]
  exact ((aestronglyMeasurable_sqrt_vecNormSq hF).mono_measure
    (Measure.restrict_mono hAW le_rfl)).smul_measure _

/-! ## 2. Two `L²` atoms for the normalized window measure -/

/-- **The window move to the ambient domain.**  The normalized `L²` magnitude
over a subwindow is the plain `L²` magnitude over the domain, at the cost of the
inverse square root of the window's volume. -/
theorem eLpNorm_sqrt_vecNormSq_normalized_le {W A : Set (Vec d)} (hAW : A ⊆ W)
    (F : Vec d → Vec d) :
    eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (normalizedVolumeMeasureOn A) ≤
      ((volume A)⁻¹) ^ ((2 : ℝ)⁻¹) *
        eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (volume.restrict W) := by
  by_cases hg : AEStronglyMeasurable (fun y => Real.sqrt (vecNormSq (F y))) (volume.restrict A)
  swap
  · rcases eq_or_ne (volume A) ⊤ with hA | hA
    · rw [normalizedVolumeMeasureOn_def, hA, ENNReal.inv_top, zero_smul, eLpNorm_measure_zero]
      exact zero_le
    · have hW : eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (volume.restrict W) = ⊤ :=
        eLpNorm_of_not_aestronglyMeasurable fun h =>
          hg (h.mono_measure (Measure.restrict_mono hAW le_rfl))
      rw [hW, ENNReal.mul_top
        (ENNReal.rpow_pos_of_nonneg (ENNReal.inv_pos.mpr hA) (by norm_num)).ne']
      exact le_top
  rw [normalizedVolumeMeasureOn_def,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) _ _ hg]
  have hmono : eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (volume.restrict A) ≤
      eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (volume.restrict W) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hAW le_rfl)
  have hexp : ((1 : ℝ≥0∞) / 2).toReal = (2 : ℝ)⁻¹ := by norm_num
  rw [hexp, smul_eq_mul]
  exact mul_le_mul' le_rfl hmono

/-- **The dictionary with the energy integral.**  The `L²` norm of the Euclidean
magnitude of a square-integrable field over the domain is bounded by `sqrt d`
times the square root of the energy of the field in the ambient norm. -/
theorem eLpNorm_sqrt_vecNormSq_restrict_le {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 W F) :
    eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (volume.restrict W) ≤
      ENNReal.ofReal (Real.sqrt d) *
        ENNReal.ofReal (Real.sqrt (∫ y in W, ‖F y‖ ^ (2 : ℕ) ∂volume)) := by
  have h1 : eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (volume.restrict W) ≤
      eLpNorm (fun y => Real.sqrt d * ‖F y‖) 2 (volume.restrict W) := by
    refine eLpNorm_mono_real (aestronglyMeasurable_sqrt_vecNormSq hF) fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_vecNormSq_le_sqrt_card_mul_norm (F y)
  have h2 : eLpNorm (fun y => Real.sqrt d * ‖F y‖) 2 (volume.restrict W) =
      ENNReal.ofReal (Real.sqrt d) * eLpNorm F 2 (volume.restrict W) := by
    have hsm : (fun y => Real.sqrt (d : ℝ) * ‖F y‖) = (Real.sqrt (d : ℝ)) • fun y => ‖F y‖ := by
      funext y
      simp [smul_eq_mul]
    rw [hsm, eLpNorm_const_smul, eLpNorm_norm _ hF.aestronglyMeasurable]
    congr 1
    exact Real.enorm_eq_ofReal (Real.sqrt_nonneg _)
  have h3 : eLpNorm F 2 (volume.restrict W) =
      ENNReal.ofReal (Real.sqrt (∫ y in W, ‖F y‖ ^ (2 : ℕ) ∂volume)) := by
    rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 1
    have hpow : ∀ y : Vec d, ‖F y‖ ^ ((2 : ℝ≥0∞).toReal) = ‖F y‖ ^ (2 : ℕ) := by
      intro y
      rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hpow]
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [h3] at h2
  exact h1.trans_eq h2

/-- **The triangle inequality for the `L²` magnitude of a field.** -/
theorem eLpNorm_sqrt_vecNormSq_le_add {μ : Measure (Vec d)} {F G : Vec d → Vec d}
    (hG : AEStronglyMeasurable (fun y => Real.sqrt (vecNormSq (G y))) μ) :
    eLpNorm (fun y => Real.sqrt (vecNormSq (G y))) 2 μ ≤
      eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 μ +
        eLpNorm (fun y => Real.sqrt (vecNormSq (G y - F y))) 2 μ := by
  have hpt : ∀ y : Vec d, Real.sqrt (vecNormSq (G y)) ≤
      Real.sqrt (vecNormSq (F y)) + Real.sqrt (vecNormSq (G y - F y)) := by
    intro y
    have h := slopeMagnitude_add_le (F y) (G y - F y)
    have hEq : F y + (G y - F y) = G y := by abel
    rw [hEq] at h
    exact h
  refine le_trans ?_ (eLpNorm_add_le one_le_two)
  refine eLpNorm_mono_real hG fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hpt y

/-- The Euclidean magnitude of a difference is symmetric in its two arguments. -/
theorem sqrt_vecNormSq_sub_comm (F G : Vec d → Vec d) :
    (fun y => Real.sqrt (vecNormSq (F y - G y))) =
      fun y => Real.sqrt (vecNormSq (G y - F y)) := by
  funext y
  exact slopeMagnitude_sub_comm (F y) (G y)

/-! ## 3. The limit passage in `ℝ≥0∞` -/

/-- **A two-sided inequality with vanishing defects passes to the limit.**  If
`a` is below a family `PA` up to a defect, the family `PW` is above `b` up to a
defect, the two families satisfy `PA ≤ K (PW + c)` eventually, and both defects
are a finite multiple of a real quantity tending to zero, then `a ≤ K (b + c)`. -/
theorem le_mul_add_of_eventually {a b K c : ℝ≥0∞} {PA PW : ℤ → ℝ≥0∞} {TA TW : ℝ≥0∞}
    {t : ℤ → ℝ} (hK : K ≠ ⊤) (hTA : TA ≠ ⊤) (hTW : TW ≠ ⊤)
    (ht : Tendsto (fun L : ℤ => ENNReal.ofReal (t L)) atTop (𝓝 0))
    (hA : ∀ L, a ≤ PA L + TA * ENNReal.ofReal (t L))
    (hW : ∀ L, PW L ≤ b + TW * ENNReal.ofReal (t L))
    (hbd : ∀ᶠ L in atTop, PA L ≤ K * (PW L + c)) :
    a ≤ K * (b + c) := by
  have hstep : ∀ᶠ L : ℤ in atTop,
      a ≤ K * (b + c) + (K * TW + TA) * ENNReal.ofReal (t L) := by
    filter_upwards [hbd] with L hL
    have h2 : K * (PW L + c) ≤ K * ((b + TW * ENNReal.ofReal (t L)) + c) :=
      mul_le_mul' le_rfl (add_le_add (hW L) le_rfl)
    have h3 : K * ((b + TW * ENNReal.ofReal (t L)) + c) + TA * ENNReal.ofReal (t L)
        = K * (b + c) + (K * TW + TA) * ENNReal.ofReal (t L) := by ring
    calc a ≤ PA L + TA * ENNReal.ofReal (t L) := hA L
      _ ≤ K * (PW L + c) + TA * ENNReal.ofReal (t L) := add_le_add hL le_rfl
      _ ≤ K * ((b + TW * ENNReal.ofReal (t L)) + c) + TA * ENNReal.ofReal (t L) :=
          add_le_add h2 le_rfl
      _ = K * (b + c) + (K * TW + TA) * ENNReal.ofReal (t L) := h3
  have hfin : K * TW + TA ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hK hTW, hTA⟩
  have hlim0 : Tendsto (fun L : ℤ => (K * TW + TA) * ENNReal.ofReal (t L)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := K * TW + TA) ht (Or.inr hfin)
    simpa using h
  have hlim : Tendsto (fun L : ℤ => K * (b + c) + (K * TW + TA) * ENNReal.ofReal (t L)) atTop
      (𝓝 (K * (b + c) + 0)) := tendsto_const_nhds.add hlim0
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim hstep

/-! ## 4. Closedness of the excess-decay display -/

/-- **The excess-decay display is closed under `L²` convergence of the fields.**
If the display holds for a family of fields `G L` on a subwindow `A` of a domain
`W`, both of positive volume, and `G L` converges to `F` in `L²` on `W`, then it
holds for `F` with the same constants. -/
theorem excess_display_closed {W A : Set (Vec d)} (hAW : A ⊆ W)
    (hA0 : volume A ≠ 0) (hW0 : volume W ≠ 0)
    {G : ℤ → Vec d → Vec d} {F : Vec d → Vec d}
    (hG : ∀ L, MemVectorL2 W (G L)) (hF : MemVectorL2 W F)
    (ht : Tendsto (fun L : ℤ =>
      Real.sqrt (∫ y in W, ‖G L y - F y‖ ^ (2 : ℕ) ∂volume)) atTop (𝓝 0))
    {s K c : ℝ≥0∞} (hs : s ≠ ⊤) (hK : K ≠ ⊤)
    (hbd : ∀ᶠ L : ℤ in atTop,
      s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2 (normalizedVolumeMeasureOn A) ≤
        K * (s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2
              (normalizedVolumeMeasureOn W) + c)) :
    s * eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (normalizedVolumeMeasureOn A) ≤
      K * (s * eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2
            (normalizedVolumeMeasureOn W) + c) := by
  set t : ℤ → ℝ := fun L => Real.sqrt (∫ y in W, ‖G L y - F y‖ ^ (2 : ℕ) ∂volume) with ht_def
  set rho : Set (Vec d) → ℝ≥0∞ := fun S => ((volume S)⁻¹) ^ ((2 : ℝ)⁻¹) with hrho_def
  have hrho_ne : ∀ S : Set (Vec d), volume S ≠ 0 → rho S ≠ ⊤ := fun S hS =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.inv_ne_top.2 hS)
  set T : Set (Vec d) → ℝ≥0∞ := fun S => s * (rho S * ENNReal.ofReal (Real.sqrt d)) with hT_def
  have hT_ne : ∀ S : Set (Vec d), volume S ≠ 0 → T S ≠ ⊤ := fun S hS =>
    ENNReal.mul_ne_top hs (ENNReal.mul_ne_top (hrho_ne S hS) ENNReal.ofReal_ne_top)
  have herr : ∀ S : Set (Vec d), S ⊆ W → ∀ L : ℤ,
      s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y - F y))) 2
          (normalizedVolumeMeasureOn S) ≤ T S * ENNReal.ofReal (t L) := by
    intro S hSW L
    have hdiff : MemVectorL2 W (fun y => G L y - F y) := (hG L).sub hF
    have h1 := (eLpNorm_sqrt_vecNormSq_normalized_le hSW (fun y => G L y - F y)).trans
      (mul_le_mul' le_rfl (eLpNorm_sqrt_vecNormSq_restrict_le hdiff))
    calc s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y - F y))) 2
            (normalizedVolumeMeasureOn S)
        ≤ s * (rho S * (ENNReal.ofReal (Real.sqrt d) * ENNReal.ofReal (t L))) :=
          mul_le_mul' le_rfl h1
      _ = T S * ENNReal.ofReal (t L) := by rw [hT_def]; ring
  refine le_mul_add_of_eventually (PA := fun L =>
      s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2 (normalizedVolumeMeasureOn A))
    (PW := fun L =>
      s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2 (normalizedVolumeMeasureOn W))
    (TA := T A) (TW := T W) (t := t) hK (hT_ne A hA0) (hT_ne W hW0) ?_ ?_ ?_ hbd
  · have h := (ENNReal.continuous_ofReal.tendsto 0).comp ht
    simpa using! h
  · intro L
    have htri := eLpNorm_sqrt_vecNormSq_le_add (μ := normalizedVolumeMeasureOn A)
      (F := G L) (G := F) (aestronglyMeasurable_sqrt_vecNormSq_normalized hAW hF)
    rw [sqrt_vecNormSq_sub_comm F (G L)] at htri
    calc s * eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2 (normalizedVolumeMeasureOn A)
        ≤ s * (eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2
              (normalizedVolumeMeasureOn A) +
            eLpNorm (fun y => Real.sqrt (vecNormSq (G L y - F y))) 2
              (normalizedVolumeMeasureOn A)) := mul_le_mul' le_rfl htri
      _ = s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2
              (normalizedVolumeMeasureOn A) +
            s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y - F y))) 2
              (normalizedVolumeMeasureOn A) := by rw [mul_add]
      _ ≤ s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2
              (normalizedVolumeMeasureOn A) + T A * ENNReal.ofReal (t L) :=
          add_le_add le_rfl (herr A hAW L)
  · intro L
    have htri := eLpNorm_sqrt_vecNormSq_le_add (μ := normalizedVolumeMeasureOn W)
      (F := F) (G := G L) (aestronglyMeasurable_sqrt_vecNormSq_normalized (subset_refl W) (hG L))
    calc s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y))) 2 (normalizedVolumeMeasureOn W)
        ≤ s * (eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2
              (normalizedVolumeMeasureOn W) +
            eLpNorm (fun y => Real.sqrt (vecNormSq (G L y - F y))) 2
              (normalizedVolumeMeasureOn W)) := mul_le_mul' le_rfl htri
      _ = s * eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2
              (normalizedVolumeMeasureOn W) +
            s * eLpNorm (fun y => Real.sqrt (vecNormSq (G L y - F y))) 2
              (normalizedVolumeMeasureOn W) := by rw [mul_add]
      _ ≤ s * eLpNorm (fun y => Real.sqrt (vecNormSq (F y))) 2
              (normalizedVolumeMeasureOn W) + T W * ENNReal.ofReal (t L) :=
          add_le_add le_rfl (herr W (subset_refl W) L)

/-! ## 5. The truncated Dirichlet problems with the given data -/

private theorem hasZeroTraceDifferenceOn_castH1 {U V : Set (Vec d)} (hUV : U = V)
    {u h : H1Function U} (H : HasZeroTraceDifferenceOn U u h) :
    HasZeroTraceDifferenceOn V (castH1 hUV u) (castH1 hUV h) := by
  subst hUV
  exact H

private theorem isDivFormWeakSolutionOn_castH1 {U V : Set (Vec d)} (hUV : U = V)
    {a : CoeffField d} {u : H1Function U} {g : Vec d → Vec d}
    (H : IsDivFormWeakSolutionOn a U u g) :
    IsDivFormWeakSolutionOn a V (castH1 hUV u) g := by
  subst hUV
  exact H

/-- **The truncated Dirichlet problem on the origin cube is solvable with the
given datum and force.**  The truncated field is elliptic on the cube and the
force is square integrable, so the Lax-Milgram construction supplies a solution
of the form `h + w` with `w` of zero trace. -/
theorem exists_isDirichletSolutionOn_cutoff (M : ABKModel d) [NeZero d]
    (omega : Cutoff.CutoffSample d) (m L : ℤ) (h : H1Function (openCubeSet (originCube d m)))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet (originCube d m)) g) :
    ∃ uL : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField)
        (originCube d m) uL h g := by
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_cutoff M L m (0 : Vec d) omega
  rw [cubeSetAt_zero_eq] at hEll
  obtain ⟨w, hw⟩ := exists_h10_isDivFormWeakSolutionOn_add
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m))
    ⟨0, zero_mem_openCubeSet_originCube m⟩ hEll h hg
  exact ⟨h + w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, hw⟩

/-- **The gradients of the truncated solutions converge in `L²`**, on a cube
centred anywhere, to the gradient of the full-field solution of the same
Dirichlet problem.  Two solutions of the same problem for two coefficient fields
differ by a zero-trace function whose energy is bounded by the supremum distance
of the two fields times the energy of one solution, and that distance is
geometric in the truncation scale. -/
theorem tendsto_sqrt_integral_grad_sub_cubeSetAt (M : ABKModel d)
    (omega : FullSample d M.gamma) (y : Vec d) (n : ℤ)
    {h : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    {u : ℤ → H1Function (cubeSetAt y n)} {v : H1Function (cubeSetAt y n)}
    (hu : ∀ L : ℤ, HasZeroTraceDifferenceOn (cubeSetAt y n) (u L) h)
    (huw : ∀ L : ℤ, IsDivFormWeakSolutionOn
      ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) (cubeSetAt y n) (u L) g)
    (hv : HasZeroTraceDifferenceOn (cubeSetAt y n) v h)
    (hvw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt y n) v g) :
    Tendsto (fun L : ℤ =>
        Real.sqrt (∫ z in cubeSetAt y n, ‖(u L).grad z - v.grad z‖ ^ (2 : ℕ) ∂volume))
      atTop (𝓝 0) := by
  exact Algsuperdiff.Section5.Provider.tendsto_sqrt_energy_grad_cutoff_of_h10Diff
    M omega y n hu huw hv hvw

/-- The `L²` convergence of the gradients of the truncated solutions, read on
the origin cube. -/
theorem tendsto_sqrt_integral_grad_sub (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ)
    {h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    {u : ℤ → H1Function (openCubeSet (originCube d m))}
    {v : H1Function (openCubeSet (originCube d m))}
    (hu : ∀ L : ℤ, IsDirichletSolutionOn
      ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) (originCube d m) (u L) h g)
    (hv : IsDirichletSolutionOn (streamCoefficient M.nu omega) (originCube d m) v h g) :
    Tendsto (fun L : ℤ =>
        Real.sqrt (∫ z in openCubeSet (originCube d m),
          ‖(u L).grad z - v.grad z‖ ^ (2 : ℕ) ∂volume)) atTop (𝓝 0) := by
  have hVW : cubeSetAt (0 : Vec d) m = openCubeSet (originCube d m) := cubeSetAt_zero_eq m
  have key := tendsto_sqrt_integral_grad_sub_cubeSetAt M omega (0 : Vec d) m
    (h := castH1 hVW.symm h) (g := g)
    (u := fun L => castH1 hVW.symm (u L)) (v := castH1 hVW.symm v)
    (fun L => hasZeroTraceDifferenceOn_castH1 hVW.symm (hu L).1)
    (fun L => isDivFormWeakSolutionOn_castH1 hVW.symm (hu L).2)
    (hasZeroTraceDifferenceOn_castH1 hVW.symm hv.1)
    (isDivFormWeakSolutionOn_castH1 hVW.symm hv.2)
  simp only [castH1_grad] at key
  rwa [hVW] at key

/-! ## 6. The transports along the inclusion of the full-sample carrier -/

/-- Events of the cutoff sample space transport to the full-sample carrier. -/
theorem measure_preimage_val (M : ABKModel d) (s : Set (Cutoff.CutoffSample d))
    (hs : MeasurableSet s) :
    (fullSampleLaw M).toMeasure (Subtype.val ⁻¹' s) =
      (Cutoff.cutoffSampleLaw M).toMeasure s := by
  rw [← map_fullSampleLaw_val M, Measure.map_apply measurable_subtype_coe hs]

/-- The tail events of an `ℕ∞`-valued random variable transport to the
full-sample carrier. -/
theorem measure_tail_comp_val (M : ABKModel d) {X : Cutoff.CutoffSample d → ℕ∞}
    (hX : Measurable X) (N : ℕ) :
    (fullSampleLaw M).toMeasure {omega : FullSample d M.gamma | (N : ℕ∞) ≤ X omega.1} =
      (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} :=
  measure_preimage_val M (X ⁻¹' Set.Ici (N : ℕ∞)) (hX MeasurableSet.of_discrete)

/-- Almost-sure clauses of the cutoff sample space transport to the full-sample
carrier. -/
theorem ae_comp_val (M : ABKModel d) {P : Cutoff.CutoffSample d → Prop}
    (h : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, P omega) :
    ∀ᵐ omega ∂(fullSampleLaw M).toMeasure, P omega.1 := by
  rw [← map_fullSampleLaw_val M] at h
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable h

end

end Algsuperdiff.Section4.Provider.Introduction.AnomalousLimit

/-! ## 7. Anomalous regularity for the stream coefficient field -/

namespace Algsuperdiff.Section4.Provider.Introduction

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

open Filter Algsuperdiff.Section4.Support Algsuperdiff.Section4.Provider.Holder
  Algsuperdiff.Section4.Provider.Schauder Algsuperdiff.Section5.Field
  Algsuperdiff.Section5.Support Algsuperdiff.Section5.Provider
  Algsuperdiff.Section4.Provider.Introduction.AnomalousLimit in
/-- **Anomalous regularity for the stream coefficient field.**  For a disorder
model of small enough strength, and every Hölder exponent below
`1 - C sqrt gamma`, there is an almost surely finite minimal scale with an
exponential tail such that, above it, every Dirichlet solution of the field
`nu I + k` on a triadic cube with `C^{0,1/2}` force and `C^{1,1/2}` boundary
datum satisfies the large-scale excess decay `3^{(1-alpha)(m-n)}` between any
two scales `n ≤ m`. -/
theorem anomalous_regularity_provider
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Algsuperdiff.Section5.Field.FullSample d M.gamma → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure
                    {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure,
              ∀ (u h : HCPolySupport.H1Function
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                (g : HCPolySupport.Vec d → HCPolySupport.Vec d)
                (Kg Kh : ℝ),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
                    (HCPolySupport.originCube d m) u h g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kg g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kh h.grad →
                (∀ y ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m),
                  ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                Algsuperdiff.Section4.Support.HasGradientOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    h.toFun h.grad →
                ∀ x : HCPolySupport.Vec d,
                  x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
                  ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                    (ENNReal.ofReal (Real.sqrt M.nu) *
                        MeasureTheory.eLpNorm
                          (fun y => Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                          (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                            (((fun y => x + y) ''
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d n)) ∩
                              HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) ≤
                      ENNReal.ofReal
                          (C *
                            Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                        (ENNReal.ofReal (Real.sqrt M.nu) *
                            MeasureTheory.eLpNorm
                              (fun y =>
                                Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                (HCPolySupport.openCubeSet
                                  (HCPolySupport.originCube d m))) +
                          ENNReal.ofReal
                            (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                          ENNReal.ofReal
                            (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                              Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                    (x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d (m - 1)) →
                      ENNReal.ofReal (Real.sqrt M.nu) *
                          MeasureTheory.eLpNorm
                            (fun y => Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y => x + y) ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d n)) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) ≤
                        ENNReal.ofReal
                            (C *
                              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          (ENNReal.ofReal (Real.sqrt M.nu) *
                              MeasureTheory.eLpNorm
                                (fun y =>
                                  Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                                (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                  (HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d m))) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)))
    := by
  classical
  obtain ⟨gamma0, C, hgamma0, hC, hmain⟩ :=
    Algsuperdiff.Frozen.Section4.anomalous_regularity d cstar _hcstar
  refine ⟨gamma0, C, hgamma0, hC, ?_⟩
  intro M hcstarM hgammaM alpha halpha halphaC m
  obtain ⟨X, hXmeas, hXtail, hXae⟩ := hmain M hcstarM hgammaM alpha halpha halphaC m
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨fun omega => X omega.1, hXmeas.comp measurable_subtype_coe, ?_, ?_⟩
  · intro N
    rw [measure_tail_comp_val M hXmeas N]
    exact hXtail N
  · filter_upwards [ae_comp_val M hXae] with omega hom
    intro u h g Kg Kh hsol hKg hKh hKhsup hhgrad x hx n hnm hXle
    have hKg0 : 0 ≤ Kg := holderSeminormBoundOn_nonneg_openCubeSet hd hKg
    have hgL2 : MemVectorL2 (openCubeSet (originCube d m)) g :=
      memVectorL2_of_holderSeminormBoundOn hKg0 (by norm_num) hKg
    choose uL huL using fun L : ℤ =>
      exists_isDirichletSolutionOn_cutoff M omega.1 m L h hgL2
    have htend := tendsto_sqrt_integral_grad_sub M omega m huL hsol
    have hxA : x ∈ (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
        openCubeSet (originCube d m)) :=
      ⟨⟨0, zero_mem_openCubeSet_originCube n, by simp⟩, hx⟩
    have hAopen : IsOpen (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
        openCubeSet (originCube d m)) :=
      ((Homeomorph.addLeft x).isOpenMap _ (isOpen_openCubeSet _)).inter (isOpen_openCubeSet _)
    have hA0 : volume (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
        openCubeSet (originCube d m)) ≠ 0 := (hAopen.measure_pos volume ⟨x, hxA⟩).ne'
    have hW0 : volume (openCubeSet (originCube d m)) ≠ 0 :=
      ((isOpen_openCubeSet (originCube d m)).measure_pos volume
        ⟨0, zero_mem_openCubeSet_originCube m⟩).ne'
    have hAW : (((fun y => x + y) '' openCubeSet (originCube d n)) ∩
        openCubeSet (originCube d m)) ⊆ openCubeSet (originCube d m) := Set.inter_subset_right
    constructor
    · rw [add_assoc]
      refine excess_display_closed (F := u.grad) (G := fun L => (uL L).grad) hAW hA0 hW0
        (fun L => (uL L).grad_memVectorL2) u.grad_memVectorL2 htend
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ?_
      filter_upwards [Filter.eventually_ge_atTop m] with L hL
      have hcl := (hom L hL (uL L) h g Kg Kh (huL L) hKg hKh hKhsup hhgrad x hx n hnm hXle).1
      rwa [add_assoc] at hcl
    · intro hxm1
      refine excess_display_closed (F := u.grad) (G := fun L => (uL L).grad) hAW hA0 hW0
        (fun L => (uL L).grad_memVectorL2) u.grad_memVectorL2 htend
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ?_
      filter_upwards [Filter.eventually_ge_atTop m] with L hL
      exact (hom L hL (uL L) h g Kg Kh (huL L) hKg hKh hKhsup hhgrad x hx n hnm hXle).2 hxm1

end Algsuperdiff.Section4.Provider.Introduction
