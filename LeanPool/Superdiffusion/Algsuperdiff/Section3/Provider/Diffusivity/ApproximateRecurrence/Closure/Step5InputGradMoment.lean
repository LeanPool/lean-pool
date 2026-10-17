/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputShellMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellCZ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLargeTransport

/-!
# Step5InputGradMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hgradM`: the grid fourth moment of the Dirichlet corrector's cube averages

ABK26, `e.nablaw.in.L.eight`, read inside Step 5 of
`l.approximate.recurrence.formula`.

`Closure.Step5Basket.step5GaugeEndpoint_closureFamilies_of_momentLegs` leaves
`hgradM` as the binder

```
  ( avsum_{R in grid}  E[ |(grad w_D)_R|^4 ] )^{1/2}
      <=  C2 * shom_n^{-2} * h * 3^{2 cgamma (n+h)} .
```

## The route

The manuscript's own three steps, in order.

1. **The grid step.**  The grid tiles `cu_K`, so per-cube Jensen followed by the
   tiling identity gives, at *fixed* sample and with no dependence on `K`,
   ```
     avsum_R |(grad w_D)_R|^4  <=  8 ||grad w_D||_{L8bar(cu_K)}^4 ,
   ```
   which is `PrincipalResponseDisplayTwoGrid.descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le`
   at `c = 0`.  The grid fourth moment is a finite average of integrals, so the
   sample integral may be taken outside.
2. **Calderon--Zygmund.**  `Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le`
   bounds `||grad w_D||^2_{L8bar(cu_K)}` by the `L^8` norm of the forcing of
   `e.def.w`, which `Corrector.cubeEuclideanLpNorm_streamForcing_le` reads as
   `shom_n^{-1} ||k_{n+h} - k_n||_{L8bar(cu_K)}`.
3. **`e.km.kn.Lp`.**  `Corrector.exists_streamIncrementLpNormSq_head_tail` ---
   the *proved* frozen theorem --- splits that square into the head `C h 3^{2
   cgamma (n+h)}` and a `Gamma_1` tail whose amplitude carries the extra decay
   `3^{-(K-m)d/8} <= 1`.  Its second moment is
   `LocalizationEnvelopeMoment.integral_sq_le_of_isBigOWith_gammaSigma_one'`,
   so the fourth moment of the `L^8` norm is at most an absolute multiple of
   the head squared, and the square root of the grid moment is the display.

## References

* ABK26, `e.nablaw.in.L.eight`; `e.km.kn.Lp`; Step 5.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The grid step, at fixed sample -/

/-- **Per-cube Jensen and the tiling identity, at `c = 0`.**  The grid average of
the fourth power of the cube averages of a field is at most `8` times the fourth
power of its normalized Euclidean `L^8` norm on the ambient cube.  No dependence
on the depth `j`. -/
theorem descendantsAverage_vecNorm_cubeAverageVec_pow_four_le (Q : TriadicCube d) (j : ℕ)
    (u : Vec d → Vec d) (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun R => vecNorm (cubeAverageVec R u) ^ (4 : ℕ)) ≤
      8 * cubeEuclideanLpNorm Q 8 u ^ (4 : ℕ) := by
  have hbase := descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le Q j (0 : Vec d) u hu
  have hzero : vecNormSq (0 : Vec d) = 0 := by
    change ∑ i, (0 : Vec d) i * (0 : Vec d) i = 0
    simp
  have hfun : (fun R : TriadicCube d =>
      vecNormSq ((0 : Vec d) + cubeAverageVec R u) ^ (2 : ℕ)) =
      fun R : TriadicCube d => vecNorm (cubeAverageVec R u) ^ (4 : ℕ) := by
    funext R
    rw [zero_add, ← vecNorm_sq_eq_vecNormSq]
    ring
  rw [hfun, hzero] at hbase
  simpa using hbase

/-- The per-cube form of the same estimate, with the grid cardinality: enough
for integrability, not for the display. -/
theorem vecNorm_cubeAverageVec_pow_four_le_card (Q : TriadicCube d) (j : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) (u : Vec d → Vec d)
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    vecNorm (cubeAverageVec R u) ^ (4 : ℕ) ≤
      ((descendantsAtDepth Q j).card : ℝ) * (8 * cubeEuclideanLpNorm Q 8 u ^ (4 : ℕ)) := by
  classical
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨R, hR⟩
  have hsum : vecNorm (cubeAverageVec R u) ^ (4 : ℕ) ≤
      ∑ S ∈ descendantsAtDepth Q j, vecNorm (cubeAverageVec S u) ^ (4 : ℕ) :=
    Finset.single_le_sum (f := fun S => vecNorm (cubeAverageVec S u) ^ (4 : ℕ))
      (fun S _ => by positivity) hR
  have hdef : descendantsAverage Q j (fun S => vecNorm (cubeAverageVec S u) ^ (4 : ℕ)) =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ S ∈ descendantsAtDepth Q j, vecNorm (cubeAverageVec S u) ^ (4 : ℕ) := rfl
  have havg := descendantsAverage_vecNorm_cubeAverageVec_pow_four_le Q j u hu
  rw [hdef] at havg
  have hmul := mul_le_mul_of_nonneg_left havg hcard.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard), one_mul] at hmul
  exact hsum.trans hmul

/-! ## Taking the sample integral outside the grid average -/

/-- **The grid fourth moment under a pathwise grid bound.**  The grid is finite,
so the sample integral commutes with its average. -/
theorem gridFourthMoment_le_integral_of_cubeFamilyAverage_le {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (I : Finset (TriadicCube d))
    (F : TriadicCube d → Omega → ℝ) (G : Omega → ℝ)
    (hFint : ∀ R ∈ I, Integrable (fun omega => F R omega ^ (4 : ℝ)) mu)
    (hGint : Integrable G mu)
    (hle : ∀ omega, cubeFamilyAverage I (fun R => F R omega ^ (4 : ℝ)) ≤ G omega) :
    gridFourthMoment mu I F ≤ ∫ omega, G omega ∂mu := by
  classical
  have hswap : ∑ R ∈ I, (∫ omega, F R omega ^ (4 : ℝ) ∂mu) =
      ∫ omega, ∑ R ∈ I, F R omega ^ (4 : ℝ) ∂mu :=
    (integral_finsetSum I hFint).symm
  have hsumint : Integrable (fun omega => ∑ R ∈ I, F R omega ^ (4 : ℝ)) mu :=
    integrable_finsetSum I hFint
  have hcmp : Integrable (fun omega => ((I.card : ℝ))⁻¹ *
      ∑ R ∈ I, F R omega ^ (4 : ℝ)) mu := hsumint.const_mul _
  have hmono : (∫ omega, ((I.card : ℝ))⁻¹ * ∑ R ∈ I, F R omega ^ (4 : ℝ) ∂mu) ≤
      ∫ omega, G omega ∂mu :=
    integral_mono hcmp hGint (fun omega => hle omega)
  have hpull : (∫ omega, ((I.card : ℝ))⁻¹ * ∑ R ∈ I, F R omega ^ (4 : ℝ) ∂mu) =
      ((I.card : ℝ))⁻¹ * ∫ omega, ∑ R ∈ I, F R omega ^ (4 : ℝ) ∂mu :=
    integral_const_mul _ _
  change cubeFamilyAverage I (fun R => ∫ omega, F R omega ^ (4 : ℝ) ∂mu) ≤ _
  change ((I.card : ℝ))⁻¹ * ∑ R ∈ I, (∫ omega, F R omega ^ (4 : ℝ) ∂mu) ≤ _
  rw [hswap, ← hpull]
  exact hmono

/-! ## The `L^8` carrier of `e.km.kn.Lp`, made measurable -/

/-- The volume-normalized `L^8` norm of the fresh shell on `cu_K` is a random
variable. -/
theorem measurable_streamIncrementLpNorm_eight (l n m : ℤ) :
    Measurable (Provider.Stream.streamIncrementLpNorm (d := d) 8 l n m) := by
  have hmass := Provider.Stream.measurable_streamIncrementLpMass_for_momentBoosted
    (d := d) (p := 8) (by norm_num) l n m
  exact hmass.pow_const _

/-- **The fourth moment of the fresh-shell `L^8` norm on `cu_K`.**

`e.km.kn.Lp` (the *proved* frozen theorem) splits `||k_m -
k_n||^2_{L8bar(cu_K)}` into a head and a `Gamma_1` tail whose amplitude carries
the factor `3^{-(K-m)d/8} <= 1`.  Replacing the anchor's tail variable by the
*measurable* positive part `max(L^2 - head, 0)` --- which the anchor's own
bound dominates --- makes the second moment available, and the fourth moment of
`L` follows.

Both the bound and the integrability are produced; no measurability of the
anchor's own tail variable is assumed. -/
theorem exists_integral_streamIncrementLpNorm_eight_pow_four_le (d : ℕ) :
    ∃ Ckm : ℝ, 0 < Ckm ∧
      ∀ (M : ABKModel d) (K n m : ℤ), n < m → m ≤ K →
        Integrable (fun omega : CutoffSample d =>
            Provider.Stream.streamIncrementLpNorm 8 K n m omega.val ^ (4 : ℕ))
          (cutoffSampleLaw M).toMeasure ∧
        (∫ omega : CutoffSample d,
            Provider.Stream.streamIncrementLpNorm 8 K n m omega.val ^ (4 : ℕ)
            ∂(cutoffSampleLaw M).toMeasure) ≤
          Ckm * (((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (2 : ℕ) := by
  classical
  obtain ⟨C, hCpos, hsplit⟩ := Corrector.exists_streamIncrementLpNormSq_head_tail d
  refine ⟨2 * C ^ (2 : ℕ) * (1 + 16 * Real.exp 1 ^ (2 : ℕ)), by positivity, ?_⟩
  intro M K n m hnm hmK
  obtain ⟨T, hT0, hTle, hTtail⟩ := hsplit M K n m hnm hmK
  set L : ShellSeq d → ℝ := Provider.Stream.streamIncrementLpNorm 8 K n m with hL
  set A0 : ℝ := min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
    with hA0
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hnmR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hA0pos : 0 < A0 := by
    have hmin : 0 < min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) :=
      lt_min (inv_pos.2 hgamma0) (by linarith)
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [hA0]
    exact mul_pos hmin h3
  have hA0le : A0 ≤ ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) h3
  set decay : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) with hdecay
  have hdecay_le : decay ≤ 1 := by
    have hexp : -((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ)) ≤ 0 := by
      have hKm : (0 : ℝ) ≤ (K : ℝ) - (m : ℝ) := by
        have : (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK
        linarith
      have hd8 : (0 : ℝ) ≤ (d : ℝ) / 8 := by positivity
      nlinarith
    calc decay ≤ (3 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 := Real.rpow_zero 3
  -- the measurable positive part
  set Gp : ShellSeq d → ℝ := fun omega => max (L omega ^ (2 : ℕ) - C * A0) 0 with hGp
  have hGp0 : ∀ omega, 0 ≤ Gp omega := fun omega => le_max_right _ _
  have hGple : ∀ omega, Gp omega ≤ T omega := by
    intro omega
    rw [hGp]
    exact max_le (by linarith [hTle omega]) (hT0 omega)
  have hLsq : ∀ omega, L omega ^ (2 : ℕ) ≤ C * A0 + Gp omega := by
    intro omega
    have := le_max_left (L omega ^ (2 : ℕ) - C * A0) 0
    rw [hGp]
    linarith
  have hGpmeas : Measurable Gp := by
    rw [hGp]
    exact ((measurable_streamIncrementLpNorm_eight (d := d) K n m).pow_const 2).sub
      measurable_const |>.max measurable_const
  have hGptail : IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
      Gp (C * A0 * decay) := hTtail.of_le hGple
  -- transport to the cutoff sample law
  set mu : Measure (CutoffSample d) := (cutoffSampleLaw M).toMeasure with hmu
  have hGpc_tail := Provider.Stream.isBigOWith_cutoffSampleLaw_comp_val (M := M) hGptail
  have hGpc_meas : Measurable fun omega : CutoffSample d => Gp omega.val :=
    hGpmeas.comp measurable_subtype_coe
  have hGpcsq : (∫ omega : CutoffSample d, Gp omega.val ^ (2 : ℕ) ∂mu) ≤
      16 * Real.exp 1 ^ (2 : ℕ) * (C * A0 * decay) ^ (2 : ℕ) :=
    integral_sq_le_of_isBigOWith_gammaSigma_one' (μ := mu)
      (by positivity) (fun omega => hGp0 omega.val) hGpc_meas.aemeasurable hGpc_tail
  have hGpcint : Integrable (fun omega : CutoffSample d => Gp omega.val ^ (2 : ℕ)) mu := by
    have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := fun omega : CutoffSample d => Gp omega.val)
      (K := C * A0 * decay) (σ := 1) (p := 2) (by norm_num) (by positivity) (by norm_num)
      (fun omega => hGp0 omega.val) hGpc_meas.aemeasurable hGpc_tail
    refine h.congr (Filter.Eventually.of_forall fun omega => ?_)
    change Gp omega.val ^ (2 : ℝ) = Gp omega.val ^ (2 : ℕ)
    rw [← Real.rpow_natCast (Gp omega.val) 2]
    norm_num
  -- the pathwise fourth-power majorant
  set maj : CutoffSample d → ℝ := fun omega =>
    2 * ((C * A0) ^ (2 : ℕ) + Gp omega.val ^ (2 : ℕ)) with hmaj
  have hmajint : Integrable maj mu := by
    rw [hmaj]
    exact ((integrable_const _).add hGpcint).const_mul 2
  have hdom : ∀ omega : CutoffSample d, L omega.val ^ (4 : ℕ) ≤ maj omega := by
    intro omega
    have h1 := hLsq omega.val
    have h2 : (0 : ℝ) ≤ L omega.val ^ (2 : ℕ) := by positivity
    have h3 : (0 : ℝ) ≤ C * A0 := by positivity
    have h4 : (0 : ℝ) ≤ Gp omega.val := hGp0 omega.val
    have hsq : L omega.val ^ (4 : ℕ) = (L omega.val ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    rw [hsq, hmaj]
    nlinarith [sq_nonneg (C * A0 - Gp omega.val)]
  have hLmeas : Measurable fun omega : CutoffSample d => L omega.val ^ (4 : ℕ) :=
    (((measurable_streamIncrementLpNorm_eight (d := d) K n m)).comp
      measurable_subtype_coe).pow_const 4
  have hLint : Integrable (fun omega : CutoffSample d => L omega.val ^ (4 : ℕ)) mu := by
    refine hmajint.mono' hLmeas.aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L omega.val ^ (4 : ℕ))]
    exact hdom omega
  refine ⟨hLint, ?_⟩
  have hmono : (∫ omega : CutoffSample d, L omega.val ^ (4 : ℕ) ∂mu) ≤ ∫ omega, maj omega ∂mu :=
    integral_mono hLint hmajint hdom
  have hmajval : (∫ omega, maj omega ∂mu) =
      2 * ((C * A0) ^ (2 : ℕ) + ∫ omega : CutoffSample d, Gp omega.val ^ (2 : ℕ) ∂mu) := by
    rw [hmaj, integral_const_mul, integral_add (integrable_const _) hGpcint, integral_const]
    simp
  have hdecaysq : (C * A0 * decay) ^ (2 : ℕ) ≤ (C * A0) ^ (2 : ℕ) := by
    have hd0 : (0 : ℝ) ≤ decay := (Real.rpow_pos_of_pos (by norm_num) _).le
    have hCA : (0 : ℝ) ≤ C * A0 := by positivity
    have hdsq : decay ^ (2 : ℕ) ≤ 1 := by nlinarith [hd0, hdecay_le]
    calc (C * A0 * decay) ^ (2 : ℕ) = (C * A0) ^ (2 : ℕ) * decay ^ (2 : ℕ) := by ring
      _ ≤ (C * A0) ^ (2 : ℕ) * 1 := mul_le_mul_of_nonneg_left hdsq (by positivity)
      _ = (C * A0) ^ (2 : ℕ) := mul_one _
  have hA0sq : (C * A0) ^ (2 : ℕ) ≤
      C ^ (2 : ℕ) * (((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (2 : ℕ) := by
    have hstep := pow_le_pow_left₀ hA0pos.le hA0le 2
    calc (C * A0) ^ (2 : ℕ) = C ^ (2 : ℕ) * A0 ^ (2 : ℕ) := by ring
      _ ≤ C ^ (2 : ℕ) *
            (((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  have hexp0 : (0 : ℝ) ≤ Real.exp 1 ^ (2 : ℕ) := by positivity
  calc (∫ omega : CutoffSample d, L omega.val ^ (4 : ℕ) ∂mu)
      ≤ 2 * ((C * A0) ^ (2 : ℕ) + ∫ omega : CutoffSample d, Gp omega.val ^ (2 : ℕ) ∂mu) := by
        rw [← hmajval]; exact hmono
    _ ≤ 2 * ((C * A0) ^ (2 : ℕ) +
          16 * Real.exp 1 ^ (2 : ℕ) * (C * A0) ^ (2 : ℕ)) := by
        have := hGpcsq.trans (mul_le_mul_of_nonneg_left hdecaysq (by positivity))
        linarith
    _ = (1 + 16 * Real.exp 1 ^ (2 : ℕ)) * (2 * (C * A0) ^ (2 : ℕ)) := by ring
    _ ≤ (1 + 16 * Real.exp 1 ^ (2 : ℕ)) *
          (2 * (C ^ (2 : ℕ) *
            (((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (2 : ℕ))) := by
        have hc : (0 : ℝ) ≤ 1 + 16 * Real.exp 1 ^ (2 : ℕ) := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hc
    _ = 2 * C ^ (2 : ℕ) * (1 + 16 * Real.exp 1 ^ (2 : ℕ)) *
          (((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (2 : ℕ) := by ring

/-! ## `hvmem` and `hgradM` at the closure's Dirichlet family -/

/-- **`hvmem` and `hgradM`, proved.**

One constant, produced before the model, such that at every admissible pair
`(n, n+h)` and every localization scale `K >= n+h` the closure's own Dirichlet
family satisfies both Step-5 gradient legs: the cube averages are `L^4` in the
sample, and the square root of their grid fourth moment obeys
`e.nablaw.in.L.eight` in the shape the manuscript reads it.

The depth `j` is arbitrary: the grid step is the tiling identity, which holds at
every depth.

Proved from `Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le` and
`ApproximateRecurrence.memLp_eight_grad_freshShellDirichlet`, hence from the
external Calderon--Zygmund input
`Algsuperdiff.Frozen.External.calderon_zygmund`. -/
theorem exists_step5GradMomentConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ) (e : Vec d),
        vecNorm e ≤ 1 → 0 < h → n + (h : ℤ) ≤ (K : ℤ) →
        (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
          MemLp (fun omega : CutoffSample d =>
            vecNorm (cubeAverageVec R
              (fun x => (alongIncrementPath n h
                (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
                  omega.val).toH1Function.grad x))) 4 (cutoffSampleLaw M).toMeasure) ∧
        (gridFourthMoment (cutoffSampleLaw M).toMeasure
              (descendantsAtDepth (originCube d (K : ℤ)) j)
              (fun (R : TriadicCube d) (omega : CutoffSample d) =>
                vecNorm (cubeAverageVec R
                  (fun x => (alongIncrementPath n h
                    (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
                      omega.val).toH1Function.grad x))))
            ^ ((2 : ℝ)⁻¹) ≤
          C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
            (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Ccz, hCczpos, hCZ⟩ := Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le (d := d) hd
  obtain ⟨Ckm, hCkmpos, hkm⟩ := exists_integral_streamIncrementLpNorm_eight_pow_four_le d
  refine ⟨(32 * Ccz ^ (2 : ℕ) * Ckm) ^ ((2 : ℝ)⁻¹),
    Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro M n h K j e he hh hmK
  set m : ℤ := n + (h : ℤ) with hm
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set sinv : ℝ := ((Annealed.sigmaBar M n : ℝ))⁻¹ with hsinv
  have hsig0 : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hsinv0 : (0 : ℝ) ≤ sinv := (inv_pos.2 hsig0).le
  have hnm : n < m := by
    have hpos : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
    omega
  set wD : ShellSeq d → H10Function (openCubeSet Q) := fun omega =>
    alongIncrementPath n h (closureDirichletFamily sinv e K) omega with hwDdef
  have hsol : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wD omega)
        (fun x => -Corrector.streamForcing sinv omega n m e x) := fun omega =>
    isZeroTraceDirichletRhsWeakSolution_alongIncrementPath sinv e K n h omega
  set L : ShellSeq d → ℝ := Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n m with hL
  set mu : Measure (CutoffSample d) := (cutoffSampleLaw M).toMeasure with hmu
  set u : CutoffSample d → (Vec d → Vec d) := fun omega =>
    fun x => (wD omega.val).toH1Function.grad x with hu
  -- the `L^8` membership on the localization cube
  have hmem8 : ∀ omega : CutoffSample d, MemLp (u omega) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := fun omega =>
    memLp_eight_grad_freshShellDirichlet hd Q sinv omega.val n m e (wD omega.val)
      (hsol omega.val)
  -- the pathwise Calderon--Zygmund bound
  have hND : ∀ omega : CutoffSample d,
      cubeEuclideanLpNorm Q 8 (u omega) ^ (2 : ℕ) ≤
        2 * Ccz * sinv ^ (2 : ℕ) * L omega.val ^ (2 : ℕ) := by
    intro omega
    obtain ⟨wN, hwN⟩ := Corrector.exists_isMeanZeroNeumannRhsWeakSolution_streamForcing
      Q sinv omega.val n m e
    have hcz := hCZ Q (Corrector.streamForcing sinv omega.val n m e)
      (Corrector.streamForcing sinv omega.val n m e)
      (Corrector.continuous_streamForcing _ _ _ _ _)
      (Corrector.continuous_streamForcing _ _ _ _ _)
      (wD omega.val) (hsol omega.val) wN hwN
    have hNN : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ (2 : ℕ) := by
      positivity
    have hstr := Corrector.cubeEuclideanLpNorm_streamForcing_le (d := d) hsinv0
      (K : ℤ) n m omega.val he
    have hf0 : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8
        (Corrector.streamForcing sinv omega.val n m e) := cubeEuclideanLpNorm_nonneg _ _ _
    have hfsq : cubeEuclideanLpNorm Q 8
        (Corrector.streamForcing sinv omega.val n m e) ^ (2 : ℕ) ≤
        sinv ^ (2 : ℕ) * L omega.val ^ (2 : ℕ) := by
      have h := pow_le_pow_left₀ hf0 hstr 2
      calc cubeEuclideanLpNorm Q 8
            (Corrector.streamForcing sinv omega.val n m e) ^ (2 : ℕ)
          ≤ (sinv * L omega.val) ^ (2 : ℕ) := h
        _ = sinv ^ (2 : ℕ) * L omega.val ^ (2 : ℕ) := by ring
    nlinarith [hcz, hNN, hfsq, hCczpos.le]
  -- the majorant, in terms of the measurable `L^8` carrier alone
  set G : CutoffSample d → ℝ := fun omega =>
    32 * Ccz ^ (2 : ℕ) * sinv ^ (4 : ℕ) * L omega.val ^ (4 : ℕ) with hG
  obtain ⟨hLint, hLbound⟩ := hkm M (K : ℤ) n m hnm hmK
  have hGint : Integrable G mu := by
    rw [hG]
    exact hLint.const_mul _
  have hgridpt : ∀ omega : CutoffSample d,
      cubeFamilyAverage (descendantsAtDepth Q j)
        (fun R => vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℝ)) ≤ G omega := by
    intro omega
    have hconv : (fun R : TriadicCube d => vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℝ)) =
        fun R : TriadicCube d => vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℕ) := by
      funext R
      rw [← Real.rpow_natCast (vecNorm (cubeAverageVec R (u omega))) 4]
      norm_num
    rw [hconv, ← descendantsAverage_eq_cubeFamilyAverage]
    refine (descendantsAverage_vecNorm_cubeAverageVec_pow_four_le Q j (u omega)
      (hmem8 omega)).trans ?_
    have hN0 : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 (u omega) := cubeEuclideanLpNorm_nonneg _ _ _
    have hfour : cubeEuclideanLpNorm Q 8 (u omega) ^ (4 : ℕ) ≤
        4 * Ccz ^ (2 : ℕ) * sinv ^ (4 : ℕ) * L omega.val ^ (4 : ℕ) := by
      have hsq := hND omega
      have hb0 : (0 : ℝ) ≤ 2 * Ccz * sinv ^ (2 : ℕ) * L omega.val ^ (2 : ℕ) := by
        have := hCczpos.le
        positivity
      have := pow_le_pow_left₀ (by positivity :
        (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 (u omega) ^ (2 : ℕ)) hsq 2
      calc cubeEuclideanLpNorm Q 8 (u omega) ^ (4 : ℕ)
          = (cubeEuclideanLpNorm Q 8 (u omega) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
        _ ≤ (2 * Ccz * sinv ^ (2 : ℕ) * L omega.val ^ (2 : ℕ)) ^ (2 : ℕ) := this
        _ = 4 * Ccz ^ (2 : ℕ) * sinv ^ (4 : ℕ) * L omega.val ^ (4 : ℕ) := by ring
    rw [hG]
    linarith
  -- measurability of the per-cube observable
  have hFmeas : ∀ R ∈ descendantsAtDepth Q j,
      Measurable fun omega : CutoffSample d => vecNorm (cubeAverageVec R (u omega)) := by
    intro R hR
    exact (continuous_vecNorm (d := d)).measurable.comp
      ((measurable_cubeAverageVec_freshShellDirichletGrad hR sinv n m e wD hsol).comp
        measurable_subtype_coe)
  have hFint : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega : CutoffSample d =>
        vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℝ)) mu := by
    intro R hR
    have hmeas := (hFmeas R hR)
    have hconv : (fun omega : CutoffSample d =>
        vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℝ)) =
        fun omega : CutoffSample d => vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℕ) := by
      funext omega
      rw [← Real.rpow_natCast (vecNorm (cubeAverageVec R (u omega))) 4]
      norm_num
    rw [hconv]
    refine (hGint.const_mul ((descendantsAtDepth Q j).card : ℝ)).mono'
      (hmeas.pow_const 4).aestronglyMeasurable ?_
    filter_upwards with omega
    have hbase := vecNorm_cubeAverageVec_pow_four_le_card Q j hR (u omega) (hmem8 omega)
    have hcard0 : (0 : ℝ) ≤ ((descendantsAtDepth Q j).card : ℝ) := by positivity
    have hstep : ((descendantsAtDepth Q j).card : ℝ) *
        (8 * cubeEuclideanLpNorm Q 8 (u omega) ^ (4 : ℕ)) ≤
        ((descendantsAtDepth Q j).card : ℝ) * G omega := by
      refine mul_le_mul_of_nonneg_left ?_ hcard0
      have hsum := hgridpt omega
      have hN0 : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 (u omega) := cubeEuclideanLpNorm_nonneg _ _ _
      have hsq := hND omega
      have hb0 : (0 : ℝ) ≤ 2 * Ccz * sinv ^ (2 : ℕ) * L omega.val ^ (2 : ℕ) := by
        have := hCczpos.le
        positivity
      have h4 := pow_le_pow_left₀ (by positivity :
        (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 (u omega) ^ (2 : ℕ)) hsq 2
      have hrw : cubeEuclideanLpNorm Q 8 (u omega) ^ (4 : ℕ) =
          (cubeEuclideanLpNorm Q 8 (u omega) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      have hexp : (2 * Ccz * sinv ^ (2 : ℕ) * L omega.val ^ (2 : ℕ)) ^ (2 : ℕ) =
          4 * Ccz ^ (2 : ℕ) * sinv ^ (4 : ℕ) * L omega.val ^ (4 : ℕ) := by ring
      rw [hG]
      rw [hrw]
      nlinarith [h4, hexp]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℕ))]
    exact hbase.trans hstep
  refine ⟨?_, ?_⟩
  · -- `hvmem`
    intro R hR
    have hmeas := hFmeas R hR
    refine (integrable_norm_rpow_iff (p := (4 : ℝ≥0∞)) hmeas.aestronglyMeasurable
      (by norm_num) (by norm_num)).1 ?_
    have hfun : (fun omega : CutoffSample d =>
        ‖vecNorm (cubeAverageVec R (u omega))‖ ^ ((4 : ℝ≥0∞).toReal)) =
        fun omega : CutoffSample d => vecNorm (cubeAverageVec R (u omega)) ^ (4 : ℝ) := by
      funext omega
      rw [Real.norm_eq_abs, abs_of_nonneg (vecNorm_nonneg _)]
      norm_num
    rw [hfun]
    exact hFint R hR
  · -- `hgradM`
    have hgrid := gridFourthMoment_le_integral_of_cubeFamilyAverage_le mu
      (descendantsAtDepth Q j)
      (fun (R : TriadicCube d) (omega : CutoffSample d) =>
        vecNorm (cubeAverageVec R (u omega))) G hFint hGint hgridpt
    have hGval : (∫ omega, G omega ∂mu) ≤
        32 * Ccz ^ (2 : ℕ) * Ckm * sinv ^ (4 : ℕ) *
          (((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (2 : ℕ) := by
      rw [hG, integral_const_mul]
      have hc0 : (0 : ℝ) ≤ 32 * Ccz ^ (2 : ℕ) * sinv ^ (4 : ℕ) := by positivity
      have := mul_le_mul_of_nonneg_left hLbound hc0
      nlinarith [this]
    have hdiff : ((m : ℝ) - (n : ℝ)) = (h : ℝ) := by rw [hm]; push_cast; ring
    rw [hdiff] at hGval
    set W : ℝ := (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hW
    have hW0 : (0 : ℝ) ≤ W := by
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
        (Real.rpow_pos_of_pos (by norm_num) _).le
      have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
      rw [hW]; positivity
    have hchain : gridFourthMoment mu (descendantsAtDepth Q j)
        (fun (R : TriadicCube d) (omega : CutoffSample d) =>
          vecNorm (cubeAverageVec R (u omega))) ≤
        (32 * Ccz ^ (2 : ℕ) * Ckm) * (sinv ^ (2 : ℕ) * W) ^ (2 : ℕ) := by
      refine hgrid.trans (hGval.trans (le_of_eq ?_))
      ring
    refine (Real.rpow_le_rpow (gridFourthMoment_nonneg _ _ _) hchain (by norm_num)).trans
      (le_of_eq ?_)
    have hc0 : (0 : ℝ) ≤ 32 * Ccz ^ (2 : ℕ) * Ckm := by positivity
    have hsw0 : (0 : ℝ) ≤ sinv ^ (2 : ℕ) * W := by positivity
    rw [Real.mul_rpow hc0 (by positivity)]
    have hroot1 : ((sinv ^ (2 : ℕ) * W) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = sinv ^ (2 : ℕ) * W := by
      rw [← Real.rpow_natCast (sinv ^ (2 : ℕ) * W) 2, ← Real.rpow_mul hsw0]
      norm_num
    have hsq : sinv ^ (2 : ℕ) = (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ := by
      rw [hsinv, ← inv_pow]
    rw [hroot1, hsq, hW, hm]
    push_cast
    ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
