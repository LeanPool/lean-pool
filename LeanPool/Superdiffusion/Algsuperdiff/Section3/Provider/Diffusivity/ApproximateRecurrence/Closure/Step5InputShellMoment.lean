/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5Basket

/-!
# Step5InputShellMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hshell`: the grid fourth moment of the averaged fresh shell

`Closure.Step5Basket.step5GaugeEndpoint_closureFamilies_of_momentLegs` leaves
`hshell` as the binder

```
  ( avsum_{R in grid}  E[ |(k_{n+h} - k_n)_R|^4 ] )^{1/2}
      <=  C1 * h * 3^{2 cgamma (n+h)} ,
```

the grid being `descendantsAtDepth cu_K j` at `K - j = nmesh <= n` and `|.|` the
exact Euclidean matrix operator norm.  This module proves it.

## The route

The cube `R` has scale `nmesh <= n`, so `cu_R` sits inside the window
`z_R + cu_n` based at the cube's own site `z_R = triadicCubeShift R`.  On that
window ABK26's `e.km.kn.Linfty.smallcube` gives the deterministic domination
`|k_{n+h} - k_n|(x) <= translatedIncrementSupBound z_R n (n+h)`, so the cube
average of each entry is dominated by the same random variable, and

```
  |(k_{n+h} - k_n)_R|  <=  d^2 * translatedIncrementSupBound z_R n (n+h) .
```

The probabilistic half is the proved weak-Orlicz tail
`Provider.Stream.isBigOWith_gammaSigma_translatedIncrementSupBound_cutoffLaw`,
whose amplitude is uniform in the base point; CoarseGraining's layer-cake
moment bound at `p = 4`, `sigma = 2` turns it into a *per-cube* fourth moment
`<= (C_d sqrt h 3^{cgamma (n+h)})^4`, and a uniform per-cube bound passes to
the grid average by `gridFourthMoment_le_of_forall_le`.  Taking the square root
gives the display with `C1 = step5ShellMomentConst d`.

Nothing here is asymptotic in `K`: the per-cube bound does not see the
localization scale at all.

## References

* ABK26, `e.km.kn.Lp`; `e.km.kn.Linfty.smallcube`; Step 5.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cube average against a uniform bound on the open cube -/

/-- The cube average of an integrable scalar is dominated by a bound assumed on
the **open** cube alone: the closed and open forms of a triadic cube differ by a
null set. -/
theorem abs_cubeAverage_le_of_forall_openCubeSet (R : TriadicCube d) {g : Vec d → ℝ}
    {eps : ℝ} (heps : 0 ≤ eps) (hg : IntegrableOn g (cubeSet R) volume)
    (hb : ∀ x ∈ openCubeSet R, |g x| ≤ eps) : |cubeAverage R g| ≤ eps := by
  classical
  have hmem : ∀ᵐ x ∂(volume.restrict (cubeSet R)), x ∈ openCubeSet R := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact ae_restrict_mem (measurableSet_openCubeSet R)
  have haeeq : (fun x : Vec d => if x ∈ openCubeSet R then g x else (0 : ℝ))
      =ᵐ[volume.restrict (cubeSet R)] g := by
    filter_upwards [hmem] with x hx
    simp [hx]
  have hint : IntegrableOn (fun x : Vec d => if x ∈ openCubeSet R then g x else (0 : ℝ))
      (cubeSet R) volume := hg.congr haeeq.symm
  have havg : cubeAverage R (fun x : Vec d => if x ∈ openCubeSet R then g x else (0 : ℝ))
      = cubeAverage R g := cubeAverage_eq_of_ae_eq_on_cubeSet haeeq
  have hbase := Provider.Stream.abs_cubeAverage_sub_le R (c := (0 : ℝ)) (eps := eps) hint
    (by
      intro x _
      by_cases hxo : x ∈ openCubeSet R
      · simpa [hxo] using hb x hxo
      · simpa [hxo] using heps)
  rwa [havg, sub_zero] at hbase

/-! ## The deterministic per-cube domination -/

private theorem openCubeSet_originCube_mono {s n : ℤ} (h : s ≤ n) :
    openCubeSet (originCube d s) ⊆ openCubeSet (originCube d n) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3 : (3 : ℝ) ^ s ≤ (3 : ℝ) ^ n := zpow_le_zpow_right₀ (by norm_num) h
  have hpos : (0 : ℝ) < (3 : ℝ) ^ s := zpow_pos (by norm_num) s
  exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩

/-- A cube of scale at most `n` sits inside the window based at its own site. -/
theorem openCubeSet_subset_translateSet_openCubeSet_originCube {R : TriadicCube d}
    {n : ℤ} (hsc : R.scale ≤ n) :
    openCubeSet R ⊆ translateSet (triadicCubeShift R) (openCubeSet (originCube d n)) := by
  intro x hx
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R,
    mem_translateSet_iff_sub_mem] at hx
  rw [mem_translateSet_iff_sub_mem]
  exact openCubeSet_originCube_mono hsc hx

/-- **The averaged fresh shell is dominated by the small-cube `L^infty` bound at
the cube's own site.**  For a cube of scale at most `n` the entries of
`k_{n+h} - k_n` are dominated on `cu_R` by `translatedIncrementSupBound z_R`, and
the exact Euclidean operator norm is at most the entrywise `l^1` sum. -/
theorem matrixOperatorNorm_freshShellCubeAverage_le_translatedIncrementSupBound
    {R : TriadicCube d} {n : ℤ} (hsc : R.scale ≤ n) (omega : ShellSeq d) (m : ℤ) :
    matrixOperatorNorm (freshShellCubeAverage R omega n m) ≤
      (d : ℝ) ^ 2 *
        Provider.Stream.translatedIncrementSupBound (triadicCubeShift R) n m omega := by
  classical
  set T : ℝ := Provider.Stream.translatedIncrementSupBound (triadicCubeShift R) n m omega
    with hT
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d n) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
    exact ⟨by simp; linarith, by simp; linarith⟩
  have hT0 : (0 : ℝ) ≤ T := by
    have hbase := matrixOperatorNorm_nonneg
      (finiteShellIncrement omega n m (triadicCubeShift R))
    exact le_trans hbase
      (Provider.Stream.matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
        (triadicCubeShift R) omega n m
        (by
          rw [mem_translateSet_iff_sub_mem, sub_self]
          exact hzero))
  have hentry : ∀ i l : Fin d, |freshShellCubeAverage R omega n m i l| ≤ T := by
    intro i l
    have hint : IntegrableOn (fun x => finiteShellIncrement omega n m x i l)
        (cubeSet R) volume :=
      integrableOn_cubeSet_of_continuous R (continuous_finiteShellIncrement_entry omega n m i l)
    have hb : ∀ x ∈ openCubeSet R, |finiteShellIncrement omega n m x i l| ≤ T := by
      intro x hx
      have hop := Provider.Stream.matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
        (triadicCubeShift R) omega n m
        (openCubeSet_subset_translateSet_openCubeSet_originCube hsc hx)
      exact le_trans (abs_entry_le_matrixOperatorNorm _ i l) hop
    have hcube := abs_cubeAverage_le_of_forall_openCubeSet R hT0 hint hb
    rwa [freshShellCubeAverage_apply]
  calc matrixOperatorNorm (freshShellCubeAverage R omega n m)
      ≤ ∑ p : Fin d × Fin d, |freshShellCubeAverage R omega n m p.1 p.2| :=
        Provider.Stream.matrixOperatorNorm_le_sum_univ_abs_entry _
    _ ≤ ∑ _p : Fin d × Fin d, T := Finset.sum_le_sum fun p _ => hentry p.1 p.2
    _ = (d : ℝ) ^ 2 * T := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-! ## The per-cube fourth moment -/

/-- The absolute dimensional constant of `hshell`: the entrywise-`l^1` comparison
`d^2` of the Euclidean operator norm, times CoarseGraining's layer-cake moment
constant at `p = 4`, `sigma = 2`, times the small-cube `L^infty` constant of
`e.km.kn.Linfty.smallcube`, squared. -/
def step5ShellMomentBase (d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 * (IndependentSums.gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹)) *
    Provider.Stream.streamLinftyConst d

/-- The constant of `hshell`. -/
def step5ShellMomentConst (d : ℕ) : ℝ := step5ShellMomentBase d ^ (2 : ℕ)

theorem step5ShellMomentBase_pos (hd : 0 < d) : 0 < step5ShellMomentBase d := by
  have h1 : (0 : ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have h2 : (0 : ℝ) < (4 : ℝ) ^ ((2 : ℝ)⁻¹) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : 0 < Provider.Stream.streamLinftyConst d := Provider.Stream.streamLinftyConst_pos hd
  have h4 : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  unfold step5ShellMomentBase
  positivity

theorem step5ShellMomentConst_nonneg (d : ℕ) : 0 ≤ step5ShellMomentConst d := by
  unfold step5ShellMomentConst
  positivity

/-- The measurability of the averaged fresh shell in the sample, on the closure's
own carrier. -/
theorem measurable_cutoffSample_matrixOperatorNorm_freshShellCubeAverage
    {R Q : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) (n m : ℤ) :
    Measurable fun omega : CutoffSample d =>
      matrixOperatorNorm (freshShellCubeAverage R omega.val n m) :=
  (Algsuperdiff.Frozen.Assumptions.ShellField.continuous_matrixOperatorNorm
      (d := d)).measurable.comp
    ((measurable_freshShellCubeAverage hR n m).comp measurable_subtype_coe)

/-- **The weak-Orlicz tail of the averaged fresh shell**, at the amplitude of
`e.km.kn.Linfty.smallcube` and the entrywise constant `d^2`.  The proved tail
is uniform in the base point, so this bound does not see the cube. -/
theorem isBigOWith_gammaSigma_two_matrixOperatorNorm_freshShellCubeAverage
    (M : ABKModel d) {R : TriadicCube d} {n m : ℤ} (hsc : R.scale ≤ n) (hnm : n < m) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : CutoffSample d =>
        matrixOperatorNorm (freshShellCubeAverage R omega.val n m))
      ((d : ℝ) ^ 2 * (Provider.Stream.streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)))) := by
  have hd2pos : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  exact ((Provider.Stream.isBigOWith_gammaSigma_translatedIncrementSupBound_cutoffLaw
      M hnm (triadicCubeShift R)).const_mul hd2pos).of_le fun omega =>
    matrixOperatorNorm_freshShellCubeAverage_le_translatedIncrementSupBound hsc omega.val m

/-- **The per-cube fourth moment of the averaged fresh shell.** -/
theorem integral_rpow_four_matrixOperatorNorm_freshShellCubeAverage_le [NeZero d]
    (M : ABKModel d) {R : TriadicCube d} {Q : TriadicCube d} {jd : ℕ}
    (hR : R ∈ descendantsAtDepth Q jd) {n m : ℤ} (hsc : R.scale ≤ n) (hnm : n < m) :
    (∫ omega : CutoffSample d,
        matrixOperatorNorm (freshShellCubeAverage R omega.val n m) ^ (4 : ℝ)
        ∂(cutoffSampleLaw M).toMeasure) ≤
      step5ShellMomentBase d ^ (4 : ℕ) *
        ((m : ℝ) - (n : ℝ)) ^ (2 : ℕ) * (3 : ℝ) ^ (4 * (M.gamma * (m : ℝ))) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set mn : ℝ := min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) with hmn
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hmnpos : 0 < mn := by
    have hnmR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    exact lt_min (Real.sqrt_pos.2 (inv_pos.2 hgamma0)) (Real.sqrt_pos.2 (by linarith))
  set A : ℝ := Provider.Stream.streamLinftyConst d * mn * (3 : ℝ) ^ (M.gamma * (m : ℝ))
    with hA
  have hApos : 0 < A := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hc : 0 < Provider.Stream.streamLinftyConst d :=
      Provider.Stream.streamLinftyConst_pos hd0
    rw [hA]
    positivity
  have hd2pos : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    positivity
  have hY := isBigOWith_gammaSigma_two_matrixOperatorNorm_freshShellCubeAverage
    M (R := R) hsc hnm
  have hYmeas : AEMeasurable (fun omega : CutoffSample d =>
      matrixOperatorNorm (freshShellCubeAverage R omega.val n m))
      (cutoffSampleLaw M).toMeasure :=
    (measurable_cutoffSample_matrixOperatorNorm_freshShellCubeAverage hR n m).aemeasurable
  have hmoment := IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    (μ := (cutoffSampleLaw M).toMeasure)
    (Y := fun omega : CutoffSample d =>
      matrixOperatorNorm (freshShellCubeAverage R omega.val n m))
    (K := (d : ℝ) ^ 2 * A) (σ := 2) (p := 4) (by norm_num)
    (by positivity) (by norm_num)
    (fun omega => matrixOperatorNorm_nonneg _) hYmeas hY
  refine hmoment.trans ?_
  -- rewrite the layer-cake constant into the module's own form
  have hbase : IndependentSums.gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) *
      ((d : ℝ) ^ 2 * A) =
      step5ShellMomentBase d * (mn * (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
    rw [hA, step5ShellMomentBase]
    ring
  have houter : (step5ShellMomentBase d * (mn * (3 : ℝ) ^ (M.gamma * (m : ℝ)))) ^ (4 : ℝ)
      = (step5ShellMomentBase d * (mn * (3 : ℝ) ^ (M.gamma * (m : ℝ)))) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast (step5ShellMomentBase d * (mn * (3 : ℝ) ^ (M.gamma * (m : ℝ)))) 4]
    norm_num
  rw [hbase, houter]
  have hmnfour : mn ^ (4 : ℕ) ≤ ((m : ℝ) - (n : ℝ)) ^ (2 : ℕ) := by
    have hle : mn ≤ Real.sqrt ((m : ℝ) - (n : ℝ)) := min_le_right _ _
    have hsq : mn ^ (2 : ℕ) ≤ (m : ℝ) - (n : ℝ) := by
      have := pow_le_pow_left₀ hmnpos.le hle 2
      rwa [Real.sq_sqrt (by
        have hnmR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
        linarith)] at this
    have hmn0 : (0 : ℝ) ≤ mn ^ (2 : ℕ) := by positivity
    calc mn ^ (4 : ℕ) = (mn ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ ((m : ℝ) - (n : ℝ)) ^ (2 : ℕ) := pow_le_pow_left₀ hmn0 hsq 2
  have h3four : ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ (4 : ℕ) =
      (3 : ℝ) ^ (4 * (M.gamma * (m : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (m : ℝ))) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hbase0 : (0 : ℝ) ≤ step5ShellMomentBase d := (step5ShellMomentBase_pos hd0).le
  have h30 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  calc (step5ShellMomentBase d * (mn * (3 : ℝ) ^ (M.gamma * (m : ℝ)))) ^ (4 : ℕ)
      = step5ShellMomentBase d ^ (4 : ℕ) * mn ^ (4 : ℕ) *
          ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ (4 : ℕ) := by ring
    _ ≤ step5ShellMomentBase d ^ (4 : ℕ) * ((m : ℝ) - (n : ℝ)) ^ (2 : ℕ) *
          ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ (4 : ℕ) := by
        have hc : (0 : ℝ) ≤ step5ShellMomentBase d ^ (4 : ℕ) := by positivity
        have hp : (0 : ℝ) ≤ ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ (4 : ℕ) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmnfour hc) hp
    _ = step5ShellMomentBase d ^ (4 : ℕ) * ((m : ℝ) - (n : ℝ)) ^ (2 : ℕ) *
          (3 : ℝ) ^ (4 * (M.gamma * (m : ℝ))) := by rw [h3four]

/-! ## `hshell` on the closure's grid -/

/-- **`hshell`, proved.**  The square root of the grid fourth moment of the
averaged fresh shell is at most h 3^{2 cgamma (n+h)}`, at the explicit absolute
constant = step5ShellMomentConst d`.

This is `e.km.kn.Lp` in the shape the Hoelder step consumes it, read on the
closure's own grid `descendantsAtDepth cu_K j` at `K - j = nmesh <= n`.  The
bound is uniform in the localization scale `K`. -/
theorem gridFourthMoment_matrixOperatorNorm_freshShellCubeAverage_root_le [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ) {nmesh : ℤ}
    (hmesh : (K : ℤ) - (j : ℤ) = nmesh) (hsc : nmesh ≤ n) (hh : 0 < h) :
    (gridFourthMoment (cutoffSampleLaw M).toMeasure
          (descendantsAtDepth (originCube d (K : ℤ)) j)
          (fun (R : TriadicCube d) (omega : CutoffSample d) =>
            matrixOperatorNorm (freshShellCubeAverage R omega.val n (n + (h : ℤ)))))
        ^ ((2 : ℝ)⁻¹) ≤
      step5ShellMomentConst d * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hbase0 : (0 : ℝ) ≤ step5ShellMomentBase d := (step5ShellMomentBase_pos hd0).le
  have hlt : n < n + (h : ℤ) := by
    have hpos : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
    omega
  have hhR : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hdiff : (((n + (h : ℤ) : ℤ) : ℝ)) - ((n : ℤ) : ℝ) = (h : ℝ) := by push_cast; ring
  set s : ℝ := ((n + (h : ℤ) : ℤ) : ℝ) with hs
  set B : ℝ := step5ShellMomentBase d ^ (4 : ℕ) * (h : ℝ) ^ (2 : ℕ) *
      (3 : ℝ) ^ (4 * (M.gamma * s)) with hB
  have hB0 : (0 : ℝ) ≤ B := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (4 * (M.gamma * s)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hB]
    positivity
  have hgrid : gridFourthMoment (cutoffSampleLaw M).toMeasure
      (descendantsAtDepth (originCube d (K : ℤ)) j)
      (fun (R : TriadicCube d) (omega : CutoffSample d) =>
        matrixOperatorNorm (freshShellCubeAverage R omega.val n (n + (h : ℤ)))) ≤ B := by
    refine gridFourthMoment_le_of_forall_le _ _ _ hB0 fun R hR => ?_
    have hRscale : R.scale ≤ n := by
      rw [scale_of_mem_descendantsAtDepth_originCube hR, hmesh]
      exact hsc
    have hper := integral_rpow_four_matrixOperatorNorm_freshShellCubeAverage_le
      M hR hRscale hlt
    rwa [hdiff] at hper
  refine (Real.rpow_le_rpow (gridFourthMoment_nonneg _ _ _) hgrid (by norm_num)).trans
    (le_of_eq ?_)
  have hsplit1 : (0 : ℝ) ≤ step5ShellMomentBase d ^ (4 : ℕ) * (h : ℝ) ^ (2 : ℕ) := by
    positivity
  have h30 : (0 : ℝ) ≤ (3 : ℝ) ^ (4 * (M.gamma * s)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hc1 : (0 : ℝ) ≤ step5ShellMomentBase d ^ (4 : ℕ) := by positivity
  have hh2 : (0 : ℝ) ≤ (h : ℝ) ^ (2 : ℕ) := by positivity
  have hrootBase : (step5ShellMomentBase d ^ (4 : ℕ)) ^ ((2 : ℝ)⁻¹)
      = step5ShellMomentConst d := by
    rw [← Real.rpow_natCast (step5ShellMomentBase d) 4, ← Real.rpow_mul hbase0,
      step5ShellMomentConst, ← Real.rpow_natCast (step5ShellMomentBase d) 2]
    norm_num
  have hrootH : ((h : ℝ) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (h : ℝ) := by
    rw [← Real.rpow_natCast (h : ℝ) 2, ← Real.rpow_mul hhR]
    norm_num
  have hroot3 : ((3 : ℝ) ^ (4 * (M.gamma * s))) ^ ((2 : ℝ)⁻¹)
      = (3 : ℝ) ^ (2 * M.gamma * s) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hB, Real.mul_rpow hsplit1 h30, Real.mul_rpow hc1 hh2, hrootBase, hrootH, hroot3]

/-! ## `hAmem`: the `L^4` sample membership of the averaged fresh shell -/

/-- **`hAmem`, proved.**  The averaged fresh shell is `L^4` in the sample: its
weak-Orlicz tail is `Gamma_2`, and CoarseGraining's layer-cake integrability at
`p = 4` turns that into the fourth-power integrability. -/
theorem memLp_four_matrixOperatorNorm_freshShellCubeAverage [NeZero d] (M : ABKModel d)
    {R Q : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) {n m : ℤ}
    (hsc : R.scale ≤ n) (hnm : n < m) :
    MemLp (fun omega : CutoffSample d =>
      matrixOperatorNorm (freshShellCubeAverage R omega.val n m)) 4
      (cutoffSampleLaw M).toMeasure := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hmnpos : 0 < min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) := by
    have hnmR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    exact lt_min (Real.sqrt_pos.2 (inv_pos.2 hgamma0)) (Real.sqrt_pos.2 (by linarith))
  have hcpos : 0 < Provider.Stream.streamLinftyConst d :=
    Provider.Stream.streamLinftyConst_pos hd0
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hdpos : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    positivity
  have hmeas := measurable_cutoffSample_matrixOperatorNorm_freshShellCubeAverage hR
    (n := n) (m := m)
  refine (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
    (by norm_num) (by norm_num)).1 ?_
  have hfun : (fun omega : CutoffSample d =>
      ‖matrixOperatorNorm (freshShellCubeAverage R omega.val n m)‖ ^
        ((4 : ℝ≥0∞).toReal)) =
      fun omega : CutoffSample d =>
        matrixOperatorNorm (freshShellCubeAverage R omega.val n m) ^ (4 : ℝ) := by
    funext omega
    rw [Real.norm_eq_abs, abs_of_nonneg (matrixOperatorNorm_nonneg _)]
    norm_num
  rw [hfun]
  exact IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (μ := (cutoffSampleLaw M).toMeasure)
    (Y := fun omega : CutoffSample d =>
      matrixOperatorNorm (freshShellCubeAverage R omega.val n m))
    (σ := 2) (p := 4) (by norm_num) (by positivity) (by norm_num)
    (fun omega => matrixOperatorNorm_nonneg _) hmeas.aemeasurable
    (isBigOWith_gammaSigma_two_matrixOperatorNorm_freshShellCubeAverage M (R := R) hsc hnm)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
