/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.SiteFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Hypotheses
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedLocality
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale

/-!
# SiteFamilyFive

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The scale decomposition of the event `Q` at a lattice site

Section 5.2 of ABK26 applies the abstract percolation path bound on the rescaled
lattice `3^{n-1} ℤ^d ↦ ℤ^d`, to a family of bad events indexed by a site `z` and
a scale `L`.  This module defines that family and proves the two properties that
do not involve any probability: the family covers the complement of the event
`Q(3^{n-1} z + □_n, ε)`, and every one of its members is an event of the shells
of index at most `n + L` on the closed cube of its own site.

The event `Q(y + □_n, ε)` is the intersection of the good cube event at
`y + □_n` with the large-scale event `𝒥(y + □_n, Cinj⁻¹ ε γ^{-1/2})`, whose
defining sum runs over every shell of index at least `n`.  The good cube event is
an event of the cube itself; the large-scale sum is not, and this is why it is
resolved shell by shell:

```
B_0(z) = 𝒢(3^{n-1} z + □_n, ε)^c ∪ { shell n exceeds C_0 ε γ^{-1/2} } ,
B_L(z) = { shell n + L exceeds C_0 ε γ^{-1/2} · 3^{-L/8} } ,        L ≥ 1 .
```

## The two disclosed constants

1. **The threshold decay `δ = 1/8`** (`shellDecayBase`).  The thresholds must be
   summable, and the shell tail they produce carries the exponent
   `2 (1 - γ - δ)`, which the path bound needs to exceed `1`.  Both hold with
   `δ = 1/8` throughout the range `γ ≤ 1/4` of the scaling parameter, where
   `2 (1 - γ - δ) ≥ 5/4`.
2. **The threshold constant `C_0`** (`siteThresholdConst`).  The geometric sum of
   the thresholds is `C_0 (1 - 3^{-1/8})^{-1} ε γ^{-1/2}`, so the scale
   decomposition needs `C_0 ≤ Cinj⁻¹ (1 - 3^{-1/8})`, and
   `siteThresholdConst Cinj` is that largest admissible value.

## Main definitions

* `largeScaleShellTerm` — the `k`-th term `3^{(2-γ)n} ‖∇ j_k‖_{W^{1,∞}(y+□_n)}`
  of the large-scale sum on `y + □_n`.
* `shellDecayBase`, `shellThreshold`, `siteThresholdConst` — the thresholds.
* `shellExcessEvent`, `siteBadEventFive` — the events `B_L(z)`.

## Main results

* `mem_largeScaleEvent_iff_tsum` — the large-scale event as a series over the
  shells above the cube scale.
* `compl_qEvent_subset_iUnion_siteBadEventFive` — the scale decomposition.
* `measurableSet_goodCubeEvent` — measurability of the good cube event in the
  sample, with no hypothesis beyond the model.
* `measurableSet_siteBadEventFive_local`, `measurableSet_siteBadEventFive` — the
  locality and the measurability of every member of the family.

## References

* ABK26, the event `Q` and the chains of good cubes of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open HCPolySupport MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The closed cube as a sup ball, and the rescaled lattice point -/

theorem closedCubeAt_eq_closedBall (y : Vec d) (n : ℤ) :
    closedCubeAt y n = Metric.closedBall y ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
  have hr : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  ext x
  rw [Metric.mem_closedBall, dist_pi_le_iff hr]
  constructor
  · intro hx i
    simpa only [Real.dist_eq] using hx i
  · intro hx i
    simpa only [Real.dist_eq] using hx i

theorem rescaledLatticePoint_apply (n : ℤ) (z : Fin d → ℤ) (i : Fin d) :
    rescaledLatticePoint n z i = (3 : ℝ) ^ (n - 1) * (z i : ℝ) := by
  have h : Real.rpow 3 ((n : ℝ) - 1) = (3 : ℝ) ^ (n - 1) := by
    have hcast : ((n : ℝ) - 1) = ((n - 1 : ℤ) : ℝ) := by push_cast; ring
    rw [hcast]
    exact Real.rpow_intCast 3 (n - 1)
  simp only [rescaledLatticePoint, Pi.smul_apply, smul_eq_mul]
  rw [h]

/-! ## 2. The terms of the large-scale sum on one cube -/

/-- The `k`-th term of the large-scale sum on the cube `y + □_n`, namely
`3^{(2-γ) n} ‖∇ j_k‖_{W^{1,∞}(y+□_n)}`, realized by translating the shell. -/
def largeScaleShellTerm (M : ABKModel d) (n k : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
    Section4.Support.shellW1InfGradNorm n (ShellField.translate y (omega.1 k))

/-- The scales `k ≥ n` of the large-scale sum, enumerated as `k = n + L`. -/
def shellIndexEquiv (n : ℤ) : ℕ ≃ {k : ℤ // n ≤ k} where
  toFun L := ⟨n + (L : ℤ), by omega⟩
  invFun k := (k.1 - n).toNat
  left_inv L := by simp
  right_inv k := by
    ext
    simp only
    omega

/-- **The large-scale event as a series over the shells above the cube scale.**
-/
theorem mem_largeScaleEvent_iff_tsum (M : ABKModel d) (n : ℤ) (y : Vec d) (theta : ℝ)
    (omega : Cutoff.CutoffSample d) :
    omega ∈ largeScaleEvent M n y theta ↔
      (∑' L : ℕ, ENNReal.ofReal (largeScaleShellTerm M n (n + (L : ℤ)) y omega)) ≤
        ENNReal.ofReal theta := by
  have hre := (shellIndexEquiv n).tsum_eq
    (fun k : {k : ℤ // n ≤ k} =>
      ENNReal.ofReal (Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
        Section4.Support.shellW1InfGradNorm n
          ((Cutoff.translateCutoffSample y omega).1 k.1)))
  rw [mem_largeScaleEvent_iff]
  simp only [largeScaleEventBase, Set.mem_ofPred_eq]
  rw [← hre]
  rfl

/-! ## 3. The shell thresholds -/

/-- The geometric ratio `3^{-1/8}` of the shell thresholds: the decay exponent
of the scale-resolved thresholds is `δ = 1/8`. -/
def shellDecayBase : ℝ := (3 : ℝ) ^ (-(1 / 8) : ℝ)

theorem shellDecayBase_pos : 0 < shellDecayBase :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem shellDecayBase_lt_one : shellDecayBase < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The powers of the ratio are the printed decay `3^{-L/8}`. -/
theorem shellDecayBase_pow (L : ℕ) :
    shellDecayBase ^ L = (3 : ℝ) ^ (-((L : ℝ) / 8)) := by
  rw [shellDecayBase, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 8) : ℝ)) L,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf

/-- The threshold of the scale-`L` shell event:
`C_0 ε γ^{-1/2} 3^{-L/8}`. -/
def shellThreshold (M : ABKModel d) (C0 ep : ℝ) (L : ℕ) : ℝ :=
  C0 * ep * (Real.sqrt M.gamma)⁻¹ * shellDecayBase ^ L

theorem shellThreshold_nonneg (M : ABKModel d) {C0 ep : ℝ} (hC0 : 0 ≤ C0)
    (hep : 0 ≤ ep) (L : ℕ) : 0 ≤ shellThreshold M C0 ep L := by
  have h1 : (0 : ℝ) ≤ (Real.sqrt M.gamma)⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ shellDecayBase ^ L := pow_nonneg shellDecayBase_pos.le L
  have := mul_nonneg (mul_nonneg (mul_nonneg hC0 hep) h1) h2
  simpa only [shellThreshold, mul_assoc, ge_iff_le] using this

theorem summable_shellThreshold (M : ABKModel d) (C0 ep : ℝ) :
    Summable (shellThreshold M C0 ep) := by
  exact (summable_geometric_of_lt_one shellDecayBase_pos.le shellDecayBase_lt_one).mul_left
    (C0 * ep * (Real.sqrt M.gamma)⁻¹)

theorem tsum_shellThreshold (M : ABKModel d) (C0 ep : ℝ) :
    (∑' L : ℕ, shellThreshold M C0 ep L) =
      C0 * ep * (Real.sqrt M.gamma)⁻¹ * (1 - shellDecayBase)⁻¹ := by
  simp only [shellThreshold]
  rw [tsum_mul_left, tsum_geometric_of_lt_one shellDecayBase_pos.le shellDecayBase_lt_one]

/-- **The admissible constant `C_0(d)`** of the scale decomposition: the
geometric sum of the thresholds is then exactly the threshold `Cinj⁻¹ ε γ^{-1/2}`
of the large-scale event. -/
def siteThresholdConst (Cinj : ℝ) : ℝ := Cinj⁻¹ * (1 - shellDecayBase)

theorem siteThresholdConst_pos {Cinj : ℝ} (hCinj : 0 < Cinj) :
    0 < siteThresholdConst Cinj := by
  have h : 0 < 1 - shellDecayBase := by linarith [shellDecayBase_lt_one]
  exact mul_pos (inv_pos.2 hCinj) h

theorem siteThresholdConst_mul_geometric (Cinj : ℝ) :
    siteThresholdConst Cinj * (1 - shellDecayBase)⁻¹ = Cinj⁻¹ := by
  have h : (1 : ℝ) - shellDecayBase ≠ 0 := by
    have hlt := shellDecayBase_lt_one
    intro hc
    linarith only [hlt, hc.ge, hc.le]
  rw [siteThresholdConst, mul_assoc, mul_inv_cancel₀ h, mul_one]

/-! ## 4. The site-indexed bad events -/

/-- **The scale-`L` shell event at the lattice site `z`**: the shell of index
`n + L` contributes more than its threshold to the large-scale sum on the cube
`3^{n-1} z + □_n`. -/
def shellExcessEvent (M : ABKModel d) (C0 ep : ℝ) (n : ℤ) (L : ℕ)
    (z : Percolation.Site d) : Set (Cutoff.CutoffSample d) :=
  {omega | shellThreshold M C0 ep L <
    largeScaleShellTerm M n (n + (L : ℤ)) (rescaledLatticePoint n z) omega}

theorem not_mem_shellExcessEvent_iff (M : ABKModel d) (C0 ep : ℝ) (n : ℤ) (L : ℕ)
    (z : Percolation.Site d) (omega : Cutoff.CutoffSample d) :
    omega ∉ shellExcessEvent M C0 ep n L z ↔
      largeScaleShellTerm M n (n + (L : ℤ)) (rescaledLatticePoint n z) omega ≤
        shellThreshold M C0 ep L := by
  simp only [shellExcessEvent, Set.mem_ofPred_eq, not_lt]

/-- **The site-indexed bad events of the scale decomposition.**  At level `0`
the good cube event at the rescaled site fails, or the shell of index `n`
already exceeds its threshold; at level `L + 1` the shell of index `n + L + 1`
exceeds its threshold. -/
def siteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ) :
    ℕ → Percolation.Site d → Set (Cutoff.CutoffSample d)
  | 0 => fun z => (goodCubeEvent M Creg n (rescaledLatticePoint n z) ep)ᶜ ∪
      shellExcessEvent M C0 ep n 0 z
  | (L + 1) => fun z => shellExcessEvent M C0 ep n (L + 1) z

theorem siteBadEventFive_zero (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ)
    (z : Percolation.Site d) :
    siteBadEventFive M Creg C0 ep n 0 z =
      (goodCubeEvent M Creg n (rescaledLatticePoint n z) ep)ᶜ ∪
        shellExcessEvent M C0 ep n 0 z :=
  rfl

theorem siteBadEventFive_succ (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ) (L : ℕ)
    (z : Percolation.Site d) :
    siteBadEventFive M Creg C0 ep n (L + 1) z = shellExcessEvent M C0 ep n (L + 1) z :=
  rfl

theorem shellExcessEvent_subset_siteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ)
    (n : ℤ) (L : ℕ) (z : Percolation.Site d) :
    shellExcessEvent M C0 ep n L z ⊆ siteBadEventFive M Creg C0 ep n L z := by
  cases L with
  | zero => exact Set.subset_union_right
  | succ L => exact subset_rfl

/-! ## 5. The scale decomposition of the event `Q` -/

/-- **The threshold sum.**  If every shell stays below its threshold then the
whole large-scale sum on the cube stays below `C_0 (1 - 3^{-1/8})^{-1} ε
γ^{-1/2}`. -/
theorem mem_largeScaleEvent_of_forall_le (M : ABKModel d) {C0 ep : ℝ} (n : ℤ)
    (y : Vec d) (hC0 : 0 ≤ C0) (hep : 0 ≤ ep) {omega : Cutoff.CutoffSample d}
    (h : ∀ L : ℕ, largeScaleShellTerm M n (n + (L : ℤ)) y omega ≤
      shellThreshold M C0 ep L) :
    omega ∈ largeScaleEvent M n y
      (C0 * ep * (Real.sqrt M.gamma)⁻¹ * (1 - shellDecayBase)⁻¹) := by
  rw [mem_largeScaleEvent_iff_tsum]
  calc (∑' L : ℕ, ENNReal.ofReal (largeScaleShellTerm M n (n + (L : ℤ)) y omega))
      ≤ ∑' L : ℕ, ENNReal.ofReal (shellThreshold M C0 ep L) :=
        ENNReal.tsum_le_tsum fun L => ENNReal.ofReal_le_ofReal (h L)
    _ = ENNReal.ofReal (∑' L : ℕ, shellThreshold M C0 ep L) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun L => shellThreshold_nonneg M hC0 hep L)
          (summable_shellThreshold M C0 ep)).symm
    _ = ENNReal.ofReal
          (C0 * ep * (Real.sqrt M.gamma)⁻¹ * (1 - shellDecayBase)⁻¹) := by
        rw [tsum_shellThreshold]

/-- **The scale decomposition of the event `Q`**: if the constant `C_0` is small
enough that the geometric sum of the thresholds is at most the threshold
`Cinj⁻¹ ε γ^{-1/2}` of the large-scale event, then the complement of
`Q(3^{n-1} z + □_n, ε)` is covered by the site-indexed bad events. -/
theorem compl_qEvent_subset_iUnion_siteBadEventFive (M : ABKModel d)
    {Creg Cinj C0 ep : ℝ} (n : ℤ) (z : Percolation.Site d)
    (hC0 : 0 ≤ C0) (hep : 0 ≤ ep)
    (hthr : C0 * (1 - shellDecayBase)⁻¹ ≤ Cinj⁻¹) :
    (qEvent M Creg Cinj n (rescaledLatticePoint n z) ep)ᶜ ⊆
      ⋃ L : ℕ, siteBadEventFive M Creg C0 ep n L z := by
  intro omega homega
  by_contra hcon
  refine homega ?_
  have hnot : ∀ L : ℕ, omega ∉ siteBadEventFive M Creg C0 ep n L z := by
    intro L hL
    exact hcon (Set.mem_iUnion.2 ⟨L, hL⟩)
  have hzero := hnot 0
  rw [siteBadEventFive_zero, Set.mem_union, not_or] at hzero
  have hgood : omega ∈ goodCubeEvent M Creg n (rescaledLatticePoint n z) ep :=
    not_not.1 hzero.1
  have hshell : ∀ L : ℕ,
      largeScaleShellTerm M n (n + (L : ℤ)) (rescaledLatticePoint n z) omega ≤
        shellThreshold M C0 ep L := by
    intro L
    rw [← not_mem_shellExcessEvent_iff]
    intro hmem
    exact hnot L (shellExcessEvent_subset_siteBadEventFive M Creg C0 ep n L z hmem)
  have hlarge := mem_largeScaleEvent_of_forall_le M n (rescaledLatticePoint n z)
    hC0 hep hshell
  refine ⟨hgood, ?_⟩
  have hmono : C0 * ep * (Real.sqrt M.gamma)⁻¹ * (1 - shellDecayBase)⁻¹ ≤
      Cinj⁻¹ * ep * (Real.sqrt M.gamma)⁻¹ := by
    have hnn : (0 : ℝ) ≤ ep * (Real.sqrt M.gamma)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_right hthr hnn
    calc C0 * ep * (Real.sqrt M.gamma)⁻¹ * (1 - shellDecayBase)⁻¹
        = C0 * (1 - shellDecayBase)⁻¹ * (ep * (Real.sqrt M.gamma)⁻¹) := by ring
      _ ≤ Cinj⁻¹ * (ep * (Real.sqrt M.gamma)⁻¹) := this
      _ = Cinj⁻¹ * ep * (Real.sqrt M.gamma)⁻¹ := by ring
  rw [mem_largeScaleEvent_iff_tsum] at hlarge ⊢
  exact hlarge.trans (ENNReal.ofReal_le_ofReal hmono)

/-! ## 6. Measurability of the site-indexed bad events -/

/-- **The good cube event is measurable in the sample**, with no hypothesis
beyond the model: it is the intersection of two sublevel sets of the localized
quantities, which are measurable in the sample. -/
theorem measurableSet_goodCubeEvent (M : ABKModel d) (Creg : ℝ) (n : ℤ) (y : Vec d)
    (ep : ℝ) : MeasurableSet (goodCubeEvent M Creg n y ep) :=
  (measurableSet_le (measurable_localizedError M n y) measurable_const).inter
    (measurableSet_le (measurable_localizedRegularity M n y) measurable_const)

theorem measurable_largeScaleShellTerm (M : ABKModel d) (n k : ℤ) (y : Vec d) :
    Measurable (largeScaleShellTerm M n k y) :=
  Measurable.const_mul
    (((Section4.Support.measurable_shellW1InfGradNorm n).comp
        (ShellField.measurable_translate y)).comp
      ((measurable_pi_apply k).comp measurable_subtype_coe)) _

/-- **The shell term of the cube `y + □_n` reads only the shell `k` on the
closed cube.** -/
theorem measurable_largeScaleShellTerm_shellLocal (M : ABKModel d) (n k : ℤ) (y : Vec d)
    {U : Set (Vec d)} (hU : closedCubeAt y n ⊆ U) :
    Measurable[Provider.BadEvents.shellCoordinateLocalSigma k U]
      (largeScaleShellTerm M n k y) := by
  have hball : Metric.closedBall y ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ⊆ U := by
    rw [← closedCubeAt_eq_closedBall]
    exact hU
  have hcoord : @Measurable (Cutoff.CutoffSample d) (ShellField d)
      (Provider.BadEvents.shellCoordinateLocalSigma k U)
      (ShellField.lihLocalSigma U) (fun omega => omega.1 k) :=
    Measurable.of_comap_le le_rfl
  have hfirst := Provider.BadEvents.measurable_localCubeDerivNorm_translate_lihLocalSigma
    (U := U) n y hball
  have hsecond :=
    Provider.BadEvents.measurable_localCubeSecondDerivNorm_translate_lihLocalSigma
      (U := U) n y hball
  have hrw : largeScaleShellTerm M n k y = fun omega : Cutoff.CutoffSample d =>
      Real.rpow 3 ((2 - M.gamma) * (n : ℝ)) *
        max (Provider.Stream.localCubeSecondDerivNorm n
              (ShellField.translate y (omega.1 k)))
          ((3 : ℝ) ^ (-n) *
            Provider.Stream.localCubeDerivNorm n
              (ShellField.translate y (omega.1 k))) := rfl
  rw [hrw]
  exact Measurable.const_mul
    ((hsecond.comp hcoord).max ((hfirst.comp hcoord).const_mul _)) _

theorem measurableSet_shellExcessEvent (M : ABKModel d) (C0 ep : ℝ) (n : ℤ) (L : ℕ)
    (z : Percolation.Site d) : MeasurableSet (shellExcessEvent M C0 ep n L z) :=
  measurableSet_lt measurable_const
    (measurable_largeScaleShellTerm M n (n + (L : ℤ)) (rescaledLatticePoint n z))

/-- **The scale-`L` shell event is an event of the shell `n + L` on the closed
cube of its own site.** -/
theorem measurableSet_shellExcessEvent_shellLocal (M : ABKModel d) (C0 ep : ℝ) (n : ℤ)
    (L : ℕ) (z : Percolation.Site d) {U : Set (Vec d)}
    (hU : closedCubeAt (rescaledLatticePoint n z) n ⊆ U) :
    MeasurableSet[Provider.BadEvents.shellCoordinateLocalSigma (n + (L : ℤ)) U]
      (shellExcessEvent M C0 ep n L z) := by
  let : MeasurableSpace (Cutoff.CutoffSample d) :=
    Provider.BadEvents.shellCoordinateLocalSigma (n + (L : ℤ)) U
  exact measurableSet_lt measurable_const
    (measurable_largeScaleShellTerm_shellLocal M n (n + (L : ℤ))
      (rescaledLatticePoint n z) hU)

theorem measurableSet_shellExcessEvent_local (M : ABKModel d) (C0 ep : ℝ) (n : ℤ)
    (L : ℕ) (z : Percolation.Site d) {U : Set (Vec d)}
    (hU : closedCubeAt (rescaledLatticePoint n z) n ⊆ U) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma M (n + (L : ℤ)) U]
      (shellExcessEvent M C0 ep n L z) := by
  have h2 : Provider.BadEvents.shellCoordinateLocalSigma (n + (L : ℤ)) U ≤
      Provider.Percolation.cutoffShellLocalSigma (n + (L : ℤ)) U :=
    Provider.Percolation.shellCoordinateLocalSigma_le_cutoffShellLocalSigma le_rfl U
  have h3 : Provider.Percolation.cutoffShellLocalSigma (n + (L : ℤ)) U ≤
      Cutoff.cutoffSampleLocalSigma M (n + (L : ℤ)) U :=
    MeasurableSpace.comap_mono
      (Cutoff.lowerShellLocalSigma_le_completion M (n + (L : ℤ)) U)
  exact h3 _ (h2 _ (measurableSet_shellExcessEvent_shellLocal M C0 ep n L z hU))

/-- **Every site-indexed bad event is local**: the level-`L` event of the site
`z` is an event of the shells of index at most `n + L` on any region containing
the closed cube `3^{n-1} z + □_n`. -/
theorem measurableSet_siteBadEventFive_local (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ)
    (L : ℕ) (z : Percolation.Site d) {U : Set (Vec d)}
    (hU : closedCubeAt (rescaledLatticePoint n z) n ⊆ U) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma M (n + (L : ℤ)) U]
      (siteBadEventFive M Creg C0 ep n L z) := by
  let : MeasurableSpace (Cutoff.CutoffSample d) :=
    Cutoff.cutoffSampleLocalSigma M (n + (L : ℤ)) U
  cases L with
  | zero =>
      refine MeasurableSet.union ?_ (measurableSet_shellExcessEvent_local M C0 ep n 0 z hU)
      exact MeasurableSet.compl
        (measurableSet_goodCubeEvent_local_of_subset M Creg n (n + ((0 : ℕ) : ℤ))
          (rescaledLatticePoint n z) ep (by omega) hU)
  | succ L => exact measurableSet_shellExcessEvent_local M C0 ep n (L + 1) z hU

theorem measurableSet_siteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ)
    (L : ℕ) (z : Percolation.Site d) :
    MeasurableSet (siteBadEventFive M Creg C0 ep n L z) := by
  cases L with
  | zero =>
      exact ((measurableSet_goodCubeEvent M Creg n (rescaledLatticePoint n z) ep).compl).union
        (measurableSet_shellExcessEvent M C0 ep n 0 z)
  | succ L => exact measurableSet_shellExcessEvent M C0 ep n (L + 1) z

end

end Algsuperdiff.Section5.Support
