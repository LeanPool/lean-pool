/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5SampDefMeasurable

/-!
# Step5SampDef

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hsampDef`, and `Closure.ClosureStep5Input`

`Closure.Step5Input.closureStep5Input_of_sampDef` reduces
`Closure.ClosureStep5Input` to the single binder `hsampDef`: the sample
integrability of `Closure.JunctionDischargeStepFiveDisplay.step5CrossDefect` at
the closure's own Dirichlet family.  This module discharges that binder **inside
the regime in which it is read** and produces `Closure.ClosureStep5Input`.

## The two halves of `hsampDef`

* **Measurability** is `Closure.Step5SampDefMeasurable`: the cube average of the
  product `e . ((k_{n+h} - k_n) grad w_D)` is a Caratheodory function of the
  corrector's `L^2` class, hence measurable in the sample.
* **Domination** is the manuscript's own per-cube step:
  `Closure.Step5DefectGauge.step5CrossDefect_le_meshOscillationCell` is one
  sided, and the defect is *linear* in the direction, so reading it at `-e`
  (whose norm is the same, and whose right-hand side is unchanged) gives the
  two-sided bound
  ```
    |defect_R| <= Cdef * ( osc_R * ( 3^nmesh * G_h(z_R) ) ) .
  ```
  Both factors are `L^4` in the sample on the closure's grid --- the oscillation
  cell by `Closure.Step5InputOscillation.exists_gamma0_step5OscillationLegs`, the
  re-sited gauge by `Closure.Step5Basket.memLp_four_step5Gauge` --- so their
  product is integrable by Cauchy--Schwarz and the defect is integrable by
  domination.

## Why the regime is entered first

`closureStep5Input_of_sampDef` carries `hsampDef` for *all* parameters, whereas
the two `L^4` legs above exist only where the manuscript proves them: at a unit
direction, at a positive shell width, and on a mesh grid of scale at most `n`
(the per-cube step needs `R.scale <= n`).  This module therefore reproduces the
assembly of `closureStep5Input_of_sampDef` --- the same nine discharged legs,
the same produced constants = max (max (step5GateConst d) closureRegimeConst)
((3/2) gamma0^{-1})` and `Fend = step5ShellMomentConst d * --- and supplies
`hsampDef` at the point where the grid, the direction and the shell width are
the closure's own.  No hypothesis of the assembly is changed, weakened or
added.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 5; `e.nablaw.oscillations`;
  `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The defect is odd in the direction -/

theorem vecNormSq_neg (e : Vec d) : vecNormSq (-e) = vecNormSq e := by
  change (∑ i, (-e) i * (-e) i) = ∑ i, e i * e i
  exact Finset.sum_congr rfl fun i _ => by simp

theorem vecNorm_neg (e : Vec d) : vecNorm (-e) = vecNorm e := by
  rw [vecNorm_eq_sqrt_vecNormSq, vecNorm_eq_sqrt_vecNormSq, vecNormSq_neg]

theorem cubeAverage_neg (R : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage R (fun x => -f x) = -cubeAverage R f := by
  change (cubeVolume R)⁻¹ * ∫ x in cubeSet R, -f x ∂volume
      = -((cubeVolume R)⁻¹ * ∫ x in cubeSet R, f x ∂volume)
  rw [integral_neg]
  ring

/-- The per-cube cross defect is linear in the direction; in particular reading
it at `-e` flips its sign. -/
theorem step5CrossDefect_neg_direction (R : TriadicCube d) (omega : ShellSeq d) (n m : ℤ)
    (e : Vec d) (u : Vec d → Vec d) :
    step5CrossDefect R omega n m (-e) u = -step5CrossDefect R omega n m e u := by
  have hfun : (fun x => vecDot (-e) (matVecMul (finiteShellIncrement omega n m x) (u x)))
      = fun x => -vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x)) :=
    funext fun x => vecDot_neg_left _ _
  have h1 : cubeAverage R
      (fun x => vecDot (-e) (matVecMul (finiteShellIncrement omega n m x) (u x)))
      = -cubeAverage R
        (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x))) := by
    rw [hfun, cubeAverage_neg]
  simp only [step5CrossDefect]
  rw [h1, vecDot_neg_left]
  ring

/-! ## The two-sided per-cube step -/

/-- **The two-sided form of the per-cube step.**  The proved bound is one sided;
the defect is odd in the direction and its bound does not see the direction, so
reading the proved bound at `-e` closes the other side. -/
theorem abs_step5CrossDefect_le_meshOscillationCell (R : TriadicCube d) (omega : ShellSeq d)
    (n m : ℤ) (hsc : R.scale ≤ n) {e : Vec d} (he : vecNorm e ≤ 1) (u : Vec d → Vec d)
    (hu : MemLp u 2 (normalizedCubeMeasure R)) :
    |step5CrossDefect R omega n m e u| ≤
      step5CrossDefectConst d *
        (meshOscillationCell R.scale u R *
          ((3 : ℝ) ^ ((R.scale : ℤ) : ℝ) *
            shellDerivNormSum n m (triadicCubeShift R) omega)) := by
  have hup := step5CrossDefect_le_meshOscillationCell R omega n m hsc he u hu
  have hne : vecNorm (-e) ≤ 1 := by rwa [vecNorm_neg]
  have hlo := step5CrossDefect_le_meshOscillationCell R omega n m hsc hne u hu
  rw [step5CrossDefect_neg_direction] at hlo
  exact abs_le.2 ⟨by linarith, hup⟩

/-- The two-sided per-cube step on the closure's own mesh grid. -/
theorem abs_step5CrossDefect_le_step5Gauge {K : ℤ} {j : ℕ} {nmesh n m : ℤ}
    (hmesh : K - (j : ℤ) = nmesh) (hsc : nmesh ≤ n) {e : Vec d} (he : vecNorm e ≤ 1)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d K) j)
    (omega : ShellSeq d) (u : Vec d → Vec d)
    (hu : MemLp u 2 (normalizedCubeMeasure R)) :
    |step5CrossDefect R omega n m e u| ≤
      step5CrossDefectConst d *
        (meshOscillationCell nmesh u R *
          ((3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
            shellDerivNormSum n m (triadicCubeShift R) omega)) := by
  have hRscale : R.scale = nmesh := by
    rw [scale_of_mem_descendantsAtDepth_originCube hR, hmesh]
  have hbase := abs_step5CrossDefect_le_meshOscillationCell R omega n m
    (by rw [hRscale]; exact hsc) he u hu
  rwa [hRscale] at hbase

/-! ## Domination by a product of two `L^4` factors -/

/-- A random variable dominated by a constant multiple of a product of two
nonnegative `L^4` factors is integrable: the product is `L^1` by
Cauchy--Schwarz. -/
theorem integrable_of_abs_le_const_mul_memLp_four {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] {f a b : Omega → ℝ} (c : ℝ)
    (hf : AEStronglyMeasurable f mu) (ha : MemLp a 4 mu) (hb : MemLp b 4 mu)
    (hbound : ∀ omega, |f omega| ≤ c * (a omega * b omega)) :
    Integrable f mu := by
  have ha2 : MemLp a 2 mu := ha.mono_exponent (by norm_num)
  have hb2 : MemLp b 2 mu := hb.mono_exponent (by norm_num)
  have hab : Integrable (fun omega => a omega * b omega) mu := ha2.integrable_mul hb2
  refine (hab.const_mul c).mono' hf ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs]
  exact hbound omega

/-! ## `Closure.ClosureStep5Input` -/

/-- **`Closure.ClosureStep5Input`, produced.**

Every leg of the Step-5 endpoint at the closure's own corrector families is
proved: the nine legs of `Closure.Step5Input.closureStep5Input_of_sampDef` and,
here, the tenth, `hsampDef`.  The produced constants are the same as that
theorem's,
`C5 = max (max (step5GateConst d) closureRegimeConst) ((3/2) gamma0^{-1})` and
`Fend = step5ShellMomentConst d * C2`.

Proved from the ingredients listed in the module docstring. -/
theorem closureStep5Input (d : ℕ) [NeZero d] : ClosureStep5Input d := by
  classical
  intro hd
  obtain ⟨C2, hC2pos, hgrad⟩ := exists_step5GradMomentConst d hd
  obtain ⟨gamma0, hg0pos, hg0quarter, hosc⟩ := exists_gamma0_step5OscillationLegs d hd
  refine ⟨max (max (step5GateConst d) closureRegimeConst) ((3 / 2) * gamma0⁻¹),
    step5ShellMomentConst d * C2, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (step5GateConst_pos d)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact mul_nonneg (step5ShellMomentConst_nonneg d) hC2pos.le
  intro M n h Ec e he hreg
  obtain ⟨hstate, hpos, hCE, hgammaE, hhcap, hcap⟩ := hreg
  set C5 : ℝ := max (max (step5GateConst d) closureRegimeConst) ((3 / 2) * gamma0⁻¹)
    with hC5
  have hgate5 : step5GateConst d ≤ C5 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hg0le : (3 / 2) * gamma0⁻¹ ≤ C5 := le_max_right _ _
  have hC5pos : 0 < C5 := lt_of_lt_of_le (step5GateConst_pos d) hgate5
  -- the Step-5 defect gate, from the regime's own antecedents
  have hgate : step5CrossDefectConst d * M.gamma ^ (15 : ℕ) ≤ 2 :=
    step5CrossDefectConst_mul_gamma_pow_fifteen_le_two_of_regime M hgate5 hCE hgammaE
  -- the smallness `cgamma <= gamma0`, from the same antecedents
  have hMg : M.gamma ≤ gamma0 := by
    have hEbig := two_thirds_mul_le_of_regime M hC5pos.le hCE
    have hgi := gamma_le_inv_of_regime M hgammaE
    have hE1 : (1 : ℝ) ≤ (Ec : ℝ) := Ec.2
    have hE0 : (0 : ℝ) < (Ec : ℝ) := lt_of_lt_of_le zero_lt_one hE1
    have hg0inv : gamma0⁻¹ ≤ (Ec : ℝ) := by
      have h1 : (2 / 3 : ℝ) * ((3 / 2) * gamma0⁻¹) ≤ (2 / 3 : ℝ) * C5 :=
        mul_le_mul_of_nonneg_left hg0le (by norm_num)
      have h2 : (2 / 3 : ℝ) * ((3 / 2) * gamma0⁻¹) = gamma0⁻¹ := by ring
      linarith [hEbig]
    have hinvle : ((Ec : ℝ))⁻¹ ≤ gamma0 := by
      rw [inv_le_comm₀ hE0 hg0pos]
      exact hg0inv
    exact le_trans hgi hinvle
  -- the direction
  have hnorm : vecNorm e ≤ 1 := le_of_eq (vecNorm_eq_one_of_vecNormSq_eq_one he)
  have hlt : n < n + (h : ℤ) := by
    have hp : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hpos
    omega
  set nmesh : ℤ := recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ)
    with hnmeshdef
  have hsc : nmesh ≤ n := recurrenceMesoScale_closure_le M n h
  have hgamma0M : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  -- the three largeness conditions on the localization scale
  have hbigK : ∀ᶠ K : ℕ in Filter.atTop,
      (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ ((K : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop
      (⌈(10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ + ((n + (h : ℤ) : ℤ) : ℝ)⌉₊)] with K hK
    have hcast : ((⌈(10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ + ((n + (h : ℤ) : ℤ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ (K : ℝ) := by exact_mod_cast hK
    have hle := Nat.le_ceil ((10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ + ((n + (h : ℤ) : ℤ) : ℝ))
    have hKcast : (((K : ℕ) : ℤ) : ℝ) = (K : ℝ) := by push_cast; ring
    rw [hKcast]
    linarith
  have hKge : ∀ᶠ K : ℕ in Filter.atTop, n + (h : ℤ) ≤ (K : ℤ) := by
    filter_upwards [Filter.eventually_ge_atTop (n + (h : ℤ)).toNat] with K hK
    have := Int.self_le_toNat (n + (h : ℤ))
    have hKcast : ((n + (h : ℤ)).toNat : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
    omega
  filter_upwards [eventually_closureMeshDepth_scale M n h, hbigK, hKge]
    with K hscale hK10 hKn
  set j : ℕ := closureMeshDepth M n h K with hjdef
  have hmesh : (K : ℤ) - (j : ℤ) = nmesh := by
    have hQ : ((originCube d (K : ℤ)).scale : ℤ) = (K : ℤ) := by simp [originCube]
    rw [← hQ]
    exact hscale
  have hj : (j : ℤ) = (K : ℤ) - nmesh := by omega
  -- the two `L^8`-based spatial legs at the closure's Dirichlet family
  set sinv : ℝ := ((Annealed.sigmaBar M n : ℝ))⁻¹ with hsinv
  set wD : ShellSeq d → H10Function (openCubeSet (originCube d (K : ℤ))) := fun omega =>
    alongIncrementPath n h (closureDirichletFamily sinv e K) omega with hwD
  have hsol : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (wD omega)
        (fun x => -streamForcing sinv omega n (n + (h : ℤ)) e x) := fun omega =>
    isZeroTraceDirichletRhsWeakSolution_alongIncrementPath sinv e K n h omega
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (K : ℤ))) := fun omega =>
    memLp_eight_grad_freshShellDirichlet hd (originCube d (K : ℤ)) sinv omega n
      (n + (h : ℤ)) e (wD omega) (hsol omega)
  -- the oscillation pair
  obtain ⟨hmemOsc, hoscBound⟩ := hosc M hMg (n + (h : ℤ) - 1) Ec hstate n h K j nmesh
    hpos (by omega) hhcap hK10 hnmeshdef hj e hnorm
  -- the gradient pair
  obtain ⟨hvmem, hgradM⟩ := hgrad M n h K j e hnorm hpos hKn
  -- `hsampDef`: measurability from the Caratheodory pairing, domination from the
  -- two-sided per-cube step and the two `L^4` legs
  have hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
        (fun omega : CutoffSample d =>
          step5CrossDefect R omega.val n (n + (h : ℤ)) e
            (fun x => (wD omega.val).toH1Function.grad x))
        (cutoffSampleLaw M).toMeasure := by
    intro R hR
    refine integrable_of_abs_le_const_mul_memLp_four (cutoffSampleLaw M).toMeasure
      (step5CrossDefectConst d)
      (measurable_cutoffSample_step5CrossDefect_freshShellDirichletGrad hR e n
        (n + (h : ℤ)) sinv n (n + (h : ℤ)) e wD hsol).aestronglyMeasurable
      (hmemOsc R hR) (memLp_four_step5Gauge M hlt nmesh R) ?_
    intro omega
    exact abs_step5CrossDefect_le_step5Gauge hmesh hsc hnorm hR omega.val _
      (memLp_two_grad_normalizedCubeMeasure_descendant hR (wD omega.val).toH1Function)
  exact step5GaugeEndpoint_closureFamilies_of_momentLegs M n h K j he hmesh hsc hpos hgate
    (fun omega => integrableOn_cubeSet_vecDot_matVecMul_finiteShellIncrement
      (originCube d (K : ℤ)) omega n (n + (h : ℤ)) e (hL8 omega))
    (fun R hR => aestronglyMeasurable_step5PairingX M n h K e hR)
    (fun R hR => aestronglyMeasurable_step5PairingS M n h K e hR)
    hsampDef
    (fun R hR => memLp_four_matrixOperatorNorm_freshShellCubeAverage M hR
      (by rw [scale_of_mem_descendantsAtDepth_originCube hR, hmesh]; exact hsc) hlt)
    hvmem hmemOsc hoscBound (step5ShellMomentConst_nonneg d)
    (gridFourthMoment_matrixOperatorNorm_freshShellCubeAverage_root_le M n h K j hmesh
      hsc hpos)
    hgradM

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
