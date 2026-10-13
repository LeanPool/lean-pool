/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.JunctionDischargeStepFive
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ShellProductControl
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationEndpoint

/-!
# JunctionDischargeStepFiveDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-5 gauge junction: the averaged display and the endpoint

ABK26, `l.approximate.recurrence.formula`, Step 5, together with
`e.what.nablaw.really.is` and `e.lower.bound.oscillations`.

`Closure.JunctionDischargeStepFive` reduces `Closure.Step5GaugeEndpoint` to one
binder, `hdisplay`:

```
  avsum_R E[ step5CellExcess ]
    <= - E|| grad w_D^{(K)} ||^2_{L2(cu_K)}
       + Fend h^2 shom_n^{-4} 3^{4 cgamma (n+h)} + cgamma^15 .
```

This module proves that display, and then the endpoint.

## The three pieces of the display

* **`e.what.nablaw.really.is`**, proved here as
  `cubeAverage_vecNormSq_grad_eq_shellPairing`: the Dirichlet weak formulation
  of `e.def.w` tested with *its own solution* --- legitimate because
  `IsZeroTraceDirichletRhsWeakSolution` tests against all of `H10Function U`
  and the solution is one --- gives, with the identity coefficient field and
  the forcing `g = -streamForcing shom_n^{-1} omega n (n+h) e`,

  ```
    fint_{cu_K} |grad w_D|^2 = shom_n^{-1} fint_{cu_K} e . (h grad w_D) ,
  ```

  the sign being fixed by the pointwise skew-symmetry of the fresh shell
  (`Cutoff.finiteShellIncrement_skew`), through `vecDot_matVecMul_skew`.  This is
  the manuscript's own second equality in `e.what.nablaw.really.is`.

* **product of averages vs average of product.**  `step5CrossDefect` names the
  per-cube cost of replacing `(h)_R (grad w_D)_R` by `(h grad w_D)_R`, and
  `descendantsAverage_shellPairing_eq` is the exact tiling identity that carries
  it to the grid.  The defect is charged to the two factors of
  `e.lower.bound.oscillations` by the binder `hdefect`, and the *sum* form of
  that endpoint is turned into the *product* the cross term produces by the
  Cauchy--Schwarz chain proved here:
  `integral_rpow_two_le_rpow_integral_rpow_four` (Lyapunov in the sample),
  `integral_mul_le_rpowFourRoot_mul_rpowFourRoot` (Cauchy--Schwarz in the
  sample, in the fourth-moment spelling),
  `cubeFamilyAverage_rpowFourRoot_mul_le` (Hoelder for the fourth roots on the
  grid) and `cubeFamilyAverage_integral_mul_le_gridFourthMomentRoot_mul_root`
  (the two combined, delivering exactly `gridFourthMomentRoot` against the
  gauge's own fourth-moment root).  The final fold is `crossOscillationFold`, in the form
  ```
    2 sinv DD <= Cdef (2 A B) <= Cdef (A+B)^2/2
              <= (Cdef cgamma^15 / 2) cgamma^15 <= cgamma^15 ,
  ```
  the last step being the gate `hgate`.

* **the quadratic error**: `Closure.shellProduct_le_quadratic_error`
  instantiated at `prod = avsum_ |(h)_R (grad w_D)_R|^2`, `Fend = * C2`.

## Carrier transports the caller must supply on `hosc`

The proved Lean endpoint
`exists_gamma0_freshShellDirichlet_meshOscillation_le_gamma_pow_sixteen`
(`LocalizationOscillationEndpointSixteen.lean`) proves
`e.lower.bound.oscillations`

* on the **interior** meso grid `interiorMesoCubeGrid`, whereas the
  manuscript's display --- and `Closure.Step5GaugeEndpoint`, whose carrier is
  `descendantsAtDepth (originCube d K) j` --- averages over the **full** mesh.
  This is the known manuscript gap; closing it needs either the interior
  average or a boundary-strip argument; `hosc` is stated at the full mesh, i.e.
  faithfully to the source, and the transport from the interior endpoint is the
  remaining chain;
* against the shell-sequence law `M.P.toMeasure`, whereas the closure's carrier
  is the cutoff sample law `(cutoffSampleLaw M).toMeasure`.  The two are related
  by `Cutoff.map_cutoffSampleLaw_val`; the change of variables is the second
  remaining chain.

Neither transport is performed here, and neither is assumed away: both live
inside the single binder `hosc`, which is the manuscript's own display.

## References

* ABK26, `e.lower.bound.pre2`; the Step-5 estimate;
  `e.what.nablaw.really.is`; `e.nablaw.oscillations`;
  `e.lower.bound.oscillations`; `e.km.kn.Lp`; `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `e.what.nablaw.really.is` -/

/-- Skew-symmetry moves a matrix across the dot product with a sign change. -/
theorem vecDot_matVecMul_skew (A : Mat d) (hA : A.transpose = -A) (u v : Vec d) :
    vecDot (matVecMul A u) v = -vecDot u (matVecMul A v) := by
  classical
  have hentry : ∀ i j : Fin d, A j i = -A i j := by
    intro i j
    have hij := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply, Matrix.neg_apply] using hij
  change (∑ i, (∑ j, A i j * u j) * v i) = -∑ j, u j * ∑ i, A j i * v i
  rw [show (∑ j, u j * ∑ i, A j i * v i) = ∑ j, ∑ i, u j * (A j i * v i) from
      Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _,
    Finset.sum_comm]
  rw [show (∑ i, (∑ j, A i j * u j) * v i) = ∑ i, ∑ j, A i j * u j * v i from
      Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hentry i j]
  ring

private theorem matVecMul_one_vec (v : Vec d) :
    matVecMul (1 : Matrix (Fin d) (Fin d) ℝ) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

/-- **`e.what.nablaw.really.is`, Dirichlet leg**. -/
theorem cubeAverage_vecNormSq_grad_eq_shellPairing (Q : TriadicCube d) (c : ℝ)
    (omega : ShellSeq d) (n m : ℤ) (e : Vec d) (w : H10Function (openCubeSet Q))
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -streamForcing c omega n m e x)) :
    cubeAverage Q (fun x => vecNormSq (w.toH1Function.grad x)) =
      c * cubeAverage Q (fun x => vecDot e
        (matVecMul (finiteShellIncrement omega n m x) (w.toH1Function.grad x))) := by
  have hself := hw w
  have hLfun : (fun x : Vec d =>
      vecDot (matVecMul ((fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) x)
        (w.toH1Function.grad x)) (w.toH1Function.grad x))
      = fun x : Vec d => vecNormSq (w.toH1Function.grad x) := by
    funext x
    rw [matVecMul_one_vec]
    rfl
  have hRfun : (fun x : Vec d =>
      vecDot ((fun y : Vec d => -streamForcing c omega n m e y) x) (w.toH1Function.grad x))
      = fun x : Vec d => c * vecDot e
          (matVecMul (finiteShellIncrement omega n m x) (w.toH1Function.grad x)) := by
    funext x
    have hskew := vecDot_matVecMul_skew (finiteShellIncrement omega n m x)
      (finiteShellIncrement_skew omega n m x) e (w.toH1Function.grad x)
    have hlin : vecDot (-streamForcing c omega n m e x) (w.toH1Function.grad x)
        = -c * vecDot (matVecMul (finiteShellIncrement omega n m x) e)
            (w.toH1Function.grad x) := by
      change (∑ i, (-(streamForcing c omega n m e x)) i * (w.toH1Function.grad x) i)
        = -c * ∑ i, matVecMul (finiteShellIncrement omega n m x) e i *
            (w.toH1Function.grad x) i
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change -(c * matVecMul (finiteShellIncrement omega n m x) e i) *
          (w.toH1Function.grad x) i = _
      ring
    change vecDot (-streamForcing c omega n m e x) (w.toH1Function.grad x) = _
    rw [hlin, hskew]
    ring
  rw [hLfun, hRfun, integral_const_mul] at hself
  change (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, vecNormSq (w.toH1Function.grad x) ∂volume
    = c * ((cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, vecDot e
        (matVecMul (finiteShellIncrement omega n m x) (w.toH1Function.grad x)) ∂volume)
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet, hself]
  ring

/-! ## The Cauchy--Schwarz step that feeds the fourth-moment endpoint -/

private theorem holderConjugate_two_two : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

private theorem ofReal_two : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  simp [ENNReal.ofReal_ofNat]

/-- Lyapunov's inequality on a probability space, in the `rpow` spelling. -/
theorem integral_rpow_two_le_rpow_integral_rpow_four {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : ∀ omega, 0 ≤ X omega) (hXm : MemLp X 4 mu) :
    ∫ omega, X omega ^ (2 : ℝ) ∂mu ≤
      (∫ omega, X omega ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) := by
  have hsq : MemLp (fun omega => X omega ^ (2 : ℝ)) 2 mu := by
    have hbase := hXm.norm_rpow_div (2 : ℝ≥0∞)
    have hdiv : (4 : ℝ≥0∞) / (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
        ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
    rw [hdiv] at hbase
    refine hbase.ae_eq ?_
    filter_upwards with omega
    simp [Real.norm_of_nonneg (hX omega)]
  have hsq' : MemLp (fun omega => X omega ^ (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu := by
    rwa [ofReal_two]
  have hone : MemLp (fun _ : Omega => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_const 1
  have hnn : 0 ≤ᵐ[mu] fun omega => X omega ^ (2 : ℝ) :=
    Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hX omega) _
  have hone' : 0 ≤ᵐ[mu] fun _ : Omega => (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ => zero_le_one
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg holderConjugate_two_two hnn hone' hsq' hone
  have hmid : ∀ omega : Omega, (X omega ^ (2 : ℝ)) ^ (2 : ℝ) = X omega ^ (4 : ℝ) := by
    intro omega
    rw [← Real.rpow_mul (hX omega)]
    norm_num
  simp only [mul_one, hmid, Real.one_rpow, integral_const, smul_eq_mul] at hh
  simpa using hh

/-- **Cauchy--Schwarz in the sample, in the fourth-moment spelling.** -/
theorem integral_mul_le_rpowFourRoot_mul_rpowFourRoot {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : ∀ omega, 0 ≤ X omega) (hY : ∀ omega, 0 ≤ Y omega)
    (hXm : MemLp X 4 mu) (hYm : MemLp Y 4 mu) :
    ∫ omega, X omega * Y omega ∂mu ≤
      (∫ omega, X omega ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) *
        (∫ omega, Y omega ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) := by
  have hX2 : MemLp X (ENNReal.ofReal (2 : ℝ)) mu := by
    rw [ofReal_two]
    exact hXm.mono_exponent (by norm_num)
  have hY2 : MemLp Y (ENNReal.ofReal (2 : ℝ)) mu := by
    rw [ofReal_two]
    exact hYm.mono_exponent (by norm_num)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg holderConjugate_two_two
    (Filter.Eventually.of_forall hX) (Filter.Eventually.of_forall hY) hX2 hY2
  have hXl := integral_rpow_two_le_rpow_integral_rpow_four mu hX hXm
  have hYl := integral_rpow_two_le_rpow_integral_rpow_four mu hY hYm
  have hX4nn : (0 : ℝ) ≤ ∫ omega, X omega ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hX omega) _
  have hY4nn : (0 : ℝ) ≤ ∫ omega, Y omega ^ (4 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hY omega) _
  have hX2nn : (0 : ℝ) ≤ ∫ omega, X omega ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hX omega) _
  have hY2nn : (0 : ℝ) ≤ ∫ omega, Y omega ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun omega => Real.rpow_nonneg (hY omega) _
  have hstepX : (∫ omega, X omega ^ (2 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) ≤
      (∫ omega, X omega ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) := by
    have h1 : (∫ omega, X omega ^ (2 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) ≤
        ((∫ omega, X omega ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_le_rpow hX2nn hXl (by norm_num)
    rwa [← Real.rpow_mul hX4nn, show (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ by norm_num] at h1
  have hstepY : (∫ omega, Y omega ^ (2 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) ≤
      (∫ omega, Y omega ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) := by
    have h1 : (∫ omega, Y omega ^ (2 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) ≤
        ((∫ omega, Y omega ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_le_rpow hY2nn hYl (by norm_num)
    rwa [← Real.rpow_mul hY4nn, show (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ by norm_num] at h1
  have hhalf : (1 : ℝ) / (2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [hhalf] at hh
  exact hh.trans (mul_le_mul hstepX hstepY (Real.rpow_nonneg hY2nn _)
    (Real.rpow_nonneg hX4nn _))

/-- Cauchy--Schwarz on a finite cube family. -/
theorem sq_cubeFamilyAverage_le_cubeFamilyAverage_sq (I : Finset (TriadicCube d))
    (F : TriadicCube d → ℝ) :
    (cubeFamilyAverage I F) ^ (2 : ℕ) ≤ cubeFamilyAverage I (fun R => F R ^ (2 : ℕ)) := by
  classical
  rcases Nat.eq_zero_or_pos I.card with hI0 | hIpos
  · have hIempty : I = ∅ := Finset.card_eq_zero.mp hI0
    subst hIempty
    simp [cubeFamilyAverage]
  have hN : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hIpos
  have hcheb := sq_sum_le_card_mul_sum_sq (s := I) (f := F)
  unfold cubeFamilyAverage
  rw [mul_pow]
  have hstep : ((I.card : ℝ))⁻¹ ^ (2 : ℕ) * (∑ R ∈ I, F R) ^ (2 : ℕ) ≤
      ((I.card : ℝ))⁻¹ ^ (2 : ℕ) * ((I.card : ℝ) * ∑ R ∈ I, F R ^ 2) :=
    mul_le_mul_of_nonneg_left hcheb (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-! ## The grid Cauchy--Schwarz for a *per-cube* second factor

The one-sided step above is the shape the display needed while the forcing
gauge of `e.nablaw.oscillations` was read at a **single** window `z0`.  The
gauge is sited at the cube's own base point, so the second factor of the cross
term is itself a grid family, and the grid step must be Hoelder in *both*
factors.  The three lemmas below supply that. -/

/-- Jensen for the concave square root, at the finite cube family. -/
theorem cubeFamilyAverage_sqrt_le (I : Finset (TriadicCube d))
    (G : TriadicCube d → ℝ) (hG : ∀ R ∈ I, 0 ≤ G R) :
    cubeFamilyAverage I (fun R => G R ^ ((2 : ℝ)⁻¹)) ≤
      (cubeFamilyAverage I G) ^ ((2 : ℝ)⁻¹) := by
  classical
  have hAnn : (0 : ℝ) ≤ cubeFamilyAverage I (fun R => G R ^ ((2 : ℝ)⁻¹)) :=
    cubeFamilyAverage_nonneg fun R hR => Real.rpow_nonneg (hG R hR) _
  have h1 := sq_cubeFamilyAverage_le_cubeFamilyAverage_sq I (fun R => G R ^ ((2 : ℝ)⁻¹))
  have hpt : ∀ R ∈ I, (G R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) = G R := by
    intro R hR
    rw [← Real.rpow_natCast (G R ^ ((2 : ℝ)⁻¹)) 2, ← Real.rpow_mul (hG R hR)]
    norm_num
  have hrewrite : cubeFamilyAverage I (fun R => (G R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ))
      = cubeFamilyAverage I G := by
    unfold cubeFamilyAverage
    exact congrArg _ (Finset.sum_congr rfl hpt)
  rw [hrewrite] at h1
  have hroot := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  rwa [← Real.rpow_natCast (cubeFamilyAverage I (fun R => G R ^ ((2 : ℝ)⁻¹))) 2,
    ← Real.rpow_mul hAnn, show (((2 : ℕ) : ℝ) * (2 : ℝ)⁻¹) = 1 by norm_num,
    Real.rpow_one] at hroot

/-- Cauchy--Schwarz for the finite cube-family average. -/
theorem sq_cubeFamilyAverage_mul_le (I : Finset (TriadicCube d))
    (u v : TriadicCube d → ℝ) :
    (cubeFamilyAverage I (fun R => u R * v R)) ^ (2 : ℕ) ≤
      cubeFamilyAverage I (fun R => u R ^ (2 : ℕ)) *
        cubeFamilyAverage I (fun R => v R ^ (2 : ℕ)) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I u v
  have hshape : ∀ F : TriadicCube d → ℝ, cubeFamilyAverage I F
      = ((I.card : ℝ))⁻¹ * ∑ R ∈ I, F R := fun _ => rfl
  simp only [hshape, mul_pow]
  have hnn : (0 : ℝ) ≤ ((I.card : ℝ))⁻¹ ^ (2 : ℕ) := by positivity
  calc ((I.card : ℝ))⁻¹ ^ (2 : ℕ) * (∑ R ∈ I, u R * v R) ^ (2 : ℕ)
      ≤ ((I.card : ℝ))⁻¹ ^ (2 : ℕ) *
          ((∑ R ∈ I, u R ^ 2) * (∑ R ∈ I, v R ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hnn
    _ = ((I.card : ℝ))⁻¹ * (∑ R ∈ I, u R ^ (2 : ℕ)) *
          (((I.card : ℝ))⁻¹ * ∑ R ∈ I, v R ^ (2 : ℕ)) := by ring

/-- Hoelder on the grid at a pair of fourth roots. -/
theorem cubeFamilyAverage_rpowFourRoot_mul_le (I : Finset (TriadicCube d))
    (a b : TriadicCube d → ℝ) (ha : ∀ R ∈ I, 0 ≤ a R) (hb : ∀ R ∈ I, 0 ≤ b R) :
    cubeFamilyAverage I (fun R => a R ^ ((4 : ℝ)⁻¹) * b R ^ ((4 : ℝ)⁻¹)) ≤
      (cubeFamilyAverage I a) ^ ((4 : ℝ)⁻¹) * (cubeFamilyAverage I b) ^ ((4 : ℝ)⁻¹) := by
  classical
  have hAnn : (0 : ℝ) ≤ cubeFamilyAverage I a := cubeFamilyAverage_nonneg ha
  have hBnn : (0 : ℝ) ≤ cubeFamilyAverage I b := cubeFamilyAverage_nonneg hb
  have hLnn : (0 : ℝ) ≤
      cubeFamilyAverage I (fun R => a R ^ ((4 : ℝ)⁻¹) * b R ^ ((4 : ℝ)⁻¹)) :=
    cubeFamilyAverage_nonneg fun R hR =>
      mul_nonneg (Real.rpow_nonneg (ha R hR) _) (Real.rpow_nonneg (hb R hR) _)
  have hMnn : (0 : ℝ) ≤ (cubeFamilyAverage I a) ^ ((4 : ℝ)⁻¹) *
      (cubeFamilyAverage I b) ^ ((4 : ℝ)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg hAnn _) (Real.rpow_nonneg hBnn _)
  have hsq := sq_cubeFamilyAverage_mul_le I (fun R => a R ^ ((4 : ℝ)⁻¹))
    (fun R => b R ^ ((4 : ℝ)⁻¹))
  have hptA : ∀ R ∈ I, (a R ^ ((4 : ℝ)⁻¹)) ^ (2 : ℕ) = a R ^ ((2 : ℝ)⁻¹) := by
    intro R hR
    rw [← Real.rpow_natCast (a R ^ ((4 : ℝ)⁻¹)) 2, ← Real.rpow_mul (ha R hR)]
    norm_num
  have hptB : ∀ R ∈ I, (b R ^ ((4 : ℝ)⁻¹)) ^ (2 : ℕ) = b R ^ ((2 : ℝ)⁻¹) := by
    intro R hR
    rw [← Real.rpow_natCast (b R ^ ((4 : ℝ)⁻¹)) 2, ← Real.rpow_mul (hb R hR)]
    norm_num
  have hA2 : cubeFamilyAverage I (fun R => (a R ^ ((4 : ℝ)⁻¹)) ^ (2 : ℕ))
      = cubeFamilyAverage I (fun R => a R ^ ((2 : ℝ)⁻¹)) := by
    unfold cubeFamilyAverage
    exact congrArg _ (Finset.sum_congr rfl hptA)
  have hB2 : cubeFamilyAverage I (fun R => (b R ^ ((4 : ℝ)⁻¹)) ^ (2 : ℕ))
      = cubeFamilyAverage I (fun R => b R ^ ((2 : ℝ)⁻¹)) := by
    unfold cubeFamilyAverage
    exact congrArg _ (Finset.sum_congr rfl hptB)
  rw [hA2, hB2] at hsq
  have hJA := cubeFamilyAverage_sqrt_le I a ha
  have hJB := cubeFamilyAverage_sqrt_le I b hb
  have hJBnn : (0 : ℝ) ≤ cubeFamilyAverage I (fun R => b R ^ ((2 : ℝ)⁻¹)) :=
    cubeFamilyAverage_nonneg fun R hR => Real.rpow_nonneg (hb R hR) _
  have hstep : cubeFamilyAverage I (fun R => a R ^ ((2 : ℝ)⁻¹)) *
      cubeFamilyAverage I (fun R => b R ^ ((2 : ℝ)⁻¹)) ≤
      (cubeFamilyAverage I a) ^ ((2 : ℝ)⁻¹) * (cubeFamilyAverage I b) ^ ((2 : ℝ)⁻¹) :=
    mul_le_mul hJA hJB hJBnn (Real.rpow_nonneg hAnn _)
  have hMsq : ((cubeFamilyAverage I a) ^ ((4 : ℝ)⁻¹) *
      (cubeFamilyAverage I b) ^ ((4 : ℝ)⁻¹)) ^ (2 : ℕ) =
      (cubeFamilyAverage I a) ^ ((2 : ℝ)⁻¹) * (cubeFamilyAverage I b) ^ ((2 : ℝ)⁻¹) := by
    rw [mul_pow, ← Real.rpow_natCast ((cubeFamilyAverage I a) ^ ((4 : ℝ)⁻¹)) 2,
      ← Real.rpow_mul hAnn, ← Real.rpow_natCast ((cubeFamilyAverage I b) ^ ((4 : ℝ)⁻¹)) 2,
      ← Real.rpow_mul hBnn]
    norm_num
  have hfinal : (cubeFamilyAverage I (fun R => a R ^ ((4 : ℝ)⁻¹) * b R ^ ((4 : ℝ)⁻¹)))
      ^ (2 : ℕ) ≤ ((cubeFamilyAverage I a) ^ ((4 : ℝ)⁻¹) *
        (cubeFamilyAverage I b) ^ ((4 : ℝ)⁻¹)) ^ (2 : ℕ) := by
    rw [hMsq]
    exact hsq.trans hstep
  nlinarith [hfinal, hLnn, hMnn]

/-- **The two-sided grid/sample Cauchy--Schwarz that feeds the re-sited
`e.lower.bound.oscillations`.** -/
theorem cubeFamilyAverage_integral_mul_le_gridFourthMomentRoot_mul_root {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (I : Finset (TriadicCube d)) (X Y : TriadicCube d → Omega → ℝ)
    (hX : ∀ R omega, 0 ≤ X R omega) (hY : ∀ R omega, 0 ≤ Y R omega)
    (hXm : ∀ R ∈ I, MemLp (X R) 4 mu) (hYm : ∀ R ∈ I, MemLp (Y R) 4 mu) :
    cubeFamilyAverage I (fun R => ∫ omega, X R omega * Y R omega ∂mu) ≤
      gridFourthMomentRoot mu I X * gridFourthMomentRoot mu I Y := by
  classical
  have hper : ∀ R ∈ I, (∫ omega, X R omega * Y R omega ∂mu) ≤
      (∫ omega, X R omega ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) *
        (∫ omega, Y R omega ^ (4 : ℝ) ∂mu) ^ ((4 : ℝ)⁻¹) := fun R hR =>
    integral_mul_le_rpowFourRoot_mul_rpowFourRoot mu (hX R) (hY R) (hXm R hR) (hYm R hR)
  refine (cubeFamilyAverage_mono hper).trans ?_
  exact cubeFamilyAverage_rpowFourRoot_mul_le I
    (fun R => ∫ omega, X R omega ^ (4 : ℝ) ∂mu)
    (fun R => ∫ omega, Y R omega ^ (4 : ℝ) ∂mu)
    (fun R _ => integral_nonneg fun omega => Real.rpow_nonneg (hX R omega) _)
    (fun R _ => integral_nonneg fun omega => Real.rpow_nonneg (hY R omega) _)

/-! ## The per-cube cross defect and the grid identity -/

/-- **The Step-5 per-cube cross defect**: the cube average of the product `h grad
w`, tested against `e`, minus the product of the two cube averages.  It is the
entire cost of replacing `(h)_R (grad w)_R` by `(h grad w)_R`. -/
def step5CrossDefect (R : TriadicCube d) (omega : ShellSeq d) (n m : ℤ) (e : Vec d)
    (u : Vec d → Vec d) : ℝ :=
  cubeAverage R (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x)))
    - vecDot e (matVecMul (freshShellCubeAverage R omega n m) (cubeAverageVec R u))

private theorem descendantsAverage_sub_real (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R - G R)
      = descendantsAverage Q j F - descendantsAverage Q j G := by
  classical
  have hshape : ∀ H : TriadicCube d → ℝ, descendantsAverage Q j H
      = ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, H R :=
    fun _ => rfl
  simp only [hshape, Finset.sum_sub_distrib]
  ring

private theorem descendantsAverage_lincomb (Q : TriadicCube d) (j : ℕ) (a b : ℝ)
    (F G H : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R - a * G R + b * H R)
      = descendantsAverage Q j F - a * descendantsAverage Q j G
        + b * descendantsAverage Q j H := by
  classical
  have hshape : ∀ P : TriadicCube d → ℝ, descendantsAverage Q j P
      = ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, P R :=
    fun _ => rfl
  simp only [hshape, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem descendantsAverage_integral_comm' {Omega : Type*} [MeasurableSpace Omega]
    (Q : TriadicCube d) (j : ℕ) (mu : Measure Omega) (F : TriadicCube d → Omega → ℝ)
    (hF : ∀ R ∈ descendantsAtDepth Q j, Integrable (F R) mu) :
    descendantsAverage Q j (fun R => ∫ w, F R w ∂mu)
      = ∫ w, descendantsAverage Q j (fun R => F R w) ∂mu := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q j, ∫ w, F R w ∂mu = _
  rw [show (fun w => descendantsAverage Q j (fun R => F R w))
      = fun w => ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j, F R w from rfl,
    integral_const_mul, integral_finsetSum _ hF]

/-- **The grid form of the cross term**: the descendant average of the products of
the averages is the cube average of the product, minus the grid average of the
defects.  This is the exact tiling bookkeeping. -/
theorem descendantsAverage_shellPairing_eq (Q : TriadicCube d) (j : ℕ)
    (omega : ShellSeq d) (n m : ℤ) (e : Vec d) (u : Vec d → Vec d)
    (hint : IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x)))
      (cubeSet Q) volume) :
    descendantsAverage Q j (fun R => vecDot e
        (matVecMul (freshShellCubeAverage R omega n m) (cubeAverageVec R u)))
      = cubeAverage Q
          (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x)))
        - descendantsAverage Q j (fun R =>
            step5CrossDefect R omega n m e u) := by
  have htile :=
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x))) hint
  have hshape : (fun R : TriadicCube d => vecDot e
        (matVecMul (freshShellCubeAverage R omega n m) (cubeAverageVec R u)))
      = fun R : TriadicCube d =>
          cubeAverage R
            (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x)))
            - step5CrossDefect R omega n m e u := by
    funext R
    rw [step5CrossDefect]
    ring
  rw [hshape, descendantsAverage_sub_real, ← htile]

/-! ## The fourth-root gauge normalization -/

private theorem descendantsAverage_congr_mem (Q : TriadicCube d) (j : ℕ)
    {F G : TriadicCube d → ℝ}
    (hFG : ∀ R ∈ descendantsAtDepth Q j, F R = G R) :
    descendantsAverage Q j F = descendantsAverage Q j G := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F R
    = ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, G R
  rw [Finset.sum_congr rfl hFG]

/-! ## The two arithmetic folds of the display -/

/-- The `2AB <= (A+B)^2/2` fold that turns the *sum* form of
`e.lower.bound.oscillations` into the *product* the cross term produces. -/
private theorem crossOscillationFold {A cB DD sinv gam Cdef : ℝ}
    (hA : 0 ≤ A) (hcB : 0 ≤ cB) (hsinv : 0 ≤ sinv) (hCdef : 0 ≤ Cdef)
    (hDD : DD ≤ Cdef * (A * cB)) (hsum : A + sinv * cB ≤ gam)
    (hgam0 : 0 ≤ gam) (hgate : Cdef * gam ≤ 2) :
    2 * sinv * DD ≤ gam := by
  have hB0 : 0 ≤ sinv * cB := mul_nonneg hsinv hcB
  have hsq : (A + sinv * cB) * (A + sinv * cB) ≤ gam * gam :=
    mul_self_le_mul_self (by linarith) hsum
  have hprodAB : 2 * (A * (sinv * cB)) ≤ gam * gam / 2 := by
    nlinarith [sq_nonneg (A - sinv * cB), hsq]
  have hstep : 2 * sinv * DD ≤ Cdef * (2 * (A * (sinv * cB))) := by
    have hmul : (2 * sinv) * DD ≤ (2 * sinv) * (Cdef * (A * cB)) :=
      mul_le_mul_of_nonneg_left hDD (by linarith)
    nlinarith [hmul]
  have hmid : Cdef * (2 * (A * (sinv * cB))) ≤ Cdef * (gam * gam / 2) :=
    mul_le_mul_of_nonneg_left hprodAB hCdef
  have hlast : Cdef * (gam * gam / 2) ≤ gam := by
    have hg := mul_le_mul_of_nonneg_right hgate hgam0
    nlinarith [hg]
  linarith

/-- The final linear fold of the three legs. -/
private theorem step5Combine {sig NN XX SS EE DD quad gam : ℝ} (hsig : 0 < sig)
    (hNN : NN ≤ EE) (hXX : XX = sig * EE - DD)
    (hosc : 2 * sig⁻¹ * DD ≤ gam) (hquad : sig⁻¹ ^ 2 * SS ≤ quad) :
    NN - 2 * sig⁻¹ * XX + sig⁻¹ ^ 2 * SS ≤ -EE + quad + gam := by
  have hinv : sig⁻¹ * sig = 1 := inv_mul_cancel₀ (ne_of_gt hsig)
  have hexp : NN - 2 * sig⁻¹ * (sig * EE - DD) + sig⁻¹ ^ 2 * SS
      = NN - 2 * (sig⁻¹ * sig) * EE + 2 * sig⁻¹ * DD + sig⁻¹ ^ 2 * SS := by ring
  rw [hXX, hexp, hinv]
  linarith

/-! ## The four legs of the averaged display -/

/-- The per-cube sample integral of the Step-5 excess splits into the three
terms of the manuscript's display. -/
private theorem step5CellExcess_integral_eq (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ)
    (e : Vec d)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (R : TriadicCube d)
    (hN : Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hX : Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hS : Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure) :
    (∫ omega : CutoffSample d,
        step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
          (alongIncrementPath n h wD) omega.val
            ∂(cutoffSampleLaw M).toMeasure)
      = (∫ omega : CutoffSample d,
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            ∂(cutoffSampleLaw M).toMeasure)
        - (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (∫ omega : CutoffSample d,
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
        + ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * (∫ omega : CutoffSample d,
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure) := by
  have hfun : (fun omega : CutoffSample d =>
      step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
        (alongIncrementPath n h wD) omega.val)
      = fun omega : CutoffSample d =>
        (vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            - (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (vecDot e (matVecMul (freshShellCubeAverage
              R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
        + ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * (vecNormSq (matVecMul (freshShellCubeAverage R
          omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))) := rfl
  have hIX : Integrable (fun omega : CutoffSample d =>
      (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (vecDot e (matVecMul (freshShellCubeAverage R
        omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
            (cutoffSampleLaw M).toMeasure := hX.const_mul _
  have hIS : Integrable (fun omega : CutoffSample d =>
      ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * (vecNormSq (matVecMul (freshShellCubeAverage R
        omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
            (cutoffSampleLaw M).toMeasure := hS.const_mul _
  have hIsub : Integrable (fun omega : CutoffSample d =>
      vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            - (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (vecDot e (matVecMul (freshShellCubeAverage
              R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
            (cutoffSampleLaw M).toMeasure := hN.sub hIX
  rw [hfun, integral_add hIsub hIS, integral_sub hN hIX,
    integral_const_mul, integral_const_mul]

/-- **Leg 1** --- the descendant-tiling Jensen step, read for the Dirichlet
corrector. -/
private theorem step5_jensen_leg (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hmemD : ∀ (omega : ShellSeq d) (R : TriadicCube d), R ∈ descendantsAtDepth (originCube d (K :
      ℤ)) j →
      MemLp (fun x => (alongIncrementPath n h wD omega).toH1Function.grad x) 2
        (normalizedCubeMeasure R))
    (hintD : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecNormSq ((alongIncrementPath n h wD omega).toH1Function.grad x))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hsampN : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hsampG : Integrable (fun omega : CutoffSample d =>
      cubeAverage (originCube d (K : ℤ)) (fun x => vecNormSq
        ((alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure) :
    descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            ∂(cutoffSampleLaw M).toMeasure)
      ≤ dirichletCubeEnergy M n h K wD := by
  rw [descendantsAverage_integral_comm' _ _ _ _ hsampN]
  have hLint : Integrable (fun omega : CutoffSample d =>
      descendantsAverage (originCube d (K : ℤ)) j (fun R => vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))) (cutoffSampleLaw
            M).toMeasure :=
    (integrable_finsetSum (descendantsAtDepth (originCube d (K : ℤ)) j) hsampN).const_mul _
  exact integral_mono hLint hsampG fun omega =>
    descendantsAverage_vecNormSq_cubeAverageVec_le_cubeAverage (originCube d (K : ℤ)) j _
      (fun R hR => hmemD omega.val R hR) (hintD omega.val)

/-- **Leg 2** --- `e.what.nablaw.really.is` at the grid, per sample. -/
private theorem step5_cross_per_sample (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ)
    (e : Vec d)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (alongIncrementPath n h wD omega)
        (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e x))
    (hintP : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n (n + (h : ℤ)) x)
        ((alongIncrementPath n h wD omega).toH1Function.grad x)))
      (cubeSet (originCube d (K : ℤ))) volume)
    (omega : CutoffSample d) :
    descendantsAverage (originCube d (K : ℤ)) j (fun R => vecDot e
            (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
      = ((Annealed.sigmaBar M n : ℝ)) * cubeAverage (originCube d (K : ℤ)) (fun x => vecNormSq
          ((alongIncrementPath n h wD omega.val).toH1Function.grad x))
        - descendantsAverage (originCube d (K : ℤ)) j (fun R =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)) := by
  have hsigpos : (0 : ℝ) < ((Annealed.sigmaBar M n : ℝ)) := (Annealed.sigmaBar M n).2
  rw [descendantsAverage_shellPairing_eq (originCube d (K : ℤ)) j omega.val n (n + (h : ℤ)) e
    (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) (hintP omega.val)]
  congr 1
  rw [cubeAverage_vecNormSq_grad_eq_shellPairing (originCube d (K : ℤ))
      ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e
      (alongIncrementPath n h wD omega.val) (hD omega.val),
    ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsigpos), one_mul]

/-- **Leg 2, averaged** --- the cross term is the Dirichlet energy up to the
grid average of the cross defects. -/
private theorem step5_cross_leg (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ) (e : Vec d)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (alongIncrementPath n h wD omega)
        (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e x))
    (hintP : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n (n + (h : ℤ)) x)
        ((alongIncrementPath n h wD omega).toH1Function.grad x)))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hsampX : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
          (cutoffSampleLaw M).toMeasure)
    (hsampG : Integrable (fun omega : CutoffSample d =>
      cubeAverage (originCube d (K : ℤ)) (fun x => vecNormSq
        ((alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure) :
    descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
      = ((Annealed.sigmaBar M n : ℝ)) * dirichletCubeEnergy M n h K wD
        - descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)
            ∂(cutoffSampleLaw M).toMeasure) := by
  have hDefAvgInt : Integrable (fun omega : CutoffSample d =>
      descendantsAverage (originCube d (K : ℤ)) j (fun R =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))) (cutoffSampleLaw
            M).toMeasure :=
    (integrable_finsetSum (descendantsAtDepth (originCube d (K : ℤ)) j) hsampDef).const_mul _
  rw [descendantsAverage_integral_comm' _ _ _ _ hsampX,
    descendantsAverage_integral_comm' _ _ _ _ hsampDef,
    show (fun omega : CutoffSample d =>
            descendantsAverage (originCube d (K : ℤ)) j (fun R => vecDot e
            (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
      = fun omega : CutoffSample d => ((Annealed.sigmaBar M n : ℝ)) *
          cubeAverage (originCube d (K : ℤ)) (fun x => vecNormSq
            ((alongIncrementPath n h wD omega.val).toH1Function.grad x))
        - descendantsAverage (originCube d (K : ℤ)) j (fun R =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
      from funext fun omega => step5_cross_per_sample M n h K j e wD hD hintP omega,
    integral_sub (hsampG.const_mul _) hDefAvgInt, integral_const_mul]
  rfl

/-- **Leg 3** --- the grid/sample Cauchy--Schwarz feeding
`e.lower.bound.oscillations`, at a **per-cube** forcing gauge.

The gauge family `gauge R omega` is the right factor of `e.nablaw.oscillations`
read at the cube `R`'s own base point; the caller instantiates it at
`3^nmesh * shellDerivNormSum n (n+h) (triadicCubeShift R) omega`. -/
private theorem step5_defect_leg (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ) (e : Vec d)
    (nmesh : ℤ) (gauge : TriadicCube d → CutoffSample d → ℝ) {Cdef : ℝ} (hCdef : 0 ≤ Cdef)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hgauge0 : ∀ (R : TriadicCube d) (omega : CutoffSample d), 0 ≤ gauge R omega)
    (hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
          (cutoffSampleLaw M).toMeasure)
    (hdefect : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j, ∀ omega : CutoffSample d,
      step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) ≤ Cdef *
            ((meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) * gauge R omega))
    (hmemOsc : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp
          (fun omega : CutoffSample d =>
            meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) 4
          (cutoffSampleLaw M).toMeasure)
    (hmemGauge : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp (fun omega : CutoffSample d => gauge R omega) 4
          (cutoffSampleLaw M).toMeasure) :
    descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)
            ∂(cutoffSampleLaw M).toMeasure)
      ≤ Cdef * ((gridFourthMomentRoot (cutoffSampleLaw M).toMeasure (descendantsAtDepth
        (originCube d (K : ℤ)) j)
      (fun R omega => meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R)) *
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j) gauge) := by
  have hintOG : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j, Integrable
      (fun omega : CutoffSample d =>
            (meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) *
        gauge R omega) (cutoffSampleLaw M).toMeasure := by
    intro R hR
    exact MemLp.integrable_mul (p := 2) (q := 2)
      ((hmemOsc R hR).mono_exponent (by norm_num))
      ((hmemGauge R hR).mono_exponent (by norm_num))
  have hstep1 : descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)
            ∂(cutoffSampleLaw M).toMeasure)
      ≤ Cdef * descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            (meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) *
        gauge R omega
            ∂(cutoffSampleLaw M).toMeasure) := by
    rw [← descendantsAverage_mul_left]
    refine descendantsAverage_le_descendantsAverage _ _ fun R hR => ?_
    rw [← integral_const_mul]
    exact integral_mono (hsampDef R hR) ((hintOG R hR).const_mul _) (hdefect R hR)
  have hstep2 := cubeFamilyAverage_integral_mul_le_gridFourthMomentRoot_mul_root
    (cutoffSampleLaw M).toMeasure (descendantsAtDepth (originCube d (K : ℤ)) j)
    (fun R omega => meshOscillationCell nmesh
      (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) gauge
    (fun R omega => meshOscillationCell_nonneg _ _ _) hgauge0 hmemOsc hmemGauge
  rw [descendantsAverage_eq_cubeFamilyAverage] at hstep1
  exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hCdef)

/-- The grid average of the per-cube excess splits into the three grid averages. -/
private theorem step5_average_split (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ)
    (e : Vec d)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hsampN : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hsampX : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampS : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure) :
    descendantsAverage (originCube d (K : ℤ)) j (fun R => ∫ omega : CutoffSample d,
        step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
          (alongIncrementPath n h wD) omega.val
            ∂(cutoffSampleLaw M).toMeasure)
      = descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            ∂(cutoffSampleLaw M).toMeasure)
        - (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
        + ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure) := by
  have hA : descendantsAverage (originCube d (K : ℤ)) j (fun R => ∫ omega : CutoffSample d,
        step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
          (alongIncrementPath n h wD) omega.val
            ∂(cutoffSampleLaw M).toMeasure)
      = descendantsAverage (originCube d (K : ℤ)) j (fun R => (∫ omega : CutoffSample d,
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            ∂(cutoffSampleLaw M).toMeasure)
          - (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (∫ omega : CutoffSample d,
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
          + ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * (∫ omega : CutoffSample d,
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)) :=
    descendantsAverage_congr_mem _ _ fun R hR =>
      step5CellExcess_integral_eq M n h K e wD R (hsampN R hR) (hsampX R hR) (hsampS R hR)
  rw [hA]
  exact descendantsAverage_lincomb _ _ _ _ _ _ _

/-- Nonnegativity of the grid fourth-moment root. -/
private theorem gridFourthMomentRoot_nonneg' {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (I : Finset (TriadicCube d)) (F : TriadicCube d → Omega → ℝ) :
    0 ≤ gridFourthMomentRoot mu I F :=
  Real.rpow_nonneg (gridFourthMoment_nonneg _ _ _) _

/-- **The numeric fold of the four legs of the Step-5 display.**  Everything the
display needs about the legs is recorded here as plain real arithmetic. -/
private theorem step5_fold (M : ABKModel d) (n : ℤ) (h : ℕ)
    {C1 C2 Cdef shellMoment gradMoment NN XX SS DD A cB EE : ℝ}
    (hCdef : 0 ≤ Cdef) (hgate : Cdef * M.gamma ^ (15 : ℕ) ≤ 2)
    (hA : 0 ≤ A) (hcB : 0 ≤ cB)
    (hjensen : NN ≤ EE)
    (hcross : XX = ((Annealed.sigmaBar M n : ℝ)) * EE - DD)
    (hdefbound : DD ≤ Cdef * (A * cB))
    (hosc : A + ((Annealed.sigmaBar M n : ℝ))⁻¹ * cB ≤ M.gamma ^ (15 : ℕ))
    (hC1 : 0 ≤ C1) (hgrad0 : 0 ≤ gradMoment)
    (hprod : SS ≤ shellMoment * gradMoment)
    (hshell : shellMoment ≤
      C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (hgradM : gradMoment ≤
      C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :
    NN - 2 * ((Annealed.sigmaBar M n : ℝ))⁻¹ * XX + ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * SS ≤
      -EE + (C1 * C2) * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
        + M.gamma ^ (15 : ℕ) := by
  have hsigpos : (0 : ℝ) < ((Annealed.sigmaBar M n : ℝ)) := (Annealed.sigmaBar M n).2
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hoscfinal := crossOscillationFold hA hcB (inv_pos.2 hsigpos).le hCdef hdefbound hosc
    (pow_nonneg hgamma0.le 15) hgate
  have hquadleg : ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * SS ≤
      (C1 * C2) * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
        (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
    rw [inv_pow]
    exact shellProduct_le_quadratic_error M hC1 hgrad0 hprod hshell hgradM
  exact step5Combine hsigpos hjensen hcross hoscfinal hquadleg

/-! ## The averaged Step-5 display -/

/-- **The averaged Step-5 display**, at the closure's grid carrier and the finite
localization cube.  This is exactly the binder `hdisplay` of
`step5GaugeEndpoint_of_cellDisplay`. -/
theorem step5CellDisplay_of_legs (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ)
    (e : Vec d) (nmesh : ℤ) (gauge : TriadicCube d → CutoffSample d → ℝ)
    {C1 C2 Cdef shellMoment gradMoment : ℝ}
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hgauge0 : ∀ (R : TriadicCube d) (omega : CutoffSample d), 0 ≤ gauge R omega)
    (hCdef : 0 ≤ Cdef) (hgate : Cdef * M.gamma ^ (15 : ℕ) ≤ 2)
    (hD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (alongIncrementPath n h wD omega)
        (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e x))
    (hmemD : ∀ (omega : ShellSeq d) (R : TriadicCube d), R ∈ descendantsAtDepth (originCube d (K :
      ℤ)) j →
      MemLp (fun x => (alongIncrementPath n h wD omega).toH1Function.grad x) 2
        (normalizedCubeMeasure R))
    (hintD : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecNormSq ((alongIncrementPath n h wD omega).toH1Function.grad x))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hintP : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n (n + (h : ℤ)) x)
        ((alongIncrementPath n h wD omega).toH1Function.grad x)))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hsampN : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hsampX : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampS : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
          (cutoffSampleLaw M).toMeasure)
    (hsampG : Integrable (fun omega : CutoffSample d =>
      cubeAverage (originCube d (K : ℤ)) (fun x => vecNormSq
        ((alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hdefect : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j, ∀ omega : CutoffSample d,
      step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) ≤ Cdef *
            ((meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) * gauge R omega))
    (hmemOsc : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp
          (fun omega : CutoffSample d =>
            meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) 4
          (cutoffSampleLaw M).toMeasure)
    (hmemGauge : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp (fun omega : CutoffSample d => gauge R omega) 4
          (cutoffSampleLaw M).toMeasure)
    (hosc : (gridFourthMomentRoot (cutoffSampleLaw M).toMeasure (descendantsAtDepth (originCube d
      (K : ℤ)) j)
      (fun R omega => meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R)) +
          ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j) gauge ≤ M.gamma ^ (15 : ℕ))
    (hC1 : 0 ≤ C1) (hgrad0 : 0 ≤ gradMoment)
    (hprod : descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
      ≤ shellMoment * gradMoment)
    (hshell : shellMoment ≤
      C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (hgradM : gradMoment ≤
      C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :
    descendantsAverage (originCube d (K : ℤ)) j (fun R => ∫ omega : CutoffSample d,
        step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
          (alongIncrementPath n h wD) omega.val
            ∂(cutoffSampleLaw M).toMeasure) ≤
      -dirichletCubeEnergy M n h K wD
        + (C1 * C2) * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
        + M.gamma ^ (15 : ℕ) := by
  rw [step5_average_split M n h K j e wD hsampN hsampX hsampS]
  exact step5_fold M n h hCdef hgate (gridFourthMomentRoot_nonneg' _ _ _)
    (gridFourthMomentRoot_nonneg' _ _ _)
    (step5_jensen_leg M n h K j wD hmemD hintD hsampN hsampG)
    (step5_cross_leg M n h K j e wD hD hintP hsampX hsampDef hsampG)
    (step5_defect_leg M n h K j e nmesh gauge hCdef wD hgauge0 hsampDef hdefect hmemOsc
      hmemGauge)
    hosc hC1 hgrad0 hprod hshell hgradM

/-! ## The endpoint -/

/-- The per-cube Step-5 excess is sample integrable as soon as its three terms
are. -/
private theorem step5CellExcess_integrable (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ)
    (e : Vec d)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (R : TriadicCube d)
    (hN : Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hX : Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hS : Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega : CutoffSample d =>
      step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
        (alongIncrementPath n h wD) omega.val) (cutoffSampleLaw M).toMeasure := by
  have hIX : Integrable (fun omega : CutoffSample d =>
      (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (vecDot e (matVecMul (freshShellCubeAverage R
        omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
            (cutoffSampleLaw M).toMeasure := hX.const_mul _
  have hIS : Integrable (fun omega : CutoffSample d =>
      ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * (vecNormSq (matVecMul (freshShellCubeAverage R
        omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
            (cutoffSampleLaw M).toMeasure := hS.const_mul _
  have hIsub : Integrable (fun omega : CutoffSample d =>
      vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            - (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (vecDot e (matVecMul (freshShellCubeAverage
              R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
            (cutoffSampleLaw M).toMeasure := hN.sub hIX
  have hfun : (fun omega : CutoffSample d =>
      step5CellExcess (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e
        (alongIncrementPath n h wD) omega.val)
      = fun omega : CutoffSample d =>
        (vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
            - (2 * ((Annealed.sigmaBar M n : ℝ))⁻¹) * (vecDot e (matVecMul (freshShellCubeAverage
              R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))))
        + ((Annealed.sigmaBar M n : ℝ))⁻¹ ^ 2 * (vecNormSq (matVecMul (freshShellCubeAverage R
          omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))) := rfl
  rw [hfun]
  exact hIsub.add hIS

/-- **`Closure.Step5GaugeEndpoint`, from the two correctors and the named legs, at
a per-cube forcing gauge.**  This is the Step-5 mirror of
`Closure.JunctionDischargeStepFour.step4GaugeEndpoint_of_correctors`.

The gauge family `gauge R omega` is the right factor of `e.nablaw.oscillations`
read at the cube `R`'s own base point; the producer instantiates it at `3^nmesh
* shellDerivNormSum n (n+h) (triadicCubeShift R) omega`. -/
theorem step5GaugeEndpoint_of_correctors_gauge (M : ABKModel d) (n : ℤ) (h : ℕ) (K j : ℕ)
    {e : Vec d} (he : vecNormSq e = 1) (nmesh : ℤ)
    (gauge : TriadicCube d → CutoffSample d → ℝ)
    {C1 C2 Cdef shellMoment gradMoment : ℝ}
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (wN : C(Vec d, Mat d) → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))))
    (hgauge0 : ∀ (R : TriadicCube d) (omega : CutoffSample d), 0 ≤ gauge R omega)
    (hCdef : 0 ≤ Cdef) (hgate : Cdef * M.gamma ^ (15 : ℕ) ≤ 2)
    (hD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (alongIncrementPath n h wD omega)
        (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e x))
    (hN : ∀ omega : ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (originCube d (K : ℤ))) (alongIncrementPath n h wN omega)
        (fun x => -streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) (0 : Vec d)
          x))
    (hmemD : ∀ (omega : ShellSeq d) (R : TriadicCube d), R ∈ descendantsAtDepth (originCube d (K :
      ℤ)) j →
      MemLp (fun x => (alongIncrementPath n h wD omega).toH1Function.grad x) 2
        (normalizedCubeMeasure R))
    (hintD : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecNormSq ((alongIncrementPath n h wD omega).toH1Function.grad x))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hintP : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n (n + (h : ℤ)) x)
        ((alongIncrementPath n h wD omega).toH1Function.grad x)))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hsampN : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hsampX : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampS : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x))
          (cutoffSampleLaw M).toMeasure)
    (hsampG : Integrable (fun omega : CutoffSample d =>
      cubeAverage (originCube d (K : ℤ)) (fun x => vecNormSq
        ((alongIncrementPath n h wD omega.val).toH1Function.grad x)))
          (cutoffSampleLaw M).toMeasure)
    (hdefect : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j, ∀ omega : CutoffSample d,
      step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) ≤ Cdef *
            ((meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) * gauge R omega))
    (hmemOsc : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp
          (fun omega : CutoffSample d =>
            meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R) 4
          (cutoffSampleLaw M).toMeasure)
    (hmemGauge : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp (fun omega : CutoffSample d => gauge R omega) 4
          (cutoffSampleLaw M).toMeasure)
    (hosc : (gridFourthMomentRoot (cutoffSampleLaw M).toMeasure (descendantsAtDepth (originCube d
      (K : ℤ)) j)
      (fun R omega => meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x) R)) +
          ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j) gauge ≤ M.gamma ^ (15 : ℕ))
    (hC1 : 0 ≤ C1) (hgrad0 : 0 ≤ gradMoment)
    (hprod : descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h wD omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
      ≤ shellMoment * gradMoment)
    (hshell : shellMoment ≤
      C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (hgradM : gradMoment ≤
      C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :
    Step5GaugeEndpoint M n h K j e (C1 * C2) wD wN :=
  step5GaugeEndpoint_of_cellDisplay M n h K j he (C1 * C2) wD wN hN
    (fun R hR => step5CellExcess_integrable M n h K e wD R
      (hsampN R hR) (hsampX R hR) (hsampS R hR))
    (step5CellDisplay_of_legs M n h K j e nmesh gauge wD hgauge0 hCdef hgate hD hmemD hintD
      hintP hsampN hsampX hsampS hsampDef hsampG hdefect hmemOsc hmemGauge hosc hC1 hgrad0
      hprod hshell hgradM)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
