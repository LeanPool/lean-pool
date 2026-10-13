/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableGradient

/-!
# CorrectorMeasurableOctic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Borel measurability of the octic window observables

`CorrectorMeasurableQuartic` turns the *quartic* window functional
`F |-> int_S ‖F x‖^4` into a Borel function of the `L^2` class, by a countable
supremum of Lipschitz truncations.  The eighth-moment envelope of
`LocalizationFluctuationEighthMoment` and `LocalizationFluctuationGridEighth`
reads the *octic* window functional instead, and the same route carries it: the
only thing that changes is the truncation exponent and its Lipschitz constant.

## The route

For `n : Nat` put `g_n(v) = (max (min ‖v‖ n) 0)^8`.  The clamp is `1`-Lipschitz
and `t |-> t^8` has slope at most `8 n^7` on `[0, n]`, so each `g_n` is
Lipschitz with constant `8 n^7` and kills `0`; mathlib's `LipschitzWith.compLp`
turns it into a *continuous* map of `L^2` classes, and composing with
CoarseGraining's continuous linear window functional `scalarL2SetIntegralCLM` gives
a continuous real functional

```
  Phi_n (F) = int_S g_n(F x) dx .
```

Pointwise `g_n(v)` increases to `‖v‖^8`, so monotone convergence identifies the
lower integral `int_S ‖F x‖^8` (in `ℝ≥0∞`) with `⨆_n Phi_n(F)`, a countable
supremum of continuous functionals, hence Borel.  Reading it back through
`integral_eq_lintegral_of_nonneg_ae` -- which needs no integrability, both sides
being `0` off the integrable set -- gives Borel measurability of the Bochner
functional `F |-> int_S ‖F x‖^8`.

**No new obstruction appears at the eighth power.**  The quartic route uses only
(i) boundedness of the clamp, which is exponent-free, and (ii) the algebraic
factorization `A^k - B^k = (A - B) * sum_{i<k} A^i B^{k-1-i}`, whose `k = 8`
instance is the same one-line `ring` identity as its `k = 4` instance.  Nothing
in the argument is special to `4`.

## What is proved

Two `private` steps carry the analysis -- Borel measurability of
`F |-> int_S ‖F x‖^8` on `HilbertVectorL2 U`, and its identification at a
gradient class with the ordinary Lebesgue integral of `|grad w|^8` over a window
`S ⊆ U` -- and the file exports only what a consumer reads:

* `measurable_volumeAverage_vecNormSq_pow_four_freshShellDirichletGrad` and its
  Neumann mirror: the normalized eighth energy of the corrector gradient over
  any window of the cube is a measurable function of the sample, for an
  arbitrary family of weak solutions of `e.def.w`.

## Scope

It is an ordinary conditional Provider helper.  No frozen theorem is consumed
and no `sorry` occurs.

## References

* ABK26, `e.def.w` (the correctors whose gradients are read).
* ABK26, `e.nablaw.in.L.eight` (the eighth window energies).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The clamped octic on the Euclidean carrier -/

/-- The octic truncated at height `n`: `(max (min ‖v‖ n) 0)^8`.  The clamp is
taken on both sides so that the function is globally Lipschitz on the carrier,
not merely on the range of the norm. -/
def hilbertVecOcticTrunc (n : ℕ) (v : HilbertVec d) : ℝ :=
  max (min ‖v‖ (n : ℝ)) 0 ^ 8

theorem hilbertVecOcticTrunc_zero (n : ℕ) :
    hilbertVecOcticTrunc (d := d) n 0 = 0 := by
  unfold hilbertVecOcticTrunc
  rw [norm_zero, min_eq_left (Nat.cast_nonneg n), max_self]
  norm_num

/-- The elementary monomial bound behind the Lipschitz constant. -/
private theorem pow_mul_pow_le_pow_add {A B n : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hAn : A ≤ n) (hBn : B ≤ n) (i j : ℕ) : A ^ i * B ^ j ≤ n ^ (i + j) := by
  have hn : 0 ≤ n := le_trans hA0 hAn
  calc A ^ i * B ^ j ≤ n ^ i * n ^ j :=
        mul_le_mul (pow_le_pow_left₀ hA0 hAn i) (pow_le_pow_left₀ hB0 hBn j)
          (pow_nonneg hB0 j) (pow_nonneg hn i)
    _ = n ^ (i + j) := (pow_add n i j).symm

theorem lipschitzWith_hilbertVecOcticTrunc (n : ℕ) :
    LipschitzWith (8 * (n : NNReal) ^ 7) (hilbertVecOcticTrunc (d := d) n) := by
  have hclamp : LipschitzWith 1 (fun v : HilbertVec d => max (min ‖v‖ (n : ℝ)) 0) :=
    (lipschitzWith_one_norm.min_const _).max_const _
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  set A : ℝ := max (min ‖x‖ (n : ℝ)) 0 with hA
  set B : ℝ := max (min ‖y‖ (n : ℝ)) 0 with hB
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  have hAn : A ≤ (n : ℝ) := max_le (min_le_right _ _) (Nat.cast_nonneg n)
  have hBn : B ≤ (n : ℝ) := max_le (min_le_right _ _) (Nat.cast_nonneg n)
  have hAB : |A - B| ≤ dist x y := by
    have h := hclamp.dist_le_mul x y
    simpa [Real.dist_eq, hA, hB] using h
  have hcast : ((8 * (n : NNReal) ^ 7 : NNReal) : ℝ) = 8 * (n : ℝ) ^ 7 := by
    push_cast
    ring
  rw [Real.dist_eq, hcast]
  change |A ^ 8 - B ^ 8| ≤ 8 * (n : ℝ) ^ 7 * dist x y
  set Sm : ℝ := A ^ 7 + A ^ 6 * B + A ^ 5 * B ^ 2 + A ^ 4 * B ^ 3 + A ^ 3 * B ^ 4 +
    A ^ 2 * B ^ 5 + A * B ^ 6 + B ^ 7 with hSm
  have hfac : A ^ 8 - B ^ 8 = (A - B) * Sm := by
    rw [hSm]; ring
  have hsumnn : 0 ≤ Sm := by
    have h0 := pow_nonneg hA0 7
    have h1 := mul_nonneg (pow_nonneg hA0 6) hB0
    have h2 := mul_nonneg (pow_nonneg hA0 5) (pow_nonneg hB0 2)
    have h3 := mul_nonneg (pow_nonneg hA0 4) (pow_nonneg hB0 3)
    have h4 := mul_nonneg (pow_nonneg hA0 3) (pow_nonneg hB0 4)
    have h5 := mul_nonneg (pow_nonneg hA0 2) (pow_nonneg hB0 5)
    have h6 := mul_nonneg hA0 (pow_nonneg hB0 6)
    have h7 := pow_nonneg hB0 7
    rw [hSm]
    linarith
  have hsum : Sm ≤ 8 * (n : ℝ) ^ 7 := by
    have e0 : A ^ 7 ≤ (n : ℝ) ^ 7 := pow_le_pow_left₀ hA0 hAn 7
    have e7 : B ^ 7 ≤ (n : ℝ) ^ 7 := pow_le_pow_left₀ hB0 hBn 7
    have e1 : A ^ 6 * B ≤ (n : ℝ) ^ 7 := by
      simpa using pow_mul_pow_le_pow_add hA0 hB0 hAn hBn 6 1
    have e2 : A ^ 5 * B ^ 2 ≤ (n : ℝ) ^ 7 := by
      simpa using pow_mul_pow_le_pow_add hA0 hB0 hAn hBn 5 2
    have e3 : A ^ 4 * B ^ 3 ≤ (n : ℝ) ^ 7 := by
      simpa using pow_mul_pow_le_pow_add hA0 hB0 hAn hBn 4 3
    have e4 : A ^ 3 * B ^ 4 ≤ (n : ℝ) ^ 7 := by
      simpa using pow_mul_pow_le_pow_add hA0 hB0 hAn hBn 3 4
    have e5 : A ^ 2 * B ^ 5 ≤ (n : ℝ) ^ 7 := by
      simpa using pow_mul_pow_le_pow_add hA0 hB0 hAn hBn 2 5
    have e6 : A * B ^ 6 ≤ (n : ℝ) ^ 7 := by
      simpa using pow_mul_pow_le_pow_add hA0 hB0 hAn hBn 1 6
    rw [hSm]
    linarith
  calc |A ^ 8 - B ^ 8|
      = |A - B| * |Sm| := by rw [hfac, abs_mul]
    _ = |A - B| * Sm := by rw [abs_of_nonneg hsumnn]
    _ ≤ dist x y * (8 * (n : ℝ) ^ 7) := mul_le_mul hAB hsum hsumnn dist_nonneg
    _ = 8 * (n : ℝ) ^ 7 * dist x y := by ring

private theorem hilbertVecOcticTrunc_nonneg (n : ℕ) (v : HilbertVec d) :
    0 ≤ hilbertVecOcticTrunc n v :=
  pow_nonneg (le_max_right _ _) 8

private theorem hilbertVecOcticTrunc_le (n : ℕ) (v : HilbertVec d) :
    hilbertVecOcticTrunc n v ≤ ‖v‖ ^ 8 :=
  pow_le_pow_left₀ (le_max_right _ _)
    (max_le (min_le_left _ _) (norm_nonneg v)) 8

private theorem monotone_hilbertVecOcticTrunc (v : HilbertVec d) :
    Monotone fun n : ℕ => hilbertVecOcticTrunc n v := by
  intro a b hab
  refine pow_le_pow_left₀ (le_max_right _ _) ?_ 8
  refine max_le_max ?_ le_rfl
  exact min_le_min le_rfl (by exact_mod_cast hab)

private theorem iSup_ofReal_hilbertVecOcticTrunc (v : HilbertVec d) :
    ⨆ n : ℕ, ENNReal.ofReal (hilbertVecOcticTrunc n v) =
      ENNReal.ofReal (‖v‖ ^ 8) := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal
    (hilbertVecOcticTrunc_le n v)) ?_
  refine le_iSup_of_le ⌈‖v‖⌉₊ (ENNReal.ofReal_le_ofReal ?_)
  have hmin : min ‖v‖ ((⌈‖v‖⌉₊ : ℕ) : ℝ) = ‖v‖ := min_eq_left (Nat.le_ceil _)
  unfold hilbertVecOcticTrunc
  rw [hmin, max_eq_left (norm_nonneg v)]

/-! ## The truncated window functional is continuous -/

variable {U : Set (Vec d)}

/-- The truncated window functional `F |-> int_S g_n(F x)`, presented as a
composition of two continuous maps: mathlib's Lipschitz composition on `L^2`
classes, and CoarseGraining's continuous linear window integration functional. -/
def windowOcticTrunc [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (n : ℕ) (F : HilbertVectorL2 U) : ℝ :=
  scalarL2SetIntegralCLM (U := U) S hS
    ((lipschitzWith_hilbertVecOcticTrunc (d := d) n).compLp
      (hilbertVecOcticTrunc_zero n) F)

private theorem continuous_windowOcticTrunc [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (n : ℕ) :
    Continuous (windowOcticTrunc (U := U) S hS n) :=
  (scalarL2SetIntegralCLM (U := U) S hS).continuous.comp
    (LipschitzWith.continuous_compLp _ _)

private theorem windowOcticTrunc_eq [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (n : ℕ) (F : HilbertVectorL2 U) :
    windowOcticTrunc (U := U) S hS n F =
      ∫ x in S, hilbertVecOcticTrunc n (F x) ∂(volumeMeasureOn U) := by
  rw [windowOcticTrunc, scalarL2SetIntegralCLM_apply]
  refine integral_congr_ae ?_
  exact ((lipschitzWith_hilbertVecOcticTrunc (d := d) n).coeFn_compLp
    (hilbertVecOcticTrunc_zero n) F).filter_mono
    (ae_mono Measure.restrict_le_self)

/-! ## Borel measurability of the octic window functional -/

private theorem measurable_setLIntegral_norm_pow_eight
    [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) :
    Measurable fun F : HilbertVectorL2 U =>
      ∫⁻ x in S, ENNReal.ofReal (‖F x‖ ^ 8) ∂(volumeMeasureOn U) := by
  have hmeas : ∀ n : ℕ, Measurable fun F : HilbertVectorL2 U =>
      ENNReal.ofReal (windowOcticTrunc (U := U) S hS n F) := fun n =>
    (continuous_windowOcticTrunc (U := U) S hS n).measurable.ennreal_ofReal
  have hEq : (fun F : HilbertVectorL2 U =>
      ∫⁻ x in S, ENNReal.ofReal (‖F x‖ ^ 8) ∂(volumeMeasureOn U)) =
      fun F : HilbertVectorL2 U =>
        ⨆ n : ℕ, ENNReal.ofReal (windowOcticTrunc (U := U) S hS n F) := by
    funext F
    have hcoe : AEStronglyMeasurable (fun x => (F : Vec d → HilbertVec d) x)
        ((volumeMeasureOn U).restrict S) := (Lp.aestronglyMeasurable F).restrict
    have haem : ∀ n : ℕ, AEMeasurable
        (fun x => ENNReal.ofReal (hilbertVecOcticTrunc n ((F : Vec d → HilbertVec d) x)))
        ((volumeMeasureOn U).restrict S) := by
      intro n
      refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact (((lipschitzWith_hilbertVecOcticTrunc (d := d)
        n).continuous).comp_aestronglyMeasurable hcoe).aemeasurable
    have hfin : ∀ n : ℕ,
        ∫⁻ x in S, ENNReal.ofReal (hilbertVecOcticTrunc n
            ((F : Vec d → HilbertVec d) x)) ∂(volumeMeasureOn U) ≠ ⊤ := by
      intro n
      refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x =>
        ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (le_max_right _ _)
            (max_le (min_le_right _ _) (Nat.cast_nonneg n)) 8))
      rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top ((volumeMeasureOn U).restrict S) Set.univ)
    have htrunc : ∀ n : ℕ,
        ENNReal.ofReal (windowOcticTrunc (U := U) S hS n F) =
          ∫⁻ x in S, ENNReal.ofReal (hilbertVecOcticTrunc n
            ((F : Vec d → HilbertVec d) x)) ∂(volumeMeasureOn U) := by
      intro n
      rw [windowOcticTrunc_eq, integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun x => hilbertVecOcticTrunc_nonneg n _)
        ((((lipschitzWith_hilbertVecOcticTrunc (d := d) n).continuous).comp_aestronglyMeasurable
          hcoe))]
      exact ENNReal.ofReal_toReal (hfin n)
    simp_rw [htrunc]
    rw [← lintegral_iSup' haem
      (Filter.Eventually.of_forall fun x => by
        intro a b hab
        exact ENNReal.ofReal_le_ofReal (monotone_hilbertVecOcticTrunc _ hab))]
    exact lintegral_congr fun x => (iSup_ofReal_hilbertVecOcticTrunc _).symm
  rw [hEq]
  exact Measurable.iSup hmeas

/-- **Unconditional: the octic window functional is Borel on `L^2`.**

`F |-> int_S ‖F x‖^8` is a Borel measurable function of the `L^2` class `F`, for
every measurable window `S` and every domain of finite volume.  It is not
continuous, and no continuity is claimed; the proof is the countable supremum of
the truncated functionals. -/
private theorem measurable_setIntegral_norm_pow_eight [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) :
    Measurable fun F : HilbertVectorL2 U =>
      ∫ x in S, ‖(F : Vec d → HilbertVec d) x‖ ^ 8 ∂(volumeMeasureOn U) := by
  have hEq : (fun F : HilbertVectorL2 U =>
      ∫ x in S, ‖(F : Vec d → HilbertVec d) x‖ ^ 8 ∂(volumeMeasureOn U)) =
      fun F : HilbertVectorL2 U =>
        (∫⁻ x in S, ENNReal.ofReal (‖(F : Vec d → HilbertVec d) x‖ ^ 8)
          ∂(volumeMeasureOn U)).toReal := by
    funext F
    refine integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => by positivity) ?_
    exact ((continuous_pow 8).comp continuous_norm).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable F).restrict
  rw [hEq]
  exact (measurable_setLIntegral_norm_pow_eight (U := U) S hS).ennreal_toReal

/-! ## From the `L^2` class back to the pointwise gradient -/

/-- Unconditional: the octic window functional at the gradient class of an `H^1`
function is the ordinary Lebesgue integral of `|grad w|^8` over the window, for
any measurable window contained in the domain. -/
private theorem setIntegral_vecNormSq_pow_four_eq (w : H1Function U) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫ x in S, ‖(w.gradToHilbertVectorL2 : Vec d → HilbertVec d) x‖ ^ 8
        ∂(volumeMeasureOn U) =
      ∫ x in S, vecNormSq (w.grad x) ^ 4 ∂volume := by
  have hrestrict : (volumeMeasureOn U).restrict S = volume.restrict S := by
    rw [Measure.restrict_restrict hS, Set.inter_eq_self_of_subset_left hSU]
  have hae : ∀ᵐ x ∂((volumeMeasureOn U).restrict S),
      ‖(w.gradToHilbertVectorL2 : Vec d → HilbertVec d) x‖ ^ 8 =
        vecNormSq (w.grad x) ^ 4 := by
    refine (w.coeFn_gradToHilbertVectorL2.filter_mono
      (ae_mono Measure.restrict_le_self)).mono fun x hx => ?_
    rw [hx]
    have hsq : ‖HilbertVec.ofVec (w.grad x)‖ ^ 2 = vecNormSq (w.grad x) :=
      HilbertVec.norm_sq_ofVec (w.grad x)
    calc ‖hilbertifyVecField w.grad x‖ ^ 8
        = (‖HilbertVec.ofVec (w.grad x)‖ ^ 2) ^ 4 := by
          rw [hilbertifyVecField]
          ring
      _ = vecNormSq (w.grad x) ^ 4 := by rw [hsq]
  rw [integral_congr_ae hae, hrestrict]

/-! ## The corrector-level consequence -/

/-- Unconditional: for a measurable family of `L^2` classes, the normalized
eighth energy over a window of `U` is a measurable function of the sample. -/
private theorem measurable_volumeAverage_normPowEight {Omega : Type*}
    [MeasurableSpace Omega] [IsFiniteMeasure (volumeMeasureOn U)]
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ U)
    {F : Omega → HilbertVectorL2 U} (hF : Measurable F)
    {w : Omega → H1Function U}
    (hw : ∀ omega, F omega = (w omega).gradToHilbertVectorL2) :
    Measurable fun omega =>
      volumeAverage S (fun x => vecNormSq ((w omega).grad x) ^ 4) := by
  have hEq : (fun omega =>
      volumeAverage S (fun x => vecNormSq ((w omega).grad x) ^ 4)) =
      fun omega => (volume S).toReal⁻¹ *
        ∫ x in S, ‖((F omega : Vec d → HilbertVec d)) x‖ ^ 8
          ∂(volumeMeasureOn U) := by
    funext omega
    rw [hw omega, setIntegral_vecNormSq_pow_four_eq (w omega) hS hSU, volumeAverage]
  rw [hEq]
  exact measurable_const.mul
    ((measurable_setIntegral_norm_pow_eight (U := U) S hS).comp hF)

/-- Unconditional: **the normalized eighth energy of the Dirichlet corrector
gradient over any measurable window of the cube is a measurable function of the
sample.**

`wD` is an arbitrary family of zero-trace weak solutions of the fresh-shell
Dirichlet problem `e.def.w`; no measurability, continuity or selection property
of the family is assumed.  This is the octic observable the eighth-moment
envelope reads. -/
theorem measurable_volumeAverage_vecNormSq_pow_four_freshShellDirichletGrad [NeZero d]
    (Q : TriadicCube d) (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega =>
      volumeAverage S
        (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 4) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact measurable_volumeAverage_normPowEight hS hSU
    (measurable_freshShellDirichletGradL2 Q sigmaInv n m e wD hwD)
    (w := fun omega => (wD omega).toH1Function) fun _ => rfl

/-- Unconditional: the Neumann mirror of the previous statement. -/
theorem measurable_volumeAverage_vecNormSq_pow_four_freshShellNeumannGrad
    (Q : TriadicCube d) (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwN : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega =>
      volumeAverage S
        (fun x => vecNormSq ((wN omega).toH1Function.grad x) ^ 4) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact measurable_volumeAverage_normPowEight hS hSU
    (measurable_freshShellNeumannGradL2 Q sigmaInv n m e wN hwN)
    (w := fun omega => (wN omega).toH1Function) fun _ => rfl

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
