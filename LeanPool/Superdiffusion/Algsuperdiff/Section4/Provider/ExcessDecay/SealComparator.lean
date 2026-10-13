/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidualCorrectorExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundarySplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportNorms

/-!
# SealComparator

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `Δ`-harmonic comparator with the Dirichlet-principle `L²` bound

## What is proved

For a translated triadic cube `V = translateSet c □_j` inside the anchor's
domain `□_m` and an ambient datum `h : H¹(□_m)`, there is a **`Δ`-harmonic
comparator** `w ∈ h + H¹₀(V)` — the `H¹₀` corrector `ρ` is exposed, with exact
pointwise value and gradient identities — satisfying the coefficient-free
Dirichlet-principle bound (`exists_deltaComparator_translatedCube`)

```text
  ‖h − w‖_{L²(V)} ≤ comparatorPoincareConst d · 3^j · Σᵢ ‖∂ᵢh‖_{L²(V)} ,
```

`comparatorPoincareConst d = √d · dirichletCubePoincareConst d`, a function of
`d` alone.  The two moves:

* **energy minimality** (`setIntegral_vecNormSq_grad_corrector_le`): testing
  the corrector's zero-trace weak equation at the identity background with the
  corrector itself and completing the square gives `∫_V |∇ρ|² ≤ ∫_V |∇h|²` —
  no Cauchy–Schwarz on the pairing, no ellipticity constant;
* **the Dirichlet Poincaré** (`BoundarySplit`), transported to the translated
  frame through `H10Function.untranslate` and the exact norm transport of
  `Ch01.volumeAverage_translateSet_eq_comp_addRight`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2, (the two `Δ`-harmonic
  replacements of the boundary covering argument).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 0. Square-root/sum calculus on `Fin d` -/

/-- `√(x + y) ≤ √x + √y`. -/
theorem sealSqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hnn : 0 ≤ Real.sqrt x + Real.sqrt y :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have h2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    have h3 : 0 ≤ 2 * (Real.sqrt x * Real.sqrt y) := by positivity
    calc x + y = Real.sqrt x ^ 2 + Real.sqrt y ^ 2 := by rw [h1, h2]
      _ ≤ Real.sqrt x ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) + Real.sqrt y ^ 2 := by
          linarith only [h3]
      _ = (Real.sqrt x + Real.sqrt y) ^ 2 := by ring
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq hnn

/-- `√(Σ aᵢ) ≤ Σ √aᵢ` for nonnegative terms. -/
theorem sqrt_sum_le_sum_sqrt {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Real.sqrt (∑ i : Fin d, a i) ≤ ∑ i : Fin d, Real.sqrt (a i) := by
  classical
  suffices h : ∀ s : Finset (Fin d),
      Real.sqrt (∑ i ∈ s, a i) ≤ ∑ i ∈ s, Real.sqrt (a i) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      have hsum : 0 ≤ ∑ k ∈ s, a k := Finset.sum_nonneg fun k _ => ha k
      calc Real.sqrt (a i + ∑ k ∈ s, a k)
          ≤ Real.sqrt (a i) + Real.sqrt (∑ k ∈ s, a k) :=
            sealSqrt_add_le_sqrt_add_sqrt (ha i) hsum
        _ ≤ Real.sqrt (a i) + ∑ k ∈ s, Real.sqrt (a k) := by linarith only [ih]

/-- `Σᵢ √aᵢ ≤ √d · √(Σᵢ aᵢ)` (Cauchy–Schwarz on `Fin d`). -/
theorem sum_sqrt_le_sqrt_card_mul_sqrt {a : Fin d → ℝ} (ha : ∀ i, 0 ≤ a i) :
    ∑ i : Fin d, Real.sqrt (a i) ≤
      Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, a i) := by
  classical
  have hsq : (∑ i : Fin d, Real.sqrt (a i)) ^ 2 ≤
      (d : ℝ) * ∑ i : Fin d, a i := by
    have hcheb := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin d))) (f := fun i => Real.sqrt (a i))
    have hcard : (((Finset.univ : Finset (Fin d)).card : ℝ)) = (d : ℝ) := by simp
    have hterm : ∑ i : Fin d, Real.sqrt (a i) ^ 2 = ∑ i : Fin d, a i :=
      Finset.sum_congr rfl fun i _ => Real.sq_sqrt (ha i)
    calc (∑ i : Fin d, Real.sqrt (a i)) ^ 2
        ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) *
            ∑ i : Fin d, Real.sqrt (a i) ^ 2 := hcheb
      _ = (d : ℝ) * ∑ i : Fin d, a i := by rw [hcard, hterm]
  have hlhs : 0 ≤ ∑ i : Fin d, Real.sqrt (a i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc ∑ i : Fin d, Real.sqrt (a i)
      = Real.sqrt ((∑ i : Fin d, Real.sqrt (a i)) ^ 2) := (Real.sqrt_sq hlhs).symm
    _ ≤ Real.sqrt ((d : ℝ) * ∑ i : Fin d, a i) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, a i) := Real.sqrt_mul hd _

/-! ## 1. `L²` product integrability and the `vecDot` expansion -/

private theorem holderTriple_two_two' : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
  ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩

private theorem integrableOn_mul_of_memL2 {V : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict V)) (hv : MemLp v 2 (volume.restrict V)) :
    IntegrableOn (fun y => u y * v y) V volume := by
  have := holderTriple_two_two'
  exact hu.integrable_mul hv

private theorem integrableOn_vecDot_of_memL2 {V : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (volume.restrict V))
    (hG : ∀ i, MemLp (fun y => G y i) 2 (volume.restrict V)) :
    IntegrableOn (fun y => vecDot (F y) (G y)) V volume := by
  classical
  have hterm : ∀ i : Fin d, IntegrableOn (fun y => F y i * G y i) V volume :=
    fun i => integrableOn_mul_of_memL2 (hF i) (hG i)
  have hsum : IntegrableOn (fun y => ∑ i : Fin d, F y i * G y i) V volume :=
    MeasureTheory.integrable_finsetSum Finset.univ fun i _ => hterm i
  have hfun : (fun y => vecDot (F y) (G y)) =
      fun y => ∑ i : Fin d, F y i * G y i := by
    funext y
    rfl
  rw [hfun]
  exact hsum

private theorem vecDot_add_self (x y : Vec d) :
    vecDot (x + y) (x + y) = vecDot x x + 2 * vecDot x y + vecDot y y := by
  classical
  simp only [vecDot, Pi.add_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem vecDot_neg_left' (x y : Vec d) : vecDot (-x) y = -vecDot x y := by
  classical
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-! ## 2. The identity-background corrector -/

/-- **The zero-trace corrector at the identity background exists**: an `H¹₀(V)`
function `ρ` with `∫_V ∇ρ·∇φ = −∫_V ∇Φ·∇φ` for every `φ ∈ H¹₀(V)`.  This is
CoarseGraining's Dirichlet existence theorem at the identity coefficient field. -/
theorem exists_identityCorrector [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (Φ : H1Function V) :
    ∃ rho : H10Function V,
      IsZeroTraceDirichletRhsWeakSolution (unitCoeffField d) V rho
        (fun y => -Φ.grad y) := by
  have : IsFiniteMeasure (volumeMeasureOn V) := hV.isFiniteMeasure_restrict_volume
  have hgrad : MemVectorL2 V Φ.grad := Φ.grad_memVectorL2
  have hg : MemVectorL2 V (fun y => -Φ.grad y) := hgrad.neg
  have hrealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization V :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
      hV
  exact
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := unitCoeffField d) (U := V) (g := fun y => -Φ.grad y) (lam := 1) (Lam := 1)
      hg hrealize hne (isEllipticFieldOn_unitCoeffField hV.isOpen.measurableSet)

/-! ## 3. Energy minimality: the Dirichlet principle, by completing the square -/

/-- **The corrector's gradient energy is at most the datum's.**

Test the corrector's own weak equation with the corrector and complete the
square: `0 ≤ ∫|∇Φ + ∇ρ|² = ∫|∇Φ|² − ∫|∇ρ|²`. -/
theorem setIntegral_vecNormSq_grad_corrector_le {V : Set (Vec d)}
    (hVm : MeasurableSet V) (Φ : H1Function V) {rho : H10Function V}
    (hrho : IsZeroTraceDirichletRhsWeakSolution (unitCoeffField d) V rho
      (fun y => -Φ.grad y)) :
    ∫ y in V, vecNormSq (rho.toH1Function.grad y) ≤
      ∫ y in V, vecNormSq (Φ.grad y) := by
  classical
  set F : Vec d → Vec d := Φ.grad with hF
  set G : Vec d → Vec d := rho.toH1Function.grad with hG
  have hFi : ∀ i, MemLp (fun y => F y i) 2 (volume.restrict V) := fun i => Φ.gradMemL2 i
  have hGi : ∀ i, MemLp (fun y => G y i) 2 (volume.restrict V) :=
    fun i => rho.toH1Function.gradMemL2 i
  have hIFF : IntegrableOn (fun y => vecDot (F y) (F y)) V volume :=
    integrableOn_vecDot_of_memL2 hFi hFi
  have hIFG : IntegrableOn (fun y => vecDot (F y) (G y)) V volume :=
    integrableOn_vecDot_of_memL2 hFi hGi
  have hIGG : IntegrableOn (fun y => vecDot (G y) (G y)) V volume :=
    integrableOn_vecDot_of_memL2 hGi hGi
  -- the weak identity, tested with the corrector itself
  have hid : ∫ y in V, vecDot (G y) (G y) = -∫ y in V, vecDot (F y) (G y) := by
    have h0 := hrho rho
    have hleft : ∫ y in V,
        vecDot (matVecMul (unitCoeffField d y) (rho.toH1Function.grad y))
          (rho.toH1Function.grad y) = ∫ y in V, vecDot (G y) (G y) := by
      refine setIntegral_congr_fun hVm fun y _ => ?_
      rw [matVecMul_unitCoeffField]
    have hright : ∫ y in V, vecDot ((fun y' => -Φ.grad y') y)
        (rho.toH1Function.grad y) = -∫ y in V, vecDot (F y) (G y) := by
      have hfun : (fun y => vecDot ((fun y' => -Φ.grad y') y)
          (rho.toH1Function.grad y)) = fun y => -vecDot (F y) (G y) := by
        funext y
        exact vecDot_neg_left' (F y) (G y)
      rw [hfun, integral_neg]
    rw [← hleft, h0, hright]
  -- completing the square
  have hnonneg : 0 ≤ ∫ y in V, vecDot (F y + G y) (F y + G y) :=
    setIntegral_nonneg hVm fun y _ => vecNormSq_nonneg (F y + G y)
  have hexp : ∫ y in V, vecDot (F y + G y) (F y + G y) =
      (∫ y in V, vecDot (F y) (F y)) + 2 * (∫ y in V, vecDot (F y) (G y)) +
        ∫ y in V, vecDot (G y) (G y) := by
    have hfun : (fun y => vecDot (F y + G y) (F y + G y)) =
        fun y => vecDot (F y) (F y) + 2 * vecDot (F y) (G y) +
          vecDot (G y) (G y) := by
      funext y
      exact vecDot_add_self (F y) (G y)
    have hI2 : IntegrableOn (fun y => 2 * vecDot (F y) (G y)) V volume :=
      hIFG.const_mul 2
    have hI12 : IntegrableOn
        (fun y => vecDot (F y) (F y) + 2 * vecDot (F y) (G y)) V volume :=
      hIFF.add hI2
    rw [hfun, integral_add hI12 hIGG, integral_add hIFF hI2, integral_const_mul]
  have hGG : ∫ y in V, vecNormSq (rho.toH1Function.grad y) =
      ∫ y in V, vecDot (G y) (G y) := rfl
  have hFF : ∫ y in V, vecNormSq (Φ.grad y) = ∫ y in V, vecDot (F y) (F y) := rfl
  rw [hGG, hFF]
  linarith only [hnonneg, hexp, hid]

/-! ## 4. The componentwise form of energy minimality -/

private theorem volumeAverage_vecNormSq_eq_sum {V : Set (Vec d)} {G : Vec d → Vec d}
    (hGi : ∀ i, MemLp (fun y => G y i) 2 (volume.restrict V)) :
    volumeAverage V (fun y => vecNormSq (G y)) =
      ∑ i : Fin d, volumeAverage V (fun y => G y i ^ 2) := by
  classical
  have hterm : ∀ i : Fin d, IntegrableOn (fun y => G y i ^ 2) V volume := by
    intro i
    have h := (hGi i).integrable_sq
    simpa only [IntegrableOn] using h
  have hfun : (fun y => vecNormSq (G y)) = fun y => ∑ i : Fin d, G y i ^ 2 := by
    funext y
    show vecDot (G y) (G y) = _
    simp only [vecDot, pow_two]
  unfold volumeAverage
  rw [hfun, integral_finsetSum Finset.univ fun i _ => hterm i, Finset.mul_sum]

/-- **The componentwise Dirichlet principle.**

`Σᵢ ‖∂ᵢρ‖_{L²(V)} ≤ √d · Σᵢ ‖∂ᵢΦ‖_{L²(V)}` for the identity-background
corrector `ρ` of the datum `Φ`. -/
theorem sum_normalizedL2On_grad_corrector_le {V : Set (Vec d)}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal)
    (Φ : H1Function V) {rho : H10Function V}
    (hrho : IsZeroTraceDirichletRhsWeakSolution (unitCoeffField d) V rho
      (fun y => -Φ.grad y)) :
    ∑ i : Fin d, normalizedL2On V (fun y => rho.toH1Function.grad y i) ≤
      Real.sqrt (d : ℝ) *
        ∑ i : Fin d, normalizedL2On V (fun y => Φ.grad y i) := by
  classical
  have hFi : ∀ i, MemLp (fun y => Φ.grad y i) 2 (volume.restrict V) :=
    fun i => Φ.gradMemL2 i
  have hGi : ∀ i, MemLp (fun y => rho.toH1Function.grad y i) 2 (volume.restrict V) :=
    fun i => rho.toH1Function.gradMemL2 i
  have hmin := setIntegral_vecNormSq_grad_corrector_le hVm Φ hrho
  have hminAvg : volumeAverage V (fun y => vecNormSq (rho.toH1Function.grad y)) ≤
      volumeAverage V (fun y => vecNormSq (Φ.grad y)) := by
    unfold volumeAverage
    have hc : (0 : ℝ) ≤ ((volume V).toReal)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hmin hc
  have hGsum := volumeAverage_vecNormSq_eq_sum (V := V) hGi
  have hFsum := volumeAverage_vecNormSq_eq_sum (V := V) hFi
  have hGnn : ∀ i : Fin d, 0 ≤ volumeAverage V
      (fun y => rho.toH1Function.grad y i ^ 2) :=
    fun i => volumeAverage_sq_nonneg V _
  have hFnn : ∀ i : Fin d, 0 ≤ volumeAverage V (fun y => Φ.grad y i ^ 2) :=
    fun i => volumeAverage_sq_nonneg V _
  have hstep1 : ∑ i : Fin d,
      normalizedL2On V (fun y => rho.toH1Function.grad y i) ≤
      Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d,
        volumeAverage V (fun y => rho.toH1Function.grad y i ^ 2)) :=
    sum_sqrt_le_sqrt_card_mul_sqrt hGnn
  have hstep2 : Real.sqrt (∑ i : Fin d,
      volumeAverage V (fun y => rho.toH1Function.grad y i ^ 2)) ≤
      Real.sqrt (∑ i : Fin d, volumeAverage V (fun y => Φ.grad y i ^ 2)) := by
    refine Real.sqrt_le_sqrt ?_
    rw [← hGsum, ← hFsum]
    exact hminAvg
  have hstep3 : Real.sqrt (∑ i : Fin d,
      volumeAverage V (fun y => Φ.grad y i ^ 2)) ≤
      ∑ i : Fin d, normalizedL2On V (fun y => Φ.grad y i) :=
    sqrt_sum_le_sum_sqrt hFnn
  have hd : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  calc ∑ i : Fin d, normalizedL2On V (fun y => rho.toH1Function.grad y i)
      ≤ Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d,
          volumeAverage V (fun y => rho.toH1Function.grad y i ^ 2)) := hstep1
    _ ≤ Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d,
          volumeAverage V (fun y => Φ.grad y i ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep2 hd
    _ ≤ Real.sqrt (d : ℝ) *
          ∑ i : Fin d, normalizedL2On V (fun y => Φ.grad y i) :=
        mul_le_mul_of_nonneg_left hstep3 hd

/-! ## 5. The Dirichlet Poincaré on a translated cube -/

private theorem normalizedL2On_translateSet' (c : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) :
    normalizedL2On (translateSet c U) f = normalizedL2On U (fun y => f (y + c)) := by
  unfold normalizedL2On
  rw [Ch01.volumeAverage_translateSet_eq_comp_addRight]

/-- **The Dirichlet Poincaré on a translated origin cube.**

An `H¹₀(translateSet c □_j)` function obeys the un-subtracted `L²` Poincaré at
the cube's own scale, with the coefficient-free constant of
`BoundarySplit`. -/
theorem normalizedL2On_h10_translatedCube_le [NeZero d] (c : Vec d) (j : ℤ)
    (rho : H10Function (translateSet c (openCubeSet (originCube d j)))) :
    normalizedL2On (translateSet c (openCubeSet (originCube d j)))
        rho.toH1Function.toFun ≤
      dirichletCubePoincareConst d * (3 : ℝ) ^ j *
        ∑ i : Fin d,
          normalizedL2On (translateSet c (openCubeSet (originCube d j)))
            (fun y => rho.toH1Function.grad y i) := by
  classical
  set rho' : H10Function (openCubeSet (originCube d j)) :=
    H10Function.untranslate c rho with hrho'
  have hUpos : 0 < volume (openCubeSet (originCube d j)) := by
    have htr : (volume (openCubeSet (originCube d j))).toReal = ((3 : ℝ) ^ j) ^ d :=
      volume_toReal_openCubeSet_originCube d j
    have hpos : (0 : ℝ) < ((3 : ℝ) ^ j) ^ d := by positivity
    by_contra hcon
    push Not at hcon
    have h0 : volume (openCubeSet (originCube d j)) = 0 :=
      le_antisymm hcon zero_le
    rw [h0] at htr
    simp only [ENNReal.toReal_zero] at htr
    exact absurd htr.symm (ne_of_gt hpos)
  have hUtop : volume (openCubeSet (originCube d j)) ≠ ⊤ :=
    volume_openCubeSet_originCube_ne_top d j
  have hmemf : MemLp rho'.toH1Function.toFun 2
      (volume.restrict (openCubeSet (originCube d j))) :=
    rho'.toH1Function.memL2
  have hmemg : ∀ i : Fin d,
      MemLp (fun y => rho'.toH1Function.grad y i) 2
        (volume.restrict (openCubeSet (originCube d j))) :=
    fun i => rho'.toH1Function.gradMemL2 i
  have hP := eLpNorm_normalized_le_dirichletCubePoincare j rho'
  have hlhs : normalizedL2On (openCubeSet (originCube d j)) rho'.toH1Function.toFun =
      (eLpNorm rho'.toH1Function.toFun 2
        (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d j)))).toReal :=
    Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
      hUpos hUtop hmemf
  have hrhs : ∀ i : Fin d,
      normalizedL2On (openCubeSet (originCube d j))
        (fun y => rho'.toH1Function.grad y i) =
      (eLpNorm (fun y => rho'.toH1Function.grad y i) 2
        (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d j)))).toReal :=
    fun i =>
      Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
        hUpos hUtop (hmemg i)
  have hP' : normalizedL2On (openCubeSet (originCube d j)) rho'.toH1Function.toFun ≤
      dirichletCubePoincareConst d * (3 : ℝ) ^ j *
        ∑ i : Fin d, normalizedL2On (openCubeSet (originCube d j))
          (fun y => rho'.toH1Function.grad y i) := by
    rw [hlhs]
    refine hP.trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun i _ => (hrhs i).symm
  have hval : rho'.toH1Function.toFun = fun y => rho.toH1Function.toFun (y + c) := by
    funext y
    rw [hrho', H10Function.untranslate_toH1Function, H1Function.untranslate_toFun]
  have hgradval : ∀ i : Fin d, (fun y => rho'.toH1Function.grad y i) =
      fun y => rho.toH1Function.grad (y + c) i := by
    intro i
    funext y
    rw [hrho', H10Function.untranslate_toH1Function, H1Function.untranslate_grad]
  rw [normalizedL2On_translateSet' c (openCubeSet (originCube d j))
    rho.toH1Function.toFun]
  have hsumeq : ∑ i : Fin d,
      normalizedL2On (translateSet c (openCubeSet (originCube d j)))
        (fun y => rho.toH1Function.grad y i) =
      ∑ i : Fin d, normalizedL2On (openCubeSet (originCube d j))
        (fun y => rho'.toH1Function.grad y i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [normalizedL2On_translateSet' c (openCubeSet (originCube d j))
      (fun y => rho.toH1Function.grad y i), hgradval i]
  rw [hsumeq, ← hval]
  exact hP'

/-! ## 6. The packaged comparator -/

/-- The comparator's coefficient-free constant: `√d` times the Dirichlet
Poincaré constant. -/
def comparatorPoincareConst (d : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) * dirichletCubePoincareConst d

theorem comparatorPoincareConst_nonneg (d : ℕ) : 0 ≤ comparatorPoincareConst d :=
  mul_nonneg (Real.sqrt_nonneg _) (dirichletCubePoincareConst_nonneg d)

/-- **The `Δ`-harmonic comparator on a translated cube, with the
Dirichlet-principle bound.**

For `V = translateSet c □_j ⊆ □_m` and an ambient `h : H¹(□_m)` there are
`w : H¹(V)` and an `H¹₀(V)` corrector `ρ` with `w = h + ρ` pointwise (values
and gradients), `w` weakly `Δ`-harmonic on `V`, and

```text
  ‖h − w‖_{L²(V)} ≤ comparatorPoincareConst d · 3^j · Σᵢ ‖∂ᵢh‖_{L²(V)} .
```
-/
theorem exists_deltaComparator_translatedCube [NeZero d] {m j : ℤ} {c : Vec d}
    (hsub : translateSet c (openCubeSet (originCube d j)) ⊆
      openCubeSet (originCube d m))
    (h : H1Function (openCubeSet (originCube d m))) :
    ∃ (w : H1Function (translateSet c (openCubeSet (originCube d j))))
      (rho : H10Function (translateSet c (openCubeSet (originCube d j)))),
      IsWeaklyHarmonicOn (translateSet c (openCubeSet (originCube d j))) w ∧
      (∀ y, w.toFun y = h.toFun y + rho.toH1Function.toFun y) ∧
      (∀ y, w.grad y = h.grad y + rho.toH1Function.grad y) ∧
      normalizedL2On (translateSet c (openCubeSet (originCube d j)))
          (fun y => h.toFun y - w.toFun y) ≤
        comparatorPoincareConst d * (3 : ℝ) ^ j *
          ∑ i : Fin d,
            normalizedL2On (translateSet c (openCubeSet (originCube d j)))
              (fun y => h.grad y i) := by
  classical
  set V : Set (Vec d) := translateSet c (openCubeSet (originCube d j)) with hVdef
  have hV : IsOpenBoundedConvexDomain V :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d j)).translateSet c
  have hne : V.Nonempty := by
    obtain ⟨y0, hy0⟩ := Ch02.openCubeSet_nonempty (originCube d j)
    exact ⟨y0 + c, y0, hy0, rfl⟩
  have hVm : MeasurableSet V := hV.isOpen.measurableSet
  have hVpos : 0 < (volume V).toReal := by
    have hvol : volume V = volume (openCubeSet (originCube d j)) := by
      rw [hVdef]
      exact volume_translateSet_eq c (openCubeSet (originCube d j))
    rw [hvol, volume_toReal_openCubeSet_originCube d j]
    positivity
  set Φ : H1Function V := h.restrict hV.isOpen hsub with hΦdef
  obtain ⟨rho, hrho⟩ := exists_identityCorrector hV hne Φ
  have hΦval : ∀ y, Φ.toFun y = h.toFun y := fun _ => rfl
  have hΦgrad : ∀ y, Φ.grad y = h.grad y := fun _ => rfl
  refine ⟨Φ + rho.toH1Function, rho, ?_, ?_, ?_, ?_⟩
  · -- weak harmonicity of `Φ + ρ`
    intro φ
    have hgrad : MemVectorL2 V Φ.grad := Φ.grad_memVectorL2
    have hrhomem : MemVectorL2 V rho.toH1Function.grad :=
      rho.toH1Function.grad_memVectorL2
    have hsplit := integral_vecDot_add_left_split (U := V) hgrad hrhomem
      (H := (Φ + rho.toH1Function).grad)
      (fun x => by rw [H1Function.add_grad]) φ
    have hid := hrho φ
    have hcongr : ∫ x in V, vecDot (matVecMul (unitCoeffField d x)
          (rho.toH1Function.grad x)) (φ.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (rho.toH1Function.grad x)
          (φ.toH1Function.grad x) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show vecDot (matVecMul (unitCoeffField d x) (rho.toH1Function.grad x))
            (φ.toH1Function.grad x) =
          vecDot (rho.toH1Function.grad x) (φ.toH1Function.grad x)
        rw [matVecMul_unitCoeffField])
    rw [hcongr] at hid
    have hneg : ∫ x in V, vecDot ((fun y => -Φ.grad y) x)
        (φ.toH1Function.grad x) ∂volume =
        -∫ x in V, vecDot (Φ.grad x) (φ.toH1Function.grad x) ∂volume := by
      have hfun : (fun x => vecDot ((fun y => -Φ.grad y) x)
          (φ.toH1Function.grad x)) =
          fun x => -vecDot (Φ.grad x) (φ.toH1Function.grad x) := by
        funext x
        exact vecDot_neg_left' (Φ.grad x) (φ.toH1Function.grad x)
      rw [hfun, integral_neg]
    rw [hneg] at hid
    rw [hsplit, hid]
    ring
  · intro y
    rw [H1Function.add_toFun]
    exact congrArg (· + rho.toH1Function.toFun y) (hΦval y)
  · intro y
    rw [H1Function.add_grad]
    exact congrArg (· + rho.toH1Function.grad y) (hΦgrad y)
  · -- the Dirichlet-principle bound
    have hdiff : (fun y => h.toFun y - (Φ + rho.toH1Function).toFun y) =
        fun y => -rho.toH1Function.toFun y := by
      funext y
      rw [H1Function.add_toFun]
      have := hΦval y
      linarith only [this]
    rw [hdiff]
    have hnegnorm : normalizedL2On V (fun y => -rho.toH1Function.toFun y) =
        normalizedL2On V rho.toH1Function.toFun := by
      have h1 := normalizedL2On_neg V rho.toH1Function.toFun
      have hfun : (fun y => -rho.toH1Function.toFun y) =
          fun y => -(rho.toH1Function.toFun y) := rfl
      rw [hfun]
      exact h1
    rw [hnegnorm]
    have hpo := normalizedL2On_h10_translatedCube_le c j rho
    have hcomp := sum_normalizedL2On_grad_corrector_le hVm hVpos Φ hrho
    have hgradsum : ∑ i : Fin d,
        normalizedL2On V (fun y => Φ.grad y i) =
        ∑ i : Fin d, normalizedL2On V (fun y => h.grad y i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfun : (fun y => Φ.grad y i) = fun y => h.grad y i := by
        funext y
        rw [hΦgrad y]
      rw [hfun]
    rw [hgradsum] at hcomp
    have hCd0 : (0 : ℝ) ≤ dirichletCubePoincareConst d :=
      dirichletCubePoincareConst_nonneg d
    have h3j : (0 : ℝ) ≤ (3 : ℝ) ^ j := le_of_lt (zpow_pos (by norm_num) j)
    calc normalizedL2On V rho.toH1Function.toFun
        ≤ dirichletCubePoincareConst d * (3 : ℝ) ^ j *
            ∑ i : Fin d,
              normalizedL2On V (fun y => rho.toH1Function.grad y i) := hpo
      _ ≤ dirichletCubePoincareConst d * (3 : ℝ) ^ j *
            (Real.sqrt (d : ℝ) *
              ∑ i : Fin d, normalizedL2On V (fun y => h.grad y i)) :=
          mul_le_mul_of_nonneg_left hcomp (mul_nonneg hCd0 h3j)
      _ = comparatorPoincareConst d * (3 : ℝ) ^ j *
            ∑ i : Fin d, normalizedL2On V (fun y => h.grad y i) := by
          rw [comparatorPoincareConst]
          ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
