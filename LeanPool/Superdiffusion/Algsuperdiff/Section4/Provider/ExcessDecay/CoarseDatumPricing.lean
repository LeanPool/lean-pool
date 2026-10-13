/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReplacementDatumHarmonic
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincareRHS
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.Theory

/-!
# CoarseDatumPricing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The composed `‖v − h‖_{L²}` pricing for a Dirichlet forced solution

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## The gap this module closes

```text
  [B]   ‖v_cc − h‖_{L²(cc)} ,
```

where `v_cc` is CoarseGraining's `DirichletForcedCubeSolution` on the covering
cube with boundary datum `h` and force `g` — the SAME force and the SAME
boundary data as `u`.  This is the author's final same-boundary-data
architecture: nothing is subtracted through the operator anywhere below, and
the zero-trace object is CoarseGraining's own structural `zeroTraceDifference`
field.

The composition is the manuscript's move 3 at `q = 2`, with every ingredient
already:

```text
  3^{-scale} ‖v − h‖_{L²(Q)}
      ≤ 2 C_neg(d) [∇(v − h)]_{B^{-s/2}_{2,2}(Q)}            (negative norm to L²)
      ≤ 2 C_neg(d) √2 ( [∇v]_{B^{-s/2}} + [∇h]_{B^{-s/2}} )   (subadditivity)
      ≤ 2 C_neg(d) √2 ( coarsePoincareWithRHSGradientRHS(s/2)
                          + K_s^{1/2} ‖∇h‖_{L²(Q)} ) .
```

The gradient of the structural zero-trace witness is identified with
`∇v − ∇h` by uniqueness of the weak gradient (§1), which is the only genuinely
new Lean content of the module.

## References

* ABK26, the Section-2 Caccioppoli lemma's move 3; the boundary application.
* CoarseGraining: `Book/Ch03/Definitions.lean` (`DirichletForcedCubeSolution`),
  `Book/Ch03/Theorems/CoarseCaccioppoli/ZeroTraceValue.lean`,
  `Book/Ch03/Theorems/CoarsePoincare.lean`,
  `Book/Ch03/Theorems/Energy/Theory.lean`,
  `Deterministic/CoarsePoincare/SeminormRecurrence.lean`,
  `Deterministic/WeakNormInterfaces/A.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The structural zero-trace difference and its gradient -/

/-- A weak partial derivative only sees the function's a.e. class. -/
private theorem hasWeakPartialDerivOn_congr_fun_ae {U : Set (Vec d)} {i : Fin d}
    {u u' gi : Vec d → ℝ}
    (hu : u =ᵐ[MeasureTheory.volume.restrict U] u')
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn U i u' gi := by
  intro φ hφ hφc hφs
  rw [← h φ hφ hφc hφs]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hu] with x hx
  rw [hx]

/-- **Uniqueness of the weak gradient in a.e. form.**

If two `H¹` witnesses on an open set agree a.e., their gradients agree a.e.
This upgrades CoarseGraining's `gradCoord_ae_eq_of_toFun_eq` (which needs
strict equality of the values) to the a.e. hypothesis actually supplied by
`DirichletForcedCubeSolution.zeroTraceDifference`. -/
theorem grad_ae_eq_of_toFun_ae_eq {U : Set (Vec d)} (hU : IsOpen U)
    (w p : H1Function U)
    (hw : w.toFun =ᵐ[MeasureTheory.volume.restrict U] p.toFun) :
    w.grad =ᵐ[MeasureTheory.volume.restrict U] p.grad := by
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      MeasureTheory.LocallyIntegrableOn (fun x => z.grad x i) U MeasureTheory.volume :=
    fun z i =>
      MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hcoord : ∀ i : Fin d,
      (fun x => w.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
        (fun x => p.grad x i) := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU (hloc w i) (hloc p i) ?_ (p.hasWeakGradient i)
    exact hasWeakPartialDerivOn_congr_fun_ae hw (w.hasWeakGradient i)
  have hall : ∀ᵐ x ∂(MeasureTheory.volume.restrict U), ∀ i : Fin d,
      w.grad x i = p.grad x i := (MeasureTheory.ae_all_iff).2 hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

/-- The value and gradient of the structural zero-trace difference of a
`DirichletForcedCubeSolution`, in a.e. form on the half-open cube. -/
theorem exists_h10_datumDifference (Q : TriadicCube d)
    {a : CoeffFamily d} {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    ∃ w : H10Function (openCubeSet Q),
      w.toH1Function.toFun =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ∧
      w.toH1Function.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        (fun y => v.toH1.grad y - v.boundaryData.grad y) := by
  obtain ⟨w, hw⟩ := v.zeroTraceDifference
  refine ⟨w, ?_, ?_⟩
  · rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hw
  · rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    have hp := grad_ae_eq_of_toFun_ae_eq (isOpen_openCubeSet Q) w.toH1Function
      (v.toH1 - v.boundaryData) (by
        filter_upwards [hw] with x hx
        rw [hx, H1Function.sub_toFun])
    filter_upwards [hp] with x hx
    rw [hx, H1Function.sub_grad]

/-! ## 2. The composed negative-seminorm pricing -/

/-- The dimension-only constant of the composed pricing: the zero-trace value
constant of the negative-norm-to-`L²` step and the subadditivity factor `√2`. -/
def datumPricingConst (d : ℕ) : ℝ :=
  2 * negNormBaseConst d * Real.sqrt 2

theorem datumPricingConst_pos (d : ℕ) : 0 < datumPricingConst d  := by
  have h1 : 0 < negNormBaseConst d := negNormBaseConst_pos d
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [datumPricingConst]
  positivity

/-- **The datum difference against the two negative seminorms.**

`3^{-scale(Q)} ‖v − h‖_{L²(Q)}` is bounded by the negative seminorms of `∇v`
and of `∇h` at the index `s/2`, at the coefficient-free constant
`2 C_neg(d) √2`.  Both legs are coarse carriers; nothing flat acts on the
solution. -/
theorem cubeBesovScaleWeight_mul_cubeLpNorm_datumDifference_le_negativeBesov
    [NeZero d] (Q : TriadicCube d) {a : CoeffFamily d} {s : ℝ} {g : Vec d → Vec d}
    (v : DirichletForcedCubeSolution Q a g) (hs : 0 < s) (hs1 : s ≤ 1) :
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ≤
      datumPricingConst d *
        (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
          cubeBesovNegativeVectorSeminormTwo Q (s / 2)
            (fun x => v.boundaryData.grad x)) := by
  classical
  obtain ⟨w, hwval, hwgrad⟩ := exists_h10_datumDifference Q v
  -- `L²` memberships of the two gradients on the half-open cube
  have hvL2 : MemVectorL2 (cubeSet Q) (fun x => v.toH1.grad x) :=
    memVectorL2_cubeSet_of_openCubeSet v.toH1.grad_memVectorL2
  have hhL2 : MemVectorL2 (cubeSet Q) (fun x => v.boundaryData.grad x) :=
    memVectorL2_cubeSet_of_openCubeSet v.boundaryData.grad_memVectorL2
  have hvLp : MeasureTheory.MemLp (fun x => v.toH1.grad x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hvL2
  have hhLp : MeasureTheory.MemLp (fun x => v.boundaryData.grad x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hhL2
  have hshalf : (0 : ℝ) < s / 2 := by linarith only [hs]
  have hvBdd := cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hshalf
    (fun x => v.toH1.grad x) hvLp
  have hhBdd := cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hshalf
    (fun x => v.boundaryData.grad x) hhLp
  -- step 1: the zero-trace value estimate at `t = s/4`
  have hval := cubeLpNorm_h10_le_negativeBesov_quarter Q w.toCubeSet hs hs1
  rw [H10Function.toCubeSet_toH1Function_toFun,
    H10Function.toCubeSet_toH1Function_grad] at hval
  -- step 2: the left-hand side is the datum difference
  have hLHS : cubeLpNorm Q (2 : ℝ≥0∞) (fun y => w.toH1Function.toFun y) =
      cubeLpNorm Q (2 : ℝ≥0∞)
        (fun y => v.toH1.toFun y - v.boundaryData.toFun y) := by
    unfold cubeLpNorm
    refine congrArg ENNReal.toReal (MeasureTheory.eLpNorm_congr_ae ?_)
    rw [normalizedCubeMeasure, cubeMeasure]
    exact MeasureTheory.Measure.ae_smul_measure hwval _
  -- step 3: the gradient is the difference of the two gradients
  have hgradeq : cubeBesovNegativeVectorSeminormTwo Q (s / 2)
        (fun x => w.toH1Function.grad x) =
      cubeBesovNegativeVectorSeminormTwo Q (s / 2)
        (fun x => v.toH1.grad x - v.boundaryData.grad x) :=
    cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet (s / 2) hwgrad
  -- step 4: subadditivity
  have hsub := cubeBesovNegativeVectorSeminormTwo_sub_le_sqrtTwo_mul_add_of_bddAbove
    Q (s / 2) (fun x => v.toH1.grad x) (fun x => v.boundaryData.grad x)
    hvL2 hhL2 hvBdd hhBdd
  have hCpos : (0 : ℝ) ≤ 2 * negNormBaseConst d := by
    have := negNormBaseConst_pos d
    linarith only [this]
  calc cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - v.boundaryData.toFun y)
      = cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun y => w.toH1Function.toFun y) := by
        rw [hLHS]
    _ ≤ 2 * negNormBaseConst d *
          cubeBesovNegativeVectorSeminormTwo Q (s / 2)
            (fun x => w.toH1Function.grad x) := hval
    _ = 2 * negNormBaseConst d *
          cubeBesovNegativeVectorSeminormTwo Q (s / 2)
            (fun x => v.toH1.grad x - v.boundaryData.grad x) := by
        rw [hgradeq]
    _ ≤ 2 * negNormBaseConst d *
          (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
              cubeBesovNegativeVectorSeminormTwo Q (s / 2)
                (fun x => v.boundaryData.grad x))) :=
        mul_le_mul_of_nonneg_left hsub hCpos
    _ = datumPricingConst d *
          (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
            cubeBesovNegativeVectorSeminormTwo Q (s / 2)
              (fun x => v.boundaryData.grad x)) := by
        rw [datumPricingConst]; ring

/-! ## 3. The two legs: coarse Poincaré on `v`, crude Jensen on `h` -/

/-- The `ForcedCubeSolution` adapter: a Dirichlet forced solution *is* a forced
solution, at the same force, by forgetting the boundary datum. -/
def forcedOfDirichlet {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    ForcedCubeSolution Q a g where
  toH1 := v.toH1
  weakSolution := v.weakSolution

/-- The gradient leg of the solution, in the explicit coarse display at the `r₀ =
s/2` pin.  This is `coarsePoincareRHSTheory` clause (i) read through the public/internal
Besov bridge. -/
theorem exists_negativeBesov_grad_le_coarsePoincare (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) (g : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q a g),
        0 < s → s ≤ 1 → ForceBesovRegularity Q (s / 2) g →
          cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) ≤
            C * Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
                poincareLowerEllipticityFactor Q a (s / 4)
                  (Ch02.MultiscaleExponent.finite 2) *
                dirichletForcedSolutionEnergyNorm Q a v +
              C * Real.rpow (s / 2) (-3 : ℝ) *
                Real.rpow
                  (Ch02.lambdaSq Q (s / 4) (Ch02.MultiscaleExponent.finite 2) a)
                  (-1 : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g := by
  obtain ⟨Cp, hCp, hgrad, _⟩ := (coarsePoincareRHSTheory (d := d)).exists_constant
  refine ⟨Cp, hCp, ?_⟩
  intro Q a s g v hs hs1 hforce
  have hbase := hgrad (Q := Q) (a := a) (s := s / 2) (g := g) (forcedOfDirichlet v)
    (by linarith only [hs]) (by linarith only [hs1]) hforce
  rw [scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm,
    coarsePoincareWithRHSGradientRHS, show s / 2 / 2 = s / 4 by ring] at hbase
  exact hbase

/-! ## 4. The composed pricing -/

/-- **The composed datum pricing.**  The pricing of the structural datum
difference of a Dirichlet forced solution, in its displayed shape:

```text
  3^{-scale(Q)} ‖v − h‖_{L²(Q)}
      ≤ C₁ ( (s/2)^{-3/2} λ_{s/4,2}^{-1/2} · dirichletEnergyWithRHSRHS(C₂, s/2)
             + (s/2)^{-3} λ_{s/4,2}^{-1} [g]_{B^{s/2}_{2,2}(Q)}
             + K_s^{1/2} ‖∇h‖_{L²(Q)} ) .
```

All three legs are coarse (`λ`-weighted) except the last, which acts on the
**datum** `h` alone.  Nothing is subtracted through the operator: the force is
`g` at every station and the zero-trace object is CoarseGraining's own
structural `zeroTraceDifference`. -/
theorem exists_cubeLpNorm_datumDifference_le_dirichletEnergyRHS (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Q : TriadicCube d) (a : CoeffFamily d) (s : ℝ) (g : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q a g),
        0 < s → s ≤ 1 →
        ForceBesovRegularity Q (s / 2) g →
        ForceBesovRegularity Q (s / 2) (dirichletBoundaryGradientField v) →
          cubeBesovScaleWeight (1 : ℝ) Q *
              cubeLpNorm Q (2 : ℝ≥0∞)
                (fun y => v.toH1.toFun y - v.boundaryData.toFun y) ≤
            C₁ *
              (Real.rpow (s / 2) (-(3 / 2 : ℝ)) *
                    poincareLowerEllipticityFactor Q a (s / 4)
                      (Ch02.MultiscaleExponent.finite 2) *
                    dirichletEnergyWithRHSRHS C₂ Q a (s / 2) g v +
                  Real.rpow (s / 2) (-3 : ℝ) *
                    Real.rpow
                      (Ch02.lambdaSq Q (s / 4) (Ch02.MultiscaleExponent.finite 2) a)
                      (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g +
                  negativeToL2Factor s *
                    normalizedEuclideanL2 Q (dirichletBoundaryGradientField v)) := by
  obtain ⟨Cp, hCp, hpoin⟩ := exists_negativeBesov_grad_le_coarsePoincare d
  obtain ⟨Ce, hCe, hdir, _⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  refine ⟨datumPricingConst d * max 1 Cp, Ce, mul_pos (datumPricingConst_pos d)
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 Cp)), hCe, ?_⟩
  intro Q a s g v hs hs1 hforce hforceH
  set K : ℝ := max 1 Cp with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left 1 Cp
  have hKp : Cp ≤ K := le_max_right 1 Cp
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK1]
  -- the two abbreviations for the coarse factors
  set lamHalf : ℝ :=
    poincareLowerEllipticityFactor Q a (s / 4) (Ch02.MultiscaleExponent.finite 2)
    with hlamHalf
  set lamInv : ℝ :=
    Real.rpow (Ch02.lambdaSq Q (s / 4) (Ch02.MultiscaleExponent.finite 2) a) (-1 : ℝ)
    with hlamInv
  set Bg : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 2) g with hBg
  set E : ℝ := dirichletForcedSolutionEnergyNorm Q a v with hE
  set D : ℝ := dirichletEnergyWithRHSRHS Ce Q a (s / 2) g v with hD
  set Hn : ℝ := normalizedEuclideanL2 Q (dirichletBoundaryGradientField v) with hHn
  have hlamHalf0 : 0 ≤ lamHalf := by
    rw [hlamHalf, poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_nonneg Q a (by linarith only [hs]) (by norm_num)) _
  have hlamInv0 : 0 ≤ lamInv := by
    rw [hlamInv]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_nonneg Q a (by linarith only [hs]) (by norm_num)) _
  have hpow32 : (0 : ℝ) ≤ Real.rpow (s / 2) (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg (by linarith only [hs]) _
  have hpow3 : (0 : ℝ) ≤ Real.rpow (s / 2) (-3 : ℝ) :=
    Real.rpow_nonneg (by linarith only [hs]) _
  -- the solution leg, with the energy re-priced by the Dirichlet energy estimate
  have hED : E ≤ D := hdir (Q := Q) (a := a) (s := s / 2) (g := g) v
    (by linarith only [hs]) (by linarith only [hs1]) hforce hforceH
  have hsol : cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) ≤
      K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
        Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by
    have hbase := hpoin Q a s g v hs hs1 hforce
    have hstep1 : Cp * Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E ≤
        K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D) := by
      have h1 : Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E ≤
          Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D :=
        mul_le_mul_of_nonneg_left hED (mul_nonneg hpow32 hlamHalf0)
      have h2 : (0 : ℝ) ≤ Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D := by
        refine le_trans ?_ h1
        refine mul_nonneg (mul_nonneg hpow32 hlamHalf0) ?_
        rw [hE, dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
        exact Real.sqrt_nonneg _
      calc Cp * Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E
          = Cp * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E) := by ring
        _ ≤ K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D) :=
            mul_le_mul hKp h1 (by
              refine mul_nonneg (mul_nonneg hpow32 hlamHalf0) ?_
              rw [hE, dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
              exact Real.sqrt_nonneg _) hK0
    have hstep2 : Cp * Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg ≤
        K * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by
      have hBg0 : 0 ≤ Bg := by
        rw [hBg]
        exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
          hforce
      have h2 : (0 : ℝ) ≤ Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg :=
        mul_nonneg (mul_nonneg hpow3 hlamInv0) hBg0
      calc Cp * Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg
          = Cp * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by ring
        _ ≤ K * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) :=
            mul_le_mul_of_nonneg_right hKp h2
    calc cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x)
        ≤ Cp * Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * E +
            Cp * Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg := hbase
      _ ≤ K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D) +
            K * (Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := add_le_add hstep1 hstep2
      _ = K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
            Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) := by ring
  -- the datum leg, crude Jensen on `∇h` alone
  have hdatum : cubeBesovNegativeVectorSeminormTwo Q (s / 2)
      (fun x => v.boundaryData.grad x) ≤ K * (negativeToL2Factor s * Hn) := by
    have hbase := cubeBesovNegativeVectorSeminormTwo_le_normalizedEuclideanL2
      (Q := Q) (s := s) hs (F := fun x => v.boundaryData.grad x)
      v.boundaryData.grad_memVectorL2
    have h0 : (0 : ℝ) ≤ negativeToL2Factor s * Hn := by
      rw [hHn]
      exact mul_nonneg (negativeToL2Factor_nonneg s)
        (normalizedEuclideanL2_nonneg Q _)
    refine hbase.trans ?_
    rw [hHn, dirichletBoundaryGradientField]
    have : negativeToL2Factor s * normalizedEuclideanL2 Q v.boundaryData.grad ≤
        K * (negativeToL2Factor s * normalizedEuclideanL2 Q v.boundaryData.grad) := by
      nlinarith only [hK1, mul_nonneg (negativeToL2Factor_nonneg s)
        (normalizedEuclideanL2_nonneg Q v.boundaryData.grad)]
    exact this
  -- assemble
  have hmain := cubeBesovScaleWeight_mul_cubeLpNorm_datumDifference_le_negativeBesov
    Q (a := a) (g := g) v hs hs1
  have hC0 : (0 : ℝ) ≤ datumPricingConst d := (datumPricingConst_pos d).le
  refine hmain.trans ?_
  calc datumPricingConst d *
        (cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.toH1.grad x) +
          cubeBesovNegativeVectorSeminormTwo Q (s / 2) (fun x => v.boundaryData.grad x))
      ≤ datumPricingConst d *
          (K * (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
              Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg) +
            K * (negativeToL2Factor s * Hn)) :=
        mul_le_mul_of_nonneg_left (add_le_add hsol hdatum) hC0
    _ = datumPricingConst d * K *
          (Real.rpow (s / 2) (-(3 / 2 : ℝ)) * lamHalf * D +
            Real.rpow (s / 2) (-3 : ℝ) * lamInv * Bg +
            negativeToL2Factor s * Hn) := by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
