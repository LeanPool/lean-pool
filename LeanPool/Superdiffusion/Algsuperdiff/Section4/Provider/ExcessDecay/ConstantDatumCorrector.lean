/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.NegNormToL2
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.L2Bridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryAssemblyEnergy
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincareRHS
public import LeanPool.Superdiffusion.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.PublicRHSScalar

/-!
# ConstantDatumCorrector

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The zero-trace corrector of a cube, at the ellipticity constants it really has

This module prepares the *constant-datum comparison* route of the
anchor's **general** clause in the interior (frontier-empty) regime.

```text
  -∇ · a∇ρ = -∇ · g   in Q ,      ρ ∈ H¹₀(Q) ,
```

and the module records the two bounds the route needs, **with the coarse-grained
ellipticity constants left in place**:

* `exists_correctorParentEnergy_le` — the parent-cube coefficient energy of
  `ρ`, from CoarseGraining's zero-Dirichlet energy estimate: `⨍_Q ∇ρ·a∇ρ ≤ K
  t^{-3} λ_{t,2}^{-1} [g]²_{B^{2t}(Q)}`;
* `exists_correctorParentL2_forceScale` — the parent-cube `L²` value of `ρ`,
  through the negative-norm chain
  (`NegNormToL2.cubeLpNorm_h10_le_negativeBesov_quarter` composed with
  CoarseGraining's coarse Poincaré with right-hand side): `3^{-2 m}
  ‖ρ‖²_{L²(Q)} ≤ K (t^{-3} λ_{t,2}^{-1} [g]_{B^{2t}(Q)})²`.

## Why not CoarseGraining's own parent-`L²` bridge (disclosed)

CoarseGraining performs exactly this composition inside the proof of its coarse
Caccioppoli with right-hand side, but its internal bridge is stated at `t^{-8}
λ_{t,1}^{-1} [g]²` — it spends `λ_{t,1} λ_{t,2}^{-2} ≤ A t^{-2} λ_{t,1}^{-1}`,
a *deterministic* comparison of the two lower-ellipticity constants which costs
a factor `t^{-2}`.  The two theorems below therefore re-run CoarseGraining's
composition from its public parts and stop *before* the ellipticity comparison,
leaving `λ_{t,2}^{-1}` visible for the caller to discharge from the good
event.

Nothing here is a new analytic input: every step is a public CoarseGraining
theorem or the proved `NegNormToL2`/`L2Bridge` bridge.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; `e.energy.bound.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant datum -/

/-- The constant function as an `H¹` function of a cube. -/
def constantDatumH1 (Q : TriadicCube d) (c : ℝ) :
    H1Function (Ch02.cubeDomain Q : Set (Vec d)) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (by
      rw [Ch02.cubeDomain_coe]
      exact isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_const : ContDiff ℝ 1 fun _ : Vec d => c)

theorem constantDatumH1_toFun (Q : TriadicCube d) (c : ℝ) :
    (constantDatumH1 Q c).toFun = fun _ => c := rfl

theorem constantDatumH1_grad (Q : TriadicCube d) (c : ℝ) :
    (constantDatumH1 Q c).grad = fun _ => (0 : Vec d) := by
  funext y
  funext i
  change (fderiv ℝ (fun _ : Vec d => c) y) (basisVec i) = 0
  rw [fderiv_fun_const]
  rfl

/-- The gradient of a constant-shifted `H¹` function. -/
theorem sub_constantDatumH1_grad (Q : TriadicCube d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ) :
    (u - constantDatumH1 Q c).grad = u.grad := by
  rw [H1Function.sub_grad, constantDatumH1_grad]
  funext y
  exact sub_zero (u.grad y)

/-- The values of a constant-shifted `H¹` function. -/
theorem sub_constantDatumH1_toFun (Q : TriadicCube d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ) :
    (u - constantDatumH1 Q c).toFun = fun y => u.toFun y - c := by
  funext y
  rw [H1Function.sub_toFun, constantDatumH1_toFun]

/-! ## 2. The corrector exists at the cube's own coefficient family -/

variable [NeZero d]

/-- **The zero-trace corrector of the cube.**  CoarseGraining's canonical Dirichlet
corrector at the everywhere-elliptic representative of the family. -/
def constantDatumCorrector (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSet Q) g) :
    ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g :=
  zeroTraceDirichletCorrectorDataOfCubeEllipticity Q hg
    (publicCoeffField_isEllipticFieldOn_cubeSet Q a)

/-! ## 3. The parent-cube energy of the corrector -/

/-- Squaring a real power of a positive base. -/
private theorem rpow_sq {x : ℝ} (hx : 0 < x) (a : ℝ) :
    Real.rpow x a ^ (2 : ℕ) = Real.rpow x (2 * a) := by
  have h : Real.rpow x (a + a) = Real.rpow x a * Real.rpow x a := Real.rpow_add hx a a
  have h2 : (2 : ℝ) * a = a + a := by ring
  rw [h2, h, pow_two]

/-- **The corrector's parent energy, at CoarseGraining's zero-Dirichlet force
scale.**

`⨍_Q ∇ρ · a ∇ρ ≤ K t^{-3} λ_{t,2}^{-1} [g]²_{B^{2t}(Q)}`.  This is
CoarseGraining's `zeroDirichletEnergyWithRHSRHS`, squared; no ellipticity comparison
is made. -/
theorem exists_correctorParentEnergy_le (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ} {g : Vec d → Vec d}
        (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
          localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q)
              (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a)
                rho).toH1Function ≤
            K * (Real.rpow t (-3 : ℝ) *
              Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ (2 : ℕ)) := by
  obtain ⟨Cp, hCp, _hgrad, henergy⟩ := (coarsePoincareRHSTheory (d := d)).exists_constant
  refine ⟨Cp ^ (2 : ℕ), by positivity, ?_⟩
  intro Q a t g rho ht ht2 hg
  have hbound := henergy
    (boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution (Q := Q) (a := a) rho)
    ht ht2 hg
  have hE : localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q)
      (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) rho).toH1Function =
      zeroTraceForcedSolutionEnergyNorm Q a
        (boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution
          (Q := Q) (a := a) rho) ^ (2 : ℕ) := by
    rw [zeroTraceForcedSolutionEnergyNorm, h1EnergyNormOnCube]
    exact (Real.sq_sqrt (localizedCoeffEnergyValue_openCubeSet_nonneg Q a _)).symm
  have hnn : 0 ≤ zeroTraceForcedSolutionEnergyNorm Q a
      (boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution (Q := Q) (a := a) rho) := by
    rw [zeroTraceForcedSolutionEnergyNorm, h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  rw [hE]
  refine le_trans (pow_le_pow_left₀ hnn hbound 2) (le_of_eq ?_)
  rw [zeroDirichletEnergyWithRHSRHS, poincareLowerEllipticityFactor]
  have hlam : 0 < Ch02.lambdaSq Q t (.finite 2) a :=
    Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 2)
  have hsq : Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-(1 / 2 : ℝ)) ^ (2 : ℕ) =
      Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) := by
    rw [rpow_sq hlam]
    congr 1
    norm_num
  have hts : Real.rpow t (-(3 / 2 : ℝ)) ^ (2 : ℕ) = Real.rpow t (-3 : ℝ) := by
    rw [rpow_sq ht]
    congr 1
    norm_num
  calc (Cp * Real.rpow t (-(3 / 2 : ℝ)) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-(1 / 2 : ℝ)) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ (2 : ℕ)
      = Cp ^ (2 : ℕ) * (Real.rpow t (-(3 / 2 : ℝ)) ^ (2 : ℕ) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-(1 / 2 : ℝ)) ^ (2 : ℕ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ (2 : ℕ)) := by
        ring
    _ = Cp ^ (2 : ℕ) * (Real.rpow t (-3 : ℝ) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ (2 : ℕ)) := by
        rw [hsq, hts]

/-! ## 4. The corrector's negative-norm bound, at the same force scale -/

/-- **The corrector's gradient in the negative Besov norm.**

CoarseGraining's coarse Poincaré with right-hand side, applied to the corrector and closed
with its own zero-Dirichlet energy estimate: `[∇ρ]_{B^{-2t}(Q)} ≤ K t^{-3} λ_{t,2}^{-1}
[g]_{B^{2t}(Q)}`.  This is CoarseGraining's own
`coarsePoincareWithRHSGradientRHS_le_corrector_forceScale`, read at the concrete seminorm
carrier. -/
theorem exists_correctorNegativeBesov_le (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ} {g : Vec d → Vec d}
        (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
          cubeBesovNegativeVectorSeminormTwo Q (2 * t)
              (fun x => rho.toH10.toH1Function.grad x) ≤
            K * (Real.rpow t (-3 : ℝ) *
              Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) := by
  obtain ⟨Cp, hCp, hgrad, henergy⟩ := (coarsePoincareRHSTheory (d := d)).exists_constant
  refine ⟨Cp ^ (2 : ℕ) + Cp, by positivity, ?_⟩
  intro Q a t g rho ht ht2 hg
  have h2t : (0 : ℝ) < 2 * t := by linarith only [ht]
  have h2t1 : 2 * t < 1 := by linarith only [ht2]
  have hgradU := hgrad
    (boundaryForcedCaccioppoliCorrectorForcedCubeSolution (Q := Q) (a := a) rho) h2t h2t1 hg
  have henergyU : forcedSolutionEnergyNorm Q a
      (boundaryForcedCaccioppoliCorrectorForcedCubeSolution (Q := Q) (a := a) rho) ≤
      zeroDirichletEnergyWithRHSRHS Cp Q a t g := by
    rw [boundaryForcedCaccioppoliCorrectorForcedCubeSolution_energyNorm_eq]
    exact henergy
      (boundaryForcedCaccioppoliCorrectorZeroTraceForcedCubeSolution (Q := Q) (a := a) rho)
      ht ht2 hg
  have hscale := coarsePoincareWithRHSGradientRHS_le_corrector_forceScale hCp.le
    (Q := Q) (a := a) (t := t) (g := g)
    (boundaryForcedCaccioppoliCorrectorForcedCubeSolution (Q := Q) (a := a) rho)
    ht ht2 hg henergyU
  have heq : scaleNormalizedNegativeBesovVectorNorm Q (2 * t) (.finite 2)
      (forcedSolutionGradientField
        (boundaryForcedCaccioppoliCorrectorForcedCubeSolution (Q := Q) (a := a) rho)) =
      cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (fun x => rho.toH10.toH1Function.grad x) := by
    rw [scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm,
      forcedSolutionGradientField, boundaryForcedCaccioppoliCorrectorForcedCubeSolution_grad]
  rw [← heq]
  exact hgradU.trans hscale

/-! ## 5. The corrector's parent `L²` value, at the same force scale -/

/-- **The parent-`L²` bridge, with the ellipticity constants left in place.**

```text
  3^{-2m} ‖ρ‖²_{L²(Q)} ≤ K ( t^{-3} λ_{t,2}^{-1} [g]_{B^{2t}(Q)} )² .
```

Compare CoarseGraining's internal bridge, which continues to `t^{-8}
λ_{t,1}^{-1}`; see the module docstring. -/
theorem exists_correctorParentL2_forceScale (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ} {g : Vec d → Vec d}
        (rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g),
        0 < t → t ≤ 1 / 4 → ForceBesovRegularity Q (2 * t) g →
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
              normalizedL2SqOnSet (openCubeSet Q)
                (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a)
                  rho).toH1Function.toFun ≤
            K * (Real.rpow t (-3 : ℝ) *
              Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ (2 : ℕ) := by
  obtain ⟨KN, hKN, hN⟩ := exists_correctorNegativeBesov_le d
  refine ⟨(2 * negNormBaseConst d) ^ (2 : ℕ) * KN ^ (2 : ℕ), by
    have hb : 0 < negNormBaseConst d := negNormBaseConst_pos d
    positivity, ?_⟩
  intro Q a t g rho ht ht4 hg
  have ht2 : t < 1 / 2 := by linarith only [ht4]
  have hindex : 4 * t / 2 = 2 * t := by ring
  have hvalue := cubeLpNorm_h10_le_negativeBesov_quarter Q rho.toH10 (s := 4 * t)
    (by linarith only [ht]) (by linarith only [ht4])
  rw [hindex] at hvalue
  -- the parent `L²` square is the square of the cube norm
  have hmem : MemLp (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a)
      rho).toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
    memLp_two_normalizedCubeMeasure_of_h1 Q _
  have hnorm : normalizedL2SqOnSet (openCubeSet Q)
      (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) rho).toH1Function.toFun =
      cubeLpNorm Q 2 (fun x => rho.toH10.toH1Function.toFun x) ^ (2 : ℕ) := by
    rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _ hmem,
      boundaryForcedCaccioppoliCorrectorOpenH10_toFun]
  have hscale2 : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) =
      cubeBesovScaleWeight (1 : ℝ) Q ^ (2 : ℕ) := by
    have h1 : Real.rpow (3 : ℝ) (-(2 : ℝ) * (((Q.scale : ℤ) : ℝ))) =
        cubeBesovScaleWeight (2 : ℝ) Q :=
      publicDualBesovScaleWeight_eq_cubeBesovScaleWeight Q (2 : ℝ)
    have h2 : cubeBesovScaleWeight (1 : ℝ) Q * cubeBesovScaleWeight (1 : ℝ) Q =
        cubeBesovScaleWeight (2 : ℝ) Q := by
      rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
      norm_num
    rw [h1, ← h2, pow_two]
  -- the composition
  have hW : 0 ≤ cubeBesovScaleWeight (1 : ℝ) Q := cubeBesovScaleWeight_nonneg 1 Q
  have hL : 0 ≤ cubeLpNorm Q 2 (fun x => rho.toH10.toH1Function.toFun x) :=
    cubeLpNorm_nonneg Q 2 _
  have hprod : 0 ≤ cubeBesovScaleWeight (1 : ℝ) Q *
      cubeLpNorm Q 2 (fun x => rho.toH10.toH1Function.toFun x) := mul_nonneg hW hL
  have hsq := pow_le_pow_left₀ hprod hvalue 2
  have hNbound := hN rho ht ht2 hg
  have hCdpos : 0 < 2 * negNormBaseConst d := by
    have hb : 0 < negNormBaseConst d := negNormBaseConst_pos d
    linarith only [hb]
  have hCd : 0 ≤ 2 * negNormBaseConst d := hCdpos.le
  have hNnn : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q (2 * t)
      (fun x => rho.toH10.toH1Function.grad x) := by
    have h0 := hprod.trans hvalue
    by_contra hcon
    push Not at hcon
    have hneg := mul_neg_of_pos_of_neg hCdpos hcon
    linarith only [h0, hneg]
  have hchain : (2 * negNormBaseConst d *
      cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (fun x => rho.toH10.toH1Function.grad x)) ^ (2 : ℕ) ≤
      (2 * negNormBaseConst d) ^ (2 : ℕ) *
        (KN * (Real.rpow t (-3 : ℝ) *
          Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g)) ^ (2 : ℕ) := by
    have hstep : 2 * negNormBaseConst d *
        cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => rho.toH10.toH1Function.grad x) ≤
        2 * negNormBaseConst d *
          (KN * (Real.rpow t (-3 : ℝ) *
            Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g)) :=
      mul_le_mul_of_nonneg_left hNbound hCd
    refine le_trans (pow_le_pow_left₀ (mul_nonneg hCd hNnn) hstep 2) (le_of_eq ?_)
    ring
  rw [hscale2, hnorm, ← mul_pow]
  refine le_trans hsq (le_trans hchain (le_of_eq ?_))
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
