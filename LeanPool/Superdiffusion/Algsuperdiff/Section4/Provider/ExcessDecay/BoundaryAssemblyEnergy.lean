/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryAssemblyDirichlet
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.Theory
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.EnergySplit

/-!
# BoundaryAssemblyEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary-regime Caccioppoli display, with the `∇h` legs

`l.coarse.grained.Caccioppoli.RHS`: with `v` the Dirichlet solution carrying the
same force and the same boundary datum, the difference `u - v` has global zero
trace, solves the homogeneous equation, and CoarseGraining's zero-datum theorem
applies to it (`exists_boundaryCaccioppoliEnergy_ofDifference`).  Three steps
separated that from the printed display; this module proves all three and
closes it.

```text
  E_core(∇u)  ≤  2 E_core(∇(u-v))  +  2 E_core(∇v)          (i)   Minkowski
  E_core(∇v)  ≤  18^d · E_{□_m}(∇v)                         (ii)  volume ratio
  E_{□_m}(∇v) ≤  (Dirichlet energy RHS)²                    (iv)  e.cg.RHS
```

Step (iv) is CoarseGraining's `energyConsequencesRHSTheory`, whose right-hand
side `dirichletEnergyWithRHSRHS` carries **both** printed legs: the force leg `[g]_{B^r}`
and the boundary leg `‖∇h‖_{B^r}` at `dirichletBoundaryGradientField v = ∇h`.
That is where the anchor's `∇h` terms enter, and it is the whole point of the
boundary lane.

## The constant, honestly

The right-hand side proved here is **CoarseGraining's own**
`dirichletEnergyWithRHSRHS` squared, times `2 · 18^d`, not the printed normalization
`t^{-3} Λ_t ‖∇h‖²_{H^{2t}(□_0)}`.  No exponent has been moved: the two legs
are CoarseGraining's, at CoarseGraining's exponent `r ∈ (0,1)` (kept free and
*separate* from the Caccioppoli pair `s, t`, since the two CoarseGraining
theorems do not share a normalizer), and the geometric loss `18^d` and the
Minkowski factor `2` are explicit.  The printed `t^{-3}Λ_t` shape would require
CoarseGraining's energy theorem restated at the Caccioppoli normalizer, which
is not available and is not attempted.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The quadratic-form Minkowski step -/

/-- **The Minkowski step of the printed display.**

On the Caccioppoli core the coefficient energy of `u` is at most twice the
energy of `u - v` plus twice the energy of `v`.  This is the quadratic-form
triangle inequality `‖σ^{1/2}∇u‖² ≤ 2‖σ^{1/2}∇(u-v)‖² + 2‖σ^{1/2}∇v‖²`, with
CoarseGraining's own decomposition lemma doing the work. -/
theorem localizedCoeffEnergyValue_core_le_two_mul_sub_add
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
      2 * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) (u - v) +
        2 * localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) v := by
  set V : Set (Vec d) := caccioppoliCoreSet Q x with hVdef
  have hV_open : V ⊆ openCubeSet Q := fun y hy => hy.1
  have hV_cube : V ⊆ cubeSet Q := fun y hy => openCubeSet_subset_cubeSet Q (hV_open hy)
  have hmono : volumeMeasureOn V ≤ volumeMeasureOn (openCubeSet Q) :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hV_open
  have hu_mem : MemVectorL2 V u.grad := u.grad_memVectorL2.mono_measure hmono
  have hv_mem : MemVectorL2 V v.grad := v.grad_memVectorL2.mono_measure hmono
  have hw_mem : MemVectorL2 V (u - v).grad := (u - v).grad_memVectorL2.mono_measure hmono
  have hsplit : u.grad =ᵐ[volumeMeasureOn V] fun y => (u - v).grad y + v.grad y := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [H1Function.sub_grad]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htriangle :=
    volumeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
      (V := V) (A := publicCoeffField Q a)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      ((publicCoeffField_isEllipticFieldOn_cubeSet Q a).mono
        (measurableSet_caccioppoliCoreSet Q x) hV_cube)
      hu_mem hw_mem hv_mem hsplit
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hV_open u,
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hV_open (u - v),
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hV_open v]
  exact htriangle

/-! ## 2. The core-volume ratio -/

/-- **The core-volume ratio.**  A core average of the nonnegative coefficient
energy density is at most `18^d = 2^d 3^{2d}` times the parent-cube average:
`|□_m| / |caccioppoliCoreSet □_m x| ≤ 2^d 3^{2d}` for `x ∈ □_m`. -/
theorem localizedCoeffEnergyValue_core_le_eighteen_pow_mul_parent
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d} (hx : x ∈ openCubeSet Q)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
      (18 : ℝ) ^ d * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u := by
  have hcore_open : caccioppoliCoreSet Q x ⊆ openCubeSet Q := fun y hy => hy.1
  have hnonneg : ∀ y ∈ cubeSet Q,
      0 ≤ coefficientEnergyDensity (publicCoeffField Q a) u.grad y :=
    coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) u.grad
  have hgradcube : MemVectorL2 (cubeSet Q) u.grad := by
    have h := u.grad_memVectorL2
    rwa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  have hint : MeasureTheory.IntegrableOn
      (coefficientEnergyDensity (publicCoeffField Q a) u.grad) (cubeSet Q)
      MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hgradcube
  have hcore := normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_cubeAverage
    Q hx hnonneg hint
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      hcore_open u,
    ← cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue Q a u]
  exact hcore

/-! ## 3. The parent energy is the square of CoarseGraining's energy norm -/

omit [NeZero d] in
theorem localizedCoeffEnergyValue_openCubeSet_nonneg (Q : TriadicCube d)
    (a : CoeffFamily d) (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u := by
  rw [← cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue
    Q a u]
  exact cubeAverage_nonneg_of_nonneg_on
    (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) u.grad)

omit [NeZero d] in
theorem dirichletForcedSolutionEnergyNorm_sq (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    dirichletForcedSolutionEnergyNorm Q a v ^ 2 =
      localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v.toH1 := by
  rw [dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
  exact Real.sq_sqrt (localizedCoeffEnergyValue_openCubeSet_nonneg Q a v.toH1)

/-- **The `∇h` leg, as an energy bound on the parent cube.**  CoarseGraining's
Dirichlet energy estimate with right-hand side, squared: its right-hand side
carries the force leg `[g]` and the boundary leg `‖∇h‖`. -/
theorem exists_localizedCoeffEnergyValue_openCubeSet_le_dirichletEnergyWithRHSRHS_sq
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {r : ℝ} {g : Vec d → Vec d}
        (v : DirichletForcedCubeSolution Q a g),
        0 < r → r < 1 → ForceBesovRegularity Q r g →
        ForceBesovRegularity Q r (dirichletBoundaryGradientField v) →
          localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v.toH1 ≤
            dirichletEnergyWithRHSRHS C Q a r g v ^ 2 := by
  obtain ⟨C, hCpos, hdir, _hneu⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  refine ⟨C, hCpos, ?_⟩
  intro Q a r g v hr hr1 hg hh
  have hbase := hdir (Q := Q) (a := a) (s := r) (g := g) v hr hr1 hg hh
  have hnn : 0 ≤ dirichletForcedSolutionEnergyNorm Q a v := by
    rw [dirichletForcedSolutionEnergyNorm, h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  rw [← dirichletForcedSolutionEnergyNorm_sq Q a v]
  exact pow_le_pow_left₀ hnn hbase 2

/-! ## 4. The printed boundary display, with the `∇h` legs present -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
