/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.ShellIndependence
public import LeanPool.HighContrastHomogenization.Support.Ambient.BlockMatrix
public import Mathlib.Probability.Independence.Integration

/-!
# PrincipalResponseLegsIndep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: sub-step (iii) of the principal response, the independence step

Source display in ABK26:

* `e.lower.bound.principal.one.pre` (label; display), whose derivation is the
  sentence:

  ```
  Therefore, by independence of bfA_{m-h} and G_{-(h)_{z+cu_n}} P_z
  (the latter is a function of k_m - k_{m-h}), ...
  ```

The content of that sentence, and the only content of this module, is that the
expectation of the doubled quadratic form

```
  G_{-(h)_{z+cu_n}} P_z . bfA_{m-h}(z+cu_n) G_{-(h)_{z+cu_n}} P_z
```

may be computed by replacing the *random* matrix `bfA_{m-h}(z+cu_n)` by its
entrywise expectation, the manuscript's `bfAhom_{m-h}(z+cu_n)`, while the load
is held fixed.  In the source's index conventions the matrix is a function of
the shells at or below `m - h` and the load is a function of the fresh shell
`k_m - k_{m-h}`, i.e. of the shells in `(m-h, m]`; these two index blocks are
disjoint, so the cross-shell independence of ABK26 applies.

There is **no Jensen step and no convexity step** here, and none is used below:
the load is not averaged, only the matrix is.

## The two carrier binders, and why neither is a proof step

`integral_blockQuadratic_shellSplit_eq` carries exactly two measurability
binders, and both are the manuscript's own descriptions of its objects rather
than steps of its argument:

* `hWmeas`, that the load is measurable for the fresh block `(n, m]`.  This is
  the parenthetical "the latter is a function of `k_m - k_{m-h}`" and nothing
  more; the fresh shell it names is the repository's
  `Cutoff.finiteShellIncrement`.
* `hBmeas`, that the matrix is measurable for the null completion of the
  lower-shell local field at index `L <= n`.  This is the statement that
  `bfA_{m-h}` is built from the shells at or below `m - h`; the completion, not
  the bare lower field, is used because the genuine infinite lower cutoff is
  only measurable after completion (`Cutoff.lowerShellLocalCompletion`).

The independence itself is **not** a binder: it is obtained from
`Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_Ioc`, hence from
`ShellLawPrefix.independent` alone.

The integrability binders `hB`, `hW` are the manuscript's own standing moment
information: `hW` is the second-moment content of `e.nablaw.in.L.eight`
(label), quoted in the display immediately above, and `hB` is entrywise
integrability of the coarse matrix, which is what makes `bfAhom_{m-h}(z+cu_n)`
a matrix at all.

## Main results

* `integral_blockQuadratic_eq_of_indepFun` -- the factorization at the level of
  the `2d` doubled coordinates, from pairwise independence.
* `integral_blockQuadratic_eq_of_indep` -- the same from independence of two
  sub-sigma-fields.
* `integral_blockQuadratic_shellSplit_eq` -- the shell-block form: past shells
  against a fresh range.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory ProbabilityTheory
open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## The doubled quadratic form over the `2d` doubled coordinates -/

private theorem toFullBlockMat_eq_blockMatEntry (A : BlockMat d)
    (a b : BlockCoord d) :
    toFullBlockMat A a b = blockMatEntry A a b := by
  cases a <;> cases b <;> rfl

/-- The doubled quadratic form as a double sum over the `2d` doubled
coordinates, with the matrix entry factored out in front. -/
private theorem blockQuadratic_eq_sum_entry (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      ∑ a : BlockCoord d, ∑ b : BlockCoord d,
        blockMatEntry A a b * (toFullBlockVec X a * toFullBlockVec X b) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [toFullBlockMat_eq_blockMatEntry]
  ring

private theorem measurable_toFullBlockVec_apply {Omega : Type*}
    {m : MeasurableSpace Omega} {W : Omega → BlockVec d}
    (hW : Measurable[m] W) (a : BlockCoord d) :
    Measurable[m] fun omega => toFullBlockVec (W omega) a := by
  cases a with
  | inl i => exact (measurable_pi_apply i).comp hW.fst
  | inr i => exact (measurable_pi_apply i).comp hW.snd

/-! ## The factorization -/

/-- **The independence factorization, at the doubled coordinates.**  If every
entry of the random doubled matrix `B` is independent of every product of two
coordinates of the random doubled load `W`, then the expected quadratic form is
unchanged when `B` is replaced by its entrywise expectation `Bbar`.

The load is held fixed throughout; only the matrix is averaged. -/
theorem integral_blockQuadratic_eq_of_indepFun {Omega : Type*}
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega} {W : Omega → BlockVec d}
    {B : Omega → BlockMat d} {Bbar : BlockMat d}
    (hindep : ∀ a b : BlockCoord d,
      IndepFun (fun omega => blockMatEntry (B omega) a b)
        (fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b) mu)
    (hB : ∀ a b : BlockCoord d,
      Integrable (fun omega => blockMatEntry (B omega) a b) mu)
    (hW : ∀ a b : BlockCoord d,
      Integrable
        (fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b) mu)
    (hBbar : ∀ a b : BlockCoord d,
      blockMatEntry Bbar a b = ∫ omega, blockMatEntry (B omega) a b ∂mu) :
    ∫ omega, blockVecDot (W omega) (blockMatVecMul (B omega) (W omega)) ∂mu =
      ∫ omega, blockVecDot (W omega) (blockMatVecMul Bbar (W omega)) ∂mu := by
  have hprod : ∀ a b : BlockCoord d,
      Integrable (fun omega => blockMatEntry (B omega) a b *
        (toFullBlockVec (W omega) a * toFullBlockVec (W omega) b)) mu :=
    fun a b => (hindep a b).integrable_mul (hB a b) (hW a b)
  have hprodBar : ∀ a b : BlockCoord d,
      Integrable (fun omega => blockMatEntry Bbar a b *
        (toFullBlockVec (W omega) a * toFullBlockVec (W omega) b)) mu :=
    fun a b => (hW a b).const_mul _
  simp_rw [blockQuadratic_eq_sum_entry]
  rw [integral_finsetSum _
      (fun a _ => integrable_finsetSum _ fun b _ => hprod a b),
    integral_finsetSum _
      (fun a _ => integrable_finsetSum _ fun b _ => hprodBar a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => hprod a b),
    integral_finsetSum _ (fun b _ => hprodBar a b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [(hindep a b).integral_fun_mul_eq_mul_integral (hB a b).1 (hW a b).1,
    integral_const_mul, hBbar a b]

/-- **The independence factorization, at two sub-sigma-fields.**  The same
factorization when the matrix is measurable for one sub-sigma-field, the load
for another, and the two are independent. -/
theorem integral_blockQuadratic_eq_of_indep {Omega : Type*}
    {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {mB mW : MeasurableSpace Omega} (hindep : Indep mB mW mu)
    {W : Omega → BlockVec d} {B : Omega → BlockMat d} {Bbar : BlockMat d}
    (hBmeas : ∀ a b : BlockCoord d,
      Measurable[mB] fun omega => blockMatEntry (B omega) a b)
    (hWmeas : Measurable[mW] W)
    (hB : ∀ a b : BlockCoord d,
      Integrable (fun omega => blockMatEntry (B omega) a b) mu)
    (hW : ∀ a b : BlockCoord d,
      Integrable
        (fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b) mu)
    (hBbar : ∀ a b : BlockCoord d,
      blockMatEntry Bbar a b = ∫ omega, blockMatEntry (B omega) a b ∂mu) :
    ∫ omega, blockVecDot (W omega) (blockMatVecMul (B omega) (W omega)) ∂mu =
      ∫ omega, blockVecDot (W omega) (blockMatVecMul Bbar (W omega)) ∂mu := by
  refine integral_blockQuadratic_eq_of_indepFun ?_ hB hW hBbar
  intro a b
  have hWab : Measurable[mW]
      fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b :=
    (measurable_toFullBlockVec_apply hWmeas a).mul
      (measurable_toFullBlockVec_apply hWmeas b)
  exact (IndepFun_iff_Indep _ _ mu).mpr
    (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hindep (hBmeas a b).comap_le) hWab.comap_le)

/-! ## The shell-block form -/

/-- **The independence factorization at the shell blocks.**  A doubled matrix
measurable for the completed lower-shell field at index `L`, against a doubled
load measurable for a fresh shell range `(n, m]` lying above `L`: the expected
quadratic form is computed at the entrywise expectation of the matrix.

The independence is not assumed: it is
`Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_Ioc`, i.e. ABK26 in
block form. -/
theorem integral_blockQuadratic_shellSplit_eq (M : ABKModel d) {L n m : ℤ}
    (hLn : L ≤ n) (U : Set (Vec d)) {W : Cutoff.ShellSeq d → BlockVec d}
    {B : Cutoff.ShellSeq d → BlockMat d} {Bbar : BlockMat d}
    (hBmeas : ∀ a b : BlockCoord d,
      Measurable[Cutoff.lowerShellLocalCompletion M L U]
        fun omega => blockMatEntry (B omega) a b)
    (hWmeas : Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)] W)
    (hB : ∀ a b : BlockCoord d,
      Integrable (fun omega => blockMatEntry (B omega) a b) M.P.toMeasure)
    (hW : ∀ a b : BlockCoord d,
      Integrable
        (fun omega => toFullBlockVec (W omega) a * toFullBlockVec (W omega) b)
        M.P.toMeasure)
    (hBbar : ∀ a b : BlockCoord d,
      blockMatEntry Bbar a b =
        ∫ omega, blockMatEntry (B omega) a b ∂M.P.toMeasure) :
    ∫ omega, blockVecDot (W omega) (blockMatVecMul (B omega) (W omega))
        ∂M.P.toMeasure =
      ∫ omega, blockVecDot (W omega) (blockMatVecMul Bbar (W omega))
        ∂M.P.toMeasure :=
  integral_blockQuadratic_eq_of_indep
    (Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_Ioc M hLn U)
    hBmeas hWmeas hB hW hBbar

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
