/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionSum

/-!
# LocalizationFluctuationSelectValue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The fluctuation contribution of the localization split, as a canonical number

ABK26, `l.approximate.recurrence.formula`, Step 2; the split it estimates is
`e.lower.bound.basic.split`, whose third line reads

```
P . bfA_m(cu_{Kc}) P
  <= avsum_z ( P_z . bfA_m(z+cu_n) P_z
               + 2 P_z . fint_{z+cu_n} bfA_m tilde S_z
               + fint_{z+cu_n} tilde S_z . bfA_m tilde S_z ) .
```

## The problem this module solves

`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`
produces the fluctuation field `tilde S_z` by an **existential, one sample at a
time**.  The Step-2 endpoint is an integral over the sample,

```
  int_omega avsum_z ( 2 P_z . fint bfA tilde S_z + fint tilde S_z . bfA tilde S_z ) ,
```

so its integrand must be a *function* of `omega`, not a witness of a per-sample
existential.  Producing one by choosing a witness for each sample is exactly
what the project's no-hypothesis-smuggling rule forbids: the field-slope
minimizer is unique only **almost everywhere**
(`sameAE_of_isDoubledMuMinimizerField`), so `Classical.choose` applied to
`exists_isDoubledMuMinimizerField` is a choice from a class, not from a
singleton, and nothing measurable follows from it.

This module removes the need for any selection at all.  The two fluctuation
summands are not independent data: their sum is a **difference of two
variational minima**, both of which are canonical numbers attached to the
*data* `(U, a, P, bfF_z)` and to nothing else:

```
  2 P_z . fint bfA tilde S_z + fint tilde S_z . bfA tilde S_z
    =  2 mu_field(U, a; P_z + bfF_z)  -  P_z . bfA(U) P_z .
```

The right-hand side mentions no minimizer.  The identity is
`localizationFluctuationValue_eq_of_isDoubledMuMinimizerField` below; it is the
proved exact expansion `LocalizationBasicSplit.two_mul_doubledMuValue_add_eq`
read backwards, together with
`LocalizationSelectionSum.isDoubledMuMinimizerField_add` (`X_z = S_z + tilde
S_z`).

## What is proved

* `doubledMuFieldValueSet`, `doubledMuField` -- the field-slope analogue of
  upstream's `doubledMuValueSet` / `doubledMu`, defined by the *same* recipe
  (`sInf` of the set of admissible energy values).  No choice, no witness.
* `doubledMuField_eq_doubledMuValue_of_isDoubledMuMinimizerField` -- the
  characterization: at any minimizer of the field-slope problem the canonical
  number is the attained energy.  This is what replaces a selection.
* `memVectorL2_potential_of_isDoubledMuAdmissibleField'` and its flux mirror --
  the slope field inherits vector-`L^2` membership from any admissible field
  that has it.  These let the consumer *derive* the caller propositions
  `hFpot`/`hFflux` of the selection layer from the split's own outputs instead
  of assuming them.
* `localizationFluctuationValue` -- the canonical number displayed above.
* `localizationFluctuationValue_eq_of_isDoubledMuMinimizerField` -- it equals
  the two printed fluctuation summands at every realization of the split.

## Why this is not hypothesis smuggling

Nothing below asserts the existence of a minimizer, and nothing below is stated
about a chosen one.  `doubledMuField U a F` is an infimum, defined for every
`(U, a, F)`; every theorem that *identifies* it with an attained energy carries
the minimizer as an explicit hypothesis supplied by the caller --- in practice
by the proved split, which produces it.  In particular the endpoint integrand
built from `localizationFluctuationValue` is a genuine function of the sample,
with a proved characterization at every sample at which the split's witnesses
exist, and the characterization is realization-independent because it is an
identity between numbers and not between fields.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The canonical field-slope minimum -/

/-- **The value set of the field-slope doubled variational problem.**  The
field-slope analogue of upstream's `doubledMuValueSet`, at the affine class `F
+ (L^2_{pot,0} x Lsolo)(U)` of the two `argmin` displays. -/
def doubledMuFieldValueSet (U : Domain d) (a : CoeffOn U) (F : DoubledField d) :
    Set ℝ :=
  {m | ∃ X : DoubledField d, IsDoubledMuAdmissibleField U F X ∧
    m = doubledMuValue U a X}

/-- **The canonical field-slope doubled minimum `mu_field(U, a; F)`.**  Defined
by upstream's own recipe for `doubledMu`: the infimum of the admissible energy
values.  It is a function of `(U, a, F)` alone --- no minimizer is chosen and
none is assumed to exist. -/
def doubledMuField (U : Domain d) (a : CoeffOn U) (F : DoubledField d) : ℝ :=
  sInf (doubledMuFieldValueSet U a F)

/-- A field-slope minimizer realizes the least element of the value set. -/
theorem isLeast_doubledMuFieldValueSet_of_isDoubledMuMinimizerField {U : Domain d}
    {a : CoeffOn U} {F X : DoubledField d} (hX : IsDoubledMuMinimizerField U a F X) :
    IsLeast (doubledMuFieldValueSet U a F) (doubledMuValue U a X) := by
  refine ⟨⟨X, hX.1, rfl⟩, ?_⟩
  rintro m ⟨Y, hY, rfl⟩
  exact hX.2 Y hY

/-- **The characterization that replaces a measurable selection.**  At any
realization of the `argmin` the canonical number `doubledMuField` is the
attained energy.  Since the left-hand side does not mention `X`, the energy is
the same at every realization --- which is exactly the a.e. uniqueness
`sameAE_of_isDoubledMuMinimizerField`, read at the level of numbers, where it
needs no null set. -/
theorem doubledMuField_eq_doubledMuValue_of_isDoubledMuMinimizerField {U : Domain d}
    {a : CoeffOn U} {F X : DoubledField d} (hX : IsDoubledMuMinimizerField U a F X) :
    doubledMuField U a F = doubledMuValue U a X :=
  (isLeast_doubledMuFieldValueSet_of_isDoubledMuMinimizerField hX).csInf_eq

/-! ## The slope field inherits `L²` membership from an admissible field -/

/-- If some admissible field over the slope `F` is vector-`L²`, so is `F`.  This
is what lets a consumer *derive* the caller proposition `hFpot` of the selection
layer from the split's own outputs rather than assume it. -/
theorem memVectorL2_potential_of_isDoubledMuAdmissibleField' {U : Domain d}
    {F X : DoubledField d} (hX : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hadm : IsDoubledMuAdmissibleField U F X) :
    MemVectorL2 (U : Set (Vec d)) F.potential := by
  have hfun : (X.potential - fun x => X.potential x - F.potential x) = F.potential := by
    funext x
    change X.potential x - (X.potential x - F.potential x) = F.potential x
    abel
  exact hfun ▸ hX.sub hadm.1.1

/-- The flux mirror of `memVectorL2_potential_of_isDoubledMuAdmissibleField'`. -/
theorem memVectorL2_flux_of_isDoubledMuAdmissibleField' {U : Domain d}
    {F X : DoubledField d} (hX : MemVectorL2 (U : Set (Vec d)) X.flux)
    (hadm : IsDoubledMuAdmissibleField U F X) :
    MemVectorL2 (U : Set (Vec d)) F.flux := by
  have hfun : (X.flux - fun x => X.flux x - F.flux x) = F.flux := by
    funext x
    change X.flux x - (X.flux x - F.flux x) = F.flux x
    abel
  exact hfun ▸ hX.sub hadm.2.1

/-! ## The fluctuation contribution as a canonical number -/

/-- **The fluctuation contribution of `e.lower.bound.basic.split` at one
localization cube, as a canonical number.**

```
  fluct(U, a; P, F)
    =  2 mu_field(U, a; P + F)  -  P . bfA(U; a) P .
```

At the manuscript's carriers `U = z + cu_n`, `P = P_z` (`e.Pz.def`) and `F =
bfF_z` (`e.Fz.def`), and `fluct` is the sum of the two fluctuation summands,
i.e. exactly what Step 2 has to bound by `cgamma^{10}` after averaging over the
mesh and the sample.  It is defined for every `(U, a, P, F)` and mentions no
minimizer. -/
def localizationFluctuationValue (U : Domain d) (a : CoeffOn U) (P : BlockVec d)
    (F : DoubledField d) : ℝ :=
  2 * doubledMuField U a (constantDoubledField P + F) -
    blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P)

/-- **The characterization of the fluctuation number**.

At any realization `(S, T)` of the split's two `argmin` displays --- `S` the
constant-load minimizer of `e.variational.mu.U.P` at `P` and `T` the
field-slope minimizer over `F`, which the proved split produces together with
the response-field property of `T` --- the canonical number is the printed pair
of fluctuation summands:

```
  fluct(U, a; P, F)
    = 2 P . fint_U bfA T  +  fint_U T . bfA T .
```

The right-hand side is stated in CoarseGraining's half-normalized
`doubledMuValue`, so the manuscript's `fint_U tilde S . bfA tilde S` appears as
`2 * doubledMuValue U a T`, exactly as in
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`.

only on data the split itself supplies: no vector-`L²` proposition about `F` is
a binder, because `hFpot`/`hFflux` are derived from `T`. -/
theorem localizationFluctuationValue_eq_of_isDoubledMuMinimizerField {U : Domain d}
    {a : CoeffOn U} {P : BlockVec d} {F S T : DoubledField d}
    (hS : IsDoubledMuMinimizer U a P S) (hT : IsDoubledMuMinimizerField U a F T)
    (hTresp : IsDoubledResponseField U a T) :
    localizationFluctuationValue U a P F =
      2 * volumeAverage (U : Set (Vec d))
          (fun x => blockVecDot P (blockMatVecMul (blockMatrixField a x) (T.eval x))) +
        2 * doubledMuValue U a T := by
  have hFpot : MemVectorL2 (U : Set (Vec d)) F.potential :=
    memVectorL2_potential_of_isDoubledMuAdmissibleField' hTresp.1.1.1 hT.1
  have hFflux : MemVectorL2 (U : Set (Vec d)) F.flux :=
    memVectorL2_flux_of_isDoubledMuAdmissibleField' hTresp.1.2.1 hT.1
  have hST : IsDoubledMuMinimizerField U a (constantDoubledField P + F) (S + T) :=
    isDoubledMuMinimizerField_add hFpot hFflux hS hT
  have hval : doubledMuField U a (constantDoubledField P + F) =
      doubledMuValue U a (S + T) :=
    doubledMuField_eq_doubledMuValue_of_isDoubledMuMinimizerField hST
  have hexp := two_mul_doubledMuValue_add_eq a P hS hTresp
  change 2 * doubledMuField U a (constantDoubledField P + F) -
      blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) = _
  rw [hval]
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
