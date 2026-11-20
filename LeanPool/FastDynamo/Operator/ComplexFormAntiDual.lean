/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.ComplexForm
public import LeanPool.FastDynamo.Operator.AssociatedForm

/-!
# Sesquilinear forms as maps into the anti-dual

`Analysis/ComplexForm.lean` carries a continuous sesquilinear form `a : V → V*` both as the
bundled `ComplexForm V` and, through `complexFormOperator`, as the Riesz representative
`A : V → V` of `Analysis/AntiDual.lean`.  This module records the three facts that tie the two
pictures together and that every weak-formulation argument uses:

* `complexToAntiDual_complexFormOperator` — the anti-dual Riesz map sends the representative of
  a form back to the form;
* `coerciveFormAntiDualEquiv` — complex Lax-Milgram read as a continuous linear *equivalence*
  `V ≃L V*`, with `coerciveFormAntiDualEquiv_coe` saying that the equivalence is the form;
* `isInvertible_of_isComplexCoercive` — hence a coercive form is an invertible map `V → V*`.

All three are generic in the complex Hilbert space `V`; the seed's weak form
(`Local/HorizontalWeakForm.lean`, `Local/HorizontalFormOperator.lean`,
`Local/HorizontalFormCompactness.lean`) is their consumer, but nothing here is
specific to it.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The anti-dual Riesz map turns the representative of a form back into the form. -/
theorem complexToAntiDual_complexFormOperator (a : ComplexForm V) (u : V) :
    complexToAntiDual (complexFormOperator a u) = a u := by
  ext v
  rw [complexToAntiDual_apply_apply]
  exact (complexForm_eq_inner a u v).symm

/-- Complex Lax-Milgram read as an isomorphism onto the anti-dual: a coercive form `a` is the
forward map of a continuous linear equivalence `V ≃L V*`. -/
def coerciveFormAntiDualEquiv (a : ComplexForm V) (ha : IsComplexCoercive a) :
    V ≃L[ℂ] ComplexAntiDual V :=
  (IsComplexCoercive.continuousLinearEquiv a ha).trans
    (complexToAntiDual (E := V)).toContinuousLinearEquiv

/-- The Lax-Milgram anti-dual equivalence is the form itself. -/
theorem coerciveFormAntiDualEquiv_coe (a : ComplexForm V) (ha : IsComplexCoercive a) :
    ((coerciveFormAntiDualEquiv a ha : V ≃L[ℂ] ComplexAntiDual V) :
        V →L[ℂ] ComplexAntiDual V) = a :=
  ContinuousLinearMap.ext fun u => complexToAntiDual_complexFormOperator a u

/-- A coercive complex form is an invertible continuous linear map `V → V*`. -/
theorem isInvertible_of_isComplexCoercive (a : ComplexForm V) (ha : IsComplexCoercive a) :
    (a : V →L[ℂ] ComplexAntiDual V).IsInvertible :=
  ⟨coerciveFormAntiDualEquiv a ha, coerciveFormAntiDualEquiv_coe a ha⟩

end

end FastDynamo
