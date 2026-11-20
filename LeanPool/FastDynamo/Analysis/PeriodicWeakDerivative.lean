/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Fourier.PeriodicH2

/-!
# Fourier characterization of periodic weak derivatives

On a torus, a distribution is determined by its Fourier coefficients.  This
module therefore records weak derivatives directly through their coefficient
identity.  In particular, this is a semantic specification, not merely a
symbolic multiplier convention: the derivative and Laplacian are unique in
`L²`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- Scalar `L²` fields on the transverse torus are determined by all Fourier
coefficients. -/
theorem transverseScalarL2_ext_coeff {f g : TransverseScalarL2}
    (h : ∀ n, transverseScalarCoeffCLM n f =
      transverseScalarCoeffCLM n g) :
    f = g :=
  transverseScalarL2_ext_of_coeff h

/-- Vector-valued `L²` fields are determined coordinatewise by all Fourier
coefficients. -/
theorem transverseC3L2_ext_coeff {f g : TransverseC3L2}
    (h : ∀ n i, transverseCoeffCLM n i f =
      transverseCoeffCLM n i g) :
    f = g :=
  transverseVecL2_ext_coeff h

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `df` is the `j`-th periodic weak derivative of `f : TransverseVecL2 ι`,
expressed by the equivalent Fourier-coefficient characterization. -/
def HasTransverseVecFourierDerivative (j : Fin 2)
    (f df : TransverseVecL2 ι) : Prop :=
  ∀ n i, transverseCoeffCLM n i df =
    (2 * Real.pi * Complex.I * (n j : ℂ)) *
      transverseCoeffCLM n i f

/-- The bounded derivative synthesized from a transverse `H²` certificate is the
periodic Fourier weak derivative of its physical field, at any finite fibre. -/
theorem transverseVecDerivFromH2_hasFourierDerivative (j : Fin 2)
    (b : TransverseVecH2 ι) :
    HasTransverseVecFourierDerivative j (transverseH2Embedding b)
      (transverseVecDerivFromH2 ι j b) := by
  intro n i
  exact transverseCoeffCLM_transverseDerivFromH2 j b n i

end

/-- `df` is the `j`-th periodic weak derivative of `f`, expressed by the
equivalent Fourier-coefficient characterization. -/
def HasTransverseFourierDerivative (j : Fin 2)
    (f df : TransverseC3L2) : Prop :=
  HasTransverseVecFourierDerivative j f df

/-- An `L²` Fourier weak derivative is unique. -/
theorem HasTransverseFourierDerivative.unique {j : Fin 2}
    {f df dg : TransverseC3L2}
    (hdf : HasTransverseFourierDerivative j f df)
    (hdg : HasTransverseFourierDerivative j f dg) :
    df = dg := by
  apply transverseC3L2_ext_coeff
  intro n i
  rw [hdf n i, hdg n i]

/-- The bounded derivative synthesized from a transverse `H²` certificate is
the unique periodic Fourier weak derivative of its physical field. -/
theorem transverseDerivFromH2_hasFourierDerivative
    (j : Fin 2) (b : TransverseC3H2) :
    HasTransverseFourierDerivative j (transverseH2Embedding b)
      (transverseDerivFromH2 j b) :=
  transverseVecDerivFromH2_hasFourierDerivative j b

/-- `lap` is the periodic weak Laplacian of `f`, expressed through its Fourier
coefficients. -/
def HasTransverseFourierLaplacian
    (f lap : TransverseC3L2) : Prop :=
  ∀ n i, transverseCoeffCLM n i lap =
    -(transverseFrequencyEnergy n : ℂ) *
      transverseCoeffCLM n i f

/-- An `L²` Fourier weak Laplacian is unique. -/
theorem HasTransverseFourierLaplacian.unique
    {f lap₁ lap₂ : TransverseC3L2}
    (h₁ : HasTransverseFourierLaplacian f lap₁)
    (h₂ : HasTransverseFourierLaplacian f lap₂) :
    lap₁ = lap₂ := by
  apply transverseC3L2_ext_coeff
  intro n i
  rw [h₁ n i, h₂ n i]

/-- The bounded Laplacian synthesized from a transverse `H²` certificate is
the unique periodic Fourier weak Laplacian of its physical field. -/
theorem transverseLaplacianFromH2_hasFourierLaplacian
    (b : TransverseC3H2) :
    HasTransverseFourierLaplacian (transverseH2Embedding b)
      (transverseLaplacianFromH2 b) := by
  intro n i
  exact transverseCoeffCLM_transverseLaplacianFromH2 b n i

end

end FastDynamo
