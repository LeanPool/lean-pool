/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.WholePlaneLocal

/-!
# Density of the whole-plane weak `H²` graph in `L²`

The whole-plane `H²` model is a closed weak-derivative jet rather than a
weighted coefficient graph.  Its dense core is nevertheless most naturally
constructed on the Fourier side.  We approximate an arbitrary Fourier
coefficient in `L²` by Schwartz coefficients, apply inverse Fourier transform,
and bundle the resulting physical Schwartz function with its first and
ordered second Schwartz derivatives.  These jets satisfy the weak derivative
constraints exactly.

Plancherel synthesis is onto and continuous, while Schwartz functions are
dense in Fourier `L²`.  Hence these Fourier-Schwartz jets have physical values
dense in `L²`, proving dense range of `wholePlaneH2Embedding`.  The result is
generic in the Hilbert-valued codomain.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology FourierTransform LineDeriv SchwartzMap

/-! ## Schwartz weak-`H²` jets -/

/-- A physical Schwartz function bundled with its actual first and ordered
second derivatives as an element of the whole-plane weak `H²` graph. -/
def wholePlaneSchwartzToH2
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (f : SchwartzMap WholePlane F) : WholePlaneH2 F :=
  wholePlaneH2OfWeakDerivatives F
    (f.toLp 2 volume)
    (fun j ↦ (∂_{wholePlaneBasis j} f).toLp 2 volume)
    (fun j k ↦
      (∂_{wholePlaneBasis k} (∂_{wholePlaneBasis j} f)).toLp 2 volume)
    (by
      intro j
      rw [wholePlaneL2ToTempered_apply,
        Lp.toTemperedDistribution_toLp_eq,
        wholePlaneL2ToTempered_apply,
        Lp.toTemperedDistribution_toLp_eq]
      exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
        f (wholePlaneBasis j))
    (by
      intro j k
      rw [wholePlaneL2ToTempered_apply,
        Lp.toTemperedDistribution_toLp_eq,
        wholePlaneL2ToTempered_apply,
        Lp.toTemperedDistribution_toLp_eq]
      exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
        (∂_{wholePlaneBasis j} f) (wholePlaneBasis k))

/-- The physical `L²` field of the weak `H²` jet built from a Schwartz function is the `L²`
class of that function. -/
theorem wholePlaneH2Embedding_schwartzToH2
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (f : SchwartzMap WholePlane F) :
    wholePlaneH2Embedding F (wholePlaneSchwartzToH2 F f) =
      f.toLp 2 volume :=
  rfl

/-! ## Fourier-Schwartz core and density -/

/-- Interpret a Schwartz Fourier coefficient as a physical weak `H²` field
by inverse Fourier transformation. -/
def wholePlaneFourierSchwartzToH2
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (c : SchwartzMap WholePlane F) : WholePlaneH2 F :=
  wholePlaneSchwartzToH2 F (𝓕⁻ c)

/-- The physical value of a Fourier-Schwartz core element is exactly
Plancherel inverse synthesis of the `L²` Fourier coefficient. -/
theorem wholePlaneH2Embedding_fourierSchwartzToH2
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (c : SchwartzMap WholePlane F) :
    wholePlaneH2Embedding F (wholePlaneFourierSchwartzToH2 F c) =
      wholePlaneFourierSynthesis F (c.toLp 2 volume) := by
  rw [wholePlaneFourierSchwartzToH2,
    wholePlaneH2Embedding_schwartzToH2]
  exact (SchwartzMap.toLp_fourierInv_eq c).symm

/-- Inverse transforms of Schwartz Fourier coefficients, bundled with their
exact weak derivatives, have dense physical range in whole-plane `L²`. -/
theorem denseRange_wholePlaneFourierSchwartzH2Core
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    DenseRange (fun c : SchwartzMap WholePlane F ↦
      wholePlaneH2Embedding F (wholePlaneFourierSchwartzToH2 F c)) := by
  have hs : DenseRange
      (SchwartzMap.toLpCLM ℝ F 2 (volume : Measure WholePlane)) :=
    SchwartzMap.denseRange_toLpCLM (F := F) (p := 2)
      ENNReal.ofNat_ne_top
  have hfourier : DenseRange
      ((wholePlaneFourierSynthesis F) ∘
        SchwartzMap.toLpCLM ℝ F 2 (volume : Measure WholePlane)) :=
    (wholePlaneFourierSynthesis F).surjective.denseRange.comp hs
      (wholePlaneFourierSynthesis F).continuous
  have heq : (fun c : SchwartzMap WholePlane F ↦
      wholePlaneH2Embedding F (wholePlaneFourierSchwartzToH2 F c)) =
      ((wholePlaneFourierSynthesis F) ∘
        SchwartzMap.toLpCLM ℝ F 2 (volume : Measure WholePlane)) := by
    funext c
    rw [Function.comp_apply, SchwartzMap.toLpCLM_apply,
      wholePlaneH2Embedding_fourierSchwartzToH2]
  rw [heq]
  exact hfourier

/-- For every complete complex Hilbert-valued field, the physical projection
from the whole-plane weak `H²` graph has dense range in `L²`. -/
theorem denseRange_wholePlaneH2Embedding
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    DenseRange (wholePlaneH2Embedding F) := by
  exact DenseRange.of_comp (denseRange_wholePlaneFourierSchwartzH2Core F)

end

end FastDynamo
