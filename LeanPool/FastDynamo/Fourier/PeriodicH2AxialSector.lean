/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Fourier.PeriodicH2

/-!
# The fixed axial sector of the Fourier-graph periodic `H²`

For a fixed integer axial frequency `K`, the transverse Fourier-graph `H²` domain
`TransverseC3H2` lifts into product `L²` by multiplication with the axial character.  This
module collects that lift together with the Fourier-defined derivative and Laplacian
candidates it carries: the axial derivative is the exact scalar multiplier `2π i K`, the
transverse derivatives are the lifts of the coefficientwise candidates, and the fixed-sector
Laplacian subtracts `(2πK)²` from the transverse Laplacian.  The coordinate decomposition of
the transverse `ℂ^ι`-valued inner product is in this module, since it is used only with
these lifts.

The module is separate from `FastDynamo/Fourier/PeriodicH2.lean` for build weight: over three
hundred modules depend on that one, and nothing in its graph construction, synthesis bridge or
multiplier layer refers to any declaration below.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

variable {ι : Type*} [Fintype ι]

/-! ## The fixed axial sector -/

/-- Axial lift from the transverse `H²` graph domain to physical product `L²`. -/
def axialLiftFromH2 (K : ℤ) : TransverseC3H2 →L[ℂ] ProductC3L2 :=
  (axialLiftL2 K).toContinuousLinearMap.comp transverseH2Embedding

/-- The axial lift from the `H²` graph is the `L²` axial lift applied to the stored physical
field. -/
@[simp] theorem axialLiftFromH2_apply (K : ℤ) (b : TransverseC3H2) :
    axialLiftFromH2 K b = axialLiftL2 K b.1.1 :=
  rfl

/--
The axial lift from the transverse `H²` graph is injective, since both the graph embedding and
the `L²` lift are.
-/
theorem axialLiftFromH2_injective (K : ℤ) :
    Function.Injective (axialLiftFromH2 K) := by
  intro x y hxy
  apply transverseH2Embedding_injective
  apply (axialLiftL2 K).injective
  exact hxy

/-- Lifting an `H²` amplitude into the axial sector preserves the physical `L²` norm. -/
theorem norm_axialLiftFromH2 (K : ℤ) (b : TransverseC3H2) :
    ‖axialLiftFromH2 K b‖ = ‖transverseH2Embedding b‖ := by
  change ‖axialLiftL2 K b.1.1‖ = ‖b.1.1‖
  exact norm_axialLiftL2 K b.1.1

/-- Fourier-defined first axial derivative candidate on a fixed Fourier mode. -/
def axialDerivFromH2 (K : ℤ) : TransverseC3H2 →L[ℂ] ProductC3L2 :=
  (axialMultiplier K) • axialLiftFromH2 K

/--
On the fixed axial sector, one axial derivative acts as multiplication by the exact symbol
`axialMultiplier K = 2π i K`.
-/
theorem axialDerivFromH2_apply (K : ℤ) (b : TransverseC3H2) :
    axialDerivFromH2 K b =
      axialMultiplier K • axialLiftL2 K b.1.1 := by
  rfl

/-- A Fourier-characterized transverse derivative candidate, lifted into the axial sector. -/
def axialTransverseDerivFromH2 (K : ℤ) (j : Fin 2) :
    TransverseC3H2 →L[ℂ] ProductC3L2 :=
  (axialLiftL2 K).toContinuousLinearMap.comp (transverseDerivFromH2 j)

/--
The lifted transverse derivative is the axial lift of the Fourier-defined transverse derivative
of the amplitude.
-/
@[simp] theorem axialTransverseDerivFromH2_apply
    (K : ℤ) (j : Fin 2) (b : TransverseC3H2) :
    axialTransverseDerivFromH2 K j b =
      axialLiftL2 K (transverseDerivFromH2 j b) :=
  rfl

/--
The Fourier-defined Laplacian candidate on the fixed axial sector.  Its
transverse part is synthesized from the stored weighted coefficients, while
the axial part is the exact multiplier `-(2πK)²`.
-/
def fixedAxialLaplacianFromH2 (K : ℤ) :
    TransverseC3H2 →L[ℂ] ProductC3L2 :=
  (axialLiftL2 K).toContinuousLinearMap.comp
    (transverseLaplacianFromH2 -
      (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding)

/--
The fixed-sector Laplacian is the axial lift of the transverse Laplacian of the amplitude minus
`(2πK)²` times the amplitude itself.
-/
theorem fixedAxialLaplacianFromH2_apply
    (K : ℤ) (b : TransverseC3H2) :
    fixedAxialLaplacianFromH2 K b =
      axialLiftL2 K
        (transverseLaplacianFromH2 b -
          (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding b) :=
  rfl

/-- Coordinate decomposition of the transverse `ℂ^ι`-valued `L²` inner product. -/
theorem inner_transverseC3L2_eq_sum_coord
    (f g : TransverseVecL2 ι) :
    inner ℂ f g =
      ∑ i : ι, inner ℂ (transverseCoordL2 i f)
        (transverseCoordL2 i g) := by
  rw [MeasureTheory.L2.inner_def]
  simp_rw [MeasureTheory.L2.inner_def]
  rw [← integral_finsetSum]
  swap
  · intro i hi
    exact L2.integrable_inner (𝕜 := ℂ)
      (transverseCoordL2 i f) (transverseCoordL2 i g)
  apply integral_congr_ae
  have hf : ∀ i : ι,
      ((transverseCoordL2 i f : TransverseScalarL2) :
          TransverseTorus → ℂ) =ᵐ[transverseMeasure]
        fun x ↦ f x i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f
  have hg : ∀ i : ι,
      ((transverseCoordL2 i g : TransverseScalarL2) :
          TransverseTorus → ℂ) =ᵐ[transverseMeasure]
        fun x ↦ g x i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL g
  filter_upwards [ae_all_iff.2 hf, ae_all_iff.2 hg] with x hfx hgx
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfx i, hgx i]
  rfl

end

end FastDynamo
