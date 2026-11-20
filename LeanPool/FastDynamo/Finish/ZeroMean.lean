/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Finish.RealSolution

/-!
# Zero spatial mean of the magnetic fields of the main theorem

Remark 1.5 of the paper (`rem:scope-intro`): since `K_ε ≠ 0`, every magnetic field constructed
in Theorem 1.2 has zero spatial mean.

`HasZeroMean V` says that the zeroth Fourier coefficient of every component of the product-torus
field `V` vanishes; `productCoeffCLM_zero_zero_eq_integral` identifies that coefficient with the
integral of the component over the torus, so `HasZeroMean` is the vanishing of the spatial mean.

* `hasZeroMean_axialLiftH2` : an axial mode `e^{2πiKx₃} b` with `K ≠ 0` has zero mean;
* `HasZeroMean.realPart` : the real part of a field of zero mean has zero mean;
* `hasZeroMean_realifiedEigenTrajectoryH2` and `hasZeroMean_complexify_realAxialTrajectory`:
  the mode `V^ε = e^{2πiKx₃} b^ε`, its real part `B_in^ε`, and the real solution `B^ε(t)` (as the
  `H²` representative and as the explicit real `L²` curve) have zero mean, for every `K ≠ 0`,
  `λ` and `b`, in particular for those of `MainPhysicalClauses`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- A product-torus field has *zero spatial mean* when the integral of each of its three
components over the torus (Haar probability measure) vanishes. -/
def HasZeroMean (V : ProductC3L2) : Prop :=
  ∀ i : Fin 3, ∫ x, V x i ∂productMeasure = 0

/-- The zeroth Fourier coefficient of a component of a product-torus field is the integral of
that component over the torus (Haar probability measure). -/
theorem productCoeffCLM_zero_zero_eq_integral (V : ProductC3L2) (i : Fin 3) :
    productCoeffCLM 0 0 i V = ∫ x, V x i ∂productMeasure := by
  rw [productCoeffCLM, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  have hmono := scalarAxialLiftL2Fun_ae 0 (transverseMonomialL2 0)
  have htrans := (measurePreserving_fst
    (μ := transverseMeasure) (ν := axialMeasure)).quasiMeasurePreserving.ae_eq_comp
      (transverseMonomialL2_coe_ae 0)
  have hcoord := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL V
  filter_upwards [hmono, htrans, hcoord] with x hm ht hc
  change inner ℂ (((scalarAxialLiftL2Fun 0 (transverseMonomialL2 0) :
      ProductScalarL2) : ProductTorus3 → ℂ) x)
    (((productCoordL2 i V : ProductScalarL2) : ProductTorus3 → ℂ) x) = _
  change (transverseMonomialL2 0 : TransverseTorus → ℂ) x.1 =
    UnitAddTorus.mFourier 0 x.1 at ht
  rw [hm, ht]
  change ((productCoordL2 i V : ProductScalarL2) : ProductTorus3 → ℂ) x = V x i at hc
  simp [RCLike.inner_apply, hc, UnitAddTorus.mFourier_zero]

/-- Zero mean is the vanishing of the zeroth Fourier coefficients. -/
theorem hasZeroMean_iff (V : ProductC3L2) :
    HasZeroMean V ↔ ∀ i : Fin 3, productCoeffCLM 0 0 i V = 0 := by
  simp only [HasZeroMean, productCoeffCLM_zero_zero_eq_integral]

/-- Scalar multiples of a field of zero mean have zero mean. -/
theorem HasZeroMean.smul {V : ProductC3L2} (h : HasZeroMean V) (c : ℂ) :
    HasZeroMean (c • V) := by
  rw [hasZeroMean_iff] at h ⊢
  intro i
  rw [map_smul, h i, smul_zero]

/-- Conjugating a field of zero mean gives a field of zero mean. -/
theorem HasZeroMean.conj {V : ProductC3L2} (h : HasZeroMean V) :
    HasZeroMean (productConjL2 V) := by
  rw [hasZeroMean_iff] at h ⊢
  intro i
  rw [productCoeffCLM_productConjL2, neg_zero, neg_zero, h i, map_zero]

/-- The real part of a field of zero mean has zero mean. -/
theorem HasZeroMean.realPart {V : ProductC3L2} (h : HasZeroMean V) :
    HasZeroMean (productRealPartL2 V) := by
  have hconj := (hasZeroMean_iff _).1 h.conj
  rw [hasZeroMean_iff] at h ⊢
  intro i
  have h2 := h i
  change productCoeffCLM 0 0 i (((1 / 2 : ℝ) : ℂ) • (V + productConjL2 V)) = 0
  rw [map_smul, map_add, h2, hconj i, add_zero, smul_zero]

/-- **Remark 1.5 of the paper, for a single axial mode.**  The mode `e^{2πiKx₃} b` has zero
spatial mean as soon as `K ≠ 0`, whatever the amplitude `b`: its Fourier coefficients are
supported on the axial frequency `K`. -/
theorem hasZeroMean_axialLiftH2 {K : ℤ} (hK : K ≠ 0) (b : TransverseC3H2) :
    HasZeroMean (productH2Embedding (axialLiftH2 K b)) := by
  rw [hasZeroMean_iff]
  intro i
  rw [productCoeffCLM_productH2Embedding_axialLiftH2, ite_eq_right (Ne.symm hK)]

/-- **Remark 1.5 of the paper, for the real solution.**  For `K ≠ 0` and every `λ` and `b`, the
real field `B(t) = Re(e^{tλ} e^{2πiKx₃} b)`, in its `H²` representative
`realifiedEigenTrajectoryH2`, has zero spatial mean at every time `t`; at `t = 0` this is the
real datum `B_in = Re V`.  The `λ`, `K`, `b` of `MainPhysicalClauses` are among them. -/
theorem hasZeroMean_realifiedEigenTrajectoryH2 {K : ℤ} (hK : K ≠ 0) (lam : ℂ)
    (b : TransverseC3H2) (t : ℝ) :
    HasZeroMean
      (productH2Embedding (realifiedEigenTrajectoryH2 lam (axialLiftH2 K b) t)) := by
  rw [productH2Embedding_realifiedEigenTrajectoryH2]
  exact ((hasZeroMean_axialLiftH2 hK b).smul _).realPart

/-- **Remark 1.5 of the paper, for the explicit real curve.**  For `K ≠ 0` and every `λ` and
`b`, the real `L²` curve `realAxialTrajectory K λ b t` of Theorem 1.2, read in `ℂ³` through the
complexification, has zero spatial mean at every time `t`. -/
theorem hasZeroMean_complexify_realAxialTrajectory {K : ℤ} (hK : K ≠ 0) (lam : ℂ)
    (b : TransverseC3H2) (t : ℝ) :
    HasZeroMean
      (complexifyProductR3L2 (realAxialTrajectory K lam (transverseH2Embedding b) t)) := by
  rw [complexify_realAxialTrajectory_eq_realified_embedding]
  exact hasZeroMean_realifiedEigenTrajectoryH2 hK lam b t

/-- **Remark 1.5 of the paper, for the real datum.**  For `K ≠ 0`, the real initial field
`B_in = Re V` of Theorem 1.2 has zero spatial mean. -/
theorem hasZeroMean_complexify_realAxialInitialField {K : ℤ} (hK : K ≠ 0)
    (b : TransverseC3H2) :
    HasZeroMean (complexifyProductR3L2 (realAxialInitialField K (transverseH2Embedding b))) := by
  have h := hasZeroMean_complexify_realAxialTrajectory hK 0 b 0
  rwa [realAxialTrajectory_zero] at h

end

end FastDynamo
