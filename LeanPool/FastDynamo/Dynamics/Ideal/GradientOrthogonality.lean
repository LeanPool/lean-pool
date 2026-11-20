/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.LiteralThreeTorusGradient
public import LeanPool.FastDynamo.Dynamics.ParticleFlow

/-!
# Gradients of test functions annihilate the solenoidal subspace of `L²(T³;ℂ³)`

The formalisation splits the argument of the divergence-constraint paragraph of the proof of
`cor:ideal-growth` ("The formula preserves the divergence constraint") into two steps:
**(S1)** gradients of test functions are orthogonal to `L²_σ(T³)`, and **(S2)** the Cauchy
transport maps `L²_σ(T³)` into itself (`FastDynamo/Dynamics/Ideal/SolenoidalInvariance.lean`).
This module proves (S1): for every `B` in `literalSolenoidalSubspace` and
every test function `w` on the literal three-torus whose canonical periodic lift to `ℝ³` is `C¹`,

```
  ∫_{T³} ∑_{i<3} conj(∂ᵢ w(x)) B(x)ᵢ dx = 0.
```

The paper tests the transported field against `∇ψ` for smooth `ψ`.  In this library
`L²_σ(T³)` is **not** defined by a differential equation: it is
`productSolenoidalSubspace.map toLiteralC3L2` (`FastDynamo/Dynamics/Assembly/MainGrowthRate.lean`)
and `productSolenoidalSubspace` is the intersection of the kernels of the Fourier functionals
`productSolenoidalFunctional n k` (`FastDynamo/Dynamics/Assembly/SolenoidalSubspace.lean`).  So
the orthogonality has to be produced *from* the Fourier definition, in three steps:

1. **Transport of the constraint.**  The isometric transport `toLiteralC3L2` carries the split
   monomial `productMonomialL2 n k` to the three-torus character of frequency `Fin.snoc n k`
   and commutes with taking a vector component, so the vanishing of
   `productSolenoidalFunctional` reads on the literal torus as
   `∑_{i<3} 2πi mᵢ ⟪e_m, Bᵢ⟫ = 0` for every frequency `m : Fin 3 → ℤ`
   (`sum_inner_flatTorus3FourierBasis_eq_zero`).
2. **Integration by parts.**  `⟪e_m, ∂ᵢ w⟫ = 2πi mᵢ ⟪e_m, w⟫`, proved in
   `FastDynamo/Analysis/LiteralThreeTorusGradient.lean`.
3. **Parseval.**  `flatTorus3FourierBasis` is a Hilbert basis, so
   `⟪∂ᵢ w, Bᵢ⟫ = ∑_m conj⟪e_m, ∂ᵢ w⟫ ⟪e_m, Bᵢ⟫`; the `i`-sum is finite, so it may be taken
   inside the `m`-sum, where by 1 and 2 each term is
   `-conj(⟪e_m, w⟫) · ∑_i 2πi mᵢ ⟪e_m, Bᵢ⟫ = 0`.

## Contents

* `literalCoordL2`, the component of a vector field on `Torus 3` as a scalar `L²` class, and its
  compatibility with the transport from the product model.
* `productCoeffCLM_eq_inner_flatTorus3FourierBasis`, the dictionary of step 1.
* `sum_inner_flatTorus3FourierBasis_eq_zero`, the transported solenoidality constraint.
* `sum_inner_torusGradientL2_literalCoordL2_eq_zero`, the Parseval assembly.
* **`inner_gradient_eq_zero_of_mem_literalSolenoidalSubspace`** — (S1), the statement used in
  the truncation step (S2).
* `torusGradient_eq_fderiv_of_lift`, the identity a consumer uses to compute `torusGradient`
  from an explicit smooth lift.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Components of a vector field on the literal three-torus -/

/-- The `i`-th scalar component of a complex vector field on the literal three-torus, as an `L²`
class.  This is the literal-model companion of `productCoordL2`. -/
def literalCoordL2 (i : Fin 3) : LiteralC3L2 →L[ℂ] FlatTorus3ScalarL2 :=
  (EuclideanSpace.proj i).compLpL 2 (volume : Measure (Torus 3))

/-- The component class is represented by the component of a representative. -/
theorem literalCoordL2_coe_ae (i : Fin 3) (B : LiteralC3L2) :
    (literalCoordL2 i B : Torus 3 → ℂ) =ᵐ[(volume : Measure (Torus 3))]
      fun x ↦ (B : Torus 3 → C3) x i :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL B

/-- Taking a component commutes with the isometric transport to the literal three-torus. -/
theorem productScalarL2ToFlat_productCoordL2 (i : Fin 3) (V : ProductC3L2) :
    productScalarL2ToFlat (productCoordL2 i V) = literalCoordL2 i (toLiteralC3L2 V) := by
  apply Lp.ext
  have h1 : (productScalarL2ToFlat (productCoordL2 i V) : Torus 3 → ℂ)
      =ᵐ[(volume : Measure (Torus 3))]
        fun x ↦ (productCoordL2 i V : ProductTorus3 → ℂ) (productToLiteral.symm x) :=
    Lp.coeFn_compMeasurePreserving (productCoordL2 i V)
      (measurePreserving_productToLiteral.symm productToLiteral)
  have h2 : ((productCoordL2 i V : ProductScalarL2) : ProductTorus3 → ℂ)
      =ᵐ[productMeasure] fun y ↦ (V : ProductTorus3 → C3) y i :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL V
  have h3 := (measurePreserving_productToLiteral.symm
    productToLiteral).quasiMeasurePreserving.ae h2
  filter_upwards [h1, h3, literalCoordL2_coe_ae i (toLiteralC3L2 V), toLiteralC3L2_coe_ae V]
    with x hx1 hx3 hx4 hx5
  rw [hx1, hx3, hx4, hx5, productToLiteral_symm_apply]

/-! ## The solenoidality constraint, read on the literal three-torus -/

/-- **Dictionary for the Fourier constraint.**  A product-model Fourier coefficient of a field is
the pairing of the transported field's component with the three-torus character of the
corresponding flat frequency. -/
theorem productCoeffCLM_eq_inner_flatTorus3FourierBasis (i : Fin 3) (m : Fin 3 → ℤ)
    (V : ProductC3L2) :
    productCoeffCLM (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) i V =
      inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i (toLiteralC3L2 V)) := by
  have hsnoc : Fin.snoc (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) = m :=
    Fin.snoc_init_self m
  rw [show productCoeffCLM (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) i V =
      inner ℂ (productMonomialL2 (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)))
        (productCoordL2 i V) from rfl,
    ← productScalarL2ToFlat.inner_map_map, productScalarL2ToFlat_productMonomial,
    productScalarL2ToFlat_productCoordL2, hsnoc]

/-- **The solenoidality constraint on the literal three-torus.**  A field of
`literalSolenoidalSubspace` satisfies, at every flat frequency `m`, the single scalar constraint
`∑_{i<3} 2πi mᵢ ⟪e_m, Bᵢ⟫ = 0`. -/
theorem sum_inner_flatTorus3FourierBasis_eq_zero {B : LiteralC3L2}
    (hB : B ∈ literalSolenoidalSubspace) (m : Fin 3 → ℤ) :
    (∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
      inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i B)) = 0 := by
  obtain ⟨V, hV, hVB⟩ := hB
  have hVB' : toLiteralC3L2 V = B := hVB
  have hfun : productSolenoidalFunctional (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) V = 0 :=
    (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hV _) _
  rw [productSolenoidalFunctional_apply] at hfun
  simp only [productCoeffCLM_eq_inner_flatTorus3FourierBasis, hVB'] at hfun
  rw [← hfun]
  simp [Fin.sum_univ_two, Fin.sum_univ_three]

/-! ## Parseval assembly -/

/-- **Parseval assembly.**  The gradient of a test function with a `C¹` lift is orthogonal to
every field of `literalSolenoidalSubspace`, in the componentwise `L²` pairing. -/
theorem sum_inner_torusGradientL2_literalCoordL2_eq_zero {B : LiteralC3L2}
    (hB : B ∈ literalSolenoidalSubspace) {w : Torus 3 → ℂ}
    (hw : ContDiff ℝ 1 (torusLift w)) :
    (∑ i : Fin 3, inner ℂ (torusGradientL2 hw i) (literalCoordL2 i B)) = 0 := by
  have htot : HasSum (fun m : Fin 3 → ℤ ↦ ∑ i : Fin 3,
      inner ℂ (torusGradientL2 hw i) (flatTorus3FourierBasis m) *
        inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i B))
      (∑ i : Fin 3, inner ℂ (torusGradientL2 hw i) (literalCoordL2 i B)) :=
    hasSum_sum fun i _ ↦ flatTorus3FourierBasis.hasSum_inner_mul_inner _ _
  have hzero : ∀ m : Fin 3 → ℤ, (∑ i : Fin 3,
      inner ℂ (torusGradientL2 hw i) (flatTorus3FourierBasis m) *
        inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i B)) = 0 := by
    intro m
    have hg : ∀ i : Fin 3,
        inner ℂ (torusGradientL2 hw i) (flatTorus3FourierBasis m) =
          -(2 * Real.pi * Complex.I * (m i : ℂ)) *
            (starRingEnd ℂ) (inner ℂ (flatTorus3FourierBasis m)
              (torusTestL2 hw.continuous)) := by
      intro i
      rw [← inner_conj_symm, inner_flatTorus3FourierBasis_torusGradientL2 hw m i, map_mul]
      congr 1
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
      ring
    have hfact : (∑ i : Fin 3,
        inner ℂ (torusGradientL2 hw i) (flatTorus3FourierBasis m) *
          inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i B)) =
        -((starRingEnd ℂ) (inner ℂ (flatTorus3FourierBasis m) (torusTestL2 hw.continuous))) *
          ∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
            inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i B) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hg i]
      ring
    rw [hfact, sum_inner_flatTorus3FourierBasis_eq_zero hB m, mul_zero]
  have hz : HasSum (fun _ : Fin 3 → ℤ ↦ (0 : ℂ))
      (∑ i : Fin 3, inner ℂ (torusGradientL2 hw i) (literalCoordL2 i B)) := by
    simpa only [hzero] using htot
  exact hz.unique hasSum_zero

/-! ## The orthogonality statement (S1) -/

/-- **(S1) of the solenoidality argument of `cor:ideal-growth`** (the divergence-constraint
paragraph of its proof): *the gradient of a smooth test function on the literal three-torus
annihilates `literalSolenoidalSubspace`.*

The test function is presented, as the paper presents maps of the torus in the proof of
`cor:ideal-growth`, by a periodic lift: `hlift` says that `W` is a lift of `w`, and `hW` that
this lift is `C¹`.  The gradient is
`torusGradient` of `FastDynamo/Analysis/LiteralThreeTorusGradient.lean`, computed from
`W` by `torusGradient_eq_fderiv_of_lift`. -/
theorem inner_gradient_eq_zero_of_mem_literalSolenoidalSubspace {B : LiteralC3L2}
    (hB : B ∈ literalSolenoidalSubspace) {w : Torus 3 → ℂ} {W : R3 → ℂ}
    (hlift : ∀ a : R3, w (literalTorusPoint a) = W a) (hW : ContDiff ℝ 1 W) :
    (∫ x : Torus 3, ∑ i : Fin 3,
      (starRingEnd ℂ) (torusGradient w x i) * ((B : Torus 3 → C3) x i)) = 0 := by
  have hw : ContDiff ℝ 1 (torusLift w) := by
    rw [show torusLift w = W from funext hlift]
    exact hW
  have hEach : ∀ i : Fin 3, (∫ x : Torus 3,
      (starRingEnd ℂ) (torusGradient w x i) * ((B : Torus 3 → C3) x i)) =
      inner ℂ (torusGradientL2 hw i) (literalCoordL2 i B) := by
    intro i
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [torusGradientL2_coe_ae hw i, literalCoordL2_coe_ae i B] with x h1 h2
    rw [RCLike.inner_apply', h1, h2]
  have hInt : ∀ i : Fin 3, Integrable
      (fun x : Torus 3 ↦ (starRingEnd ℂ) (torusGradient w x i) * ((B : Torus 3 → C3) x i))
      (volume : Measure (Torus 3)) := by
    intro i
    refine (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (torusGradientL2 hw i)
      (literalCoordL2 i B)).congr ?_
    filter_upwards [torusGradientL2_coe_ae hw i, literalCoordL2_coe_ae i B] with x h1 h2
    rw [RCLike.inner_apply', h1, h2]
  rw [integral_finsetSum _ fun i _ ↦ hInt i]
  simp only [hEach]
  exact sum_inner_torusGradientL2_literalCoordL2_eq_zero hB hw

/-- **How to compute the gradient from a lift.**  If `W` is a periodic lift of `w`, the torus
gradient of `w` at the class of `a` is the directional derivative of `W` at `a`. -/
theorem torusGradient_eq_fderiv_of_lift {w : Torus 3 → ℂ} {W : R3 → ℂ}
    (hlift : ∀ a : R3, w (literalTorusPoint a) = W a) (a : R3) (i : Fin 3) :
    torusGradient w (literalTorusPoint a) i = fderiv ℝ W a (EuclideanSpace.single i 1) := by
  rw [torusGradient_literalTorusPoint, show torusLift w = W from funext hlift]

/-! ## The shape the truncation step consumes: a character composed with a flow map -/

/-- The canonical periodic lift of the character `e_m` composed with a self-map of the literal
three-torus that has the periodic lift `L`:
`a ↦ exp (2πi ⟨m, L a⟩)` (the periodic lifts of the proof of `cor:ideal-growth`). -/
def literalCharacterLift (m : Fin 3 → ℤ) (L : R3 → R3) : R3 → ℂ :=
  fun a ↦ Complex.exp (2 * Real.pi * Complex.I * ∑ j, (m j : ℂ) * ((L a) j : ℂ))

/-- `literalCharacterLift m L` is a lift of `e_m ∘ Φ` when `L` is a lift of `Φ`. -/
theorem literalCharacterLift_isLift {Φ : Torus 3 → Torus 3} {L : R3 → R3}
    (hL : IsLiteralTorusLift Φ L) (m : Fin 3 → ℤ) (a : R3) :
    (fun x : Torus 3 ↦ UnitAddTorus.mFourier m (Φ x)) (literalTorusPoint a) =
      literalCharacterLift m L a := by
  change UnitAddTorus.mFourier m (Φ (literalTorusPoint a)) = _
  rw [hL a, mFourier_literalTorusPoint]
  rfl

/-- The lift of a character composed with a `C¹` map is `C¹`. -/
theorem contDiff_literalCharacterLift {L : R3 → R3} (hL : ContDiff ℝ 1 L) (m : Fin 3 → ℤ) :
    ContDiff ℝ 1 (literalCharacterLift m L) := by
  have hproj : ∀ j : Fin 3, ContDiff ℝ 1 fun a : R3 ↦ ((L a j : ℝ) : ℂ) := fun j ↦
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hL)
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul (ContDiff.sum fun j _ ↦ contDiff_const.mul (hproj j)))

/-- **(S1), specialised to the test functions of the truncation step (S2).**  If `Φ` is a
self-map of the literal three-torus with a `C¹` periodic lift `L`, then for every frequency `m`
the gradient of `e_m ∘ Φ` annihilates `literalSolenoidalSubspace`.  Applied to the truncated
flow `Φ^{(N)}_t` — a finite sum of compactly supported smooth displacements, hence a `C^∞`
diffeomorphism with a `C^∞` lift — this is exactly what the change of variables of (S2)
needs. -/
theorem inner_gradient_mFourier_comp_eq_zero_of_mem_literalSolenoidalSubspace
    {B : LiteralC3L2} (hB : B ∈ literalSolenoidalSubspace) {Φ : Torus 3 → Torus 3} {L : R3 → R3}
    (hL : IsLiteralTorusLift Φ L) (hLsmooth : ContDiff ℝ 1 L) (m : Fin 3 → ℤ) :
    (∫ x : Torus 3, ∑ i : Fin 3,
      (starRingEnd ℂ) (torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) x i) *
        ((B : Torus 3 → C3) x i)) = 0 :=
  inner_gradient_eq_zero_of_mem_literalSolenoidalSubspace hB
    (literalCharacterLift_isLift hL m) (contDiff_literalCharacterLift hLsmooth m)

/-- The chain-rule form of the gradient of `e_m ∘ Φ`, read at a lift: this is the identity that
turns (S1) into a statement about `DΦ` transported through the Cauchy formula. -/
theorem torusGradient_mFourier_comp_literalTorusPoint {Φ : Torus 3 → Torus 3} {L : R3 → R3}
    (hL : IsLiteralTorusLift Φ L) (m : Fin 3 → ℤ) (a : R3) (i : Fin 3) :
    torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) (literalTorusPoint a) i =
      fderiv ℝ (literalCharacterLift m L) a (EuclideanSpace.single i 1) :=
  torusGradient_eq_fderiv_of_lift (literalCharacterLift_isLift hL m) a i

end

end FastDynamo
