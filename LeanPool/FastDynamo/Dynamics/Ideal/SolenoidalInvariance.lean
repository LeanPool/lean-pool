/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Ideal.GradientOrthogonality
public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedConvergence

/-!
# Invariance of the solenoidal subspace under the ideal Cauchy transport

This module proves step **(S2)** — the Cauchy transport maps `L²_σ(T³)` into itself; step (S1)
is `FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean` — of the solenoidality argument of
`cor:ideal-growth` (the paragraph "The formula preserves the divergence constraint" of its
proof) and packages its
consequence, the ideal induction group acting on `L²_σ(T³)`.

The paper's computation is

```
  ∫_{T³} 𝒯₀(t)B · ∇ψ dx = ∫_{T³} DΦ_t(a) B(a) · ∇ψ(Φ_t a) da
                        = ∫_{T³} B(a) · ∇(ψ ∘ Φ_t)(a) da = 0,
```

and it needs `ψ ∘ Φ_t ∈ H¹`, to which the paper extends the divergence identity "by density".
Here `L²_σ(T³)` is
defined by Fourier coefficients rather than by a differential equation, so the argument is run
in the following shape:

1. **A Fourier criterion for membership** (`mem_literalSolenoidalSubspace_of_integral_eq_zero`).
   Reading `productSolenoidalFunctional` through the dictionary of
   `FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`, a field `C` lies in
   `literalSolenoidalSubspace` as soon as, for every flat frequency `m`,
   `∫_{T³} ∑_{i<3} 2πi mᵢ conj(e_m(x)) C(x)ᵢ dx = 0`.  This is the *converse* of
   `sum_inner_flatTorus3FourierBasis_eq_zero`
   (`FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`), and it is what step 3 must produce.
2. **The chain rule on the lift** (`torusGradient_mFourier_comp_apply`).  For a self-map `Φ` of
   the literal three-torus with a differentiable periodic lift `L`, the torus gradient of
   `e_m ∘ Φ` is `e_m(Φ x) · 2πi · (DΦ(x)ᵀ m)`, computed from the explicit lift
   `literalCharacterLift` of `FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`.
3. **The transport step** (`mem_literalSolenoidalSubspace_of_cauchy_formula`).  If `C` satisfies
   the Cauchy formula `C(Φ a)ᵢ = ∑_j DΦ(a)_{ij} B(a)_j` almost everywhere for a solenoidal `B`
   and a measure-preserving `Φ` as in 2, then the criterion of 1 holds for `C`: the change of
   variables `x = Φ a` turns the integrand into `−∑_j conj(∂_j(e_m ∘ Φ)(a)) B(a)_j`, whose
   integral vanishes by `sum_inner_flatTorus3FourierBasis_eq_zero`
   (`FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`).
4. **The truncation** (`idealTruncatedTransport_mem_literalSolenoidalSubspace` and
   `idealTransport_mem_literalSolenoidalSubspace`).  Step 3 applies verbatim to the truncated
   flow of `FastDynamo/Dynamics/Ideal/TruncatedFlow.lean`, whose lift is `C^∞`; the untruncated
   transport is the `L²` limit of the truncated ones
   (`tendsto_idealTruncatedTransport`) and `literalSolenoidalSubspace` is closed.
5. **The group on the subspace** (`idealGroup`), the corestriction of `idealTransport` supplied
   by 4, with its group law and the two-sided per-datum bounds inherited from
   `FastDynamo/Dynamics/Ideal/CauchyOperator.lean` (the last step of the proof of
   `cor:ideal-growth`).

## Contents

* `fderiv_literalCharacterLift_apply`, `torusGradient_mFourier_comp_apply` — the chain rule.
* `inner_flatTorus3FourierBasis_literalCoordL2`, `integrable_conj_mFourier_mul_literalCoord`,
  `productSolenoidalFunctional_eq_sum_inner`, `productSolenoidalFunctional_eq_sum_inner_snoc`,
  `mem_literalSolenoidalSubspace_of_sum_inner_eq_zero`,
  **`mem_literalSolenoidalSubspace_of_integral_eq_zero`** — the Fourier criterion.
* **`mem_literalSolenoidalSubspace_of_cauchy_formula`** — the transport step, for an arbitrary
  smooth measure-preserving self-map of the literal three-torus.
* `idealTruncatedTransport_mem_literalSolenoidalSubspace`,
  **`idealTransport_mem_literalSolenoidalSubspace`** — (S2) proper.
* **`idealGroup`**, `idealGroup_coe`, `idealGroup_zero`, `idealGroup_add`,
  `norm_idealGroup_apply_le`, `norm_le_mul_norm_idealGroup` — the group on `L²_σ`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## The chain rule for a character composed with a self-map of the torus -/

/-- **The derivative of the lift of a character composed with a map.**  If `L` is differentiable
at `a` with derivative `Da`, then the lift `a ↦ exp (2πi ⟨m, L a⟩)` of `e_m ∘ Φ` has, in the
direction of the `j`-th coordinate axis, the derivative `e_m(L a) · 2πi · ∑_k mₖ (Da)_{kj}`
(the periodic lifts of the proof of `cor:ideal-growth`). -/
theorem fderiv_literalCharacterLift_apply {L : R3 → R3} {Da : R3 →L[ℝ] R3} {a : R3}
    (hLd : HasFDerivAt L Da a) (m : Fin 3 → ℤ) (j : Fin 3) :
    fderiv ℝ (literalCharacterLift m L) a (EuclideanSpace.single j (1 : ℝ)) =
      literalCharacterLift m L a * (2 * Real.pi * Complex.I) *
        ∑ k : Fin 3, (m k : ℂ) * ((Da (EuclideanSpace.single j (1 : ℝ)) k : ℝ) : ℂ) := by
  have hcoord : ∀ k : Fin 3, HasFDerivAt (fun b : R3 ↦ ((L b k : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((EuclideanSpace.proj (𝕜 := ℝ) k).comp Da)) a := by
    intro k
    have h1 := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp a hLd
    exact Complex.ofRealCLM.hasFDerivAt.comp a h1
  have hterm : ∀ k : Fin 3, HasFDerivAt (fun b : R3 ↦ (m k : ℂ) * ((L b k : ℝ) : ℂ))
      ((m k : ℂ) • (Complex.ofRealCLM.comp ((EuclideanSpace.proj (𝕜 := ℝ) k).comp Da))) a :=
    fun k ↦ (hcoord k).const_mul _
  have hsum : HasFDerivAt (fun b : R3 ↦ ∑ k : Fin 3, (m k : ℂ) * ((L b k : ℝ) : ℂ))
      (∑ k : Fin 3,
        (m k : ℂ) • (Complex.ofRealCLM.comp ((EuclideanSpace.proj (𝕜 := ℝ) k).comp Da))) a := by
    have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
      (A := fun k (b : R3) ↦ (m k : ℂ) * ((L b k : ℝ) : ℂ)) fun k _ ↦ hterm k
    have hfun : (∑ k : Fin 3, fun b : R3 ↦ (m k : ℂ) * ((L b k : ℝ) : ℂ)) =
        fun b : R3 ↦ ∑ k : Fin 3, (m k : ℂ) * ((L b k : ℝ) : ℂ) := by
      funext b
      rw [Finset.sum_apply]
    rw [hfun] at hs
    exact hs
  have hlin : HasFDerivAt
      (fun b : R3 ↦ 2 * (Real.pi : ℂ) * Complex.I *
        ∑ k : Fin 3, (m k : ℂ) * ((L b k : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I) • (∑ k : Fin 3,
        (m k : ℂ) • (Complex.ofRealCLM.comp ((EuclideanSpace.proj (𝕜 := ℝ) k).comp Da)))) a :=
    hsum.const_mul _
  have hfd : fderiv ℝ (literalCharacterLift m L) a =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ∑ k : Fin 3, (m k : ℂ) * ((L a k : ℝ) : ℂ)) •
      ((2 * (Real.pi : ℂ) * Complex.I) • (∑ k : Fin 3,
        (m k : ℂ) • (Complex.ofRealCLM.comp ((EuclideanSpace.proj (𝕜 := ℝ) k).comp Da)))) :=
    hlin.cexp.fderiv
  rw [hfd, literalCharacterLift]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul, Complex.ofRealCLM_apply,
    PiLp.proj_apply]
  ring

/-- **The torus gradient of a character composed with a self-map of the literal three-torus.**
If `Φ` has the periodic lift `L` and `D x` is the derivative of `L` at every representative of
`x`, then `∂_j (e_m ∘ Φ) (x) = e_m(Φ x) · 2πi · ∑_k mₖ (D x)_{kj}`.  This is the identity that
turns the orthogonality statement (S1) of `FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`
into a statement about `DΦ`, which is the form the Cauchy formula produces. -/
theorem torusGradient_mFourier_comp_apply {Φ : Torus 3 → Torus 3} {L : R3 → R3}
    {D : Torus 3 → (R3 →L[ℝ] R3)} (hL : IsLiteralTorusLift Φ L)
    (hD : ∀ a : R3, HasFDerivAt L (D (literalTorusPoint a)) a) (m : Fin 3 → ℤ) (x : Torus 3)
    (j : Fin 3) :
    torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) x j =
      UnitAddTorus.mFourier m (Φ x) * (2 * Real.pi * Complex.I) *
        ∑ k : Fin 3, (m k : ℂ) * ((D x (EuclideanSpace.single j (1 : ℝ)) k : ℝ) : ℂ) := by
  obtain ⟨a, rfl⟩ := literalTorusPoint_surjective x
  have hval : literalCharacterLift m L a = UnitAddTorus.mFourier m (Φ (literalTorusPoint a)) :=
    (literalCharacterLift_isLift hL m a).symm
  rw [torusGradient_mFourier_comp_literalTorusPoint hL m a j,
    fderiv_literalCharacterLift_apply (hD a) m j, hval]

/-! ## A Fourier criterion for membership of the literal solenoidal subspace -/

/-- Pairing the `m`-th character with the `i`-th component of a vector field is integration of
that component against the conjugate character. -/
theorem inner_flatTorus3FourierBasis_literalCoordL2 (m : Fin 3 → ℤ) (i : Fin 3)
    (C : LiteralC3L2) :
    inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i C) =
      ∫ x : Torus 3, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * (C : Torus 3 → C3) x i := by
  rw [inner_flatTorus3FourierBasis]
  refine integral_congr_ae ?_
  filter_upwards [literalCoordL2_coe_ae i C] with x hx
  rw [hx]

/-- A component of an `L²` vector field, tested against a character, is integrable: the torus
volume is finite and the character is bounded. -/
theorem integrable_conj_mFourier_mul_literalCoord (m : Fin 3 → ℤ) (i : Fin 3) (C : LiteralC3L2) :
    Integrable (fun x : Torus 3 ↦ (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      (C : Torus 3 → C3) x i) (volume : Measure (Torus 3)) := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (flatTorus3FourierBasis m)
    (literalCoordL2 i C)).congr ?_
  filter_upwards [flatTorus3FourierBasis_coe_ae m, literalCoordL2_coe_ae i C] with x h1 h2
  rw [RCLike.inner_apply', h1, h2]

/-- **The solenoidality functional, read on the literal three-torus.**  This is the identity
behind `sum_inner_flatTorus3FourierBasis_eq_zero`
(`FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`), isolated so that it can also be run
backwards. -/
theorem productSolenoidalFunctional_eq_sum_inner (m : Fin 3 → ℤ) (V : ProductC3L2) :
    productSolenoidalFunctional (fun j : Fin 2 ↦ m j.castSucc) (m (Fin.last 2)) V =
      ∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
        inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i (toLiteralC3L2 V)) := by
  rw [productSolenoidalFunctional_apply]
  simp only [productCoeffCLM_eq_inner_flatTorus3FourierBasis]
  simp [Fin.sum_univ_two, Fin.sum_univ_three]

/-- The same identity, indexed by a transverse frequency and an axial frequency instead of by a
flat frequency. -/
theorem productSolenoidalFunctional_eq_sum_inner_snoc (n : TransverseFrequency) (k : ℤ)
    (V : ProductC3L2) :
    productSolenoidalFunctional n k V =
      ∑ i : Fin 3, 2 * Real.pi * Complex.I * ((Fin.snoc n k : Fin 3 → ℤ) i : ℂ) *
        inner ℂ (flatTorus3FourierBasis (Fin.snoc n k))
          (literalCoordL2 i (toLiteralC3L2 V)) := by
  have hn : (fun j : Fin 2 ↦ (Fin.snoc n k : Fin 3 → ℤ) j.castSucc) = n := by
    funext j
    simp
  have hk : (Fin.snoc n k : Fin 3 → ℤ) (Fin.last 2) = k := Fin.snoc_last ..
  have hgen := productSolenoidalFunctional_eq_sum_inner (Fin.snoc n k) V
  rw [hn, hk] at hgen
  exact hgen

/-- **The Fourier criterion, in inner-product form.**  A field of `L²(T³;ℂ³)` whose components
satisfy the single scalar constraint `∑_{i<3} 2πi mᵢ ⟪e_m, Cᵢ⟫ = 0` at every flat frequency `m`
lies in `literalSolenoidalSubspace`.  This is the converse of
`sum_inner_flatTorus3FourierBasis_eq_zero`
(`FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`). -/
theorem mem_literalSolenoidalSubspace_of_sum_inner_eq_zero {C : LiteralC3L2}
    (h : ∀ m : Fin 3 → ℤ, (∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
      inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i C)) = 0) :
    C ∈ literalSolenoidalSubspace := by
  have hmemV : toLiteralC3L2.symm C ∈ productSolenoidalSubspace := by
    rw [productSolenoidalSubspace, Submodule.mem_iInf]
    intro n
    rw [Submodule.mem_iInf]
    intro k
    change productSolenoidalFunctional n k (toLiteralC3L2.symm C) = 0
    rw [productSolenoidalFunctional_eq_sum_inner_snoc n k, toLiteralC3L2.apply_symm_apply]
    exact h (Fin.snoc n k)
  exact ⟨toLiteralC3L2.symm C, hmemV, by simp⟩

/-- **The Fourier criterion, in integral form.**  This is the shape the change of variables of
(S2) produces: the whole three-term sum sits inside a single integral. -/
theorem mem_literalSolenoidalSubspace_of_integral_eq_zero {C : LiteralC3L2}
    (h : ∀ m : Fin 3 → ℤ, (∫ x : Torus 3, ∑ i : Fin 3,
      2 * Real.pi * Complex.I * (m i : ℂ) *
        ((starRingEnd ℂ) (UnitAddTorus.mFourier m x) * (C : Torus 3 → C3) x i)) = 0) :
    C ∈ literalSolenoidalSubspace := by
  refine mem_literalSolenoidalSubspace_of_sum_inner_eq_zero fun m ↦ ?_
  have hint : ∀ i : Fin 3, Integrable (fun x : Torus 3 ↦
      2 * Real.pi * Complex.I * (m i : ℂ) *
        ((starRingEnd ℂ) (UnitAddTorus.mFourier m x) * (C : Torus 3 → C3) x i))
      (volume : Measure (Torus 3)) :=
    fun i ↦ (integrable_conj_mFourier_mul_literalCoord m i C).const_mul _
  rw [← h m, integral_finsetSum _ fun i _ ↦ hint i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_flatTorus3FourierBasis_literalCoordL2 m i C, integral_const_mul]

/-! ## The transport step -/

/-- **(S2) of the solenoidality argument of `cor:ideal-growth`** (the divergence-constraint
paragraph of its proof), for an arbitrary smooth measure-preserving self-map of the literal
three-torus.

If `Φ` is measure preserving with a `C¹` periodic lift `L` whose derivative is `D`, and if `C` is
obtained from a solenoidal `B` by the Cauchy formula `C(Φ a)ᵢ = ∑_j DΦ(a)_{ij} B(a)_j`, then `C`
is solenoidal.  The proof is the paper's computation: the change of variables `x = Φ a`
turns `∫ ∑_i conj(∂_i e_m)(x) C(x)_i dx` into `∫ ∑_j conj(∂_j (e_m ∘ Φ))(a) B(a)_j da`, which
vanishes by the orthogonality statement (S1) of
`FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`. -/
theorem mem_literalSolenoidalSubspace_of_cauchy_formula {Φ : Torus 3 → Torus 3} {L : R3 → R3}
    {D : Torus 3 → (R3 →L[ℝ] R3)} (hL : IsLiteralTorusLift Φ L) (hLsmooth : ContDiff ℝ 1 L)
    (hD : ∀ a : R3, HasFDerivAt L (D (literalTorusPoint a)) a)
    (hmp : MeasurePreserving Φ (volume : Measure (Torus 3)) volume)
    (hemb : MeasurableEmbedding Φ) {B C : LiteralC3L2} (hB : B ∈ literalSolenoidalSubspace)
    (hcauchy : ∀ᵐ a : Torus 3, ∀ i : Fin 3, (C : Torus 3 → C3) (Φ a) i =
      ∑ j : Fin 3, ((D a (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) *
        (B : Torus 3 → C3) a j) :
    C ∈ literalSolenoidalSubspace := by
  refine mem_literalSolenoidalSubspace_of_integral_eq_zero fun m ↦ ?_
  have hseam : (∫ x : Torus 3, ∑ i : Fin 3,
      (starRingEnd ℂ) (torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) x i) *
        ((B : Torus 3 → C3) x i)) = 0 :=
    inner_gradient_mFourier_comp_eq_zero_of_mem_literalSolenoidalSubspace hB hL hLsmooth m
  have hcov := hmp.integral_comp hemb
    (fun x : Torus 3 ↦ ∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
      ((starRingEnd ℂ) (UnitAddTorus.mFourier m x) * (C : Torus 3 → C3) x i))
  rw [← hcov]
  have hpt : ∀ᵐ a : Torus 3, (∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
      ((starRingEnd ℂ) (UnitAddTorus.mFourier m (Φ a)) * (C : Torus 3 → C3) (Φ a) i)) =
      -∑ j : Fin 3,
        (starRingEnd ℂ) (torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) a j) *
          ((B : Torus 3 → C3) a j) := by
    filter_upwards [hcauchy] with a ha
    have hgrad : ∀ j : Fin 3,
        (starRingEnd ℂ) (torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) a j) =
          -((2 * Real.pi * Complex.I) * (starRingEnd ℂ) (UnitAddTorus.mFourier m (Φ a)) *
            ∑ k : Fin 3, (m k : ℂ) *
              ((D a (EuclideanSpace.single j (1 : ℝ)) k : ℝ) : ℂ)) := by
      intro j
      rw [torusGradient_mFourier_comp_apply hL hD m a j]
      simp only [map_mul, map_sum, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
      ring
    calc (∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
            ((starRingEnd ℂ) (UnitAddTorus.mFourier m (Φ a)) * (C : Torus 3 → C3) (Φ a) i))
        = ∑ i : Fin 3, ∑ j : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
            ((starRingEnd ℂ) (UnitAddTorus.mFourier m (Φ a)) *
              (((D a (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) *
                (B : Torus 3 → C3) a j)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [ha i, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ j : Fin 3, ∑ i : Fin 3, 2 * Real.pi * Complex.I * (m i : ℂ) *
            ((starRingEnd ℂ) (UnitAddTorus.mFourier m (Φ a)) *
              (((D a (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) *
                (B : Torus 3 → C3) a j)) := Finset.sum_comm
      _ = ∑ j : Fin 3, -((starRingEnd ℂ)
            (torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) a j) *
              ((B : Torus 3 → C3) a j)) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hgrad j, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ = -∑ j : Fin 3, (starRingEnd ℂ)
            (torusGradient (fun y : Torus 3 ↦ UnitAddTorus.mFourier m (Φ y)) a j) *
              ((B : Torus 3 → C3) a j) := Finset.sum_neg_distrib _
  rw [integral_congr_ae hpt, integral_neg, hseam, neg_zero]

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- **The truncated transport preserves the solenoidal subspace.**  This is (S2) for the
truncated flow, where the lift is `C^∞` and (S1) applies with no density argument. -/
theorem idealTruncatedTransport_mem_literalSolenoidalSubspace (htau : 0 ≤ tau) (N : ℕ) (t : ℝ)
    {B : LiteralC3L2} (hB : B ∈ literalSolenoidalSubspace) :
    idealTruncatedTransport h P angularSpeed axialSpeed tau N t B ∈
      literalSolenoidalSubspace :=
  mem_literalSolenoidalSubspace_of_cauchy_formula
    (isLiteralTorusLift_literalTruncatedFlow h P angularSpeed axialSpeed tau N t)
    ((contDiff_literalTruncatedFlowLift h P angularSpeed axialSpeed tau N t).of_le (by simp))
    (hasFDerivAt_literalTruncatedFlowLift h P angularSpeed axialSpeed tau N t)
    (measurePreserving_literalTruncatedFlow h P angularSpeed axialSpeed tau N t)
    (measurableEmbedding_literalTruncatedFlow h P angularSpeed axialSpeed tau N t) hB
    (idealTruncatedTransport_cauchy h P angularSpeed axialSpeed tau htau N t B)

/-- **Invariance of `L²_σ(T³)` under the ideal Cauchy transport** (the divergence-constraint
paragraph of the proof of `cor:ideal-growth`).  The truncated transports all preserve the closed
subspace `literalSolenoidalSubspace` and converge to `idealTransport … t B` in `L²`. -/
theorem idealTransport_mem_literalSolenoidalSubspace (htau : 0 ≤ tau) (t : ℝ) {B : LiteralC3L2}
    (hB : B ∈ literalSolenoidalSubspace) :
    idealTransport h P angularSpeed axialSpeed tau t B ∈ literalSolenoidalSubspace :=
  isClosed_literalSolenoidalSubspace.mem_of_tendsto
    (tendsto_idealTruncatedTransport h P angularSpeed axialSpeed tau htau t B)
    (Filter.Eventually.of_forall fun N ↦
      idealTruncatedTransport_mem_literalSolenoidalSubspace h P angularSpeed axialSpeed tau
        htau N t hB)

/-! ## The ideal induction group on the solenoidal subspace -/

/-- **The ideal induction group of `cor:ideal-growth`**, as an operator on `L²_σ(T³)`: the
corestriction of `idealTransport … t` to `literalSolenoidalSubspace`, legitimate by
`idealTransport_mem_literalSolenoidalSubspace`, which the tree proves only under `0 ≤ tau`.
Following the convention of `FastDynamo/Conventions.lean` the definition does not take that
hypothesis as an argument but branches on the invariance itself; `idealGroup_eq_codRestrict`
recovers the corestriction from it, and `idealGroup_coe` is the form every consumer uses. -/
def idealGroup (t : ℝ) :
    literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace :=
  @dite _ (∀ B ∈ literalSolenoidalSubspace,
      idealTransport h P angularSpeed axialSpeed tau t B ∈ literalSolenoidalSubspace)
    (Classical.propDecidable _)
    (fun hinv ↦ ContinuousLinearMap.codRestrict
      ((idealTransport h P angularSpeed axialSpeed tau t).comp
        (Submodule.subtypeL literalSolenoidalSubspace)) literalSolenoidalSubspace
      fun B ↦ hinv (B : LiteralC3L2) B.2)
    fun _ ↦ 0

/-- Whenever the transport preserves the solenoidal subspace, the group is its corestriction. -/
theorem idealGroup_eq_codRestrict {t : ℝ}
    (hinv : ∀ B ∈ literalSolenoidalSubspace,
      idealTransport h P angularSpeed axialSpeed tau t B ∈ literalSolenoidalSubspace) :
    idealGroup h P angularSpeed axialSpeed tau t =
      ContinuousLinearMap.codRestrict
        ((idealTransport h P angularSpeed axialSpeed tau t).comp
          (Submodule.subtypeL literalSolenoidalSubspace)) literalSolenoidalSubspace
        fun B ↦ hinv (B : LiteralC3L2) B.2 :=
  dite_eq_left hinv

/-- The group acts by the ideal transport. -/
theorem idealGroup_coe (htau : 0 ≤ tau) (t : ℝ) (B : literalSolenoidalSubspace) :
    ((idealGroup h P angularSpeed axialSpeed tau t B : literalSolenoidalSubspace) :
        LiteralC3L2) =
      idealTransport h P angularSpeed axialSpeed tau t (B : LiteralC3L2) := by
  rw [idealGroup_eq_codRestrict h P angularSpeed axialSpeed tau
    (fun _ hB ↦ idealTransport_mem_literalSolenoidalSubspace h P angularSpeed axialSpeed tau htau
      t hB)]
  rfl

/-- The group at time zero is the identity of `L²_σ`. -/
theorem idealGroup_zero (htau : 0 ≤ tau) :
    idealGroup h P angularSpeed axialSpeed tau 0 =
      ContinuousLinearMap.id ℂ literalSolenoidalSubspace := by
  refine ContinuousLinearMap.ext fun B ↦ Subtype.ext ?_
  rw [idealGroup_coe h P angularSpeed axialSpeed tau htau, idealTransport_zero]
  rfl

/-- The group law of the ideal induction group on `L²_σ`. -/
theorem idealGroup_add (htau : 0 ≤ tau) (s t : ℝ) :
    idealGroup h P angularSpeed axialSpeed tau (s + t) =
      (idealGroup h P angularSpeed axialSpeed tau s).comp
        (idealGroup h P angularSpeed axialSpeed tau t) := by
  refine ContinuousLinearMap.ext fun B ↦ Subtype.ext ?_
  rw [idealGroup_coe h P angularSpeed axialSpeed tau htau,
    idealTransport_add h P angularSpeed axialSpeed tau htau s t,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← idealGroup_coe h P angularSpeed axialSpeed tau htau t B,
    ← idealGroup_coe h P angularSpeed axialSpeed tau htau s]

/-- **The per-datum upper bound** of `cor:ideal-growth` (proved in the last step of its
proof), on the solenoidal subspace. -/
theorem norm_idealGroup_apply_le (htau : 0 ≤ tau) (t : ℝ) (B : literalSolenoidalSubspace) :
    ‖idealGroup h P angularSpeed axialSpeed tau t B‖ ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau t * ‖B‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe (x := B),
    idealGroup_coe h P angularSpeed axialSpeed tau htau]
  exact norm_idealTransport_apply_le h P angularSpeed axialSpeed tau htau t (B : LiteralC3L2)

/-- **The per-datum lower bound** of `cor:ideal-growth` (proved in the last step of its
proof), on the solenoidal subspace.  The constant may be
read at `t` instead of `-t` through `flowComplexDerivativeBound_neg`. -/
theorem norm_le_mul_norm_idealGroup (htau : 0 ≤ tau) (t : ℝ) (B : literalSolenoidalSubspace) :
    ‖B‖ ≤ flowComplexDerivativeBound h P angularSpeed axialSpeed tau (-t) *
      ‖idealGroup h P angularSpeed axialSpeed tau t B‖ := by
  rw [← Submodule.norm_coe (x := B), ← Submodule.norm_coe,
    idealGroup_coe h P angularSpeed axialSpeed tau htau]
  exact norm_le_mul_norm_idealTransport h P angularSpeed axialSpeed tau htau t (B : LiteralC3L2)

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
