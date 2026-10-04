/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.DifferentiatedEquation
public import LeanPool.EllipticPDE.Regularity.LeibnizWkInfty
public import LeanPool.EllipticPDE.Regularity.LowerOrderWkInfty


/-!
# Moving a derivative onto the solution under Guo's coefficient hypothesis

`EllipticPdes.Regularity.principal_move`, `transport_move` and `zeroth_move` move `∂_ℓ` from
the test function onto the solution in the three terms of the equation, each by one application
of the Leibniz rule for a `C¹` weight. Guo, *Partial Differential Equations I and II* (Course
Lecture Notes), Theorem VIII.3.2 (p. 65) asks only for `W^{k,∞}` coefficients, which have no
classical derivative, and this file repeats the three with `HasWeakDerivOn.mul_isWkInfty_left`
in place of `HasWeakDerivOn.mul_contDiff_left`.

The statements differ from their `C¹` counterparts in one place: where those write `partialD ℓ
(fun y => A.a y i j)` for the derivative of a coefficient, these write the chosen representative
`hA.D [ℓ] i j` that `IsWkInftyCoeff` supplies. Everything else is unchanged, so a consumer that
reaches for the commutator by name sees the same shape.

## Main declarations

* `principal_move_wkInfty`: the principal term, for `a ∈ W^{1,∞}`.
* `transport_move_wkInfty`: the transport term, for `b_i ∈ W^{1,∞}`.
* `zeroth_move_wkInfty`: the zeroth-order term, for `c ∈ W^{1,∞}`.
* `commutator_move_wkInfty`: the principal commutator, for `a ∈ W^{2,∞}`.
* `differentiated_weakForm_div_wkInfty`: the four moves assembled, divergence-datum form.
* `differentiated_weakForm_wkInfty`: Evans's equation (34), strong-datum form.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Reading the order-one data off a `W^{k,∞}` bundle -/

namespace IsWkInftyCoeff

variable {A : EllipticCoeff d} {k : ℕ}

/-- The coefficient entry is measurable, read off the order-zero member of the family. -/
theorem measurable_coeff (hA : IsWkInftyCoeff A k) (i j : Fin d) :
    Measurable (fun x => A.a x i j) := by
  have h := hA.D_meas i j [] (by simp)
  rwa [hA.D_nil i j] at h

/-- The order-one member of the family is a weak partial derivative of the coefficient entry. -/
theorem hasWeakPartial_D (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    HasWeakPartial ℓ (fun x => A.a x i j) (hA.D [ℓ] i j) := by
  have h := hA.D_step i j ℓ [] (by simp)
  rwa [hA.D_nil i j] at h

/-- The order-one member of the family is measurable. -/
theorem measurable_D_singleton (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    Measurable (hA.D [ℓ] i j) := hA.D_meas i j [ℓ] (by simp)

/-- The order-one member of the family is essentially bounded by `bound 1`. -/
theorem ae_abs_D_singleton_le (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hA.D [ℓ] i j x| ≤ hA.bound 1 := by
  have h := hA.ess_bdd i j [ℓ] (by simp)
  simpa using h

/-- The order-two member of the family is a weak partial derivative of the order-one member. -/
theorem hasWeakPartial_D_singleton (hA : IsWkInftyCoeff A (k + 2)) (m ℓ i j : Fin d) :
    HasWeakPartial m (hA.D [ℓ] i j) (hA.D [m, ℓ] i j) := hA.D_step i j m [ℓ] (by simp)

/-- The order-two member of the family is measurable. -/
theorem measurable_D_pair (hA : IsWkInftyCoeff A (k + 2)) (m ℓ i j : Fin d) :
    Measurable (hA.D [m, ℓ] i j) := hA.D_meas i j [m, ℓ] (by simp)

/-- The order-two member of the family is essentially bounded by `bound 2`. -/
theorem ae_abs_D_pair_le (hA : IsWkInftyCoeff A (k + 2)) (m ℓ i j : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hA.D [m, ℓ] i j x| ≤ hA.bound 2 := by
  have h := hA.ess_bdd i j [m, ℓ] (by simp)
  simpa using h

end IsWkInftyCoeff

namespace IsWkInfty

variable {f : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ}

/-- The function is measurable, read off the order-zero member of the family. -/
theorem measurable_self (hf : IsWkInfty f k) : Measurable f := by
  have h := hf.D_meas [] (by simp)
  rwa [hf.D_nil] at h

/-- The function is essentially bounded by `bound 0`. -/
theorem ae_abs_le (hf : IsWkInfty f k) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |f x| ≤ hf.bound 0 := by
  have h := hf.ess_bdd [] (by simp)
  rwa [hf.D_nil] at h

/-- The order-one member of the family is a weak partial derivative of the function. -/
theorem hasWeakPartial_D (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    HasWeakPartial ℓ f (hf.D [ℓ]) := by
  have h := hf.D_step ℓ [] (by simp)
  rwa [hf.D_nil] at h

/-- The order-one member of the family is measurable. -/
theorem measurable_D_singleton (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    Measurable (hf.D [ℓ]) := hf.D_meas [ℓ] (by simp)

/-- The order-one member of the family is essentially bounded by `bound 1`. -/
theorem ae_abs_D_singleton_le (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hf.D [ℓ] x| ≤ hf.bound 1 := by
  have h := hf.ess_bdd [ℓ] (by simp)
  simpa using h

end IsWkInfty

/-! ### Three terms -/

/-- **Principal term for a `W^{1,∞}` coefficient.** For every direction pair the weighted first
derivative `a_{ij}·∂ᵢu` has weak `ℓ`-derivative `(∂_ℓ a_{ij})·∂ᵢu + a_{ij}·∂_ℓ∂ᵢu`, with the
coefficient derivative read off the family rather than taken classically. Testing against `∂ⱼφ`
and summing gives
`∑ ∫_V a_{ij}(∂ᵢu) ∂_ℓ∂ⱼφ = -∑ ∫_V [(∂_ℓ a_{ij})(∂ᵢu) + a_{ij}(∂ₗ∂ᵢu)] ∂ⱼφ`. -/
theorem principal_move_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))}
    {A : EllipticCoeff d} {k : ℕ} (hA : IsWkInftyCoeff A (k + 1)) (ℓ : Fin d)
    (Du : Fin d → Lp ℝ 2 (volume.restrict V))
    (D2 : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (hD2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (aDu : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (haDu : ∀ i j, aDu i j =ᵐ[volume.restrict V] fun x => A.a x i j * (Du i x : ℝ))
    (comm : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (hcomm : ∀ i j, comm i j =ᵐ[volume.restrict V] fun x =>
      hA.D [ℓ] i j x * (Du i x : ℝ) + A.a x i j * (D2 ℓ i x : ℝ))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∑ i, ∑ j, ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
      = - ∑ i, ∑ j, ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
  have hstep : ∀ i j : Fin d,
      ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
        = - ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
    intro i j
    have hmove := HasWeakDerivOn.mul_isWkInfty_left ℓ (hD2 i)
      (hA.measurable_coeff i j) (hA.measurable_D_singleton ℓ i j) (hA.hasWeakPartial_D ℓ i j)
      (A.bdd i j) (hA.ae_abs_D_singleton_le ℓ i j) (aDu i j) (haDu i j) (comm i j) (hcomm i j)
    obtain ⟨hψc, hψcs, hψV⟩ := isTest_partialD hφc hφcs hφV j
    exact hmove (partialD j φ) hψc hψcs hψV
  calc ∑ i, ∑ j, ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
      = ∑ i : Fin d, ∑ j : Fin d, - ∫ x in V, (comm i j x : ℝ) * partialD j φ x :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hstep i j))
    _ = - ∑ i, ∑ j, ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
        simp only [Finset.sum_neg_distrib]

/-- **Transport term for a `W^{1,∞}` coefficient.**
`∫_V b_i(∂ᵢu) ∂_ℓφ = -∫_V [(∂_ℓ b_i)(∂ᵢu) + b_i(∂ₗ∂ᵢu)] φ`, with the coefficient derivative read
off the family. -/
theorem transport_move_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {bi : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ} (hbi : IsWkInfty bi (k + 1))
    (Du_i D2_ℓi : Lp ℝ 2 (volume.restrict V)) (hD2 : HasWeakDerivOn V ℓ Du_i D2_ℓi)
    (bDu : Lp ℝ 2 (volume.restrict V))
    (hbDu : bDu =ᵐ[volume.restrict V] fun x => bi x * (Du_i x : ℝ))
    (comm : Lp ℝ 2 (volume.restrict V))
    (hcomm : comm =ᵐ[volume.restrict V]
      fun x => hbi.D [ℓ] x * (Du_i x : ℝ) + bi x * (D2_ℓi x : ℝ))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, (bDu x : ℝ) * partialD ℓ φ x = - ∫ x in V, (comm x : ℝ) * φ x :=
  HasWeakDerivOn.mul_isWkInfty_left ℓ hD2 hbi.measurable_self (hbi.measurable_D_singleton ℓ)
    (hbi.hasWeakPartial_D ℓ) hbi.ae_abs_le (hbi.ae_abs_D_singleton_le ℓ) bDu hbDu comm hcomm
    φ hφc hφcs hφV

/-- **Zeroth-order term for a `W^{1,∞}` coefficient.**
`∫_V c·u·∂_ℓφ = -∫_V [(∂_ℓ c)·u + c·(∂ₗu)] φ`, with the coefficient derivative read off the
family. -/
theorem zeroth_move_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ} (hc : IsWkInfty c (k + 1))
    (u_V Du_ℓ : Lp ℝ 2 (volume.restrict V)) (hDu : HasWeakDerivOn V ℓ u_V Du_ℓ)
    (cu : Lp ℝ 2 (volume.restrict V))
    (hcu : cu =ᵐ[volume.restrict V] fun x => c x * (u_V x : ℝ))
    (comm : Lp ℝ 2 (volume.restrict V))
    (hcomm : comm =ᵐ[volume.restrict V]
      fun x => hc.D [ℓ] x * (u_V x : ℝ) + c x * (Du_ℓ x : ℝ))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, (cu x : ℝ) * partialD ℓ φ x = - ∫ x in V, (comm x : ℝ) * φ x :=
  HasWeakDerivOn.mul_isWkInfty_left ℓ hDu hc.measurable_self (hc.measurable_D_singleton ℓ)
    (hc.hasWeakPartial_D ℓ) hc.ae_abs_le (hc.ae_abs_D_singleton_le ℓ) cu hcu comm hcomm
    φ hφc hφcs hφV

/-! ### Principal commutator -/

/-- **Moving `∂ⱼ` off the principal commutator for a `W^{2,∞}` coefficient.** The coefficient
derivative `∂_ℓ a_{ij}` is itself a `W^{1,∞}` weight, so the product `(∂_ℓ a_{ij})·∂ᵢu` has a weak
`j`-derivative and testing against `φ` moves `∂ⱼ` onto the product:
`∫_V (∂_ℓ a_{ij})(∂ᵢu) ∂ⱼφ = -∫_V [(∂ⱼ∂_ℓ a_{ij})(∂ᵢu) + (∂_ℓ a_{ij})(∂ⱼ∂ᵢu)] φ`.

The second order of the coefficient hypothesis is used only here: it supplies the mixed member
`hA.D [j, ℓ]` of the family. The `C²` version `commutator_move` spends most of its length
turning the Hessian bound into a bound on the mixed partial through two operator-norm steps, and
the `W^{2,∞}` bundle has that bound outright. -/
theorem commutator_move_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))}
    {A : EllipticCoeff d} {k : ℕ} (hA : IsWkInftyCoeff A (k + 2)) (ℓ i j : Fin d)
    (Du_i D2_ji : L2D V) (hD2 : HasWeakDerivOn V j Du_i D2_ji)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, hA.D [ℓ] i j x * (Du_i x : ℝ) * partialD j φ x
      = - ∫ x in V, (hA.D [j, ℓ] i j x * (Du_i x : ℝ)
              + hA.D [ℓ] i j x * (D2_ji x : ℝ)) * φ x := by
  classical
  have hwm : Measurable (hA.D [ℓ] i j) := hA.measurable_D_singleton ℓ i j
  have hdwm : Measurable (hA.D [j, ℓ] i j) := hA.measurable_D_pair j ℓ i j
  have hwM : ∀ᵐ x ∂(volume.restrict V), |hA.D [ℓ] i j x| ≤ hA.bound 1 :=
    ae_restrict_of_ae (hA.ae_abs_D_singleton_le ℓ i j)
  have hdwM : ∀ᵐ x ∂(volume.restrict V), |hA.D [j, ℓ] i j x| ≤ hA.bound 2 :=
    ae_restrict_of_ae (hA.ae_abs_D_pair_le j ℓ i j)
  -- The two product classes, with their pointwise representatives.
  set ag := mulCoeffL hwm hwM Du_i with hag_def
  set dag := mulCoeffL hdwm hdwM Du_i + mulCoeffL hwm hwM D2_ji with hdag_def
  have hag_rep : ag =ᵐ[volume.restrict V] fun x => hA.D [ℓ] i j x * (Du_i x : ℝ) := by
    rw [hag_def]; exact mulCoeffL_coeFn hwm hwM Du_i
  have hdag_rep : dag =ᵐ[volume.restrict V]
      fun x => hA.D [j, ℓ] i j x * (Du_i x : ℝ) + hA.D [ℓ] i j x * (D2_ji x : ℝ) := by
    rw [hdag_def]
    filter_upwards [Lp.coeFn_add (mulCoeffL hdwm hdwM Du_i) (mulCoeffL hwm hwM D2_ji),
      mulCoeffL_coeFn hdwm hdwM Du_i, mulCoeffL_coeFn hwm hwM D2_ji] with x hadd h1 h2
    simp only [hadd, h1, h2, Pi.add_apply]
  have hmove := HasWeakDerivOn.mul_isWkInfty_left j hD2 hwm hdwm
    (hA.hasWeakPartial_D_singleton j ℓ i j) (hA.ae_abs_D_singleton_le ℓ i j)
    (hA.ae_abs_D_pair_le j ℓ i j) ag hag_rep dag hdag_rep φ hφc hφcs hφV
  -- Read the identity through the representatives.
  have hlhs : ∫ x in V, (ag x : ℝ) * partialD j φ x
      = ∫ x in V, hA.D [ℓ] i j x * (Du_i x : ℝ) * partialD j φ x :=
    integral_congr_ae (by filter_upwards [hag_rep] with x hx; rw [hx])
  have hrhs : ∫ x in V, (dag x : ℝ) * φ x
      = ∫ x in V, (hA.D [j, ℓ] i j x * (Du_i x : ℝ)
          + hA.D [ℓ] i j x * (D2_ji x : ℝ)) * φ x :=
    integral_congr_ae (by filter_upwards [hdag_rep] with x hx; rw [hx])
  rw [← hlhs, ← hrhs]
  exact hmove

/-! ### Differentiated identity -/

/-- **Differentiated weak formulation (divergence-datum form) for `W^{1,∞}` coefficients.**
Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2, with every classical
coefficient derivative replaced by the chosen representative the `W^{k,∞}` bundles supply. Given
the localised weak identity `hLoc` for `u` on `V` together with the first and second weak
derivatives, for a fixed direction `ℓ` and every test function `φ` with `tsupport φ ⊆ V`, `∑ ∫_V
a_{ij}(∂ₗ∂ᵢu) ∂ⱼφ + ∑ ∫_V (∂_ℓ a_{ij})(∂ᵢu) ∂ⱼφ = ∫_V (∂_ℓf) φ - ∑ ∫_V [(∂_ℓ
b_i)(∂ᵢu)+b_i(∂ₗ∂ᵢu)] φ - ∫_V [(∂_ℓ c)u + c(∂_ℓu)] φ`.

Where `differentiated_weakForm_div` asks for `a ∈ C²` and `b, c ∈ C¹`, this asks for one weak
derivative of each, which is Guo's hypothesis at the first order. -/
theorem differentiated_weakForm_div_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))}
    (Op : FullEllipticOp d) {k m : ℕ} (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1))
    (hbc : IsWkInftyLower Op (m + 1)) (ℓ : Fin d)
    (u_V : L2D V) (Du : Fin d → L2D V) (D2 : Fin d → Fin d → L2D V) (f_V Df : L2D V)
    (hDu_D2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (hu_Duℓ : HasWeakDerivOn V ℓ u_V (Du ℓ))
    (hf_Df : HasWeakDerivOn V ℓ f_V Df)
    (hLoc : ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
        HasCompactSupport v → tsupport v ⊆ V →
        (∑ i, ∑ j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j v x)
          + (∑ i, ∫ x in V, Op.b x i * (Du i x : ℝ) * v x)
          + (∫ x in V, Op.c x * (u_V x : ℝ) * v x)
          = ∫ x in V, (f_V x : ℝ) * v x)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
      + (∑ i, ∑ j, ∫ x in V, hA.D [ℓ] i j x * (Du i x : ℝ) * partialD j φ x)
    = (∫ x in V, (Df x : ℝ) * φ x)
      - (∑ i, ∫ x in V, ((hbc.bReg i).D [ℓ] x * (Du i x : ℝ)
                          + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
      - (∫ x in V, (hbc.cReg.D [ℓ] x * (u_V x : ℝ) + Op.c x * (Du ℓ x : ℝ)) * φ x) := by
  classical
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  -- The order-one members of the three bundles, with their measurability and bounds.
  have hwm : ∀ i j, Measurable (hA.D [ℓ] i j) := fun i j => hA.measurable_D_singleton ℓ i j
  have hwM : ∀ i j, ∀ᵐ x ∂(volume.restrict V), |hA.D [ℓ] i j x| ≤ hA.bound 1 :=
    fun i j => ae_restrict_of_ae (hA.ae_abs_D_singleton_le ℓ i j)
  have hdbm : ∀ i, Measurable ((hbc.bReg i).D [ℓ]) :=
    fun i => (hbc.bReg i).measurable_D_singleton ℓ
  have hdbM : ∀ i, ∀ᵐ x ∂(volume.restrict V),
      |(hbc.bReg i).D [ℓ] x| ≤ (hbc.bReg i).bound 1 :=
    fun i => ae_restrict_of_ae ((hbc.bReg i).ae_abs_D_singleton_le ℓ)
  have hdcm : Measurable (hbc.cReg.D [ℓ]) := hbc.cReg.measurable_D_singleton ℓ
  have hdcM : ∀ᵐ x ∂(volume.restrict V), |hbc.cReg.D [ℓ] x| ≤ hbc.cReg.bound 1 :=
    ae_restrict_of_ae (hbc.cReg.ae_abs_D_singleton_le ℓ)
  -- Each partial derivative of the test function lies in `L²(V)`.
  have hφj : ∀ j : Fin d, MemLp (partialD j φ) 2 (volume.restrict V) := fun j =>
    ((contDiff_partialD hφc j).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume)
      (hasCompactSupport_partialD hφcs j)).restrict V
  -- Integrability of the two split summands of the principal term.
  have hInt1 : ∀ i j, Integrable
      (fun x => hA.D [ℓ] i j x * (Du i x : ℝ) * partialD j φ x) (volume.restrict V) := by
    intro i j
    have hbase : Integrable
        (fun x => ((mulCoeffL (hwm i j) (hwM i j) (Du i)) x : ℝ) * partialD j φ x)
        (volume.restrict V) :=
      (Lp.memLp (mulCoeffL (hwm i j) (hwM i j) (Du i))).integrable_mul (hφj j)
    refine hbase.congr ?_
    filter_upwards [mulCoeffL_coeFn (hwm i j) (hwM i j) (Du i)] with x hx
    rw [hx]
  have hInt2 : ∀ i j, Integrable
      (fun x => Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x) (volume.restrict V) := by
    intro i j
    have hbase : Integrable
        (fun x => ((Op.toEllipticCoeff.actL i j (D2 ℓ i)) x : ℝ) * partialD j φ x)
        (volume.restrict V) :=
      (Lp.memLp (Op.toEllipticCoeff.actL i j (D2 ℓ i))).integrable_mul (hφj j)
    refine hbase.congr ?_
    filter_upwards [Op.toEllipticCoeff.actL_coeFn i j (D2 ℓ i)] with x hx
    rw [hx]
  -- Names for the running integrals.
  set Sa := ∑ i, ∑ j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j (partialD ℓ φ) x
    with hSa_def
  set Sb := ∑ i, ∫ x in V, Op.b x i * (Du i x : ℝ) * partialD ℓ φ x with hSb_def
  set Sc := ∫ x in V, Op.c x * (u_V x : ℝ) * partialD ℓ φ x with hSc_def
  set Sf := ∫ x in V, (f_V x : ℝ) * partialD ℓ φ x with hSf_def
  set G1 := ∑ i, ∑ j, ∫ x in V, hA.D [ℓ] i j x * (Du i x : ℝ) * partialD j φ x with hG1_def
  set G2 := ∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x with hG2_def
  set Tterm := ∑ i, ∫ x in V, ((hbc.bReg i).D [ℓ] x * (Du i x : ℝ)
      + Op.b x i * (D2 ℓ i x : ℝ)) * φ x with hT_def
  set Zterm := ∫ x in V, (hbc.cReg.D [ℓ] x * (u_V x : ℝ) + Op.c x * (Du ℓ x : ℝ)) * φ x
    with hZ_def
  set Dterm := ∫ x in V, (Df x : ℝ) * φ x with hD_def
  -- The localised weak form tested against the admissible `∂_ℓφ`.
  have hstar : Sa + Sb + Sc = Sf := by
    rw [hSa_def, hSb_def, hSc_def, hSf_def]
    exact hLoc (partialD ℓ φ) (contDiff_partialD hφc ℓ) (hasCompactSupport_partialD hφcs ℓ)
      ((tsupport_partialD_subset ℓ φ).trans hφV)
  -- Principal term, through `principal_move_wkInfty` and the symmetry of mixed partials.
  have hprin : Sa = -(G1 + G2) := by
    have hP := principal_move_wkInfty hA ℓ Du D2 hDu_D2
      (fun i j => Op.toEllipticCoeff.actL i j (Du i))
      (fun i j => Op.toEllipticCoeff.actL_coeFn i j (Du i))
      (fun i j => mulCoeffL (hwm i j) (hwM i j) (Du i)
        + Op.toEllipticCoeff.actL i j (D2 ℓ i))
      (fun i j => by
        filter_upwards [Lp.coeFn_add (mulCoeffL (hwm i j) (hwM i j) (Du i))
            (Op.toEllipticCoeff.actL i j (D2 ℓ i)),
          mulCoeffL_coeFn (hwm i j) (hwM i j) (Du i),
          Op.toEllipticCoeff.actL_coeFn i j (D2 ℓ i)] with x hadd h1 h2
        simp only [hadd, h1, h2, Pi.add_apply]) hφc hφcs hφV
    have hLHS : (∑ i, ∑ j, ∫ x in V,
          (Op.toEllipticCoeff.actL i j (Du i) x : ℝ) * partialD ℓ (partialD j φ) x)
        = ∑ i, ∑ j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j (partialD ℓ φ) x := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      refine integral_congr_ae ?_
      filter_upwards [Op.toEllipticCoeff.actL_coeFn i j (Du i)] with x hx
      rw [hx, congrFun (partialD_partialD_swap hφc j ℓ) x]
    have hRHS : (∑ i, ∑ j, ∫ x in V,
          ((mulCoeffL (hwm i j) (hwM i j) (Du i)
            + Op.toEllipticCoeff.actL i j (D2 ℓ i)) x : ℝ) * partialD j φ x)
        = (∑ i, ∑ j, ∫ x in V, hA.D [ℓ] i j x * (Du i x : ℝ) * partialD j φ x)
          + (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← integral_add (hInt1 i j) (hInt2 i j)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (mulCoeffL (hwm i j) (hwM i j) (Du i))
          (Op.toEllipticCoeff.actL i j (D2 ℓ i)),
        mulCoeffL_coeFn (hwm i j) (hwM i j) (Du i),
        Op.toEllipticCoeff.actL_coeFn i j (D2 ℓ i)] with x hadd h1 h2
      simp only [hadd, h1, h2, Pi.add_apply]; ring
    rw [hSa_def, hG1_def, hG2_def, ← hLHS, hP, hRHS]
  -- Transport term, summed over the coordinate directions.
  have htrans : Sb = -Tterm := by
    rw [hSb_def, hT_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbrep : (mulCoeffL (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) (Du i))
        =ᵐ[volume.restrict V] fun x => Op.b x i * (Du i x : ℝ) :=
      mulCoeffL_coeFn (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) (Du i)
    have hcommBrep : (mulCoeffL (hdbm i) (hdbM i) (Du i)
          + mulCoeffL (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) (D2 ℓ i))
        =ᵐ[volume.restrict V] fun x => (hbc.bReg i).D [ℓ] x * (Du i x : ℝ)
          + Op.b x i * (D2 ℓ i x : ℝ) := by
      filter_upwards [Lp.coeFn_add (mulCoeffL (hdbm i) (hdbM i) (Du i))
          (mulCoeffL (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) (D2 ℓ i)),
        mulCoeffL_coeFn (hdbm i) (hdbM i) (Du i),
        mulCoeffL_coeFn (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) (D2 ℓ i)] with x hadd h1 h2
      simp only [hadd, h1, h2, Pi.add_apply]
    have hmove := transport_move_wkInfty ℓ (hbc.bReg i) (Du i) (D2 ℓ i) (hDu_D2 i)
      _ hbrep _ hcommBrep hφc hφcs hφV
    calc (∫ x in V, Op.b x i * (Du i x : ℝ) * partialD ℓ φ x)
        = ∫ x in V, ((mulCoeffL (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) (Du i) x : ℝ))
            * partialD ℓ φ x := by
          refine integral_congr_ae ?_
          filter_upwards [hbrep] with x hx
          rw [hx]
      _ = -∫ x in V, ((mulCoeffL (hdbm i) (hdbM i) (Du i)
              + mulCoeffL (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i)) (D2 ℓ i)) x : ℝ)
            * φ x := hmove
      _ = -∫ x in V, ((hbc.bReg i).D [ℓ] x * (Du i x : ℝ)
              + Op.b x i * (D2 ℓ i x : ℝ)) * φ x := by
          rw [neg_inj]
          refine integral_congr_ae ?_
          filter_upwards [hcommBrep] with x hx
          rw [hx]
  -- Zeroth-order term.
  have hzero : Sc = -Zterm := by
    rw [hSc_def, hZ_def]
    have hcrep : (mulCoeffL Op.c_meas (ae_restrict_of_ae Op.c_bdd) u_V)
        =ᵐ[volume.restrict V] fun x => Op.c x * (u_V x : ℝ) :=
      mulCoeffL_coeFn Op.c_meas (ae_restrict_of_ae Op.c_bdd) u_V
    have hcommCrep : (mulCoeffL hdcm hdcM u_V
          + mulCoeffL Op.c_meas (ae_restrict_of_ae Op.c_bdd) (Du ℓ))
        =ᵐ[volume.restrict V] fun x => hbc.cReg.D [ℓ] x * (u_V x : ℝ)
          + Op.c x * (Du ℓ x : ℝ) := by
      filter_upwards [Lp.coeFn_add (mulCoeffL hdcm hdcM u_V)
          (mulCoeffL Op.c_meas (ae_restrict_of_ae Op.c_bdd) (Du ℓ)),
        mulCoeffL_coeFn hdcm hdcM u_V,
        mulCoeffL_coeFn Op.c_meas (ae_restrict_of_ae Op.c_bdd) (Du ℓ)] with x hadd h1 h2
      simp only [hadd, h1, h2, Pi.add_apply]
    have hmove := zeroth_move_wkInfty ℓ hbc.cReg u_V (Du ℓ) hu_Duℓ _ hcrep _ hcommCrep
      hφc hφcs hφV
    calc (∫ x in V, Op.c x * (u_V x : ℝ) * partialD ℓ φ x)
        = ∫ x in V, ((mulCoeffL Op.c_meas (ae_restrict_of_ae Op.c_bdd) u_V x : ℝ))
            * partialD ℓ φ x := by
          refine integral_congr_ae ?_
          filter_upwards [hcrep] with x hx
          rw [hx]
      _ = -∫ x in V, ((mulCoeffL hdcm hdcM u_V
              + mulCoeffL Op.c_meas (ae_restrict_of_ae Op.c_bdd) (Du ℓ)) x : ℝ) * φ x := hmove
      _ = -∫ x in V, (hbc.cReg.D [ℓ] x * (u_V x : ℝ) + Op.c x * (Du ℓ x : ℝ)) * φ x := by
          rw [neg_inj]
          refine integral_congr_ae ?_
          filter_upwards [hcommCrep] with x hx
          rw [hx]
  -- The datum term is the defining property of the weak `ℓ`-derivative of `f`.
  have hdat : Sf = -Dterm := by
    rw [hSf_def, hD_def]
    exact datum_move ℓ hf_Df hφc hφcs hφV
  linarith [hstar, hprin, htrans, hzero, hdat]

/-- **Differentiated weak formulation (Evans strong-datum form), for `W^{2,∞}` principal and
`W^{1,∞}` lower-order coefficients.** Moving `∂ⱼ` off the principal commutator with
`commutator_move_wkInfty` merges the second block of the left-hand side into the datum, leaving
`∑ ∫_V a_{ij}(∂ₗ∂ᵢu) ∂ⱼφ = ∫_V f_ℓ · φ` with
`f_ℓ = ∂_ℓf - ∑_i [(∂_ℓ b_i)(∂ᵢu)+b_i(∂ₗ∂ᵢu)] - [(∂_ℓ c)u + c(∂_ℓu)]
        + ∑_{i,j}[(∂ⱼ∂_ℓ a_{ij})(∂ᵢu)+(∂_ℓ a_{ij})(∂ⱼ∂ᵢu)]`
delivered as an explicit sum of integrals. Every derivative of a coefficient is read off the
bundle, so nothing here asks a coefficient to be differentiable. -/
theorem differentiated_weakForm_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))}
    (Op : FullEllipticOp d) {k m : ℕ} (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2))
    (hbc : IsWkInftyLower Op (m + 1)) (ℓ : Fin d)
    (u_V : L2D V) (Du : Fin d → L2D V) (D2 : Fin d → Fin d → L2D V) (f_V Df : L2D V)
    (hDu_D2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (hD2_j : ∀ i j, HasWeakDerivOn V j (Du i) (D2 j i))
    (hu_Duℓ : HasWeakDerivOn V ℓ u_V (Du ℓ))
    (hf_Df : HasWeakDerivOn V ℓ f_V Df)
    (hLoc : ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
        HasCompactSupport v → tsupport v ⊆ V →
        (∑ i, ∑ j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j v x)
          + (∑ i, ∫ x in V, Op.b x i * (Du i x : ℝ) * v x)
          + (∫ x in V, Op.c x * (u_V x : ℝ) * v x)
          = ∫ x in V, (f_V x : ℝ) * v x)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
    = (∫ x in V, (Df x : ℝ) * φ x)
      - (∑ i, ∫ x in V, ((hbc.bReg i).D [ℓ] x * (Du i x : ℝ)
                          + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
      - (∫ x in V, (hbc.cReg.D [ℓ] x * (u_V x : ℝ) + Op.c x * (Du ℓ x : ℝ)) * φ x)
      + (∑ i, ∑ j, ∫ x in V, (hA.D [j, ℓ] i j x * (Du i x : ℝ)
          + hA.D [ℓ] i j x * (D2 j i x : ℝ)) * φ x) := by
  classical
  have hdiv := differentiated_weakForm_div_wkInfty Op hA hbc ℓ u_V Du D2 f_V Df
    hDu_D2 hu_Duℓ hf_Df hLoc hφc hφcs hφV
  have hCG : (∑ i, ∑ j, ∫ x in V, hA.D [ℓ] i j x * (Du i x : ℝ) * partialD j φ x)
      = -(∑ i, ∑ j, ∫ x in V, (hA.D [j, ℓ] i j x * (Du i x : ℝ)
          + hA.D [ℓ] i j x * (D2 j i x : ℝ)) * φ x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact commutator_move_wkInfty hA ℓ i j (Du i) (D2 j i) (hD2_j i j) hφc hφcs hφV
  linarith [hdiv, hCG]

end EllipticPdes.Regularity
