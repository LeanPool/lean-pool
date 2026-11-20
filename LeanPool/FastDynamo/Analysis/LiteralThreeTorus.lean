/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseChart
public import LeanPool.FastDynamo.Analysis.R3Assembly
public import LeanPool.FastDynamo.Finish.RealSolution
public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# The literal three-torus

The whole development is carried out on the *product model*
`ProductTorus3 = TransverseTorus × AxialCircle` equipped with
`productMeasure = volume.prod AddCircle.haarAddCircle`, while the paper phrases its
statements on the *literal* three-torus `Torus 3 = Fin 3 → UnitAddCircle` equipped with its
ambient `volume`.  This module supplies the dictionary between the two models.

The measure-preserving equivalence `productToLiteral : ProductTorus3 ≃ᵐ Torus 3` and the induced
isometric `L²` transport `toLiteralL2` are built once, for an arbitrary Banach-module-valued `L²`
space, in `FastDynamo/Analysis/ProductFourier.lean`, where the scalar Fourier analysis already
needs them.  This module specialises and applies them.

It contains four groups of results.

* The real and complex specialisations `toLiteralR3L2` and `toLiteralC3L2` of `toLiteralL2`,
  with their norm and representative formulas.
* The transported real magnetic trajectory `literalRealTrajectory`, with its exact exponential
  norm law and growth bound — stated both against the product-model initial field and entirely
  inside `L²(Torus 3)`, against the trajectory's own value at time zero — and the transfer of
  nonvanishing from the product model.
* The axially independent velocity `literalVelocity` on `Torus 3`.
* A standalone descent lemma: a `LipschitzWith L`, `ℤ²`-periodic map on the plane descends to a
  `LipschitzWith L` map on the transverse two-torus for the quotient metric, and its axially
  independent extension to `Torus 3` is again `LipschitzWith L` for the product (sup) metric.
  The quotient map it descends along is `transverseTorusPoint` of
  `FastDynamo/Analysis/TransverseChart.lean`, the same map the velocity construction uses.  This
  part depends on nothing but the metric structure of `AddCircle`; in particular it does not use
  any of the velocity-construction modules.

No differential operator is transported here.  The induction operators of the development stay
on the product model, so divergence-freeness on `Torus 3` is not asserted; only
the measure-theoretic, metric and `L²` dictionaries are provided.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-! ## The vector-valued `L²` transports of the development -/

/-- Almost-everywhere representative formula for the `L²` transport: it is composition with the
inverse coordinate identification. -/
theorem toLiteralL2_coe_ae (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (g : Lp E 2 productMeasure) :
    (toLiteralL2 𝕜 E g : Torus 3 → E) =ᵐ[(volume : Measure (Torus 3))]
      fun x => g (productToLiteral.symm x) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_productToLiteral.symm productToLiteral)

/-- Coordinate form of the representative formula for the `L²` transport: the transported class
is represented by the product representative read at the transverse and axial coordinates. -/
theorem toLiteralL2_coe_ae_coords (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (g : Lp E 2 productMeasure) :
    (toLiteralL2 𝕜 E g : Torus 3 → E) =ᵐ[(volume : Measure (Torus 3))]
      fun x => g (fun j : Fin 2 => x j.castSucc, x (Fin.last 2)) := by
  refine (toLiteralL2_coe_ae 𝕜 E g).trans ?_
  filter_upwards with x
  rw [productToLiteral_symm_apply]

/-- Real vector fields in `L²` on the literal three-torus. -/
abbrev LiteralR3L2 := Lp R3 2 (volume : Measure (Torus 3))

/-- Complex vector fields in `L²` on the literal three-torus. -/
abbrev LiteralC3L2 := Lp C3 2 (volume : Measure (Torus 3))

/-- The real `L²` transport of the development to the literal three-torus. -/
def toLiteralR3L2 : ProductR3L2 ≃ₗᵢ[ℝ] LiteralR3L2 := toLiteralL2 ℝ R3

/-- The complex `L²` transport of the development to the literal three-torus. -/
def toLiteralC3L2 : ProductC3L2 ≃ₗᵢ[ℂ] LiteralC3L2 := toLiteralL2 ℂ C3

/-- The real `L²` transport preserves norms. -/
theorem norm_toLiteralR3L2 (g : ProductR3L2) : ‖toLiteralR3L2 g‖ = ‖g‖ :=
  toLiteralR3L2.norm_map g

/-- Representative formula for the complex `L²` transport. -/
theorem toLiteralC3L2_coe_ae (g : ProductC3L2) :
    (toLiteralC3L2 g : Torus 3 → C3) =ᵐ[(volume : Measure (Torus 3))]
      fun x => g (fun j : Fin 2 => x j.castSucc, x (Fin.last 2)) :=
  toLiteralL2_coe_ae_coords ℂ C3 g

/-! ## The transported real magnetic trajectory -/

/-- The explicit real magnetic trajectory, read on the literal three-torus. -/
def literalRealTrajectory (K : ℤ) (eigenvalue : ℂ) (b : TransverseC3L2) (t : ℝ) :
    LiteralR3L2 :=
  toLiteralR3L2 (realAxialTrajectory K eigenvalue b t)

/-- Transport does not change the norm of the real magnetic trajectory. -/
@[simp] theorem norm_literalRealTrajectory_eq (K : ℤ) (eigenvalue : ℂ) (b : TransverseC3L2)
    (t : ℝ) :
    ‖literalRealTrajectory K eigenvalue b t‖ = ‖realAxialTrajectory K eigenvalue b t‖ :=
  toLiteralR3L2.norm_map _

/-- Exact exponential norm law for the real magnetic trajectory on the literal three-torus. -/
theorem norm_literalRealTrajectory (K : ℤ) (hK : K ≠ 0) (eigenvalue : ℂ) (b : TransverseC3L2)
    (t : ℝ) :
    ‖literalRealTrajectory K eigenvalue b t‖ =
      Real.exp (t * eigenvalue.re) * ‖realAxialInitialField K b‖ := by
  rw [norm_literalRealTrajectory_eq, norm_realAxialTrajectory K hK]

/-- Nonvanishing transfers to the literal three-torus: no time can make the transported real
trajectory vanish. -/
theorem literalRealTrajectory_ne_zero (K : ℤ) (hK : K ≠ 0) (eigenvalue : ℂ)
    {b : TransverseC3L2} (hb : b ≠ 0) (t : ℝ) :
    literalRealTrajectory K eigenvalue b t ≠ 0 := by
  intro hzero
  have hnorm := norm_literalRealTrajectory_eq K eigenvalue b t
  rw [hzero, norm_zero] at hnorm
  exact realAxialTrajectory_ne_zero K hK eigenvalue hb t (norm_eq_zero.1 hnorm.symm)

/-- Exponential lower bound for the transported trajectory below the growth rate. -/
theorem literalRealTrajectory_norm_lower_bound (K : ℤ) (hK : K ≠ 0) (eigenvalue : ℂ)
    (b : TransverseC3L2) (g t : ℝ) (hg : g ≤ eigenvalue.re) (ht : 0 ≤ t) :
    Real.exp (t * g) * ‖realAxialInitialField K b‖ ≤
      ‖literalRealTrajectory K eigenvalue b t‖ := by
  rw [norm_literalRealTrajectory_eq]
  exact realAxialTrajectory_norm_lower_bound K hK eigenvalue b g t hg ht

/-- At time zero the transported trajectory is the transported initial field. -/
theorem literalRealTrajectory_zero (K : ℤ) (eigenvalue : ℂ) (b : TransverseC3L2) :
    literalRealTrajectory K eigenvalue b 0 = toLiteralR3L2 (realAxialInitialField K b) := by
  rw [literalRealTrajectory, realAxialTrajectory_zero]

/-- The norm of the transported trajectory at time zero is the norm of the initial field. -/
theorem norm_literalRealTrajectory_zero (K : ℤ) (eigenvalue : ℂ) (b : TransverseC3L2) :
    ‖literalRealTrajectory K eigenvalue b 0‖ = ‖realAxialInitialField K b‖ := by
  rw [literalRealTrajectory_zero, norm_toLiteralR3L2]

/-- **The exact exponential norm law entirely inside `L²(Torus 3; ℝ³)`**: both sides of the law
refer to the transported trajectory, the initial field being its value at time zero. -/
theorem norm_literalRealTrajectory_eq_exp_mul_norm_zero (K : ℤ) (hK : K ≠ 0) (eigenvalue : ℂ)
    (b : TransverseC3L2) (t : ℝ) :
    ‖literalRealTrajectory K eigenvalue b t‖ =
      Real.exp (t * eigenvalue.re) * ‖literalRealTrajectory K eigenvalue b 0‖ := by
  rw [norm_literalRealTrajectory_zero, norm_literalRealTrajectory K hK]

/-- **The exponential growth bound entirely inside `L²(Torus 3; ℝ³)`**: below the growth rate
the transported trajectory stays above `e^{t g}` times its own value at time zero. -/
theorem literalRealTrajectory_norm_lower_bound_zero (K : ℤ) (hK : K ≠ 0) (eigenvalue : ℂ)
    (b : TransverseC3L2) (g t : ℝ) (hg : g ≤ eigenvalue.re) (ht : 0 ≤ t) :
    Real.exp (t * g) * ‖literalRealTrajectory K eigenvalue b 0‖ ≤
      ‖literalRealTrajectory K eigenvalue b t‖ := by
  rw [norm_literalRealTrajectory_zero]
  exact literalRealTrajectory_norm_lower_bound K hK eigenvalue b g t hg ht

/-! ## Complexification on the literal three-torus -/

/-- Complexification of real vector fields on the literal three-torus: the pointwise inclusion
`ℝ³ → ℂ³` applied to `L²(Torus 3; ℝ³)`. -/
def complexifyLiteralR3L2 : LiteralR3L2 →L[ℝ] LiteralC3L2 :=
  complexifyR3.compLpL 2 (volume : Measure (Torus 3))

/-- **Complexification commutes with the transport to the literal three-torus**: transporting
the complexification of a real field on the product model is complexifying the transported
real field. -/
theorem toLiteralC3L2_complexifyProductR3L2 (v : ProductR3L2) :
    toLiteralC3L2 (complexifyProductR3L2 v) = complexifyLiteralR3L2 (toLiteralR3L2 v) := by
  have hqmp := (measurePreserving_productToLiteral.symm productToLiteral).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [toLiteralL2_coe_ae ℂ C3 (complexifyProductR3L2 v),
    hqmp.ae_eq_comp (complexifyProductR3L2_coe_ae v),
    complexifyR3.coeFn_compLpL (μ := (volume : Measure (Torus 3))) (toLiteralR3L2 v),
    toLiteralL2_coe_ae ℝ R3 v] with x h1 h2 h3 h4
  exact h1.trans (h2.trans ((congrArg complexifyR3 h4).symm.trans h3.symm))

/-! ## The axially independent velocity on the literal three-torus -/

/-- The axially independent extension of a transverse velocity profile to the literal
three-torus. -/
def literalVelocity (v : TransverseTorus → R3) : Torus 3 → R3 :=
  fun x => v (fun j : Fin 2 => x j.castSucc)

/-- The extension is independent of the axial coordinate. -/
@[simp] theorem literalVelocity_snoc (v : TransverseTorus → R3) (y : TransverseTorus)
    (s : AxialCircle) : literalVelocity v (Fin.snoc y s) = v y := by
  simp [literalVelocity]

/-- Dropping the axial coordinate is `1`-Lipschitz for the sup metrics. -/
theorem lipschitzWith_dropAxial :
    LipschitzWith 1 (fun x : Torus 3 => (fun j : Fin 2 => x j.castSucc)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  exact (dist_pi_le_iff dist_nonneg).2 fun j => dist_le_pi_dist x y j.castSucc

/-- The axially independent extension keeps the Lipschitz constant. -/
theorem lipschitzWith_literalVelocity {L : ℝ≥0} {v : TransverseTorus → R3}
    (hv : LipschitzWith L v) : LipschitzWith L (literalVelocity v) := by
  have h := hv.comp lipschitzWith_dropAxial
  rwa [mul_one] at h

/-! ## Three generic facts about `L²(T³; ℂ³)`

Nothing below depends on the velocity, on a flow or on a parameter; they are stated here, next to
`LiteralC3L2`, so that the modules of `FastDynamo/Dynamics/Ideal/` share one copy. -/

/-- **Parseval in physical space on the literal three-torus**: the squared `L²` norm is the
integral of the pointwise squared norm of any representative. -/
theorem sq_norm_literalC3L2_eq_integral (G : LiteralC3L2) :
    ‖G‖ ^ 2 = ∫ a : Torus 3, ‖(G : Torus 3 → C3) a‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) G, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) G G)]
  refine integral_congr_ae ?_
  filter_upwards with a
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((G : Torus 3 → C3) a)

/-- The pointwise squared norm of an `L²` field on the literal three-torus is integrable; it is
the dominating function of the dominated-convergence steps of
`FastDynamo/Dynamics/Ideal/StrongContinuity.lean` and
`FastDynamo/Dynamics/Ideal/TruncatedConvergence.lean`. -/
theorem integrable_sq_norm_literalC3L2 (B : LiteralC3L2) :
    Integrable (fun a : Torus 3 ↦ ‖(B : Torus 3 → C3) a‖ ^ 2)
      (volume : Measure (Torus 3)) := by
  refine ((L2.integrable_inner (𝕜 := ℂ) B B).re).congr ?_
  filter_upwards with a
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((B : Torus 3 → C3) a)

/-- Pointwise application of a measurable operator-valued symbol to an `L²` field is almost
everywhere strongly measurable.  The symbol of the Cauchy transport
(`FastDynamo/Dynamics/Ideal/CauchyOperator.lean`) is measurable but **not** continuous, so this
is the form of the measurability statement the dominated-convergence steps need. -/
theorem aestronglyMeasurable_clm_apply_literalC3L2 {M : Torus 3 → (C3 →L[ℂ] C3)}
    (hM : Measurable M) (B : LiteralC3L2) :
    AEStronglyMeasurable (fun a : Torus 3 ↦ M a ((B : Torus 3 → C3) a))
      (volume : Measure (Torus 3)) :=
  (ContinuousLinearMap.id ℂ (C3 →L[ℂ] C3)).aestronglyMeasurable_comp₂
    hM.aestronglyMeasurable (Lp.aestronglyMeasurable B)

/-! General facts about the integer lattice acting on the plane and on the unit circle.  Their
names are collision-prone, so they are kept out of the root namespace. -/

namespace LatticePeriodic

/-- `ℤ²`-periodicity of a map on the plane. -/
def IsPeriodic {F : Type*} (f : ℝ × ℝ → F) : Prop :=
  ∀ (x : ℝ × ℝ) (m n : ℤ), f (x.1 + m, x.2 + n) = f x

/-- Adding an integer does not move a point of the unit circle. -/
theorem unitAddCircle_coe_add_intCast (u : ℝ) (k : ℤ) :
    ((u + k : ℝ) : UnitAddCircle) = (u : UnitAddCircle) := by
  have hk : ((k : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [AddCircle.coe_add, hk, add_zero]

/-- Two reals have the same class on the unit circle exactly when they differ by an integer. -/
theorem unitAddCircle_coe_eq_iff {u v : ℝ} :
    ((u : UnitAddCircle)) = (v : UnitAddCircle) ↔ ∃ k : ℤ, u = v + k := by
  constructor
  · intro h
    have h0 : ((u - v : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    refine ⟨k, ?_⟩
    have hk' : (k : ℝ) = u - v := by simpa using hk
    linarith
  · rintro ⟨k, rfl⟩
    exact unitAddCircle_coe_add_intCast v k

/-- The unit-circle distance between the classes of two reals is the distance from their
difference to the nearest integer. -/
theorem dist_unitAddCircle_coe (u v : ℝ) :
    dist ((u : UnitAddCircle)) ((v : UnitAddCircle)) = |u - v - (round (u - v) : ℤ)| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]

end LatticePeriodic

/-- **The quotient map of the unit circle is `1`-Lipschitz.**  `UnitAddCircle` is
`ℝ ⧸ AddSubgroup.zmultiples 1` with the quotient norm, so the class of a real is no longer than
the real itself.  Consumed by `lipschitzWith_transverseTorusPoint`
(`FastDynamo/Dynamics/Flow/TorusFlow.lean`) and by `lipschitzWith_literalTorusPoint`
(`FastDynamo/Dynamics/Flow/ParticleFlowUniqueness.lean`). -/
theorem lipschitzWith_unitAddCircle_coe :
    LipschitzWith 1 (fun u : ℝ ↦ (u : UnitAddCircle)) := by
  refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
  have h := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := u - v)
  simpa [dist_eq_norm, Real.norm_eq_abs] using h

/-- On the unit circle the distance of two classes is at most the distance of any two
representatives: the quotient can only shorten.  Consumed by `exists_dist_div_natCast_le`
(`FastDynamo/Analysis/TorusNet.lean`). -/
theorem dist_unitAddCircle_coe_le_abs_sub (u v : ℝ) :
    dist ((u : UnitAddCircle)) ((v : UnitAddCircle)) ≤ |u - v| := by
  simpa [Real.dist_eq] using lipschitzWith_unitAddCircle_coe.dist_le_mul u v

/-- The quotient map of `FastDynamo/Analysis/TransverseChart.lean` is surjective: every point of
the transverse two-torus has a representative in the plane. -/
theorem transverseTorusPoint_surjective : Function.Surjective transverseTorusPoint := by
  intro y
  obtain ⟨u, hu⟩ := Quotient.exists_rep (y 0)
  obtain ⟨v, hv⟩ := Quotient.exists_rep (y 1)
  refine ⟨(u, v), ?_⟩
  funext j
  fin_cases j
  · simpa using hu
  · simpa using hv

/-- Integer translations do not change the projection to the transverse torus. -/
theorem transverseTorusPoint_add_int (x : ℝ × ℝ) (m n : ℤ) :
    transverseTorusPoint (x.1 + m, x.2 + n) = transverseTorusPoint x := by
  funext i
  change (if i = 0 then ((x.1 + m : ℝ) : UnitAddCircle) else ((x.2 + n : ℝ) : UnitAddCircle)) =
    if i = 0 then (x.1 : UnitAddCircle) else (x.2 : UnitAddCircle)
  rw [LatticePeriodic.unitAddCircle_coe_add_intCast,
    LatticePeriodic.unitAddCircle_coe_add_intCast]

/-- Points of the plane with the same transverse class differ by an integer vector. -/
theorem exists_int_of_transverseTorusPoint_eq {a b : ℝ × ℝ}
    (h : transverseTorusPoint a = transverseTorusPoint b) :
    ∃ m n : ℤ, a.1 = b.1 + m ∧ a.2 = b.2 + n := by
  have h0 : ((a.1 : UnitAddCircle)) = (b.1 : UnitAddCircle) := by
    simpa using congrFun h 0
  have h1 : ((a.2 : UnitAddCircle)) = (b.2 : UnitAddCircle) := by
    simpa using congrFun h 1
  obtain ⟨m, hm⟩ := LatticePeriodic.unitAddCircle_coe_eq_iff.1 h0
  obtain ⟨n, hn⟩ := LatticePeriodic.unitAddCircle_coe_eq_iff.1 h1
  exact ⟨m, n, hm, hn⟩

/-- A Lipschitz map on the plane that factors through the transverse two-torus descends with the
same Lipschitz constant, for the quotient metric on the torus. -/
theorem lipschitzWith_of_factorsThrough_transverseTorusPoint {F : Type*} [PseudoMetricSpace F]
    {L : ℝ≥0} {f : ℝ × ℝ → F} {g : TransverseTorus → F} (hf : LipschitzWith L f)
    (hg : ∀ x, g (transverseTorusPoint x) = f x) : LipschitzWith L g := by
  have key : ∀ u v : ℝ, |u - (round (u - v) : ℤ) - v|
      = dist ((u : UnitAddCircle)) ((v : UnitAddCircle)) := by
    intro u v
    rw [LatticePeriodic.dist_unitAddCircle_coe]
    congr 1
    ring
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  obtain ⟨a, rfl⟩ := transverseTorusPoint_surjective y
  obtain ⟨b, rfl⟩ := transverseTorusPoint_surjective z
  have hshift : transverseTorusPoint
      (a.1 - (round (a.1 - b.1) : ℤ), a.2 - (round (a.2 - b.2) : ℤ))
      = transverseTorusPoint a := by
    have h := transverseTorusPoint_add_int a (-round (a.1 - b.1)) (-round (a.2 - b.2))
    simpa [sub_eq_add_neg] using h
  have hgy : g (transverseTorusPoint a)
      = f (a.1 - (round (a.1 - b.1) : ℤ), a.2 - (round (a.2 - b.2) : ℤ)) := by
    rw [← hshift, hg]
  rw [hgy, hg b]
  refine (hf.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · rw [Real.dist_eq, key a.1 b.1]
    exact dist_le_pi_dist (transverseTorusPoint a) (transverseTorusPoint b) 0
  · rw [Real.dist_eq, key a.2 b.2]
    exact dist_le_pi_dist (transverseTorusPoint a) (transverseTorusPoint b) 1

/-- The descent of a lattice-periodic map on the plane to the transverse two-torus. -/
def transverseDescent {F : Type*} (f : ℝ × ℝ → F) : TransverseTorus → F :=
  fun y => f (Function.surjInv transverseTorusPoint_surjective y)

/-- The descent of a `ℤ²`-periodic map reproduces the map on the plane. -/
theorem transverseDescent_transverseTorusPoint {F : Type*} {f : ℝ × ℝ → F}
    (hf : LatticePeriodic.IsPeriodic f) (x : ℝ × ℝ) :
    transverseDescent f (transverseTorusPoint x) = f x := by
  have h : transverseTorusPoint
      (Function.surjInv transverseTorusPoint_surjective (transverseTorusPoint x))
      = transverseTorusPoint x :=
    Function.surjInv_eq transverseTorusPoint_surjective _
  obtain ⟨m, n, h1, h2⟩ := exists_int_of_transverseTorusPoint_eq h
  change f (Function.surjInv transverseTorusPoint_surjective (transverseTorusPoint x)) = f x
  rw [show Function.surjInv transverseTorusPoint_surjective (transverseTorusPoint x)
      = ((x.1 + m : ℝ), (x.2 + n : ℝ)) from Prod.ext h1 h2]
  exact hf x m n

/-- The descent is the unique map on the transverse two-torus compatible with a `ℤ²`-periodic
map on the plane. -/
theorem eq_transverseDescent {F : Type*} {f : ℝ × ℝ → F} {g : TransverseTorus → F}
    (hf : LatticePeriodic.IsPeriodic f) (hg : ∀ x, g (transverseTorusPoint x) = f x) :
    g = transverseDescent f := by
  funext y
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [hg, transverseDescent_transverseTorusPoint hf]

/-- A `LipschitzWith L`, `ℤ²`-periodic map on the plane descends to a `LipschitzWith L` map on
the transverse two-torus with its quotient metric. -/
theorem lipschitzWith_transverseDescent {F : Type*} [PseudoMetricSpace F] {L : ℝ≥0}
    {f : ℝ × ℝ → F} (hL : LipschitzWith L f) (hper : LatticePeriodic.IsPeriodic f) :
    LipschitzWith L (transverseDescent f) :=
  lipschitzWith_of_factorsThrough_transverseTorusPoint hL
    (transverseDescent_transverseTorusPoint hper)

/-! ## The quotient `ℝ³ → T³` and its metric properties -/

/-- The coordinatewise quotient `ℝ³ → T³ = Fin 3 → UnitAddCircle`.  This is the three-dimensional
companion of `transverseTorusPoint` (`FastDynamo/Analysis/TransverseChart.lean`) and of
`rawTorusPoint` (`FastDynamo/Global/TorusChartL2Operators.lean`).  It is the device the paper uses
to differentiate maps of `T³` ("the periodic lift of `u` and the corresponding equivariant lift of
`Φ_t`", proof of `cor:ideal-growth`); the notion of a periodic lift itself is `IsLiteralTorusLift`
of `FastDynamo/Dynamics/ParticleFlow.lean`. -/
def literalTorusPoint (x : R3) : Torus 3 := fun j ↦ (x j : UnitAddCircle)

/-! ## Additivity of the quotient -/

/-- The quotient `ℝ³ → T³` is additive. -/
theorem literalTorusPoint_add (a b : R3) :
    literalTorusPoint (a + b) = literalTorusPoint a + literalTorusPoint b := by
  funext j
  simp [literalTorusPoint]

/-- The quotient sends the origin to the origin. -/
@[simp] theorem literalTorusPoint_zero : literalTorusPoint (0 : R3) = 0 := by
  funext j
  simp [literalTorusPoint]

/-- The quotient commutes with negation. -/
theorem literalTorusPoint_neg (a : R3) :
    literalTorusPoint (-a) = -literalTorusPoint a := by
  funext j
  simp [literalTorusPoint]

/-- Subtracting an integer vector does not change the class in the transverse two-torus. -/
theorem transverseTorusPoint_sub_int (x : ℝ × ℝ) (m n : ℤ) :
    transverseTorusPoint ((x.1 - m, x.2 - n)) = transverseTorusPoint x := by
  have h := transverseTorusPoint_add_int ((x.1 - m, x.2 - n)) m n
  simpa using h.symm

/-! ## The quotient map `transverseTorusPoint` as a metric quotient -/

/-- **The quotient map to the transverse two-torus is `1`-Lipschitz** for the sup metric of the
plane and the sup metric of `TransverseTorus`.  Each of the two coordinates is the `1`-Lipschitz
quotient map `lipschitzWith_unitAddCircle_coe` of `FastDynamo/Analysis/LiteralThreeTorus.lean`. -/
theorem lipschitzWith_transverseTorusPoint : LipschitzWith 1 transverseTorusPoint := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i ↦ ?_
  have hfst : dist x.1 y.1 ≤ dist x y := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hsnd : dist x.2 y.2 ≤ dist x y := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  fin_cases i
  · change dist ((x.1 : UnitAddCircle)) ((y.1 : UnitAddCircle)) ≤ dist x y
    exact le_trans (by simpa using lipschitzWith_unitAddCircle_coe.dist_le_mul x.1 y.1) hfst
  · change dist ((x.2 : UnitAddCircle)) ((y.2 : UnitAddCircle)) ≤ dist x y
    exact le_trans (by simpa using lipschitzWith_unitAddCircle_coe.dist_le_mul x.2 y.2) hsnd

/-- **A metric section of the quotient map**: every point of the transverse two-torus has a plane
representative whose distance to a prescribed base point is at most the torus distance between the
point and the class of the base point.  Recentring a representative by the nearest integer vector
realises the quotient distance in each coordinate. -/
theorem exists_transverseTorusPoint_eq_and_dist_le (x : ℝ × ℝ) (y : TransverseTorus) :
    ∃ x' : ℝ × ℝ, transverseTorusPoint x' = y ∧
      dist x' x ≤ dist y (transverseTorusPoint x) := by
  obtain ⟨a, rfl⟩ := transverseTorusPoint_surjective y
  refine ⟨(a.1 - (round (a.1 - x.1) : ℤ), a.2 - (round (a.2 - x.2) : ℤ)),
    transverseTorusPoint_sub_int a _ _, ?_⟩
  have key : ∀ u v : ℝ, |u - (round (u - v) : ℤ) - v|
      = dist ((u : UnitAddCircle)) ((v : UnitAddCircle)) := by
    intro u v
    rw [LatticePeriodic.dist_unitAddCircle_coe]
    congr 1
    ring
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · rw [Real.dist_eq]
    change |a.1 - (round (a.1 - x.1) : ℤ) - x.1| ≤ _
    rw [key a.1 x.1]
    exact dist_le_pi_dist (transverseTorusPoint a) (transverseTorusPoint x) 0
  · rw [Real.dist_eq]
    change |a.2 - (round (a.2 - x.2) : ℤ) - x.2| ≤ _
    rw [key a.2 x.2]
    exact dist_le_pi_dist (transverseTorusPoint a) (transverseTorusPoint x) 1

/-- **A continuous `ℤ²`-periodic map on the plane descends to a continuous map** of the transverse
two-torus.  This is the continuity companion of `lipschitzWith_transverseDescent`; the proof reads
the value of the descent at a nearby torus point on the plane representative supplied by
`exists_transverseTorusPoint_eq_and_dist_le`, which is correspondingly near the base point. -/
theorem continuous_transverseDescent {F : Type*} [PseudoMetricSpace F] {f : ℝ × ℝ → F}
    (hf : Continuous f) (hper : LatticePeriodic.IsPeriodic f) :
    Continuous (transverseDescent f) := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hf.continuousAt ε hε
  refine ⟨δ, hδ, fun {z} hz ↦ ?_⟩
  obtain ⟨x', hx', hdist⟩ := exists_transverseTorusPoint_eq_and_dist_le x z
  rw [← hx', transverseDescent_transverseTorusPoint hper,
    transverseDescent_transverseTorusPoint hper]
  exact hball (lt_of_le_of_lt (hx' ▸ hdist) hz)

/-- The transverse coordinates of the class of a point of `ℝ³` are the class of its first two
coordinates: `literalTorusPoint` and `transverseTorusPoint` agree on the transverse block. -/
theorem literalTorusPoint_castSucc (a : R3) :
    (fun j : Fin 2 ↦ literalTorusPoint a j.castSucc) = transverseTorusPoint (a 0, a 1) := by
  funext j
  fin_cases j <;> rfl

/-! ## The fundamental box of the transverse quotient -/

/-- The canonical half-open fundamental box `(0,1]²` of the lattice `ℤ²` acting on the Euclidean
transverse chart.  It is the pair-coordinate form of `TorusChartL2.rawFundamentalBox`. -/
def pairUnitIocBox : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1

/-- The fundamental box is measurable, being a product of two half-open intervals. -/
theorem measurableSet_pairUnitIocBox : MeasurableSet pairUnitIocBox :=
  measurableSet_Ioc.prod measurableSet_Ioc

end

end FastDynamo
