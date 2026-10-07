/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselDistributionEmbedding

/-!
# L² representatives of Sobolev derivatives

An ordered spatial derivative through the Bessel order has a unique
spatial L² representative. The representative is defined here so its
linear and continuous dependence on the Sobolev field can be established.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap LineDeriv

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The L² representative of an ordered distributional derivative of a
Bessel field. -/
@[expose]
def regularisedBesselEvenOrderedDerivativeL2
    (k : ℕ) (α : List L2Vec3) (hα : α.length ≤ 2 * k)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3
      ((2 * k : ℕ) : ℝ) 2) : ComplexVectorL2 :=
  Classical.choose (regularisedBesselEven_orderedLineDeriv_L2 k v α hα)

/-- The chosen L² field represents exactly the ordered derivative of
the underlying Sobolev distribution. -/
theorem regularisedBesselEvenOrderedDerivativeL2_toDistr
    (k : ℕ) (α : List L2Vec3) (hα : α.length ≤ 2 * k)
    (v : BesselPotentialSpace L2Vec3 ComplexVec3
      ((2 * k : ℕ) : ℝ) 2) :
    (regularisedBesselEvenOrderedDerivativeL2 k α hα v :
      𝓢'(L2Vec3, ComplexVec3)) =
        regularisedOrderedDistributionDerivativeCLM α v.toDistr := by
  rw [regularisedOrderedDistributionDerivativeCLM_apply]
  exact (Classical.choose_spec
    (regularisedBesselEven_orderedLineDeriv_L2 k v α hα)).symm

theorem regularisedL2_toDistr_injective :
    Function.Injective
      (fun g : ComplexVectorL2 =>
        (g : 𝓢'(L2Vec3, ComplexVec3))) := by
  exact LinearMap.ker_eq_bot.mp
    (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ComplexVec3) (μ := volume) (p := 2))

/-- Ordered differentiation through the Bessel order is a complex-linear
map from the Sobolev carrier to the physical spatial L² carrier. -/
@[expose]
def regularisedBesselEvenOrderedDerivativeL2Linear
    (k : ℕ) (α : List L2Vec3) (hα : α.length ≤ 2 * k) :
    BesselPotentialSpace L2Vec3 ComplexVec3
      ((2 * k : ℕ) : ℝ) 2 →ₗ[ℂ] ComplexVectorL2 where
  toFun := regularisedBesselEvenOrderedDerivativeL2 k α hα
  map_add' v w := by
    apply regularisedL2_toDistr_injective
    change ((regularisedBesselEvenOrderedDerivativeL2 k α hα (v + w) :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
      MeasureTheory.Lp.toTemperedDistributionCLM ComplexVec3 volume 2
        (regularisedBesselEvenOrderedDerivativeL2 k α hα v +
          regularisedBesselEvenOrderedDerivativeL2 k α hα w)
    rw [map_add]
    change ((regularisedBesselEvenOrderedDerivativeL2 k α hα (v + w) :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
      ((regularisedBesselEvenOrderedDerivativeL2 k α hα v :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) +
      ((regularisedBesselEvenOrderedDerivativeL2 k α hα w :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3))
    rw [regularisedBesselEvenOrderedDerivativeL2_toDistr,
      regularisedBesselEvenOrderedDerivativeL2_toDistr,
      regularisedBesselEvenOrderedDerivativeL2_toDistr,
      BesselPotentialSpace.toDistr_add, map_add]
  map_smul' c v := by
    apply regularisedL2_toDistr_injective
    change ((regularisedBesselEvenOrderedDerivativeL2 k α hα (c • v) :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
      MeasureTheory.Lp.toTemperedDistributionCLM ComplexVec3 volume 2
        (c • regularisedBesselEvenOrderedDerivativeL2 k α hα v)
    rw [map_smul]
    change ((regularisedBesselEvenOrderedDerivativeL2 k α hα (c • v) :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
      c • ((regularisedBesselEvenOrderedDerivativeL2 k α hα v :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3))
    rw [regularisedBesselEvenOrderedDerivativeL2_toDistr,
      regularisedBesselEvenOrderedDerivativeL2_toDistr,
      BesselPotentialSpace.toDistr_smul, map_smul]

/-- The physical L² representative of an ordered Sobolev derivative is
continuous in the complete Bessel norm. -/
theorem regularisedBesselEvenOrderedDerivativeL2_continuous
    (k : ℕ) (α : List L2Vec3) (hα : α.length ≤ 2 * k) :
    Continuous (regularisedBesselEvenOrderedDerivativeL2 k α hα) := by
  let g := regularisedBesselEvenOrderedDerivativeL2Linear k α hα
  have hg : Continuous (g :
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * k : ℕ) : ℝ) 2 → ComplexVectorL2) := by
    apply g.continuous_of_seq_closed_graph
    intro seq x y hseq hgy
    let D := regularisedOrderedDistributionDerivativeCLM α |>.comp
      (regularisedBesselToDistrCLM ((2 * k : ℕ) : ℝ))
    let E : ComplexVectorL2 →L[ℂ] 𝓢'(L2Vec3, ComplexVec3) :=
      MeasureTheory.Lp.toTemperedDistributionCLM ComplexVec3 volume 2
    have hD : Filter.Tendsto (fun n => D (seq n)) Filter.atTop
        (nhds (D x)) := (D.continuous.tendsto x).comp hseq
    have hE : Filter.Tendsto (fun n => E (g (seq n))) Filter.atTop
        (nhds (E y)) := (E.continuous.tendsto y).comp hgy
    have hEq : (fun n => D (seq n)) = (fun n => E (g (seq n))) := by
      funext n
      change regularisedOrderedDistributionDerivativeCLM α
        ((regularisedBesselToDistrCLM ((2 * k : ℕ) : ℝ)) (seq n)) =
          (regularisedBesselEvenOrderedDerivativeL2 k α hα (seq n) :
            𝓢'(L2Vec3, ComplexVec3))
      rw [regularisedBesselToDistrCLM_apply]
      exact (regularisedBesselEvenOrderedDerivativeL2_toDistr
        k α hα (seq n)).symm
    rw [hEq] at hD
    have hLimit : E y = D x := tendsto_nhds_unique hE hD
    apply regularisedL2_toDistr_injective
    change E y = E (g x)
    have hRep : E (g x) = D x := by
      change ((regularisedBesselEvenOrderedDerivativeL2 k α hα x :
          ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
        regularisedOrderedDistributionDerivativeCLM α
          (regularisedBesselToDistrCLM ((2 * k : ℕ) : ℝ) x)
      rw [regularisedBesselToDistrCLM_apply]
      exact regularisedBesselEvenOrderedDerivativeL2_toDistr k α hα x
    exact hLimit.trans hRep.symm
  exact hg

/-- Ordered spatial differentiation of an H^{2k} Bessel field is a
bounded linear map to spatial L² through every order at most `2k`. -/
@[expose]
def regularisedBesselEvenOrderedDerivativeL2CLM
    (k : ℕ) (α : List L2Vec3) (hα : α.length ≤ 2 * k) :
    BesselPotentialSpace L2Vec3 ComplexVec3
      ((2 * k : ℕ) : ℝ) 2 →L[ℂ] ComplexVectorL2 :=
  ⟨regularisedBesselEvenOrderedDerivativeL2Linear k α hα,
    regularisedBesselEvenOrderedDerivativeL2_continuous k α hα⟩

/-- Each ordered physical L² derivative through the Bessel order has a
finite norm constant chosen independently of the Sobolev field. -/
theorem regularisedBesselEvenOrderedDerivativeL2_norm_le
    (k : ℕ) (α : List L2Vec3) (hα : α.length ≤ 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v :
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * k : ℕ) : ℝ) 2,
      ‖regularisedBesselEvenOrderedDerivativeL2 k α hα v‖ ≤
        C * ‖v‖ := by
  let D := regularisedBesselEvenOrderedDerivativeL2CLM k α hα
  refine ⟨‖D‖, norm_nonneg _, ?_⟩
  intro v
  have hD_apply : D v = regularisedBesselEvenOrderedDerivativeL2 k α hα v := rfl
  rw [← hD_apply]
  exact D.le_opNorm v

end CKN.Leray

end
