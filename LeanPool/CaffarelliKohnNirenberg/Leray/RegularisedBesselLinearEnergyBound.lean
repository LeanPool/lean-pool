/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearFixedPoint
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesNorm

/-!
# Uniform energy bound for the linear complete Sobolev solution

The fixed physical L² coefficient makes the complete Sobolev mild
estimate linear, so the uniform energy time step controls its fixed point.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A fixed point of the linear complete Sobolev mild map on the
uniform energy interval has norm at most twice its initial norm. -/
theorem regularisedBesselLinearLocalFixedPoint_norm_le_twice
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (B : ℝ) (hB : 0 ≤ B)
    (g : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B), ComplexVectorL2))
    (hg : ∀ q, ‖g q‖ ≤ B)
    (v : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hfix : regularisedBesselLinearLocalMap ρ ε hε k b
      (regularisedBesselUniformEnergyStep ρ ε hε k B)
      (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
      g B hB hg v = v) :
    ‖v‖ ≤ 2 * ‖b‖ := by
  let T := regularisedBesselUniformEnergyStep ρ ε hε k B
  let hT : 0 ≤ T := (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
  let K := regularisedBesselTensorConstant ρ ε hε k
  let F := regularisedBesselLinearTensorPath ρ ε hε k T hT g v
  let C := K * B * ‖v‖
  let A := 2 * (K * B / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T
  have hK : 0 ≤ K := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hK hB) (norm_nonneg v)
  have hFC : ∀ s, ‖F s‖ ≤ C :=
    regularisedBesselLinearTensorPath_norm_le
      ρ ε hε k T hT g v B hB hg
  have hpoint : ∀ t, ‖v t‖ ≤ ‖b‖ + A * ‖v‖ := by
    intro t
    have hfixAt := congrArg
      (fun w : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) => w t) hfix
    have hHeat := regularisedBesselHeat_norm_le
      ((2 * k : ℕ) : ℝ) t.1 t.2.1 b
    have hInt := regularisedBesselShiftedStokesIntegral_norm_le
      k F C hFC hC T t.1 hT
    rw [← hfixAt, regularisedBesselLinearLocalMap_apply]
    calc
      ‖regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k F t.1 τ‖ ≤
          ‖regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b‖ +
            ‖∫ τ in (0 : ℝ)..T,
              regularisedBesselShiftedStokesIntegrand k F t.1 τ‖ :=
        norm_sub_le _ _
      _ ≤ ‖b‖ + 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T :=
        add_le_add hHeat hInt
      _ = ‖b‖ + A * ‖v‖ := by dsimp [C, A]; ring
  have hnonneg : 0 ≤ ‖b‖ + A * ‖v‖ :=
    (norm_nonneg (v ⟨0, le_refl _, hT⟩)).trans (hpoint _)
  have hsup : ‖v‖ ≤ ‖b‖ + A * ‖v‖ := (v.norm_le hnonneg).2 hpoint
  have hsmall : A ≤ 1 / 2 :=
    regularisedBesselUniformEnergyStep_small ρ ε hε k B hB
  have hmul : A * ‖v‖ ≤ (1 / 2 : ℝ) * ‖v‖ :=
    mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)
  linarith only [hsup, hmul]

end CKN.Leray

end
