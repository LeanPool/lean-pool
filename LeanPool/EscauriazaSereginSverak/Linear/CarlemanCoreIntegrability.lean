/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanCore

/-!
# Integrability of the scalar commutator density

The compact-support property needed to compare the pointwise half-space
commutator bound with the integrated identity in `eq:carleman-commutator`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The product norm on parabolic space-time used for classical differentiation. -/
local instance carlemanCoreIntegrabilityNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

/-- The real scalar action compatible with the product norm on parabolic space-time. -/
local instance carlemanCoreIntegrabilityNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

private theorem commutatorDensity_contDiffOn
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiffOn ℝ (⊤ : ℕ∞) (carlemanCommutatorDensity φ v) U := by
  have hφi (i : Fin 3) := contDiffOn_spatialPartial hU hφ i
  have hvi (i : Fin 3) := contDiffOn_spatialPartial hU hv.contDiffOn i
  have hφij (i j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => spatialSecondPartial φ i j z) U := by
    exact contDiffOn_spatialPartial hU (hφi i) j
  have hφtt : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => timePartial (fun y => timePartial φ y) z) U :=
    contDiffOn_timePartial hU (contDiffOn_timePartial hU hφ)
  have hφit (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => timePartial (fun y => spatialPartial φ i y) z) U :=
    contDiffOn_timePartial hU (hφi i)
  have hφiijj (i j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => spatialSecondPartial
        (fun y => spatialSecondPartial φ i i y) j j z) U := by
    exact contDiffOn_spatialPartial hU
      (contDiffOn_spatialPartial hU (hφij i i) j) j
  have hgradφ := contDiffOn_scalarGradSq hU hφ
  have hgradv := contDiffOn_scalarGradSq hU hv.contDiffOn
  have htimeφ := contDiffOn_timePartial hU hφ
  unfold carlemanCommutatorDensity
  fun_prop (disch := assumption)

/-- The commutator density vanishes off the support of the field. -/
theorem carlemanCommutatorDensity_tsupport_subset
    (φ v : ParabolicPoint → ℝ) :
    tsupport (carlemanCommutatorDensity φ v) ⊆ tsupport v := by
  rw [tsupport]
  apply closure_minimal _ (isClosed_tsupport v)
  intro z hz
  by_contra hn
  have hv0 : v z = 0 := image_eq_zero_of_notMem_tsupport hn
  have hgrad (i : Fin 3) : spatialPartial v i z = 0 :=
    CKN.spatialPartial_eq_zero_off_tsupport hn i
  have hzero : carlemanCommutatorDensity φ v z = 0 := by
    simp [carlemanCommutatorDensity, scalarGradSq, hv0, hgrad]
  exact hz hzero

/-- The scalar commutator density is integrable for a smooth, compactly
supported field and a phase smooth near its support. -/
theorem integrable_carlemanCommutatorDensity
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    Integrable (carlemanCommutatorDensity φ v) volume := by
  have hs := carlemanCommutatorDensity_tsupport_subset φ v
  have hfc : HasCompactSupport (carlemanCommutatorDensity φ v) :=
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hs
  have hglobal : ContDiff ℝ (⊤ : ℕ∞)
      (carlemanCommutatorDensity φ v) :=
    contDiff_of_local_and_tsupport hU
      (commutatorDensity_contDiffOn hU hφ hv) (hs.trans hvU)
  change Integrable (fun z : Vec3 × ℝ =>
    carlemanCommutatorDensity φ v z) volume
  exact integrable_contDiff_compact hglobal hfc

end ESS
