/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CampanatoRepresentative

/-!
# SchauderRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Common representative for the unified Schauder chain
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- A globally defined representative: the Campanato representative on the
interior half-ball and the original Sobolev representative elsewhere. -/
def smallContrastSchauderRepresentative
    (u : H1Function (smallContrastUnitBall d)) (x : Vec d) : ℝ :=
  if x ∈ smallContrastBall d (1 / 2) then
    smallContrastCampanatoRepresentative (d := d) u.toFun x
  else u.toFun x

theorem smallContrastSchauderRepresentative_of_mem
    {u : H1Function (smallContrastUnitBall d)} {x : Vec d}
    (hx : x ∈ smallContrastBall d (1 / 2)) :
    smallContrastSchauderRepresentative u x =
      smallContrastCampanatoRepresentative (d := d) u.toFun x := by
  simp only [smallContrastSchauderRepresentative, ite_eq_left hx]

theorem smallContrastSchauderRepresentative_ae_eq [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u) :
    smallContrastSchauderRepresentative u =ᵐ[
      volume.restrict (smallContrastUnitBall d)] u.toFun := by
  have hhalf := campanatoRepresentative_ae_eq halpha hcamp
  have hhalfGlobal := (ae_restrict_iff'
    (isOpen_euclideanBall 0 (1 / 2 : ℝ)).measurableSet).1 hhalf
  refine (ae_restrict_iff'
    (isOpen_euclideanBall 0 (1 : ℝ)).measurableSet).2 ?_
  filter_upwards [hhalfGlobal] with x hx hunit
  by_cases hxin : x ∈ smallContrastBall d (1 / 2)
  · rw [smallContrastSchauderRepresentative_of_mem hxin, hx hxin]
  · simp only [smallContrastSchauderRepresentative, ite_eq_right hxin]

theorem continuousOn_smallContrastSchauderRepresentative [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hK : 0 ≤ K)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u) :
    ContinuousOn (smallContrastSchauderRepresentative u)
      (smallContrastBall d (1 / 2)) := by
  exact (continuousOn_smallContrastCampanatoRepresentative halpha hK hcamp).congr
    (fun x hx => smallContrastSchauderRepresentative_of_mem hx)

end


end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
