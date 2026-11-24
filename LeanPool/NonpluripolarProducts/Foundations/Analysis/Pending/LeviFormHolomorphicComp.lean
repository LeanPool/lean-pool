/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicDDC
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlaneTubePositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.UniformTubePositivity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LogWeightFactorization

/-!
# Naturality of the Levi form under a holomorphic map, and the chart tube function

Source: Copy-4, step 6 of the proof of `prop:principalization`, where `r_W²` is the
squared distance to the strict transform and the statement used is that *"the Levi
form of `r_W²` is positive semidefinite with kernel exactly `T_W`"*.

`Pending.PlaneTubePositivity` proves this when the submanifold is the standard
coordinate plane.  A submanifold is only *locally biholomorphic* to that plane
(`FirstPass.RegularAtDim` carries a flattening `Φ`), so the plane statement has to be
transported along `Φ`.  The transport rule is the naturality of the Levi form:

  `leviForm (ρ ∘ F) z v = leviForm ρ (F z) (dF_z v)`   for `F` holomorphic.

The workspace had only the **linear** case
(`Pending.AdaptedRadialLeviPreimage.leviForm_comp_complexLinearMap`).  The
holomorphic case is not a new analytic input: the second-derivative terms of `F`
cancel because `D²F` is `ℂ`-bilinear, and that cancellation is already carried by
`FirstPass.HolomorphicDDC.smoothDDC_comp`.  This file only reads it off at the
complex diagonal, where `smoothDDC` is the Levi form divided by `π`.

Consequences, all sorry-free:

* `leviForm_comp`: the naturality rule above.
* `leviForm_planeDistSq_comp`: the Levi form of the pulled-back tube function
  `r² ∘ F` is `‖(dF_z v)_normal‖²` — semipositive at EVERY point of the chart, not
  only along the submanifold, because the Levi form of `planeDistSq` does not depend
  on the base point and `F` is holomorphic.
* `leviForm_planeDistSq_comp_eq_zero_iff`: its kernel at `z` is exactly the
  preimage `(dF_z)⁻¹ (ℂ^k × 0)`, which is the tangent space of the flattened
  submanifold.  When `dF_z` is injective this is a `k`-dimensional subspace, and the
  inclusion `⊇` needs no injectivity at all.
* `exists_forall_isStrictlyPositive_add_smul_ddc_planeDistSq_comp`: step 6's sentence
  in a chart.  A continuous family of two-forms strictly positive along the flattened
  tangent directions at every point of a compact `S` becomes strictly positive in all
  directions after adding `B ddᶜ (r² ∘ F)`, for one `B₀` and on one open `V` with
  `S ⊆ V ⊆ U`.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp

open FirstPass PlaneTubePositivity PositivityPerturbation

noncomputable section

variable {k n : ℕ}

/-- **Naturality of the Levi form under a holomorphic map.**  This is
`FirstPass.HolomorphicDDC.smoothDDC_comp` read off at the complex diagonal; the
second-derivative terms of `F` have already cancelled there. -/
theorem leviForm_comp {F : ComplexModel k → ComplexModel n} {ρ : ComplexModel n → ℝ}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F U)
    (hρ : ContDiffOn ℝ ∞ ρ V) (hFV : MapsTo F U V) {z : ComplexModel k} (hz : z ∈ U)
    (v : ComplexModel k) :
    leviForm (fun y => ρ (F y)) z v = leviForm ρ (F z) (fderiv ℝ F z v) :=
  FirstPass.HolomorphicDDC.leviForm_comp hU hV hF hρ hFV hz v

/-! ### The tube function of a holomorphic flattening -/

variable {j : ℕ}

/-- **The Levi form of the pulled-back tube function.**  `r² ∘ F` has Levi form
`‖(dF_z v)_normal‖²` at every point of the chart. -/
theorem leviForm_planeDistSq_comp {F : ComplexModel k → ComplexModel n}
    {U : Set (ComplexModel k)} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {z : ComplexModel k} (hz : z ∈ U) (v : ComplexModel k) :
    leviForm (fun y => planeDistSq n j (F y)) z v =
      ∑ i ∈ normalIndices n j, ‖(fderiv ℝ F z v) i‖ ^ 2 := by
  rw [leviForm_comp hU isOpen_univ hF
      (contDiff_planeDistSq (n := n) (k := j)).contDiffOn (mapsTo_univ _ _) hz v,
    leviForm_planeDistSq]

/-- The pulled-back tube function is psh on the whole chart, not only along the
submanifold. -/
theorem leviForm_planeDistSq_comp_nonneg {F : ComplexModel k → ComplexModel n}
    {U : Set (ComplexModel k)} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {z : ComplexModel k} (hz : z ∈ U) (v : ComplexModel k) :
    0 ≤ leviForm (fun y => planeDistSq n j (F y)) z v := by
  rw [leviForm_planeDistSq_comp hU hF hz v]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The kernel of the Levi form of the pulled-back tube function is exactly the
preimage of the plane under the differential** — the tangent space of the flattened
submanifold. -/
theorem leviForm_planeDistSq_comp_eq_zero_iff {F : ComplexModel k → ComplexModel n}
    {U : Set (ComplexModel k)} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {z : ComplexModel k} (hz : z ∈ U) (v : ComplexModel k) :
    leviForm (fun y => planeDistSq n j (F y)) z v = 0 ↔
      fderiv ℝ F z v ∈ complexCoordinatePlane n j := by
  rw [leviForm_planeDistSq_comp hU hF hz v]
  exact planeDistSq_eq_zero_iff _

/-! ### Step 6 of `prop:principalization`, in a chart -/

/-- **The tube estimate in a chart.**  Copy-4's step 6 sentence, with `r_W²` read
through a holomorphic flattening `F`: a continuous family `a` of two-forms which is
strictly positive along `(dF)⁻¹(ℂ^j × 0)` at every point of a compact `S ⊆ U`
becomes strictly positive in all directions after adding `B ddᶜ (r² ∘ F)`, for ONE
constant `B₀` and on ONE open `V` with `S ⊆ V ⊆ U`.

The semipositivity of `ddᶜ (r² ∘ F)` holds on all of `U`, not just on `S`, which is
what makes the constant monotone and the compactness argument available. -/
theorem exists_forall_isStrictlyPositive_add_smul_ddc_planeDistSq_comp
    {F : ComplexModel k → ComplexModel n} {U : Set (ComplexModel k)}
    (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {a : ComplexModel k → ComplexModel k [⋀^Fin 2]→L[ℝ] ℝ} (hacont : ContinuousOn a U)
    {S : Set (ComplexModel k)} (hS : IsCompact S) (hSU : S ⊆ U)
    (hpos : ∀ z ∈ S, ∀ v : ComplexModel k, v ≠ 0 →
      fderiv ℝ F z v ∈ complexCoordinatePlane n j → 0 < quad (a z) v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ V : Set (ComplexModel k), IsOpen V ∧ S ⊆ V ∧ V ⊆ U ∧
      ∀ B : ℝ, B₀ ≤ B → ∀ z ∈ V,
        IsStrictlyPositive (a z + B • smoothDDC (fun y => planeDistSq n j (F y)) z) := by
  set ρ : ComplexModel k → ℝ := fun y => planeDistSq n j (F y) with hρdef
  have hρ : ContDiffOn ℝ ∞ ρ U :=
    (contDiff_planeDistSq (n := n) (k := j)).contDiffOn.comp
      (hF.restrict_scalars ℝ) (mapsTo_univ _ _)
  have hbcont : ContinuousOn (fun z => smoothDDC ρ z) U :=
    (LogWeightFactorization.smoothDDC_contDiffOn hU hρ).continuousOn
  have hquad : ∀ z ∈ U, ∀ v : ComplexModel k,
      quad (smoothDDC ρ z) v = leviForm ρ z v / Real.pi := by
    intro z hz v
    have hz2 : ContDiffAt ℝ 2 ρ z :=
      ((hρ z hz).contDiffAt (hU.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    exact FirstPass.smoothDDC_complexDiagonal_eq_leviForm hz2 v
  refine UniformTubePositivity.exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_familyOn
    hU hacont hbcont (fun z hz v => ?_) hS hSU (fun z hz v hv hnull => ?_)
  · rw [hquad z hz v]
    exact div_nonneg (leviForm_planeDistSq_comp_nonneg hU hF hz v) Real.pi_nonneg
  · refine hpos z hz v hv ?_
    rw [hquad z (hSU hz) v, div_eq_zero_iff] at hnull
    rcases hnull with h | h
    · exact (leviForm_planeDistSq_comp_eq_zero_iff hU hF (hSU hz) v).mp h
    · exact absurd h Real.pi_ne_zero

end

end SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp
