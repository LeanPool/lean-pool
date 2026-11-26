/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section9
public import LeanPool.GraphMinor.GM14.Section10
public import LeanPool.GraphMinor.GM15.Cited

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM14.Section8

/-!
# Graph Minors XIV: Bridges to Graph Minors XV Cited Statements

This file concludes the cited statements `GM15.GM14Theorem96Statement` and
`GM15.GM14Theorem101Statement` from `theorem_9_6` and `theorem_10_1`.
-/

@[expose] public section

namespace GraphMinor.GM14

universe u v w

/-- Bridge theorem concluding `GM15.GM14Theorem96Statement` from `theorem_9_6_proof`. -/
theorem gm14_theorem_9_6 :
    GM15.GM14Theorem96Statement.{u, v, w} :=
  theorem_9_6_proof

/-- Bridge theorem concluding `GM15.GM14Theorem101Statement` from `theorem_10_1_proof`. -/
theorem gm14_theorem_10_1 :
    GM15.GM14Theorem101Statement.{u, v, w} := by
  intro S _ _ α β G₀ H η θ μ T d hS hConn hV_fin hE_fin hRig hMetric h12 hEven hθ hnot_step hii
  have h2cell : H.IsTwoCell := hMetric.1.1
  have hT : IsRespectfulDrawingTangle H θ T := hMetric.1
  have hi_path : ∀ (P : Graph α β) (u v : S),
      u ∈ H.V → v ∈ H.V →
      IsHPathWithEnds G₀ η.imageGraph P (η.vMap u) (η.vMap v) →
      d {u} {v} < μ := by
    intro P u v hu hv hP
    exact not_le.mp fun hge => hnot_step ⟨P, u, v, hu, hv, hP, hge⟩
  have hii_no_eye : ∀ (Λ : Set S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ)
      (η_cl : SpanEmbedding (clearedSubdrawing H Λ) G₀),
      IsLambdaZone H d (3 * μ + 3) Λ →
      IsRigid (clearedSubdrawing H Λ) →
      IsClearedTangle H T d θ (3 * μ + 3) Λ T' d' →
      (∀ v ∈ (clearedSubdrawing H Λ).V, η_cl.vMap v = η.vMap v) →
      (∀ e ∈ (clearedSubdrawing H Λ).E, η_cl.eMap e = η.eMap e) →
      ¬ IsDrawingEye G₀ (clearedSubdrawing H Λ) η_cl (θ - 4 * (3 * μ + 3) - 2) T' Λ := by
    rintro Λ T' d' η_cl ⟨z, _, hzone⟩ hRig_cl hT' hv he
    exact hii z Λ T' d' η_cl hzone hT' hRig_cl hv he
  exact theorem_10_1_proof
    hS hConn G₀ H η T d θ μ hV_fin hE_fin h2cell hRig hT hMetric ⟨h12, hEven⟩ hθ hi_path hii_no_eye

end GraphMinor.GM14
