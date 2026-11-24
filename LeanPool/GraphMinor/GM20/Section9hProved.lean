/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9h

import LeanPool.GraphMinor.GM20.Section8b

/-!
# Graph Minors XX: deductions from Section9h

The deductions apply the proved results after their geometric prerequisites.
-/

public section
namespace GraphMinor.GM20
open Set Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 Hypergraph
universe u v
variable {α : Type u} {β : Type v}

/-- Graph Minors XX, (9.1) (page 349): "For every graded surface $(\Sigma, \rho)$, the set of all
$(\Sigma, \rho)$-hulled patchworks is well-behaved." -/
theorem theorem_9_1_proof
    (X : GradedSurface) : WellBehaved {P : UnlabeledPatchwork α β | IsHulled X P} := by
  classical
  intro Ω _ hΩ Q hQ
  obtain ⟨-, hfin, harc⟩ := cuff_statement.{0} X.S X.isSurface
  have hF : ∀ Θ ∈ cuffs X.S, Nonempty (Circle ≃ₜ Θ) := fun Θ hΘ ↦ harc Θ hΘ
  let F : CuffParam X.S := fun Θ hΘ ↦ (hF Θ hΘ).some
  obtain ⟨r, hr⟩ := (hfin.image X.ρ).bddAbove
  have hr' : ∀ Θ ∈ cuffs X.S, X.ρ Θ ≤ r := fun Θ hΘ ↦ hr ⟨Θ, hΘ, rfl⟩
  choose P hP hPc using hQ
  let A : ∀ i, Side X F (Q i) := fun i ↦ (exists_side X F (hP i) (hPc i)).some
  obtain ⟨i, j, hij, ζn, ζc, hζ, hle⟩ := GraphMinor.GM20.theorem_8_1_proof.{max u v} X.S
    X.isSurface X.connected
    (wqo_labelOrder hΩ (2 * r + 2)) (fun i ↦ (A i).Γ) (fun i c ↦ (A i).ψ (2 * r + 2) c)
    fun i ↦ (A i).three_connected
  exact ⟨i, j, hij, InflationHyp.simulated ⟨hζ, hle, by omega, (A i).bounded hr',
    (A j).bounded hr'⟩⟩

end GraphMinor.GM20
