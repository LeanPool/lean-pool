/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Conditional
public import LeanPool.GraphMinor.GM19.RadialExists
import LeanPool.GraphMinor.GM19.Section5r
import LeanPool.GraphMinor.GM19.Section6Two

/-!
# Graph Minors XIX, (6.1)

Far along a bad sequence, every inflation can be replaced by a linear one with the same edges. So
far
along the sequence there are no inflations at all.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe u w

/-- **Graph Minors XIX, (6.1)** (page 339): "Let $\chi$ satisfy* **S**$_1$, **S**$_3$, *and let*
$(\Gamma_i, \phi_i)$ $(i = 1, 2, \dots)$
*be a similarly oriented bad sequence for $\chi$. Then there exists $h \ge 1$ such that for
all $j > i \ge h$ there is no inflation of $(\Gamma_i, \phi_i)$ in $(\Gamma_j, \phi_j)$." -/
theorem theorem_6_1_proof
    {S Shat : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
    {β : Type w} [Infinite β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hS1 : ConditionS1.{u, w} Shat) (hS3 : ConditionS3 χ cap)
    (P : ℕ → ColouredPainting χ) (hbad : IsBadSequence χ P) (hsim : IsSimilarlyOriented χ P)
    (rad : ∀ i, RadialDrawing cap (P i).Γ) :
    ∃ h, ∀ i ≥ h, ∀ j > i, ¬ ∃ σv σe, IsColouredInflation χ (P i) (P j) σv σe := by
  obtain ⟨n, hn⟩ := theorem_6_2_proof.{u} S Shat cap χ.isSurface
  obtain ⟨h, hh⟩ := theorem_5_5_proof.{u, w} S Shat β cap χ hS1 hS3 P hbad hsim rad n
  refine ⟨h, fun i hi j hj ⟨σv, σe, hσ⟩ ↦ ?_⟩
  obtain ⟨σv', hσ', -⟩ := hn χ.Φ (P i).Γ (P j).Γ (rad i) (P i).fits (P j).fits (hh i hi).le σv σe
    hσ.isInflation hσ.respects
  exact hbad i j hj ⟨σv', σe, ⟨⟨hσ'.toIsInflation, hσ.respects, hσ.le_internal_2,
    hσ.le_internal_3, hσ.le_border⟩,
    hσ'⟩⟩

end GraphMinor.GM19
