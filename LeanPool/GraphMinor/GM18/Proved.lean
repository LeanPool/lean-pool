/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Cited
public import LeanPool.GraphMinor.GM04.Main
public import LeanPool.GraphMinor.GM10.Section8
public import LeanPool.GraphMinor.GM10.Section9
public import LeanPool.GraphMinor.GM10.Section10
public import LeanPool.GraphMinor.GM10.TreeWidth

/-!
# The results that Graph Minors XVIII cites, proved

Each statement of `GraphMinor/GM18/Cited.lean` is proved here from the proofs of Graph Minors IV and
X,
so that the sections of Graph Minors XVIII take no hypotheses.
-/

@[expose] public section

namespace GraphMinor.GM18

open GraphMinor

universe u v w

/-- Graph Minors IV, (9.1) (page 252). -/
theorem gm04Theorem91 : GM04Theorem91Statement.{u, v, w} :=
  fun n P hΩ hrob htw ↦
    GM04.theorem_9_1_proof.{u, v, w, 0, 0} (GM04.theorem_5_3_proof GM04.lemma_2_2
      (GM04.thomas_5_1)) menger
      GM04.higman_8_3 hΩ n P hrob htw

/-- Graph Minors X, (5.2) (page 169). -/
theorem gm10Theorem52 : GM10.Theorem52Statement.{u, v} := GM10.theorem_5_2_statement

/-- Graph Minors X, (8.3) (page 175). -/
theorem gm10Theorem83 : GM10Theorem83Statement.{u, v} :=
  fun _ _ _ _ _ _ _ hCD hC'D hV h𝒯 hθ hmem ↦
    GM10.theorem_8_3_proof hCD hC'D hV hθ h𝒯 hmem

/-- Graph Minors X, (9.2) (page 178). -/
theorem gm10Theorem92 : GM10Theorem92Statement.{u, v} := fun G ↦
  let ⟨lam, hlam⟩ := GM10.theorem_9_2_proof G
  ⟨_, inferInstance, lam, hlam⟩

/-- Graph Minors X, (10.2) (page 181). -/
theorem gm10Theorem102 : GM10Theorem102Statement.{u, v, w} :=
  fun G lam θ₁ θ₂ 𝒯₁ 𝒯₂ A B hTB h₁ h₂ hdist ↦
    GM10.theorem_10_2_proof G lam θ₁ θ₂ 𝒯₁ 𝒯₂ A B hTB h₁ h₂ hdist

/-- Graph Minors X, (10.3) (page 181). -/
theorem gm10Theorem103 : GM10Theorem103Statement.{u, v, w} :=
  fun G lam θ 𝒯 hn hTB h𝒯 hdist ↦ GM10.theorem_10_3_proof G lam θ 𝒯 hn hTB h𝒯 hdist

end GraphMinor.GM18
