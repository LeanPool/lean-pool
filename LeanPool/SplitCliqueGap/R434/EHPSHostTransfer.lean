/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSProduct
public import LeanPool.SplitCliqueGap.R434.CoreDirections
public import Mathlib.Data.Sym.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Physical host budget and exact-order transfer for the EHPS powers. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434.EHPS

/-- The grid elements whose normalized coordinates lie in the admissible region. -/
noncomputable def gridSupport (ε : ℝ) (m : ℕ) [NeZero m] : Finset (Grid m) := by
  classical
  exact univ.filter fun a => Region ε (gridPoint m a)

theorem mem_gridSupport {ε : ℝ} {m : ℕ} [NeZero m] {a : Grid m} :
    a ∈ gridSupport ε m ↔ Region ε (gridPoint m a) := by
  classical
  simp [gridSupport]

theorem productSupport_card (ε : ℝ) (m j : ℕ) [NeZero m] :
    (productSupport ε m j).card = (gridSupport ε m).card ^ j := by
  classical
  let eqv : productSupport ε m j ≃ (Fin j → gridSupport ε m) := {
    toFun := fun a i => ⟨a.val i, mem_gridSupport.mpr (mem_productSupport.mp a.prop i)⟩
    invFun := fun f => ⟨fun i => (f i).val,
      mem_productSupport.mpr (fun i => mem_gridSupport.mp (f i).prop)⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => funext fun _ => Subtype.ext rfl
  }
  simpa [Fintype.card_fun] using Fintype.card_congr eqv

/-- The linear bound on the number of host labels in the basic product construction. -/
def hostFactor (j : ℕ) := 255 + 1049760 * j

theorem host_order (m j : ℕ) [NeZero m] :
    Fintype.card ((H54.Role × ProductGrid m j) ⊕
      MidHost H54.Role (ProductGrid m j) (ProductClass j)) =
      hostFactor j * (m ^ 2) ^ j := by
  have hc : Fintype.card (ProductGrid m j) = (m ^ 2) ^ j := by
    simp [ZMod.card, pow_two]
  simp only [MidHost, Fintype.card_sum, Fintype.card_prod, hc, Sym2.card,
    Fintype.card_fin, Fintype.card_option, hostFactor]
  norm_num [Nat.choose_two_right]
  ring

theorem exact_graph_from_EHPS_scores {ε : ℝ} {m j n : ℕ} [NeZero m] (hm : Odd m)
    (hn : hostFactor j * (m ^ 2) ^ j ≤ n)
    (I : ℤ) {y : Finset (H54.Role × ProductGrid m j) → ℝ}
    (hi : ∀ P : Finset (Finset (H54.Role × ProductGrid m j)), IsPack P →
      ∑ Q ∈ P, w (H54.coreGraph (productHalf m j) (productSupport ε m j)) Q ≤ I)
    (hy : ResPack y) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
      (∑ Q, y Q * (w (H54.coreGraph (productHalf m j)
        (productSupport ε m j)) Q : ℝ)) - (I : ℝ) ≤ gap G := by
  classical
  have hH := midpoint_host_hyp H54.roleGraph (H54.roleStep (productHalf m j))
    (productSupport ε m j) (productHalf m j) (H54.roleStep_swap _) (productHalf_spec hm)
    (productColour ε m j) (fun _ _ ha hb hc => product_mid_outside hm ha hb hc)
  exact exact_graph_of_host_scores hH ((0,0),0) n (by simpa only [host_order] using hn) I hi hy

end GapExtremal.R434.EHPS
