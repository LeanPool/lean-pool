/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CategoryAvoidance.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CategoryReduction
public import LeanPool.TuringConeRigidity.Representation.Assembly

/-!
# Category Avoidance
-/


@[expose] public section

namespace OAI

open Set Topology
namespace TuringRigidity.CategorySearch

theorem rational_rectangle_basis (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (p : ℝ × ℝ) (hp : p ∈ U) :
    ∃ l r : ℚ × ℚ, p ∈ rectangle l r ∧ rectangle l r ⊆ U := by
  obtain ⟨u,hu,v,hv,huv⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hp)
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
  obtain ⟨c,d,hcd,hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp hv
  obtain ⟨l1,hl1,hl1'⟩ := exists_rat_btwn hab.1
  obtain ⟨r1,hr1,hr1'⟩ := exists_rat_btwn hab.2
  obtain ⟨l2,hl2,hl2'⟩ := exists_rat_btwn hcd.1
  obtain ⟨r2,hr2,hr2'⟩ := exists_rat_btwn hcd.2
  refine ⟨(l1,l2),(r1,r2),⟨⟨hl1',hr1⟩,⟨hl2',hr2⟩⟩,?_⟩
  intro q hq
  exact huv ⟨hsub ⟨hl1.trans hq.1.1,hq.1.2.trans hr1'⟩,
    hsub' ⟨hl2.trans hq.2.1,hq.2.2.trans hr2'⟩⟩

theorem success_nowhereDense (A Y : Oracle) (hY : ¬ Reduces Y A) (c : OracleCode) :
    IsNowhereDense (success A Y c) := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨l,r,hpR,hR⟩ := rational_rectangle_basis _ isOpen_interior p hp
  exact hY (reduces_of_dense A Y c l r ⟨p,hpR⟩ (hR.trans interior_subset))

theorem category_avoidance : CategoryAvoidance := by
  intro A Y hY
  have heq : {p : ℝ × ℝ | Reduces Y (join (join A (cut p.1)) (cut p.2))} =
      ⋃ c : OracleCode, success A Y c := by
    ext p
    exact (OracleCode.turingReducible_iff_exists_code (oracleFunction Y)
      (oracleFunction (pairOracle A p))).trans (by simp [success])
  rw [heq]
  exact isMeagre_iUnion (fun c => (success_nowhereDense A Y hY c).isMeagre)

end TuringRigidity.CategorySearch

end OAI
