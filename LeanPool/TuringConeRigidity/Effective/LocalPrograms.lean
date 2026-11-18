/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalPrograms.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.ProgramSelection

/-!
# Local Programs
-/


@[expose] public section

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem locally_constant_on_restriction {X Y : Type*} [PseudoMetricSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : X → Y) (D : Set X)
    (hf : ContinuousOn f D) (x : X) (hx : x ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ D, dist y x < ε → f y = f x := by
  have hpre : f ⁻¹' {f x} ∈ nhdsWithin x D :=
    (hf x hx) ((isOpen_discrete ({f x} : Set Y)).mem_nhds (by simp))
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  exact ⟨ε,hε,fun y hy hdist => hsub ⟨hdist,hy⟩⟩

theorem fixed_local_indices (t u v : ℝ) (D : Set ℝ) (E : Set (ℝ × ℝ))
    (e : ℝ × ℝ → ℕ) (he : ContinuousOn e E)
    (hgood : (u, v) ∈ goodPairs t D E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      (∀ s ∈ rationalSpan t, ∀ a ∈ rationalSpan t, |s| < ρ → |a| < ρ →
        e (u+s,v-u+a) = e (u,v-u)) ∧
      (∀ s ∈ rationalSpan t, |s| < ρ → e (v+s,u-v) = e (v,u-v)) := by
  have hz : (0 : ℝ) ∈ rationalSpan t := ⟨0,0,by simp⟩
  have hp : (u,v-u) ∈ E := by simpa using (hgood 0 hz).2.1 0 hz
  have hq : (v,u-v) ∈ E := by simpa using (hgood 0 hz).2.2
  obtain ⟨εp,hεp,hpconst⟩ := locally_constant_on_restriction e E he (u,v-u) hp
  obtain ⟨εq,hεq,hqconst⟩ := locally_constant_on_restriction e E he (v,u-v) hq
  let ρ : ℝ := min 1 (min εp εq) / 2
  have hmin : 0 < min 1 (min εp εq) := lt_min (by norm_num) (lt_min hεp hεq)
  have hρ : 0 < ρ := div_pos hmin (by norm_num)
  have hρmin : ρ < min 1 (min εp εq) := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := hρmin.trans_le (min_le_left _ _)
  have hρp : ρ ≤ εp := le_trans hρmin.le ((min_le_right _ _).trans (min_le_left _ _))
  have hρq : ρ ≤ εq := le_trans hρmin.le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hρ,hρ1,?_,?_⟩
  · intro s hs a ha hsr har
    apply hpconst _ ((hgood s hs).2.1 a ha)
    rw [Prod.dist_eq]
    apply max_lt
    · simpa [Real.dist_eq, add_sub_cancel_left] using hsr.trans_le hρp
    · simpa only [Real.dist_eq, add_sub_cancel_left] using har.trans_le hρp
  · intro s hs hsr
    apply hqconst _ ((hgood s hs).2.2)
    rw [Prod.dist_eq]
    apply max_lt
    · simpa [Real.dist_eq, add_sub_cancel_left] using hsr.trans_le hρq
    · simpa using hεq

theorem fixed_local_programs (F : ℝ → Oracle) (t u v : ℝ)
    (D : Set ℝ) (E : Set (ℝ × ℝ)) (e : ℝ × ℝ → ℕ)
    (he : ContinuousOn e E) (hgood : (u, v) ∈ goodPairs t D E)
    (hspec : ∀ x y, OracleCode.eval (oracleFunction (join (F x) (F y)))
      (codeEnumeration (e (x, y))) = oracleFunction (F (x + y))) :
    ∃ (p q : ℕ) (ρ : ℝ), 0 < ρ ∧ ρ < 1 ∧
      (∀ s ∈ rationalSpan t, ∀ a ∈ rationalSpan t, |s| < ρ → |a| < ρ →
        OracleCode.eval (oracleFunction (join (F (u+s)) (F (v-u+a))))
          (codeEnumeration p) = oracleFunction (F (v+s+a))) ∧
      (∀ s ∈ rationalSpan t, |s| < ρ →
        OracleCode.eval (oracleFunction (join (F (v+s)) (F (u-v))))
          (codeEnumeration q) = oracleFunction (F (u+s))) := by
  obtain ⟨ρ,hρ,hρ1,hp,hq⟩ := fixed_local_indices t u v D E e he hgood
  refine ⟨e (u,v-u),e (v,u-v),ρ,hρ,hρ1,?_,?_⟩
  · intro s hs a ha hsr har
    have heq := hspec (u+s) (v-u+a)
    have hsum : (u+s)+(v-u+a) = v+s+a := by ring
    rw [hp s hs a ha hsr har, hsum] at heq
    exact heq
  · intro s hs hsr
    have heq := hspec (v+s) (u-v)
    have hsum : (v+s)+(u-v) = u+s := by ring
    rw [hq s hs hsr, hsum] at heq
    exact heq

end TuringRigidity

end OAI
