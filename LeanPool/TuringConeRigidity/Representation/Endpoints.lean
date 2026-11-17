/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/Endpoints.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalPrograms
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Endpoints
-/


@[expose] public section

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem countable_real_meagre (s : Set ℝ) (hs : s.Countable) : IsMeagre s := by
  have hsingle : ∀ x : ℝ, IsMeagre ({x} : Set ℝ) := by
    intro x
    apply IsNowhereDense.isMeagre
    simp [IsNowhereDense]
  have h := isMeagre_biUnion hs (fun x _ => hsingle x)
  simpa using h

theorem exists_separating_endpoints (F : ℝ → Oracle)
    (hfiber : ∀ B, {x | F x = B}.Countable) (D : Set ℝ) (hD : D ∈ residual ℝ)
    (u ρ : ℝ) (hρ : 0 < ρ) :
    ∃ lo hi : ℝ, -ρ < lo ∧ lo < 0 ∧ 0 < hi ∧ hi < ρ ∧
      u+lo ∈ D ∧ u+hi ∈ D ∧ F (u+lo) ≠ F (u+hi) := by
  have hleft : (D ∩ Ioo (u-ρ) u).Nonempty := by
    obtain ⟨x,hx,hxD⟩ := (dense_of_mem_residual hD).inter_open_nonempty
      (Ioo (u-ρ) u) isOpen_Ioo (nonempty_Ioo.mpr (by linarith))
    exact ⟨x,hxD,hx⟩
  obtain ⟨xm,hxmD,hxmlo,hxmhi⟩ := hleft
  have hfib : IsMeagre {x | F x = F xm} := countable_real_meagre _ (hfiber (F xm))
  have hres : D ∩ {x | F x = F xm}ᶜ ∈ residual ℝ := inter_mem hD hfib
  have hright : ((D ∩ {x | F x = F xm}ᶜ) ∩ Ioo u (u+ρ)).Nonempty := by
    obtain ⟨x,hx,hxD⟩ := (dense_of_mem_residual hres).inter_open_nonempty
      (Ioo u (u+ρ)) isOpen_Ioo (nonempty_Ioo.mpr (by linarith))
    exact ⟨x,hxD,hx⟩
  obtain ⟨xp,⟨hxpD,hxpF⟩,hxplo,hxphi⟩ := hright
  refine ⟨xm-u,xp-u,by linarith,by linarith,by linarith,by linarith,?_,?_,?_⟩
  · simpa using hxmD
  · simpa using hxpD
  · simpa [ne_comm] using hxpF

theorem exists_endpoint_bands (F : ℝ → Oracle)
    (hfiber : ∀ B, {x | F x = B}.Countable) (D : Set ℝ) (hD : D ∈ residual ℝ)
    (hcont : ContinuousOn F D) (t u ρ : ℝ) (hρ : 0 < ρ)
    (hshift : ∀ s ∈ rationalSpan t, u + s ∈ D) :
    ∃ (lo hi : ℝ) (j : ℕ) (δ : ℚ),
      -ρ < lo ∧ lo < 0 ∧ 0 < hi ∧ hi < ρ ∧
      0 < δ ∧ (δ : ℝ) < ρ ∧ 3*(δ : ℝ) < hi-lo ∧
      (∀ s ∈ rationalSpan t, s ∈ Icc lo (lo+(δ : ℝ)) → F (u+s) j ≠ F (u+hi) j) ∧
      (∀ s ∈ rationalSpan t, s ∈ Icc (hi-(δ : ℝ)) hi → F (u+s) j = F (u+hi) j) := by
  obtain ⟨lo,hi,hloρ,hlo,hhi,hhiρ,hloD,hhiD,hne⟩ :=
    exists_separating_endpoints F hfiber D hD u ρ hρ
  have hbit : ∃ j : ℕ, F (u+lo) j ≠ F (u+hi) j := by
    by_contra h
    apply hne
    funext j
    exact not_ne_iff.mp (fun hj => h ⟨j,hj⟩)
  obtain ⟨j,hj⟩ := hbit
  have hc : ContinuousOn (fun x => F x j) D := (continuous_apply j).comp_continuousOn hcont
  obtain ⟨εl,hεl,hlconst⟩ := locally_constant_on_restriction (fun x => F x j) D hc (u+lo) hloD
  obtain ⟨εr,hεr,hrconst⟩ := locally_constant_on_restriction (fun x => F x j) D hc (u+hi) hhiD
  let b : ℝ := min ρ (min εl (min εr ((hi-lo)/3)))
  have hb : 0 < b := lt_min hρ (lt_min hεl (lt_min hεr (by linarith)))
  obtain ⟨δ,hδ0,hδb⟩ := exists_rat_btwn hb
  have hδρ : (δ : ℝ) < ρ := hδb.trans_le (min_le_left _ _)
  have hδl : (δ : ℝ) < εl := hδb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : (δ : ℝ) < εr := hδb.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδgap : (δ : ℝ) < (hi-lo)/3 := hδb.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨lo,hi,j,δ,hloρ,hlo,hhi,hhiρ,by exact_mod_cast hδ0,hδρ,by linarith,?_,?_⟩
  · intro s hs hband
    have hdist : dist (u+s) (u+lo) < εl := by
      rw [Real.dist_eq]
      have heq : u+s-(u+lo) = s-lo := by ring
      rw [heq, abs_of_nonneg (sub_nonneg.mpr hband.1)]
      linarith [hband.2]
    rw [hlconst _ (hshift s hs) hdist]
    exact hj
  · intro s hs hband
    have hdist : dist (u+s) (u+hi) < εr := by
      rw [Real.dist_eq]
      have heq : u+s-(u+hi) = s-hi := by ring
      rw [heq, abs_of_nonpos (sub_nonpos.mpr hband.2)]
      linarith [hband.1]
    exact hrconst _ (hshift s hs) hdist

end TuringRigidity

end OAI
