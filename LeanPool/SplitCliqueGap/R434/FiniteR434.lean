/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.CoreFractional
public import LeanPool.SplitCliqueGap.R434.RobustHosts
public import LeanPool.SplitCliqueGap.R434.EHPSCompactExterior
public import LeanPool.SplitCliqueGap.R434.UniversalHosts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! The finite gap at an exact order, with the concrete EHPS support. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434.EHPS

theorem finite_gap_of_product_for {ε : ℝ} {m j n d : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m)
    (loss : ∀ {U : Type} [Fintype U] [DecidableEq U], SimpleGraph U → ℝ)
    (realize : ∀ (I : ℤ) {y : Finset (H54.Role × ProductGrid m j) → ℝ},
      (∀ P : Finset (Finset (H54.Role × ProductGrid m j)), IsPack P →
        ∑ S ∈ P, w (H54.coreGraph (productHalf m j) (productSupport ε m j)) S ≤ I) →
      ResPack y → (∀ S, y S ≠ 0 → S.card ≤ 3) →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G d ∧
        (∑ Q, y Q * (w (H54.coreGraph (productHalf m j) (productSupport ε m j)) Q : ℝ)) -
          (I : ℝ) ≤ loss G) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G d ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ loss G := by
  classical
  let A := productSupport ε m j
  let h := productHalf m j
  let B := H54.coreGraph h A
  let τ : ℝ := ((A.card * Fintype.card (ProductGrid m j) : ℕ) : ℝ)
  let R : ℝ := (j : ℝ) * (100 * (m : ℝ) ^ 2 / ε ^ 2)
  let D : ℝ := 6 * τ / (27 * (1 + 2 * R / 1))
  let I := ⌊36 * τ - D⌋
  have hh : 2 * h = 1 := productHalf_spec hm
  have hi (P : Finset (Finset (H54.Role × ProductGrid m j))) (hP : IsPack P) :
      ∑ S ∈ P, w B S ≤ I := by
    apply Int.le_floor.mpr
    have hdef := H54.core_integer_defect_six h hh A R 1 (by dsimp [R]; positivity) (by norm_num)
      (productPotential ε m j) (fun _ ha => product_potential_bounds hε hε₁ ha)
      (fun a b c ha hb hc hab he => product_potential_midpoint hm hε hε₁ ha hc hb hab he) hP
    change D ≤ 36 * τ - ∑ S ∈ P, (w B S : ℝ) at hdef
    push_cast
    linarith only [hdef]
  obtain ⟨y, hy, hsmall, hscore⟩ := H54.core_fractional_score_small h hh A
  obtain ⟨V, fV, dV, G, hcard, hs, hconn, hcuts, hgap⟩ := realize I hi hy hsmall
  rw [hscore] at hgap
  have hfloor : (I : ℝ) ≤ 36 * τ - D := Int.floor_le _
  have hD : D ≤ loss G := by linarith only [hgap,hfloor]
  refine ⟨V, fV, dV, G, hcard, hs, hconn, hcuts, ?_⟩
  have hgrid : Fintype.card (ProductGrid m j) = (m ^ 2) ^ j := by simp [ZMod.card,pow_two]
  have hnume : τ = ((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j := by
    dsimp [τ,A]
    rw [productSupport_card, hgrid]
    push_cast
    rfl
  have hden : 27 * (1 + 2 * R / 1) = 27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2) := by
    dsimp [R]
    ring
  simpa only [D, hnume, hden] using hD

theorem finite_gap_of_product_with {ε : ℝ} {m j n d : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m)
    (realize : ∀ (I : ℤ) {y : Finset (H54.Role × ProductGrid m j) → ℝ},
      (∀ P : Finset (Finset (H54.Role × ProductGrid m j)), IsPack P →
        ∑ S ∈ P, w (H54.coreGraph (productHalf m j) (productSupport ε m j)) S ≤ I) →
      ResPack y →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G d ∧
        (∑ Q, y Q * (w (H54.coreGraph (productHalf m j) (productSupport ε m j)) Q : ℝ)) -
          (I : ℝ) ≤ gap G) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G d ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gap G := by
  exact finite_gap_of_product_for hε hε₁ hm gap (fun I _ hi hy _ => realize I hi hy)

theorem finite_gap_of_product_robust {ε : ℝ} {m j n : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m)
    (hn : hostFactor j * (m ^ 2) ^ j ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G ((m^2)^j) ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gap G := by
  exact finite_gap_of_product_with hε hε₁ hm (fun I _ hi hy => robust_graph_from_EHPS_scores hm hn
    I hi hy)

/-- The host-count multiplier for the compact 6-class construction. -/
def compactHostFactor (j : ℕ) := 255 + 2880 * j

theorem compact_host_order (m j : ℕ) [NeZero m] :
    Fintype.card ((H54.Role × ProductGrid m j) ⊕
      MidHost H54.Role (ProductGrid m j) (Option (CompactExterior.Label j))) =
      compactHostFactor j * (m ^ 2) ^ j := by
  have hc : Fintype.card (ProductGrid m j) = (m ^ 2) ^ j := by simp [ZMod.card, pow_two]
  simp only [MidHost, Fintype.card_sum, Fintype.card_prod, hc, Sym2.card,
    Fintype.card_fin, Fintype.card_option, compactHostFactor]
  norm_num [Nat.choose_two_right]
  ring

theorem finite_gap_of_product_compact {ε : ℝ} {m j n : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m)
    (hn : compactHostFactor j * (m ^ 2) ^ j ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G ((m^2)^j) ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gap G := by
  classical
  exact finite_gap_of_product_with hε hε₁ hm fun I _ hi hy =>
    robust_graph_from_EHPS_scores_with hm (CompactExterior.colour hm hε)
      (fun _ _ ha hb hc => CompactExterior.mid_outside hm hε ha hb hc)
      ((compact_host_order m j).trans_le hn) I hi hy

/-- The host-count multiplier including the extra labels for linear cut survival. -/
def linearHostFactor (j : ℕ) := 25 * compactHostFactor j

theorem finite_gap_of_product_linear_mixed {ε : ℝ} {m j n : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m) (hn₀ : 100 ≤ n)
    (hn : linearHostFactor j * (m ^ 2) ^ j ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G ((n+4)/5) ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gapWithFracFour G := by
  classical
  let R := ProductGrid m j
  let T := H54.Role × R
  let H := MidHost H54.Role R (Option (CompactExterior.Label j))
  let χ := CompactExterior.colour hm hε (j := j)
  let h := productHalf m j
  let A := productSupport ε m j
  let x := (n+4)/5
  have hx : 0 < x := by dsimp [x]; omega
  have base := midpoint_host_hyp H54.roleGraph (H54.roleStep h) A h (H54.roleStep_swap h)
    (productHalf_spec hm) χ (fun _ _ ha hb hc => CompactExterior.mid_outside hm hε ha hb hc)
  have hbase : 25 * Fintype.card (T ⊕ H) ≤ n := by
    simpa only [T, R, H, compact_host_order, linearHostFactor, Nat.mul_assoc] using hn
  have hcore : Fintype.card T ≤ Fintype.card (T ⊕ H) := by simp
  have hbudget : Fintype.card (T ⊕ H) + x + Fintype.card (Fin 3) * (Fintype.card T + x) ≤ n := by
    simp only [Fintype.card_fin]
    dsimp [x]
    omega
  have proper (u v : T) (he : (H54.coreGraph h A).Adj u v) : u.1.1 ≠ v.1.1 := by
    exact H54.core_is_tripartite h A he
  apply finite_gap_of_product_for hε hε₁ hm gapWithFracFour
  intro I y hi hy hsmall
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,hcuts,_,hmixed⟩ :=
    universal_graph_of_host_scores_with_support base (fun u : T => u.1.1) 0 proper hx hbudget I hi
      hy
  exact ⟨V,fV,dV,G,hcard,hs,hconn,hcuts,hmixed hsmall⟩

theorem finite_gap_of_product_linear {ε : ℝ} {m j n : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m) (hn₀ : 100 ≤ n)
    (hn : linearHostFactor j * (m ^ 2) ^ j ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G ((n+4)/5) ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gap G := by
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,hcuts,hgap⟩ :=
    finite_gap_of_product_linear_mixed hε hε₁ hm hn₀ hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,hcuts,hgap.trans (gapWithFracFour_le_gap G)⟩

theorem finite_gap_of_product_six {ε : ℝ} {m j n : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m)
    (hn : hostFactor j * (m ^ 2) ^ j ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
      6 * (((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j) /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gap G := by
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,_,hg⟩ := finite_gap_of_product_robust hε hε₁ hm hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,hg⟩

theorem finite_gap_of_product {ε : ℝ} {m j n : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : Odd m)
    (hn : hostFactor j * (m ^ 2) ^ j ≤ n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
      ((gridSupport ε m).card : ℝ) ^ j * ((m : ℝ) ^ 2) ^ j /
        (27 * (1 + 200 / ε ^ 2 * (j : ℝ) * (m : ℝ) ^ 2)) ≤ gap G := by
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,hgap⟩ := finite_gap_of_product_six hε hε₁ hm hn
  refine ⟨V,fV,dV,G,hcard,hs,hconn,le_trans ?_ hgap⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith only [show 0 ≤ ((gridSupport ε m).card : ℝ)^j * ((m : ℝ)^2)^j by positivity]

end GapExtremal.R434.EHPS
