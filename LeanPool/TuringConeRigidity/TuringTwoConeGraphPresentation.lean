/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeGraphPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePresentationCountability

/-!
# The conventional (unjoined) index graph has the same arithmetic bound

RawGraph rho H (i,j) asserts that deg(H_i) is in the source cone and its
image is deg(H_j). A source-cone test converts the joined graph to this
ordinary partial graph without increasing the five-jump decoding level.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePresentation

open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions
open IndexPresentation
open ConePersistence (Cone)

noncomputable section

def RawGraph {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (H : Oracle) (v : ℕ) : Prop :=
  ∃ x : Cone I a, x.val = degree (columns H (Nat.unpair v).1) ∧
    (ρ x).val = degree (columns H (Nat.unpair v).2)

theorem raw_graph_iff {I : CountableIdeal} {a b : Degree} {H : Oracle}
    (ρ : Cone I a ≃o Cone I b) (hpres : ConePresentation.Presented I H)
    (ha : a ∈ I.carrier) (v : ℕ) :
    RawGraph ρ H v ↔ a ≤ degree (columns H (Nat.unpair v).1) ∧ Graph ρ hpres ha v := by
  constructor
  · rintro ⟨x, hx, hy⟩
    have hb : a ≤ degree (columns H (Nat.unpair v).1) := hx ▸ x.property.2
    have he : presentationEntry hpres ha (Nat.unpair v).1 = x := by
      apply Subtype.ext
      change a ⊔ degree (columns H (Nat.unpair v).1) = x.val
      rw [sup_eq_right.mpr hb]
      exact hx.symm
    exact ⟨hb, by simpa only [Graph, he] using hy⟩
  · rintro ⟨hx, hg⟩
    exact ⟨presentationEntry hpres ha (Nat.unpair v).1, sup_eq_right.mpr hx, hg⟩

/-- Deciding whether a presented input lies in the source cone costs only
Sigma-3, hence fits inside the existing Sigma-5 graph calculation. -/
theorem source_test_sigma {a : Degree} {H Y : Oracle}
    (ha : a ≤ degree Y) (hHY : Reduces H Y) :
    Sigma Y 5 (fun v => a ≤ degree (columns H (Nat.unpair v).1)) := by
  obtain ⟨i, hi, hei⟩ := value_surjective Y a ha
  obtain ⟨idx, hidx, hrep⟩ := LocalColumnIndices.uniform_indices hHY
  have h := (le_sigma Y (Primrec.const i)
    (hidx.comp (Primrec.fst.comp Primrec.unpair))).raise.raise
  apply h.congr
  intro v
  rw [le_iff hi ((TableIndices.valid_iff_represents _ _).mpr ⟨_, hrep _⟩),
    hei, value_eq (hrep _)]

theorem raw_graph_sigma_of_graph {I : CountableIdeal} {a b : Degree} {H Y : Oracle}
    (ρ : Cone I a ≃o Cone I b) (hpres : ConePresentation.Presented I H)
    (ha : a ∈ I.carrier) (hHY : Reduces H Y) (hg : Sigma Y 5 (Graph ρ hpres ha)) :
    Sigma Y 5 (RawGraph ρ H) ∧ RecursivePred (iterate Y 5) (RawGraph ρ H) := by
  have hs := source_test_sigma ((ConePresentation.presentation_bound hpres ha).trans hHY) hHY
  have h := (hs.and hg).congr (fun v => (raw_graph_iff ρ hpres ha v).symm)
  exact ⟨h, form_recursive h⟩

/-- Ordinary partial graph, with no source join hidden in the statement. -/
theorem raw_graph_arithmetic_of_persistent {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    {H : Oracle} (hpres : ConePresentation.Presented I H)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    Sigma (iterate H 6) 5 (RawGraph ρ H) ∧
      RecursivePred (iterate H 11) (RawGraph ρ H) := by
  have ha : a ∈ I.carrier := I.lower (degree_le_jump a) hza
  exact raw_graph_sigma_of_graph ρ hpres ha (ConePresentation.reduces_iterate H 6)
    (arithmetic_presentation_of_persistent ρ hp hpres ha hza hzb).1

/-- The conventional graph is also arithmetic for an arbitrary larger extension. -/
theorem raw_graph_arithmetic_of_extension {I K : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (σ : Cone K a ≃o Cone K b)
    (hIK : I.carrier ⊆ K.carrier) (he : TwoConePersistence.Extends hIK ρ σ)
    {H : Oracle} (hpres : ConePresentation.Presented I H)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    (hH' : degree (jump H) ∈ K.carrier) :
    Sigma (iterate H 6) 5 (RawGraph ρ H) ∧
      RecursivePred (iterate H 11) (RawGraph ρ H) := by
  have ha : a ∈ I.carrier := I.lower (degree_le_jump a) hza
  exact raw_graph_sigma_of_graph ρ hpres ha (ConePresentation.reduces_iterate H 6)
    (arithmetic_presentation_of_extension ρ σ hIK he hpres ha hza hzb hH').1

end
end OAI.TuringRigidity.TwoConePresentation
