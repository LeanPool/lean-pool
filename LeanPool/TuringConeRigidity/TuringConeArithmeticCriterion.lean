/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeArithmeticCriterion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeNumerical
public import LeanPool.TuringConeRigidity.Computability.ArithmeticActions
public import LeanPool.TuringConeRigidity.TuringConePersistentExtension

/-!
# An arithmetic matrix for cone persistence

The base is specified by a column index in the original presentation. Thus the
only free real parameters are the presentation A and graph R. Extension maps
are represented by numerical program indices, rather than existential real
quantifiers. The remaining real quantifier is universal over presentations H.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeArithmeticCriterion

open Encodable EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic
open PersistentRestrictions ConePersistence ConePresentation ConeNumerical
open NumericalIdeal NumericalExtension

noncomputable section

/-- All clauses of a cone action are uniformly arithmetic. In particular,
surjectivity is restricted to columns above the base. -/
theorem action_arith {B H P : OracleFamily} (hB : ArithmeticOracle B)
    (hH : ArithmeticOracle H) (hP : ArithmeticOracle P) :
    Arith (fun O v => ConeNumerical.Action (B O v) (H O v) (fun w => P O v w = true)) := by
  let l := UniformArithmetic.left_primrec
  let r := UniformArithmetic.right_primrec
  have ht := (query_at hP (l.comp l) (Primrec₂.natPair.comp (r.comp l) r)).ex.all
  have hpAbove := query_at hP (l.comp l) (Primrec₂.natPair.comp (r.comp l) r)
  have hAbove := reduces_arith (hB.comp (l.comp l)) (columns_at hH (l.comp l) r)
  have ha := (hpAbove.imp hAbove).all.all
  have hTarget := reduces_arith (hB.comp l) (columns_at hH l r)
  have hOnto := (query_at hP (l.comp l) (Primrec₂.natPair.comp r (r.comp l))).ex
  have hs := (hTarget.imp hOnto).all
  have ho := UniformArithmetic.action_order_arith hH hP
  have hu := UniformArithmetic.action_saturated_arith hH hP
  apply (ht.and (ha.and (hs.and (ho.and hu)))).congr
  intro O v
  simp only [UniformArithmetic.left, UniformArithmetic.right, Nat.unpair_pair]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.total, h.above, h.onto, h.order, h.saturated⟩⟩

theorem graph_program {I : CountableIdeal} {a : Degree} {H Y : Oracle}
    (hH : Presented I H) (ρ : I ≃o Cone I a)
    (hr : RecursivePred Y (ConePresentation.Graph ρ hH)) :
    ∃ e : ℕ, ∀ v, tableOracle Y e v = true ↔ ConePresentation.Graph ρ hH v := by
  obtain ⟨d, hd⟩ := TableIndices.reduces_represents (graphOracle_reduces hH ρ hr)
  have hd' : TableIndices.Represents Y (IndexMatrix.machine (encode d)) (graphOracle hH ρ) := by
    simpa only [IndexMatrix.machine_encode] using hd
  refine ⟨encode d, fun v => ?_⟩
  rw [tableOracle_eq hd']
  simp [graphOracle]

/-- Every coded jump-closed ideal extension admits an arithmetic action onto the prescribed
principal cone. -/
def Criterion (A R : Oracle) (k : ℕ) : Prop :=
  ∀ H : Oracle, JumpCode H → Includes A H →
    ∃ e : ℕ, ConeNumerical.Action (columns A k) H
      (fun v => tableOracle (iterate H 11) e v = true) ∧
      Compatible A H (fun v => R v = true)
        (fun v => tableOracle (iterate H 11) e v = true)

/-- The numerical criterion is equivalent to the original persistence
property, not an additional hypothesis on persistent maps. -/
theorem persistent_iff {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (k : ℕ) (ρ : I ≃o Cone I (degree (columns A k)))
    (hza : degreeJump (degree (columns A k)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ ConePresentation.Graph ρ hA v) :
    ConePersistence.Persistent I ρ ↔ Criterion A R k := by
  constructor
  · intro hp H hc hi
    let J := decode H hc
    have hH : Presented J H := decoded_presentation H hc
    have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hH).mp hi
    obtain ⟨σ, he, hpσ⟩ := ConePersistentExtension.persistent_extension I J ρ hp hza hIJ
      (decoded_closed H hc)
    obtain ⟨e, hg⟩ := graph_program hH σ
      (ConePersistentLocality.arithmetic_presentation_of_persistent σ hpσ hH (hIJ hza)).2
    refine ⟨e, (ConeNumerical.action_congr hg).mpr (action_of_iso hH σ), ?_⟩
    intro i j n m hr hp hin
    exact ((ConeNumerical.compatible_iff hA hH hIJ ρ σ).mpr he) i j n m
      ((hR _).mp hr) ((hg _).mp hp) hin
  · intro hc x
    let J := JumpIdeal.generated (degree A ⊔ x)
    have hIJ : I.carrier ⊆ J.carrier := by
      intro y hy
      exact J.lower ((presentation_bound hA hy).trans le_sup_left) (JumpIdeal.includes _)
    have hx : x ∈ J.carrier := J.lower le_sup_right (JumpIdeal.includes _)
    obtain ⟨H, hH⟩ := ConePresentation.presentation_exists J
    have hj : JumpCode H := code_of_ideal hH (JumpIdeal.closed _)
    have hi : Includes A H := (includes_iff hA hH).mpr hIJ
    obtain ⟨e, ha, hcompat⟩ := hc H hj hi
    obtain ⟨σ, hσ⟩ := ConeNumerical.reconstruct hH ha
    refine ⟨J, hIJ, σ, hx, (ConeNumerical.compatible_iff hA hH hIJ ρ σ).mp ?_⟩
    intro i j n m hr hp hin
    exact hcompat i j n m ((hR _).mpr hr) ((hσ _).mpr hp) hin

/-- The arithmetic matrix expressing the cone persistence criterion for a test-extension
oracle. -/
def Matrix (O : Oracles) (k : ℕ) : Prop :=
  JumpCode (O 2) → Includes (O 0) (O 2) →
    ∃ e : ℕ, ConeNumerical.Action (columns (O 0) k) (O 2)
      (fun v => tableOracle (iterate (O 2) 11) e v = true) ∧
      Compatible (O 0) (O 2) (fun v => O 1 v = true)
        (fun v => tableOracle (iterate (O 2) 11) e v = true)

theorem matrix_arith : Arith Matrix := by
  have hA := parameter_arith 0
  have hR := parameter_arith 1
  have hH := parameter_arith 2
  have hB := column_arith hA Primrec.id
  let l := UniformArithmetic.left_primrec
  let r := UniformArithmetic.right_primrec
  have hP := tableOracle_arith (iterate_arith (hH.comp l) 11) r
  have he := ((action_arith (hB.comp l) (hH.comp l) hP).and
    (UniformArithmetic.compatible_arith (hA.comp l) (hH.comp l) (hR.comp l) hP)).ex
  exact ((jumpCode_arith hH).imp ((includes_arith hA hH).imp he)).congr
    (fun _ _ => by simp only [Matrix, UniformArithmetic.left, UniformArithmetic.right,
      Nat.unpair_pair, id_eq])

end
end OAI.TuringRigidity.ConeArithmeticCriterion
