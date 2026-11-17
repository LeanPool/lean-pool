/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeArithmeticCriterion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeNumerical
public import LeanPool.TuringConeRigidity.Computability.ArithmeticPersistence

/-!
# Natural-number indices for extensions between two cones

The natural k pairs the indices of the source and target base columns.
For each larger presentation H the eleven-jump graph is specified by one
machine index e in Nat, with oracle H^(11). No existential real quantifier
is used for an extension graph in the criterion or its arithmetic matrix.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeArithmeticCriterion

open Encodable EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic
open PersistentRestrictions NumericalIdeal NumericalExtension
open ConePersistence (Cone)
open ConePresentation (Presented)
open TwoConePresentation (RawGraph)

noncomputable section

/-- Domain, range, order, and saturation are all arithmetic index conditions. -/
theorem action_arith {B C H P : OracleFamily} (hB : ArithmeticOracle B)
    (hC : ArithmeticOracle C) (hH : ArithmeticOracle H) (hP : ArithmeticOracle P) :
    Arith (fun O v => TwoConeNumerical.Action (B O v) (C O v) (H O v)
      (fun w => P O v w = true)) := by
  let l := UniformArithmetic.left_primrec
  let r := UniformArithmetic.right_primrec
  have hSource := reduces_arith (hB.comp l) (columns_at hH l r)
  have hOutputs := (query_at hP (l.comp l) (Primrec₂.natPair.comp (r.comp l) r)).ex
  have ht := (hSource.imp hOutputs).all
  have hpAbove := query_at hP (l.comp l) (Primrec₂.natPair.comp (r.comp l) r)
  have hInput := reduces_arith (hB.comp (l.comp l)) (columns_at hH (l.comp l) (r.comp l))
  have hOutput := reduces_arith (hC.comp (l.comp l)) (columns_at hH (l.comp l) r)
  have ha := (hpAbove.imp (hInput.and hOutput)).all.all
  have hTarget := reduces_arith (hC.comp l) (columns_at hH l r)
  have hOnto := (query_at hP (l.comp l) (Primrec₂.natPair.comp r (r.comp l))).ex
  have hs := (hTarget.imp hOnto).all
  let c := l.comp (l.comp (l.comp l))
  let n := r.comp (l.comp (l.comp l))
  let m := r.comp (l.comp l)
  let n' := r.comp l
  let m' := r
  have hp := query_at hP c (Primrec₂.natPair.comp n m)
  have hq := query_at hP c (Primrec₂.natPair.comp n' m')
  have hl := reduces_arith (columns_at hH c n) (columns_at hH c n')
  have hr := reduces_arith (columns_at hH c m) (columns_at hH c m')
  have ho := (hp.imp (hq.imp (hl.iff hr))).all.all.all.all
  let d := l.comp (l.comp l)
  have hp' := query_at hP d (Primrec₂.natPair.comp (r.comp (l.comp l)) (r.comp l))
  have he := degree_equal_arith (columns_at hH d (r.comp l)) (columns_at hH d r)
  have hq' := query_at hP d (Primrec₂.natPair.comp (r.comp (l.comp l)) r)
  have hu := (hp'.imp (he.imp hq')).all.all.all
  apply (ht.and (ha.and (hs.and (ho.and hu)))).congr
  intro O v
  simp only [UniformArithmetic.left, UniformArithmetic.right, Nat.unpair_pair]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.total, h.above, h.onto, h.order, h.saturated⟩⟩

/-- A natural-number code for a whole graph, relative to its decoding oracle. -/
theorem graph_program {I : CountableIdeal} {a b : Degree} {H Y : Oracle}
    (ρ : Cone I a ≃o Cone I b) (hr : RecursivePred Y (RawGraph ρ H)) :
    ∃ e : ℕ, ∀ v, tableOracle Y e v = true ↔ RawGraph ρ H v := by
  obtain ⟨d, hd⟩ := TableIndices.reduces_represents (TwoConeNumerical.graphOracle_reduces ρ hr)
  have hd' : TableIndices.Represents Y (IndexMatrix.machine (encode d))
      (TwoConeNumerical.graphOracle ρ H) := by
    simpa only [IndexMatrix.machine_encode] using hd
  refine ⟨encode d, fun v => ?_⟩
  rw [tableOracle_eq hd']
  exact TwoConeNumerical.graphOracle_true ρ H v

def Criterion (A R : Oracle) (k : ℕ) : Prop :=
  ∀ H : Oracle, JumpCode H → Includes A H →
    ∃ e : ℕ, TwoConeNumerical.Action (columns A (Nat.unpair k).1)
      (columns A (Nat.unpair k).2) H (fun v => tableOracle (iterate H 11) e v = true) ∧
      Compatible A H (fun v => R v = true)
        (fun v => tableOracle (iterate H 11) e v = true)

/-- No arithmetic-extension hypothesis is added: persistence supplies it. -/
theorem persistent_iff {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (k : ℕ) (ρ : Cone I (degree (columns A (Nat.unpair k).1)) ≃o
      Cone I (degree (columns A (Nat.unpair k).2)))
    (hza : degreeJump (degree (columns A (Nat.unpair k).1)) ∈ I.carrier)
    (hzb : degreeJump (degree (columns A (Nat.unpair k).2)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ RawGraph ρ A v) :
    TwoConePersistence.Persistent I ρ ↔ Criterion A R k := by
  constructor
  · intro hp H hc hi
    let J := decode H hc
    have hH : Presented J H := decoded_presentation H hc
    have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hH).mp hi
    obtain ⟨σ, he, hpσ⟩ := TwoConePersistentExtension.persistent_extension I J ρ hp
      hza hzb hIJ (decoded_closed H hc)
    obtain ⟨e, hg⟩ := graph_program σ
      (TwoConePresentation.raw_graph_arithmetic_of_persistent σ hpσ hH (hIJ hza) (hIJ hzb)).2
    refine ⟨e, (TwoConeNumerical.action_congr hg).mpr (TwoConeNumerical.action_of_iso hH σ), ?_⟩
    intro i j n m hr hp hin
    exact ((TwoConeNumerical.compatible_iff hA hH hIJ ρ σ).mpr he) i j n m
      ((hR _).mp hr) ((hg _).mp hp) hin
  · intro hc x
    let J := JumpIdeal.generated (degree A ⊔ x)
    have hIJ : I.carrier ⊆ J.carrier := by
      intro y hy
      exact J.lower ((ConePresentation.presentation_bound hA hy).trans le_sup_left)
        (JumpIdeal.includes _)
    have hx : x ∈ J.carrier := J.lower le_sup_right (JumpIdeal.includes _)
    obtain ⟨H, hH⟩ := ConePresentation.presentation_exists J
    have hj : JumpCode H := code_of_ideal hH (JumpIdeal.closed _)
    have hi : Includes A H := (includes_iff hA hH).mpr hIJ
    obtain ⟨e, ha, hcompat⟩ := hc H hj hi
    obtain ⟨σ, hσ⟩ := TwoConeNumerical.reconstruct hH ha
    refine ⟨J, hIJ, σ, hx, (TwoConeNumerical.compatible_iff hA hH hIJ ρ σ).mp ?_⟩
    intro i j n m hr hp hin
    exact hcompat i j n m ((hR _).mpr hr) ((hσ _).mpr hp) hin

def Matrix (O : Oracles) (k : ℕ) : Prop :=
  JumpCode (O 2) → Includes (O 0) (O 2) →
    ∃ e : ℕ, TwoConeNumerical.Action (columns (O 0) (Nat.unpair k).1)
      (columns (O 0) (Nat.unpair k).2) (O 2)
      (fun v => tableOracle (iterate (O 2) 11) e v = true) ∧
      Compatible (O 0) (O 2) (fun v => O 1 v = true)
        (fun v => tableOracle (iterate (O 2) 11) e v = true)

theorem matrix_arith : Arith Matrix := by
  have hA := parameter_arith 0
  have hR := parameter_arith 1
  have hH := parameter_arith 2
  have hB := column_arith hA (Primrec.fst.comp Primrec.unpair)
  have hC := column_arith hA (Primrec.snd.comp Primrec.unpair)
  let l := UniformArithmetic.left_primrec
  let r := UniformArithmetic.right_primrec
  have hP := tableOracle_arith (iterate_arith (hH.comp l) 11) r
  have he := ((action_arith (hB.comp l) (hC.comp l) (hH.comp l) hP).and
    (UniformArithmetic.compatible_arith (hA.comp l) (hH.comp l) (hR.comp l) hP)).ex
  exact ((jumpCode_arith hH).imp ((includes_arith hA hH).imp he)).congr
    (fun _ _ => by simp only [Matrix, UniformArithmetic.left, UniformArithmetic.right,
      Nat.unpair_pair])

end
end OAI.TuringRigidity.TwoConeArithmeticCriterion
