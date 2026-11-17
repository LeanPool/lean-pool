/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConePresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeEnumeration
public import LeanPool.TuringConeRigidity.TuringConePersistence
public import LeanPool.TuringConeRigidity.SetModels.EnumerationConstruction
public import LeanPool.TuringConeRigidity.Computability.JumpIdeal

/-!
# Arithmetic presentations of partial cone isomorphisms

We prove the enumeration/presentation implication separately from the missing
locality theorem. If a partial cone isomorphism extends to the ideal of degrees
arithmetic in a presentation real `H`, its entire index graph is arithmetic in
`H`. The extension is an explicit hypothesis, not inferred from persistence.

The more general bound theorem works whenever one oracle bounds both `H` and
the image of `H'`. No arbitrary choices of infinitely many program indices are
used to produce the graph: one transported enumeration is decoded uniformly.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePresentation

open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation
open BoundedDecoding EnumerationConstruction ConeIdealCoding

noncomputable section

def idealEntry {J : DegreeIdeal} (H : Oracle) (hH : degree H ∈ J.carrier) (n : ℕ) : J :=
  ⟨degree (columns H n), J.lower (CodingExtraction.column_projection_reduces H n) hH⟩

def IdealGraph {J : DegreeIdeal} {a : J} (ρ : J ≃o Set.Ici a)
    (H : Oracle) (hH : degree H ∈ J.carrier) (v : ℕ) : Prop :=
  image ρ (idealEntry H hH (Nat.unpair v).1) = degree (columns H (Nat.unpair v).2)

/-- A bound on the image of the coding bound yields one arithmetic graph for
all inputs of the presented sequence, not merely pointwise arithmetic values. -/
theorem graph_sigma_of_bound {J : DegreeIdeal} {a : J} (ρ : J ≃o Set.Ici a)
    (H : Oracle) (hH : degree H ∈ J.carrier)
    (hz : Reduces (jump FixedArithmetic.zero) H)
    (b : J) (hb : b.val = degree (jump H))
    (Y : Oracle) (hHY : Reduces H Y) (hbound : image ρ b ≤ degree Y) :
    Sigma Y 5 (IdealGraph ρ H hH) ∧
      RecursivePred (iterate Y 5) (IdealGraph ρ H hH) := by
  obtain ⟨c, hout, hS, hP⟩ := enumeration_exists H hz
  obtain ⟨d, hdout, hdS, hdP⟩ := ConeEnumeration.transport_enumeration ρ c b
    (hb.symm ▸ hS) (hb.symm ▸ hP) (idealEntry H hH)
    (fun n => by simp only [idealEntry, hout])
  have hg := ConeEnumeration.graph_sigma ((base_le_image ρ b).trans hbound)
    hHY d (hdS.mono hbound) (hdP.mono hbound)
  have h : Sigma Y 5 (IdealGraph ρ H hH) := hg.congr (fun v => by
    simp only [hdout, IdealGraph])
  exact ⟨h, form_recursive h⟩

theorem reduces_iterate (H : Oracle) (n : ℕ) : Reduces H (iterate H n) := by
  induction n with
  | zero => exact reduces_refl H
  | succ n ih => exact reduces_trans ih (reduces_jump _)

/-- The ordinary ideal consisting of all degrees arithmetic in `H`. -/
def arithmeticIdeal (H : Oracle) : DegreeIdeal :=
  PersistentLocality.ideal (JumpIdeal.generated (degree H))

theorem self_mem_arithmeticIdeal (H : Oracle) : degree H ∈ (arithmeticIdeal H).carrier :=
  JumpIdeal.includes _

/-- Membership of the image bound in the arithmetic ideal supplies some finite
jump bound. This statement does not assert that a given partial map extends to
this ideal. -/
theorem graph_arithmetic_on_jump_ideal (H : Oracle)
    (hz : Reduces (jump FixedArithmetic.zero) H)
    (a : arithmeticIdeal H) (σ : arithmeticIdeal H ≃o Set.Ici a) :
    ∃ n, Sigma (iterate H n) 5 (IdealGraph σ H (self_mem_arithmeticIdeal H)) ∧
      RecursivePred (iterate H (n + 5)) (IdealGraph σ H (self_mem_arithmeticIdeal H)) := by
  let b : arithmeticIdeal H := ⟨degree (jump H),
    (JumpIdeal.closed (degree H)) _ (self_mem_arithmeticIdeal H)⟩
  have hm := (σ b).val.property
  change ∃ n, image σ b ≤ GlobalLocality.degreeIterate (degree H) n at hm
  obtain ⟨n, hn⟩ := hm
  rw [GlobalLocality.degreeIterate_degree] at hn
  obtain ⟨h, hr⟩ := graph_sigma_of_bound σ H (self_mem_arithmeticIdeal H) hz b rfl
    (iterate H n) (reduces_iterate H n) hn
  exact ⟨n, h, hr⟩

open PersistentRestrictions

/-- `H` presents an ideal by the degrees of its columns; repetitions are allowed. -/
def Presented (I : CountableIdeal) (H : Oracle) : Prop :=
  ∀ x, x ∈ I.carrier ↔ ∃ k, degree (columns H k) = x

def presentationEntry {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) (n : ℕ) : I :=
  ⟨degree (columns H n), (hpres _).mpr ⟨n, rfl⟩⟩

def Graph {I : CountableIdeal} {a : Degree} (ρ : I ≃o ConePersistence.Cone I a)
    {H : Oracle} (hpres : Presented I H) (v : ℕ) : Prop :=
  (ρ (presentationEntry hpres (Nat.unpair v).1)).val = degree (columns H (Nat.unpair v).2)

theorem presentation_bound {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) {x : Degree} (hx : x ∈ I.carrier) : x ≤ degree H := by
  obtain ⟨k, rfl⟩ := (hpres x).mp hx
  exact CodingExtraction.column_projection_reduces H k

theorem presentation_subset_generated {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) : I.carrier ⊆ (JumpIdeal.generated (degree H)).carrier :=
  fun _ hx => (JumpIdeal.generated (degree H)).lower (presentation_bound hpres hx)
    (JumpIdeal.includes _)

theorem base_mem {I : CountableIdeal} {a : Degree}
    (ρ : I ≃o ConePersistence.Cone I a) : a ∈ I.carrier := by
  obtain ⟨x, hx⟩ := I.nonempty
  exact I.lower (ρ ⟨x, hx⟩).property.2 (ρ ⟨x, hx⟩).property.1

/-- Bridge the two existing representations of an ideal and its upper cone. -/
def coneBridge (I : CountableIdeal) (a : Degree) (ha : a ∈ I.carrier) :
    ConePersistence.Cone I a ≃o
      Set.Ici (⟨a, ha⟩ : PersistentLocality.ideal I) where
  toFun y := ⟨⟨y.val, y.property.1⟩, Set.mem_Ici.mpr y.property.2⟩
  invFun y := ⟨y.val.val, y.val.property, Set.mem_Ici.mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def lift {I : CountableIdeal} {a : Degree} (ρ : I ≃o ConePersistence.Cone I a)
    (ha : a ∈ I.carrier) : PersistentLocality.ideal I ≃o
      Set.Ici (⟨a, ha⟩ : PersistentLocality.ideal I) :=
  (PersistentLocality.bridge I).symm.trans (ρ.trans (coneBridge I a ha))

/-- The exact extension obligation still needed from the cone-locality and
persistence argument. This is not asserted to follow from `Persistent`. -/
def HasJumpIdealExtension {I : CountableIdeal} {a : Degree}
    (ρ : I ≃o ConePersistence.Cone I a) {H : Oracle} (hpres : Presented I H) : Prop :=
  ∃ σ : (JumpIdeal.generated (degree H)) ≃o
    ConePersistence.Cone (JumpIdeal.generated (degree H)) a,
    ConePersistence.Extends (presentation_subset_generated hpres) ρ σ

/-- Arithmetic presentation of a partial cone isomorphism, once it extends to
all degrees arithmetic in its presentation real. The graph is uniform in both
indices. A proof of persistence-to-extension is a separate remaining theorem. -/
theorem arithmetic_presentation_of_jump_extension {I : CountableIdeal} {a : Degree}
    (ρ : I ≃o ConePersistence.Cone I a) {H : Oracle} (hpres : Presented I H)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hext : HasJumpIdealExtension ρ hpres) :
    ∃ n, Sigma (iterate H n) 5 (Graph ρ hpres) ∧
      RecursivePred (iterate H (n + 5)) (Graph ρ hpres) := by
  obtain ⟨σ, he⟩ := hext
  have ha := base_mem σ
  let τ := lift σ ha
  obtain ⟨n, hg, hr⟩ := graph_arithmetic_on_jump_ideal H (presentation_bound hpres hz)
    ⟨a, ha⟩ τ
  have hgraph : ∀ v, IdealGraph τ H (self_mem_arithmeticIdeal H) v ↔ Graph ρ hpres v := by
    intro v
    change (σ ⟨degree (columns H (Nat.unpair v).1), _⟩).val =
      degree (columns H (Nat.unpair v).2) ↔ _
    exact Iff.of_eq (congrArg (fun x : Degree => x = degree (columns H (Nat.unpair v).2))
      (he (presentationEntry hpres (Nat.unpair v).1)))
  have h := hg.congr hgraph
  exact ⟨n, h, Form.congr (n := 0) (s := true) hr hgraph⟩

end
end OAI.TuringRigidity.ConePresentation
