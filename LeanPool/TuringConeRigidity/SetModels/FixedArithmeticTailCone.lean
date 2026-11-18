/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FixedArithmeticTailCone.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticOutputSyntax
public import LeanPool.TuringConeRigidity.CohenForcing.CohenNiceNameConstruction
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenProjectionSymmetry
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenTailTruth

/-!
# Fixed Arithmetic Tail Cone
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenFactor OracleJump TableIndices IndexMatrix
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem fixed_arithmetic_tail_cone (M C B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (x y : Name (Conditions (conditions C)))
    (hx : x.encode (label (conditions C)) ∈ M)
    (hy : y.encode (label (conditions C)) ∈ M)
    (hxfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)),
        x.val (AutomorphismName.mapFilter a H).carrier = x.val H.carrier)
    (hyfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)),
        y.val (AutomorphismName.mapFilter a H).carrier = y.val H.carrier)
    (R : Oracle) (hR : realCode R ∈ M) (d k : ℕ)
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (A X : Oracle) (hxv : x.val G.carrier = realCode A) (hyv : y.val G.carrier = realCode X)
    (hprog : Represents (iterate (join A R) k) (machine d) X)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ p ∈ G.carrier, p ≤ p₀ ∧
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        project C B hBC p ∈ (projected C B hBC H).carrier →
          ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
            Represents (iterate (join A' R) k) (machine d) X' := by
  have hc := conditions_mem M C hM hT hC
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have ht (H : GenericFilter (Conditions (conditions C))) : ⊤ ∈ H.carrier := by
    obtain ⟨q,hq⟩ := H.nonempty; exact H.upper le_top hq
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{0} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  have hcheck {z : ZFSet.{0}} (hz : z ∈ M) :
      (Name.check z : Name (Conditions (conditions C))).encode (label (conditions C)) ∈ M :=
    encoded_check_mem M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hz
  obtain ⟨φ,hφ⟩ := ExtensionArithmeticRepresentative.fixed_output_bounded d k
  let ψ : BoundedSetTheory.Formula := .conj (.subset 3 1) (.conj (.subset 5 1) φ)
  let e := push (Name.check (natSet 0)) (push (Name.check ZFSet.omega)
    (push (Name.check Q) (push x (push (Name.check (realCode R)) (fun _ => y)))))
  have he (i : ℕ) : (e i).encode (label (conditions C)) ∈ M := by
    rcases i with _|_|_|_|_|i
    · exact hcheck hz
    · exact hcheck hω
    · exact hcheck hQM
    · exact hx
    · exact hcheck hR
    · exact hy
  have hev (H : GenericFilter (Conditions (conditions C))) : (fun i => (e i).val H.carrier) =
      cons (natSet 0) (cons ZFSet.omega (cons Q
        (cons (x.val H.carrier) (cons (realCode R) (fun _ => y.val H.carrier))))) := by
    funext i; rcases i with _|_|_|_|_|i
    · exact Name.val_check _ (ht H) _
    · exact Name.val_check _ (ht H) _
    · exact Name.val_check _ (ht H) _
    · rfl
    · exact Name.val_check _ (ht H) _
    rfl
  have hspec (A' X' : Oracle) :
      φ.Eval (cons (natSet 0) (cons ZFSet.omega (cons Q
        (cons (realCode A') (cons (realCode R) (fun _ => realCode X')))))) ↔
        Represents (iterate (join A' R) k) (machine d) X' := by
    have henv : arithmeticEnv Q (push A' (push R (fun _ => X'))) 0 =
        cons (natSet 0) (cons ZFSet.omega (cons Q
          (cons (realCode A') (cons (realCode R) (fun _ => realCode X'))))) := by
      funext i; rcases i with _|_|_|_|_|i <;> rfl
    simpa only [henv,push] using hφ Q hQ (push A' (push R (fun _ => X'))) 0
  have meaning (H : GenericFilter (Conditions (conditions C))) :
      ψ.Eval (fun i => (e i).val H.carrier) ↔
        ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
          Represents (iterate (join A' R) k) (machine d) X' := by
    rw [hev H]
    simp only [ψ,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ]
    constructor
    · rintro ⟨hxs,hys,hformula⟩
      let A' := decodeReal (x.val H.carrier)
      let X' := decodeReal (y.val H.carrier)
      have hxa : x.val H.carrier = realCode A' := (realCode_decodeReal hxs).symm
      have hya : y.val H.carrier = realCode X' := (realCode_decodeReal hys).symm
      refine ⟨A',X',hxa,hya,?_⟩
      rw [hxa,hya] at hformula
      exact (hspec A' X').mp hformula
    · rintro ⟨A',X',hxa,hya,hpr⟩
      rw [hxa,hya]
      exact ⟨realCode_subset A',realCode_subset X',
        (hspec A' X').mpr hpr⟩
  have hinv : ∀ w ∈ M, ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        (ψ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a H).carrier) ↔
          ψ.Eval (fun i => (e i).val H.carrier)) := by
    intro w hw a ha hfix H hH
    rw [hev _,hev H,hxfix a hfix H,hyfix a hfix H]
  have hv := (meaning G).mpr ⟨A,X,hxv,hyv,hprog⟩
  obtain ⟨r,hr,hrφ⟩ := (internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
    (InternalCollapse.orderSet_pair _) G hG ψ e he).mp hv
  obtain ⟨p,hp,hp₀',hpr⟩ := G.directed hp₀ hr
  refine ⟨p,hp,hp₀',?_⟩
  intro H hH hpH
  exact (meaning H).mp (cone_truth_of_internal_tail_symmetry M C B hM hT hct hC hB hBC
    ψ e he hinv p (forces_mono _ e hpr hrφ) H hH ((projected_cone_iff C B hBC H p).mp hpH))

end TuringRigidity.BoundedForcing

end OAI
