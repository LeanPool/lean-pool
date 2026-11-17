/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeInternalPersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePersistenceAbsoluteness

/-!
# Internal persistence witnessed by real codes

We identify the arithmetic criterion with the direct assertion that every real
in a model has a cone-extension witness whose presentation and graph are also
in that model. Extension domains here are ordinary ideals, not necessarily
jump-closed. The forward implication restricts a possibly nonpersistent
internal extension and computes its graph; the reverse implication uses the
persistent-extension theorem and arithmetic closure.

These are assertions about real codes. A native set-theoretic formula on the
model's degree objects and a global forcing-extension construction remain
separate steps.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeInternalPersistence

open EncodedForcing OracleJump UniformArithmetic PersistentRestrictions
open ConePersistence ConePresentation NumericalIdeal NumericalExtension
open BoundedSetTheory TransitiveNameModel SetModelReals
open ConePersistenceAbsoluteness

universe u
noncomputable section

/-- All extension witnesses are real codes belonging to the collection. The
extension domain need only be an ordinary ideal. -/
def HasExtensions (M : Set Oracle) (A R : Oracle) (k : ℕ) : Prop :=
  ∀ X ∈ M, ∃ H ∈ M, ∃ S ∈ M,
    ArithmeticPersistence.IdealCode H ∧ Includes A H ∧
    (∃ n, degree X = degree (columns H n)) ∧
    ConeNumerical.Action (columns A k) H (fun v => S v = true) ∧
    Compatible A H (fun v => R v = true) (fun v => S v = true)

/-- Internal extension witnesses imply the arithmetic criterion on the
collection's presentations. None of the intermediate maps is assumed
persistent. Closure under one jump is sufficient for this direction. -/
theorem matrix_of_extensions {M : Set Oracle}
    (hjump : ∀ H ∈ M, jump H ∈ M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A) (k : ℕ)
    (ρ : I ≃o Cone I (degree (columns A k)))
    (hza : degreeJump (degree (columns A k)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ ConePresentation.Graph ρ hA v)
    (hp : HasExtensions M A R k) :
    ∀ H ∈ M, ConeArithmeticCriterion.Matrix (ArithmeticPersistence.parameters A R H) k := by
  intro H hHM hc hi
  let J := decode H hc
  have hH : Presented J H := decoded_presentation H hc
  have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hH).mp hi
  obtain ⟨F, _, S, _, hFcode, hiF, hn, hact, hcompat⟩ := hp (jump H) (hjump H hHM)
  let K := ArithmeticPersistence.idealOfCode F hFcode
  have hF : Presented K F := fun _ => Iff.rfl
  have hIK : I.carrier ⊆ K.carrier := (includes_iff hA hF).mp hiF
  obtain ⟨τ, hτ⟩ := ConeNumerical.reconstruct hF hact
  have he : ConePersistence.Extends hIK ρ τ := by
    apply (ConeNumerical.compatible_iff hA hF hIK ρ τ).mp
    intro i j n m hr hs hin
    exact hcompat i j n m ((hR _).mpr hr) ((hτ _).mpr hs) hin
  have hHK : degree (jump H) ∈ K.carrier := by
    obtain ⟨n, hn⟩ := hn
    exact (hF _).mpr ⟨n, hn.symm⟩
  have hJK : J.carrier ⊆ K.carrier := fun x hx =>
    K.lower ((presentation_bound hH hx).trans (reduces_jump H)) hHK
  obtain ⟨σ, hρ, _, hr⟩ := ConePersistentRestriction.restriction ρ τ hIK he hza
    hIJ hJK (decoded_closed H hc) hH hHK
  obtain ⟨e, hg⟩ := ConeArithmeticCriterion.graph_program hH σ hr
  refine ⟨e, (ConeNumerical.action_congr hg).mpr (ConeNumerical.action_of_iso hH σ), ?_⟩
  intro i j n m hr hs hin
  exact ((ConeNumerical.compatible_iff hA hH hIJ ρ σ).mpr hρ) i j n m
    ((hR _).mp hr) ((hg _).mp hs) hin

/-- Internal persistence of real codes agrees with ambient persistence of the
actual partial cone isomorphism. SourceT is the existing source theory, not
an additional absoluteness hypothesis. -/
theorem internal_extensions_iff_persistent (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (hAM : A ∈ reals M) (hRM : R ∈ reals M) (k : ℕ)
    (ρ : I ≃o Cone I (degree (columns A k)))
    (hza : degreeJump (degree (columns A k)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ ConePresentation.Graph ρ hA v) :
    HasExtensions (reals M) A R k ↔ ConePersistence.Persistent I ρ := by
  let C := ArithmeticTree.sourceContext M hM hT
  have hclosed := SetModelSyntax.realClosure C
  constructor
  · intro hp
    apply (internal_criterion_iff_persistent M hM hT hA hAM hRM k ρ hza hR).mp
    exact matrix_of_extensions (fun H hH => hclosed.jump hH) hA k ρ hza hR hp
  · intro hp X hX
    obtain ⟨H, hH, S, hS, hc, hi, hn, ha, he⟩ :=
      ConeRealClosure.extension_witnesses hclosed hA hAM ρ hp hza hR hX
    exact ⟨H, hH, S, hS, ⟨hc.lower, hc.join⟩, hi, hn, ha, he⟩

/-- Two suitable transitive models agree on the direct real-coded extension
property, even though they may have different collections of real inputs. -/
theorem internal_extensions_comparison (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (hAM : A ∈ reals M) (hAN : A ∈ reals N)
    (hRM : R ∈ reals M) (hRN : R ∈ reals N) (k : ℕ)
    (ρ : I ≃o Cone I (degree (columns A k)))
    (hza : degreeJump (degree (columns A k)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ ConePresentation.Graph ρ hA v) :
    HasExtensions (reals M) A R k ↔ HasExtensions (reals N) A R k :=
  (internal_extensions_iff_persistent M hM hTM hA hAM hRM k ρ hza hR).trans
    (internal_extensions_iff_persistent N hN hTN hA hAN hRN k ρ hza hR).symm

end
end OAI.TuringRigidity.ConeInternalPersistence
