/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeInternalPersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePersistenceAbsoluteness

/-!
# Direct internal persistence for real-coded two-cone maps

Every internal real must have an extension whose presentation and graph are
also internal. The extension ideal need not be jump-closed, and its map is
not assumed persistent. Arithmetic restriction converts these witnesses to
the checked matrix. Conversely persistent extensions and real closure supply
the witnesses. Native ZFSet graphs and forcing extensions remain separate.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeInternalPersistence

open EncodedForcing OracleJump UniformArithmetic PersistentRestrictions
open ConePersistence (Cone)
open ConePresentation (Presented)
open TwoConePresentation (RawGraph)
open NumericalIdeal NumericalExtension
open BoundedSetTheory TransitiveNameModel SetModelReals
open TwoConePersistenceAbsoluteness

universe u
noncomputable section

def HasExtensions (M : Set Oracle) (A R : Oracle) (k : ℕ) : Prop :=
  ∀ X ∈ M, ∃ H ∈ M, ∃ S ∈ M,
    ArithmeticPersistence.IdealCode H ∧ Includes A H ∧
    (∃ n, degree X = degree (columns H n)) ∧
    TwoConeNumerical.Action (columns A (Nat.unpair k).1)
      (columns A (Nat.unpair k).2) H (fun v => S v = true) ∧
    Compatible A H (fun v => R v = true) (fun v => S v = true)

/-- Only jump closure is needed in this direction; no intermediate map is
assumed persistent, and every chosen witness is explicitly in the collection. -/
theorem matrix_of_extensions {M : Set Oracle}
    (hjump : ∀ H ∈ M, jump H ∈ M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A) (k : ℕ)
    (ρ : Cone I (degree (columns A (Nat.unpair k).1)) ≃o
      Cone I (degree (columns A (Nat.unpair k).2)))
    (hza : degreeJump (degree (columns A (Nat.unpair k).1)) ∈ I.carrier)
    (hzb : degreeJump (degree (columns A (Nat.unpair k).2)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ RawGraph ρ A v)
    (hp : HasExtensions M A R k) :
    ∀ H ∈ M, TwoConeArithmeticCriterion.Matrix (ArithmeticPersistence.parameters A R H) k := by
  intro H hHM hc hi
  let J := decode H hc
  have hH : Presented J H := decoded_presentation H hc
  have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hH).mp hi
  obtain ⟨F, _, S, _, hFcode, hiF, hn, hact, hcompat⟩ := hp (jump H) (hjump H hHM)
  let K := ArithmeticPersistence.idealOfCode F hFcode
  have hF : Presented K F := fun _ => Iff.rfl
  have hIK : I.carrier ⊆ K.carrier := (includes_iff hA hF).mp hiF
  obtain ⟨τ, hτ⟩ := TwoConeNumerical.reconstruct hF hact
  have he : TwoConePersistence.Extends hIK ρ τ := by
    apply (TwoConeNumerical.compatible_iff hA hF hIK ρ τ).mp
    intro i j n m hr hs hin
    exact hcompat i j n m ((hR _).mpr hr) ((hτ _).mpr hs) hin
  have hHK : degree (jump H) ∈ K.carrier := by
    obtain ⟨n, hn⟩ := hn
    exact (hF _).mpr ⟨n, hn.symm⟩
  have hJK : J.carrier ⊆ K.carrier := fun x hx =>
    K.lower ((ConePresentation.presentation_bound hH hx).trans (reduces_jump H)) hHK
  obtain ⟨σ, hρ, hστ⟩ := TwoConePersistentLocality.restrict_extension ρ τ hIK he
    hza hzb hIJ hJK (decoded_closed H hc)
  have hr := (TwoConePresentation.raw_graph_arithmetic_of_extension σ τ hJK hστ hH
    (hIJ hza) (hIJ hzb) hHK).2
  obtain ⟨e, hg⟩ := TwoConeArithmeticCriterion.graph_program σ hr
  refine ⟨e, (TwoConeNumerical.action_congr hg).mpr (TwoConeNumerical.action_of_iso hH σ), ?_⟩
  intro i j n m hr hs hin
  exact ((TwoConeNumerical.compatible_iff hA hH hIJ ρ σ).mpr hρ) i j n m
    ((hR _).mp hr) ((hg _).mp hs) hin

/-- Direct internal witnesses agree with ambient persistence of the actual map. -/
theorem internal_extensions_iff_persistent (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (hAM : A ∈ reals M) (hRM : R ∈ reals M) (k : ℕ)
    (ρ : Cone I (degree (columns A (Nat.unpair k).1)) ≃o
      Cone I (degree (columns A (Nat.unpair k).2)))
    (hza : degreeJump (degree (columns A (Nat.unpair k).1)) ∈ I.carrier)
    (hzb : degreeJump (degree (columns A (Nat.unpair k).2)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ RawGraph ρ A v) :
    HasExtensions (reals M) A R k ↔ TwoConePersistence.Persistent I ρ := by
  let C := ArithmeticTree.sourceContext M hM hT
  have hclosed := SetModelSyntax.realClosure C
  constructor
  · intro hp
    apply (internal_criterion_iff_persistent M hM hT hA hAM hRM k ρ hza hzb hR).mp
    exact matrix_of_extensions (fun H hH => hclosed.jump hH) hA k ρ hza hzb hR hp
  · intro hp X hX
    obtain ⟨H, hH, S, hS, hc, hi, hn, ha, he⟩ :=
      TwoConeRealClosure.extension_witnesses hclosed hA hAM ρ hp hza hzb hR hX
    exact ⟨H, hH, S, hS, ⟨hc.lower, hc.join⟩, hi, hn, ha, he⟩

/-- Comparison of suitable models, with no common-real-set assumption. -/
theorem internal_extensions_comparison (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (hAM : A ∈ reals M) (hAN : A ∈ reals N)
    (hRM : R ∈ reals M) (hRN : R ∈ reals N) (k : ℕ)
    (ρ : Cone I (degree (columns A (Nat.unpair k).1)) ≃o
      Cone I (degree (columns A (Nat.unpair k).2)))
    (hza : degreeJump (degree (columns A (Nat.unpair k).1)) ∈ I.carrier)
    (hzb : degreeJump (degree (columns A (Nat.unpair k).2)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ RawGraph ρ A v) :
    HasExtensions (reals M) A R k ↔ HasExtensions (reals N) A R k :=
  (internal_extensions_iff_persistent M hM hTM hA hAM hRM k ρ hza hzb hR).trans
    (internal_extensions_iff_persistent N hN hTN hA hAN hRN k ρ hza hzb hR).symm

end
end OAI.TuringRigidity.TwoConeInternalPersistence
