/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeSigmaSchemas.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeSigmaReflection

/-!
# Relative Sigma Schemas
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem relativeModel_sigma_separation (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaSeparation (relativeModel M R) := by
  intro φ e he a ha
  let N := relativeModel M R
  obtain ⟨i,hi,hia,e',he',_,hcongr⟩ := relative_sigma_parameter_bound M R hM hT φ e
    (fun n => (mem_relativeModel M R _ hM hT hR).mp (he n)) a
    ((mem_relativeModel M R _ hM hT hR).mp ha)
  obtain ⟨o,ho,hio,hφ⟩ := relative_sigma_reflection M R hM hT hR i hi φ e' he' a hia
  let A := level R o
  let ψ := SentenceForm.conj (.member 0 1) ((fromSigma φ).rename parameterShift)
  have haA : a ∈ A := hio hia
  have hψ := separation_mem_definablePower A ψ (cons a e') (by
    intro n _
    cases n
    · exact haA
    · exact hio (he' _))
  let b := a.sep (fun x => φ.Realize N (cons x e))
  have eq : A.sep (fun x => ψ.Sat (A : Set ZFSet) (cons x (cons a e'))) = b := by
    apply ZFSet.ext; intro x
    simp only [b,ZFSet.mem_sep,ψ,Sat,cons_zero,cons_succ,shifted_parameters,sigma_sat]
    constructor
    · rintro ⟨_,hxa,hψ⟩
      exact ⟨hxa,(hcongr N x).mp ((hφ x hxa).mpr hψ)⟩
    · rintro ⟨hxa,hψ⟩
      exact ⟨level_transitive R o a haA x hxa,hxa,(hφ x hxa).mp ((hcongr N x).mpr hψ)⟩
  have hb : b ∈ N := by
    apply (mem_relativeModel M R b hM hT hR).mpr
    refine ⟨o+1,internal_ordinal_succ M hM hT o ho,?_⟩
    rw [level_succ,← eq]
    exact hψ
  exact ⟨b,hb,fun _ _ => ZFSet.mem_sep⟩

/-- Variable placement for a sigma-defined replacement image. -/
def replacementImageVars : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n+2 => n+3

/-- A sigma formula defining the image of a relation with its witness in the prescribed
domain. -/
def replacementImageFormula (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (SigmaFormula.andBounded (.member 0 2) (φ.rename replacementImageVars))

theorem replacementImageFormula_spec (φ : SigmaFormula) (N a y : ZFSet.{u})
    (hN : Transitive N) (ha : a ∈ N) (e : ℕ → ZFSet.{u}) :
    (replacementImageFormula φ).Realize N (cons y (cons a e)) ↔
      ∃ x ∈ a, φ.Realize N (cons y (cons x e)) := by
  simp only [replacementImageFormula,SigmaFormula.Realize,SigmaFormula.realize_andBounded,
    Formula.Realize,cons_zero,cons_succ,SigmaFormula.realize_rename]
  have eq (x : ZFSet.{u}) : (fun i => cons x (cons y (cons a e)) (replacementImageVars i)) =
      cons y (cons x e) := by
    funext i
    rcases i with _ | i
    · rfl
    rcases i with _|i <;> rfl
  simp only [eq]
  exact ⟨fun ⟨x,_,hx,hφ⟩ => ⟨x,hx,hφ⟩,
    fun ⟨x,hx,hφ⟩ => ⟨x,hN a ha x hx,hx,hφ⟩⟩

theorem relativeModel_sigma_replacement (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaReplacement (relativeModel M R) := by
  intro φ e he a ha htotal
  let N := relativeModel M R
  have hN := relativeModel_transitive M R hM
  obtain ⟨W,hW,hw⟩ := relativeModel_sigma_collection M R hM hT hR φ e he a ha
    (fun x hx => by obtain ⟨y,hy,hφ,_⟩ := htotal x hx; exact ⟨y,hy,hφ⟩)
  obtain ⟨b,hb,hbdef⟩ := relativeModel_sigma_separation M R hM hT hR
    (replacementImageFormula φ) (cons a e) (by
      intro n
      cases n
      · exact ha
      · exact he _) W hW
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy,replacementImageFormula_spec φ N a y hN ha e]
  constructor
  · exact And.right
  · rintro ⟨x,hx,hφ⟩
    obtain ⟨z,hz,hφz⟩ := hw x hx
    obtain ⟨w,hw,_,hu⟩ := htotal x hx
    have hyz : y = z := (hu y hy hφ).trans (hu z (hN W hW z hz) hφz).symm
    exact ⟨hyz ▸ hz,x,hx,hφ⟩

end TuringRigidity.RelativeConstructible

end OAI
