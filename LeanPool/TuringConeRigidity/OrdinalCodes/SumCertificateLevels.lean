/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/SumCertificateLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.SumCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumLevels
public import LeanPool.TuringConeRigidity.Constructibility.RelativeDefCertificates
public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelOrdinals

/-!
# Sum Certificate Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem sum_certificates_at_levels (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      a.toZFSet ∈ level (groundReals M) δ ∧ b.toZFSet ∈ level (groundReals M) δ ∧
      (a+b).toZFSet ∈ level (groundReals M) δ ∧ SumCertificates (level (groundReals M) δ) a b := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  have hRep := relativeModel_sigma_replacement M R hM hT hR
  have haN := (ground_relativeModel_ordinal_iff M hM hT a).mpr ha
  have hbN := (ground_relativeModel_ordinal_iff M hM hT b).mpr hb
  obtain ⟨hd,hr,f,hf,hcert⟩ := SumCertificates.context N C hRep a b haN hbN
  have hc := (ordinal_add_relative M R hM hT hR a b haN hbN).1
  let e := cons a.toZFSet (cons b.toZFSet (cons (a+b).toZFSet
    (cons (sumDomain a.toZFSet b.toZFSet) (cons (sumRelation a.toZFSet b.toZFSet) (fun _ => f)))))
  have he (i : ℕ) : e i ∈ N := by
    rcases i with _|_|_|_|_|i
    · exact haN
    · exact hbN
    · exact hc
    · exact hd
    · exact hr
    · exact hf
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 6
    (fun i _ => (mem_relativeModel M R _ hM hT hR).mp (he i))
  refine ⟨γ,hγ,?_⟩
  intro δ hδ
  have hL (i : ℕ) (hi : i < 6) : e i ∈ level R δ := level_mono R hδ (hγe i hi)
  exact ⟨hL 0 (by omega),hL 1 (by omega),hL 2 (by omega),
    hL 3 (by omega),hL 4 (by omega),f,hL 5 (by omega),hcert⟩

end TuringRigidity.OrdinalArithmetic

end OAI
