/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ParameterFreeOrdinalStage.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericStage

/-!
# Parameter Free Ordinal Stage
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

theorem parameter_free_ordinal_stage :
    ∃ p : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ o : Ordinal.{u}, o.toZFSet ∈ M →
        ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
          ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
            o.toZFSet ∈ level (groundReals M) δ ∧ level (groundReals M) o ∈ level (groundReals M)
              δ ∧
            groundReals M ∈ level (groundReals M) δ ∧
            ∀ A ∈ level (groundReals M) δ,
              p.Sat (level (groundReals M) δ : Set ZFSet)
                (cons A (cons o.toZFSet (fun _ => groundReals M))) ↔ A = level (groundReals M) o
                  := by
  obtain ⟨p,hp⟩ := NumericSyntax.stage_formula.{u}
  refine ⟨p,?_⟩
  intro M hM hT o ho
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  obtain ⟨B,hBN,hB,hcover⟩ := internal_finite_natural_graph_bound N C.transitive C.pairing C.union
    C.power C.separation C.omega_mem
  let e := cons ZFSet.omega (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons B (fun _ => R)))
  have he (i : ℕ) (_hi : i < 4) : InRelativeModel M R (e i) := by
    apply (mem_relativeModel M R _ hM hT hR).mp
    rcases i with _|_|_|i
    · exact C.omega_mem
    · exact C.prod_mem C.omega_mem C.omega_mem
    · exact hBN
    · exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
  obtain ⟨β,hβ,hβe⟩ := finite_parameters_in_relative_level M R hM hT e 4 he
  obtain ⟨α,hα,hαspec⟩ := seed_bound_stage_at_levels M o.toZFSet hM hT
    ((ground_relativeModel_ordinal_iff M hM hT o).mpr ho)
  refine ⟨max α β,internal_ordinal_max M hα hβ,?_⟩
  intro δ hδ hle
  have hin (i : ℕ) (hi : i < 4) : e i ∈ level R δ :=
    level_mono R ((le_max_right α β).trans hle) (hβe i hi)
  have hL := level_transitive R δ
  have hsub : level R δ ⊆ N := fun x hx => (mem_relativeModel M R x hM hT hR).mpr ⟨δ,hδ,hx⟩
  have hBL : PowerBound (level R δ) (ZFSet.prod ZFSet.omega ZFSet.omega) B :=
    PowerBound.between hB hL hsub (hin 2 (by decide))
  have hfin (f : ℕ → ℕ) (k : ℕ) : finiteNaturalGraph f k ∈ level R δ :=
    hL B (hin 2 (by decide)) _ (hcover f k)
  obtain ⟨hoL,hAL,hstage⟩ := hαspec δ hδ ((le_max_left α β).trans hle)
  refine ⟨hoL,hAL,hin 3 (by decide),?_⟩
  intro A hA
  have hv : ∀ i, cons A (cons o.toZFSet (fun _ => R)) i ∈ level R δ := by
    intro i; rcases i with _|_|i
    · exact hA
    · exact hoL
    · exact hin 3 (by decide)
  exact (hp (level R δ) hL (hin 0 (by decide)) (hin 1 (by decide)) hfin
    ⟨B,hin 2 (by decide),hBL⟩ _ hv).trans (hstage A)

end TuringRigidity.RelativeConstructible

end OAI
