/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelPresentationSets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ColumnSetFormula
public import LeanPool.TuringConeRigidity.SetModels.DegreeSetFormula

/-!
# Model Presentation Sets
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing UniformArithmetic
universe u

theorem sourceT_real_column (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) (n : ℕ) : columns A n ∈ modelReals M :=
  sourceT_arithmetic_oracle M hM hT (column_arith (parameter_arith 0) (Primrec.const n))
    (fun _ => A) (fun _ => hA) 0

/-- The set of degree classes of the columns of `H`, represented inside `R`. -/
noncomputable def presentationSet (R : ZFSet.{u}) (H : Oracle) : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => degreeCode R (columns H n))

theorem mem_presentationSet (R : ZFSet.{u}) (H : Oracle) (D : ZFSet.{u}) :
    D ∈ presentationSet R H ↔ ∃ n, D = degreeCode R (columns H n) := by
  rw [presentationSet,ZFSet.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨n,hn.symm⟩,fun ⟨n,hn⟩ => ⟨n,hn.symm⟩⟩

namespace Formula
/-- Bounded formula describing membership in the column-degree presentation set. -/
def presentationMember (φ : Formula) (o Q z R H D : ℕ) : Formula :=
  .existsMem o (.existsMem (R+1) (.conj (columnSet (o+2) (Q+2) 1 (H+2) 0)
    (degreeSet φ (o+2) (Q+2) (z+2) (R+2) 0 (D+2))))

theorem presentationMember_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R H D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : e H = realCode A) (hc : ∀ n, realCode (columns A n) ∈ e R) :
    (presentationMember φ o Q z R H D).Eval e ↔ e D ∈ presentationSet (e R) A := by
  simp only [presentationMember,Formula.Eval,cons_succ]
  rw [ho,mem_presentationSet]
  constructor
  · rintro ⟨n,hn,B,_,hb,hd⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have heB : B = realCode (columns A n) :=
      (columnSet_spec (o+2) (Q+2) 1 (H+2) 0 (cons B (cons (natSet n) e)) ho hQ A hA n rfl).mp hb
    refine ⟨n,?_⟩
    exact (degreeSet_spec hφ (o+2) (Q+2) (z+2) (R+2) 0 (D+2)
      (cons B (cons (natSet n) e)) ho hQ hz hR (columns A n) heB).mp hd
  · rintro ⟨n,hd⟩
    refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,realCode (columns A n),hc n,?_,?_⟩
    · exact (columnSet_spec (o+2) (Q+2) 1 (H+2) 0
        (cons (realCode (columns A n)) (cons (natSet n) e)) ho hQ A hA n rfl).mpr rfl
    · exact (degreeSet_spec hφ (o+2) (Q+2) (z+2) (R+2) 0 (D+2)
        (cons (realCode (columns A n)) (cons (natSet n) e)) ho hQ hz hR (columns A n) rfl).mpr hd
end Formula

theorem internal_presentationSet (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {H : Oracle} (hH : H ∈ modelReals M) : presentationSet R H ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω
  obtain ⟨P,hPM,hP⟩ := internal_power M hM hT.powerSet hRM
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  have hφ' : DegreeEqualityFormula.{u} φ := hφ
  have hc : ∀ n, realCode (columns H n) ∈ R :=
    fun n => (hR _).mpr (sourceT_real_column M hM hT hH n)
  have hsub : presentationSet R H ⊆ P := by
    intro D hD
    obtain ⟨n,rfl⟩ := (mem_presentationSet R H D).mp hD
    exact (hP _).mpr ⟨internal_degreeCode M hM hT R hRM hRd (sourceT_real_column M hM hT hH n),
      degreeCode_subset R (columns H n)⟩
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (cons R (fun _ => realCode H))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hz
    rcases i with _ | i
    · exact hRM
    exact hH
  let B := ZFSet.sep (fun D => (Formula.presentationMember φ 1 2 3 4 5 0).Eval (cons D e)) P
  have hBM : B ∈ M := sep_mem M hM hS _ e he hPM
  have hb : B = presentationSet R H := by
    apply ZFSet.ext; intro D
    rw [ZFSet.mem_sep,Formula.presentationMember_spec hφ' 1 2 3 4 5 0 (cons D e) rfl hQ rfl hRd H
      rfl hc]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  rw [←hb]
  exact hBM

end TuringRigidity.BoundedSetTheory

end OAI
