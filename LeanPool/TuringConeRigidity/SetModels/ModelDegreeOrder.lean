/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelDegreeOrder.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeUniverse

/-!
# Model Degree Order
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic
universe u

/-- Some oracle represented in `D` is Turing reducible to some oracle represented in `E`. -/
def degreeCodeLE (D E : ZFSet.{u}) : Prop :=
  ∃ A B : Oracle, realCode A ∈ D ∧ realCode B ∈ E ∧ Reduces A B

theorem degreeCodeLE_actual (R : ZFSet.{u}) {A B : Oracle}
    (hA : realCode A ∈ R) (hB : realCode B ∈ R) :
    degreeCodeLE (degreeCode R A) (degreeCode R B) ↔ degree A ≤ degree B := by
  constructor
  · rintro ⟨C,D,hC,hD,hCD⟩
    have heC := ((realCode_mem_degreeCode R A C).mp hC).2
    have heD := ((realCode_mem_degreeCode R B D).mp hD).2
    rw [←heC,←heD]
    exact hCD
  · intro h
    exact ⟨A,B,(realCode_mem_degreeCode R A A).mpr ⟨hA,rfl⟩,
      (realCode_mem_degreeCode R B B).mpr ⟨hB,rfl⟩,h⟩

/-- The set-coded Turing-reducibility relation on the degree classes represented in `R`. -/
noncomputable def degreeOrder (R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ D ∈ degreeUniverse R, ∃ E ∈ degreeUniverse R,
    p = ZFSet.pair D E ∧ degreeCodeLE D E) (ZFSet.prod (degreeUniverse R) (degreeUniverse R))

theorem mem_degreeOrder (R D E : ZFSet.{u}) :
    ZFSet.pair D E ∈ degreeOrder R ↔
      D ∈ degreeUniverse R ∧ E ∈ degreeUniverse R ∧ degreeCodeLE D E := by
  rw [degreeOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,D',hD,E',hE,he,hle⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hD,hE,hle⟩
  · rintro ⟨hD,hE,hle⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨D,hD,E,hE,rfl⟩,D,hD,E,hE,rfl,hle⟩

theorem degreeOrder_actual (R : ZFSet.{u}) {A B : Oracle}
    (hA : realCode A ∈ R) (hB : realCode B ∈ R) :
    ZFSet.pair (degreeCode R A) (degreeCode R B) ∈ degreeOrder R ↔ degree A ≤ degree B := by
  rw [mem_degreeOrder,degreeCodeLE_actual R hA hB]
  exact ⟨fun h => h.2.2,fun h => ⟨(mem_degreeUniverse _ _).mpr ⟨A,hA,rfl⟩,
    (mem_degreeUniverse _ _).mpr ⟨B,hB,rfl⟩,h⟩⟩

/-- The arithmetic formula defines Turing reducibility between two oracle parameters. -/
def DegreeOrderFormula (φ : Formula) : Prop := ∀ o Q z x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    e z = natSet 0 → ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.twoOracles φ o Q z x y).Eval e ↔ Reduces A B)

theorem degree_order_bounded : ∃ φ : Formula, DegreeOrderFormula.{u} φ := by
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u}
    (reduces_arith (parameter_arith 0) (parameter_arith 1))
  refine ⟨φ,?_⟩
  intro o Q z x y e ho hQ hz A B hx hy
  simpa using Formula.twoOracles_spec hφ o Q z x y e ho hQ A B hx hy 0 hz

namespace Formula
/-- Bounded formula expressing degree reducibility through representative real codes. -/
def degreeLE (φ : Formula) (o Q z D E : ℕ) : Formula :=
  .existsMem D (.existsMem (E+1) (twoOracles φ (o+2) (Q+2) (z+2) 1 0))

theorem degreeLE_spec {φ : Formula} (hφ : DegreeOrderFormula.{u} φ)
    (o Q z D E : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hD : ∀ w ∈ e D, ∃ A : Oracle, realCode A = w)
    (hE : ∀ w ∈ e E, ∃ A : Oracle, realCode A = w) :
    (degreeLE φ o Q z D E).Eval e ↔ degreeCodeLE (e D) (e E) := by
  simp only [degreeLE,Formula.Eval,cons_succ]
  constructor
  · rintro ⟨a,ha,b,hb,hle⟩
    obtain ⟨A,rfl⟩ := hD a ha
    obtain ⟨B,rfl⟩ := hE b hb
    exact ⟨A,B,ha,hb,(hφ (o+2) (Q+2) (z+2) 1 0
      (cons (realCode B) (cons (realCode A) e)) ho hQ hz A B rfl rfl).mp hle⟩
  · rintro ⟨A,B,hA,hB,hle⟩
    exact ⟨realCode A,hA,realCode B,hB,(hφ (o+2) (Q+2) (z+2) 1 0
      (cons (realCode B) (cons (realCode A) e)) ho hQ hz A B rfl rfl).mpr hle⟩

/-- Bounded formula describing membership in the set-coded degree order. -/
def degreeOrderMember (φ : Formula) (o Q z U p : ℕ) : Formula :=
  .existsMem U (.existsMem (U+1) (.conj (.orderedPair (p+2) 1 0)
    (degreeLE φ (o+2) (Q+2) (z+2) 1 0)))

theorem degreeOrderMember_spec {φ : Formula} (hφ : DegreeOrderFormula.{u} φ)
    (o Q z U p : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (R : ZFSet.{u}) (hU : e U = degreeUniverse R)
    (hR : ∀ w ∈ R, ∃ A : Oracle, realCode A = w) :
    (degreeOrderMember φ o Q z U p).Eval e ↔ e p ∈ degreeOrder R := by
  simp only [degreeOrderMember,Formula.Eval,eval_orderedPair,cons_succ,cons_zero]
  rw [hU]
  have hd (D : ZFSet.{u}) (hD : D ∈ degreeUniverse R) : ∀ w ∈ D, ∃ A : Oracle, realCode A = w := by
    obtain ⟨A,_,rfl⟩ := (mem_degreeUniverse R D).mp hD
    exact fun w hw => hR w (degreeCode_subset R A hw)
  constructor
  · rintro ⟨D,hD,E,hE,hp,hle⟩
    rw [hp,mem_degreeOrder]
    exact ⟨hD,hE,(degreeLE_spec hφ (o+2) (Q+2) (z+2) 1 0 (cons E (cons D e))
      ho hQ hz (hd D hD) (hd E hE)).mp hle⟩
  · intro hp
    obtain ⟨_,D,hD,E,hE,he,hle⟩ := ZFSet.mem_sep.mp hp
    exact ⟨D,hD,E,hE,he,(degreeLE_spec hφ (o+2) (Q+2) (z+2) 1 0 (cons E (cons D e))
      ho hQ hz (hd D hD) (hd E hE)).mpr hle⟩
end Formula

theorem internal_degreeOrder (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w) : degreeOrder R ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω
  obtain ⟨φ,hφ⟩ := degree_order_bounded.{u}
  have hU := internal_degreeUniverse M hM hT R hRM hR
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => degreeUniverse R)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hz
    exact hU
  have hs := sep_mem M hM hS (Formula.degreeOrderMember φ 1 2 3 4 0) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hU hU)
  have heq : ZFSet.sep (fun p => (Formula.degreeOrderMember φ 1 2 3 4 0).Eval (cons p e))
      (ZFSet.prod (degreeUniverse R) (degreeUniverse R)) = degreeOrder R := by
    apply ZFSet.ext; intro p
    rw [ZFSet.mem_sep,Formula.degreeOrderMember_spec hφ 1 2 3 4 0 (cons p e) rfl hQ rfl R rfl hR]
    exact ⟨And.right,fun h => ⟨(ZFSet.mem_sep.mp h).1,h⟩⟩
  exact heq ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI
