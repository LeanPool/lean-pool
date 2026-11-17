/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/PairGenericSelection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericTopology

/-!
# Pair Generic Selection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PairGenericSelection
open FiniteShuffle ShuffleRequirements GenericTopology GenericCoding Set

/-- Extract the even column when the flag is false, and the odd column when it is true. -/
def column (b : Bool) (G : Oracle) : Oracle :=
  fun n => if b then G (2*n+1) else G (2*n)

theorem column_agree (b : Bool) {n : ℕ} {G H : Oracle} (h : Agree (2 * n) G H) :
    Agree n (column b G) (column b H) := by
  intro i hi
  cases b <;> simp only [column,Bool.false_eq_true,↓reduceIte] <;> apply h <;> omega

theorem column_measurable (b : Bool) : Measurable (column b) := by
  apply Measurable.of_eval
  intro n
  cases b <;> exact measurable_pi_apply _

/-- A finite word ensures that the selected column realizes some word in `D`. -/
def ColumnRequirement (D : List Bool → Prop) (b : Bool) (s : List Bool) : Prop :=
  ∃ t, D t ∧ ∀ G, Realizes s G → Realizes t (column b G)

theorem column_denseOpen (D : List Bool → Prop) (hd : DenseOpen D) (b : Bool) :
    DenseOpen (ColumnRequirement D b) := by
  constructor
  · intro s
    let G : Oracle := fun i => s.getD i false
    let n := s.length+1
    obtain ⟨t,ht,hD⟩ := hd.1 (initial (column b G) n)
    let T : Oracle := fun i => t.getD i false
    let H : Oracle := if b then join (column false G) T else join T (column true G)
    have hcol : column b H = T := by
      funext i
      cases b <;> simp [H,column]
    have hl : n ≤ t.length := by simpa only [prefix_length] using ht.length_le
    have hpair : Agree (2*n) G H := by
      apply agree_of_columns
      · intro i hi
        cases b
        · simpa [H,column,T] using agree_of_prefix ht i hi
        · simp [H,column]
      · intro i hi
        cases b
        · simp [H,column]
        · simpa [H,column,T] using agree_of_prefix ht i hi
    refine ⟨initial H (2*t.length),?_,t,hD,?_⟩
    · rw [←prefix_default s]
      exact initial_prefix (n := s.length) (m := 2*t.length) (by dsimp [n] at hl; omega)
        (hpair.mono (by dsimp [n]; omega))
    · intro K hK
      have hc := column_agree b ((realizes_initial H K (2*t.length)).mp hK)
      rw [hcol] at hc
      exact hc
  · intro s t hst
    rintro ⟨u,hD,hu⟩
    exact ⟨u,hD,fun G hG => hu G (realizes_mono hst hG)⟩

/-- Enumerate both column projections of the dense-open requirement family. -/
def PairRequirements (D : ℕ → List Bool → Prop) (n : ℕ) : List Bool → Prop :=
  ColumnRequirement (Requirements D (n/2)) (decide (n%2 = 1))

theorem pair_requirements_denseOpen (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n))
    (n : ℕ) : DenseOpen (PairRequirements D n) :=
  column_denseOpen _ (requirements_denseOpen D hd _) _

theorem pair_requirements_spec (D : ℕ → List Bool → Prop) (G : Oracle)
    (hg : GenericFor (PairRequirements D) G) (b : Bool) :
    GenericFor D (column b G) ∧ InfiniteOdd (column b G) ∧
      ∀ A, GenericFor D (code A (column b G)) := by
  apply requirements_spec
  intro n
  have h : G ∈ OpenSet (ColumnRequirement (Requirements D n) b) := by
    cases b
    · simpa [OpenSet,PairRequirements] using hg (2*n)
    · simpa [OpenSet,PairRequirements,Nat.add_div] using hg (2*n+1)
  obtain ⟨s,⟨t,ht,hcol⟩,hs⟩ := h
  exact ⟨t,ht,hcol G hs⟩

theorem borel_pair_selection {X : Type*} [MeasurableSpace X]
    (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n))
    (R : X → ℕ → ℕ → Prop)
    (hRd : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ R x n t)
    (hRm : ∀ n t, MeasurableSet {x | R x n t}) :
    ∃ Z : X → Oracle, Measurable Z ∧
      (∀ x b, GenericFor D (column b (Z x)) ∧ InfiniteOdd (column b (Z x)) ∧
        ∀ A, GenericFor D (code A (column b (Z x)))) ∧
      ∀ x n, ∃ t, R x n t ∧ BorelGeneric.Meets (Z x) t := by
  obtain ⟨Z,hZ,hreq⟩ := borel_selection_with_requirements (PairRequirements D)
    (pair_requirements_denseOpen D hd) R hRd hRm
  exact ⟨Z,hZ,fun x b => pair_requirements_spec D (Z x) (hreq x).1.1 b,
    fun x => (hreq x).2⟩

end TuringRigidity.PairGenericSelection

end OAI
