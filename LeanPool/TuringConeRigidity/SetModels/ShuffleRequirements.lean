/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ShuffleRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Topology.MetricSpace.Polish
public import LeanPool.TuringConeRigidity.Effective.FiniteShuffle
public import LeanPool.TuringConeRigidity.Representation.BorelGeneric

/-!
# Shuffle Requirements
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ShuffleRequirements
open FiniteShuffle GenericCoding Set

/-- The oracle realizes every bit of the finite word. -/
def Realizes (s : List Bool) (G : Oracle) : Prop :=
  Agree s.length (fun i => s.getD i false) G

theorem realizes_initial (A G : Oracle) (n : ℕ) :
    Realizes (initial A n) G ↔ Agree n A G := by
  change (∀ i, i < (initial A n).length → (initial A n).getD i false = G i) ↔ _
  simp only [prefix_length]
  constructor
  · intro h i hi
    rw [←prefix_getD A n i hi]
    exact h i hi
  · intro h i hi
    rw [prefix_getD A n i hi]
    exact h i hi

theorem getD_of_prefix {s t : List Bool} (h : s <+: t) (i : ℕ) (hi : i < s.length) :
    s.getD i false = t.getD i false := by
  obtain ⟨u,rfl⟩ := h
  simp [List.getD,List.getElem?_append,hi]

theorem realizes_mono {s t : List Bool} {G : Oracle} (h : s <+: t) (hg : Realizes t G) :
    Realizes s G := fun i hi => (getD_of_prefix h i hi).trans (hg i (lt_of_lt_of_le hi h.length_le))

theorem realizes_default (s : List Bool) : Realizes s (fun i => s.getD i false) :=
  fun _ _ => rfl

theorem realizes_isOpen (s : List Bool) : IsOpen {G | Realizes s G} := by
  have he : {G | Realizes s G} = ⋂ i : Fin s.length, {G : Oracle | G i = s.getD i false} := by
    ext G
    simp only [mem_ofPred_eq,mem_iInter]
    exact ⟨fun h i => (h i i.isLt).symm,fun h i hi => (h ⟨i,hi⟩).symm⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous (fun G : Oracle => G (i : ℕ)) := continuous_apply _
  simpa only [Set.preimage,Set.mem_singleton_iff] using
    (isOpen_discrete ({s.getD i false} : Set Bool)).preimage hc

/-- For every oracle `A`, the word ensures that the generic code realizes some word in `D`. -/
def Transfer (D : List Bool → Prop) (s : List Bool) : Prop :=
  ∀ A, ∃ t, D t ∧ ∀ G, Realizes s G → Realizes t (code A G)

theorem transfer_mono (D : List Bool → Prop) {s t : List Bool}
    (h : s <+: t) (hs : Transfer D s) : Transfer D t := by
  intro A
  obtain ⟨r,hr,hG⟩ := hs A
  exact ⟨r,hr,fun G hg => hG G (realizes_mono h hg)⟩

theorem transfer_denseOpen (D : List Bool → Prop) (hd : DenseOpen D) : DenseOpen (Transfer D) := by
  refine ⟨?_,fun _ _ h hs => transfer_mono D h hs⟩
  intro s
  let G : Oracle := fun i => s.getD i false
  obtain ⟨m,H,hnm,hGH,hb,hD⟩ := all_extension D hd (s.length+1) G
  refine ⟨initial H (2*m),?_,?_⟩
  · rw [←prefix_default s]
    apply initial_prefix (n := s.length) (m := 2*m) (by omega)
    exact hGH.mono (by omega)
  · intro A
    obtain ⟨l,hl,hDl⟩ := hD A
    refine ⟨initial (code A H) l,hDl,?_⟩
    intro K hK
    apply (realizes_initial _ _ _).mpr
    exact code_agree (fun _ _ => rfl)
      (((realizes_initial H K (2*m)).mp hK).mono (by omega))

/-- The open union of the cylinders specified by words in `D`. -/
def OpenSet (D : List Bool → Prop) : Set Oracle := {G | ∃ s, D s ∧ Realizes s G}

theorem openSet_isOpen (D : List Bool → Prop) : IsOpen (OpenSet D) := by
  have he : OpenSet D = ⋃ s : List Bool, ⋃ (_ : D s), {G | Realizes s G} := by
    ext G; simp [OpenSet]
  rw [he]
  exact isOpen_iUnion (fun s => isOpen_iUnion (fun _ => realizes_isOpen s))

theorem openSet_measurable (D : List Bool → Prop) : MeasurableSet (OpenSet D) :=
  (openSet_isOpen D).measurableSet

/-- The oracle belongs to every open set in the specified requirement family. -/
def GenericFor (D : ℕ → List Bool → Prop) (G : Oracle) : Prop := ∀ n, G ∈ OpenSet (D n)

theorem generic_transfer (D : ℕ → List Bool → Prop) (G : Oracle)
    (hg : GenericFor (fun n => Transfer (D n)) G) (A : Oracle) : GenericFor D (code A G) := by
  intro n
  obtain ⟨s,hs,hGs⟩ := hg n
  obtain ⟨t,ht,hGt⟩ := hs A
  exact ⟨t,ht,hGt G hGs⟩

/-- The finite word has a true odd-coordinate marker at an index at least `N`. -/
def OddHit (N : ℕ) (s : List Bool) : Prop :=
  ∃ i, N ≤ i ∧ 2*i+1 < s.length ∧ s.getD (2*i+1) false = true

theorem oddHit_denseOpen (N : ℕ) : DenseOpen (OddHit N) := by
  constructor
  · intro s
    let i := N+s.length
    let H : Oracle := fun j => if j < s.length then s.getD j false else true
    refine ⟨initial H (2*i+2),?_,i,by omega,by simp,?_⟩
    · rw [←prefix_default s]
      apply initial_prefix (n := s.length) (m := 2*i+2) (by dsimp [i]; omega)
      intro j hj
      simp [H,hj]
    · rw [prefix_getD _ _ _ (by omega)]
      simp [H,show ¬2*i+1<s.length by dsimp [i]; omega]
  · intro s t hst
    rintro ⟨i,hNi,hi,hb⟩
    exact ⟨i,hNi,lt_of_lt_of_le hi hst.length_le,(getD_of_prefix hst _ hi).symm.trans hb⟩

theorem infiniteOdd_of_hits (G : Oracle) (hg : GenericFor OddHit G) : InfiniteOdd G := by
  intro N
  obtain ⟨s,⟨i,hNi,hi,hb⟩,hs⟩ := hg N
  exact ⟨i,hNi,(hs _ hi).symm.trans hb⟩

/-- Combine original dense requirements, generic-code transfer requirements, and odd-marker
hitting requirements. -/
def Requirements (D : ℕ → List Bool → Prop) (n : ℕ) (s : List Bool) : Prop :=
  if (Nat.unpair n).2 = 0 then D (Nat.unpair n).1 s
  else if (Nat.unpair n).2 = 1 then Transfer (D (Nat.unpair n).1) s
  else OddHit (Nat.unpair n).1 s

theorem requirements_denseOpen (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n)) (n : ℕ) :
    DenseOpen (Requirements D n) := by
  unfold Requirements
  split
  · exact hd _
  · split
    · exact transfer_denseOpen _ (hd _)
    · exact oddHit_denseOpen _

theorem requirements_spec (D : ℕ → List Bool → Prop) (G : Oracle)
    (hg : GenericFor (Requirements D) G) :
    GenericFor D G ∧ InfiniteOdd G ∧ ∀ A, GenericFor D (code A G) := by
  have h0 : GenericFor D G := by
    intro n
    simpa [OpenSet,Requirements,Nat.unpair_pair] using hg (Nat.pair n 0)
  have h1 : GenericFor (fun n => Transfer (D n)) G := by
    intro n
    simpa [OpenSet,Requirements,Nat.unpair_pair] using hg (Nat.pair n 1)
  have h2 : GenericFor OddHit G := by
    intro n
    simpa [OpenSet,Requirements,Nat.unpair_pair] using hg (Nat.pair n 2)
  exact ⟨h0,infiniteOdd_of_hits G h2,fun A => generic_transfer D G h1 A⟩

theorem coded_dense (D : List Bool → Prop) (hd : DenseOpen D) (s : ℕ) :
    ∃ t, BorelGeneric.Ext s t ∧ D (BorelGeneric.word t) := by
  obtain ⟨u,hu,hD⟩ := hd.1 (BorelGeneric.word s ++ [false])
  obtain ⟨t,ht⟩ := BorelGeneric.word_surjective u
  refine ⟨t,⟨?_,?_⟩,by simpa [ht] using hD⟩
  · rw [ht]
    exact (List.prefix_append _ _).trans hu
  · have hl := hu.length_le
    simp only [List.length_append,List.length_singleton] at hl
    rw [ht]
    omega

theorem realizes_iff_meets (G : Oracle) (s : ℕ) :
    Realizes (BorelGeneric.word s) G ↔ BorelGeneric.Meets G s := by
  exact ⟨fun h i hi => (h i hi).symm,fun h i hi => (h i hi).symm⟩

theorem requirements_borel {X : Type*} [MeasurableSpace X]
    (D : ℕ → List Bool → Prop) (n t : ℕ) :
    MeasurableSet {_x : X | Requirements D n (BorelGeneric.word t)} := by
  by_cases h : Requirements D n (BorelGeneric.word t) <;> simp [h]

theorem borel_all_generic_selection {X : Type*} [MeasurableSpace X]
    (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n)) :
    ∃ G : X → Oracle, Measurable G ∧ ∀ x,
      GenericFor D (G x) ∧ InfiniteOdd (G x) ∧ ∀ A, GenericFor D (code A (G x)) := by
  let R : X → ℕ → ℕ → Prop := fun _ n t => Requirements D n (BorelGeneric.word t)
  have hR : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ R x n t :=
    fun _ n s => coded_dense _ (requirements_denseOpen D hd n) s
  obtain ⟨G,hG,hreq⟩ := BorelGeneric.borel_generic_selection R hR (requirements_borel D)
  refine ⟨G,hG,fun x => requirements_spec D (G x) ?_⟩
  intro n
  obtain ⟨t,ht,hGt⟩ := hreq x n
  exact ⟨BorelGeneric.word t,ht,(realizes_iff_meets _ _).mpr hGt⟩

end TuringRigidity.ShuffleRequirements

end OAI
