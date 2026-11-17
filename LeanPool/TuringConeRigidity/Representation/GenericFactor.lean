/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericFactor.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.PairGenericSelection

/-!
# Generic Factor
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericFactor
open FiniteShuffle ShuffleRequirements PairGenericSelection GenericTopology Set

def Rectangle (D : List Bool → Prop) (s t : List Bool) : Prop :=
  ∀ Y Z, Realizes s Y → Realizes t Z → join Y Z ∈ OpenSet D

theorem rectangle_dense (D : List Bool → Prop) (hD : DenseOpen D) (s t : List Bool) :
    ∃ u v, s <+: u ∧ t <+: v ∧ Rectangle D u v := by
  let Y : Oracle := fun i => s.getD i false
  let Z : Oracle := fun i => t.getD i false
  let n := max s.length t.length
  obtain ⟨w,hw,hwD⟩ := hD.1 (initial (join Y Z) (2*n))
  let H : Oracle := fun i => w.getD i false
  have hH : Agree (2*n) (join Y Z) H := agree_of_prefix hw
  have hlen : 2*n ≤ w.length := by simpa using hw.length_le
  refine ⟨initial (column false H) w.length,initial (column true H) w.length,?_,?_,?_⟩
  · rw [←prefix_default s]
    apply initial_prefix (n := s.length) (m := w.length) (by dsimp [n] at hlen; omega)
    intro i hi
    exact (show Y i = H (2*i) from by simpa using hH (2*i) (by dsimp [n]; omega))
  · rw [←prefix_default t]
    apply initial_prefix (n := t.length) (m := w.length) (by dsimp [n] at hlen; omega)
    intro i hi
    exact (show Z i = H (2*i+1) from by simpa using hH (2*i+1) (by dsimp [n]; omega))
  · intro A B hA hB
    have ha := (realizes_initial _ _ _).mp hA
    have hb := (realizes_initial _ _ _).mp hB
    refine ⟨w,hwD,?_⟩
    apply Agree.mono (n := 2*w.length) _ (by omega)
    apply agree_of_columns
    · intro i hi
      simpa [column,H] using ha i hi
    · intro i hi
      simpa [column,H] using hb i hi

def First (D : List Bool → Prop) (t s : List Bool) : Prop :=
  ∃ u, t <+: u ∧ Rectangle D s u

theorem first_denseOpen (D : List Bool → Prop) (hD : DenseOpen D) (t : List Bool) :
    DenseOpen (First D t) := by
  constructor
  · intro s
    obtain ⟨u,v,hs,ht,hr⟩ := rectangle_dense D hD s t
    exact ⟨u,hs,v,ht,hr⟩
  · intro s u hsu
    rintro ⟨v,ht,hr⟩
    exact ⟨v,ht,fun Y Z hY hZ => hr Y Z (realizes_mono hsu hY) hZ⟩

def FirstFamily (D : ℕ → List Bool → Prop) (n : ℕ) : List Bool → Prop :=
  First (D (Nat.unpair n).1) (BorelGeneric.word (Nat.unpair n).2)

theorem firstFamily_denseOpen (D : ℕ → List Bool → Prop) (hD : ∀ n, DenseOpen (D n)) :
    ∀ n, DenseOpen (FirstFamily D n) :=
  fun index => first_denseOpen _ (hD (Nat.unpair index).1) _

def Fiber (D : ℕ → List Bool → Prop) (Y : Oracle) (n : ℕ) (t : List Bool) : Prop :=
  ∃ s, Realizes s Y ∧ Rectangle (D n) s t

theorem fiber_denseOpen (D : ℕ → List Bool → Prop) (Y : Oracle)
    (hY : GenericFor (FirstFamily D) Y) (n : ℕ) : DenseOpen (Fiber D Y n) := by
  constructor
  · intro t
    obtain ⟨k,hk⟩ := BorelGeneric.word_surjective t
    obtain ⟨s,hs,hYs⟩ := hY (Nat.pair n k)
    change First (D (Nat.unpair (Nat.pair n k)).1)
      (BorelGeneric.word (Nat.unpair (Nat.pair n k)).2) s at hs
    simp only [Nat.unpair_pair,hk] at hs
    obtain ⟨u,htu,hr⟩ := hs
    exact ⟨u,htu,s,hYs,hr⟩
  · intro t u htu
    rintro ⟨s,hYs,hr⟩
    exact ⟨s,hYs,fun A B hA hB => hr A B hA (realizes_mono htu hB)⟩

theorem fiber_isOpen (D : ℕ → List Bool → Prop) (n : ℕ) (t : List Bool) :
    IsOpen {Y | Fiber D Y n t} := by
  have he : {Y | Fiber D Y n t} =
      ⋃ s : List Bool, ⋃ (_ : Rectangle (D n) s t), {Y | Realizes s Y} := by
    ext Y
    simp only [Fiber,mem_ofPred_eq,mem_iUnion]
    aesop
  rw [he]
  exact isOpen_iUnion (fun s => isOpen_iUnion (fun _ => realizes_isOpen s))

theorem join_generic (D : ℕ → List Bool → Prop) (Y Z : Oracle)
    (hZ : GenericFor (Fiber D Y) Z) : GenericFor D (join Y Z) := by
  intro n
  obtain ⟨t,⟨s,hYs,hr⟩,hZt⟩ := hZ n
  exact hr Y Z hYs hZt

theorem borel_fiber_selection (D : ℕ → List Bool → Prop) :
    ∃ Z : {Y : Oracle // GenericFor (FirstFamily D) Y} → Oracle, Measurable Z ∧
      ∀ Y, GenericFor D (join Y.val (Z Y)) := by
  let R := fun Y : {Y : Oracle // GenericFor (FirstFamily D) Y} =>
    fun n t => Fiber D Y.val n (BorelGeneric.word t)
  have hd : ∀ Y n s, ∃ t, BorelGeneric.Ext s t ∧ R Y n t := by
    intro Y n s
    exact coded_dense _ (fiber_denseOpen D Y.val Y.property n) s
  have hm : ∀ n t, MeasurableSet {Y | R Y n t} := by
    intro n t
    exact (fiber_isOpen D n (BorelGeneric.word t)).measurableSet.preimage measurable_subtype_coe
  obtain ⟨Z,hZ,hreq⟩ := BorelGeneric.borel_generic_selection R hd hm
  refine ⟨Z,hZ,fun Y => join_generic D Y.val (Z Y) ?_⟩
  intro n
  obtain ⟨t,ht,hZt⟩ := hreq Y n
  exact ⟨BorelGeneric.word t,ht,(realizes_iff_meets _ _).mpr hZt⟩

end TuringRigidity.GenericFactor

end OAI
