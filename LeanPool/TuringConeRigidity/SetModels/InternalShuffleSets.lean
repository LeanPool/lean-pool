/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalShuffleSets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticShuffleCertificate
public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalCohenSets
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters

/-!
# Internal Shuffle Sets
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable UniformArithmetic
open FiniteShuffleCertificate FiniteShuffle CohenBorelForcing CountableForcing

def shuffleOpen (D : ZFSet.{0}) (t : List Bool) : Prop :=
  ∃ r : List Bool, wordCode r ∈ D ∧ r <+: t

noncomputable def shuffleOpenCodes (D : ZFSet.{0}) : Oracle :=
  arithmeticReal (fun O n => ∃ r : List Bool, O 0 (encode r) = true ∧ r <+: EncodedForcing.word n)
    (fun _ => wordPullback D)

theorem shuffleOpenCodes_true (D : ZFSet.{0}) (n : ℕ) :
    shuffleOpenCodes D n = true ↔ shuffleOpen D (EncodedForcing.word n) := by
  rw [shuffleOpenCodes,arithmeticReal_true]
  simp only [wordPullback_true,EncodedForcing.word,encodek,Option.getD_some,shuffleOpen]

theorem shuffleOpenCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : realCode (shuffleOpenCodes D) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT ArithmeticShuffleCertificate.open_arith
    (fun _ => wordPullback D) (fun _ => wordPullback_mem M hM hT D hD)

noncomputable def shuffleCertificateCodes (D : ZFSet.{0}) : Oracle :=
  arithmeticReal (fun O n => Certificate (fun t => O 0 (encode t) = true) (EncodedForcing.word n))
    (fun _ => shuffleOpenCodes D)

theorem shuffleCertificateCodes_true (D : ZFSet.{0}) (n : ℕ) :
    shuffleCertificateCodes D n = true ↔ Certificate (shuffleOpen D) (EncodedForcing.word n) := by
  rw [shuffleCertificateCodes,arithmeticReal_true]
  simp only [Certificate,shuffleOpenCodes_true,EncodedForcing.word,encodek,Option.getD_some]

theorem shuffleCertificateCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : realCode (shuffleCertificateCodes D) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT ArithmeticShuffleCertificate.certificate_arith
    (fun _ => shuffleOpenCodes D) (fun _ => shuffleOpenCodes_mem M hM hT D hD)

noncomputable def shuffleStar (D : ZFSet.{0}) : ZFSet.{0} :=
  conditions.sep (fun q => ∃ w : List Bool, q = wordCode w ∧ Certificate (shuffleOpen D) w)

theorem wordCode_mem_shuffleStar (D : ZFSet.{0}) (p : List Bool) :
    wordCode p ∈ shuffleStar D ↔ Certificate (shuffleOpen D) p := by
  rw [shuffleStar,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,w,hw,hc⟩
    exact wordCode_injective hw ▸ hc
  · intro hc
    exact ⟨(mem_conditions _).mpr ⟨_,wordCode_function _⟩,p,rfl,hc⟩

theorem shuffleStar_eq_image (D : ZFSet.{0}) :
    shuffleStar D = wordImage (shuffleCertificateCodes D) := by
  apply ZFSet.ext
  intro q
  by_cases hq : q ∈ conditions
  · obtain ⟨p,rfl⟩ := (prefix_iff_wordCode q).mp ((mem_conditions q).mp hq)
    exact (wordCode_mem_shuffleStar D p).trans
      (wordImage_spec (Certificate (shuffleOpen D)) (shuffleCertificateCodes D)
        (shuffleCertificateCodes_true D) p).symm
  · exact ⟨fun h => False.elim (hq (ZFSet.mem_sep.mp h).1),
      fun h => False.elim (hq (ZFSet.mem_sep.mp h).1)⟩

theorem shuffleStar_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (D : ZFSet.{0}) (hD : D ∈ M) : shuffleStar D ∈ M := by
  rw [shuffleStar_eq_image]
  exact wordImage_mem M hM hT _ (shuffleCertificateCodes_mem M hM hT D hD)

theorem shuffleOpen_denseOpen (D : ZFSet.{0})
    (hD : Dense {p : Condition | wordCode p.word ∈ D}) : DenseOpen (shuffleOpen D) := by
  refine ⟨?_,?_⟩
  · intro p
    obtain ⟨q,hq,hd⟩ := hD ⟨p⟩
    exact ⟨q.word,hq,q.word,hd,List.prefix_rfl⟩
  · intro p q hpq h
    obtain ⟨r,hr,hrp⟩ := h
    exact ⟨r,hr,hrp.trans hpq⟩

theorem shuffleStar_denseOpen (D : ZFSet.{0})
    (hD : Dense {p : Condition | wordCode p.word ∈ D}) :
    DenseOpen (fun p => wordCode p ∈ shuffleStar D) := by
  simpa only [wordCode_mem_shuffleStar] using
    certificate_denseOpen (shuffleOpen D) (shuffleOpen_denseOpen D hD)

theorem shuffleStar_dense (D : ZFSet.{0})
    (hD : Dense {p : Condition | wordCode p.word ∈ D}) :
    Dense {p : Condition | wordCode p.word ∈ shuffleStar D} := by
  intro p
  obtain ⟨q,hpq,hq⟩ := (shuffleStar_denseOpen D hD).1 p.word
  exact ⟨⟨q⟩,hpq,hq⟩

end TuringRigidity.InternalCohen

end OAI
