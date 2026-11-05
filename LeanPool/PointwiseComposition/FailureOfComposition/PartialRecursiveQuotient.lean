/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteGeneratedCongruence

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The generated quotient of a Sigma-one sound PA extension is the monoid of
unary partial recursive functions. The target consists of actual partial maps,
with partial composition as multiplication and the total identity as its unit.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition

/-- Unary partial recursive functions, identified by equality of partial maps. -/
def UnaryPartrec :=
  { f : ℕ → Part ℕ // Nat.Partrec f }

namespace UnaryPartrec

instance : Mul UnaryPartrec where
  mul f g := ⟨fun x => (g.val x).bind f.val, Nat.Partrec.comp f.property g.property⟩

instance : One UnaryPartrec where
  one :=
    ⟨Part.some,
      Nat.Partrec.Code.exists_code.mpr ⟨Nat.Partrec.Code.id, funext Nat.Partrec.Code.eval_id⟩⟩

/-- Multiplication is ordinary partial composition, with the right map applied first. -/
@[simp]
theorem mul_apply (f g : UnaryPartrec) (x : ℕ) : (f * g).val x = (g.val x).bind f.val :=
  rfl

@[simp]
theorem one_apply (x : ℕ) : (1 : UnaryPartrec).val x = Part.some x :=
  rfl

instance : Monoid UnaryPartrec
    where
  mul_assoc f g
    h := by
    apply Subtype.ext
    funext x
    exact (Part.bind_assoc (h.val x) g.val f.val).symm
  one_mul
    f := by
    apply Subtype.ext
    funext x
    exact Part.bind_some_right (f.val x)
  mul_one
    f := by
    apply Subtype.ext
    funext x
    exact Part.bind_some x f.val

/-- The partial recursive function denoted by a concrete natural-number index. -/
def ofIndex (e : ℕ) : UnaryPartrec :=
  ⟨Kleene.eval e, Nat.Partrec.Code.exists_code.mpr ⟨Denumerable.ofNat Nat.Partrec.Code e, rfl⟩⟩

@[simp]
theorem ofIndex_val (e : ℕ) : (ofIndex e).val = Kleene.eval e :=
  rfl

/-- Every unary partial recursive function has an index in the fixed numbering. -/
theorem ofIndex_surjective : Function.Surjective ofIndex :=
  by
  rintro ⟨f, hf⟩
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨Encodable.encode c, Subtype.ext ?_⟩
  change Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)) = f
  simpa only [Denumerable.ofNat_encode] using hc

end UnaryPartrec

namespace ConcreteIndices

/-- Evaluation descends to the generated quotient of a Sigma-one sound theory. -/
noncomputable def generatedQuotientDenotation (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : GeneratedCongruence.SigmaOneSound T) : GeneratedQuotient T → UnaryPartrec :=
  Quotient.lift UnaryPartrec.ofIndex fun e d h =>
    Subtype.ext ((generated_iff_extensional_of_sound T hT e d).mp h)

@[simp]
theorem generatedQuotientDenotation_mk (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : GeneratedCongruence.SigmaOneSound T) (e : ℕ) :
    generatedQuotientDenotation T hT (generatedQuotientMk T e) = UnaryPartrec.ofIndex e :=
  rfl

theorem generatedQuotientDenotation_bijective (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : GeneratedCongruence.SigmaOneSound T) :
    Function.Bijective (generatedQuotientDenotation T hT) :=
  by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro e d heq
    apply Quotient.sound
    exact (generated_iff_extensional_of_sound T hT e d).mpr (congrArg Subtype.val heq)
  · intro f
    obtain ⟨e, he⟩ := UnaryPartrec.ofIndex_surjective f
    exact ⟨generatedQuotientMk T e, he⟩

/-- In the sound case, the generated quotient is isomorphic to the monoid of
all unary partial recursive functions under partial composition. -/
noncomputable def generatedQuotientPartialRecursiveEquiv (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : GeneratedCongruence.SigmaOneSound T) : GeneratedQuotient T ≃* UnaryPartrec :=
  {
    Equiv.ofBijective (generatedQuotientDenotation T hT)
      (generatedQuotientDenotation_bijective T hT) with
    map_mul' := by
      intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro e d
      apply Subtype.ext
      funext x
      exact Kleene.eval_compIndex e d x }

@[simp]
theorem generatedQuotientPartialRecursiveEquiv_mk (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : GeneratedCongruence.SigmaOneSound T) (e : ℕ) :
    generatedQuotientPartialRecursiveEquiv T hT (generatedQuotientMk T e) =
      UnaryPartrec.ofIndex e :=
  rfl

end ConcreteIndices

end FailureOfComposition

end

end PointwiseComposition
