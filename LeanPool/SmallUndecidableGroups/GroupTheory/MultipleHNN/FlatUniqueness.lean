/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.GroupTheory.MultipleHNN.Flat
public import Mathlib.Tactic.Group

/-!
# Signature uniqueness for flat two-letter HNN words

This file develops the coefficient comparison behind the uniqueness of the
color/sign signature of `MultipleHNNFlat.ReducedWord`.  The proof first
compares the outer HNN normal forms and then recursively compares the inner
normal forms of their coefficients.  Multiplication by an element of the
original base changes only an end coefficient of an inner reduced word, and
hence does not change its stable-letter signature.
-/

@[expose] public section

namespace Undecidability
namespace MultipleHNNFlatUniqueness

open Function

noncomputable section

variable {G : Type*} [Group G]
variable (A B : Subgroup G) (phi : A ≃* B)

/-- A reduced normal word in the inner single HNN extension. -/
abbrev InnerWord := HNNExtension.NormalWord.ReducedWord G A B

/-! ## Right multiplication of a single-HNN reduced word -/

/-- Multiply the last coefficient of a syllable list on the right. -/
def rightMulList : List (ℤˣ × G) → G → List (ℤˣ × G)
  | [], _ => []
  | [x], g => [(x.1, x.2 * g)]
  | x :: y :: rest, g => x :: rightMulList (y :: rest) g

theorem rightMulList_map_fst (l : List (ℤˣ × G)) (g : G) :
    (rightMulList l g).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          simp only [rightMulList, List.map_cons]
          exact congrArg (List.cons x.1) ih

theorem rightMulList_chain
    (l : List (ℤˣ × G))
    (hchain : l.IsChain
      (fun a b ↦ a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1))
    (g : G) :
    (rightMulList l g).IsChain
      (fun a b ↦ a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1) := by
  induction l with
  | nil =>
      change List.IsChain _ []
      exact List.isChain_nil
  | cons x xs ih =>
      cases xs with
      | nil => simp [rightMulList]
      | cons y ys =>
          cases ys with
          | nil => simpa [rightMulList] using hchain
          | cons z zs =>
              simp only [rightMulList]
              rw [List.isChain_cons_cons]
              refine ⟨?_, ih (List.IsChain.tail hchain)⟩
              exact (List.isChain_cons.1 hchain).1 y (by simp)

/-- Right-multiply an inner HNN normal word by a base-group element. -/
def rightMul (w : InnerWord A B) (g : G) : InnerWord A B where
  head := if w.toList = [] then w.head * g else w.head
  toList := rightMulList w.toList g
  chain := rightMulList_chain A B w.toList w.chain g

theorem rightMul_map_fst (w : InnerWord A B) (g : G) :
    (rightMul A B w g).toList.map Prod.fst = w.toList.map Prod.fst :=
  rightMulList_map_fst w.toList g

theorem rightMulList_prod
    (l : List (ℤˣ × G)) (g : G) (hne : l ≠ []) :
    ((rightMulList l g).map (fun x ↦
        (HNNExtension.t : HNNExtension G A B phi) ^ (x.1 : ℤ) *
          HNNExtension.of x.2)).prod =
      (l.map (fun x ↦
        (HNNExtension.t : HNNExtension G A B phi) ^ (x.1 : ℤ) *
          HNNExtension.of x.2)).prod * HNNExtension.of g := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil => simp [rightMulList, map_mul, mul_assoc]
      | cons y ys =>
          simp only [rightMulList, List.map_cons, List.prod_cons]
          rw [ih (by simp)]
          simp [mul_assoc]

theorem rightMul_prod (w : InnerWord A B) (g : G) :
    (rightMul A B w g).prod phi =
      w.prod phi * HNNExtension.of g := by
  unfold HNNExtension.NormalWord.ReducedWord.prod rightMul
  by_cases hnil : w.toList = []
  · simp [hnil, rightMulList, map_mul]
  · simp only [hnil, ↓reduceIte]
    rw [rightMulList_prod (A := A) (B := B) (phi := phi)
      w.toList g hnil]
    simp [mul_assoc]

/-- Right multiplication by an embedded base element preserves the complete
stable-sign list of a reduced word. -/
theorem inner_signs_eq_of_inv_mul_mem_range
    (w₁ w₂ : InnerWord A B)
    (hmem : (w₁.prod phi)⁻¹ * w₂.prod phi ∈
      MonoidHom.range (HNNExtension.of : G →* HNNExtension G A B phi)) :
    w₁.toList.map Prod.fst = w₂.toList.map Prod.fst := by
  rcases hmem with ⟨g, hg⟩
  have heq : (rightMul A B w₁ g).prod phi = w₂.prod phi := by
    rw [rightMul_prod]
    calc
      w₁.prod phi * HNNExtension.of g =
          w₁.prod phi * ((w₁.prod phi)⁻¹ * w₂.prod phi) := by rw [hg]
      _ = w₂.prod phi := by group
  rw [← rightMul_map_fst A B w₁ g]
  exact (HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq phi heq).1

/-! ## Coefficient transport in the outer HNN extension -/

/-- Left-multiply the initial coefficient of an inner HNN normal word. -/
def innerLeftMul (g : G) (w : InnerWord A B) : InnerWord A B where
  head := g * w.head
  toList := w.toList
  chain := w.chain

theorem mapped_toSubgroup_le_stageOne_range (u : ℤˣ) :
    HNNExtension.toSubgroup
        (MultipleHNN.MappedA A B phi) (MultipleHNN.MappedB A B phi) u ≤
      MonoidHom.range (MultipleHNN.stageOneOf A B phi) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨a, rfl⟩
  · rintro x ⟨b, hb, rfl⟩
    exact ⟨b, rfl⟩

/-- Moving an element of the subgroup on the left of a stable letter across
that letter.  This unit-valued version packages the two usual HNN relations. -/
theorem of_subgroup_mul_t_zpow
    {K : Type*} [Group K] (C D : Subgroup K) (psi : C ≃* D)
    (u : ℤˣ) (a : HNNExtension.toSubgroup C D (-u)) :
    HNNExtension.of (a : K) *
        (HNNExtension.t : HNNExtension K C D psi) ^ (u : ℤ) =
      HNNExtension.t ^ (u : ℤ) *
        HNNExtension.of
          (HNNExtension.toSubgroupEquiv psi (-u) a : K) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · let b : D := ⟨a, a.property⟩
    have h := HNNExtension.of_mul_t (φ := psi) b
    change HNNExtension.of (b : K) * HNNExtension.t =
      HNNExtension.t * HNNExtension.of (psi.symm b : K)
    exact h
  · let c : C := ⟨a, a.property⟩
    have h := HNNExtension.of_mul_inv_t (φ := psi) c
    change HNNExtension.of (c : K) * HNNExtension.t⁻¹ =
      HNNExtension.t⁻¹ * HNNExtension.of (psi c : K)
    exact h

/-- The outer reduced tail beginning at the selected nested syllable. -/
def outerTail (p : MultipleHNN.Syllable A B)
    (rest : List (MultipleHNN.Syllable A B))
    (hchain : ((p :: rest).map (fun q ↦ (q.1, q.2.prod phi))).IsChain
      (fun a b ↦ a.2 ∈ HNNExtension.toSubgroup
        (MultipleHNN.MappedA A B phi) (MultipleHNN.MappedB A B phi) a.1 →
          a.1 = b.1)) : MultipleHNN.ReducedWord A B phi where
  head := p.2
  toList := rest
  chain := List.IsChain.tail hchain

/-- Left-multiply the initial base coefficient of a nested HNN normal word. -/
def nestedLeftBase (g : G) (w : MultipleHNN.ReducedWord A B phi) :
    MultipleHNN.ReducedWord A B phi where
  head := innerLeftMul A B g w.head
  toList := w.toList
  chain := w.chain

@[simp] theorem nestedLeftBase_signature
    (g : G) (w : MultipleHNN.ReducedWord A B phi) :
    MultipleHNNFlat.nestedSignature A B phi
        (nestedLeftBase A B phi g w) =
      MultipleHNNFlat.nestedSignature A B phi w := rfl

theorem nestedLeftBase_eval
    (g : G) (w : MultipleHNN.ReducedWord A B phi) :
    MultipleHNN.ReducedWord.eval A B phi
        (nestedLeftBase A B phi g w) =
      MultipleHNN.baseEmbedding A B phi g *
        MultipleHNN.ReducedWord.eval A B phi w := by
  simp [nestedLeftBase, MultipleHNN.ReducedWord.eval,
    MultipleHNN.ReducedWord.toOuter, innerLeftMul,
    HNNExtension.NormalWord.ReducedWord.prod,
    MultipleHNN.baseEmbedding, MultipleHNN.stageTwoOf,
    MultipleHNN.stageOneOf, map_mul, mul_assoc]

/-! ## Uniqueness of the nested signature -/

/-- Equal evaluations of nested reduced words have identical interleaved
color/sign signatures. -/
theorem nestedSignature_eq_of_eval_eq
    (w₁ w₂ : MultipleHNN.ReducedWord A B phi)
    (heval : MultipleHNN.ReducedWord.eval A B phi w₁ =
      MultipleHNN.ReducedWord.eval A B phi w₂) :
    MultipleHNNFlat.nestedSignature A B phi w₁ =
      MultipleHNNFlat.nestedSignature A B phi w₂ := by
  induction hlist₁ : w₁.toList generalizing w₁ w₂ with
  | nil =>
      have hout := HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq
        (MultipleHNN.mappedEquiv A B phi) heval
      have hlist₂ : w₂.toList = [] := by
        have hs := hout.1
        simpa [MultipleHNN.ReducedWord.toOuter, hlist₁] using hs.symm
      have hheads : w₁.head.prod phi = w₂.head.prod phi := by
        apply HNNExtension.of_injective (MultipleHNN.mappedEquiv A B phi)
        simpa [MultipleHNN.ReducedWord.eval,
          MultipleHNN.ReducedWord.toOuter, hlist₁, hlist₂,
          HNNExtension.NormalWord.ReducedWord.prod] using heval
      have hinner :=
        (HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq phi hheads).1
      simpa [MultipleHNNFlat.nestedSignature, hlist₁, hlist₂,
        List.map_map, Function.comp_def] using
        congrArg (List.map (fun u : ℤˣ ↦ ((0 : Fin 2), u))) hinner
  | cons p₁ rest₁ ih =>
      rcases p₁ with ⟨u₁, c₁⟩
      have hout := HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq
        (MultipleHNN.mappedEquiv A B phi) heval
      cases hlist₂ : w₂.toList with
      | nil =>
          have hs := hout.1
          simp [MultipleHNN.ReducedWord.toOuter, hlist₁, hlist₂] at hs
      | cons p₂ rest₂ =>
          rcases p₂ with ⟨u₂, c₂⟩
          have hsigns := hout.1
          have hu : u₁ = u₂ := by
            simpa [MultipleHNN.ReducedWord.toOuter, hlist₁, hlist₂] using
              congrArg List.head? hsigns
          subst u₂
          have hheadMem :
              (w₁.head.prod phi)⁻¹ * w₂.head.prod phi ∈
                HNNExtension.toSubgroup
                  (MultipleHNN.MappedA A B phi)
                  (MultipleHNN.MappedB A B phi) (-u₁) := by
            apply hout.2 u₁
            simp [MultipleHNN.ReducedWord.toOuter, hlist₁]
          have hheadRange :
              (w₁.head.prod phi)⁻¹ * w₂.head.prod phi ∈
                MonoidHom.range (MultipleHNN.stageOneOf A B phi) :=
            mapped_toSubgroup_le_stageOne_range A B phi (-u₁) hheadMem
          have hheadSigns := inner_signs_eq_of_inv_mul_mem_range
            A B phi w₁.head w₂.head hheadRange
          let k : HNNExtension.toSubgroup
              (MultipleHNN.MappedA A B phi)
              (MultipleHNN.MappedB A B phi) (-u₁) :=
            ⟨(w₁.head.prod phi)⁻¹ * w₂.head.prod phi, hheadMem⟩
          let k' := HNNExtension.toSubgroupEquiv
            (MultipleHNN.mappedEquiv A B phi) (-u₁) k
          have hk'Mem : (k' : MultipleHNN.StageOne A B phi) ∈
              HNNExtension.toSubgroup
                (MultipleHNN.MappedA A B phi)
                (MultipleHNN.MappedB A B phi) u₁ := by
            simpa using k'.property
          have hkRange : (k' : MultipleHNN.StageOne A B phi) ∈
              MonoidHom.range (MultipleHNN.stageOneOf A B phi) :=
            mapped_toSubgroup_le_stageOne_range A B phi u₁ hk'Mem
          rcases hkRange with ⟨g, hg⟩
          have hchain₁ :
              (((u₁, c₁) :: rest₁).map
                (fun q ↦ (q.1, q.2.prod phi))).IsChain
                (fun a b ↦ a.2 ∈ HNNExtension.toSubgroup
                  (MultipleHNN.MappedA A B phi)
                  (MultipleHNN.MappedB A B phi) a.1 → a.1 = b.1) := by
            simpa [hlist₁] using w₁.chain
          have hchain₂ :
              (((u₁, c₂) :: rest₂).map
                (fun q ↦ (q.1, q.2.prod phi))).IsChain
                (fun a b ↦ a.2 ∈ HNNExtension.toSubgroup
                  (MultipleHNN.MappedA A B phi)
                  (MultipleHNN.MappedB A B phi) a.1 → a.1 = b.1) := by
            simpa [hlist₂] using w₂.chain
          let t₁ := outerTail A B phi (u₁, c₁) rest₁ hchain₁
          let t₂ := outerTail A B phi (u₁, c₂) rest₂ hchain₂
          have hw₁eval : MultipleHNN.ReducedWord.eval A B phi w₁ =
              MultipleHNN.stageTwoOf A B phi (w₁.head.prod phi) *
                MultipleHNN.secondStable A B phi ^ (u₁ : ℤ) *
                  MultipleHNN.ReducedWord.eval A B phi t₁ := by
            simp [MultipleHNN.ReducedWord.eval,
              MultipleHNN.ReducedWord.toOuter, hlist₁, t₁, outerTail,
              HNNExtension.NormalWord.ReducedWord.prod,
              MultipleHNN.stageTwoOf, MultipleHNN.secondStable, mul_assoc]
          have hw₂eval : MultipleHNN.ReducedWord.eval A B phi w₂ =
              MultipleHNN.stageTwoOf A B phi (w₂.head.prod phi) *
                MultipleHNN.secondStable A B phi ^ (u₁ : ℤ) *
                  MultipleHNN.ReducedWord.eval A B phi t₂ := by
            simp [MultipleHNN.ReducedWord.eval,
              MultipleHNN.ReducedWord.toOuter, hlist₂, t₂, outerTail,
              HNNExtension.NormalWord.ReducedWord.prod,
              MultipleHNN.stageTwoOf, MultipleHNN.secondStable, mul_assoc]
          have hkhead : w₂.head.prod phi = w₁.head.prod phi * (k : _) := by
            change w₂.head.prod phi = w₁.head.prod phi *
              ((w₁.head.prod phi)⁻¹ * w₂.head.prod phi)
            group
          have hmove :
              MultipleHNN.stageTwoOf A B phi (k : _) *
                  MultipleHNN.secondStable A B phi ^ (u₁ : ℤ) =
                MultipleHNN.secondStable A B phi ^ (u₁ : ℤ) *
                  MultipleHNN.stageTwoOf A B phi (k' : _) :=
            of_subgroup_mul_t_zpow
              (MultipleHNN.MappedA A B phi)
              (MultipleHNN.MappedB A B phi)
              (MultipleHNN.mappedEquiv A B phi) u₁ k
          have htail :
              MultipleHNN.ReducedWord.eval A B phi t₁ =
                MultipleHNN.baseEmbedding A B phi g *
                  MultipleHNN.ReducedWord.eval A B phi t₂ := by
            change MultipleHNN.ReducedWord.eval A B phi t₁ =
              MultipleHNN.stageTwoOf A B phi
                  (MultipleHNN.stageOneOf A B phi g) *
                MultipleHNN.ReducedWord.eval A B phi t₂
            rw [hg]
            have hall := heval
            rw [hw₁eval, hw₂eval, hkhead, map_mul] at hall
            rw [mul_assoc
              (MultipleHNN.stageTwoOf A B phi (w₁.head.prod phi))
              (MultipleHNN.stageTwoOf A B phi (k : _))
              (MultipleHNN.secondStable A B phi ^ (u₁ : ℤ))] at hall
            rw [hmove] at hall
            have hcancel :
                (MultipleHNN.stageTwoOf A B phi (w₁.head.prod phi) *
                    MultipleHNN.secondStable A B phi ^ (u₁ : ℤ)) *
                    MultipleHNN.ReducedWord.eval A B phi t₁ =
                  (MultipleHNN.stageTwoOf A B phi (w₁.head.prod phi) *
                    MultipleHNN.secondStable A B phi ^ (u₁ : ℤ)) *
                    (MultipleHNN.stageTwoOf A B phi (k' : _) *
                      MultipleHNN.ReducedWord.eval A B phi t₂) := by
              simpa only [mul_assoc] using hall
            exact mul_left_cancel hcancel
          have htailShift :
              MultipleHNN.ReducedWord.eval A B phi t₁ =
                MultipleHNN.ReducedWord.eval A B phi
                  (nestedLeftBase A B phi g t₂) := by
            rw [nestedLeftBase_eval]
            exact htail
          have hsTail := ih t₁ (nestedLeftBase A B phi g t₂)
            htailShift (by rfl)
          rw [nestedLeftBase_signature] at hsTail
          have hheadColored :
              w₁.head.toList.map (fun p ↦ ((0 : Fin 2), p.1)) =
                w₂.head.toList.map (fun p ↦ ((0 : Fin 2), p.1)) := by
            simpa [List.map_map, Function.comp_def] using
              congrArg (List.map (fun u : ℤˣ ↦ ((0 : Fin 2), u)))
                hheadSigns
          simp only [MultipleHNNFlat.nestedSignature, hlist₁, hlist₂,
            List.flatMap_cons]
          rw [hheadColored]
          change _ ++ (1, u₁) ::
              MultipleHNNFlat.nestedSignature A B phi t₁ =
            _ ++ (1, u₁) ::
              MultipleHNNFlat.nestedSignature A B phi t₂
          rw [hsTail]

/-- The color/sign signature is a complete invariant of the stable letters
in a flat reduced word.  In particular, equality cannot change a sign,
insert a stable letter, or change the interleaving of the two colors. -/
theorem signature_eq_of_eval_eq
    (w₁ w₂ : MultipleHNNFlat.ReducedWord A B)
    (heval : MultipleHNNFlat.eval A B phi w₁ =
      MultipleHNNFlat.eval A B phi w₂) :
    MultipleHNNFlat.signature A B w₁ =
      MultipleHNNFlat.signature A B w₂ := by
  rcases MultipleHNNFlat.exists_nested_with_signature A B phi w₁ with
    ⟨v₁, hv₁eval, hv₁sig⟩
  rcases MultipleHNNFlat.exists_nested_with_signature A B phi w₂ with
    ⟨v₂, hv₂eval, hv₂sig⟩
  have hv : MultipleHNN.ReducedWord.eval A B phi v₁ =
      MultipleHNN.ReducedWord.eval A B phi v₂ := by
    rw [hv₁eval, hv₂eval, heval]
  calc
    MultipleHNNFlat.signature A B w₁ =
        MultipleHNNFlat.nestedSignature A B phi v₁ := hv₁sig.symm
    _ = MultipleHNNFlat.nestedSignature A B phi v₂ :=
      nestedSignature_eq_of_eval_eq A B phi v₁ v₂ hv
    _ = MultipleHNNFlat.signature A B w₂ := hv₂sig

end

end MultipleHNNFlatUniqueness
end Undecidability
