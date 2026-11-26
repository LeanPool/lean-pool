/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum

/-!
# Coefficient tensors on a finite set of named sites

We store a finite sum of pure tensors. Restriction acts by a local matrix
on every summand and compares the resulting coefficient arrays. It need
not preserve the chosen decomposition. Every array has a coordinate
expansion, and two expansions of the same array restrict to each other.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Spectral

/-- The data for the raw construction, including `leg`, `term`, `[fleg`, `[fterm`, `factor`. -/
structure Raw (K S : Type) where
  /-- The `Raw` component of type `S → Type`. -/
  leg : S → Type
  /-- The `Raw` component of type `Type`. -/
  term : Type
  [fleg : ∀ s, Fintype (leg s)]
  [fterm : Fintype term]
  /-- The multiplicative factor of type `term → (s : S) → leg s → K`. -/
  factor : term → (s : S) → leg s → K

attribute [instance] Raw.fleg Raw.fterm

namespace Raw

variable {K S : Type} [CommSemiring K] [Fintype S]

/-- The value specified by `∑ i : A.term, ∏ s, A.factor i s (x s)`. -/
def coeff (A : Raw K S) (x : ∀ s, A.leg s) : K :=
  ∑ i : A.term, ∏ s, A.factor i s (x s)

/-- The defining condition `∃ L : (s : S) → B.leg s → A.leg s → K, ∀ x : ∀ s, B.leg s, B.coeff x
= ∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y`. -/
def Restricts (A B : Raw K S) : Prop :=
  ∃ L : (s : S) → B.leg s → A.leg s → K, ∀ x : ∀ s, B.leg s,
    B.coeff x = ∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y

instance : Zero (Raw K S) :=
  ⟨⟨fun _ => Empty, Empty, fun i => i.elim⟩⟩

instance : One (Raw K S) :=
  ⟨⟨fun _ => Unit, Unit, fun _ _ _ => 1⟩⟩

instance : Add (Raw K S) where
  add A B := ⟨fun s => A.leg s ⊕ B.leg s, A.term ⊕ B.term,
    fun i s => Sum.elim
      (fun j => Sum.elim (A.factor j s) (fun _ => 0))
      (fun j => Sum.elim (fun _ => 0) (B.factor j s)) i⟩

instance : Mul (Raw K S) where
  mul A B := ⟨fun s => A.leg s × B.leg s, A.term × B.term,
    fun i s x => A.factor i.1 s x.1 * B.factor i.2 s x.2⟩

/-- One local matrix at each site, from the source legs to the target legs. -/
abbrev RestrictionMaps (A B : Raw K S) := (s : S) → B.leg s → A.leg s → K

variable {A B C : Raw K S}

open Classical in
/-- The local matrix that copies or selects a source coordinate. -/
def pullbackMap (f : ∀ s, B.leg s → A.leg s) : RestrictionMaps A B :=
  fun s x y => if y = f s x then 1 else 0

theorem coeff_pullbackMap (f : ∀ s, B.leg s → A.leg s)
    (h : ∀ x, B.coeff x = A.coeff (fun s => f s (x s))) (x : ∀ s, B.leg s) :
    B.coeff x = ∑ i : A.term, ∏ s, ∑ y, pullbackMap f s (x s) y * A.factor i s y := by
  classical
  rw [h]
  simp [pullbackMap, coeff, ite_mul]

/-- Copying or selecting local coordinates is a restriction. -/
theorem Restricts.pullback (f : ∀ s, B.leg s → A.leg s)
    (h : ∀ x, B.coeff x = A.coeff (fun s => f s (x s))) : A.Restricts B :=
  ⟨pullbackMap f, coeff_pullbackMap f h⟩

theorem Restricts.refl (A : Raw K S) : A.Restricts A :=
  Restricts.pullback (fun _ x => x) (fun _ => rfl)

theorem expand [DecidableEq S] (A : Raw K S) (v : ∀ s, A.leg s → K) :
    (∑ i : A.term, ∏ s, ∑ y : A.leg s, v s y * A.factor i s y) =
      ∑ y : ∀ s, A.leg s, (∏ s, v s (y s)) * A.coeff y := by
  simp only [Fintype.prod_sum, Finset.prod_mul_distrib, coeff, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Formula independent of the chosen expansions of both arrays. -/
theorem restricts_iff [DecidableEq S] (A B : Raw K S) :
    A.Restricts B ↔
      ∃ L : (s : S) → B.leg s → A.leg s → K, ∀ x : ∀ s, B.leg s,
        B.coeff x = ∑ y : ∀ s, A.leg s, (∏ s, L s (x s) (y s)) * A.coeff y := by
  simp only [Restricts, expand]

/-- Compose the local restriction maps by matrix multiplication at each site. -/
def composeRestrictionMaps (L : RestrictionMaps A B) (M : RestrictionMaps B C) :
    RestrictionMaps A C := fun s x z => ∑ y, M s x y * L s y z

theorem coeff_composeRestrictionMaps (L : RestrictionMaps A B) (M : RestrictionMaps B C)
    (hL : ∀ x, B.coeff x = ∑ i : A.term, ∏ s, ∑ y, L s (x s) y * A.factor i s y)
    (hM : ∀ x, C.coeff x = ∑ j : B.term, ∏ s, ∑ y, M s (x s) y * B.factor j s y)
    (x : ∀ s, C.leg s) :
    C.coeff x = ∑ i : A.term, ∏ s, ∑ y, composeRestrictionMaps L M s (x s) y * A.factor i s y := by
  classical
  rw [hM, B.expand]
  simp only [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun s y => M s (x s) y * ∑ z, L s y z * A.factor i s z)]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [composeRestrictionMaps, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem Restricts.trans (h : A.Restricts B) (g : B.Restricts C) : A.Restricts C := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := g
  exact ⟨composeRestrictionMaps L M, coeff_composeRestrictionMaps L M hL hM⟩

instance : Setoid (Raw K S) where
  r A B := A.Restricts B ∧ B.Restricts A
  iseqv := ⟨fun A => ⟨.refl A, .refl A⟩, fun h => ⟨h.2, h.1⟩,
    fun h g => ⟨h.1.trans g.1, g.2.trans h.2⟩⟩

theorem equiv_coeff (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ x, A.coeff x = B.coeff (fun s => f s (x s))) : A ≈ B := by
  refine ⟨Restricts.pullback (fun s => (f s).symm) ?_, Restricts.pullback (fun s => f s) h⟩
  intro x
  simp only [h, Equiv.apply_symm_apply]

theorem relabel (e : A.term ≃ B.term) (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ i s x, A.factor i s x = B.factor (e i) s (f s x)) : A ≈ B := by
  refine equiv_coeff f fun x => ?_
  simp only [coeff, h]
  exact e.sum_comp (fun i => ∏ s, B.factor i s (f s (x s)))

/-- Equivalences of all coordinates and terms that preserve the tensor factors. -/
def Relabels (A B : Raw K S) : Prop :=
  ∃ (terms : A.term ≃ B.term) (legs : ∀ s, A.leg s ≃ B.leg s),
    ∀ i s x, A.factor i s x = B.factor (terms i) s (legs s x)

theorem relabel_of_relabels {A B : Raw K S} (h : Relabels A B) : A ≈ B := by
  obtain ⟨terms, legs, factors⟩ := h
  exact relabel terms legs factors

end Raw
end MatrixMultiplicationAllFields.MatrixExponent.Spectral
end

/-
# Direct sums and products of restrictions

Use block diagonal matrices for sums and Kronecker products for products.
The identities concern coefficient arrays and require no termwise
correspondence between the decompositions.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Spectral.Raw

variable {K S : Type} [CommSemiring K] [Fintype S] {A B C D : Raw K S}

theorem coeff_mul (A B : Raw K S) (x : ∀ s, (A * B).leg s) :
    (A * B).coeff x = A.coeff (fun s => (x s).1) * B.coeff (fun s => (x s).2) := by
  change (∑ i : A.term × B.term, ∏ s, A.factor i.1 s (x s).1 * B.factor i.2 s (x s).2) = _
  simp only [coeff, Fintype.sum_prod_type, Finset.prod_mul_distrib, Finset.sum_mul_sum]

/-- The Kronecker product of the local maps witnessing two restrictions. -/
def restrictMulMap (L : (s : S) → B.leg s → A.leg s → K)
    (M : (s : S) → D.leg s → C.leg s → K) :
    (s : S) → (B * D).leg s → (A * C).leg s → K :=
  fun s x y => L s x.1 y.1 * M s x.2 y.2

theorem coeff_restrictMulMap (L : (s : S) → B.leg s → A.leg s → K)
    (M : (s : S) → D.leg s → C.leg s → K)
    (hL : ∀ x, B.coeff x = ∑ i : A.term, ∏ s, ∑ y, L s (x s) y * A.factor i s y)
    (hM : ∀ x, D.coeff x = ∑ i : C.term, ∏ s, ∑ y, M s (x s) y * C.factor i s y)
    (x : ∀ s, (B * D).leg s) :
    (B * D).coeff x = ∑ i : (A * C).term, ∏ s, ∑ y : (A * C).leg s,
      restrictMulMap L M s (x s) y * (A * C).factor i s y := by
  rw [coeff_mul, hL, hM]
  change _ = ∑ i : A.term × C.term, ∏ s, ∑ y : A.leg s × C.leg s,
    L s (x s).1 y.1 * M s (x s).2 y.2 * (A.factor i.1 s y.1 * C.factor i.2 s y.2)
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_mul_mul_comm _ _ _ _

theorem Restricts.mul (h : A.Restricts B) (g : C.Restricts D) :
    (A * C).Restricts (B * D) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := g
  exact ⟨restrictMulMap L M, coeff_restrictMulMap L M hL hM⟩

/-- Equality of coefficient arrays survives extending the factors by zero. -/
theorem extend {I J : Type} [Fintype I] [Fintype J] {Z : S → Type}
    (f : I → (s : S) → Z s → K) (g : J → (s : S) → Z s → K)
    (h : ∀ x : ∀ s, Z s, (∑ i, ∏ s, f i s (x s)) = ∑ j, ∏ s, g j s (x s))
    {u : I → S → K} {v : J → S → K}
    (huv : ∀ s, (∃ z, (∀ i, u i s = f i s z) ∧ (∀ j, v j s = g j s z)) ∨
      ((∀ i, u i s = 0) ∧ (∀ j, v j s = 0))) :
    (∑ i, ∏ s, u i s) = ∑ j, ∏ s, v j s := by
  classical
  by_cases he : ∃ s, (∀ i, u i s = 0) ∧ (∀ j, v j s = 0)
  · obtain ⟨s, hu, hv⟩ := he
    exact (Finset.sum_eq_zero fun i _ => Finset.prod_eq_zero (Finset.mem_univ s) (hu i)).trans
      (Finset.sum_eq_zero fun j _ => Finset.prod_eq_zero (Finset.mem_univ s) (hv j)).symm
  · have hx (s : S) := (huv s).resolve_right fun hs => he ⟨s, hs⟩
    choose x hu hv using hx
    simp only [hu, hv, h]

/-- The block-diagonal sum of the local maps witnessing two restrictions. -/
def restrictAddMap (L : (s : S) → B.leg s → A.leg s → K)
    (M : (s : S) → D.leg s → C.leg s → K) (s : S) :
    (B + D).leg s → (A + C).leg s → K :=
  Sum.elim (fun b => Sum.elim (L s b) (fun _ => 0))
    (fun d => Sum.elim (fun _ => 0) (M s d))

theorem coeff_restrictAddMap (L : (s : S) → B.leg s → A.leg s → K)
    (M : (s : S) → D.leg s → C.leg s → K)
    (hL : ∀ x, B.coeff x = ∑ i : A.term, ∏ s, ∑ y, L s (x s) y * A.factor i s y)
    (hM : ∀ x, D.coeff x = ∑ i : C.term, ∏ s, ∑ y, M s (x s) y * C.factor i s y)
    (x : ∀ s, (B + D).leg s) :
    (B + D).coeff x = ∑ i : (A + C).term, ∏ s, ∑ y : (A + C).leg s,
      restrictAddMap L M s (x s) y * (A + C).factor i s y := by
  have left (i : A.term) (s : S) (y : A.leg s ⊕ C.leg s) :
      (A + C).factor (.inl i) s y = Sum.elim (A.factor i s) (fun _ => 0) y := rfl
  have right (i : C.term) (s : S) (y : A.leg s ⊕ C.leg s) :
      (A + C).factor (.inr i) s y = Sum.elim (fun _ => 0) (C.factor i s) y := rfl
  change (∑ i : B.term ⊕ D.term, ∏ s, (B + D).factor i s (x s)) =
    ∑ i : A.term ⊕ C.term, ∏ s, ∑ y : A.leg s ⊕ C.leg s,
      restrictAddMap L M s (x s) y * (A + C).factor i s y
  simp only [Fintype.sum_sum_type, left, right]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine extend B.factor (fun i s z => ∑ y, L s z y * A.factor i s y) hL ?_
    intro s
    cases x s with
    | inl z => exact Or.inl ⟨z, fun _ => rfl, fun _ => by simp [restrictAddMap]⟩
    | inr z => exact Or.inr ⟨fun _ => rfl, fun _ => by simp [restrictAddMap]⟩
  · refine extend D.factor (fun i s z => ∑ y, M s z y * C.factor i s y) hM ?_
    intro s
    cases x s with
    | inl z => exact Or.inr ⟨fun _ => rfl, fun _ => by simp [restrictAddMap]⟩
    | inr z => exact Or.inl ⟨z, fun _ => rfl, fun _ => by simp [restrictAddMap]⟩

theorem Restricts.add (h : A.Restricts B) (g : C.Restricts D) :
    (A + C).Restricts (B + D) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := g
  exact ⟨restrictAddMap L M, coeff_restrictAddMap L M hL hM⟩

end MatrixMultiplicationAllFields.MatrixExponent.Spectral.Raw
end

section
/-
# Semiring laws up to mutual restriction

Each identity reindexes the terms and the coordinates at every site by
the same sum or product equivalence.
-/

namespace MatrixMultiplicationAllFields.MatrixExponent.Spectral.Raw

variable {K S : Type} [CommSemiring K] (A B C : Raw K S)

theorem comm_add_relabels : Relabels (A + B) (B + A) := by
  refine ⟨(Equiv.sumComm _ _), (fun _ => Equiv.sumComm _ _), ?_⟩
  rintro (i | i) s (x | x) <;> rfl

theorem assoc_add_relabels : Relabels ((A + B) + C) (A + (B + C)) := by
  refine ⟨(Equiv.sumAssoc _ _ _), (fun _ => Equiv.sumAssoc _ _ _), ?_⟩
  rintro ((i | i) | i) s ((x | x) | x) <;> rfl

theorem nil_add_relabels : Relabels (0 + A) A := by
  refine ⟨(Equiv.emptySum Empty _), (fun _ => Equiv.emptySum Empty _), ?_⟩
  rintro (i | i)
  · exact i.elim
  rintro s (x | x)
  · exact x.elim
  rfl

theorem comm_mul_relabels : Relabels (A * B) (B * A) := by
  refine ⟨(Equiv.prodComm _ _), (fun _ => Equiv.prodComm _ _), ?_⟩
  intro i s x
  exact mul_comm _ _

theorem assoc_mul_relabels : Relabels ((A * B) * C) (A * (B * C)) := by
  refine ⟨(Equiv.prodAssoc _ _ _), (fun _ => Equiv.prodAssoc _ _ _), ?_⟩
  intro i s x
  exact mul_assoc _ _ _

theorem unit_mul_relabels : Relabels (1 * A) A := by
  refine ⟨(Equiv.punitProd _), (fun _ => Equiv.punitProd _), ?_⟩
  intro i s x
  exact one_mul _

theorem nil_mul_relabels : Relabels (0 * A) 0 := by
  refine ⟨(Equiv.emptyProd _), (fun _ => Equiv.emptyProd _), ?_⟩
  intro i
  exact i.1.elim

theorem distrib_left_relabels : Relabels (A * (B + C)) (A * B + A * C) := by
  refine ⟨(Equiv.prodSumDistrib _ _ _), (fun _ => Equiv.prodSumDistrib _ _ _), ?_⟩
  rintro ⟨i, j | j⟩ s ⟨x, y | y⟩
  · rfl
  · exact mul_zero _
  · exact mul_zero _
  · rfl
variable [Fintype S]

theorem comm_add : A + B ≈ B + A :=
  relabel_of_relabels (comm_add_relabels A B)

theorem assoc_add : (A + B) + C ≈ A + (B + C) :=
  relabel_of_relabels (assoc_add_relabels A B C)

theorem nil_add : 0 + A ≈ A :=
  relabel_of_relabels (nil_add_relabels A)

theorem comm_mul : A * B ≈ B * A :=
  relabel_of_relabels (comm_mul_relabels A B)

theorem assoc_mul : (A * B) * C ≈ A * (B * C) :=
  relabel_of_relabels (assoc_mul_relabels A B C)

theorem unit_mul : 1 * A ≈ A :=
  relabel_of_relabels (unit_mul_relabels A)

theorem nil_mul : 0 * A ≈ 0 :=
  relabel_of_relabels (nil_mul_relabels A)

theorem distrib_left : A * (B + C) ≈ A * B + A * C :=
  relabel_of_relabels (distrib_left_relabels A B C)

end MatrixMultiplicationAllFields.MatrixExponent.Spectral.Raw
end

/-
# The restriction semiring on a fixed finite set of sites
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Spectral

namespace Raw

variable {K S : Type} [CommSemiring K]

/-- Order tensor classes by reverse restriction for the chosen relation. -/
@[instance_reducible]
def quotientLE (s : Setoid (Raw K S)) (restricts : Raw K S → Raw K S → Prop)
    (equivalent : ∀ a b, s.r a b ↔ restricts a b ∧ restricts b a)
    (transitive : ∀ {a b c}, restricts a b → restricts b c → restricts a c) : LE (Quotient s) :=
  ⟨Quotient.lift₂ (fun a b => restricts b a) fun a b a' b' ha hb => by
    obtain ⟨haa', ha'a⟩ := (equivalent a a').mp ha
    obtain ⟨hbb', hb'b⟩ := (equivalent b b').mp hb
    exact propext ⟨fun h => transitive hb'b (transitive h haa'),
      fun h => transitive hbb' (transitive h ha'a)⟩⟩

/-- Mutual restriction yields antisymmetry on tensor classes. -/
@[instance_reducible]
def quotientOrder (s : Setoid (Raw K S)) (restricts : Raw K S → Raw K S → Prop)
    (equivalent : ∀ a b, s.r a b ↔ restricts a b ∧ restricts b a)
    (reflexive : ∀ a, restricts a a)
    (transitive : ∀ {a b c}, restricts a b → restricts b c → restricts a c) :
    PartialOrder (Quotient s) :=
  letI : LE (Quotient s) := quotientLE s restricts equivalent transitive
  { le_refl := fun A => Quotient.inductionOn A reflexive
    le_trans := fun A B C => Quotient.inductionOn₃ A B C fun _ _ _ h g => transitive g h
    le_antisymm := fun A B => Quotient.inductionOn₂ A B fun a b h g =>
      Quotient.sound ((equivalent a b).mpr ⟨g, h⟩) }

/-- Lift a binary operation on tensor tables that respects the chosen setoid. -/
def quotientOperation (s : Setoid (Raw K S)) (operation : Raw K S → Raw K S → Raw K S)
    (congruent : ∀ {a a' b b'}, s.r a a' → s.r b b' → s.r (operation a b) (operation a' b')) :
    Quotient s → Quotient s → Quotient s :=
  Quotient.map₂ operation fun _ _ ha _ _ hb => congruent ha hb

/-- The raw tensor relabelings supply the laws for either restriction semiring. -/
@[instance_reducible]
def quotientSemiring (s : Setoid (Raw K S))
    (addCongr : ∀ {a a' b b'}, s.r a a' → s.r b b' → s.r (a + b) (a' + b'))
    (mulCongr : ∀ {a a' b b'}, s.r a a' → s.r b b' → s.r (a * b) (a' * b'))
    (relabel : ∀ {a b}, Relabels a b → s.r a b) : CommSemiring (Quotient s) := by
  letI : Zero (Quotient s) := ⟨Quotient.mk s 0⟩
  letI : One (Quotient s) := ⟨Quotient.mk s 1⟩
  letI : Add (Quotient s) := ⟨quotientOperation s (· + ·) addCongr⟩
  letI : Mul (Quotient s) := ⟨quotientOperation s (· * ·) mulCongr⟩
  have addComm (A B : Quotient s) : A + B = B + A :=
    Quotient.inductionOn₂ A B fun a b => Quotient.sound (relabel (comm_add_relabels a b))
  have mulComm (A B : Quotient s) : A * B = B * A :=
    Quotient.inductionOn₂ A B fun a b => Quotient.sound (relabel (comm_mul_relabels a b))
  have zeroAdd (A : Quotient s) : 0 + A = A :=
    Quotient.inductionOn A fun a => Quotient.sound (relabel (nil_add_relabels a))
  have oneMul (A : Quotient s) : 1 * A = A :=
    Quotient.inductionOn A fun a => Quotient.sound (relabel (unit_mul_relabels a))
  have zeroMul (A : Quotient s) : 0 * A = 0 :=
    Quotient.inductionOn A fun a => Quotient.sound (relabel (nil_mul_relabels a))
  have leftDistrib (A B C : Quotient s) : A * (B + C) = A * B + A * C :=
    Quotient.inductionOn₃ A B C fun a b c => Quotient.sound (relabel (distrib_left_relabels a b c))
  exact {
    add := (· + ·)
    mul := (· * ·)
    zero := 0
    one := 1
    nsmul := nsmulRec
    add_assoc := fun A B C => Quotient.inductionOn₃ A B C fun a b c =>
      Quotient.sound (relabel (assoc_add_relabels a b c))
    add_comm := addComm
    zero_add := zeroAdd
    add_zero := fun A => (addComm A 0).trans (zeroAdd A)
    mul_assoc := fun A B C => Quotient.inductionOn₃ A B C fun a b c =>
      Quotient.sound (relabel (assoc_mul_relabels a b c))
    mul_comm := mulComm
    one_mul := oneMul
    mul_one := fun A => (mulComm A 1).trans (oneMul A)
    zero_mul := zeroMul
    mul_zero := fun A => (mulComm A 0).trans (zeroMul A)
    left_distrib := leftDistrib
    right_distrib := fun A B C => by rw [mulComm, leftDistrib, mulComm C A, mulComm C B] }

end Raw

/-- Coefficient tensors modulo mutual local linear restriction. -/
def Tensor (K S : Type) [CommSemiring K] [Fintype S] :=
  Quotient (inferInstance : Setoid (Raw K S))

namespace Tensor

variable {K S : Type} [CommSemiring K] [Fintype S]

/-- Passes a raw multilinear table to its equivalence class under mutual restriction. -/
def ofRaw (A : Raw K S) : Tensor K S := Quotient.mk _ A

theorem ofRaw_eq {A B : Raw K S} (h : A ≈ B) : ofRaw A = ofRaw B :=
  Quotient.sound h

instance : LE (Tensor K S) :=
  Raw.quotientLE (inferInstance : Setoid (Raw K S)) Raw.Restricts (fun _ _ => Iff.rfl)
    (fun h g => Raw.Restricts.trans h g)

theorem ofRaw_le (A B : Raw K S) : ofRaw A ≤ ofRaw B ↔ B.Restricts A := Iff.rfl

instance : PartialOrder (Tensor K S) :=
  Raw.quotientOrder (inferInstance : Setoid (Raw K S)) Raw.Restricts
    (fun _ _ => Iff.rfl) Raw.Restricts.refl (fun h g => Raw.Restricts.trans h g)

instance : Zero (Tensor K S) := ⟨ofRaw 0⟩
instance : One (Tensor K S) := ⟨ofRaw 1⟩

instance : Add (Tensor K S) :=
  ⟨Raw.quotientOperation (inferInstance : Setoid (Raw K S)) (· + ·)
    fun h g => ⟨h.1.add g.1, h.2.add g.2⟩⟩

instance : Mul (Tensor K S) :=
  ⟨Raw.quotientOperation (inferInstance : Setoid (Raw K S)) (· * ·)
    fun h g => ⟨h.1.mul g.1, h.2.mul g.2⟩⟩

theorem ofRaw_add (A B : Raw K S) : ofRaw (A + B) = ofRaw A + ofRaw B := rfl
theorem ofRaw_mul (A B : Raw K S) : ofRaw (A * B) = ofRaw A * ofRaw B := rfl

instance : CommSemiring (Tensor K S) := by
  let laws : CommSemiring (Tensor K S) :=
    Raw.quotientSemiring (inferInstance : Setoid (Raw K S))
      (fun h g => ⟨h.1.add g.1, h.2.add g.2⟩)
      (fun h g => ⟨h.1.mul g.1, h.2.mul g.2⟩) Raw.relabel_of_relabels
  exact { laws with
    add := (· + ·)
    mul := (· * ·)
    zero := 0
    one := 1 }

theorem comm_add (A B : Tensor K S) : A + B = B + A := add_comm A B

theorem comm_mul (A B : Tensor K S) : A * B = B * A := mul_comm A B

theorem distrib_left (A B C : Tensor K S) : A * (B + C) = A * B + A * C :=
  (inferInstance : CommSemiring (Tensor K S)).left_distrib A B C

theorem add_le_add_right (A B C : Tensor K S) : A ≤ B → A + C ≤ B + C :=
  Quotient.inductionOn₃ A B C fun _ _ c h => Raw.Restricts.add h (.refl c)

theorem mul_le_mul_left (A B C : Tensor K S) : A ≤ B → C * A ≤ C * B :=
  Quotient.inductionOn₃ A B C fun _ _ c h => Raw.Restricts.mul (.refl c) h

end Tensor
end MatrixMultiplicationAllFields.MatrixExponent.Spectral
end

/-
# Finite coefficient tables

The product of local coordinate selectors is a weighted Kronecker delta.
It suffices to put the weight at one site.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Spectral.Raw

variable {K S : Type} [Fintype S] [Nonempty S]

section Tables

variable [CommSemiring K]

open Classical in
/-- Selects the appropriate branch of `if y = x s then if s = Classical.arbitrary S then a else
1 else 0`. -/
def selector {X : S → Type} (x : ∀ s, X s) (a : K) (s : S) (y : X s) : K :=
  if y = x s then if s = Classical.arbitrary S then a else 1 else 0

open Classical in
private theorem prod_selector {X : S → Type} (x y : ∀ s, X s) (a : K) :
    (∏ s, selector x a s (y s)) = if y = x then a else 0 := by
  by_cases h : y = x
  · subst y
    simp [selector]
  · rw [ite_eq_right h]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right hs)

variable (X : S → Type) [∀ s, Fintype (X s)]

/-- Coordinate expansion of any finite array as a sum of pure tensors. -/
def ofTable (f : (∀ s, X s) → K) : Raw K S := by
  classical
  exact ⟨X, ∀ s, X s, fun i => selector i (f i)⟩

@[simp] theorem coeff_ofTable (f : (∀ s, X s) → K) (x : ∀ s, X s) :
    (ofTable X f).coeff x = f x := by
  classical
  change (∑ i : ∀ s, X s, ∏ s, selector i (f i) s (x s)) = _
  simp [prod_selector]

end Tables

variable [Field K]

/-- Selecting a nonzero coefficient and scaling by its inverse recovers the unit. -/
theorem restricts_one (A : Raw K S) (h : ∃ x, A.coeff x ≠ 0) : A.Restricts 1 := by
  classical
  obtain ⟨x, hx⟩ := h
  refine (restricts_iff _ _).mpr ⟨fun s _ => selector x (A.coeff x)⁻¹ s, fun _ => ?_⟩
  change (∑ _ : Unit, ∏ _ : S, (1 : K)) = _
  simp [prod_selector, ite_mul, hx]

end MatrixMultiplicationAllFields.MatrixExponent.Spectral.Raw
end
