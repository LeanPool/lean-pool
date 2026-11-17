/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Order.UpperLower.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A lower set of exponent vectors is a finite disjoint union of translated
coordinate orthants. Dickson's lemma supplies a threshold above which each
coordinate is either fixed or unrestricted. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Truncate every coordinate of the exponent vector `a` at `B`, giving `i ↦ min (a i) B`. -/
def clampExponent {σ : Type*} (B : ℕ) (a : σ → ℕ) : σ → ℕ :=
  fun i => min (a i) B

/-- Membership in a lower exponent set is determined by a finite box. -/
theorem lowerSet_clamp_stabilizes {σ : Type*} [Finite σ]
    (S : Set (σ → ℕ)) (hS : IsLowerSet S) :
    ∃ B : ℕ, 0 < B ∧ ∀ a, a ∈ S ↔ clampExponent B a ∈ S := by
  classical
  let := Fintype.ofFinite σ
  let T : Set (σ → ℕ) := {a | Minimal (fun a => a ∉ S) a}
  have hT : T.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  let B := hT.toFinset.sup (fun a => Finset.univ.sup a) + 1
  have hbound (a : σ → ℕ) (ha : a ∈ T) (i : σ) : a i ≤ B := by
    have h₁ := Finset.le_sup (f := a) (Finset.mem_univ i)
    have h₂ := Finset.le_sup (f := fun a : σ → ℕ => Finset.univ.sup a)
      (hT.mem_toFinset.mpr ha)
    dsimp [B]
    omega
  refine ⟨B, by dsimp [B]; omega, ?_⟩
  intro a
  constructor
  · exact fun ha => hS (fun i => min_le_left _ _) ha
  · intro ha
    by_contra hn
    have hp : (Sᶜ).IsPWO := by
      intro f
      exact wellQuasiOrdered_le (fun n => (f n).val)
    obtain ⟨b, hba, hb⟩ := hp.exists_le_minimal hn
    apply hb.1
    apply hS (a := clampExponent B a) _ ha
    intro i
    exact le_min (hba i) (hbound b hb i)

/-- A truncated coordinate pattern, with value B marking its free coordinates. -/
abbrev orthantFree {σ : Type*} {B : ℕ} (b : σ → Fin (B + 1)) :=
  {i : σ // (b i).val = B}

/-- The total degree `∑ i, b i` of the base point of the orthant with truncated coordinate
pattern `b`. -/
def orthantBaseDegree {σ : Type*} [Fintype σ] {B : ℕ}
    (b : σ → Fin (B + 1)) : ℕ := ∑ i, (b i).val

/-- The point of the orthant with truncated pattern `b` obtained by adding `c` to the base
point `b` in the free coordinates (those where `b i = B`). -/
def orthantExpand {σ : Type*} {B : ℕ} (b : σ → Fin (B + 1))
    (c : orthantFree b → ℕ) : σ → ℕ :=
  fun i => (b i).val + if h : (b i).val = B then c ⟨i, h⟩ else 0

/-- Every point of the orthant with truncated pattern `b` truncates back to `b`. -/
lemma clamp_orthantExpand {σ : Type*} {B : ℕ}
    (b : σ → Fin (B + 1)) (c : orthantFree b → ℕ) :
    clampExponent B (orthantExpand b c) = fun i => (b i).val := by
  funext i
  simp only [clampExponent, orthantExpand]
  split_ifs with h
  · rw [h]
    omega
  · have hi := (b i).isLt
    omega

/-- The total degree of a point of the orthant with pattern `b` is the base degree of `b`
plus the total of the added free coordinates. -/
lemma orthantExpand_sum {σ : Type*} [Fintype σ] {B : ℕ}
    (b : σ → Fin (B + 1)) (c : orthantFree b → ℕ) :
    (∑ i, orthantExpand b c i) = orthantBaseDegree b + ∑ j, c j := by
  classical
  simp only [orthantExpand, Finset.sum_add_distrib, orthantBaseDegree]
  congr 1
  have hh := Finset.sum_subtype (p := fun i => (b i).val = B) (F := inferInstance)
      (Finset.univ.filter (fun i => (b i).val = B))
      (by simp) (fun i => if h : (b i).val = B then c ⟨i, h⟩ else 0)
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => (b i).val = B),
        if h : (b i).val = B then c ⟨i, h⟩ else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (b i).val = B <;> simp [hi]
    _ = _ := hh
    _ = ∑ j, c j := Finset.sum_congr rfl (fun j _ => by simp [j.property])

/-- Every cell of the truncation map is a coordinate orthant. -/
def orthantExpandEquiv {σ : Type*} {B : ℕ} (b : σ → Fin (B + 1)) :
    (orthantFree b → ℕ) ≃
      {a : σ → ℕ // clampExponent B a = fun i => (b i).val} where
  toFun c := ⟨orthantExpand b c, clamp_orthantExpand b c⟩
  invFun a := fun i => a.val i.val - B
  left_inv c := by
    funext i
    simp [orthantExpand, i.property]
  right_inv a := by
    apply Subtype.ext
    funext i
    have hi := congrFun a.property i
    change min (a.val i) B = (b i).val at hi
    simp only [orthantExpand]
    split_ifs with h
    · rw [h]
      omega
    · have hb := (b i).isLt
      simp only [add_zero]
      omega

/-- Truncation gives the unique cell containing any exponent vector. -/
def exponentPattern {σ : Type*} (B : ℕ) (a : σ → ℕ) : σ → Fin (B + 1) :=
  fun i => ⟨min (a i) B, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- A bounded slice of an orthant is a bounded exponent simplex in its free
coordinates. -/
def boundedOrthantEquiv {σ : Type*} [Fintype σ] {B N : ℕ}
    (b : σ → Fin (B + 1)) (hN : orthantBaseDegree b ≤ N) :
    {c : orthantFree b → ℕ // ∑ i, c i ≤ N - orthantBaseDegree b} ≃
      {a : σ → ℕ // clampExponent B a = (fun i => (b i).val) ∧ ∑ i, a i ≤ N} := by
  let e := orthantExpandEquiv b
  refine Equiv.ofBijective
    (fun c => ⟨orthantExpand b c.val, clamp_orthantExpand b c.val, ?_⟩) ⟨?_, ?_⟩
  · rw [orthantExpand_sum]
    omega
  · intro c d h
    have hv : orthantExpand b c.val = orthantExpand b d.val :=
      congrArg (fun a : {a : σ → ℕ //
        clampExponent B a = (fun i => (b i).val) ∧ ∑ i, a i ≤ N} => a.val) h
    apply Subtype.ext
    apply e.injective
    exact Subtype.ext hv
  · intro a
    let c := e.symm ⟨a.val, a.property.1⟩
    have he : orthantExpand b c = a.val :=
      congrArg Subtype.val (e.apply_symm_apply ⟨a.val, a.property.1⟩)
    have hc : ∑ i, c i ≤ N - orthantBaseDegree b := by
      have hs := orthantExpand_sum b c
      rw [he] at hs
      omega
    exact ⟨⟨c, hc⟩, Subtype.ext he⟩

end
end CCDN
