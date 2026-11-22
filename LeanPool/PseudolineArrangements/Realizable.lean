/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.Chirotope
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Realizable chirotopes

The chirotope of a family of vectors `v : E → 𝕜 ^ r` over an ordered field takes an ordered
`r`-tuple of elements of `E` to the sign of the determinant whose rows are the corresponding
vectors. When the vectors span `𝕜 ^ r`, this is a chirotope (`Chirotope.isChirotope_ofVectorsFun`):
its supports are the bases of the linear matroid of `v`, and the three-term Grassmann–Plücker
relations are the signs of the three-term Plücker identity for determinants, which we prove for
every rank (`Chirotope.det_plucker`).

## References

* A. Björner, M. Las Vergnas, B. Sturmfels, N. White, G. M. Ziegler, *Oriented Matroids*,
  2nd ed., Cambridge University Press, 1999, §3.5 and §3.6.
* J. Richter-Gebert, G. M. Ziegler, *Oriented matroids*, Chapter 6 of *Handbook of Discrete and
  Computational Geometry*, 3rd ed., 2017, §6.2.3.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv Matrix

namespace Chirotope

variable {r : ℕ} {E : Type*} {𝕜 : Type*} [Field 𝕜]

/-! ### Determinants of rows -/

/-- A matrix of nonzero determinant has rows spanning the whole space. -/
theorem span_rows_eq_top_of_det_ne_zero {A : Matrix (Fin r) (Fin r) 𝕜} (hA : A.det ≠ 0) :
    Submodule.span 𝕜 (Set.range A) = ⊤ :=
  (linearIndependent_rows_of_det_ne_zero hA).span_eq_top_of_card_eq_finrank' (by simp)

/-- Replacing a row by a vector of the span of the other rows gives determinant zero. -/
theorem det_updateRow_eq_zero_of_mem_span (A : Matrix (Fin r) (Fin r) 𝕜) (k : Fin r)
    {w : Fin r → 𝕜} (hw : w ∈ Submodule.span 𝕜 (Set.range (A.updateRow k 0))) :
    (A.updateRow k w).det = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hw
  have h := det_updateRow_sum (A.updateRow k 0) k c
  rw [updateRow_idem] at h
  rw [h, det_eq_zero_of_row_eq_zero k (fun j => by simp), smul_zero]

/-- Replacing a row of an invertible matrix by a vector outside the span of the other rows keeps
the determinant nonzero. -/
theorem det_updateRow_ne_zero_of_notMem_span {A : Matrix (Fin r) (Fin r) 𝕜} (hA : A.det ≠ 0)
    (k : Fin r) {w : Fin r → 𝕜}
    (hw : w ∉ Submodule.span 𝕜 (Set.range (A.updateRow k 0))) :
    (A.updateRow k w).det ≠ 0 := by
  have hw' : w ∈ Submodule.span 𝕜 (Set.range A) := by
    rw [span_rows_eq_top_of_det_ne_zero hA]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hw'
  rw [det_updateRow_sum, smul_eq_mul]
  refine mul_ne_zero (fun hck => hw ?_) hA
  have : ∑ m, c m • A m = ∑ m, c m • A.updateRow k 0 m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m = k
    · subst hm; simp [hck]
    · simp [updateRow_ne hm]
  rw [this]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-! ### The three-term Plücker identity -/

/-- The determinant with rows `i` and `j` of `X` replaced by `p` and `q`. -/
noncomputable def plucker (X : Matrix (Fin r) (Fin r) 𝕜) (i j : Fin r) (p q : Fin r → 𝕜) : 𝕜 :=
  ((X.updateRow i p).updateRow j q).det

theorem plucker_self (X : Matrix (Fin r) (Fin r) 𝕜) {i j : Fin r} (hij : i ≠ j)
    (p : Fin r → 𝕜) : plucker X i j p p = 0 :=
  det_zero_of_row_eq hij (by simp [updateRow_ne hij])

/-- The determinant as a linear function of the row `k`. -/
noncomputable def detRowLinear (A : Matrix (Fin r) (Fin r) 𝕜) (k : Fin r) :
    (Fin r → 𝕜) →ₗ[𝕜] 𝕜 where
  toFun p := (A.updateRow k p).det
  map_add' := det_updateRow_add A k
  map_smul' c p := det_updateRow_smul A k c p

theorem plucker_eq_toLinearMap (X : Matrix (Fin r) (Fin r) 𝕜) {i j : Fin r} (hij : i ≠ j)
    (p q : Fin r → 𝕜) : plucker X i j p q = detRowLinear (X.updateRow j q) i p := by
  rw [plucker, updateRow_comm _ hij]
  rfl

theorem plucker_eq_toLinearMap_right (X : Matrix (Fin r) (Fin r) 𝕜) (i j : Fin r)
    (p q : Fin r → 𝕜) : plucker X i j p q = detRowLinear (X.updateRow i p) j q :=
  rfl

theorem plucker_swap (X : Matrix (Fin r) (Fin r) 𝕜) {i j : Fin r} (hij : i ≠ j)
    (p q : Fin r → 𝕜) : plucker X i j q p = -plucker X i j p q := by
  have h := plucker_self X hij (p + q)
  rw [plucker_eq_toLinearMap X hij, map_add, ← plucker_eq_toLinearMap X hij,
    ← plucker_eq_toLinearMap X hij, plucker_eq_toLinearMap_right, map_add,
    plucker_eq_toLinearMap_right X i j q, map_add, ← plucker_eq_toLinearMap_right,
    ← plucker_eq_toLinearMap_right, ← plucker_eq_toLinearMap_right,
    ← plucker_eq_toLinearMap_right, plucker_self X hij, plucker_self X hij] at h
  linear_combination h

theorem plucker_eq_zero_of_row {X : Matrix (Fin r) (Fin r) 𝕜} {i j k : Fin r} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (q : Fin r → 𝕜) : plucker X i j (X k) q = 0 :=
  det_zero_of_row_eq hki.symm (by simp [updateRow_ne hij, updateRow_ne hki, updateRow_ne hkj])

omit [Field 𝕜] in
/-- The rows of the doubly updated matrix lie in the span of the untouched rows and the two new
rows. -/
theorem range_updateRow_updateRow_subset (X : Matrix (Fin r) (Fin r) 𝕜) (i j : Fin r)
    (p q : Fin r → 𝕜) (T : Set (Fin r → 𝕜)) (hp : p ∈ T) (hq : q ∈ T)
    (hX : ∀ k, k ≠ i → k ≠ j → X k ∈ T) :
    Set.range ((X.updateRow i p).updateRow j q) ⊆ T := by
  rintro _ ⟨k, rfl⟩
  by_cases hkj : k = j
  · subst hkj; simpa using hq
  by_cases hki : k = i
  · subst hki; simpa [updateRow_ne hkj] using hp
  simpa [updateRow_ne hkj, updateRow_ne hki] using hX k hki hkj

/-- The three-term Plücker identity: for `i ≠ j`, the determinants `[p q]` with rows `i, j`
replaced by `p, q` satisfy `[p₁ p₂][p₃ p₄] - [p₁ p₃][p₂ p₄] + [p₁ p₄][p₂ p₃] = 0`. -/
theorem det_plucker (X : Matrix (Fin r) (Fin r) 𝕜) {i j : Fin r} (hij : i ≠ j)
    (p₁ p₂ p₃ p₄ : Fin r → 𝕜) :
    plucker X i j p₁ p₂ * plucker X i j p₃ p₄ - plucker X i j p₁ p₃ * plucker X i j p₂ p₄ +
      plucker X i j p₁ p₄ * plucker X i j p₂ p₃ = 0 := by
  set ω := plucker X i j
  have hself : ∀ p, ω p p = 0 := plucker_self X hij
  have hswap : ∀ p q, ω q p = -ω p q := plucker_swap X hij
  set ℓ : (Fin r → 𝕜) → (Fin r → 𝕜) →ₗ[𝕜] 𝕜 := fun q => detRowLinear (X.updateRow j q) i
  have hℓ : ∀ p q, ℓ q p = ω p q := fun p q => (plucker_eq_toLinearMap X hij p q).symm
  set L : (Fin r → 𝕜) →ₗ[𝕜] 𝕜 := ω p₃ p₄ • ℓ p₂ - ω p₂ p₄ • ℓ p₃ + ω p₂ p₃ • ℓ p₄
  have hL : ∀ p, L p = ω p p₂ * ω p₃ p₄ - ω p p₃ * ω p₂ p₄ + ω p p₄ * ω p₂ p₃ := fun p => by
    simp only [L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, hℓ,
      smul_eq_mul]
    ring
  set T : Set (Fin r → 𝕜) := {p | ∃ k, k ≠ i ∧ k ≠ j ∧ X k = p} ∪ {p₂, p₃, p₄}
  have hT : ∀ p ∈ T, L p = 0 := by
    rintro p (⟨k, hki, hkj, rfl⟩ | hp)
    · rw [hL]; simp [ω, plucker_eq_zero_of_row hij hki hkj]
    · rcases hp with rfl | rfl | rfl
      · rw [hL, hself]; ring
      · rw [hL, hself, hswap p₂]; ring
      · rw [hL, hself, hswap p₂, hswap p₃]; ring
  have hmemT : ∀ k, k ≠ i → k ≠ j → X k ∈ T := fun k hki hkj => Or.inl ⟨k, hki, hkj, rfl⟩
  by_cases hS : Submodule.span 𝕜 T = ⊤
  · have hmem : p₁ ∈ Submodule.span 𝕜 T := hS ▸ trivial
    have hker : Submodule.span 𝕜 T ≤ LinearMap.ker L :=
      Submodule.span_le.2 fun p hp => hT p hp
    rw [← hL]
    exact hker hmem
  · have hzero : ∀ p q, p ∈ T → q ∈ T → ω p q = 0 := by
      intro p q hp hq
      by_contra hne
      apply hS
      rw [eq_top_iff, ← span_rows_eq_top_of_det_ne_zero hne]
      exact Submodule.span_mono (range_updateRow_updateRow_subset X i j p q T hp hq hmemT)
    have h23 := hzero p₂ p₃ (by simp [T]) (by simp [T])
    have h24 := hzero p₂ p₄ (by simp [T]) (by simp [T])
    have h34 := hzero p₃ p₄ (by simp [T]) (by simp [T])
    rw [h23, h24, h34]
    ring

/-! ### The chirotope of a family of vectors -/

variable [LinearOrder 𝕜]

/-- The function of a family of vectors: the sign of the determinant whose rows are the vectors
of the tuple. Only a linear order is needed to take signs. -/
noncomputable def ofVectorsFun (v : E → Fin r → 𝕜) : (Fin r → E) → SignType :=
  fun b => SignType.sign (Matrix.of fun i j => v (b i) j).det

/-- Realizable over an ordered field `𝕜`: the function of some family of vectors. -/
def IsRealizable (c : (Fin r → E) → SignType) (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] : Prop :=
  ∃ v : E → Fin r → 𝕜, c = ofVectorsFun v

theorem ofVectorsFun_ne_zero_iff (v : E → Fin r → 𝕜) (b : Fin r → E) :
    ofVectorsFun v b ≠ 0 ↔ (Matrix.of fun i j => v (b i) j).det ≠ 0 := by
  simp [ofVectorsFun]

omit [Field 𝕜] [LinearOrder 𝕜] in
theorem of_update (v : E → Fin r → 𝕜) (b : Fin r → E) (k : Fin r) (e : E) :
    (Matrix.of fun i j => v (Function.update b k e i) j) =
      (Matrix.of fun i j => v (b i) j).updateRow k (v e) := by
  ext i j
  by_cases hi : i = k
  · subst hi; simp
  · simp [hi]

theorem range_update_of_injective {b : Fin r → E} (hb : Function.Injective b) (k : Fin r)
    (f : E) : Set.range (Function.update b k f) = insert f (Set.range b \ {b k}) := by
  classical
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, rfl⟩
    by_cases hm : m = k
    · subst hm; simp
    · right
      simp only [Function.update_of_ne hm]
      exact ⟨⟨m, rfl⟩, fun h => hm (hb h)⟩
  · rintro (rfl | ⟨⟨m, rfl⟩, hm⟩)
    · exact ⟨k, by simp⟩
    · have : m ≠ k := fun h => hm (h ▸ rfl)
      exact ⟨m, by simp [this]⟩

/-- The supports of the nonzero values of the chirotope of a family of vectors satisfy the basis
exchange property. -/
theorem exchangeProperty_ofVectorsFun (v : E → Fin r → 𝕜) :
    Matroid.ExchangeProperty
      (fun B : Set E => ∃ b, ofVectorsFun v b ≠ 0 ∧ Set.range b = B) := by
  classical
  rintro _ _ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩ a ⟨⟨k, rfl⟩, hk⟩
  rw [ofVectorsFun_ne_zero_iff] at hb₁ hb₂
  set A := Matrix.of fun i j => v (b₁ i) j
  set H := Submodule.span 𝕜 (Set.range (A.updateRow k 0))
  have hinj : Function.Injective b₁ := by
    intro m m' h
    by_contra hne
    exact hb₁ (det_zero_of_row_eq hne (by ext; simp [A, h]))
  obtain ⟨l, hl⟩ : ∃ l, v (b₂ l) ∉ H := by
    by_contra! hall
    have htop : ⊤ ≤ H := by
      rw [← span_rows_eq_top_of_det_ne_zero hb₂, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hall l
    have := det_updateRow_eq_zero_of_mem_span A k (htop (Submodule.mem_top (x := A k)))
    rw [updateRow_eq_self] at this
    exact hb₁ this
  refine ⟨b₂ l, ⟨⟨l, rfl⟩, ?_⟩, Function.update b₁ k (b₂ l), ?_, ?_⟩
  · rintro ⟨m, hm⟩
    by_cases hmk : m = k
    · subst hmk; exact hk ⟨l, hm.symm⟩
    · apply hl
      refine Submodule.subset_span ⟨m, ?_⟩
      rw [updateRow_ne hmk, ← hm]
      rfl
  · rw [ofVectorsFun_ne_zero_iff, of_update]
    exact det_updateRow_ne_zero_of_notMem_span hb₁ k hl
  · exact range_update_of_injective hinj k _

/-- A spanning family of vectors has a tuple with nonzero determinant. -/
theorem exists_ofVectorsFun_ne_zero (v : E → Fin r → 𝕜)
    (hv : Submodule.span 𝕜 (Set.range v) = ⊤) : ∃ b, ofVectorsFun v b ≠ 0 := by
  set B := Module.Basis.ofSpan hv.ge
  set e := (Pi.basisFun 𝕜 (Fin r)).indexEquiv B
  have hmem : ∀ k, ∃ x, v x = B (e k) := fun k => Module.Basis.ofSpan_subset hv.ge ⟨e k, rfl⟩
  choose b hb using hmem
  refine ⟨b, (ofVectorsFun_ne_zero_iff v b).2 ?_⟩
  have hli : LinearIndependent 𝕜 (fun k => B (e k)) := B.linearIndependent.comp e e.injective
  have hrow : (Matrix.of fun i j => v (b i) j).row = fun k => B (e k) := by
    funext k; exact hb k
  rw [← hrow] at hli
  exact (isUnit_iff_isUnit_det _).1 (linearIndependent_row_iff_isUnit.1 hli) |>.ne_zero

variable [IsStrictOrderedRing 𝕜]

/-- A spanning family of vectors over an ordered field has a chirotope. -/
theorem isChirotope_ofVectorsFun (v : E → Fin r → 𝕜) (hv : Submodule.span 𝕜 (Set.range v) = ⊤) :
    IsChirotope (ofVectorsFun v) := by
  classical
  refine ⟨⟨ofVectorsFun v, exists_ofVectorsFun_ne_zero v hv, ?_, ?_,
    exchangeProperty_ofVectorsFun v, ?_⟩, rfl⟩
  · intro b hb
    obtain ⟨m, m', h, hne⟩ : ∃ m m', b m = b m' ∧ m ≠ m' := by
      by_contra! H
      exact hb H
    simp only [ofVectorsFun, sign_eq_zero_iff]
    exact det_zero_of_row_eq hne (by ext; simp [h])
  · intro b σ
    have : (Matrix.of fun i j => v ((b ∘ σ) i) j) = (Matrix.of fun i j => v (b i) j).submatrix σ id
      := by ext; simp
    simp only [ofVectorsFun, this, det_permute, sign_mul, permSign, sign_intCast]
  · intro x i j hij a b c d
    simp only
    have hupd : ∀ u w,
        (Matrix.of fun k l => v (Function.update (Function.update x i u) j w k) l).det
          = plucker (Matrix.of fun k l => v (x k) l) i j (v u) (v w) := by
      intro u w
      rw [plucker, of_update, of_update]
    simp only [ofVectorsFun, hupd, ← sign_mul]
    set ω := plucker (Matrix.of fun k l => v (x k) l) i j
    have := det_plucker (Matrix.of fun k l => v (x k) l) hij (v a) (v b) (v c) (v d)
    have h := gp3_sign_of_add_eq_zero (x := ω (v a) (v b) * ω (v c) (v d))
      (y := -(ω (v a) (v c) * ω (v b) (v d))) (z := ω (v a) (v d) * ω (v b) (v c))
      (by linear_combination this)
    rwa [Left.sign_neg] at h

end Chirotope

end LeanPool.PseudolineArrangements
