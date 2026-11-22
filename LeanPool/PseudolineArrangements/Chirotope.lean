/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Linarith.Frontend

/-!
# Chirotopes

A chirotope of rank `r` on a type `E` is a function `χ` from ordered `r`-tuples of elements of
`E` to signs, not identically zero, vanishing on tuples with a repeated entry, alternating, whose
nonzero supports are the bases of a matroid, and satisfying the three-term Grassmann–Plücker
relations. This is the definition of Björner–Las Vergnas–Sturmfels–White–Ziegler
(Definition 3.5.3, in the form of Lemma 3.5.4).

We define chirotopes (`Chirotope`), the predicate `IsChirotope` for a function on tuples, the
matroid of a chirotope on a finite type, simple and uniform chirotopes, and the two basic
operations: reorientation on a subset (`Chirotope.reorientFun`) and relabelling along a bijection
(`Chirotope.relabelFun`). Both produce chirotopes (`Chirotope.isChirotope_reorientFun`,
`Chirotope.isChirotope_relabelFun`).

## References

* A. Björner, M. Las Vergnas, B. Sturmfels, N. White, G. M. Ziegler, *Oriented Matroids*,
  2nd ed., Cambridge University Press, 1999, §3.5.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv

/-- `Equiv.Perm.sign` read in `SignType`. -/
def permSign {r : ℕ} (σ : Perm (Fin r)) : SignType := SignType.sign ((Perm.sign σ : ℤˣ) : ℤ)

/-- The three-term Grassmann–Plücker condition on three products: all zero, or both signs occur. -/
def GP3 (s t u : SignType) : Prop :=
  (s = 0 ∧ t = 0 ∧ u = 0) ∨ ((s = 1 ∨ t = 1 ∨ u = 1) ∧ (s = -1 ∨ t = -1 ∨ u = -1))

instance (s t u : SignType) : Decidable (GP3 s t u) := by unfold GP3; infer_instance

theorem GP3.neg {s t u : SignType} (h : GP3 s t u) : GP3 (-s) (-t) (-u) := by
  revert s t u; decide

/-- The Grassmann–Plücker condition is invariant under a common sign `±1`. -/
theorem GP3.mul_left {s t u : SignType} (h : GP3 s t u) {l : SignType} (hl : l * l = 1) :
    GP3 (l * s) (l * t) (l * u) := by
  revert s t u; revert l; decide

/-- Three numbers of sum zero satisfy the Grassmann–Plücker sign condition. -/
theorem gp3_sign_of_add_eq_zero {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {x y z : 𝕜} (h : x + y + z = 0) :
    GP3 (SignType.sign x) (SignType.sign y) (SignType.sign z) := by
  unfold GP3
  rcases lt_trichotomy x 0 with hx | hx | hx <;>
  rcases lt_trichotomy y 0 with hy | hy | hy <;>
  rcases lt_trichotomy z 0 with hz | hz | hz <;>
  simp [sign_neg, sign_pos, hx, hy, hz] <;> linarith

/-- A chirotope of rank `r` on `E` (BLSWZ Definition 3.5.3, in the form of Lemma 3.5.4). -/
structure Chirotope (r : ℕ) (E : Type*) where
  /-- The value on an ordered `r`-tuple. -/
  toFun : (Fin r → E) → SignType
  /-- Not identically zero. -/
  exists_ne_zero : ∃ b, toFun b ≠ 0
  /-- Zero on tuples with a repeated entry. -/
  eq_zero_of_not_injective : ∀ b, ¬ Function.Injective b → toFun b = 0
  /-- Alternating. -/
  comp_perm : ∀ (b : Fin r → E) (σ : Perm (Fin r)), toFun (b ∘ σ) = permSign σ * toFun b
  /-- The supports of nonzero values are the bases of a matroid. -/
  isBase_exchange :
    Matroid.ExchangeProperty (fun B : Set E => ∃ b, toFun b ≠ 0 ∧ Set.range b = B)
  /-- The three-term Grassmann–Plücker relations. -/
  grassmannPlucker : ∀ (x : Fin r → E) (i j : Fin r), i ≠ j → ∀ a b c d : E,
    let s := fun u v => toFun (Function.update (Function.update x i u) j v)
    GP3 (s a b * s c d) (-(s a c * s b d)) (s a d * s b c)

/-- A function on ordered `r`-tuples is a chirotope function when some chirotope has it as its
values. -/
def IsChirotope {r : ℕ} {E : Type*} (c : (Fin r → E) → SignType) : Prop :=
  ∃ χ : Chirotope r E, χ.toFun = c

namespace Chirotope

variable {r : ℕ} {E E' : Type*}

/-- A chirotope is read as its function on ordered tuples. -/
instance : CoeFun (Chirotope r E) (fun _ => (Fin r → E) → SignType) := ⟨Chirotope.toFun⟩

theorem isChirotope (χ : Chirotope r E) : IsChirotope (⇑χ) := ⟨χ, rfl⟩

/-- The matroid of bases of a chirotope on a finite type. -/
def matroid [Finite E] (χ : Chirotope r E) : Matroid E :=
  Matroid.ofIsBaseOfFinite Set.finite_univ (fun B => ∃ b, χ b ≠ 0 ∧ Set.range b = B)
    (by obtain ⟨b, hb⟩ := χ.exists_ne_zero; exact ⟨_, b, hb, rfl⟩) χ.isBase_exchange
    (fun _ _ => Set.subset_univ _)

theorem matroid_isBase_iff [Finite E] (χ : Chirotope r E) (B : Set E) :
    χ.matroid.IsBase B ↔ ∃ b, χ b ≠ 0 ∧ Set.range b = B := by
  simp [matroid]

/-- Simple: every element, and every pair of distinct elements, lies in a basis (no loops and no
parallel pairs). -/
def IsSimple (χ : Chirotope r E) : Prop :=
  (∀ e, ∃ b, χ b ≠ 0 ∧ e ∈ Set.range b) ∧
    ∀ e f, e ≠ f → ∃ b, χ b ≠ 0 ∧ e ∈ Set.range b ∧ f ∈ Set.range b

/-- Uniform: nonzero on every injective tuple. -/
def IsUniform (c : (Fin r → E) → SignType) : Prop := ∀ b, Function.Injective b → c b ≠ 0

/-! ### Reorientation -/

open scoped Classical in
/-- The sign `-1` on `A` and `1` off `A`. -/
noncomputable def reorientSign (A : Set E) (e : E) : SignType := if e ∈ A then -1 else 1

theorem reorientSign_mul_self (A : Set E) (e : E) : reorientSign A e * reorientSign A e = 1 := by
  unfold reorientSign; split_ifs <;> rfl

/-- Reorientation on `A`: one factor `-1` for each entry of the tuple lying in `A`. -/
noncomputable def reorientFun (c : (Fin r → E) → SignType) (A : Set E) :
    (Fin r → E) → SignType :=
  fun b => (∏ i, reorientSign A (b i)) * c b

theorem prod_reorientSign_mul_self (A : Set E) (b : Fin r → E) :
    (∏ i, reorientSign A (b i)) * (∏ i, reorientSign A (b i)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  simp [reorientSign_mul_self]

theorem reorientFun_ne_zero_iff (c : (Fin r → E) → SignType) (A : Set E) (b : Fin r → E) :
    reorientFun c A b ≠ 0 ↔ c b ≠ 0 := by
  unfold reorientFun
  constructor
  · intro h hc; exact h (by rw [hc, mul_zero])
  · intro h h'
    apply h
    have := congrArg ((∏ i, reorientSign A (b i)) * ·) h'
    simpa [← mul_assoc, prod_reorientSign_mul_self] using this

/-- The product of the reorientation signs of a tuple with two entries replaced. -/
theorem prod_reorientSign_update_update (A : Set E) (x : Fin r → E) {i j : Fin r} (hij : i ≠ j)
    (u v : E) :
    ∏ k, reorientSign A (Function.update (Function.update x i u) j v k) =
      reorientSign A u * reorientSign A v *
        ∏ k ∈ (Finset.univ \ {j}) \ {i}, reorientSign A (x k) := by
  classical
  have h1 : ∀ k, reorientSign A (Function.update (Function.update x i u) j v k) =
      Function.update (fun k => reorientSign A (Function.update x i u k)) j
        (reorientSign A v) k := fun k => by
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have h2 : ∀ k, reorientSign A (Function.update x i u k) =
      Function.update (fun k => reorientSign A (x k)) i (reorientSign A u) k := fun k => by
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp_rw [h1]
  rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
  simp_rw [h2]
  rw [Finset.prod_update_of_mem (by simp [hij])]
  ac_rfl

/-- The reorientation of a chirotope on `A`, as a chirotope. -/
noncomputable def reorient (χ : Chirotope r E) (A : Set E) : Chirotope r E where
  toFun := reorientFun χ A
  exists_ne_zero := by
    obtain ⟨b, hb⟩ := χ.exists_ne_zero
    exact ⟨b, (reorientFun_ne_zero_iff _ _ _).2 hb⟩
  eq_zero_of_not_injective b hb := by
    simp [reorientFun, χ.eq_zero_of_not_injective b hb]
  comp_perm b σ := by
    unfold reorientFun
    rw [χ.comp_perm, Function.comp_def, Equiv.prod_comp σ (fun i => reorientSign A (b i))]
    exact mul_left_comm _ _ _
  isBase_exchange := by
    have : (fun B : Set E => ∃ b, reorientFun χ A b ≠ 0 ∧ Set.range b = B) =
        fun B : Set E => ∃ b, χ b ≠ 0 ∧ Set.range b = B := by
      funext B
      simp only [reorientFun_ne_zero_iff]
    rw [this]
    exact χ.isBase_exchange
  grassmannPlucker x i j hij a b c d := by
    have hgp := χ.grassmannPlucker x i j hij a b c d
    simp only at hgp ⊢
    unfold reorientFun
    simp only [prod_reorientSign_update_update A x hij]
    set K := ∏ k ∈ (Finset.univ \ {j}) \ {i}, reorientSign A (x k)
    have hK : K * K = 1 := by
      rw [← Finset.prod_mul_distrib]
      simp [reorientSign_mul_self]
    set l := reorientSign A a * reorientSign A b * reorientSign A c * reorientSign A d
    have hl : l * l = 1 := by
      have ha := reorientSign_mul_self A a
      have hb := reorientSign_mul_self A b
      have hc := reorientSign_mul_self A c
      have hd := reorientSign_mul_self A d
      calc l * l = (reorientSign A a * reorientSign A a) * (reorientSign A b * reorientSign A b) *
          (reorientSign A c * reorientSign A c) * (reorientSign A d * reorientSign A d) := by
            simp only [l]; ac_rfl
        _ = 1 := by rw [ha, hb, hc, hd]; simp
    convert hgp.mul_left hl using 1
    · calc _ = (K * K) * (l * (χ (Function.update (Function.update x i a) j b) *
            χ (Function.update (Function.update x i c) j d))) := by simp only [l]; ac_rfl
        _ = _ := by rw [hK, one_mul]
    · rw [mul_neg]
      congr 1
      calc _ = (K * K) * (l * (χ (Function.update (Function.update x i a) j c) *
            χ (Function.update (Function.update x i b) j d))) := by simp only [l]; ac_rfl
        _ = _ := by rw [hK, one_mul]
    · calc _ = (K * K) * (l * (χ (Function.update (Function.update x i a) j d) *
            χ (Function.update (Function.update x i b) j c))) := by simp only [l]; ac_rfl
        _ = _ := by rw [hK, one_mul]

/-- The reorientation of a chirotope is a chirotope (BLSWZ §3.5). -/
theorem isChirotope_reorientFun (χ : Chirotope r E) (A : Set E) :
    IsChirotope (reorientFun χ A) := ⟨χ.reorient A, rfl⟩

/-! ### Relabelling -/

/-- Relabelling along `E ≃ E'`. -/
def relabelFun (e : E ≃ E') (c : (Fin r → E) → SignType) : (Fin r → E') → SignType :=
  fun b => c (e.symm ∘ b)

/-- The relabelling of a chirotope along a bijection, as a chirotope. -/
def relabel (e : E ≃ E') (χ : Chirotope r E) : Chirotope r E' where
  toFun := relabelFun e χ
  exists_ne_zero := by
    obtain ⟨b, hb⟩ := χ.exists_ne_zero
    refine ⟨e ∘ b, ?_⟩
    simpa [relabelFun, Function.comp_def] using hb
  eq_zero_of_not_injective b hb :=
    χ.eq_zero_of_not_injective _ fun h => hb (Function.Injective.of_comp h)
  comp_perm b σ := χ.comp_perm (e.symm ∘ b) σ
  isBase_exchange := by
    have key : ∀ B : Set E', (∃ b, relabelFun e χ b ≠ 0 ∧ Set.range b = B) ↔
        ∃ b, χ b ≠ 0 ∧ Set.range b = e.symm '' B := by
      intro B
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨e.symm ∘ b, hb, Set.range_comp _ _⟩
      · rintro ⟨b, hb, hB⟩
        refine ⟨e ∘ b, by simpa [relabelFun, Function.comp_def] using hb, ?_⟩
        rw [Set.range_comp, hB, Equiv.image_symm_image]
    intro X Y hX hY a ha
    rw [key] at hX hY
    have ha' : e.symm a ∈ e.symm '' X \ e.symm '' Y := by
      rw [← Set.image_sdiff e.symm.injective]
      exact Set.mem_image_of_mem _ ha
    obtain ⟨f, hf, hB⟩ := χ.isBase_exchange _ _ hX hY _ ha'
    rw [← Set.image_sdiff e.symm.injective] at hf
    obtain ⟨f', hf', rfl⟩ := hf
    refine ⟨f', hf', (key _).2 ?_⟩
    rw [Set.image_insert_eq, Set.image_sdiff e.symm.injective, Set.image_singleton]
    exact hB
  grassmannPlucker x i j hij a b c d := by
    have hgp := χ.grassmannPlucker (e.symm ∘ x) i j hij (e.symm a) (e.symm b) (e.symm c)
      (e.symm d)
    simp only [relabelFun, Function.comp_update] at hgp ⊢
    exact hgp

/-- The relabelling of a chirotope is a chirotope. -/
theorem isChirotope_relabelFun (e : E ≃ E') (χ : Chirotope r E) :
    IsChirotope (relabelFun e χ) := ⟨χ.relabel e, rfl⟩

end Chirotope

end LeanPool.PseudolineArrangements
