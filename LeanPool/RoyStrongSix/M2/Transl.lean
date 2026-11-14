/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Geom
public import LeanPool.RoyStrongSix.M2.HDim
public import LeanPool.RoyStrongSix.M2.Veronese

/-!
# Translations on `B = K[X, Y, Z]`

* `blk`: the two blocks, `X` and `(Y, Z)`.
* `transl g`: the `K`-algebra map with `(transl g P)(pt h) = P(pt (g h))`. It sends `X ↦ X + g_x`,
  `Y ↦ g_y Y`, `Z ↦ g_y⁻¹ Z`.
* `transl_mem_FLE`: it preserves block degrees.
* `transl_comp_inv`: `transl (g⁻¹) ∘ transl g = id`.
* **`hfun_vanish_transl`**: `hfun (vanish (g·E)) = hfun (vanish E)`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

/-- The blocks: `X` is block `0`; `Y` and `Z` are block `1`. -/
def blk : V3 d0 d1 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The images of the variables under translation by `g`. -/
noncomputable def translVar (g : GPt K d0 d1) : V3 d0 d1 → MvPolynomial (V3 d0 d1) K :=
  Sum.elim (fun k => X (Sum.inl k) + C (g.1 k))
    (Sum.elim (fun j => C ((g.2 j : Kˣ) : K) * X (Sum.inr (Sum.inl j)))
      (fun j => C (((g.2 j)⁻¹ : Kˣ) : K) * X (Sum.inr (Sum.inr j))))

/-- Translation by `g`. -/
noncomputable def transl (g : GPt K d0 d1) : MvPolynomial (V3 d0 d1) K →ₐ[K] MvPolynomial (V3 d0
  d1) K :=
  aeval (translVar g)

omit [CharZero K] in
theorem eval_translVar (g h : GPt K d0 d1) (v : V3 d0 d1) :
    eval (pt h) (translVar g v) = pt (gmul g h) v := by
  rcases v with k | j | j
  · simp [translVar, pt, gmul, add_comm]
  · simp [translVar, pt, gmul, mul_comm]
  · simp [translVar, pt, gmul, mul_comm]

omit [CharZero K] in
theorem eval_transl (g h : GPt K d0 d1) (P : MvPolynomial (V3 d0 d1) K) :
    eval (pt h) (transl g P) = eval (pt (gmul g h)) P := by
  rw [transl, mv_eval_aeval]
  apply congrArg (fun f => eval f P)
  funext v
  exact eval_translVar g h v

omit [CharZero K] in
theorem gmul_assoc (a b c : GPt K d0 d1) : gmul (gmul a b) c = gmul a (gmul b c) := by
  simp [gmul, add_assoc, mul_assoc]

omit [CharZero K] in
theorem gmul_ginv (g : GPt K d0 d1) : gmul (ginv g) g = GPt.zero := by
  simp [gmul, ginv, GPt.zero]

omit [CharZero K] in
theorem gmul_ginv' (g : GPt K d0 d1) : gmul g (ginv g) = GPt.zero := by
  simp [gmul, ginv, GPt.zero]

omit [CharZero K] in
theorem gzero_gmul (g : GPt K d0 d1) : gmul GPt.zero g = g := by
  simp [gmul, GPt.zero]

theorem transl_comp (g g' : GPt K d0 d1) (P : MvPolynomial (V3 d0 d1) K) :
    transl g (transl g' P) = transl (gmul g' g) P := by
  apply MvPolynomial.funext
  intro u
  -- reduce to evaluation at arbitrary points: use the variable images
  rw [transl, transl, transl, mv_eval_aeval, mv_eval_aeval, mv_eval_aeval]
  apply congrArg (fun f => eval f P)
  funext v
  rcases v with k | j | j
  · simp [translVar, gmul]; ring
  · simp [translVar, gmul]; ring
  · simp [translVar, gmul]; ring

omit [CharZero K] in
theorem transl_zero (P : MvPolynomial (V3 d0 d1) K) : transl GPt.zero P = P := by
  have : transl (K := K) (d0 := d0) (d1 := d1) GPt.zero = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    rcases v with k | j | j <;> simp [transl, translVar, GPt.zero]
  rw [this]; rfl

theorem transl_comp_inv (g : GPt K d0 d1) (P : MvPolynomial (V3 d0 d1) K) :
    transl (ginv g) (transl g P) = P := by
  rw [transl_comp, gmul_ginv', transl_zero]

theorem transl_inv_comp (g : GPt K d0 d1) (P : MvPolynomial (V3 d0 d1) K) :
    transl g (transl (ginv g) P) = P := by
  rw [transl_comp, gmul_ginv, transl_zero]

/-! ### Block degrees -/

variable (D : Fin 2 → ℕ)

omit [CharZero K] in
theorem translVar_mem (g : GPt K d0 d1) (v : V3 d0 d1) :
    translVar g v ∈ FLE K blk (Pi.single (blk v) 1) := by
  classical
  rw [FLE, mem_restrictSupport_iff]
  intro m hm i
  rcases v with k | j | j
  · simp only [translVar, Sum.elim_inl] at hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · rw [support_X, Finset.mem_singleton] at h
      subst h
      simp only [bdeg_single, blk, Sum.elim_inl, Pi.single_apply]
      split_ifs <;> simp_all
    · rw [support_C] at h
      split_ifs at h <;> simp_all
  · simp only [translVar, Sum.elim_inr, Sum.elim_inl] at hm
    rw [C_mul_X_eq_monomial] at hm
    have := support_monomial_subset hm
    simp only [Finset.mem_singleton] at this
    subst this
    simp only [bdeg_single, blk, Sum.elim_inr, Pi.single_apply]
    split_ifs <;> simp_all
  · simp only [translVar, Sum.elim_inr] at hm
    rw [C_mul_X_eq_monomial] at hm
    have := support_monomial_subset hm
    simp only [Finset.mem_singleton] at this
    subst this
    simp only [bdeg_single, blk, Sum.elim_inr, Pi.single_apply]
    split_ifs <;> simp_all

omit [CharZero K] in
theorem one_mem_FLE (E : Fin 2 → ℕ) : (1 : MvPolynomial (V3 d0 d1) K) ∈ FLE K blk E := by
  rw [show (1 : MvPolynomial (V3 d0 d1) K) = monomial 0 1 from rfl, FLE,
    monomial_mem_restrictSupport]
  exact Or.inl fun i => by simp

omit [CharZero K] in
theorem pow_mem_FLE {f : MvPolynomial (V3 d0 d1) K} {e : Fin 2 → ℕ} (hf : f ∈ FLE K blk e) (n : ℕ) :
    f ^ n ∈ FLE K blk (n • e) := by
  induction n with
  | zero => simpa using one_mem_FLE (K := K) (d0 := d0) (d1 := d1) 0
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_FLE K ih hf

omit [CharZero K] in
theorem prod_mem_FLE {ι' : Type*} (s : Finset ι') (f : ι' → MvPolynomial (V3 d0 d1) K)
    (e : ι' → Fin 2 → ℕ) (h : ∀ i ∈ s, f i ∈ FLE K blk (e i)) :
    ∏ i ∈ s, f i ∈ FLE K blk (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_FLE (K := K) (d0 := d0) (d1 := d1) 0
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact mul_mem_FLE K (h x (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [CharZero K] in
/-- Translation preserves block degrees. -/
theorem transl_mem_FLE (g : GPt K d0 d1) {P : MvPolynomial (V3 d0 d1) K}
    (hP : P ∈ FLE K blk D) : transl g P ∈ FLE K blk D := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmS : m ∈ S blk D := by
    rw [FLE, mem_restrictSupport_iff] at hP; exact hP hm
  rw [transl, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_eq]
  have hprod := prod_mem_FLE Finset.univ (fun v => translVar g v ^ m v)
    (fun v => m v • Pi.single (blk v) 1) fun v _ => pow_mem_FLE (translVar_mem g v) (m v)
  have hle : (∑ v, m v • (Pi.single (blk v) 1 : Fin 2 → ℕ)) ≤ D := by
    intro i
    have := hmS i
    simp only [bdeg] at this
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    convert this using 2 with v
    simp [eq_comm]
  have := FLE_mono K blk hle hprod
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ this

theorem transl_injective (g : GPt K d0 d1) : Function.Injective (transl g) := fun P Q h => by
  rw [← transl_comp_inv g P, h, transl_comp_inv]

/-- The image of `E` under translation by `g`. -/
def gtransl (g : GPt K d0 d1) (E : Set (GPt K d0 d1)) : Set (GPt K d0 d1) := gmul g '' E

omit [CharZero K] in
theorem transl_mem_vanish {g : GPt K d0 d1} {E : Set (GPt K d0 d1)} {P : MvPolynomial (V3 d0 d1)
  K} :
    transl g P ∈ vanish E ↔ P ∈ vanish (gtransl g E) := by
  constructor
  · rintro h _ ⟨e, he, rfl⟩
    rw [← eval_transl]; exact h e he
  · intro h e he
    rw [eval_transl]; exact h _ ⟨e, he, rfl⟩

/-- **Translation invariance of Hilbert functions.** -/
theorem hfun_vanish_transl (g : GPt K d0 d1) (E : Set (GPt K d0 d1)) (t : ℕ) :
    hfun blk D K (vanish (gtransl g E)) t = hfun blk D K (vanish E) t := by
  unfold hfun
  set F := FLE K blk (t • D)
  congr 1
  let φ : MvPolynomial (V3 d0 d1) K →ₗ[K] MvPolynomial (V3 d0 d1) K := (transl g).toLinearMap
  have hmap : ((vanish (gtransl g E)).restrictScalars K ⊓ F).map φ = (vanish E).restrictScalars
    K ⊓ F := by
    apply le_antisymm
    · rintro _ ⟨P, ⟨hP1, hP2⟩, rfl⟩
      exact ⟨transl_mem_vanish.mpr hP1, transl_mem_FLE _ g hP2⟩
    · rintro Q ⟨hQ1, hQ2⟩
      refine ⟨transl (ginv g) Q, ⟨?_, transl_mem_FLE _ (ginv g) hQ2⟩, transl_inv_comp g Q⟩
      apply transl_mem_vanish.mp
      show transl g (transl (ginv g) Q) ∈ vanish E
      rw [transl_inv_comp]; exact hQ1
  rw [← hmap]
  have : FiniteDimensional K ↥((vanish (gtransl g E)).restrictScalars K ⊓ F) :=
    Submodule.finiteDimensional_of_le inf_le_right
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective φ (transl_injective g)
    ((vanish (gtransl g E)).restrictScalars K ⊓ F))

end StrongSix.M2

end LeanPool
