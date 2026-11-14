/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Filtered

/-!
# The Veronese bridge: filtered Hilbert functions are eventually polynomial

For an ideal `J` of `K[σ]`, and a block-degree bound `D`, set

  `hfun J t = dim FLE(tD) − dim (J ∩ FLE(tD))`,

which is Roy's `H(J; tD)`. The monomials `μ₁, …, μ_N` of block degree `≤ D` define
`vmap : K[z₁, …, z_N] → K[σ]`, `z_k ↦ μ_k`. It maps the degree-`t` part onto `FLE(tD)`, by the
splitting lemma `S_succ`. The graded ideal

  `Jsharp J = {p | vmap (homogeneous component t of p) ∈ J for all t}`

then satisfies `hilb (Jsharp J) t = hfun J t` (`hilb_Jsharp`). So `hfun J` is eventually
polynomial by
Hilbert–Serre (`hfun_evPoly`), and the dimension/degree theory of `HData.lean` applies to it.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]

section Mon

variable (β : σ → ι) (D : ι → ℕ)

/-- The number of monomials of block degree `≤ D`. -/
noncomputable def vN : ℕ := (S_finite β D).toFinset.card

/-- The `k`-th monomial of block degree `≤ D`. -/
noncomputable def vmon (k : Fin (vN β D)) : σ →₀ ℕ := ((S_finite β D).toFinset.equivFin.symm k).1

omit [DecidableEq σ] in
theorem vmon_mem (k : Fin (vN β D)) : vmon β D k ∈ S β D :=
  (Set.Finite.mem_toFinset _).mp ((S_finite β D).toFinset.equivFin.symm k).2

omit [DecidableEq σ] in
theorem exists_vmon {m : σ →₀ ℕ} (hm : m ∈ S β D) : ∃ k, vmon β D k = m :=
  ⟨(S_finite β D).toFinset.equivFin ⟨m, by simpa using hm⟩, by simp [vmon]⟩

/-- The exponent of `vmap (z^a)`. -/
noncomputable def vexp (a : Fin (vN β D) →₀ ℕ) : σ →₀ ℕ := a.sum fun k e => e • vmon β D k

omit [DecidableEq σ] in
theorem vexp_add (a b : Fin (vN β D) →₀ ℕ) : vexp β D (a + b) = vexp β D a + vexp β D b :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

omit [DecidableEq σ] in
@[simp] theorem vexp_zero : vexp β D 0 = 0 := by simp [vexp]

omit [DecidableEq σ] in
theorem vexp_single (k : Fin (vN β D)) : vexp β D (Finsupp.single k 1) = vmon β D k := by
  simp [vexp]

end Mon

omit [Fintype ι] in
omit [DecidableEq σ] in
theorem bdeg_sum {α : Type*} (β : σ → ι) (s : Finset α) (f : α → σ →₀ ℕ) (i : ι) :
    bdeg β (∑ x ∈ s, f x) i = ∑ x ∈ s, bdeg β (f x) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, bdeg_add, ih]

omit [Fintype ι] in
omit [DecidableEq σ] in
theorem bdeg_nsmul (β : σ → ι) (n : ℕ) (m : σ →₀ ℕ) (i : ι) : bdeg β (n • m) i = n * bdeg β m i
  := by
  classical
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, bdeg_add, ih]; ring

omit [Fintype ι] in
omit [DecidableEq σ] in
theorem eq_zero_of_mem_S_zero {β : σ → ι} {m : σ →₀ ℕ} (hm : m ∈ S β 0) : m = 0 := by
  classical
  ext s
  have := (le_bdeg β m s).trans (hm (β s))
  simp only [Pi.zero_apply] at this
  simpa using this

section Bridge

variable (β : σ → ι) (D : ι → ℕ)

omit [DecidableEq σ] in
theorem vexp_mem {a : Fin (vN β D) →₀ ℕ} {t : ℕ} (ha : a.degree = t) : vexp β D a ∈ S β (t • D)
  := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  intro i
  simp only [vexp, Finsupp.sum, bdeg_sum, bdeg_nsmul, Pi.smul_apply, smul_eq_mul]
  calc ∑ k ∈ a.support, a k * bdeg β (vmon β D k) i ≤ ∑ k ∈ a.support, a k * D i :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (vmon_mem β D k i)
    _ = t * D i := by rw [← Finset.sum_mul, ← ha]; rfl

omit [DecidableEq σ] in
theorem exists_vexp (t : ℕ) : ∀ m ∈ S β (t • D), ∃ a : Fin (vN β D) →₀ ℕ, a.degree = t ∧ vexp β
  D a = m := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  induction t with
  | zero =>
    intro m hm
    refine ⟨0, by simp, ?_⟩
    rw [zero_smul] at hm
    rw [eq_zero_of_mem_S_zero hm, vexp_zero]
  | succ t ih =>
    intro m hm
    rw [S_succ] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := hm
    obtain ⟨a1, ha1, rfl⟩ := ih m1 hm1
    obtain ⟨k, rfl⟩ := exists_vmon β D hm2
    exact ⟨a1 + Finsupp.single k 1, by rw [map_add, ha1, Finsupp.degree_single],
      by rw [vexp_add, vexp_single]⟩

variable (K : Type*) [Field K]

/-- `vmap : K[z_1, …, z_N] → K[σ]`, `z_k ↦ μ_k`. -/
noncomputable def vmap : MvPolynomial (Fin (vN β D)) K →ₐ[K] MvPolynomial σ K :=
  aeval fun k => monomial (vmon β D k) 1

omit [DecidableEq σ] in
theorem vmap_monomial (a : Fin (vN β D) →₀ ℕ) (c : K) :
    vmap β D K (monomial a c) = monomial (vexp β D a) c := by
  rw [vmap, aeval_monomial, Finsupp.prod]
  simp only [monomial_pow, one_pow]
  rw [← monomial_sum_one, algebraMap_eq, C_mul_monomial, mul_one]
  rfl

omit [DecidableEq σ] in
theorem vmap_mem_FLE {t : ℕ} {p : MvPolynomial (Fin (vN β D)) K} (hp : p ∈ Adeg K (vN β D) t) :
    vmap β D K p ∈ FLE K β (t • D) := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  rw [vmap_monomial, monomial_mem_restrictSupport]
  left
  apply vexp_mem
  have := hp (mem_support_iff.mp ha)
  rw [Finsupp.degree_eq_weight_one]
  exact this

omit [DecidableEq σ] in
theorem FLE_le_map {t : ℕ} :
    FLE K β (t • D) ≤ (Adeg K (vN β D) t).map (vmap β D K).toLinearMap := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  rw [FLE, restrictSupport_eq_span, span_le]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨a, ha, rfl⟩ := exists_vexp β D t m hm
  exact ⟨monomial a 1, isHomogeneous_monomial 1 ha, vmap_monomial β D K a 1⟩

/-- The graded ideal attached to `J`. -/
noncomputable def Jsharp (J : Ideal (MvPolynomial σ K)) : Ideal (MvPolynomial (Fin (vN β D)) K)
  where
  carrier := {p | ∀ t, vmap β D K (homogeneousComponent t p) ∈ J}
  add_mem' {a b} ha hb t := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact J.add_mem (ha t) (hb t)
  zero_mem' t := by simp
  smul_mem' c p hp t := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hp ⊢
    rw [c.as_sum, Finset.sum_mul, map_sum, map_sum]
    refine J.sum_mem fun a _ => ?_
    have hf : (monomial a (c.coeff a)).IsHomogeneous a.degree := isHomogeneous_monomial _ rfl
    by_cases ht : a.degree ≤ t
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
      rw [add_comm, homogeneousComponent_mul_hom hf, map_mul]
      exact J.mul_mem_left _ (hp n)
    · rw [homogeneousComponent_mul_hom_lt hf (by omega), map_zero]
      exact J.zero_mem

omit [DecidableEq σ] in
theorem Jsharp_homIdeal (J : Ideal (MvPolynomial σ K)) : HomIdeal (Jsharp β D K J) := by
  intro p hp n t
  rw [homogeneousComponent_of_mem (homogeneousComponent_mem n p)]
  split_ifs
  · exact hp n
  · simp

omit [DecidableEq σ] in
theorem mem_Jsharp_of_mem_Adeg {J : Ideal (MvPolynomial σ K)} {t : ℕ}
    {p : MvPolynomial (Fin (vN β D)) K} (hp : p ∈ Adeg K (vN β D) t) :
    p ∈ Jsharp β D K J ↔ vmap β D K p ∈ J := by
  constructor
  · intro h
    have := h t
    rwa [homogeneousComponent_of_mem hp, ite_eq_left rfl] at this
  · intro h t'
    rw [homogeneousComponent_of_mem hp]
    split_ifs
    · exact h
    · simp

/-- Roy's Hilbert function `H(J; tD)`. -/
noncomputable def hfun (J : Ideal (MvPolynomial σ K)) (t : ℕ) : ℕ :=
  finrank K (FLE K β (t • D)) - finrank K ↥(J.restrictScalars K ⊓ FLE K β (t • D))

theorem finrank_comap_subtype {V : Type*} [AddCommGroup V] [Module K V] (p N : Submodule K V) :
    finrank K (N.comap p.subtype) = finrank K ↥(p ⊓ N) := by
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

omit [DecidableEq σ] in
/-- **The bridge.** -/
theorem hilb_Jsharp (J : Ideal (MvPolynomial σ K)) (t : ℕ) :
    hilb (Jsharp β D K J) t = hfun β D K J t := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  set F := FLE K β (t • D)
  set A := Adeg K (vN β D) t
  let L : A →ₗ[K] F := (vmap β D K).toLinearMap.restrict fun p hp => vmap_mem_FLE β D K hp
  have hL : Function.Surjective L := by
    rintro ⟨y, hy⟩
    obtain ⟨p, hp, rfl⟩ := FLE_le_map β D K hy
    exact ⟨⟨p, hp⟩, rfl⟩
  let N : Submodule K F := (J.restrictScalars K).comap F.subtype
  let f : A →ₗ[K] F ⧸ N := N.mkQ ∘ₗ L
  have hf : Function.Surjective f := (Submodule.mkQ_surjective N).comp hL
  have hker : LinearMap.ker f = ((Jsharp β D K J).restrictScalars K).comap A.subtype := by
    ext ⟨p, hp⟩
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.restrictScalars_mem, N, L]
    exact (mem_Jsharp_of_mem_Adeg β D K hp).symm
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hker, finrank_comap_subtype] at h1
  have h2 := Submodule.finrank_quotient_add_finrank N
  have h3 : finrank K N = finrank K ↥(J.restrictScalars K ⊓ F) := by
    rw [finrank_comap_subtype, inf_comm]
  have e1 : hilb (Jsharp β D K J) t =
      finrank K A - finrank K ↥(A ⊓ (Jsharp β D K J).restrictScalars K) := by
    unfold hilb Jdeg; rw [inf_comm]
  have e2 : hfun β D K J t = finrank K F - finrank K ↥(J.restrictScalars K ⊓ F) := rfl
  have h4 : finrank K ↥(A ⊓ (Jsharp β D K J).restrictScalars K) ≤ finrank K A :=
    Submodule.finrank_mono inf_le_left
  rw [e1, e2]
  omega

omit [DecidableEq σ] [Fintype ι] in
theorem hfun_evPoly [Finite ι] (J : Ideal (MvPolynomial σ K)) : EvPoly fun t => (hfun β D K J t
  : ℤ) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have := hilb_evPoly (Jsharp β D K J) (Jsharp_homIdeal β D K J)
  simpa only [hilb_Jsharp] using this

end Bridge

end StrongSix.M2

end LeanPool
