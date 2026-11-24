/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermCoordinateTower

/-!
# Noether normalization for prime ideals of `𝒪_n`

Source: Demailly, *Complex analytic and differential geometry*, II.4.8 and II.4.13.
Blueprint: `lag:noether-normalization`, `lag:finite-extension`.

Let `P ⊆ 𝒪_n` be a prime ideal.  After a linear change of coordinates (`P` is replaced by
its image `Q` under the induced ring automorphism) there is `d ≤ n` such that

* `Q ∩ 𝒪_d = 0`;
* for each `d ≤ k < n` (`0`-indexed coordinates) `Q` contains a Weierstrass polynomial in
  `z_k` with coefficients in `𝒪_k` (`HasWeierstrassPolynomial`);

(`exists_isNoetherNormalization`).  Consequently every germ is congruent modulo `Q` to an
`𝒪_d`-combination of finitely many fixed germs (`exists_finite_generators`), so
`𝒪_d → 𝒪_n / Q` is injective, finite and integral (`exists_noetherNormalization`).

## Proof

Induction on `n`.  If `P = 0` take `d = n`; for `n = 0` this is the only prime.  Otherwise
move to `ℂⁿ × ℂ` by `euclideanSnocCLE`, pick `g ≠ 0` in `P`, and apply the germ form of
Weierstrass preparation after a linear change `A` of `ℂⁿ × ℂ`: a unit multiple of `g ∘ A`
is a Weierstrass polynomial `W` in the last variable, and `W` lies in the transformed prime
`P₂`.  The prime `P₂ ∩ 𝒪_n` has a normalization `(d, L')` by induction; the change of
coordinates `L' × id` preserves `𝒪_n` and maps `W` to a Weierstrass polynomial.

Finiteness: induction on `n ≥ d`, dividing by the Weierstrass polynomial in the last
coordinate and then the remainder coefficients by induction.
-/

@[expose] public section

open Filter Topology

namespace SGPT.Foundations.Analysis.Pending

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open HolGerm

noncomputable section

/-- `Q` contains a Weierstrass polynomial `z_k ^ s + ∑_{j<s} A_j z_k ^ j` in the coordinate
`z_k` with coefficients `A_j ∈ 𝒪_k` vanishing at `0`. -/
def HasWeierstrassPolynomial {n : ℕ} (Q : Ideal (HolGerm (ComplexModel n))) (k : ℕ)
    (hk : k < n) : Prop :=
  ∃ (s : ℕ) (A : ℕ → HolGerm (ComplexModel k)),
    (∀ j < s, eval (A j) = 0) ∧ weierstrassGerm n k hk s A ∈ Q

/-- `Q ⊆ 𝒪_n` is in Noether normal position with respect to `𝒪_d`: `Q ∩ 𝒪_d = 0` and `Q`
contains a Weierstrass polynomial in each coordinate `z_k`, `d ≤ k < n`, over `𝒪_k`. -/
structure IsNoetherNormalization {n : ℕ} (Q : Ideal (HolGerm (ComplexModel n))) (d : ℕ) :
    Prop where
  le : d ≤ n
  eq_zero_of_mem : ∀ c : HolGerm (ComplexModel d), projGerm n d c ∈ Q → c = 0
  weierstrass : ∀ k (hk : k < n), d ≤ k → HasWeierstrassPolynomial Q k hk

theorem isNoetherNormalization_bot (n : ℕ) :
    IsNoetherNormalization (⊥ : Ideal (HolGerm (ComplexModel n))) n where
  le := le_rfl
  eq_zero_of_mem c hc := by
    rw [Ideal.mem_bot, projGerm_self] at hc
    exact hc
  weierstrass k hk hnk := absurd hk (not_lt.mpr hnk)

/-- The only prime ideal of `𝒪_0 = ℂ` is `0`. -/
theorem eq_bot_of_isPrime_zero (P : Ideal (HolGerm (ComplexModel 0))) [hP : P.IsPrime] :
    P = ⊥ := by
  by_contra hne
  obtain ⟨g, hgP, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply hP.ne_top
  refine Ideal.eq_top_of_isUnit_mem P hgP ((isUnit_iff_eval_ne_zero g).2 fun hev => hg0 ?_)
  obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
  rw [eval_mk] at hev
  rw [← mk_zero, mk_eq_mk_iff]
  exact Eventually.of_forall fun z => by simp [Subsingleton.elim z 0, hev]

theorem mem_map_ringEquiv_apply_iff {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal R) (x : R) : e x ∈ I.map e ↔ x ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/-- **Induction step of Noether normalization** for a nonzero prime of `𝒪_{n+1}`. -/
theorem exists_isNoetherNormalization_succ {n : ℕ}
    (ih : ∀ P : Ideal (HolGerm (ComplexModel n)), P.IsPrime →
      ∃ (d : ℕ) (L : ComplexModel n ≃L[ℂ] ComplexModel n),
        IsNoetherNormalization (P.map (comapEquiv L)) d)
    (P : Ideal (HolGerm (ComplexModel (n + 1)))) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ (d : ℕ) (L : ComplexModel (n + 1) ≃L[ℂ] ComplexModel (n + 1)),
      IsNoetherNormalization (P.map (comapEquiv L)) d := by
  set σ := euclideanSnocCLE n
  set P₁ := P.map (comapEquiv σ.symm)
  have hP₁ : P₁ ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (comapEquiv σ.symm).injective]
    exact hP
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP₁
  obtain ⟨A, q, s, B, -, hB, hW⟩ := exists_mul_comapEquiv_eq_prodWeierstrassGerm hg0
  set P₂ := P₁.map (comapEquiv A)
  have hW₂ : prodWeierstrassGerm s B ∈ P₂ :=
    hW ▸ P₂.mul_mem_left q (Ideal.mem_map_of_mem _ hg)
  have : P₁.IsPrime := Ideal.map_isPrime_of_equiv _
  have : P₂.IsPrime := Ideal.map_isPrime_of_equiv _
  obtain ⟨d, L', hN⟩ := ih (P₂.comap ofFst) inferInstance
  set M := L'.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  set P₃ := P₂.map (comapEquiv M)
  have hP₃ : P₃.comap ofFst = (P₂.comap ofFst).map (comapEquiv L') :=
    comap_ofFst_map_comapEquiv_prodCongr L' P₂
  refine ⟨d, σ.trans (M.trans (A.trans σ.symm)), ?_⟩
  have hQ : P.map (comapEquiv (σ.trans (M.trans (A.trans σ.symm)))) =
      P₃.map (comapEquiv σ) := by
    rw [map_comapEquiv_trans, map_comapEquiv_trans, map_comapEquiv_trans]
  rw [hQ]
  have key : ∀ x, projGerm (n + 1) n x ∈ P₃.map (comapEquiv σ) ↔
      x ∈ (P₂.comap ofFst).map (comapEquiv L') := by
    intro x
    rw [← hP₃, Ideal.mem_comap, ← comapEquiv_euclideanSnocCLE_ofFst]
    exact mem_map_ringEquiv_apply_iff _ _ _
  refine ⟨hN.le.trans n.le_succ, fun c hc => ?_, fun k hk hdk => ?_⟩
  · rw [← projGerm_projGerm hN.le, key] at hc
    exact hN.eq_zero_of_mem c hc
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | rfl
    · obtain ⟨s', A', hA', hw⟩ := hN.weierstrass k hkn hdk
      refine ⟨s', A', hA', ?_⟩
      have := (key _).2 hw
      rwa [projGerm_weierstrassGerm hkn n.le_succ] at this
    · refine ⟨s, fun j => comapEquiv L' (B j), fun j hj => by simp [hB j hj], ?_⟩
      rw [← comapEquiv_euclideanSnocCLE_prodWeierstrassGerm,
        ← comapEquiv_prodCongr_prodWeierstrassGerm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hW₂)

/-- **Noether normalization for prime ideals of `𝒪_n`** (Demailly II.4.8).  After a linear
change of coordinates `L`, the transformed prime is in Noether normal position with respect
to `𝒪_d` for some `d ≤ n`. -/
theorem exists_isNoetherNormalization {n : ℕ} (P : Ideal (HolGerm (ComplexModel n)))
    [P.IsPrime] :
    ∃ (d : ℕ) (L : ComplexModel n ≃L[ℂ] ComplexModel n),
      IsNoetherNormalization (P.map (comapEquiv L)) d := by
  induction n with
  | zero =>
    refine ⟨0, ContinuousLinearEquiv.refl ℂ _, ?_⟩
    rw [map_comapEquiv_refl, eq_bot_of_isPrime_zero P]
    exact isNoetherNormalization_bot 0
  | succ n ih =>
    by_cases hP : P = ⊥
    · refine ⟨n + 1, ContinuousLinearEquiv.refl ℂ _, ?_⟩
      rw [map_comapEquiv_refl, hP]
      exact isNoetherNormalization_bot (n + 1)
    · exact exists_isNoetherNormalization_succ (fun P hP => @ih P hP) P hP

/-! ### Finiteness over `𝒪_d` -/

/-- **Iterated Weierstrass division** (Demailly II.4.13).  If `Q ⊆ 𝒪_n` contains Weierstrass
polynomials in `z_k` over `𝒪_k` for `d ≤ k < n`, then every germ is congruent modulo `Q`
to an `𝒪_d`-combination of finitely many fixed germs (the monomials
`z_d^{α_d} ⋯ z_{n-1}^{α_{n-1}}`, `α_k < s_k`). -/
theorem exists_finite_generators {d n : ℕ} (hdn : d ≤ n) (Q : Ideal (HolGerm (ComplexModel n)))
    (hQ : ∀ k (hk : k < n), d ≤ k → HasWeierstrassPolynomial Q k hk) :
    ∃ (N : ℕ) (m : Fin N → HolGerm (ComplexModel n)), ∀ f : HolGerm (ComplexModel n),
      ∃ c : Fin N → HolGerm (ComplexModel d), f - ∑ i, projGerm n d (c i) * m i ∈ Q := by
  induction n, hdn using Nat.le_induction with
  | base =>
    refine ⟨1, fun _ => 1, fun f => ⟨fun _ => f, ?_⟩⟩
    simp [projGerm_self]
  | succ n hdn ih =>
    obtain ⟨s, A, hA, hW⟩ := hQ n n.lt_succ_self hdn
    obtain ⟨N, m, hm⟩ := ih (Q.comap (projGerm (n + 1) n)) fun k hk hdk => by
      obtain ⟨s', A', hA', hw⟩ := hQ k (hk.trans n.lt_succ_self) hdk
      exact ⟨s', A', hA', by rwa [Ideal.mem_comap, projGerm_weierstrassGerm hk n.le_succ]⟩
    set z := coordGerm (n + 1) n n.lt_succ_self
    refine ⟨s * N, fun i => projGerm (n + 1) n (m (finProdFinEquiv.symm i).2) *
      z ^ ((finProdFinEquiv.symm i).1 : ℕ), fun f => ?_⟩
    obtain ⟨q, r, hf⟩ := exists_eq_mul_weierstrassGerm_add hA f
    choose c hc using fun j => hm (r j)
    refine ⟨fun i => c (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2, ?_⟩
    have hsum : ∑ i : Fin (s * N), projGerm (n + 1) d
          (c (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) *
          (projGerm (n + 1) n (m (finProdFinEquiv.symm i).2) *
            z ^ ((finProdFinEquiv.symm i).1 : ℕ)) =
        ∑ j ∈ Finset.range s, projGerm (n + 1) n (∑ l, projGerm n d (c j l) * m l) * z ^ j := by
      rw [finProdFinEquiv.symm.sum_comp
        (fun p : Fin s × Fin N => projGerm (n + 1) d (c p.1 p.2) *
          (projGerm (n + 1) n (m p.2) * z ^ (p.1 : ℕ))),
        Fintype.sum_prod_type,
        ← Fin.sum_univ_eq_sum_range (fun j => projGerm (n + 1) n (∑ l, projGerm n d (c j l) * m l)
          *
          z ^ j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_sum, map_mul, projGerm_projGerm hdn, Finset.sum_mul, mul_assoc]
    rw [hsum]
    have heq : f - ∑ j ∈ Finset.range s,
          projGerm (n + 1) n (∑ l, projGerm n d (c j l) * m l) * z ^ j =
        q * weierstrassGerm (n + 1) n n.lt_succ_self s A +
          ∑ j ∈ Finset.range s,
            projGerm (n + 1) n (r j - ∑ l, projGerm n d (c j l) * m l) * z ^ j := by
      rw [hf]
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [heq]
    exact Q.add_mem (Q.mul_mem_left _ hW)
      (Q.sum_mem fun j _ => Q.mul_mem_right _ (hc j))

/-- The structure map `𝒪_d → 𝒪_n / Q`. -/
def quotientStructureMap {n : ℕ} (Q : Ideal (HolGerm (ComplexModel n))) (d : ℕ) :
    HolGerm (ComplexModel d) →+* HolGerm (ComplexModel n) ⧸ Q :=
  (Ideal.Quotient.mk Q).comp (projGerm n d)

/-- Finitely many germs generating modulo `Q` make `𝒪_n / Q` a finite `𝒪_d`-module. -/
theorem quotientStructureMap_finite_of_generators {d n N : ℕ}
    {Q : Ideal (HolGerm (ComplexModel n))} {m : Fin N → HolGerm (ComplexModel n)}
    (hm : ∀ f : HolGerm (ComplexModel n), ∃ c : Fin N → HolGerm (ComplexModel d),
      f - ∑ i, projGerm n d (c i) * m i ∈ Q) :
    (quotientStructureMap Q d).Finite := by
  classical
  let _ := (quotientStructureMap Q d).toAlgebra
  change Module.Finite (HolGerm (ComplexModel d)) (HolGerm (ComplexModel n) ⧸ Q)
  refine ⟨⟨Finset.univ.image fun i => Ideal.Quotient.mk Q (m i), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, hc⟩ := hm f
  have hx : Ideal.Quotient.mk Q f = ∑ i, c i • Ideal.Quotient.mk Q (m i) := by
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, quotientStructureMap,
      RingHom.comp_apply, ← map_mul, ← map_sum]
    exact Ideal.Quotient.eq.2 hc
  rw [hx]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

namespace IsNoetherNormalization

variable {n d : ℕ} {Q : Ideal (HolGerm (ComplexModel n))}

/-- `𝒪_d → 𝒪_n / Q` is injective. -/
theorem injective (h : IsNoetherNormalization Q d) :
    Function.Injective (quotientStructureMap Q d) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  exact h.eq_zero_of_mem c (Ideal.Quotient.eq_zero_iff_mem.1 hc)

theorem exists_finite_generators (h : IsNoetherNormalization Q d) :
    ∃ (N : ℕ) (m : Fin N → HolGerm (ComplexModel n)), ∀ f : HolGerm (ComplexModel n),
      ∃ c : Fin N → HolGerm (ComplexModel d), f - ∑ i, projGerm n d (c i) * m i ∈ Q :=
  Pending.exists_finite_generators h.le Q h.weierstrass

/-- `𝒪_n / Q` is a finite `𝒪_d`-module. -/
theorem finite (h : IsNoetherNormalization Q d) : (quotientStructureMap Q d).Finite := by
  obtain ⟨N, m, hm⟩ := h.exists_finite_generators
  exact quotientStructureMap_finite_of_generators hm

/-- Every element of `𝒪_n / Q` is integral over `𝒪_d`. -/
theorem isIntegral (h : IsNoetherNormalization Q d) : (quotientStructureMap Q d).IsIntegral :=
  h.finite.to_isIntegral

end IsNoetherNormalization

/-- `HasWeierstrassPolynomial` in terms of explicit holomorphic coefficient functions. -/
theorem hasWeierstrassPolynomial_iff {n : ℕ} (Q : Ideal (HolGerm (ComplexModel n))) (k : ℕ)
    (hk : k < n) :
    HasWeierstrassPolynomial Q k hk ↔
      ∃ (s : ℕ) (a : ℕ → ComplexModel k → ℂ)
        (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z),
        (∀ j < s, a j 0 = 0) ∧
          mk (fun z : ComplexModel n => z ⟨k, hk⟩ ^ s +
              ∑ j ∈ Finset.range s, a j (coordinateProjection n k z) * z ⟨k, hk⟩ ^ j)
            (eventually_differentiableAt_coordWeierstrass n k hk s a ha) ∈ Q := by
  constructor
  · rintro ⟨s, A, hA, hW⟩
    choose a ha hAa using fun j => exists_eq_mk (A j)
    obtain rfl : A = fun j => mk (a j) (ha j) := funext hAa
    exact ⟨s, a, ha, hA, weierstrassGerm_eq_mk n k hk s a ha ▸ hW⟩
  · rintro ⟨s, a, ha, ha0, hW⟩
    exact ⟨s, fun j => mk (a j) (ha j), ha0, (weierstrassGerm_eq_mk n k hk s a ha).symm ▸ hW⟩

/-- **Noether normalization and finiteness for prime ideals of `𝒪_n`** (Demailly II.4.8,
II.4.13).  For a prime `P ⊆ 𝒪_n` there are `d ≤ n` and a linear change of coordinates `L`
such that, for the transformed prime `Q = L^* P`:
* `Q ∩ 𝒪_d = 0`;
* for `d ≤ k < n`, `Q` contains a Weierstrass polynomial
  `z_k ^ s + ∑_{j<s} a_j(z_0, …, z_{k-1}) z_k ^ j`, `a_j(0) = 0`;
* finitely many germs generate `𝒪_n` modulo `Q` over `𝒪_d`;
* `𝒪_d → 𝒪_n / Q` is injective, finite and integral. -/
theorem exists_noetherNormalization {n : ℕ} (P : Ideal (HolGerm (ComplexModel n)))
    [P.IsPrime] :
    ∃ (d : ℕ) (_ : d ≤ n) (L : ComplexModel n ≃L[ℂ] ComplexModel n),
      (∀ c : HolGerm (ComplexModel d),
        HolGerm.comap (coordinateProjection n d) c ∈ P.map (comapEquiv L) → c = 0) ∧
      (∀ k (hk : k < n), d ≤ k →
        ∃ (s : ℕ) (a : ℕ → ComplexModel k → ℂ)
          (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z),
          (∀ j < s, a j 0 = 0) ∧
            mk (fun z : ComplexModel n => z ⟨k, hk⟩ ^ s +
                ∑ j ∈ Finset.range s, a j (coordinateProjection n k z) * z ⟨k, hk⟩ ^ j)
              (eventually_differentiableAt_coordWeierstrass n k hk s a ha) ∈
              P.map (comapEquiv L)) ∧
      (∃ (N : ℕ) (m : Fin N → HolGerm (ComplexModel n)), ∀ f : HolGerm (ComplexModel n),
        ∃ c : Fin N → HolGerm (ComplexModel d),
          f - ∑ i, HolGerm.comap (coordinateProjection n d) (c i) * m i ∈ P.map (comapEquiv L)) ∧
      Function.Injective (quotientStructureMap (P.map (comapEquiv L)) d) ∧
      (quotientStructureMap (P.map (comapEquiv L)) d).Finite ∧
      (quotientStructureMap (P.map (comapEquiv L)) d).IsIntegral := by
  obtain ⟨d, L, h⟩ := exists_isNoetherNormalization P
  exact ⟨d, h.le, L, h.eq_zero_of_mem,
    fun k hk hdk => (hasWeierstrassPolynomial_iff _ k hk).1 (h.weierstrass k hk hdk),
    h.exists_finite_generators, h.injective, h.finite, h.isIntegral⟩

end

end SGPT.Foundations.Analysis.Pending
