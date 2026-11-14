/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Artinian.Instances
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Idempotents

import Mathlib.Tactic.LinearCombination

/-!
# General facts about adically complete rings and modules

Algebraic (as opposed to topological) results for `I`-adically complete rings and modules,
gathered here as Mathlib-bound material.

## Main statements

* `IsPrecomplete.exists_limit`: nonarchimedean telescoping — a sequence whose consecutive
  differences lie in `I ^ (k + 1)` has a limit, approximated to order `n` by its `n`-th term.
* `IsHausdorff.eq_zero_of_forall_mem_pow`, `IsHausdorff.exists_mem_pow_and_notMem_pow_succ`:
  Hausdorffness, and the `I`-adic order it gives a nonzero element.
* `isAdicComplete_of_finite`: a finite module over an adically complete Noetherian ring is
  adically complete (via `AdicCompletion.ofTensorProduct`).
* `isAdicComplete_of_le_of_pow_le`, `isAdicComplete_of_pow`: adic completeness depends on the
  ideal only through the cofinality class of its filtration.
* `IsIdempotentElem.isAdicComplete_quotient`: adic completeness passes to the quotient
  `A ⧸ (1 - ε)` by an idempotent, for the image of the ideal.
* `IsAdicComplete.exists_isIdempotentElem_of_sq_sub_mem`: idempotents lift along an adically
  complete ideal, by the Newton iteration `x ↦ 3x² - 2x³`.
* `IsLocalRing.of_isAdicComplete_of_isDomain`: a domain that is `I`-adically complete with
  Artinian quotient is local.
* `Module.Basis.isAdicComplete`: a module with a finite basis over an adically complete ring is
  adically complete.
-/

@[expose] public section

/-! ### Convergence in an adically complete ring -/

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- An ideal `K` of `R`, viewed as a submodule of `R`, absorbs all of `R`: `K • ⊤ = K`. -/
theorem Ideal.smul_top_eq_self (K : Ideal R) : (K • ⊤ : Submodule R R) = K := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- Nonarchimedean telescoping in an `I`-adically precomplete ring: if consecutive iterates
`wₖ` differ by an element of `I^(k+1)`, the sequence converges to a limit `z` with `z - wₙ ∈ Iⁿ`
for every `n`. Generalizes `PSeries.exists_limit_of_sub_mem_pow` (maximal-ideal case). -/
theorem IsPrecomplete.exists_limit [IsPrecomplete I R] (w : ℕ → R)
    (hstep : ∀ k, w (k + 1) - w k ∈ I ^ (k + 1)) :
    ∃ z : R, z - w 0 ∈ I ∧ ∀ n, z - w n ∈ I ^ n := by
  have hle : ∀ m n, m ≤ n → w n - w m ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : w (n + 1) - w n ∈ I ^ m := Ideal.pow_le_pow_right (by lia) (hstep n)
      have : w (n + 1) - w m = (w (n + 1) - w n) + (w n - w m) := by ring
      rw [this]; exact add_mem h1 ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹_› (f := w) fun {m n} hmn ↦ by
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self]
    exact (Ideal.neg_mem_iff _).mp (by simpa using hle m n hmn)
  have hLn : ∀ n, L - w n ∈ I ^ n := fun n ↦ by
    have := hL n
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at this
    exact (Ideal.neg_mem_iff _).mp (by simpa using this)
  refine ⟨L, ?_, hLn⟩
  have h1 : w 1 - w 0 ∈ I := by simpa using hstep 0
  have : L - w 0 = (L - w 1) + (w 1 - w 0) := by ring
  rw [this]; exact add_mem (by simpa using hLn 1) h1

/-- Hausdorffness: an element in every power of `I` is zero. Generalizes
`PSeries.eq_zero_of_forall_mem_pow` (maximal-ideal case). -/
theorem IsHausdorff.eq_zero_of_forall_mem_pow [IsHausdorff I R] (x : R) (hx : ∀ n, x ∈ I ^ n) :
    x = 0 :=
  IsHausdorff.haus ‹_› x fun n ↦ by
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_top_eq_self]; exact hx n

variable (I) in
/-- In a ring that is Hausdorff for the `I`-adic filtration, a nonzero element has a
well-defined `I`-adic order: it lies in `I ^ n` but not in `I ^ (n + 1)` for exactly one `n`. -/
theorem IsHausdorff.exists_mem_pow_and_notMem_pow_succ [IsHausdorff I R] {x : R} (hx : x ≠ 0) :
    ∃ n, x ∈ I ^ n ∧ x ∉ I ^ (n + 1) := by
  classical
  have hnot : ∃ n, x ∉ I ^ n := by
    by_contra! hall
    exact hx (eq_zero_of_forall_mem_pow x hall)
  have hpos : Nat.find hnot ≠ 0 := fun h0 ↦ Nat.find_spec hnot (by rw [h0]; simp)
  exact ⟨Nat.find hnot - 1, not_not.mp (Nat.find_min hnot (by lia)),
    by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos)]; exact Nat.find_spec hnot⟩

/-! ### A finite module over a complete Noetherian ring is adically complete -/

section FiniteModule

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
  (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over an `I`-adically complete Noetherian ring is itself `I`-adically
complete. (Single-universe, inherited from `AdicCompletion.ofTensorProduct`.) -/
theorem isAdicComplete_of_finite : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  have hR : Function.Bijective (AdicCompletion.of I R) :=
    AdicCompletion.of_bijective_iff.mpr ‹_›
  have hT : Function.Bijective (AdicCompletion.ofTensorProduct I M) :=
    AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M
  have h1 : AdicCompletion.of I R 1 = 1 := by
    have := AdicCompletion.algebraMap_apply (I := I) (S := R) 1
    simpa using this.symm
  set eR : R ≃ₗ[R] AdicCompletion I R := LinearEquiv.ofBijective _ hR with heR
  have hcomp : ⇑(AdicCompletion.of I M)
      = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑(LinearEquiv.rTensor M eR)
        ∘ ⇑(TensorProduct.lid R M).symm := by
    funext x
    simp only [Function.comp_apply, TensorProduct.lid_symm_apply, LinearEquiv.rTensor_tmul,
      AdicCompletion.ofTensorProduct_tmul]
    rw [heR]
    change _ = AdicCompletion.of I R 1 • AdicCompletion.of I M x
    rw [h1, one_smul]
  rw [hcomp]
  exact hT.comp ((eR.rTensor M).bijective.comp (TensorProduct.lid R M).symm.bijective)

end FiniteModule

/-! ### Adic completeness only depends on the ideal up to taking powers -/

/-- Adic completeness of a module transfers between ideals squeezed between powers of each
other: if `I ≤ J` and `J ^ e ≤ I`, the two filtrations are cofinal, so `I`-adic completeness
gives `J`-adic completeness. This is the module-level twin of `IsAdic.of_le_of_pow_le`, which
says the same for the topologies. -/
theorem isAdicComplete_of_le_of_pow_le {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {I J : Ideal A} {e : ℕ} (he : 0 < e) (hIJ : I ≤ J) (hJI : J ^ e ≤ I) [IsAdicComplete I M] :
    IsAdicComplete J M := by
  have hJI' (n : ℕ) : (J ^ (e * n) • ⊤ : Submodule A M) ≤ I ^ n • ⊤ :=
    Submodule.smul_mono_left (by rw [pow_mul]; exact Ideal.pow_right_mono hJI n)
  have hIJ' (n : ℕ) : (I ^ n • ⊤ : Submodule A M) ≤ J ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff J M :=
    ⟨fun x hx ↦ IsHausdorff.haus ‹IsAdicComplete I M›.toIsHausdorff x fun n ↦
      SModEq.mono (hJI' n) (hx (e * n))⟩
  have hP : IsPrecomplete J M := by
    refine ⟨fun {f} hf ↦ ?_⟩
    have hcau : ∀ {m n}, m ≤ n → f (e * m) ≡ f (e * n) [SMOD (I ^ m • ⊤ : Submodule A M)] :=
      fun {m n} hmn ↦ SModEq.mono (hJI' m) (hf (Nat.mul_le_mul_left e hmn))
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsAdicComplete I M›.toIsPrecomplete hcau
    refine ⟨L, fun n ↦ ?_⟩
    have h1 : f n ≡ f (e * n) [SMOD (J ^ n • ⊤ : Submodule A M)] :=
      hf (Nat.le_mul_of_pos_left n he)
    exact h1.trans (SModEq.mono (hIJ' n) (hL n))
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

/-- `J^e`-adic completeness of a module implies `J`-adic completeness (the filtrations are
cofinal). -/
theorem isAdicComplete_of_pow {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {J : Ideal A} {e : ℕ} (he : 0 < e) [IsAdicComplete (J ^ e) M] : IsAdicComplete J M :=
  isAdicComplete_of_le_of_pow_le he (Ideal.pow_le_self he.ne') le_rfl

/-- In `A ⧸ (1 - a)` the element `a` becomes `1`. -/
theorem Ideal.Quotient.mk_span_one_sub {A : Type*} [CommRing A] (a : A) :
    Ideal.Quotient.mk (Ideal.span {1 - a}) a = 1 :=
  (Ideal.Quotient.mk_eq_one_iff_sub_mem a).mpr (Ideal.mem_span_singleton.mpr ⟨-1, by ring⟩)

/-- Multiplication by an idempotent `ε` splits membership in a power of the image of `I` in
`A ⧸ (1 - ε)` back down to `A`: it kills the ambiguity `(1 - ε)A` of a lift. -/
theorem IsIdempotentElem.mul_mem_pow_of_mk_mem_map_pow {A : Type*} [CommRing A] {ε : A}
    (hε : IsIdempotentElem ε) (I : Ideal A) {x : A} {n : ℕ}
    (hx : Ideal.Quotient.mk (Ideal.span {1 - ε}) x ∈
      I.map (Ideal.Quotient.mk (Ideal.span {1 - ε})) ^ n) :
    ε * x ∈ I ^ n := by
  rw [← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker] at hx
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hx
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
  have hεc : ε * ((1 - ε) * d) = 0 := by
    rw [← mul_assoc, mul_sub, mul_one, hε.eq, sub_self, zero_mul]
  rw [show ε * x = ε * a by rw [← hac, mul_add, hεc, add_zero]]
  exact Ideal.mul_mem_left _ _ ha

/-- **Adic completeness passes to the quotient by an idempotent**: for an idempotent `ε`,
the quotient `A ⧸ (1 - ε)` (the corner `εA`) is complete for the image filtration. The
idempotent trivializes both halves: multiplication by `ε` projects any lift into a coherent
one, and kills the ambiguity `(1 - ε)A`. -/
theorem IsIdempotentElem.isAdicComplete_quotient {A : Type*} [CommRing A] {ε : A}
    (hε : IsIdempotentElem ε) (I : Ideal A) [IsAdicComplete I A] :
    IsAdicComplete (I.map (Ideal.Quotient.mk (Ideal.span {1 - ε})))
      (A ⧸ Ideal.span {1 - ε}) := by
  set mk := Ideal.Quotient.mk (Ideal.span {1 - ε})
  have hmkε : mk ε = 1 := Ideal.Quotient.mk_span_one_sub ε
  have hH : IsHausdorff (I.map mk) (A ⧸ Ideal.span {1 - ε}) := by
    refine ⟨fun x hx ↦ ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {1 - ε}) x
    have hεr : ε * r = 0 :=
      IsHausdorff.eq_zero_of_forall_mem_pow (I := I) _ fun n ↦
        hε.mul_mem_pow_of_mk_mem_map_pow I
          (by simpa [SModEq.zero, Ideal.smul_top_eq_self] using hx n)
    rw [show mk r = mk (ε * r) by rw [map_mul, hmkε, one_mul], hεr, map_zero]
  have hP : IsPrecomplete (I.map mk) (A ⧸ Ideal.span {1 - ε}) := by
    refine ⟨fun {f} hf ↦ ?_⟩
    choose r hr using fun n ↦ Ideal.Quotient.mk_surjective (I := Ideal.span {1 - ε}) (f n)
    have hcau : ∀ {m n}, m ≤ n → ε * r m ≡ ε * r n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at h ⊢
      rw [← mul_sub]
      exact hε.mul_mem_pow_of_mk_mem_map_pow I (by rw [map_sub, hr, hr]; exact h)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsAdicComplete I A›.toIsPrecomplete hcau
    refine ⟨mk L, fun n ↦ ?_⟩
    have h2 := hL n
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at h2 ⊢
    rw [show f n = mk (ε * r n) by rw [map_mul, hmkε, one_mul, hr], ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h2
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

/-! ### A complete domain with Artinian quotient is local -/

/-- A commutative Artinian ring with two distinct maximal ideals has a nontrivial idempotent in
its reduction `B ⧸ nilradical B`: under the Artinian decomposition
`B ⧸ nilradical B ≃ ∏ 𝔪, B ⧸ 𝔪`, the indicator of a single factor is such an idempotent. -/
theorem IsArtinianRing.exists_isIdempotentElem_ne_zero_ne_one_of_ne {B : Type*} [CommRing B]
    [IsArtinianRing B] {M₁ M₀ : MaximalSpectrum B} (hMne : M₁ ≠ M₀) :
    ∃ e : B ⧸ nilradical B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  set φ := IsArtinianRing.quotNilradicalEquivPi B
  set v : (J : MaximalSpectrum B) → B ⧸ J.asIdeal := fun J ↦ if J = M₁ then 1 else 0 with hv
  have hvv : v * v = v := by
    funext J
    by_cases h : J = M₁ <;> simp [hv, h]
  have hv1 : v M₁ = 1 := by simp [hv]
  have hv0 : v M₀ = 0 := by simp [hv, hMne.symm]
  have hnt₁ : Nontrivial (B ⧸ M₁.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr M₁.isMaximal.ne_top
  have hnt₀ : Nontrivial (B ⧸ M₀.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr M₀.isMaximal.ne_top
  refine ⟨φ.symm v, by rw [IsIdempotentElem, ← map_mul, hvv], fun h ↦ ?_, fun h ↦ ?_⟩
  · have hv' : v = 0 := by rw [← φ.apply_symm_apply v, h, map_zero]
    exact one_ne_zero (hv1.symm.trans ((congrFun hv' M₁).trans (Pi.zero_apply M₁)))
  · have hv' : v = 1 := by rw [← φ.apply_symm_apply v, h, map_one]
    exact zero_ne_one (hv0.symm.trans ((congrFun hv' M₀).trans (Pi.one_apply M₀)))

/-- **Idempotents lift along an adically complete ideal.** If `a` is idempotent modulo an
`I`-adically complete ideal `I` (`a² - a ∈ I`), the Newton iteration `x ↦ 3x² - 2x³` converges
to an exact idempotent of the ring congruent to `a` modulo `I`. -/
theorem IsAdicComplete.exists_isIdempotentElem_of_sq_sub_mem {A : Type*} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] {a : A} (ha : a ^ 2 - a ∈ I) :
    ∃ e : A, IsIdempotentElem e ∧ e - a ∈ I := by
  set w : ℕ → A := fun n ↦ Nat.rec a (fun _ x ↦ 3 * x ^ 2 - 2 * x ^ 3) n
  have hw0 : w 0 = a := rfl
  have hws : ∀ k, w (k + 1) = 3 * w k ^ 2 - 2 * w k ^ 3 := fun _ ↦ rfl
  have hkey : ∀ k, w k ^ 2 - w k ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [hw0] using ha
    | succ k ih =>
      have hident : w (k + 1) ^ 2 - w (k + 1)
          = (w k ^ 2 - w k) ^ 2 * (-(3 - 2 * w k) * (1 + 2 * w k)) := by
        rw [hws]; ring
      rw [hident]
      have h2 : (w k ^ 2 - w k) ^ 2 ∈ I ^ (k + 1) * I ^ (k + 1) := by
        rw [sq]; exact Ideal.mul_mem_mul ih ih
      rw [← pow_add] at h2
      exact Ideal.pow_le_pow_right (by lia) (Ideal.mul_mem_right _ _ h2)
  have hstep : ∀ k, w (k + 1) - w k ∈ I ^ (k + 1) := by
    intro k
    have hident : w (k + 1) - w k = -(2 * w k - 1) * (w k ^ 2 - w k) := by rw [hws]; ring
    rw [hident]
    exact Ideal.mul_mem_left _ _ (hkey k)
  obtain ⟨z, hz0, hzn⟩ := IsPrecomplete.exists_limit w hstep
  have hzid : z ^ 2 - z = 0 := by
    refine IsHausdorff.eq_zero_of_forall_mem_pow (I := I) _ fun n ↦ ?_
    have hident : z ^ 2 - z = (z - w n) * (z + w n - 1) + (w n ^ 2 - w n) := by ring
    rw [hident]
    exact add_mem (Ideal.mul_mem_right _ _ (hzn n))
      (Ideal.pow_le_pow_right (by lia) (hkey n))
  exact ⟨z, by rw [IsIdempotentElem]; linear_combination hzid, hw0 ▸ hz0⟩

-- Maximal ideals of `A` containing `I` stay maximal, and stay distinct, in `A ⧸ I`.
private theorem exists_ne_maximalSpectrum_quotient {A : Type*} [CommRing A] {I : Ideal A}
    (hIm : ∀ m : Ideal A, m.IsMaximal → I ≤ m) {m₀ m₁ : Ideal A}
    (hm₀ : m₀.IsMaximal) (hm₁ : m₁.IsMaximal) (hne : m₁ ≠ m₀) :
    ∃ M₁ M₀ : MaximalSpectrum (A ⧸ I), M₁ ≠ M₀ := by
  set ρ : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hmax (m : Ideal A) (hm : m.IsMaximal) : (m.map ρ).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIm m hm)
  have hcomap (m : Ideal A) (hm : m.IsMaximal) : (m.map ρ).comap ρ = m := by
    rw [Ideal.comap_map_of_surjective ρ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr (hIm m hm)
  refine ⟨⟨m₁.map ρ, hmax m₁ hm₁⟩, ⟨m₀.map ρ, hmax m₀ hm₀⟩, fun h ↦ hne ?_⟩
  rw [← hcomap m₁ hm₁, ← hcomap m₀ hm₀,
    show m₁.map ρ = m₀.map ρ from congrArg MaximalSpectrum.asIdeal h]

-- A nontrivial idempotent of `A ⧸ I` lifts along an adically complete `I`.
private theorem exists_isIdempotentElem_map_eq {A : Type*} [CommRing A] {I : Ideal A}
    [IsAdicComplete I A] {e₀ : A ⧸ I} (hide₀ : IsIdempotentElem e₀) :
    ∃ z : A, IsIdempotentElem z ∧ Ideal.Quotient.mk I z = e₀ := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I) e₀
  have haI : a ^ 2 - a ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ha, sq, hide₀.eq, sub_self]
  obtain ⟨z, hzid, hza⟩ := IsAdicComplete.exists_isIdempotentElem_of_sq_sub_mem I haI
  refine ⟨z, hzid, ?_⟩
  have h0 : Ideal.Quotient.mk I (z - a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hza
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ha]

/-- A domain that is `I`-adically complete with Artinian quotient `A ⧸ I` is a local ring:
two distinct maximal ideals (necessarily above `I`) would produce a nontrivial idempotent of
`(A ⧸ I) ⧸ nilradical` by the Artinian decomposition into fields, which lifts along the
nilradical and then, via Newton iteration (`e ↦ 3e² - 2e³`) through the adic completeness,
to a nontrivial idempotent of the domain `A`. -/
theorem IsLocalRing.of_isAdicComplete_of_isDomain {A : Type*} [CommRing A] [IsDomain A]
    {I : Ideal A} [IsAdicComplete I A] [IsArtinianRing (A ⧸ I)] :
    IsLocalRing A := by
  have hIm (m : Ideal A) (hm : m.IsMaximal) : I ≤ m :=
    (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨m₀, hm₀, fun m₁ hm₁ ↦ ?_⟩
  by_contra hne
  obtain ⟨M₁, M₀, hMne⟩ := exists_ne_maximalSpectrum_quotient hIm hm₀ hm₁ hne
  obtain ⟨e', hide', he'0, he'1⟩ := IsArtinianRing.exists_isIdempotentElem_ne_zero_ne_one_of_ne hMne
  obtain ⟨e₀, hide₀, he₀⟩ : ∃ e₀ : A ⧸ I, IsIdempotentElem e₀ ∧
      Ideal.Quotient.mk (nilradical (A ⧸ I)) e₀ = e' :=
    exists_isIdempotentElem_eq_of_ker_isNilpotent (f := Ideal.Quotient.mk (nilradical (A ⧸ I)))
      (fun x hx ↦ by rw [Ideal.mk_ker] at hx; exact hx) e'
      (by rw [RingHom.range_eq_top.mpr Ideal.Quotient.mk_surjective]; exact trivial) hide'
  obtain ⟨z, hzid, hmkz⟩ := exists_isIdempotentElem_map_eq hide₀
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hzid with rfl | rfl
  · exact he'0 (by rw [← he₀, ← hmkz, map_zero, map_zero])
  · exact he'1 (by rw [← he₀, ← hmkz, map_one, map_one])

/-! ### Adic completeness of finite free modules

Mathlib-gap lemmas (in their natural root namespaces): membership in `K • ⊤` is coordinatewise
for a finite basis, hence a module with a finite basis over an `I`-adically complete ring is
itself `I`-adically complete. Together with Mathlib's `IsAdicComplete.map_algebraMap_iff` and
its `(X)`-adic completeness of `MvPowerSeries` this makes `AdjoinRoot` of a monic polynomial
over a multivariate power series ring a Henselian ring (used for the disk chart). -/

section AdicBasis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Membership in `K • ⊤` of a free module is coordinatewise membership in `K`. -/
theorem Module.Basis.mem_smul_top_iff {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (K : Ideal R) (x : M) : x ∈ (K • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ K := by
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun hx i ↦ ?_, fun h ↦ ?_⟩
  · refine Submodule.smul_induction_on hx (fun k hk m _ ↦ ?_) (fun y z hy hz ↦ ?_)
    · rw [map_smul]
      exact K.mul_mem_right _ hk
    · rw [map_add, Finsupp.add_apply]
      exact K.add_mem hy hz
  · rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (h i) Submodule.mem_top

/-- A module with a finite basis over an `I`-adically complete ring is `I`-adically
complete. -/
theorem Module.Basis.isAdicComplete {I : Ideal R} {ι : Type*} [Finite ι]
    (b : Module.Basis ι R M) [IsAdicComplete I R] : IsAdicComplete I M where
  haus' x hx := by
    have h (i : ι) : b.repr x i = 0 := by
      refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff : IsHausdorff I R) _ fun n ↦ ?_
      rw [SModEq.zero, Ideal.smul_top_eq_self]
      have hxn := hx n
      rw [SModEq.zero] at hxn
      exact (b.mem_smul_top_iff _ x).mp hxn i
    have hrepr : b.repr x = 0 := Finsupp.ext h
    simpa using congrArg b.repr.symm hrepr
  prec' f hf := by
    let : Fintype ι := Fintype.ofFinite ι
    have hcoord (i : ι) :
        ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
      refine IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete : IsPrecomplete I R)
        fun {m n} hmn ↦ ?_
      have hmem := hf hmn
      rw [SModEq.sub_mem] at hmem ⊢
      rw [Ideal.smul_top_eq_self, ← Finsupp.sub_apply, ← map_sub]
      exact (b.mem_smul_top_iff _ _).mp hmem i
    choose L hL using hcoord
    refine ⟨∑ i, L i • b i, fun n ↦ ?_⟩
    rw [SModEq.sub_mem, b.mem_smul_top_iff]
    intro i
    have hLn := hL i n
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at hLn
    have hrepr : b.repr (∑ j, L j • b j) i = L i := by
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
        mul_one, Finsupp.finsetSum_apply]
      exact (Finset.sum_eq_single (f := fun c ↦ (Finsupp.single c (L c)) i) i
        (fun c _ hc ↦ Finsupp.single_eq_of_ne hc.symm)
        (fun h ↦ absurd (Finset.mem_univ i) h)).trans Finsupp.single_eq_same
    rwa [map_sub, Finsupp.sub_apply, hrepr]

end AdicBasis

end
