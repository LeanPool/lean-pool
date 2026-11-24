/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermMinimalPolynomial
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.Perfect

/-!
# Primitive element with constant coefficients, denominators and separability

Blueprint `lag:primitive-element` (Demailly, *Complex analytic and differential geometry*,
II.4.13, II.4.15).

For a prime `Q ⊆ 𝒪_n` in Noether position over `𝒪_d`, with `K = Frac 𝒪_d` and
`L = Frac(𝒪_n / Q)`: there is a linear form `u = ∑_{k ≥ d} c_k z_k`, `c_k ∈ ℂ`, with
`L = K(uTilde)`; its minimal polynomial `W` is a Weierstrass polynomial; clearing denominators
in `zTilde_k ∈ K[uTilde]` gives `δ ≠ 0` and `B_k`, and separability of `W` gives `δ ∈ (W, W')`.
-/

@[expose] public section

open Filter Topology Polynomial IntermediateField

namespace SGPT.Foundations.Analysis.Pending.GermPrimitiveElement

section Field

variable {F E : Type*} [Field F] [Field E]

/-- Variant of `Field.primitive_element_inf_aux_exists_c` with `c` from an infinite field `k`
embedded in `E`. -/
theorem exists_ne_div_sub {k : Type*} [Field k] [Infinite k] (ϕ : F →+* E) (ψ : k →+* E)
    (hψ : Function.Injective ψ) (α β : E) (f g : F[X]) :
    ∃ c : k, ∀ α' ∈ (f.map ϕ).roots, ∀ β' ∈ (g.map ϕ).roots, -(α' - α) / (β' - β) ≠ ψ c := by
  classical
  let s := ((f.map ϕ).roots.bind fun α' =>
    (g.map ϕ).roots.map fun β' => -(α' - α) / (β' - β)).toFinset
  let s' := s.preimage ψ fun x _ y _ h => hψ h
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset s'
  refine ⟨c, fun α' hα' β' hβ' heq => hc ?_⟩
  have hs : ψ c ∈ s :=
    Multiset.mem_toFinset.mpr (Multiset.mem_bind.mpr
      ⟨α', hα', Multiset.mem_map.mpr ⟨β', hβ', heq⟩⟩)
  exact Finset.mem_preimage.mpr hs

/-- Adaptation of `Field.primitive_element_inf_aux`: the coefficient `c` may be taken from the
image of a prescribed infinite field `k`. -/
theorem exists_mem_adjoin_add_smul [Algebra F E] [Algebra.IsSeparable F E] {k : Type*} [Field k]
    [Infinite k] (ι : k →+* F) (α β : E) :
    ∃ c : k, β ∈ F⟮α + ι c • β⟯ := by
  have hα := Algebra.IsSeparable.isIntegral F α
  have hβ := Algebra.IsSeparable.isIntegral F β
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (SplittingField (g.map ιFE))
  obtain ⟨c₀, hc⟩ := exists_ne_div_sub (ιEE'.comp ιFE) ((ιEE'.comp ιFE).comp ι)
    ((ιEE'.comp ιFE).comp ι).injective (ιEE' α) (ιEE' β) f g
  refine ⟨c₀, ?_⟩
  let c := ι c₀
  let γ := α + c • β
  change β ∈ F⟮γ⟯
  classical
  let p := EuclideanDomain.gcd ((f.map (algebraMap F F⟮γ⟯)).comp
    (C (AdjoinSimple.gen F γ) - (C ↑c : F⟮γ⟯[X]) * X)) (g.map (algebraMap F F⟮γ⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮γ⟯ E) = C h.leadingCoeff * (X - C β) by
    have finale : β = algebraMap F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) := by
      simp [map_div₀, map_neg, ← coeff_map, ← coeff_map, p_linear,
        mul_sub, coeff_C, mul_div_cancel_left₀ β (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable := separable_gcd_right _ (.map (Algebra.IsSeparable.isSeparable F β))
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map_algebraMap, ←
        Algebra.smul_def, add_sub_cancel_right, minpoly.aeval]
    · rw [eval_map_algebraMap, minpoly.aeval]
  have h_splits : Splits (h.map ιEE') := by
    rw [← Polynomial.gcd_map]
    exact (SplittingField.splits _).of_dvd (map_ne_zero map_g_ne_zero)
      (EuclideanDomain.gcd_dvd_right _ _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (ιEE' γ - ιEE' (ιFE c) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hβ), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [γ, c, Algebra.smul_def, map_add, map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only [γ]
    convert! (gcd_map (algebraMap F⟮γ⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_sub,
      map_C, AdjoinSimple.algebraMap_gen, Polynomial.map_mul, map_X]
    congr

/-- Finitely many elements of a separable extension lie in `F⟮∑ c_j x_j⟯` for suitable
coefficients `c_j` from a prescribed infinite subfield. -/
theorem exists_forall_mem_adjoin_sum [Algebra F E] [Algebra.IsSeparable F E] {k : Type*} [Field k]
    [Infinite k] (ι : k →+* F)
    {m : Type*} [Fintype m] (x : m → E) :
    ∃ c : m → k, ∀ i, x i ∈ F⟮∑ j, ι (c j) • x j⟯ := by
  classical
  suffices H : ∀ s : Finset m, ∃ c : m → k, ∀ i ∈ s, x i ∈ F⟮∑ j ∈ s, ι (c j) • x j⟯ by
    obtain ⟨c, hc⟩ := H Finset.univ
    exact ⟨c, fun i => hc i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s has ih =>
    obtain ⟨c, hc⟩ := ih
    set α := ∑ j ∈ s, ι (c j) • x j
    obtain ⟨c₀, hc₀⟩ := exists_mem_adjoin_add_smul ι α (x a)
    refine ⟨Function.update c a c₀, ?_⟩
    have hsum : ∑ j ∈ insert a s, ι (Function.update c a c₀ j) • x j = α + ι c₀ • x a := by
      rw [Finset.sum_insert has, Function.update_self, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj has)]
    rw [hsum]
    have hαmem : α ∈ F⟮α + ι c₀ • x a⟯ := by
      have h := sub_mem (mem_adjoin_simple_self F (α + ι c₀ • x a))
        (F⟮α + ι c₀ • x a⟯.toSubalgebra.smul_mem hc₀ (ι c₀))
      rwa [add_sub_cancel_right] at h
    have hle : F⟮α⟯ ≤ F⟮α + ι c₀ • x a⟯ := adjoin_simple_le_iff.2 hαmem
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hc₀
    · exact hle (hc i hi)

end Field

section Ring

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [IsDomain S]
  [Algebra R S] [FaithfulSMul R S] [Algebra.IsIntegral R S]

omit [IsDomain R] [IsIntegrallyClosed R] [IsDomain S] [Algebra.IsIntegral R S] in
theorem injective_algebraMap_fractionRing :
    Function.Injective (algebraMap R (FractionRing S)) := by
  rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
  exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective R S)

omit [IsIntegrallyClosed R] in
/-- **Primitive element with constant coefficients, cleared denominators.** For finitely many
`x_i` in a domain `S` integral over an integrally closed domain `R ⊇ ℂ`, there are `c_i ∈ ℂ`
such that each `x_i` is, up to a nonzero factor `b ∈ R`, a polynomial over `R` in
`θ = ∑ c_i x_i`. -/
theorem exists_const_mul_eq_aeval (ι : ℂ →+* R) {m : Type*} [Fintype m] (x : m → S) :
    ∃ c : m → ℂ, ∀ i, ∃ b : R, b ≠ 0 ∧ ∃ G : R[X],
      algebraMap R S b * x i = aeval (∑ j, algebraMap R S (ι (c j)) * x j) G := by
  let K := FractionRing R
  let L := FractionRing S
  have : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).2 injective_algebraMap_fractionRing
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  have : CharZero K :=
    (RingHom.charZero_iff ((algebraMap R K).comp ι).injective).1 inferInstance
  have : Algebra.IsAlgebraic R L := (IsFractionRing.isAlgebraic_iff' R S L).1 inferInstance
  have : Algebra.IsAlgebraic K L :=
    ⟨fun y => (IsFractionRing.isAlgebraic_iff R K L).1 (Algebra.IsAlgebraic.isAlgebraic y)⟩
  obtain ⟨c, hc⟩ := exists_forall_mem_adjoin_sum ((algebraMap R K).comp ι)
    (fun i => algebraMap S L (x i))
  refine ⟨c, fun i => ?_⟩
  have hθ : ∑ j, (algebraMap R K).comp ι (c j) • algebraMap S L (x j) =
      algebraMap S L (∑ j, algebraMap R S (ι (c j)) * x j) := by
    simp only [map_sum, map_mul, Algebra.smul_def, RingHom.comp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hmem := hc i
  rw [hθ] at hmem
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _),
    Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨g, hg⟩ := hmem
  change aeval _ g = _ at hg
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) g
  refine ⟨b, nonZeroDivisors.ne_zero hbM,
    IsLocalization.integerNormalization (nonZeroDivisors R) g, IsFractionRing.injective S L ?_⟩
  rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap K, hb, Algebra.smul_def,
    Polynomial.algebraMap_apply, map_mul (aeval _), aeval_C, hg, map_mul, ←
      IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- **Bezout relation for a separable minimal polynomial.** If `W ∈ R[X]` is monic, vanishes at
`θ ∈ S` and divides every polynomial vanishing at `θ`, then `δ ∈ (W, W')` for some `δ ≠ 0`
(characteristic zero). -/
theorem exists_mul_add_mul_derivative_eq_C (ι : ℂ →+* R) {θ : S} {W : R[X]} (hW : W.Monic)
    (hWθ : aeval θ W = 0) (hdvd : ∀ F : R[X], aeval θ F = 0 → W ∣ F) :
    ∃ δ : R, δ ≠ 0 ∧ ∃ a b : R[X], a * W + b * derivative W = C δ := by
  let K := FractionRing R
  let L := FractionRing S
  have : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).2 injective_algebraMap_fractionRing
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  have : CharZero K :=
    (RingHom.charZero_iff ((algebraMap R K).comp ι).injective).1 inferInstance
  have hθ : IsIntegral R θ := Algebra.IsIntegral.isIntegral θ
  have hWeq : W = minpoly R θ :=
    eq_of_monic_of_associated hW (minpoly.monic hθ)
      (associated_of_dvd_dvd (hdvd _ (minpoly.aeval R θ)) (minpoly.isIntegrallyClosed_dvd hθ hWθ))
  have hK : minpoly K (algebraMap S L θ) = W.map (algebraMap R K) := by
    rw [hWeq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions K L hθ
  have hθK : IsIntegral K (algebraMap S L θ) := (hθ.algebraMap (B := L)).tower_top
  have hsep : (W.map (algebraMap R K)).Separable := hK ▸ (minpoly.irreducible hθK).separable
  obtain ⟨a, b, hab⟩ := hsep
  rw [derivative_map] at hab
  obtain ⟨s₁, hs₁M, hs₁⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨s₂, hs₂M, hs₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  refine ⟨s₁ * s₂, mul_ne_zero (nonZeroDivisors.ne_zero hs₁M) (nonZeroDivisors.ne_zero hs₂M),
    C (s₂ : R) * IsLocalization.integerNormalization (nonZeroDivisors R) a,
    C (s₁ : R) * IsLocalization.integerNormalization (nonZeroDivisors R) b, ?_⟩
  apply Polynomial.map_injective _ (IsFractionRing.injective R K)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hs₁, hs₂,
    Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
  linear_combination C (algebraMap R K s₁) * C (algebraMap R K s₂) * hab

end Ring

section Germ

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open HolGerm GermAlgebraicParametrization

variable {n d : ℕ} {Q : Ideal (HolGerm (ComplexModel n))}

/-- **Primitive element, denominators and separability** (Demailly II.4.13, II.4.15).  With
`S = 𝒪_n / Q` finite over `𝒪_d`, choose constants `c_k` with `zTilde_k` a polynomial over
`Frac 𝒪_d` in `uTilde = ∑ c_k zTilde_k`; `W` is the Weierstrass minimal polynomial of `u`, the
denominators give `δ` and `B_k = δ'_k G_k mod W`, and separability of `W` gives the Bezout
relation. -/
theorem exists_primitiveElement [Q.IsPrime] (hQ : IsNoetherNormalization Q d) :
    ∃ (c : Fin n → ℂ) (W : (HolGerm (ComplexModel d))[X]) (δ : HolGerm (ComplexModel d))
      (B : Fin n → (HolGerm (ComplexModel d))[X]),
      IsWeierstrass W ∧ 0 < W.natDegree ∧ evalGerm n W (linearFormGerm n d c) ∈ Q ∧
      (∀ F : (HolGerm (ComplexModel d))[X], evalGerm n F (linearFormGerm n d c) ∈ Q → W ∣ F) ∧
      δ ≠ 0 ∧ (∀ k, (B k).natDegree < W.natDegree) ∧
      (∀ k : Fin n, d ≤ k.1 →
        projGerm n d δ * coord k - evalGerm n (B k) (linearFormGerm n d c) ∈ Q) ∧
      W ∣ (∑ k : Fin n, if d ≤ k.1 then C (constHom (c k)) * B k else 0) - C δ * X ∧
      ∃ a b : (HolGerm (ComplexModel d))[X], a * W + b * derivative W = C δ := by
  classical
  let _ : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel n) ⧸ Q) :=
    (quotientStructureMap Q d).toAlgebra
  have : FaithfulSMul (HolGerm (ComplexModel d)) (HolGerm (ComplexModel n) ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hQ.injective
  have : Algebra.IsIntegral (HolGerm (ComplexModel d)) (HolGerm (ComplexModel n) ⧸ Q) :=
    ⟨hQ.isIntegral⟩
  have hev : ∀ (F : (HolGerm (ComplexModel d))[X]) (g : HolGerm (ComplexModel n)),
      Ideal.Quotient.mk Q (evalGerm n F g) = aeval (Ideal.Quotient.mk Q g) F := fun F g => by
    rw [aeval_def, Polynomial.hom_eval₂]
    rfl
  have hmem : ∀ (F : (HolGerm (ComplexModel d))[X]) (g : HolGerm (ComplexModel n)),
      evalGerm n F g ∈ Q ↔ aeval (Ideal.Quotient.mk Q g) F = 0 := fun F g => by
    rw [← hev, Ideal.Quotient.eq_zero_iff_mem]
  have halg : ∀ r, algebraMap (HolGerm (ComplexModel d)) (HolGerm (ComplexModel n) ⧸ Q) r =
      Ideal.Quotient.mk Q (projGerm n d r) := fun r => rfl
  have hconst : ∀ z : ℂ, projGerm n d (constHom z) = constHom z := fun z => rfl
  let x : Fin n → HolGerm (ComplexModel n) ⧸ Q := fun k =>
    if d ≤ k.1 then Ideal.Quotient.mk Q (coord k) else 0
  obtain ⟨c, hc⟩ := exists_const_mul_eq_aeval (constHom : ℂ →+* HolGerm (ComplexModel d)) x
  have hu : Ideal.Quotient.mk Q (linearFormGerm n d c) =
      ∑ j, algebraMap (HolGerm (ComplexModel d)) _ (constHom (c j)) * x j := by
    simp only [linearFormGerm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d ≤ j.1
    · simp only [x, ite_eq_left hj, map_mul, halg, hconst]
    · simp only [x, ite_eq_right hj, map_zero, mul_zero]
  have hu0 : HolGerm.eval (linearFormGerm n d c) = 0 := by
    rw [linearFormGerm, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs
    · rw [map_mul, coord, coordGerm, eval_mk, map_zero, mul_zero]
    · exact map_zero _
  obtain ⟨W, hW, hWdeg, hWmem, hWdvd⟩ :=
    GermMinimalPolynomial.exists_minpoly_isWeierstrass hQ (linearFormGerm n d c) hu0
  obtain ⟨δ₁, hδ₁, a, b, hab⟩ := exists_mul_add_mul_derivative_eq_C
    (constHom : ℂ →+* HolGerm (ComplexModel d)) hW.1 ((hmem W _).1 hWmem)
    fun F hF => hWdvd F ((hmem F _).2 hF)
  choose e he G hG using hc
  obtain ⟨B, hBdef⟩ : ∃ B : Fin n → (HolGerm (ComplexModel d))[X], ∀ k,
      B k = (C (δ₁ * ∏ j ∈ Finset.univ.erase k, e j) * G k) %ₘ W := ⟨_, fun _ => rfl⟩
  have hW1 : W ≠ 1 := by
    rintro rfl
    simp at hWdeg
  have hB : ∀ k, aeval (Ideal.Quotient.mk Q (linearFormGerm n d c)) (B k) =
      algebraMap _ _ (δ₁ * ∏ j, e j) * x k := by
    intro k
    have h := congrArg (aeval (Ideal.Quotient.mk Q (linearFormGerm n d c)))
      (modByMonic_add_div (C (δ₁ * ∏ j ∈ Finset.univ.erase k, e j) * G k) W)
    rw [map_add, map_mul (aeval _) W, (hmem W _).1 hWmem, zero_mul, add_zero,
      map_mul (aeval _) (C _), aeval_C, hu,
      ← hG k] at h
    rw [hBdef, hu, h, ← mul_assoc, ← map_mul, mul_assoc,
      Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  refine ⟨c, W, δ₁ * ∏ j, e j, B, hW, hWdeg, hWmem, hWdvd,
    mul_ne_zero hδ₁ (Finset.prod_ne_zero_iff.2 fun k _ => he k),
    fun k => hBdef k ▸ natDegree_modByMonic_lt _ hW.1 hW1, fun k hk => ?_, hWdvd _ ?_,
    C (∏ j, e j) * a, C (∏ j, e j) * b, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hev, hB, map_mul, halg]
    simp only [x, ite_eq_left hk, sub_self]
  · rw [hmem]
    have hterm : ∀ k, aeval (Ideal.Quotient.mk Q (linearFormGerm n d c))
        (if d ≤ k.1 then C (constHom (c k) : HolGerm (ComplexModel d)) * B k else 0) =
        algebraMap (HolGerm (ComplexModel d)) _ (constHom (c k)) *
          (algebraMap (HolGerm (ComplexModel d)) _ (δ₁ * ∏ j, e j) * x k) := by
      intro k
      by_cases hk : d ≤ k.1
      · rw [ite_eq_left hk, map_mul, aeval_C, hB]
      · simp only [x, ite_eq_right hk, map_zero, mul_zero]
    rw [map_sub, map_sum, Finset.sum_congr rfl fun k _ => hterm k, map_mul (aeval _) (C _) X,
      aeval_C, aeval_X, hu,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun k _ => by ring
  · rw [C_mul]
    linear_combination C (∏ j, e j) * hab

end Germ

end SGPT.Foundations.Analysis.Pending.GermPrimitiveElement
