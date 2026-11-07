/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Weil.PrimeKloosterman
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# CRT factorization and Fourier completion

Exact Bézout/CRT factorization, reduced-modulus bounds, sharp centered Fourier
completion and weighted partial summation. The underlying techniques are standard; see
Iwaniec–Kowalski (2004), Ch. 12 §12.2, for completion methods. The declared hypotheses
govern each estimate.
-/

@[expose] public section


namespace KloostermanWeil

theorem kloostermanSumPrime_le_two_sqrt_of_not_both_zero
    (hWeil : PrimeNondegenerateWeil)
    (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hnot : a ≠ 0 ∨ b ≠ 0) :
    ‖kloostermanSumPrime p a b‖ ≤ 2 * Real.sqrt p := by
  have hp1 : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt p := (Real.one_le_sqrt).2 hp1
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := hnot.resolve_left (by simp)
    rw [kloostermanSumPrime_zero_left p b hb]
    norm_num
    nlinarith
  · by_cases hb : b = 0
    · subst b
      rw [kloostermanSumPrime_zero_right p a ha]
      norm_num
      nlinarith
    · exact hWeil p a b ha hb


/-! **CRT region**: exact unit-sum splitting via the chosen Bézout coefficients;
standard CRT, locally proved. No additional analytic hypothesis is hidden here. -/

def crtLeftCoeff (m n : ℕ) : ℤ := n.gcdA m

def crtRightCoeff (m n : ℕ) : ℤ := n.gcdB m

lemma crt_bezout
    {m n : ℕ} (hcop : m.Coprime n) :
    (n : ℤ) * crtLeftCoeff m n + (m : ℤ) * crtRightCoeff m n = 1 := by
  unfold crtLeftCoeff crtRightCoeff
  have h := Nat.gcd_eq_gcd_ab n m
  rw [Nat.Coprime.gcd_eq_one hcop.symm] at h
  simpa [add_comm] using h.symm

lemma stdAddChar_mul_eq_crt
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (t : ℤ) :
    ZMod.stdAddChar
        (((crtLeftCoeff m n) * t : ℤ) : ZMod m) *
      ZMod.stdAddChar
        (((crtRightCoeff m n) * t : ℤ) : ZMod n) =
      ZMod.stdAddChar ((t : ℤ) : ZMod (m * n)) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hbez := crt_bezout hcop
  have hbezC :
      (n : ℂ) * (crtLeftCoeff m n : ℂ) +
          (m : ℂ) * (crtRightCoeff m n : ℂ) = 1 := by
    exact_mod_cast hbez
  have hfrac :
      (crtLeftCoeff m n : ℂ) / (m : ℂ) +
          (crtRightCoeff m n : ℂ) / (n : ℂ) =
        1 / ((m : ℂ) * (n : ℂ)) := by
    field_simp [hm0, hn0]
    linear_combination hbezC
  push_cast
  calc
    2 * ↑Real.pi * Complex.I * (↑(crtLeftCoeff m n) * ↑t) / ↑m +
          2 * ↑Real.pi * Complex.I * (↑(crtRightCoeff m n) * ↑t) / ↑n =
        (2 * ↑Real.pi * Complex.I * ↑t) *
          (↑(crtLeftCoeff m n) / ↑m + ↑(crtRightCoeff m n) / ↑n) := by ring
    _ = (2 * ↑Real.pi * Complex.I * ↑t) *
          (1 / ((m : ℂ) * (n : ℂ))) := by rw [hfrac]
    _ = 2 * ↑Real.pi * Complex.I * ↑t / (↑m * ↑n) := by ring


noncomputable def kloostermanUnitSum
    (N : ℕ) [NeZero N] (a b : ZMod N) : ℂ :=
  ∑ x : (ZMod N)ˣ,
    ZMod.stdAddChar
      (b * (x : ZMod N) + a * ((x⁻¹ : (ZMod N)ˣ) : ZMod N))

lemma stdAddChar_mul_eq_crt_zmod
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (z : ZMod (m * n)) :
    ZMod.stdAddChar
        (((crtLeftCoeff m n : ℤ) : ZMod m) *
          (ZMod.chineseRemainder hcop z).1) *
      ZMod.stdAddChar
        (((crtRightCoeff m n : ℤ) : ZMod n) *
          (ZMod.chineseRemainder hcop z).2) =
      ZMod.stdAddChar z := by
  rw [← ZMod.natCast_zmod_val z]
  have hleft :
      (ZMod.chineseRemainder hcop ((z.val : ℕ) : ZMod (m * n))).1 =
        (z.val : ZMod m) := by
    simp [ZMod.chineseRemainder]
  have hright :
      (ZMod.chineseRemainder hcop ((z.val : ℕ) : ZMod (m * n))).2 =
        (z.val : ZMod n) := by
    simp [ZMod.chineseRemainder]
  rw [hleft, hright]
  simpa using (stdAddChar_mul_eq_crt hcop (z.val : ℤ))


noncomputable def crtUnitsEquiv
    {m n : ℕ} (hcop : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans
    MulEquiv.prodUnits

theorem kloostermanUnitSum_crt
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (a b : ZMod (m * n)) :
    kloostermanUnitSum (m * n) a b =
      kloostermanUnitSum m
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop a).1)
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop b).1) *
        kloostermanUnitSum n
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop a).2)
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop b).2) := by
  let e := crtUnitsEquiv hcop
  let α : ZMod m := ((crtLeftCoeff m n : ℤ) : ZMod m)
  let β : ZMod n := ((crtRightCoeff m n : ℤ) : ZMod n)
  let am : ZMod m := α * (ZMod.chineseRemainder hcop a).1
  let bm : ZMod m := α * (ZMod.chineseRemainder hcop b).1
  let an : ZMod n := β * (ZMod.chineseRemainder hcop a).2
  let bn : ZMod n := β * (ZMod.chineseRemainder hcop b).2
  let f : (ZMod m)ˣ → ℂ := fun x =>
    ZMod.stdAddChar (bm * (x : ZMod m) + am * ((x⁻¹ : (ZMod m)ˣ) : ZMod m))
  let g : (ZMod n)ˣ → ℂ := fun x =>
    ZMod.stdAddChar (bn * (x : ZMod n) + an * ((x⁻¹ : (ZMod n)ˣ) : ZMod n))
  change
    (∑ x : (ZMod (m * n))ˣ,
      ZMod.stdAddChar
        (b * (x : ZMod (m * n)) + a * ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n)))) =
      (∑ x : (ZMod m)ˣ, f x) * (∑ y : (ZMod n)ˣ, g y)
  calc
    (∑ x : (ZMod (m * n))ˣ,
      ZMod.stdAddChar
        (b * (x : ZMod (m * n)) + a * ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n)))) =
        ∑ y : (ZMod m)ˣ × (ZMod n)ˣ, f y.1 * g y.2 := by
          apply Fintype.sum_equiv e.toEquiv
          intro x
          have hx1 :
              (((e x).1 : (ZMod m)ˣ) : ZMod m) =
                (ZMod.chineseRemainder hcop (x : ZMod (m * n))).1 := by
            rfl
          have hx2 :
              (((e x).2 : (ZMod n)ˣ) : ZMod n) =
                (ZMod.chineseRemainder hcop (x : ZMod (m * n))).2 := by
            rfl
          have heinv : e (x⁻¹) = (e x)⁻¹ := map_inv e x
          have h1u : (e (x⁻¹)).1 = (e x).1⁻¹ :=
            congrArg Prod.fst heinv
          have h2u : (e (x⁻¹)).2 = (e x).2⁻¹ :=
            congrArg Prod.snd heinv
          have hxinv1 :
              ((((e x).1)⁻¹ : (ZMod m)ˣ) : ZMod m) =
                (ZMod.chineseRemainder hcop
                  ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n))).1 := by
            rw [← h1u]
            rfl
          have hxinv2 :
              ((((e x).2)⁻¹ : (ZMod n)ˣ) : ZMod n) =
                (ZMod.chineseRemainder hcop
                  ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n))).2 := by
            rw [← h2u]
            rfl
          have hchar := stdAddChar_mul_eq_crt_zmod hcop
            (b * (x : ZMod (m * n)) +
              a * ((x⁻¹ : (ZMod (m * n))ˣ) : ZMod (m * n)))
          rw [← hchar]
          dsimp [f, g, am, bm, an, bn, α, β]
          rw [hx1, hx2, hxinv1, hxinv2]
          simp only [map_add, map_mul, Prod.fst_add, Prod.fst_mul,
            Prod.snd_add, Prod.snd_mul]
          apply congrArg₂ (· * ·)
          · congr 1
            ring
          · congr 1
            ring
    _ = ∑ x : (ZMod m)ˣ, ∑ y : (ZMod n)ˣ, f x * g y := by
          rw [Fintype.sum_prod_type]
    _ = (∑ x : (ZMod m)ˣ, f x) * (∑ y : (ZMod n)ˣ, g y) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]


theorem kloostermanUnitSum_prime_eq
    (p : ℕ) [Fact p.Prime] (a b : ZMod p) :
    kloostermanUnitSum p a b = kloostermanSumPrime p a b := by
  unfold kloostermanUnitSum kloostermanSumPrime
  calc
    (∑ x : (ZMod p)ˣ,
      ZMod.stdAddChar
        (b * (x : ZMod p) + a * ((x⁻¹ : (ZMod p)ˣ) : ZMod p))) =
      ∑ y : {x : ZMod p // x ≠ 0},
        ZMod.stdAddChar (b * y.1 + a * y.1⁻¹) := by
          apply Fintype.sum_equiv unitsEquivNeZero
          intro x
          rw [unitsEquivNeZero_apply_coe, ZMod.inv_coe_unit]
    _ = ∑ x : ZMod p,
        if x = 0 then 0 else ZMod.stdAddChar (b * x + a * x⁻¹) := by
          rw [show (∑ y : {x : ZMod p // x ≠ 0},
              ZMod.stdAddChar (b * y.1 + a * y.1⁻¹)) =
              ∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ≠ 0),
                ZMod.stdAddChar (b * x + a * x⁻¹) by
                simpa using
                  (Finset.sum_subtype_eq_sum_filter
                    (s := (Finset.univ : Finset (ZMod p)))
                    (f := fun x : ZMod p =>
                      ZMod.stdAddChar (b * x + a * x⁻¹))
                    (p := fun x : ZMod p => x ≠ 0))]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h0 : x = 0 <;> simp [h0]


theorem norm_kloostermanUnitSum_crt
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (a b : ZMod (m * n)) :
    ‖kloostermanUnitSum (m * n) a b‖ =
      ‖kloostermanUnitSum m
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop a).1)
          (((crtLeftCoeff m n : ℤ) : ZMod m) *
            (ZMod.chineseRemainder hcop b).1)‖ *
        ‖kloostermanUnitSum n
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop a).2)
          (((crtRightCoeff m n : ℤ) : ZMod n) *
            (ZMod.chineseRemainder hcop b).2)‖ := by
  rw [kloostermanUnitSum_crt hcop]
  exact norm_mul _ _

theorem kloostermanUnitSum_prime_le_two_sqrt_of_not_both_zero
    (hWeil : PrimeNondegenerateWeil)
    (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (hnot : a ≠ 0 ∨ b ≠ 0) :
    ‖kloostermanUnitSum p a b‖ ≤ 2 * Real.sqrt p := by
  rw [kloostermanUnitSum_prime_eq]
  exact kloostermanSumPrime_le_two_sqrt_of_not_both_zero
    hWeil p a b hnot


lemma crtLeftCoeff_isUnit
    {m n : ℕ} [NeZero m] (hcop : m.Coprime n) :
    IsUnit (((crtLeftCoeff m n : ℤ) : ZMod m)) := by
  have hmul :
      (n : ZMod m) * (((crtLeftCoeff m n : ℤ) : ZMod m)) = 1 := by
    unfold crtLeftCoeff
    rw [CharP.intCast_mul_natCast_gcdA_eq_gcd]
    simp [Nat.Coprime.gcd_eq_one hcop.symm]
  exact IsUnit.of_mul_eq_one (n : ZMod m) (by simpa [mul_comm] using hmul)

lemma crtRightCoeff_isUnit
    {m n : ℕ} [NeZero n] (hcop : m.Coprime n) :
    IsUnit (((crtRightCoeff m n : ℤ) : ZMod n)) := by
  have hbez := crt_bezout hcop
  have hbezZ :
      (n : ZMod n) * (((crtLeftCoeff m n : ℤ) : ZMod n)) +
          (m : ZMod n) * (((crtRightCoeff m n : ℤ) : ZMod n)) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod n)) hbez
    simpa using h
  have hmul :
      (m : ZMod n) * (((crtRightCoeff m n : ℤ) : ZMod n)) = 1 := by
    simpa using hbezZ
  exact IsUnit.of_mul_eq_one (m : ZMod n) (by simpa [mul_comm] using hmul)

lemma crt_local_left_isUnit
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) {a : ZMod (m * n)} (ha : IsUnit a) :
    IsUnit
      ((((crtLeftCoeff m n : ℤ) : ZMod m) *
        (ZMod.chineseRemainder hcop a).1)) := by
  have hpair : IsUnit (ZMod.chineseRemainder hcop a) :=
    ha.map (ZMod.chineseRemainder hcop).toMonoidHom
  have hproj : IsUnit (ZMod.chineseRemainder hcop a).1 :=
    (Prod.isUnit_iff.mp hpair).1
  exact (crtLeftCoeff_isUnit hcop).mul hproj

lemma crt_local_right_isUnit
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) {a : ZMod (m * n)} (ha : IsUnit a) :
    IsUnit
      ((((crtRightCoeff m n : ℤ) : ZMod n) *
        (ZMod.chineseRemainder hcop a).2)) := by
  have hpair : IsUnit (ZMod.chineseRemainder hcop a) :=
    ha.map (ZMod.chineseRemainder hcop).toMonoidHom
  have hproj : IsUnit (ZMod.chineseRemainder hcop a).2 :=
    (Prod.isUnit_iff.mp hpair).2
  exact (crtRightCoeff_isUnit hcop).mul hproj


theorem kloostermanUnitSum_prod_primes_le
    (hWeil : PrimeNondegenerateWeil) :
    ∀ (s : Finset ℕ) (Q : ℕ),
      Q = ∏ p ∈ s, p → ∀ (hQ0 : Q ≠ 0),
      (∀ p ∈ s, p.Prime) → ∀ (a b : ZMod Q), IsUnit a →
        ‖@kloostermanUnitSum Q ⟨hQ0⟩ a b‖ ≤
          (2 : ℝ) ^ s.card * Real.sqrt Q := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro Q hQ hQ0 hsprime a b ha
      subst Q
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero,
        Nat.cast_one, Real.sqrt_one, one_mul] at a b ha ⊢
      simp [kloostermanUnitSum, Subsingleton.elim a 0,
        Subsingleton.elim b 0]
  | @insert p s hpnot ih =>
      intro Q hQ hQ0 hsprime a b ha
      have hpP : p.Prime := hsprime p (by simp)
      have hsP : ∀ r ∈ s, r.Prime := by
        intro r hr
        exact hsprime r (by simp [hr])
      let M : ℕ := ∏ r ∈ s, r
      have hM0 : M ≠ 0 := by
        dsimp [M]
        exact Finset.prod_ne_zero_iff.mpr fun r hr => (hsP r hr).ne_zero
      have hQeq : Q = p * M := by
        calc
          Q = ∏ r ∈ insert p s, r := hQ
          _ = p * M := by simp [M, hpnot]
      clear hQ
      subst Q
      let : NeZero M := ⟨hM0⟩
      let : Fact p.Prime := ⟨hpP⟩
      let : NeZero (p * M) := ⟨mul_ne_zero hpP.ne_zero hM0⟩
      have hcop : p.Coprime M := by
        apply hpP.coprime_iff_not_dvd.mpr
        intro hpd
        have hex := (hpP.prime.dvd_finsetProd_iff (fun r : ℕ => r)).mp hpd
        rcases hex with ⟨r, hr, hpr⟩
        have hrP := hsP r hr
        have hrpeq : r = p := (hrP.dvd_iff_eq hpP.ne_one).mp hpr
        exact hpnot (hrpeq ▸ hr)
      have haP :
          IsUnit
            ((((crtLeftCoeff p M : ℤ) : ZMod p) *
              (ZMod.chineseRemainder hcop a).1)) :=
        crt_local_left_isUnit hcop ha
      have haM :
          IsUnit
            ((((crtRightCoeff p M : ℤ) : ZMod M) *
              (ZMod.chineseRemainder hcop a).2)) :=
        crt_local_right_isUnit hcop ha
      have hprime :
          ‖kloostermanUnitSum p
              (((crtLeftCoeff p M : ℤ) : ZMod p) *
                (ZMod.chineseRemainder hcop a).1)
              (((crtLeftCoeff p M : ℤ) : ZMod p) *
                (ZMod.chineseRemainder hcop b).1)‖ ≤
            2 * Real.sqrt p := by
        apply kloostermanUnitSum_prime_le_two_sqrt_of_not_both_zero
          hWeil p
        exact Or.inl haP.ne_zero
      have hrec :
          ‖kloostermanUnitSum M
              (((crtRightCoeff p M : ℤ) : ZMod M) *
                (ZMod.chineseRemainder hcop a).2)
              (((crtRightCoeff p M : ℤ) : ZMod M) *
                (ZMod.chineseRemainder hcop b).2)‖ ≤
            (2 : ℝ) ^ s.card * Real.sqrt M := by
        exact ih M rfl hM0 hsP _ _ haM
      rw [norm_kloostermanUnitSum_crt hcop]
      calc
        _ ≤ (2 * Real.sqrt p) *
              ((2 : ℝ) ^ s.card * Real.sqrt M) :=
          mul_le_mul hprime hrec (norm_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (insert p s).card *
              Real.sqrt ((p : ℝ) * (M : ℝ)) := by
          rw [Finset.card_insert_of_notMem hpnot, pow_succ]
          rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ p)]
          ring
        _ = (2 : ℝ) ^ (insert p s).card *
              Real.sqrt (((p * M : ℕ) : ℝ)) := by
          rw [Nat.cast_mul]


theorem kloostermanUnitSum_squarefree_unit_le
    (hWeil : PrimeNondegenerateWeil)
    {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (a b : ZMod q) (ha : IsUnit a) :
    ‖kloostermanUnitSum q a b‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * Real.sqrt q := by
  exact kloostermanUnitSum_prod_primes_le hWeil
    q.primeFactors q
    (Nat.prod_primeFactors_of_squarefree hsq).symm
    (NeZero.ne q)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
    a b ha


/-! **Reduction region**: bound for a source-defined reduced modulus/sum.
No theorem here identifies that reduced sum with a full-modulus sum. -/

def reducedDivisor (A q : ℕ) : ℕ := Nat.gcd A q

def reducedModulus (A q : ℕ) : ℕ := q / reducedDivisor A q

def reducedNumerator (A q : ℕ) : ℕ := A / reducedDivisor A q

lemma reducedNumerator_coprime_reducedModulus
    {A q : ℕ} (hq : 0 < q) :
    (reducedNumerator A q).Coprime (reducedModulus A q) := by
  unfold reducedNumerator reducedModulus reducedDivisor
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right A hq)

lemma reducedModulus_dvd
    {A q : ℕ} :
    reducedModulus A q ∣ q := by
  unfold reducedModulus reducedDivisor
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right A q)

lemma reducedModulus_pos
    {A q : ℕ} (hq : 0 < q) :
    0 < reducedModulus A q := by
  unfold reducedModulus reducedDivisor
  apply Nat.div_pos
  · exact Nat.gcd_le_right A hq
  · exact Nat.gcd_pos_of_pos_right A hq

lemma reducedModulus_squarefree
    {A q : ℕ} (hsq : Squarefree q) :
    Squarefree (reducedModulus A q) :=
  hsq.squarefree_of_dvd reducedModulus_dvd

lemma reducedNumerator_isUnit
    {A q : ℕ} (hq : 0 < q) :
    IsUnit ((reducedNumerator A q : ℕ) : ZMod (reducedModulus A q)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact reducedNumerator_coprime_reducedModulus hq

theorem kloostermanUnitSum_reduced_le
    (hWeil : PrimeNondegenerateWeil)
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (b : ZMod (reducedModulus A q)) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖kloostermanUnitSum (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q)) b‖ ≤
      (2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
        Real.sqrt (reducedModulus A q) := by
  let : NeZero (reducedModulus A q) :=
    ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
  exact kloostermanUnitSum_squarefree_unit_le hWeil
    (reducedModulus_squarefree hsq)
    (reducedNumerator A q : ZMod (reducedModulus A q)) b
    (reducedNumerator_isUnit hq)


/-! **Completion region**: character orthogonality, full finite DFT and
sharp interval Fourier completion; method context [IwaniecKowalski2004]. -/

def zmodFrequencyDistance {N : ℕ} [NeZero N] (h : ZMod N) : ℕ :=
  min h.val (N - h.val)

lemma zmodFrequencyDistance_pos
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0) :
    0 < zmodFrequencyDistance h := by
  unfold zmodFrequencyDistance
  have hv0 : 0 < h.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero h).2 hh)
  have hvlt : h.val < N := ZMod.val_lt h
  exact lt_min hv0 (Nat.sub_pos_of_lt hvlt)

lemma two_mul_zmodFrequencyDistance_le
    {N : ℕ} [NeZero N] (h : ZMod N) :
    2 * zmodFrequencyDistance h ≤ N := by
  unfold zmodFrequencyDistance
  have h1 : min h.val (N - h.val) ≤ h.val := min_le_left _ _
  have h2 : min h.val (N - h.val) ≤ N - h.val := min_le_right _ _
  have hvlt : h.val < N := ZMod.val_lt h
  omega

lemma stdAddChar_chord_lower
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0) :
    (4 : ℝ) * zmodFrequencyDistance h / N ≤
      ‖ZMod.stdAddChar h - 1‖ := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (NeZero.pos N)
  have hkpos : (0 : ℝ) < zmodFrequencyDistance h := by
    exact_mod_cast zmodFrequencyDistance_pos hh
  have h2k : (2 : ℝ) * zmodFrequencyDistance h ≤ N := by
    exact_mod_cast two_mul_zmodFrequencyDistance_le h
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  let x : ℝ := Real.pi * (h.val : ℝ) / N
  let k : ℕ := zmodFrequencyDistance h
  have hsin :
      (2 : ℝ) * k / N ≤ |Real.sin x| := by
    by_cases hsmall : h.val ≤ N - h.val
    · have hk : k = h.val := by
        dsimp [k, zmodFrequencyDistance]
        exact min_eq_left hsmall
      have hx0 : 0 ≤ x := by
        dsimp [x]
        positivity
      have hxhalf : x ≤ Real.pi / 2 := by
        dsimp [x]
        have hv : (2 : ℝ) * h.val ≤ N := by
          exact_mod_cast (by omega : 2 * h.val ≤ N)
        apply (div_le_iff₀ hNpos).2
        nlinarith
      have hs := Real.mul_le_sin hx0 hxhalf
      have hsin0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0
        (hxhalf.trans (by linarith [Real.pi_pos]))
      rw [abs_of_nonneg hsin0, hk]
      calc
        (2 : ℝ) * h.val / N =
            (2 / Real.pi) * x := by
              dsimp [x]
              field_simp [hNpos.ne', Real.pi_ne_zero]
        _ ≤ Real.sin x := hs
    · have hbig : N - h.val ≤ h.val := by omega
      have hk : k = N - h.val := by
        dsimp [k, zmodFrequencyDistance]
        exact min_eq_right hbig
      let y : ℝ := Real.pi * ((N - h.val : ℕ) : ℝ) / N
      have hy0 : 0 ≤ y := by
        dsimp [y]
        positivity
      have hyhalf : y ≤ Real.pi / 2 := by
        dsimp [y]
        have hv : (2 : ℝ) * (N - h.val : ℕ) ≤ N := by
          exact_mod_cast (by omega : 2 * (N - h.val) ≤ N)
        apply (div_le_iff₀ hNpos).2
        nlinarith
      have hxy : y = Real.pi - x := by
        dsimp [x, y]
        have hvlt : h.val < N := ZMod.val_lt h
        rw [Nat.cast_sub (Nat.le_of_lt hvlt)]
        field_simp [hNpos.ne']
      have hs := Real.mul_le_sin hy0 hyhalf
      have hsin0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0
        (hyhalf.trans (by linarith [Real.pi_pos]))
      have hsineq : Real.sin y = Real.sin x := by
        rw [hxy, Real.sin_pi_sub]
      rw [← hsineq, abs_of_nonneg hsin0, hk]
      calc
        (2 : ℝ) * (N - h.val : ℕ) / N =
            (2 / Real.pi) * y := by
              dsimp [y]
              field_simp [hNpos.ne', Real.pi_ne_zero]
        _ ≤ Real.sin y := hs
  have hnorm :
      ‖ZMod.stdAddChar h - 1‖ =
        2 * |Real.sin x| := by
    rw [← ZMod.natCast_zmod_val h]
    have hcast :
        ((h.val : ℕ) : ZMod N) = ((h.val : ℤ) : ZMod N) := by
      norm_cast
    rw [hcast, ZMod.stdAddChar_coe]
    have hexp :
        Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((h.val : ℤ) : ℂ) / (N : ℂ)) =
          Complex.exp (Complex.I * ((2 * x : ℝ) : ℂ)) := by
      congr 1
      dsimp [x]
      push_cast
      ring
    rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [Real.norm_eq_abs]
  rw [hnorm]
  calc
    (4 : ℝ) * zmodFrequencyDistance h / N =
        2 * ((2 : ℝ) * k / N) := by
          dsimp [k]
          ring
    _ ≤ 2 * |Real.sin x| :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)


noncomputable def unitsEquivIsUnitSubtype (M : Type*) [Monoid M] :
    Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := by
    apply Units.ext
    simp [IsUnit.unit_of_val_units]
  right_inv x := by
    apply Subtype.ext
    exact x.2.unit_spec

noncomputable def reciprocalPhase
    (N : ℕ) [NeZero N] (a x : ZMod N) : ℂ :=
  if IsUnit x then ZMod.stdAddChar (a * x⁻¹) else 0

noncomputable def reciprocalMean
    (N : ℕ) [NeZero N] (a : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, reciprocalPhase N a x

noncomputable def centeredReciprocalPhase
    (N : ℕ) [NeZero N] (a x : ZMod N) : ℂ :=
  reciprocalPhase N a x - reciprocalMean N a

lemma sum_centeredReciprocalPhase_eq_zero
    (N : ℕ) [NeZero N] (a : ZMod N) :
    ∑ x : ZMod N, centeredReciprocalPhase N a x = 0 := by
  unfold centeredReciprocalPhase reciprocalMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp [nsmul_eq_mul, hN]

lemma sum_reciprocalPhase_eq_kloostermanUnitSum
    (N : ℕ) [NeZero N] (a b : ZMod N) :
    (∑ x : ZMod N,
      ZMod.stdAddChar (b * x) * reciprocalPhase N a x) =
      kloostermanUnitSum N a b := by
  unfold reciprocalPhase kloostermanUnitSum
  calc
    (∑ x : ZMod N,
      ZMod.stdAddChar (b * x) *
        (if IsUnit x then ZMod.stdAddChar (a * x⁻¹) else 0)) =
      ∑ x ∈ (Finset.univ.filter fun x : ZMod N => IsUnit x),
        ZMod.stdAddChar (b * x + a * x⁻¹) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hu : IsUnit x
          · simp [hu, AddChar.map_add_eq_mul]
          · simp [hu]
    _ = ∑ y : {x : ZMod N // IsUnit x},
        ZMod.stdAddChar (b * y.1 + a * y.1⁻¹) := by
          symm
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (ZMod N)))
              (f := fun x : ZMod N =>
                ZMod.stdAddChar (b * x + a * x⁻¹))
              (p := fun x : ZMod N => IsUnit x))
    _ = ∑ u : (ZMod N)ˣ,
        ZMod.stdAddChar
          (b * (u : ZMod N) +
            a * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := by
          symm
          apply Fintype.sum_equiv (unitsEquivIsUnitSubtype (ZMod N))
          intro u
          simp [unitsEquivIsUnitSubtype, ZMod.inv_coe_unit]

lemma dft_centeredReciprocalPhase_nonzero
    (N : ℕ) [NeZero N] (a : ZMod N) {h : ZMod N} (hh : h ≠ 0) :
    ZMod.dft (centeredReciprocalPhase N a) h =
      kloostermanUnitSum N a (-h) := by
  rw [ZMod.dft_apply]
  unfold centeredReciprocalPhase
  simp only [smul_eq_mul, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hchar :
      (∑ j : ZMod N, ZMod.stdAddChar (-(j * h))) = 0 := by
    have hprim : (ZMod.stdAddChar (N := N)).IsPrimitive :=
      ZMod.isPrimitive_stdAddChar N
    have hne :
        (ZMod.stdAddChar (N := N)).mulShift (-h) ≠ 1 :=
      hprim (neg_ne_zero.mpr hh)
    have hz := AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply, mul_comm] using hz
  calc
    (∑ j : ZMod N,
      ZMod.stdAddChar (-(j * h)) *
        reciprocalPhase N a j) -
        ∑ j : ZMod N,
          ZMod.stdAddChar (-(j * h)) *
            reciprocalMean N a =
      ∑ j : ZMod N,
        ZMod.stdAddChar ((-h) * j) *
          reciprocalPhase N a j := by
            have hconst :
                (∑ j : ZMod N,
                  ZMod.stdAddChar (-(j * h)) *
                    reciprocalMean N a) = 0 := by
              rw [← Finset.sum_mul, hchar, zero_mul]
            rw [hconst, sub_zero]
            apply Finset.sum_congr rfl
            intro j hj
            congr 2
            ring
    _ = kloostermanUnitSum N a (-h) := by
          simpa [neg_mul, mul_comm] using
            sum_reciprocalPhase_eq_kloostermanUnitSum N a (-h)


/-- Bézout/CRT factorization of the standard additive character on a coprime
product modulus. The local shifts are units modulo the opposite factors. -/
theorem stdAddChar_crt_bezout
    {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (y : ℤ) :
    ZMod.stdAddChar (y : ZMod (m * n)) =
      ZMod.stdAddChar ((n.gcdA m * y : ℤ) : ZMod m) *
      ZMod.stdAddChar ((n.gcdB m * y : ℤ) : ZMod n) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [← Complex.exp_add]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hbez : (1 : ℤ) =
      (n : ℤ) * n.gcdA m + (m : ℤ) * n.gcdB m := by
    simpa [hcop.symm.gcd_eq_one] using (Nat.gcd_eq_gcd_ab n m)
  have hbezC : (1 : ℂ) =
      (n : ℂ) * (n.gcdA m : ℂ) + (m : ℂ) * (n.gcdB m : ℂ) := by
    exact_mod_cast hbez
  push_cast
  field_simp [hm0, hn0]
  rw [← hbezC]
  ring


lemma norm_stdAddChar_eq_one
    (N : ℕ) [NeZero N] (h : ZMod N) :
    ‖ZMod.stdAddChar h‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Geometric kernel bound for a nonzero Fourier frequency. This is the
finite-completion denominator estimate used after centering. -/
theorem geometricKernel_norm_le
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0) (L : ℕ) :
    ‖∑ j ∈ Finset.range L, (ZMod.stdAddChar h) ^ j‖ ≤
      (N : ℝ) / (2 * zmodFrequencyDistance h) := by
  let z : ℂ := ZMod.stdAddChar h
  let S : ℂ := ∑ j ∈ Finset.range L, z ^ j
  have hz1 : ‖z‖ = 1 := by
    dsimp [z]
    exact norm_stdAddChar_eq_one N h
  have hnum : ‖z ^ L - 1‖ ≤ 2 := by
    calc
      ‖z ^ L - 1‖ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hz1]
  have hgeom : S * (z - 1) = z ^ L - 1 := by
    dsimp [S]
    exact geom_sum_mul z L
  have hprod : ‖S‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    exact hnum
  have hchord :
      (4 : ℝ) * zmodFrequencyDistance h / N ≤ ‖z - 1‖ := by
    dsimp [z]
    exact stdAddChar_chord_lower hh
  have hS : 0 ≤ ‖S‖ := norm_nonneg _
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hd : (0 : ℝ) < zmodFrequencyDistance h := by
    exact_mod_cast zmodFrequencyDistance_pos hh
  have haux :
      ‖S‖ * ((4 : ℝ) * zmodFrequencyDistance h / N) ≤ 2 := by
    calc
      ‖S‖ * ((4 : ℝ) * zmodFrequencyDistance h / N) ≤
          ‖S‖ * ‖z - 1‖ :=
        mul_le_mul_of_nonneg_left hchord hS
      _ ≤ 2 := hprod
  apply (le_div_iff₀ (show 0 < (2 : ℝ) * zmodFrequencyDistance h by positivity)).2
  have hscaled := mul_le_mul_of_nonneg_left haux hN.le
  field_simp [hN.ne'] at hscaled
  nlinarith


lemma sum_Ico_one_inv_le_harmonic (N : ℕ) :
    (∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹)) ≤ (harmonic N : ℝ) := by
  have hsub : Finset.Ico 1 N ⊆ Finset.Icc 1 N := by
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, hi.2.le⟩
  calc
    (∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹)) ≤
        ∑ i ∈ Finset.Icc 1 N, ((i : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro i hi hin
          positivity
    _ = (harmonic N : ℝ) := by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
            Rat.cast_natCast]

lemma sum_Ico_reflected_inv_eq (N : ℕ) :
    (∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹)) =
      ∑ i ∈ Finset.Ico 1 N, ((i : ℝ)⁻¹) := by
  apply Finset.sum_bij (fun i hi => N - i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    refine ⟨N - j, ?_, ?_⟩
    · simp only [Finset.mem_Ico] at hj ⊢
      omega
    · simp only [Finset.mem_Ico] at hj
      omega
  · intro i hi
    rfl

lemma zmod_finEquiv_val
    {N : ℕ} [NeZero N] (i : Fin N) :
    ((ZMod.finEquiv N) i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

lemma zmod_finEquiv_eq_zero_iff
    {N : ℕ} [NeZero N] (i : Fin N) :
    (ZMod.finEquiv N) i = 0 ↔ i.val = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [zmod_finEquiv_val] using hv
  · intro h
    have hi : i = 0 := by
      apply Fin.ext
      simpa using h
    subst i
    simp


lemma fin_sum_inv_val_eq_Ico (N : ℕ) :
    (∑ i : Fin N, if i.val = 0 then (0 : ℝ) else (i.val : ℝ)⁻¹) =
      ∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹ := by
  calc
    (∑ i : Fin N, if i.val = 0 then (0 : ℝ) else (i.val : ℝ)⁻¹) =
        ∑ i ∈ Finset.range N, if i = 0 then (0 : ℝ) else (i : ℝ)⁻¹ := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun i : ℕ => if i = 0 then (0 : ℝ) else (i : ℝ)⁻¹) N)
    _ = ∑ i ∈ (Finset.range N).filter (fun i => i ≠ 0), (i : ℝ)⁻¹ := by
          symm
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h0 : i = 0 <;> simp [h0]
    _ = ∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹ := by
          congr 1
          ext i
          simp
          omega

lemma fin_sum_inv_complement_eq_Ico_reflected (N : ℕ) :
    (∑ i : Fin N,
      if i.val = 0 then (0 : ℝ) else (((N - i.val : ℕ) : ℝ)⁻¹)) =
      ∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹) := by
  calc
    (∑ i : Fin N,
      if i.val = 0 then (0 : ℝ) else (((N - i.val : ℕ) : ℝ)⁻¹)) =
        ∑ i ∈ Finset.range N,
          if i = 0 then (0 : ℝ) else (((N - i : ℕ) : ℝ)⁻¹) := by
            simpa using
              (Fin.sum_univ_eq_sum_range
                (fun i : ℕ =>
                  if i = 0 then (0 : ℝ)
                  else (((N - i : ℕ) : ℝ)⁻¹)) N)
    _ = ∑ i ∈ (Finset.range N).filter (fun i => i ≠ 0),
          (((N - i : ℕ) : ℝ)⁻¹) := by
            symm
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h0 : i = 0 <;> simp [h0]
    _ = ∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹) := by
            congr 1
            ext i
            simp
            omega

/-- Harmonic mass of all nonzero Fourier frequencies, in the symmetric
distance normalization used by the geometric kernel. -/
theorem frequencyReciprocalMass_le_two_harmonic
    (N : ℕ) [NeZero N] :
    (∑ h : ZMod N,
      if h = 0 then (0 : ℝ)
      else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) ≤
      2 * (harmonic N : ℝ) := by
  have hfin :
      (∑ h : ZMod N,
        if h = 0 then (0 : ℝ)
        else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) =
      ∑ i : Fin N,
        if i.val = 0 then (0 : ℝ)
        else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹ := by
    symm
    apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
    intro i
    change
      (if i.val = 0 then (0 : ℝ)
       else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹) =
      (if (ZMod.finEquiv N) i = 0 then (0 : ℝ)
       else ((zmodFrequencyDistance ((ZMod.finEquiv N) i) : ℕ) : ℝ)⁻¹)
    by_cases h0 : i.val = 0
    · have hz : (ZMod.finEquiv N) i = 0 :=
        (zmod_finEquiv_eq_zero_iff i).2 h0
      simp [h0, hz]
    · have hz : (ZMod.finEquiv N) i ≠ 0 := by
        intro hz
        exact h0 ((zmod_finEquiv_eq_zero_iff i).1 hz)
      simp [h0, hz, zmodFrequencyDistance, zmod_finEquiv_val]
  rw [hfin]
  have hterm : ∀ i : Fin N,
      (if i.val = 0 then (0 : ℝ)
        else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹) ≤
      (if i.val = 0 then 0 else (i.val : ℝ)⁻¹) +
      (if i.val = 0 then 0 else (((N - i.val : ℕ) : ℝ)⁻¹)) := by
    intro i
    by_cases h0 : i.val = 0
    · simp [h0]
    · simp only [h0, ite_false]
      have hiv : 0 < i.val := Nat.pos_of_ne_zero h0
      have hic : 0 < N - i.val := Nat.sub_pos_of_lt i.isLt
      by_cases hle : i.val ≤ N - i.val
      · rw [min_eq_left hle]
        have hnon : 0 ≤ (((N - i.val : ℕ) : ℝ)⁻¹) := by positivity
        linarith
      · have hge : N - i.val ≤ i.val := Nat.le_of_not_ge hle
        rw [min_eq_right hge]
        have hnon : 0 ≤ ((i.val : ℝ)⁻¹) := by positivity
        linarith
  calc
    (∑ i : Fin N,
      if i.val = 0 then (0 : ℝ)
      else ((min i.val (N - i.val) : ℕ) : ℝ)⁻¹) ≤
        ∑ i : Fin N,
          ((if i.val = 0 then 0 else (i.val : ℝ)⁻¹) +
           (if i.val = 0 then 0 else (((N - i.val : ℕ) : ℝ)⁻¹))) := by
            exact Finset.sum_le_sum fun i hi => hterm i
    _ = (∑ i : Fin N, if i.val = 0 then 0 else (i.val : ℝ)⁻¹) +
        (∑ i : Fin N,
          if i.val = 0 then 0 else (((N - i.val : ℕ) : ℝ)⁻¹)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹) +
        (∑ i ∈ Finset.Ico 1 N, (((N - i : ℕ) : ℝ)⁻¹)) := by
          rw [fin_sum_inv_val_eq_Ico, fin_sum_inv_complement_eq_Ico_reflected]
    _ = 2 * (∑ i ∈ Finset.Ico 1 N, (i : ℝ)⁻¹) := by
          rw [sum_Ico_reflected_inv_eq]
          ring
    _ ≤ 2 * (harmonic N : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (sum_Ico_one_inv_le_harmonic N) (by norm_num)

theorem frequencyReciprocalMass_le_log
    (N : ℕ) [NeZero N] :
    (∑ h : ZMod N,
      if h = 0 then (0 : ℝ)
      else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) ≤
      2 * (1 + Real.log N) := by
  calc
    _ ≤ 2 * (harmonic N : ℝ) :=
      frequencyReciprocalMass_le_two_harmonic N
    _ ≤ 2 * (1 + Real.log N) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by norm_num)


noncomputable def intervalCharacterKernel
    (N : ℕ) [NeZero N] (h x : ZMod N) (L : ℕ) : ℂ :=
  ∑ j ∈ Finset.range L,
    ZMod.stdAddChar (h * (x + (j : ZMod N)))

lemma intervalCharacterKernel_eq
    (N : ℕ) [NeZero N] (h x : ZMod N) (L : ℕ) :
    intervalCharacterKernel N h x L =
      ZMod.stdAddChar (h * x) *
        (∑ j ∈ Finset.range L, (ZMod.stdAddChar h) ^ j) := by
  unfold intervalCharacterKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_add, AddChar.map_add_eq_mul]
  congr 1
  have hpow :
      ZMod.stdAddChar (h * (j : ZMod N)) =
        (ZMod.stdAddChar h) ^ j := by
    rw [mul_comm]
    simpa [nsmul_eq_mul] using
      (AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := N)) j h)
  exact hpow

theorem intervalCharacterKernel_norm_le
    {N : ℕ} [NeZero N] {h : ZMod N} (hh : h ≠ 0)
    (x : ZMod N) (L : ℕ) :
    ‖intervalCharacterKernel N h x L‖ ≤
      (N : ℝ) / (2 * zmodFrequencyDistance h) := by
  rw [intervalCharacterKernel_eq, norm_mul, norm_stdAddChar_eq_one, one_mul]
  exact geometricKernel_norm_le hh L

noncomputable def centeredIntervalSum
    (N : ℕ) [NeZero N] (a x : ZMod N) (L : ℕ) : ℂ :=
  ∑ j ∈ Finset.range L,
    centeredReciprocalPhase N a (x + (j : ZMod N))

lemma centeredReciprocalPhase_fourier_inversion
    (N : ℕ) [NeZero N] (a y : ZMod N) :
    centeredReciprocalPhase N a y =
      (N : ℂ)⁻¹ *
        ∑ h : ZMod N,
          ZMod.stdAddChar (h * y) *
            ZMod.dft (centeredReciprocalPhase N a) h := by
  have hInv := congrFun
    (ZMod.dft.symm_apply_apply (centeredReciprocalPhase N a)) y
  rw [ZMod.invDFT_apply] at hInv
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hInv.symm

lemma centeredIntervalSum_fourier
    (N : ℕ) [NeZero N] (a x : ZMod N) (L : ℕ) :
    centeredIntervalSum N a x L =
      (N : ℂ)⁻¹ *
        ∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L := by
  unfold centeredIntervalSum
  calc
    (∑ j ∈ Finset.range L,
      centeredReciprocalPhase N a (x + (j : ZMod N))) =
        ∑ j ∈ Finset.range L,
          ((N : ℂ)⁻¹ *
            ∑ h : ZMod N,
              ZMod.stdAddChar (h * (x + (j : ZMod N))) *
                ZMod.dft (centeredReciprocalPhase N a) h) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [centeredReciprocalPhase_fourier_inversion]
    _ = (N : ℂ)⁻¹ *
        ∑ j ∈ Finset.range L,
          ∑ h : ZMod N,
            ZMod.stdAddChar (h * (x + (j : ZMod N))) *
              ZMod.dft (centeredReciprocalPhase N a) h := by
          rw [Finset.mul_sum]
    _ = (N : ℂ)⁻¹ *
        ∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h hh
          unfold intervalCharacterKernel
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring


/-- Generic centered finite Fourier completion. The analytic input is only a
uniform bound on nonzero Fourier coefficients. -/
theorem centeredIntervalSum_norm_le_of_dft_bound
    {N : ℕ} [NeZero N] (a x : ZMod N) (L : ℕ)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ h : ZMod N, h ≠ 0 →
      ‖ZMod.dft (centeredReciprocalPhase N a) h‖ ≤ B) :
    ‖centeredIntervalSum N a x L‖ ≤
      B * (1 + Real.log N) := by
  have hzero :
      ZMod.dft (centeredReciprocalPhase N a) 0 = 0 := by
    rw [ZMod.dft_apply_zero, sum_centeredReciprocalPhase_eq_zero]
  have hsum :
      ‖∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ ≤
        ∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h)) := by
    calc
      ‖∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ ≤
        ∑ h : ZMod N,
          ‖ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h)) := by
            apply Finset.sum_le_sum
            intro h hhmem
            by_cases hh : h = 0
            · subst h
              simp [hzero]
            · rw [ite_eq_right hh, norm_mul]
              exact mul_le_mul
                (hB h hh)
                (intervalCharacterKernel_norm_le hh x L)
                (norm_nonneg _)
                hB0
  have hmass :
      (∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h))) ≤
        B * ((N : ℝ) / 2) * (2 * (1 + Real.log N)) := by
    calc
      (∑ h : ZMod N,
          if h = 0 then 0
          else B * ((N : ℝ) / (2 * zmodFrequencyDistance h))) =
        B * ((N : ℝ) / 2) *
          (∑ h : ZMod N,
            if h = 0 then 0
            else ((zmodFrequencyDistance h : ℕ) : ℝ)⁻¹) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro h hhmem
              by_cases hh : h = 0
              · simp [hh]
              · simp only [hh, ite_false]
                have hd : (0 : ℝ) < zmodFrequencyDistance h := by
                  exact_mod_cast zmodFrequencyDistance_pos hh
                field_simp [hd.ne']
      _ ≤ B * ((N : ℝ) / 2) * (2 * (1 + Real.log N)) := by
            apply mul_le_mul_of_nonneg_left
              (frequencyReciprocalMass_le_log N)
            positivity
  rw [centeredIntervalSum_fourier, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (N : ℝ)⁻¹ *
        ‖∑ h : ZMod N,
          ZMod.dft (centeredReciprocalPhase N a) h *
            intervalCharacterKernel N h x L‖ ≤
      (N : ℝ)⁻¹ *
        (B * ((N : ℝ) / 2) * (2 * (1 + Real.log N))) := by
          exact mul_le_mul_of_nonneg_left (hsum.trans hmass) (by positivity)
    _ = B * (1 + Real.log N) := by
          have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
          field_simp [hN]


/-- Centered incomplete reciprocal-phase completion at the reduced squarefree modulus.
The interval length is unrestricted. The `PrimeNondegenerateWeil` premise is proved in
`LeanPool.KloostermanWeil.Weil.PrimeKloosterman`. -/
theorem centeredReducedIntervalSum_le
    (hWeil : PrimeNondegenerateWeil)
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q)) (L : ℕ) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖centeredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x L‖ ≤
      ((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
          Real.sqrt (reducedModulus A q)) *
        (1 + Real.log (reducedModulus A q)) := by
  let : NeZero (reducedModulus A q) :=
    ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
  apply centeredIntervalSum_norm_le_of_dft_bound
    (a := (reducedNumerator A q : ZMod (reducedModulus A q)))
    (x := x) (L := L)
  · positivity
  · intro h hh
    rw [dft_centeredReciprocalPhase_nonzero
      (reducedModulus A q)
      (reducedNumerator A q : ZMod (reducedModulus A q)) hh]
    exact kloostermanUnitSum_reduced_le hWeil hq hsq (-h)


/-! **Weighted region**: discrete partial summation with reciprocal
weights, an explicit consequence of the preceding centered interval bound. -/

noncomputable def reciprocalNatWeight (Y i : ℕ) : ℂ :=
  ((((Y + i : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)

/-- Discrete partial summation for reciprocal weights. A uniform bound C on
all initial partial sums over a consecutive interval starting at Y>0 gives
an explicit 2C/Y weighted bound. -/
theorem partialSummation_reciprocal_weight_le
    (Y L : ℕ) (hY : 0 < Y) (c : ℕ → ℂ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hprefix : ∀ k ≤ L,
      ‖∑ j ∈ Finset.range k, c j‖ ≤ C) :
    ‖∑ j ∈ Finset.range L,
        c j * reciprocalNatWeight Y j‖ ≤
      2 * C / Y := by
  let r : ℕ → ℝ := fun i => (((Y + i : ℕ) : ℝ)⁻¹)
  let w : ℕ → ℂ := fun i => (r i : ℂ)
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hr_nonneg : ∀ i, 0 ≤ r i := by
    intro i
    dsimp [r]
    positivity
  have hr_mono : ∀ i, r (i + 1) ≤ r i := by
    intro i
    dsimp [r]
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by norm_num)
  have hw_norm : ∀ i, ‖w i‖ = r i := by
    intro i
    dsimp [w]
    exact Complex.norm_of_nonneg (hr_nonneg i)
  have hdiff_norm : ∀ i, ‖w (i + 1) - w i‖ = r i - r (i + 1) := by
    intro i
    dsimp [w]
    have hneg :
        ((r (i + 1) : ℂ) - (r i : ℂ)) =
          -((r i - r (i + 1) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hneg, norm_neg]
    exact Complex.norm_of_nonneg (sub_nonneg.mpr (hr_mono i))
  have hr0 : r 0 = ((Y : ℝ)⁻¹) := by
    dsimp [r]
  have hr_le_r0 : ∀ i, r i ≤ r 0 := by
    intro i
    dsimp [r]
    exact (inv_le_inv₀ (by positivity) hYreal).2 (by norm_num)
  have hparts := Finset.sum_range_by_parts' c w L
  simp only [smul_eq_mul] at hparts
  have hboundary :
      ‖(∑ i ∈ Finset.range L, c i) * w (L - 1)‖ ≤
        C * r 0 := by
    rw [norm_mul, hw_norm]
    exact mul_le_mul
      (hprefix L le_rfl)
      (hr_le_r0 (L - 1))
      (hr_nonneg _)
      hC0
  have htail :
      ‖∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ ≤
        C * r 0 := by
    calc
      ‖∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ ≤
        ∑ i ∈ Finset.range (L - 1),
          ‖(∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (L - 1),
          C * (r i - r (i + 1)) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul, hdiff_norm]
            apply mul_le_mul_of_nonneg_right
            · apply hprefix (i + 1)
              have hil : i < L - 1 := Finset.mem_range.mp hi
              omega
            · exact sub_nonneg.mpr (hr_mono i)
      _ = C * (r 0 - r (L - 1)) := by
            rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ C * r 0 := by
            have hlast : 0 ≤ r (L - 1) := hr_nonneg _
            nlinarith
  change
    ‖∑ j ∈ Finset.range L, c j * w j‖ ≤ 2 * C / Y
  rw [hparts]
  calc
    ‖(∑ i ∈ Finset.range L, c i) * w (L - 1) -
        ∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ ≤
      ‖(∑ i ∈ Finset.range L, c i) * w (L - 1)‖ +
        ‖∑ i ∈ Finset.range (L - 1),
          (∑ j ∈ Finset.range (i + 1), c j) *
            (w (i + 1) - w i)‖ := norm_sub_le _ _
    _ ≤ C * r 0 + C * r 0 := add_le_add hboundary htail
    _ = 2 * C / Y := by
          rw [hr0]
          field_simp [hYreal.ne']
          ring


noncomputable def weightedCenteredIntervalSum
    (N : ℕ) [NeZero N] (a x : ZMod N) (Y L : ℕ) : ℂ :=
  ∑ j ∈ Finset.range L,
    centeredReciprocalPhase N a (x + (j : ZMod N)) *
      reciprocalNatWeight Y j

/-- Partial summation applied to the centered reduced-modulus completion.
The interval length remains unrestricted. -/
theorem weightedCenteredReducedIntervalSum_le
    (hWeil : PrimeNondegenerateWeil)
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q))
    (Y L : ℕ) (hY : 0 < Y) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖weightedCenteredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x Y L‖ ≤
      2 *
        (((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
            Real.sqrt (reducedModulus A q)) *
          (1 + Real.log (reducedModulus A q))) / Y := by
  let : NeZero (reducedModulus A q) :=
    ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
  unfold weightedCenteredIntervalSum
  apply partialSummation_reciprocal_weight_le
    (Y := Y) (L := L)
    (c := fun j =>
      centeredReciprocalPhase
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        (x + (j : ZMod (reducedModulus A q))))
    hY
  · positivity
  · intro k hk
    exact centeredReducedIntervalSum_le hWeil hq hsq x k

end KloostermanWeil
