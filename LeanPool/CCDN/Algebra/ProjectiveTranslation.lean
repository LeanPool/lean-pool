/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousTranslation
public import LeanPool.CCDN.Height.ProjectiveBox

/-! Bounded integral shears act on all projective representatives, preserve
primitivity, and preserve distinctness of their projective classes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The shear of a point `x` by `a`, keeping `x 0` and sending `x (j + 1)` to
`x (j + 1) + a j * x 0`; on the affine chart `x 0 = 1` it is the translation by `a`. -/
def homogeneousPointTranslation {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (x : Fin (n + 1) → R) : Fin (n + 1) → R :=
  Fin.cons (x 0) (fun j => x j.succ + a j * x 0)

/-- The shear by `-a` undoes the shear by `a`. -/
lemma homogeneousPointTranslation_inverse {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (x : Fin (n + 1) → R) :
    homogeneousPointTranslation (-a) (homogeneousPointTranslation a x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [homogeneousPointTranslation]

private lemma homogeneousPointTranslation_injective {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) : Function.Injective (homogeneousPointTranslation a) :=
  Function.LeftInverse.injective (homogeneousPointTranslation_inverse a)

/-- The shear of a nonzero point is nonzero. -/
lemma homogeneousPointTranslation_ne_zero {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) {x : Fin (n + 1) → R} (hx : x ≠ 0) :
    homogeneousPointTranslation a x ≠ 0 := by
  intro h
  apply hx
  apply homogeneousPointTranslation_injective a
  have hzero : homogeneousPointTranslation a 0 = 0 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [homogeneousPointTranslation]
  exact h.trans hzero.symm

private lemma homogeneousPointTranslation_smul {K : Type*} [Field K] {n : ℕ}
    (a : Fin n → K) (c : K) (x : Fin (n + 1) → K) :
    homogeneousPointTranslation a (c • x) = c • homogeneousPointTranslation a x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [homogeneousPointTranslation, Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
    ring

private lemma homogeneousPointTranslation_map {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (φ : R →+* S) (a : Fin n → R) (x : Fin (n + 1) → R) :
    φ ∘ homogeneousPointTranslation a x = homogeneousPointTranslation (φ ∘ a) (φ ∘ x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [homogeneousPointTranslation]

/-- An integral shear preserves the greatest common divisor of the coordinates of an integer
point; in particular it preserves primitivity. -/
lemma homogeneousPointTranslation_gcd {n : ℕ} (a : Fin n → ℤ)
    (x : Fin (n + 1) → ℤ) :
    Finset.univ.gcd (homogeneousPointTranslation a x) = Finset.univ.gcd x := by
  have hdiv (b : Fin n → ℤ) (y : Fin (n + 1) → ℤ) :
      Finset.univ.gcd y ∣ Finset.univ.gcd (homogeneousPointTranslation b y) := by
    apply Finset.dvd_gcd
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Finset.gcd_dvd (Finset.mem_univ 0)
    · exact dvd_add (Finset.gcd_dvd (Finset.mem_univ j.succ))
        (dvd_mul_of_dvd_right (Finset.gcd_dvd (Finset.mem_univ 0)) (b j))
  have hback := hdiv (-a) (homogeneousPointTranslation a x)
  rw [homogeneousPointTranslation_inverse] at hback
  apply dvd_antisymm_of_normalize_eq Finset.normalize_gcd Finset.normalize_gcd
    hback (hdiv a x)

/-- An integral shear preserves distinctness of projective classes: if the nonzero integer points
`z i` represent pairwise distinct points of projective space over `ℚ`, so do their shears. -/
lemma homogeneousPointTranslation_projective_injective {n t : ℕ}
    (a : Fin n → ℤ) (z : Fin t → IntPoint (n + 1)) (hz0 : ∀ i, z i ≠ 0)
    (hinj : Function.Injective (fun i => Projectivization.mk ℚ (rationalPoint (z i))
      (rationalPoint_ne_zero (hz0 i)))) :
    Function.Injective (fun i => Projectivization.mk ℚ
      (rationalPoint (homogeneousPointTranslation a (z i)))
      (rationalPoint_ne_zero (homogeneousPointTranslation_ne_zero a (hz0 i)))) := by
  intro i j he
  apply hinj
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp he
  apply (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mpr
  refine ⟨c, ?_⟩
  change (c : ℚ) • ((Int.castRingHom ℚ) ∘ homogeneousPointTranslation a (z j)) =
    (Int.castRingHom ℚ) ∘ homogeneousPointTranslation a (z i) at hc
  rw [homogeneousPointTranslation_map, homogeneousPointTranslation_map,
    ← homogeneousPointTranslation_smul] at hc
  exact homogeneousPointTranslation_injective _ hc

/-- If `z` lies in the box of radius `B ≥ 1` and every coordinate of `a` lies in `[0, d]`, then
the shear of `z` by `-a` lies in the box of radius `(d + 1) * B`. -/
lemma homogeneousPointTranslation_box {n d : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (a : Fin n → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    (z : IntPoint (n + 1)) (hz : InBox z B) (j : Fin (n + 1)) :
    |((homogeneousPointTranslation (-a) z j : ℤ) : ℝ)| ≤ ((d : ℝ) + 1) * B := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  refine Fin.cases ?_ (fun k => ?_) j
  · change |(z 0 : ℝ)| ≤ _
    nlinarith [hz 0]
  · change |((z k.succ + -a k * z 0 : ℤ) : ℝ)| ≤ _
    rw [Int.cast_add, Int.cast_mul, Int.cast_neg]
    have hak : |(a k : ℝ)| ≤ d := by
      rw [abs_of_nonneg (by exact_mod_cast (ha k).1)]
      exact_mod_cast (ha k).2
    calc
      _ ≤ |(z k.succ : ℝ)| + |-(a k : ℝ) * (z 0 : ℝ)| := abs_add_le _ _
      _ = |(z k.succ : ℝ)| + |(a k : ℝ)| * |(z 0 : ℝ)| := by rw [abs_mul, abs_neg]
      _ ≤ B + (d : ℝ) * B := by
          gcongr
          · exact hz _
          · exact hz _
      _ = _ := by ring

/-- The homogeneous translation commutes with coefficient maps: mapping the coefficients of the
homogeneous translation of `f` by `a` along `φ` gives the homogeneous translation of the mapped
polynomial by `φ ∘ a`. -/
lemma homogeneousTranslation_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    map φ (homogeneousTranslation R a f) =
      homogeneousTranslation S (φ ∘ a) (map φ f) := by
  change map φ (eval₂ C _ f) = eval₂ C _ (map φ f)
  rw [map_eval₂]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end
end CCDN
