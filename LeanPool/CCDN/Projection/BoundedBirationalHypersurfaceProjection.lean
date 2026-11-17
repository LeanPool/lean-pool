/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Projection.BoundedIntegerNormalization
public import LeanPool.CCDN.Projection.CurvePrimitivePair
public import LeanPool.CCDN.Projection.ImageFractionField
import LeanPool.CCDN.Projection.LeadingCoordinateExtension
import LeanPool.CCDN.Projection.LinearParameterPrimitive

/-! A bounded integer linear finite birational projection of a
homogeneous prime quotient to a hypersurface of exactly the same degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient bound for the birational hypersurface projection in `n` variables and degree
`d`: the maximum of the normalization height and `(n * d ^ 2 + 1) ^ n`, which bounds the moment
row. -/
def integerBirationalProjectionHeight (n d : ℕ) : ℕ :=
  max (integerNormalizationHeight n d) ((n * d ^ 2 + 1) ^ n)

/-- The birational projection height is at least one. -/
lemma integerBirationalProjectionHeight_one_le (n d : ℕ) :
    1 ≤ integerBirationalProjectionHeight n d :=
  (integerNormalizationHeight_pos n d).trans_le (le_max_left _ _)

/-- Prepending the integer moment row `(t ^ j)_j` to integer rows realizes the moment
coordinate as the leading linear form. -/
theorem integerLinearForm_moment_cons {m n : ℕ} (t : ℕ) (a : Fin (m + 1) → Fin n → ℤ) :
    (fun i => integerLinearForm
      ((Fin.cases (fun j => (t : ℤ) ^ j.val) a : Fin (m + 2) → Fin n → ℤ) i)) =
      Fin.cases (momentCoordinate ℚ n t) (fun i => integerLinearForm (a i)) := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  simp only [Fin.cases_zero, integerLinearForm, linearForm, momentCoordinate, Int.cast_pow,
    Int.cast_natCast]

/-- Prepending the moment row with parameter `t ≤ n d²` to rows bounded by the normalization
height keeps every entry within the birational projection height. -/
theorem moment_cons_abs_le_integerBirationalProjectionHeight {m n d t : ℕ}
    (ht : t ≤ n * d ^ 2) (a : Fin (m + 1) → Fin n → ℤ)
    (ha : ∀ i j, |a i j| ≤ integerNormalizationHeight n d) (i : Fin (m + 2)) (j : Fin n) :
    |(Fin.cases (fun j => (t : ℤ) ^ j.val) a : Fin (m + 2) → Fin n → ℤ) i j| ≤
      integerBirationalProjectionHeight n d := by
  refine Fin.cases ?_ (fun s => ?_) i
  · change |(t : ℤ) ^ j.val| ≤ _
    rw [abs_pow, abs_of_nonneg (Nat.cast_nonneg t)]
    have hp : t ^ j.val ≤ (n * d ^ 2 + 1) ^ n := by
      calc
        _ ≤ (n * d ^ 2 + 1) ^ j.val :=
          Nat.pow_le_pow_left (ht.trans (Nat.le_succ _)) _
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt j.isLt)
    exact_mod_cast hp.trans (le_max_right (integerNormalizationHeight n d) _)
  · exact (ha s j).trans (by
      exact_mod_cast le_max_left (integerNormalizationHeight n d) ((n * d ^ 2 + 1) ^ n))

/-- A bounded primitive augmentation of the constructed normalization
produces a homogeneous irreducible equation of exactly the original degree. -/
private theorem exists_bounded_birational_hypersurface_projection
    (m k : ℕ) (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin (m + 1 + k) → ℤ) (f : MvPolynomial (Fin (m + 2)) ℚ),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + 1 + k) d) ∧
      IsNoetherNormalization I (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      f.IsHomogeneous d ∧ f.totalDegree = d := by
  classical
  let n := m + 1 + k
  let F := FractionRing (MvPolynomial (Fin n) ℚ ⧸ I)
  obtain ⟨a, ha, hinta, hinja⟩ := exists_bounded_integer_normalization m k I d hdimdeg
  obtain ⟨t, ht, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I _ (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
  let b : Fin (m + 2) → Fin n → ℤ := Fin.cases (fun j => (t : ℤ) ^ j.val) a
  let l : Fin (m + 2) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (b i)
  have hfield' : IntermediateField.adjoin ℚ (Set.range (fun i =>
      algebraMap _ F ((Ideal.Quotient.mk I) (l i)))) = ⊤ := by
    have hl : l = Fin.cases (momentCoordinate ℚ n t) (fun i => integerLinearForm (a i)) :=
      integerLinearForm_moment_cons t a
    rwa [hl]
  obtain ⟨f, hf, hfhom, hfdeg, _, hker⟩ := exists_homogeneous_extended_projection_equation
    (F := F) I hI l (fun i => linearForm_isHomogeneous _) hinta hinja hfield' d
    hdimdeg
  exact ⟨b, f, moment_cons_abs_le_integerBirationalProjectionHeight ht a ha, ⟨hinta, hinja⟩,
    ⟨⟨hfield', hf, hker⟩, projectionCoordinateMap_isIntegral_of_tail I l hinta⟩, hfhom, hfdeg⟩

/-- A homogeneous prime ideal in `n ≥ m + 1` variables, of projective dimension `m` and
degree `d`, has a bounded integral linear projection to `m + 2` coordinates: the integer
coefficients are bounded by `integerBirationalProjectionHeight n d`, the projection is integral
and birational, and its kernel is generated by an irreducible homogeneous form of degree `d`.
The number of variables is arbitrary, not written as `m + 1 + k`. -/
theorem exists_bounded_birational_hypersurface_projection_of_le
    (m n : ℕ) (hmn : m + 1 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin n → ℤ) (f : MvPolynomial (Fin (m + 2)) ℚ),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      IsNoetherNormalization I (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      f.IsHomogeneous d ∧ f.totalDegree = d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact exists_bounded_birational_hypersurface_projection m k I hI d hdimdeg

section

/-! The constructed projection has a coefficient bound polynomial in
the degree, with exponent and constant depending only on ambient
dimension. -/

/-- The constant `n! * 2 ^ n + (n + 1) ^ n` in the polynomial bound on the birational projection
height in `n` variables. -/
def birationalProjectionHeightConstant (n : ℕ) : ℕ :=
  n.factorial * 2 ^ n + (n + 1) ^ n

/-- The birational projection height constant is positive. -/
lemma birationalProjectionHeightConstant_pos (n : ℕ) :
    0 < birationalProjectionHeightConstant n := by
  dsimp [birationalProjectionHeightConstant]
  positivity

/-- For degree `d ≥ 1`, the birational projection height in `n` variables is at most
`birationalProjectionHeightConstant n * d ^ (2 * n)`. -/
theorem integerBirationalProjectionHeight_le (n d : ℕ) (hd : 1 ≤ d) :
    integerBirationalProjectionHeight n d ≤
      birationalProjectionHeightConstant n * d ^ (2 * n) := by
  have hpow : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
  have hfirst : integerNormalizationHeight n d ≤
      (n.factorial * 2 ^ n) * d ^ (2 * n) := by
    dsimp only [integerNormalizationHeight]
    calc
      _ ≤ n.factorial * (2 * d) ^ n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n.factorial * 2 ^ n) * d ^ n := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hd (by omega))
  have hsecond : (n * d ^ 2 + 1) ^ n ≤ (n + 1) ^ n * d ^ (2 * n) := by
    calc
      _ ≤ ((n + 1) * d ^ 2) ^ n :=
        Nat.pow_le_pow_left (by nlinarith) _
      _ = _ := by rw [Nat.mul_pow, ← pow_mul]
  apply max_le
  · exact hfirst.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · exact hsecond.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

end

end
end CCDN
