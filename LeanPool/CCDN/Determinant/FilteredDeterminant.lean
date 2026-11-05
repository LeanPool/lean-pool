/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.SingularTangent
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial
import LeanPool.CCDN.Determinant.LocalDeterminant
import LeanPool.CCDN.Determinant.ModularOriginGenerators
import LeanPool.CCDN.Determinant.SingularApproximation
import LeanPool.CCDN.ForMathlib.Matrix

/-! Local determinant divisibility in arbitrary dimension. The exponent is
computed from the cumulative dimensions of the origin-adic layers. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The sum of the deficits below successive weights. For a graded profile
this is a lower bound for the sum of the first s weights, with multiplicity. -/
def filtrationExponent (r : ℕ → ℕ) (s : ℕ) : ℕ :=
  Finset.univ.sum fun k : Fin s => s - (Finset.univ.sum fun j : Fin (k.val + 1) => r j.val)

/-- Layer-cake inequality with an arbitrary cutoff `K`: counting, for each
`k < K`, the weights exceeding `k` never exceeds the total weight. -/
lemma sum_weight_tail_counts_le {s : ℕ} (w : Fin s → ℕ) (K : ℕ) :
    (∑ k : Fin K, (Finset.univ.filter fun i => k.val < w i).card) ≤ ∑ i, w i := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hcard : (Finset.univ.filter fun k : Fin K => k.val < w i).card ≤ w i := by
    rw [Fin.card_filter_val_lt]
    exact min_le_right _ _
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcard

/-- Distinct generators of weight at most k inject into all generators in
layers zero through k, independently of the precision used to truncate them. -/
lemma low_weight_card_le {s N : ℕ} (r : ℕ → ℕ)
    (t : Fin s ↪ ((j : Fin N) × Fin (r j.val))) (k : ℕ) :
    (Finset.univ.filter fun i => (t i).1.val ≤ k).card ≤
      ∑ j : Fin (k + 1), r j.val := by
  classical
  let φ : {i : Fin s // (t i).1.val ≤ k} → ((j : Fin (k + 1)) × Fin (r j.val)) :=
    fun i => ⟨⟨(t i.val).1.val, by omega⟩, (t i.val).2⟩
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    apply t.injective
    have he := congrArg
      (fun v : (j : Fin (k + 1)) × Fin (r j.val) =>
        (⟨v.1.val, v.2⟩ : (j : ℕ) × Fin (r j))) h
    let forget : ((j : Fin N) × Fin (r j.val)) → ((j : ℕ) × Fin (r j)) :=
      Sigma.map Fin.val (fun _ j => j)
    have hinj : Function.Injective forget :=
      Fin.val_injective.sigma_map (fun _ => Function.injective_id)
    exact hinj he
  have hc := Fintype.card_le_of_injective φ hφ
  simpa only [Fintype.card_subtype, Fintype.card_sigma, Fintype.card_fin] using hc

private lemma filtrationExponent_le_weights {s N : ℕ} (r : ℕ → ℕ)
    (t : Fin s ↪ ((j : Fin N) × Fin (r j.val))) :
    filtrationExponent r s ≤ ∑ i, (t i).1.val := by
  classical
  apply le_trans ?_ (sum_weight_tail_counts_le (fun i => (t i).1.val) s)
  unfold filtrationExponent
  apply Finset.sum_le_sum
  intro k _
  have hlow := low_weight_card_le r t k.val
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin s))) (p := fun i => (t i).1.val ≤ k.val)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hpart
  omega

/-- Cauchy--Binet for a finite set of generators indexed in any way. -/
theorem pow_dvd_det_of_weighted_factorization_fintype {R ι : Type*} [CommRing R]
    [Fintype ι] {s : ℕ}
    (U : Matrix (Fin s) ι R) (V : Matrix ι (Fin s) R)
    (p : R) (weight : ι → ℕ) (e : ℕ)
    (hV : ∀ i j, p ^ weight i ∣ V i j)
    (he : ∀ t : Fin s ↪ ι, e ≤ ∑ i, weight (t i)) :
    p ^ e ∣ (U * V).det := by
  classical
  let a := (Fintype.equivFin ι).symm
  let U' := U.submatrix id a
  let V' := V.submatrix a id
  have hprod : U * V = U' * V' := by
    ext i j
    exact (Equiv.sum_comp a (fun z => U i z * V z j)).symm
  rw [hprod]
  apply pow_dvd_det_of_weighted_factorization U' V' p (fun z => weight (a z)) e
    (fun i j => hV (a i) j)
  intro t
  exact he (t.toEmbedding.trans a.toEmbedding)

/-- A homogeneous local generating family gives a determinant divisor
at any precision and in any dimension. -/
theorem origin_filtration_pow_dvd_det_mod {p n s e : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (x : Fin s → Fin (n + 1) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j)
    (he : e ≤ filtrationExponent
      (fun k => Module.finrank (ZMod p) (originLayer (map (Int.castRingHom (ZMod p)) f) k)) s)
    (hfx : ∀ i, (p : ℤ) ^ e ∣ eval (x i) f)
    (F : Fin s → MvPolynomial (Fin (n + 1)) ℤ) :
    (p : ℤ) ^ e ∣ (Matrix.of fun i j => eval (x i) (F j)).det := by
  classical
  obtain ⟨r, g, hr, hg, hrep⟩ := exists_integer_hypersurface_generators (p := p) f
  have hr' : r = fun k => Module.finrank (ZMod p)
      (originLayer (map (Int.castRingHom (ZMod p)) f) k) := funext hr
  rw [← hr'] at he
  let N := e
  choose c hc using fun j => integer_generators_approximate_mod f r g (hrep N) (F j)
  have hdiv (i : Fin s) (z : (k : Fin N) × Fin (r k.val)) :
      (p : ℤ) ^ z.1.val ∣ eval (x i) (g z.1.val z.2) :=
    origin_power_eval_dvd (p : ℤ) (x i) (hx i) (homogeneous_mem_origin_power (hg _ _))
  choose U₀ hU using hdiv
  let U : Matrix (Fin s) ((k : Fin N) × Fin (r k.val)) ℤ := U₀
  let V : Matrix ((k : Fin N) × Fin (r k.val)) (Fin s) ℤ :=
    fun z j => (p : ℤ) ^ z.1.val * c j z.1 z.2
  have hdet : (p : ℤ) ^ N ∣ (U * V).det :=
    pow_dvd_det_of_weighted_factorization_fintype U V (p : ℤ) (fun z => z.1.val) N
      (fun _ _ => dvd_mul_right _ _) (fun t => he.trans (filtrationExponent_le_weights r t))
  have hprod (i j : Fin s) : (U * V) i j =
      ∑ k : Fin N, ∑ l, c j k l * eval (x i) (g k.val l) := by
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hU i ⟨k, l⟩]
    dsimp only [U, V]
    ring
  have hd := Matrix.dvd_det_sub_det_of_dvd_sub (Matrix.of fun i j => eval (x i) (F j))
    (U * V) ((p : ℤ) ^ N) (fun i j => by
      rw [Matrix.of_apply, hprod]
      exact hc j (x i) (hfx i) (hx i))
  simpa only [sub_add_cancel] using dvd_add hd hdet

end
end CCDN
