/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousTranslation
public import LeanPool.CCDN.Algebra.ScaledHomogenization
public import LeanPool.CCDN.AuxiliaryPolynomial.Nonmultiple
import LeanPool.CCDN.AuxiliaryPolynomial.ScaledAuxiliaryCount

/-! Polynomial coordinates for a translated scaled model, with exact point
transport and transport of an auxiliary nonmultiple back to the original slice. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The integer polynomial coordinate change `(h, x₁ - a₁ h, …, xₙ - aₙ h)` from affine
coordinates to the coordinates of the translated scaled projective model. -/
def scaledModelCoordinates {n : ℕ} (h : ℤ) (a : Fin n → ℤ) :
    Fin (n + 1) → MvPolynomial (Fin n) ℤ :=
  Fin.cons (C h) (fun j => X j - C (a j * h))

private lemma scaledModelCoordinates_eval {n : ℕ} (h : ℤ) (a z : Fin n → ℤ) :
    (fun j => eval z (scaledModelCoordinates h a j)) =
      Fin.cons h (fun j => z j - a j * h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [scaledModelCoordinates]

/-- The translated scaled homogenization of `f`, evaluated at the scaled model coordinates of `z`,
equals `h ^ deg f * f(z)`. -/
lemma scaledModelCoordinates_model_eval {n : ℕ} (h : ℤ) (a z : Fin n → ℤ)
    (f : MvPolynomial (Fin n) ℤ) :
    eval (fun j => eval z (scaledModelCoordinates h a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) =
        h ^ f.totalDegree * eval z f := by
  rw [scaledModelCoordinates_eval, homogeneousTranslation_eval]
  simp only [Fin.cons_zero, Fin.cons_succ, sub_add_cancel]
  exact scaledHomogenize_eval _ _ le_rfl _

/-- For `0 ≤ h ≤ B`, translation parameters `0 ≤ a j ≤ d` and `z` in the box of size `B ≥ 1`, all
scaled model coordinates of `z` have absolute value at most `(d + 1) * B`. -/
lemma scaledModelCoordinates_box {n : ℕ} {B : ℝ} {d : ℕ} {h : ℤ}
    (hB : 1 ≤ B) (hh : 0 ≤ h) (hhB : (h : ℝ) ≤ B)
    (a z : Fin n → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    (hz : InBox z B) (j : Fin (n + 1)) :
    |(eval z (scaledModelCoordinates h a j) : ℝ)| ≤ ((d : ℝ) + 1) * B := by
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have hdR : (0 : ℝ) ≤ d := by positivity
  have he := congrFun (scaledModelCoordinates_eval h a z) j
  rw [he]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cons_zero, abs_of_nonneg hhR]
    nlinarith
  · simp only [Fin.cons_succ, Int.cast_sub, Int.cast_mul]
    have ha0 : (0 : ℝ) ≤ a k := by exact_mod_cast (ha k).1
    have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
    have hab : (a k : ℝ) * h ≤ d * B := mul_le_mul had hhB hhR hdR
    calc
      |(z k : ℝ) - (a k : ℝ) * h| ≤ |(z k : ℝ)| + |(a k : ℝ) * h| := abs_sub _ _
      _ = |(z k : ℝ)| + (a k : ℝ) * h := by rw [abs_of_nonneg (mul_nonneg ha0 hhR)]
      _ ≤ ((d : ℝ) + 1) * B := by nlinarith [hz k]

/-- A homogeneous auxiliary polynomial `g` of degree `M` not divisible by the translated scaled
homogenization of `f` transports to a homogeneous `g'` of degree `M` not divisible by the scaled
homogenization of `f`, with `g'(h, z)` equal to `g` at the scaled model coordinates of `z`. -/
lemma scaledModelCoordinates_auxiliary_transport {n M : ℕ}
    (h : ℤ) (a : Fin n → ℤ) (f : MvPolynomial (Fin n) ℤ)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f) ∣ g) :
    ∃ g' : MvPolynomial (Fin (n + 1)) ℤ, g'.IsHomogeneous M ∧
      (∀ z, eval (Fin.cons h z) g' = eval (fun j => eval z (scaledModelCoordinates h a j)) g) ∧
      ¬ scaledHomogenize f.totalDegree h f ∣ g' := by
  refine ⟨homogeneousTranslation ℤ (-a) g, homogeneousTranslation_homogeneous _ hg, ?_, ?_⟩
  · intro z
    rw [homogeneousTranslation_eval, scaledModelCoordinates_eval]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.neg_apply, neg_mul, sub_eq_add_neg]
  · intro hdiv
    apply hnd
    have he := map_dvd (homogeneousTranslation ℤ a).toRingHom hdiv
    change homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f) ∣
      homogeneousTranslation ℤ a ((homogeneousTranslation ℤ a).symm g) at he
    simpa only [AlgEquiv.apply_symm_apply] using he

/-- A nonmultiple on the translated scaled model counts the original
integer points. The bound uses only the auxiliary degree and original degree. -/
theorem scaled_positioned_points_card_le {M t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f))
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (a : Fin 2 → ℤ) (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0) (g : MvPolynomial (Fin 3) ℤ)
    (hg : IsPointAuxiliary (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree (p : ℤ) f))
      g M (fun i j => eval (z i) (scaledModelCoordinates (p : ℤ) a j))) :
    t ≤ f.totalDegree * M := by
  obtain ⟨g', hg', he, hnd'⟩ := scaledModelCoordinates_auxiliary_transport (p : ℤ) a f g
    hg.isHomogeneous hg.not_dvd
  exact scaled_plane_points_card_le_auxiliary_degree f hprim hir hp hp0 g' hg' hnd' z hinj hz
    (fun i => (he (z i)).trans (hg.eval_eq_zero i))

end
end CCDN
