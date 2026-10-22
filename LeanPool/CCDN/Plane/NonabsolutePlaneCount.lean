/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
import LeanPool.CCDN.Algebra.PolynomialLinearDescent
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Plane.Bezout
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! Irreducible base-field plane curves that split over an extension have at
most d² base-field points. The proof uses linear coefficient descent and
Bézout. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma plane_extension_section_card_le {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι]
    (f : MvPolynomial (Fin 2) k) (hf : Irreducible f)
    (g : MvPolynomial (Fin 2) K) (hg : g ≠ 0) (hdeg : g.totalDegree < f.totalDegree)
    (z : ι → Fin 2 → k) (hinj : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (algebraMap k K ∘ z i) g = 0) :
    Fintype.card ι ≤ f.totalDegree * g.totalDegree := by
  classical
  obtain ⟨g₀, hg₀, hdeg₀, hzero⟩ := exists_nonzero_polynomial_linear_descent (k := k) g hg
  have hnd : ¬ f ∣ g₀ := by
    intro hdiv
    have h := totalDegree_le_of_dvd_of_isDomain hdiv hg₀
    omega
  exact (plane_common_zeros_card_le f g₀ hf hnd z hinj hzf (fun i => hzero (z i) (hzg i))).trans
    (Nat.mul_le_mul_left _ hdeg₀)

private lemma plane_points_card_le_of_extension_factorization {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι]
    (f : MvPolynomial (Fin 2) k) (hf : Irreducible f)
    (g h : MvPolynomial (Fin 2) K) (hg : g ≠ 0) (hh : h ≠ 0)
    (hgd : 0 < g.totalDegree) (hhd : 0 < h.totalDegree)
    (hfac : MvPolynomial.map (algebraMap k K) f = g * h)
    (z : ι → Fin 2 → k) (hinj : Function.Injective z) (hz : ∀ i, eval (z i) f = 0) :
    Fintype.card ι ≤ f.totalDegree ^ 2 := by
  classical
  have hdegree : g.totalDegree + h.totalDegree = f.totalDegree := by
    have hm : (MvPolynomial.map (algebraMap k K) f).totalDegree = f.totalDegree :=
        totalDegree_map_of_injective (algebraMap k K).injective _
    rw [hfac, totalDegree_mul_of_isDomain hg hh] at hm
    exact hm
  let S := Finset.univ.filter (fun i : ι => eval (algebraMap k K ∘ z i) g = 0)
  let T := Finset.univ.filter (fun i : ι => ¬ eval (algebraMap k K ∘ z i) g = 0)
  have hs := plane_extension_section_card_le f hf g hg (by omega)
    (fun i : S => z i.val) (hinj.comp Subtype.val_injective)
    (fun i => hz i.val) (fun i => (Finset.mem_filter.mp i.property).2)
  have ht := plane_extension_section_card_le f hf h hh (by omega)
    (fun i : T => z i.val) (hinj.comp Subtype.val_injective)
    (fun i => hz i.val) (by
      intro i
      have he := congrArg (algebraMap k K) (hz i.val)
      rw [map_eval, hfac, eval_mul, map_zero] at he
      exact (mul_eq_zero.mp he).resolve_left (Finset.mem_filter.mp i.property).2)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun i : ι => eval (algebraMap k K ∘ z i) g = 0)
  simp only [Fintype.card_coe] at hs ht
  change S.card + T.card = Finset.univ.card at hsum
  rw [Finset.card_univ] at hsum
  calc
    Fintype.card ι = S.card + T.card := hsum.symm
    _ ≤ f.totalDegree * g.totalDegree + f.totalDegree * h.totalDegree := Nat.add_le_add hs ht
    _ = f.totalDegree ^ 2 := by rw [← Nat.mul_add, hdegree, pow_two]

/-- Splitting over any extension, Galois or not, gives the d² bound on
base-field points. -/
theorem nonabsolute_plane_points_card_le {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι]
    (f : MvPolynomial (Fin 2) k) (hf : Irreducible f) (hd : 0 < f.totalDegree)
    (hred : ¬ Irreducible (MvPolynomial.map (algebraMap k K) f))
    (z : ι → Fin 2 → k) (hinj : Function.Injective z) (hz : ∀ i, eval (z i) f = 0) :
    Fintype.card ι ≤ f.totalDegree ^ 2 := by
  classical
  have hmap0 : MvPolynomial.map (algebraMap k K) f ≠ 0 := by
    exact fun he => hf.ne_zero
      ((map_injective (algebraMap k K) (algebraMap k K).injective) (by simpa using he))
  have hmapu : ¬ IsUnit (MvPolynomial.map (algebraMap k K) f) := by
    intro hu
    have he := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [totalDegree_map_of_injective (algebraMap k K).injective] at he
    exact (Nat.ne_of_gt hd) he
  obtain ⟨g, h, hgu, hhu, hfac⟩ := (irreducible_or_factor hmapu).resolve_left hred
  have hg : g ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hh : h ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  exact plane_points_card_le_of_extension_factorization f hf g h hg hh
    (totalDegree_pos_of_ne_zero_of_not_isUnit hg hgu)
    (totalDegree_pos_of_ne_zero_of_not_isUnit hh hhu) hfac z hinj hz

end
end CCDN
