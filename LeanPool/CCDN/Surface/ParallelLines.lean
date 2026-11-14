/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.IntegralAffineLine
public import LeanPool.CCDN.Surface.TransversePlane
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Plane.Bezout
import LeanPool.CCDN.Surface.DirectionalDerivative
import LeanPool.CCDN.Surface.TopFormBadPrimes

/-! A transverse plane injects distinct parallel lines on a surface into
the common zeros of two proper plane equations. The second equation will
be the directional derivative. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma planeDirectionMatrix_mulVec (b c v w : Fin 3 → ℚ) (i : Fin 3) :
    (planeDirectionMatrix b c v).mulVec w i = b i * w 0 + c i * w 1 + v i * w 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, planeDirectionMatrix]
  ring

/-- Every line in the prescribed direction meets a transverse plane. -/
private theorem exists_parallel_line_plane_intersection (a b c v x : Fin 3 → ℚ)
    (hdet : (planeDirectionMatrix b c v).det ≠ 0) :
    ∃ (z : Fin 2 → ℚ) (t : ℚ),
      (fun i => a i + b i * z 0 + c i * z 1) = x + t • v := by
  have hunit : IsUnit (planeDirectionMatrix b c v) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit (x - a)
  refine ⟨![w 0,w 1], -w 2, ?_⟩
  funext i
  have hi := congrFun hw i
  rw [planeDirectionMatrix_mulVec] at hi
  simp only [Pi.sub_apply] at hi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  linarith

/-- Distinct parallel lines have distinct intersections with any
transverse plane. The index family is arbitrary but its line sets are injective. -/
private theorem surface_parallel_line_family_card_le_of_second_equation
    {ι : Type*} [Fintype ι]
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree)
    (v : Fin 3 → ℚ) (hv : v ≠ 0) (x : ι → RatPoint 3)
    (hinj : Function.Injective (fun i => rationalAffineLine (x i) v))
    (g : MvPolynomial (Fin 3) ℚ) (hg : g ≠ 0) (hgdeg : g.totalDegree < f.totalDegree)
    (hxf : ∀ i (t : ℚ), eval (x i + t • v) (map (Int.castRingHom ℚ) f) = 0)
    (hxg : ∀ i (t : ℚ), eval (x i + t • v) g = 0) :
    Fintype.card ι ≤ f.totalDegree * g.totalDegree := by
  classical
  obtain ⟨a,b,c,hdet,hF,hFd,hG⟩ := exists_surface_transverse_plane f hir hd v hv g hg
  have hex (i : ι) := exists_parallel_line_plane_intersection a b c v (x i) hdet
  choose z t hzt using hex
  have hz : Function.Injective z := by
    intro i j he
    apply hinj
    calc
      rationalAffineLine (x i) v = rationalAffineLine (x i + t i • v) v :=
        (rationalAffineLine_shift_base _ _ _).symm
      _ = rationalAffineLine (x j + t j • v) v := by rw [← hzt i, ← hzt j, he]
      _ = rationalAffineLine (x j) v := rationalAffineLine_shift_base _ _ _
  have hFG : ¬ affinePlaneMap a b c (map (Int.castRingHom ℚ) f) ∣ affinePlaneMap a b c g := by
    rintro ⟨q,hq⟩
    have hq0 : q ≠ 0 := by
      intro hz
      exact hG (by rw [hq, hz, mul_zero])
    have hh : f.totalDegree ≤ (affinePlaneMap a b c g).totalDegree := by
      rw [hq, totalDegree_mul_of_isDomain hF.ne_zero hq0, hFd]
      omega
    exact (not_le_of_gt hgdeg) (hh.trans (affinePlaneMap_totalDegree_le a b c g))
  have hcount := plane_common_zeros_card_le
    (affinePlaneMap a b c (map (Int.castRingHom ℚ) f)) (affinePlaneMap a b c g)
    hF hFG z hz
    (fun i => by rw [affinePlaneMap_eval, hzt i]; exact hxf i (t i))
    (fun i => by rw [affinePlaneMap_eval, hzt i]; exact hxg i (t i))
  rw [hFd] at hcount
  exact hcount.trans (Nat.mul_le_mul_left _ (affinePlaneMap_totalDegree_le a b c g))

/-- A finite set of line sets has no duplicate lines; its cardinality
is therefore controlled by the same proper plane intersection. -/
private theorem surface_parallel_lines_card_le_of_second_equation
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree)
    (v : Fin 3 → ℚ) (hv : v ≠ 0)
    (S : Finset (Set (RatPoint 3)))
    (hlines : ∀ L ∈ S, ∃ a, L = rationalAffineLine a v)
    (g : MvPolynomial (Fin 3) ℚ) (hg : g ≠ 0) (hgdeg : g.totalDegree < f.totalDegree)
    (hSf : ∀ L ∈ S, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f))
    (hSg : ∀ L ∈ S, L ⊆ zeroLocus g) :
    S.card ≤ f.totalDegree * g.totalDegree := by
  classical
  have hex (L : S) : ∃ a, L.val = rationalAffineLine a v := hlines L.val L.property
  choose a ha using hex
  have hinj : Function.Injective (fun L : S => rationalAffineLine (a L) v) := by
    intro L M h
    apply Subtype.ext
    exact (ha L).trans (h.trans (ha M).symm)
  have hh := surface_parallel_line_family_card_le_of_second_equation
    f hir hd v hv a hinj g hg hgdeg
    (fun L t => hSf L.val L.property (by rw [ha L]; exact ⟨t,rfl⟩))
    (fun L t => hSg L.val L.property (by rw [ha L]; exact ⟨t,rfl⟩))
  simpa only [Fintype.card_coe] using hh

/-- A surface with absolutely irreducible top form has at most d(d-1)
distinct lines in any prescribed nonzero rational direction. The directional
derivative and the transverse plane are constructed inside the proof. -/
theorem surface_parallel_lines_card_le
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : HasAbsIrreducibleTopForm f)
    (hd : 2 ≤ f.totalDegree)
    (v : RatPoint 3) (hv : v ≠ 0)
    (S : Finset (Set (RatPoint 3)))
    (hlines : ∀ L ∈ S, ∃ a, L = rationalAffineLine a v)
    (hSf : ∀ L ∈ S, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) :
    S.card ≤ f.totalDegree * (f.totalDegree - 1) := by
  let g := directionalDerivative v (map (Int.castRingHom ℚ) f)
  have hg : g ≠ 0 := surface_directionalDerivative_ne_zero f hir hd v hv
  have hgdeg : g.totalDegree ≤ f.totalDegree - 1 := by
    simpa only [rational_map_totalDegree] using
      directionalDerivative_totalDegree_le v (map (Int.castRingHom ℚ) f)
  have hh := surface_parallel_lines_card_le_of_second_equation f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f hir)
    (by omega) v hv S hlines g hg (by omega) hSf (by
      intro L hL
      obtain ⟨a, rfl⟩ := hlines L hL
      exact rationalAffineLine_contained_directionalDerivative a v
        (map (Int.castRingHom ℚ) f) (hSf _ hL))
  exact hh.trans (Nat.mul_le_mul_left _ hgdeg)

end
end CCDN
