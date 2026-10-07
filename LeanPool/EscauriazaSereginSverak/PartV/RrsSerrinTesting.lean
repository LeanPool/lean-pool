/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinLerayHopf

/-!
# Testing a Leray–Hopf solution with an `L⁵` solution

The form of Robinson–Rodrigo–Sadowski, Lemma 8.18 (printed pp. 173–174), used in
`lem:pv-serrin-uniqueness` at the exponents `(5, 5)`: for a Leray–Hopf solution
`u ∈ L⁵(Q_T)` and any Leray–Hopf solution `v`, the nonlinear integrand
`|v| |∇v| |u|` of the testing identity is integrable on `Q_T`, and the
cross-testing identity (their (8.11) after `ε → 0`, combined with the weak
equation of `v` tested with `u`) holds at almost every time. The identity is
obtained by mollifying the slices, without the positive-time strong regularity
of their Theorem 8.17.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `RRS Serrin testing estimate`, in the form used by `lem:pv-serrin-uniqueness`:
for Leray–Hopf solutions `u` and `v` on `ℝ³ × [0, T]` with data `a` and `b`, with
`u ∈ L⁵(Q_T)`, the integrand `|v| |∇v| |u|` is integrable on `Q_T`, and at almost
every time `t` the slice pairing satisfies the cross-testing identity
`(v(t), u(t)) - (b, a) = -∫∫_{Q_t} (u · (v · ∇) v + ∇u : ∇v)
  - ∫∫_{Q_t} (v · (u · ∇) u + ∇v : ∇u)`. -/
theorem rrs_serrin_testing {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    (hU : IsLerayHopfSolution T a u Du) (hV : IsLerayHopfSolution T b v Dv)
    (hu5 : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    Integrable (fun z => ‖v z‖ * ‖Dv z‖ * ‖u z‖)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, b x k * a x k) =
        (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, u q k * ∑ j : Fin 3, v q j * Dv q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Dv q k j) +
        (-(∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, v q k * ∑ j : Fin 3, u q j * Du q k j)
          - ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv q k j * Du q k j) := by
  obtain ⟨pu, hUw⟩ := serrinWeak_of_lerayHopf hU
  obtain ⟨pv, hVw⟩ := serrinWeak_of_lerayHopf hV
  have hv103 := (lerayHopf_memLp_tenThirds hV).1
  refine ⟨?_, serrin_cross_identity hUw hVw hu5 hv103⟩
  have hDv2 : MemLp Dv (ENNReal.ofReal 2)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rw [ENNReal.ofReal_ofNat]
    exact serrinWeak_gradient_memLp_two hVw
  have H1 : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3)) (ENNReal.ofReal 2)
      (ENNReal.ofReal (5 / 4)) :=
    serrin_holder_ofReal3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have H2 : ENNReal.HolderTriple (ENNReal.ofReal (5 / 4)) (ENNReal.ofReal 5) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have h1 : MemLp (fun z => ‖v z‖ * ‖Dv z‖) (ENNReal.ofReal (5 / 4))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    hv103.norm.mul hDv2.norm
  exact memLp_one_iff_integrable.mp (h1.mul hu5.norm)

end ESS

end
