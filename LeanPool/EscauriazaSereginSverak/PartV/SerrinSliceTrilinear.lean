/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinTrilinear

/-!
# Trilinear identities at a fixed time

For slices `u ∈ L² ∩ L⁵` and `v ∈ L² ∩ L^{10/3}` with square-integrable weak
gradients of vanishing trace, the self-transport form of `u` vanishes, and the
sum of the two convection pairings equals the relative convection form
`∑ₖ uₖ ∑ⱼ (vⱼ - uⱼ)(∂ⱼ vₖ - ∂ⱼ uₖ)`. These reduce the cross-testing identity
to the relative energy inequality of `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

theorem serrin_prod_memLp {f g : Vec3 → ℝ} {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (h : p⁻¹ + q⁻¹ = r⁻¹)
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume) :
    MemLp (fun x => f x * g x) (ENNReal.ofReal r) volume := by
  have _ := serrin_holder_ofReal3 hp hq hr h
  exact hf.mul hg

/-- The slice facts used in the trilinear identities. -/
structure SerrinSlice (w : Vec3 → Vec3) (Dw : Vec3 → Fin 3 → Vec3) : Prop where
  mem2 : MemLp w 2 volume
  grad2 : MemLp Dw 2 volume
  grad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3) (fun x => w x i) (fun x => Dw x i)
  trace : ∀ᵐ x ∂volume, ∑ j : Fin 3, Dw x j j = 0

theorem serrin_ofReal_two : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp

/-- The self-transport form of an `L⁵` slice vanishes. -/
theorem serrin_slice_self_transport {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    (hu : SerrinSlice u Du) (hu5 : MemLp u (ENNReal.ofReal 5) volume) :
    ∫ x : Vec3, ∑ k : Fin 3, u x k * ∑ j : Fin 3, u x j * Du x k j = 0 := by
  have hu2' : MemLp u (ENNReal.ofReal 2) volume := by rw [← serrin_ofReal_two]; exact hu.mem2
  have hu4 : MemLp u (ENNReal.ofReal 4) volume :=
    serrin_memLp_interpolate (by simp) (by simp) (ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hu2' hu5
  have hu103 : MemLp u (ENNReal.ofReal (10 / 3)) volume :=
    serrin_memLp_interpolate (by simp) (by simp) (ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hu2' hu5
  have hDu2' : MemLp Du (ENNReal.ofReal 2) volume := by rw [← serrin_ofReal_two]; exact hu.grad2
  have hbf (j k : Fin 3) : MemLp (fun x => u x j * u x k) 2 volume := by
    rw [serrin_ofReal_two]
    exact serrin_prod_memLp (p := 4) (q := 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hu4.eval j) (hu4.eval k)
  have hbDf (j k : Fin 3) : MemLp (fun x => u x j * Du x k j) (ENNReal.ofReal (10 / 7)) volume :=
    serrin_prod_memLp (p := 5) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hu5.eval j) ((hDu2'.eval k).eval j)
  have _ : ENNReal.HolderTriple (ENNReal.ofReal (10 / 7)) (ENNReal.ofReal (10 / 3)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have h := serrin_trilinear_vanish hu.mem2 hu.grad2 hu.grad hu.trace hu.mem2 hu.grad2 hu.grad
    hu.mem2 hu.grad2 hu.grad (r := ENNReal.ofReal (10 / 7)) (s := ENNReal.ofReal (10 / 3))
    (serrin_one_le_ofReal (by norm_num)) (by simp) hbf hbDf (fun k => hu103.eval k)
  have heq : (fun x => ∑ k : Fin 3, ∑ j : Fin 3, u x j * (Du x k j * u x k + u x k * Du x k j)) =
      fun x => 2 * ∑ k : Fin 3, u x k * ∑ j : Fin 3, u x j * Du x k j := by
    funext x
    simp only [Fin.sum_univ_three]
    ring
  rw [heq, integral_const_mul] at h
  linarith only [h]

/-- The sum of the two convection pairings minus the relative convection form
integrates to zero. -/
theorem serrin_slice_relative {u v : Vec3 → Vec3} {Du Dv : Vec3 → Fin 3 → Vec3}
    (hu : SerrinSlice u Du) (hu5 : MemLp u (ENNReal.ofReal 5) volume)
    (hv : SerrinSlice v Dv) (hv103 : MemLp v (ENNReal.ofReal (10 / 3)) volume) :
    (∫ x : Vec3, (∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) +
      (∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) -
      ∑ k : Fin 3, u x k * ∑ j : Fin 3, (v x j - u x j) * (Dv x k j - Du x k j)) = 0 := by
  have hu2' : MemLp u (ENNReal.ofReal 2) volume := by rw [← serrin_ofReal_two]; exact hu.mem2
  have hu4 : MemLp u (ENNReal.ofReal 4) volume :=
    serrin_memLp_interpolate (by simp) (by simp) (ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hu2' hu5
  have hu103 : MemLp u (ENNReal.ofReal (10 / 3)) volume :=
    serrin_memLp_interpolate (by simp) (by simp) (ENNReal.ofReal_le_ofReal (by norm_num))
      (ENNReal.ofReal_le_ofReal (by norm_num)) hu2' hu5
  have hDu2' : MemLp Du (ENNReal.ofReal 2) volume := by rw [← serrin_ofReal_two]; exact hu.grad2
  have hDv2' : MemLp Dv (ENNReal.ofReal 2) volume := by rw [← serrin_ofReal_two]; exact hv.grad2
  have huu (j k : Fin 3) : MemLp (fun x => u x j * u x k) 2 volume := by
    rw [serrin_ofReal_two]
    exact serrin_prod_memLp (p := 4) (q := 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hu4.eval j) (hu4.eval k)
  have huv (j k : Fin 3) : MemLp (fun x => u x j * v x k) 2 volume := by
    rw [serrin_ofReal_two]
    exact serrin_prod_memLp (p := 5) (q := 10 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hu5.eval j) (hv103.eval k)
  have hvu (j k : Fin 3) : MemLp (fun x => v x j * u x k) 2 volume := by
    rw [serrin_ofReal_two]
    exact serrin_prod_memLp (p := 10 / 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hv103.eval j) (hu5.eval k)
  have _ : ENNReal.HolderTriple (ENNReal.ofReal (10 / 7)) (ENNReal.ofReal (10 / 3)) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have hT1 := serrin_trilinear_vanish hu.mem2 hu.grad2 hu.grad hu.trace hv.mem2 hv.grad2 hv.grad
    hu.mem2 hu.grad2 hu.grad (r := ENNReal.ofReal (10 / 7)) (s := ENNReal.ofReal (10 / 3))
    (serrin_one_le_ofReal (by norm_num)) (by simp) huv
    (fun j k => serrin_prod_memLp (p := 5) (q := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hu5.eval j) ((hDv2'.eval k).eval j)) (fun k => hu103.eval k)
  have hT3 := serrin_trilinear_vanish hu.mem2 hu.grad2 hu.grad hu.trace hu.mem2 hu.grad2 hu.grad
    hu.mem2 hu.grad2 hu.grad (r := ENNReal.ofReal (10 / 7)) (s := ENNReal.ofReal (10 / 3))
    (serrin_one_le_ofReal (by norm_num)) (by simp) huu
    (fun j k => serrin_prod_memLp (p := 5) (q := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (hu5.eval j) ((hDu2'.eval k).eval j)) (fun k => hu103.eval k)
  have _ : ENNReal.HolderTriple (ENNReal.ofReal (5 / 4)) (ENNReal.ofReal 5) 1 :=
    serrin_holder_ofReal (by norm_num) (by norm_num) (by norm_num)
  have hT2 := serrin_trilinear_vanish hv.mem2 hv.grad2 hv.grad hv.trace hu.mem2 hu.grad2 hu.grad
    hu.mem2 hu.grad2 hu.grad (r := ENNReal.ofReal (5 / 4)) (s := ENNReal.ofReal 5)
    (serrin_one_le_ofReal (by norm_num)) (by simp) hvu
    (fun j k => serrin_prod_memLp (p := 10 / 3) (q := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (hv103.eval j) ((hDu2'.eval k).eval j)) (fun k => hu5.eval k)
  -- integrability of every monomial
  have hmon {F : Vec3 → ℝ} (hF : MemLp F 2 volume) {G : Vec3 → Fin 3 → Vec3}
      (hG : MemLp G 2 volume) (k j : Fin 3) : Integrable (fun x => F x * G x k j) volume :=
    hF.integrable_mul (q := 2) ((hG.eval k).eval j)
  have hsum2 (F : Fin 3 → Fin 3 → Vec3 → ℝ) (hF : ∀ k j, Integrable (F k j) volume) :
      Integrable (fun x => ∑ k : Fin 3, ∑ j : Fin 3, F k j x) volume :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hF k j
  have hX1 : Integrable (fun x => ∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) volume := by
    refine (hsum2 (fun k j x => v x j * u x k * Dv x k j)
      fun k j => hmon (hvu j k) hv.grad2 k j).congr (Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hX2 : Integrable (fun x => ∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) volume := by
    refine (hsum2 (fun k j x => u x j * v x k * Du x k j)
      fun k j => hmon (huv j k) hu.grad2 k j).congr (Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hY : Integrable (fun x => ∑ k : Fin 3, u x k * ∑ j : Fin 3,
      (v x j - u x j) * (Dv x k j - Du x k j)) volume := by
    refine (hsum2 (fun k j x => v x j * u x k * Dv x k j - v x j * u x k * Du x k j -
        u x j * u x k * Dv x k j + u x j * u x k * Du x k j)
      fun k j => (((hmon (hvu j k) hv.grad2 k j).sub (hmon (hvu j k) hu.grad2 k j)).sub
        (hmon (huu j k) hv.grad2 k j)).add (hmon (huu j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hpt : (fun x => (∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) +
      (∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) -
      ∑ k : Fin 3, u x k * ∑ j : Fin 3, (v x j - u x j) * (Dv x k j - Du x k j)) =
      fun x => (∑ k : Fin 3, ∑ j : Fin 3, u x j * (Dv x k j * u x k + v x k * Du x k j)) +
        (1 / 2 : ℝ) * (∑ k : Fin 3, ∑ j : Fin 3, v x j * (Du x k j * u x k + u x k * Du x k j)) -
        (1 / 2 : ℝ) * ∑ k : Fin 3, ∑ j : Fin 3, u x j * (Du x k j * u x k + u x k * Du x k j) := by
    funext x
    simp only [Fin.sum_univ_three]
    ring
  have hT1i : Integrable (fun x => ∑ k : Fin 3, ∑ j : Fin 3,
      u x j * (Dv x k j * u x k + v x k * Du x k j)) volume := by
    refine (hsum2 (fun k j x => u x j * u x k * Dv x k j + u x j * v x k * Du x k j)
      fun k j => (hmon (huu j k) hv.grad2 k j).add (hmon (huv j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hT2i : Integrable (fun x => ∑ k : Fin 3, ∑ j : Fin 3,
      v x j * (Du x k j * u x k + u x k * Du x k j)) volume := by
    refine (hsum2 (fun k j x => v x j * u x k * Du x k j + v x j * u x k * Du x k j)
      fun k j => (hmon (hvu j k) hu.grad2 k j).add (hmon (hvu j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hT3i : Integrable (fun x => ∑ k : Fin 3, ∑ j : Fin 3,
      u x j * (Du x k j * u x k + u x k * Du x k j)) volume := by
    refine (hsum2 (fun k j x => u x j * u x k * Du x k j + u x j * u x k * Du x k j)
      fun k j => (hmon (huu j k) hu.grad2 k j).add (hmon (huu j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hdiff : (∫ x : Vec3, (∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) +
      (∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) -
      ∑ k : Fin 3, u x k * ∑ j : Fin 3, (v x j - u x j) * (Dv x k j - Du x k j)) = 0 := by
    have hT2h : Integrable (fun x => (1 / 2 : ℝ) * ∑ k : Fin 3, ∑ j : Fin 3,
        v x j * (Du x k j * u x k + u x k * Du x k j)) volume := hT2i.const_mul _
    have hT3h : Integrable (fun x => (1 / 2 : ℝ) * ∑ k : Fin 3, ∑ j : Fin 3,
        u x j * (Du x k j * u x k + u x k * Du x k j)) volume := hT3i.const_mul _
    have hT12 : Integrable (fun x => (∑ k : Fin 3, ∑ j : Fin 3,
        u x j * (Dv x k j * u x k + v x k * Du x k j)) + (1 / 2 : ℝ) * ∑ k : Fin 3,
        ∑ j : Fin 3, v x j * (Du x k j * u x k + u x k * Du x k j)) volume := hT1i.add hT2h
    rw [hpt, integral_sub hT12 hT3h, integral_add hT1i hT2h, integral_const_mul,
      integral_const_mul, hT1, hT2, hT3]
    ring
  exact hdiff

end ESS
