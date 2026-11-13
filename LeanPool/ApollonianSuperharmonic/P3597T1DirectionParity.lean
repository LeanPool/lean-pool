/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3597T1GenericRayStability

-- [TABLET NODE: P3597T1DirectionParity]

/-!
# P3597T1DirectionParity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DirectionParityLemmas

private theorem basis_coordinates :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), (det2 d e ≠ 0) → (v = coordA d
        e v • d + coordB d e v • e) := by
  classical
  intro det2 coordA coordB d e v hD
  apply Prod.ext
  · change v.1 = (det2 v e / det2 d e) * d.1 + (det2 d v / det2 d e) * e.1
    field_simp [hD]
    dsimp [det2]; ring
  · change v.2 = (det2 v e / det2 d e) * d.2 + (det2 d v / det2 d e) * e.2
    field_simp [hD]
    dsimp [det2]; ring

private theorem coordA_swap :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), (det2 d e ≠ 0) → (coordA e d v
        = coordB d e v) := by
  classical
  intro det2 coordA coordB d e v hD
  have hnum : det2 v d = -det2 d v := by dsimp [det2]; ring
  have hden : det2 e d = -det2 d e := by dsimp [det2]; ring
  dsimp [coordA, coordB]
  rw [hnum, hden]
  simp

private theorem coordB_swap :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), (det2 d e ≠ 0) → (coordB e d v
        = coordA d e v) := by
  classical
  intro det2 coordA coordB d e v hD
  have hnum : det2 e v = -det2 v e := by dsimp [det2]; ring
  have hden : det2 e d = -det2 d e := by dsimp [det2]; ring
  dsimp [coordA, coordB]
  rw [hnum, hden]
  simp

private theorem coordA_affine :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), ∀ (w : Real × Real), ∀ (u :
        Real), coordA d e (v + u • (w-v)) = (1-u) * coordA d e v + u * coordA d e w := by
  classical
  intro det2 coordA d e v w u
  simp [coordA, det2, smul_eq_mul]; ring

private theorem coordB_affine :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), ∀ (w : Real × Real), ∀ (u :
        Real), coordB d e (v + u • (w-v)) = (1-u) * coordB d e v + u * coordB d e w := by
  classical
  intro det2 coordB d e v w u
  simp [coordB, det2, smul_eq_mul]; ring

private theorem coordA_scale :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    ∀ (d : Real × Real), ∀ (e : Real × Real), (det2 d e ≠ 0) → (∀ (t : Real), coordA d e (t • d)
        = t) := by
  classical
  intro det2 coordA d e hD t
  have hD' : d.1 * e.2 - d.2 * e.1 ≠ 0 := by simpa [det2] using hD
  dsimp [coordA, det2, smul_eq_mul]
  field_simp [hD']


private theorem coordB_scale :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1;
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e;
    ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (t : Real), coordB d e (t • d) = 0 := by
  classical
  intro det2 coordB d e t
  dsimp [coordB, det2, smul_eq_mul]
  rw [show d.1 * (t * d.2) - d.2 * (t * d.1) = 0 by ring]
  simp

private theorem ray_segment_axes :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    (∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), (det2 d e ≠ 0) → (v = coordA
        d e v • d + coordB d e v • e)) → ((∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real
        × Real), ∀ (w : Real × Real), ∀ (u : Real), coordA d e (v + u • (w-v)) = (1-u) * coordA d
        e v + u * coordA d e w) → ((∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real ×
        Real), ∀ (w : Real × Real), ∀ (u : Real), coordB d e (v + u • (w-v)) = (1-u) * coordB d e
        v + u * coordB d e w) → ((∀ (d : Real × Real), ∀ (e : Real × Real), (det2 d e ≠ 0) → (∀
        (t : Real), coordA d e (t • d) = t)) → ((∀ (d : Real × Real), ∀ (e : Real × Real), (det2
        d e ≠ 0) → (∀ (t : Real), coordB d e (t • d) = 0)) → (∀ (x : Real × Real), ∀ (d : Real ×
        Real), ∀ (e : Real × Real), ∀ (v : Real × Real), ∀ (w : Real × Real), (det2 d e ≠ 0) →
        ((∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real v w) ↔
      (∃ u : Real, 0 ≤ u ∧ u ≤ 1 ∧
        (1-u) * coordB d e (v-x) + u * coordB d e (w-x) = 0 ∧
        0 < (1-u) * coordA d e (v-x) + u * coordA d e (w-x)))))))) := by
  classical
  intro det2 coordA coordB basis_coordinates coordA_affine coordB_affine coordA_scale
      coordB_scale x d e v w hD
  constructor
  · rintro ⟨t, ht, hseg⟩
    rw [segment_eq_image'] at hseg
    obtain ⟨u, hu, heq⟩ := hseg
    refine ⟨u, hu.1, hu.2, ?_, ?_⟩
    · have hrel : t • d = (v-x) + u • ((w-x) - (v-x)) := by
        calc
          t • d = x + t • d - x := by simp
          _ = (v + u • (w-v)) - x := by rw [← heq]
          _ = (v-x) + u • ((w-x)-(v-x)) := by
            apply Prod.ext <;> simp [smul_eq_mul] <;> ring
      have hB := congrArg (coordB d e) hrel
      rw [coordB_scale d e hD t] at hB
      rw [coordB_affine] at hB
      exact hB.symm
    · have hrel : t • d = (v-x) + u • ((w-x) - (v-x)) := by
        calc
          t • d = x + t • d - x := by simp
          _ = (v + u • (w-v)) - x := by rw [← heq]
          _ = (v-x) + u • ((w-x)-(v-x)) := by
            apply Prod.ext <;> simp [smul_eq_mul] <;> ring
      have hA := congrArg (coordA d e) hrel
      rw [coordA_scale d e hD t] at hA
      rw [coordA_affine] at hA
      exact hA.symm ▸ ht
  · rintro ⟨u, hu0, hu1, hB, hA⟩
    let z := (v-x) + u • ((w-x) - (v-x))
    have hz := basis_coordinates d e z hD
    have hzB : coordB d e z = 0 := by
      dsimp [z]
      rw [coordB_affine]
      simpa using hB
    have hzA : 0 < coordA d e z := by
      dsimp [z]
      rw [coordA_affine]
      exact hA
    have hz' : z = coordA d e z • d := by
        rw [hzB] at hz
        simpa using hz
    have hrel : z = v + u • (w-v) - x := by
      dsimp [z]
      apply Prod.ext <;> simp [smul_eq_mul] <;> ring
    have hpoint : x + coordA d e z • d = v + u • (w-v) := by
      rw [← hz']
      calc
        x + z = x + (v + u • (w-v) - x) := by rw [hrel]
        _ = v + u • (w-v) := by ext <;> simp [smul_eq_mul]
    refine ⟨coordA d e z, hzA, ?_⟩
    rw [segment_eq_image']
    exact ⟨u, ⟨hu0, hu1⟩, hpoint.symm⟩

private theorem cyclicSucc_eq_add :
    let cyclicSucc (m : Nat) : Fin (m+1) ≃ Fin (m+1) := {
      toFun := fun i => ⟨(i.val + 1) % (m+1), Nat.mod_lt _ (by omega)⟩
      invFun := fun i => ⟨(i.val + m) % (m+1), Nat.mod_lt _ (by omega)⟩
      left_inv := by
        intro i
        apply Fin.ext
        change (((i.val + 1) % (m+1) + m) % (m+1)) = i.val
        by_cases hi : i.val = m
        · simp [hi]
        · have him : i.val < m := by omega
          have hinner : (i.val + 1) % (m+1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hinner]
          have heq : i.val + 1 + m = (m+1) + i.val := by omega
          rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
          simp [Nat.mod_eq_of_lt i.isLt]
      right_inv := by
        intro i
        apply Fin.ext
        change (((i.val + m) % (m+1) + 1) % (m+1)) = i.val
        by_cases hi : i.val = 0
        · simp [hi]
        · have heq : i.val + m = (m+1) + (i.val-1) := by omega
          have hmod : (i.val + m) % (m+1) = i.val - 1 := by
            have hmodi : (i.val-1) % (m+1) = i.val-1 := Nat.mod_eq_of_lt (by omega)
            rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
            simp [hmodi]
          rw [hmod]
          have hlt : i.val - 1 + 1 < m+1 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
    }
    ∀ {m : Nat}, ∀ (i : Fin (m+1)), cyclicSucc m i = i + 1 := by
  classical
  intro cyclicSucc m i
  apply Fin.ext
  simp [cyclicSucc, Fin.val_add]

private theorem cyclic_xor_count :
    let cyclicSucc (m : Nat) : Fin (m+1) ≃ Fin (m+1) := {
      toFun := fun i => ⟨(i.val + 1) % (m+1), Nat.mod_lt _ (by omega)⟩
      invFun := fun i => ⟨(i.val + m) % (m+1), Nat.mod_lt _ (by omega)⟩
      left_inv := by
        intro i
        apply Fin.ext
        change (((i.val + 1) % (m+1) + m) % (m+1)) = i.val
        by_cases hi : i.val = m
        · simp [hi]
        · have him : i.val < m := by omega
          have hinner : (i.val + 1) % (m+1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hinner]
          have heq : i.val + 1 + m = (m+1) + i.val := by omega
          rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
          simp [Nat.mod_eq_of_lt i.isLt]
      right_inv := by
        intro i
        apply Fin.ext
        change (((i.val + m) % (m+1) + 1) % (m+1)) = i.val
        by_cases hi : i.val = 0
        · simp [hi]
        · have heq : i.val + m = (m+1) + (i.val-1) := by omega
          have hmod : (i.val + m) % (m+1) = i.val - 1 := by
            have hmodi : (i.val-1) % (m+1) = i.val-1 := Nat.mod_eq_of_lt (by omega)
            rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
            simp [hmodi]
          rw [hmod]
          have hlt : i.val - 1 + 1 < m+1 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
    }
    ∀ {m : Nat}, ∀ (P : Fin (m+1) → Prop), ∀ (Q : Fin (m+1) → Prop), ∀ [DecidablePred P], ∀
        [DecidablePred Q], ∀ (b : Fin (m+1) → Bool), (∀ i, (P i ∧ ¬ Q i ∨ ¬ P i ∧ Q i) ↔
        b i ≠ b (cyclicSucc m i)) → ((Finset.univ.filter P).card % 2 = (Finset.univ.filter
            Q).card % 2) := by
  classical
  intro cyclicSucc m P Q typeclassInstance0 typeclassInstance1 b hxor
  classical
  let tr : Fin (m+1) → Prop := fun i => b i ≠ b (cyclicSucc m i)
  have hlocal (i : Fin (m+1)) :
      (if P i then 1 else 0) + (if Q i then 1 else 0) =
        (if tr i then 1 else 0) + 2 * (if P i ∧ Q i then 1 else 0) := by
    by_cases hp : P i <;> by_cases hq : Q i
    · have hnotx : ¬ (P i ∧ ¬ Q i ∨ ¬ P i ∧ Q i) := by simp [hp, hq]
      have ht : ¬ tr i := by
        intro htr
        exact hnotx ((hxor i).mpr htr)
      simp [hp, hq, tr, ht]
    · have hx : P i ∧ ¬ Q i ∨ ¬ P i ∧ Q i := by simp [hp, hq]
      have ht : tr i := (hxor i).mp hx
      simp [hp, hq, tr, ht]
    · have hx : P i ∧ ¬ Q i ∨ ¬ P i ∧ Q i := by simp [hp, hq]
      have ht : tr i := (hxor i).mp hx
      simp [hp, hq, tr, ht]
    · have hnotx : ¬ (P i ∧ ¬ Q i ∨ ¬ P i ∧ Q i) := by simp [hp, hq]
      have ht : ¬ tr i := by
        intro htr
        exact hnotx ((hxor i).mpr htr)
      simp [hp, hq, tr, ht]
  have hcounts :
      (Finset.univ.filter P).card + (Finset.univ.filter Q).card =
        (Finset.univ.filter tr).card + 2 * (Finset.univ.filter (fun i => P i ∧ Q i)).card := by
    have hp : (Finset.univ.filter P).card = ∑ i : Fin (m+1), if P i then 1 else 0 := by
      rw [Finset.card_filter]
    have hq : (Finset.univ.filter Q).card = ∑ i : Fin (m+1), if Q i then 1 else 0 := by
      rw [Finset.card_filter]
    have ht : (Finset.univ.filter tr).card = ∑ i : Fin (m+1), if tr i then 1 else 0 := by
      rw [Finset.card_filter]
    have hu : (Finset.univ.filter (fun i => P i ∧ Q i)).card =
        ∑ i : Fin (m+1), if P i ∧ Q i then 1 else 0 := by
      rw [Finset.card_filter]
    have hsum :
        (∑ i : Fin (m+1), if P i then 1 else 0) +
          (∑ i : Fin (m+1), if Q i then 1 else 0) =
        (∑ i : Fin (m+1), if tr i then 1 else 0) +
          2 * (∑ i : Fin (m+1), if P i ∧ Q i then 1 else 0) := by
      calc
        _ = ∑ i : Fin (m+1),
            ((if P i then 1 else 0) + (if Q i then 1 else 0)) := by
              rw [Finset.sum_add_distrib]
        _ = ∑ i : Fin (m+1),
            ((if tr i then 1 else 0) + 2 * (if P i ∧ Q i then 1 else 0)) := by
              exact Finset.sum_congr rfl (fun i _ => hlocal i)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hp, hq, ht, hu]
    exact hsum
  have htrans : ∃ k : Nat, (Finset.univ.filter tr).card = 2*k := by
    have heven : ∃ k : Int,
        (∑ i : Fin (m+1), if b i = b (cyclicSucc m i) then (0 : Int) else 1) = 2*k := by
      let w : Fin (m+1) → Int := fun i => if b i then 1 else 0
      let u : Fin (m+1) → Int := fun i =>
        if b i = false ∧ b (cyclicSucc m i) = true then 1 else 0
      have hlocal' (i : Fin (m+1)) :
          (if b i = b (cyclicSucc m i) then (0 : Int) else 1) =
            w i - w (cyclicSucc m i) + 2 * u i := by
        simp only [w, u]
        cases b i <;> cases b (cyclicSucc m i) <;> norm_num
      have hcomp : (∑ i, w (cyclicSucc m i)) = ∑ i, w i :=
        (cyclicSucc m).sum_comp w
      refine ⟨∑ i, u i, ?_⟩
      simp_rw [hlocal']
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcomp, sub_self,
        zero_add, Finset.mul_sum]
    obtain ⟨k, hk⟩ := heven
    have hcard : ((Finset.univ.filter tr).card : Int) =
        ∑ i : Fin (m+1), if b i = b (cyclicSucc m i) then (0 : Int) else 1 := by
      simp [tr, Finset.card_filter]
    refine ⟨k.toNat, ?_⟩
    omega
  obtain ⟨k, hk⟩ := htrans
  omega

private theorem affine_root_between :
    ∀ (a : Real), ∀ (c : Real), (a*c < 0) → (∃ u, 0 < u ∧ u < 1 ∧ (1-u)*a+u*c=0) := by
  classical
  intro a c hac
  have ha : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hac
    exact (lt_irrefl 0) hac
  by_cases hap : 0 < a
  · have hcn : c < 0 := by
      by_contra hn
      have hc0 : 0 ≤ c := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonneg (le_of_lt hap) hc0)) hac
    have hden : 0 < a-c := by linarith
    refine ⟨a/(a-c), div_pos hap hden, ?_, ?_⟩
    · rw [div_lt_one hden]
      linarith
    · field_simp [ne_of_gt hden]; ring
  · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt hap) ha
    have hcp : 0 < c := by
      by_contra hn
      have hc0 : c ≤ 0 := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos (le_of_lt han) hc0)) hac
    have hden : a-c < 0 := by linarith
    have hpos : 0 < a/(a-c) := div_pos_of_neg_of_neg han hden
    have hlt : a/(a-c) < 1 := by
      have hden' : 0 < c-a := by linarith
      have hgap : 0 < c/(c-a) := div_pos hcp hden'
      have hEq : 1-a/(a-c) = c/(c-a) := by
        have hden1 : c-a ≠ 0 := ne_of_gt hden'
        field_simp [ne_of_lt hden, hden1]; ring
      have : 0 < 1-a/(a-c) := by rw [hEq]; exact hgap
      linarith
    refine ⟨a/(a-c), hpos, hlt, ?_⟩
    field_simp [ne_of_lt hden]; ring

private theorem axis_root_x_identity :
    ∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d : Real), ∀ (u : Real), ((1-u)*b+u*d=0) →
        ((d-b)*((1-u)*a+u*c)=a*d-b*c) := by
  classical
  intro a b c d u hy
  linear_combination (c-a)*hy

private theorem axis_root_y_identity :
    ∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d : Real), ∀ (u : Real), ((1-u)*a+u*c=0) →
        ((a-c)*((1-u)*b+u*d)=a*d-b*c) := by
  classical
  intro a b c d u hx
  linear_combination (b-d)*hx

private theorem affine_pos :
    ∀ (a : Real), ∀ (c : Real), ∀ (u : Real), (0 ≤ u) → ((u ≤ 1) → ((0 < a) → ((0 < c) → (0 <
        (1-u)*a+u*c)))) := by
  classical
  intro a c u hu0 hu1 ha hc
  by_cases hu : u = 0
  · subst u
    simpa using ha
  · by_cases hu' : u = 1
    · subst u
      simpa using hc
    · have hlt : u < 1 := by
        by_contra hn
        exact hu' (le_antisymm hu1 (le_of_not_gt hn))
      have h1 : 0 < 1-u := by linarith
      have h2 : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
      exact add_pos (mul_pos h1 ha) (mul_pos h2 hc)

private theorem affine_neg :
    ∀ (a : Real), ∀ (c : Real), ∀ (u : Real), (0 ≤ u) → ((u ≤ 1) → ((a < 0) → ((c < 0) →
        ((1-u)*a+u*c < 0)))) := by
  classical
  intro a c u hu0 hu1 ha hc
  by_cases hu : u = 0
  · subst u
    simpa using ha
  · by_cases hu' : u = 1
    · subst u
      simpa using hc
    · have hlt : u < 1 := by
        by_contra hn
        exact hu' (le_antisymm hu1 (le_of_not_gt hn))
      have h1 : (1-u)*a < 0 := mul_neg_of_pos_of_neg (by linarith) ha
      have h2 : u*c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0 (le_of_lt hc)
      linarith

private theorem root_positive_product :
    ∀ (e : Real), ∀ (z : Real), ∀ (K : Real), (e ≠ 0) → ((e*z=K) → (0 < z ↔ 0 < K*e)) := by
  classical
  intro e z K he h
  rw [← h, mul_right_comm e z e,
    mul_pos_iff_of_pos_left (mul_self_pos.mpr he)]

private theorem affine_axis_crossing_iff :
    (∀ (a : Real), ∀ (c : Real), (a*c < 0) → (∃ u, 0 < u ∧ u < 1 ∧ (1-u)*a+u*c=0)) → ((∀ (a :
        Real), ∀ (c : Real), ∀ (u : Real), (0 ≤ u) → ((u ≤ 1) → ((0 < a) → ((0 < c) → (0 <
        (1-u)*a+u*c))))) → ((∀ (a : Real), ∀ (c : Real), ∀ (u : Real), (0 ≤ u) → ((u ≤ 1) → ((a <
        0) → ((c < 0) → ((1-u)*a+u*c < 0))))) → ((∀ (e : Real), ∀ (z : Real), ∀ (K : Real), (e ≠
        0) → ((e*z=K) → (0 < z ↔ 0 < K*e))) → (∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d :
        Real), (b ≠ 0) → ((d ≠ 0) → ((∃ u, 0 ≤ u ∧ u ≤ 1 ∧ (1-u)*b+u*d=0 ∧ 0<(1-u)*a+u*c) ↔
        b*d<0 ∧ 0<(a*d-b*c)*(d-b))))))) := by
  classical
  intro affine_root_between affine_pos affine_neg root_positive_product a b c d hb hd
  constructor
  · rintro ⟨u, hu0, hu1, hroot, hpos⟩
    have hbd : b*d<0 := by
      by_contra hn
      have hnonneg : 0≤b*d := le_of_not_gt hn
      rcases mul_nonneg_iff.mp hnonneg with ⟨hb0,hd0⟩ | ⟨hb0,hd0⟩
      · have hbpos : 0<b := lt_of_le_of_ne hb0 (Ne.symm hb)
        have hdpos : 0<d := lt_of_le_of_ne hd0 (Ne.symm hd)
        have h := affine_pos b d u hu0 hu1 hbpos hdpos
        linarith
      · have hbneg : b<0 := lt_of_le_of_ne' hb0 (Ne.symm hb)
        have hdneg : d<0 := lt_of_le_of_ne' hd0 (Ne.symm hd)
        have h := affine_neg b d u hu0 hu1 hbneg hdneg
        linarith
    have hbdne : b≠d := by
      intro heq
      rw [heq] at hbd
      nlinarith [sq_nonneg b]
    have hid : (d-b)*((1-u)*a+u*c)=a*d-b*c := by
      linear_combination (c-a)*hroot
    have hcrit : 0<(a*d-b*c)*(d-b) :=
      (root_positive_product (d-b) ((1-u)*a+u*c) (a*d-b*c)
        (sub_ne_zero.mpr (Ne.symm hbdne)) hid).mp hpos
    exact ⟨hbd, hcrit⟩
  · rintro ⟨hbd, hpos⟩
    obtain ⟨u, hu0, hu1, hroot⟩ := affine_root_between b d hbd
    have hbdne : b≠d := by
      intro heq
      rw [heq] at hbd
      nlinarith [sq_nonneg b]
    have hid : (d-b)*((1-u)*a+u*c)=a*d-b*c := by
      linear_combination (c-a)*hroot
    have hapos : 0<(1-u)*a+u*c :=
      (root_positive_product (d-b) ((1-u)*a+u*c) (a*d-b*c)
        (sub_ne_zero.mpr (Ne.symm hbdne)) hid).2 hpos
    exact ⟨u, le_of_lt hu0, le_of_lt hu1, hroot, hapos⟩

private theorem cone_crossing_accounting :
    ∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d : Real), ∀ (K : Real), (a ≠ 0) → ((b ≠ 0) →
        ((c ≠ 0) → ((d ≠ 0) → ((K ≠ 0) → ((K = a*d-b*c) → ((((0<a ∧ 0<b) ↔ (0<c ∧ 0<d)) ↔
        ((b*d<0 ∧ 0<K*(d-b)) ↔ (a*c<0 ∧ 0<K*(a-c)))))))))) := by
  classical
  intro a b c d K ha hb hc hd hK hKeq
  rcases lt_or_gt_of_ne ha with ha | ha <;>
    rcases lt_or_gt_of_ne hb with hb | hb <;>
    rcases lt_or_gt_of_ne hc with hc | hc <;>
    rcases lt_or_gt_of_ne hd with hd | hd <;>
    rcases lt_or_gt_of_ne hK with hK | hK
  all_goals
    try have hbd : b < d := by linarith
    try have hdb : d < b := by linarith
    try have hac : a < c := by linarith
    try have hca : c < a := by linarith
    simp only [mul_pos_iff, mul_neg_iff, sub_pos, sub_neg]
    first
    | solve | simp_all only [not_lt_of_gt, and_true, and_false, true_and, false_and,
        or_true, or_false, false_or, iff_self, iff_false,
        iff_true, not_true_eq_false]
    | simp_all only [not_lt_of_gt, and_true, and_false, true_and, false_and,
        or_true, or_false, false_or, iff_self, iff_false,
        iff_true, not_true_eq_false]
      nlinarith

private theorem cone_crossing_accounting_collinear :
    ∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d : Real), (0 < a*c) → ((0 < b*d) → ((((0<a ∧
        0<b) ↔ (0<c ∧ 0<d)) ↔
        ((b*d<0 ∧ 0<(0:Real)*(d-b)) ↔ (a*c<0 ∧ 0<(0:Real)*(a-c)))))) := by
  classical
  intro a b c d hac hbd
  have haciff : 0 < a ↔ 0 < c := by
    rcases mul_pos_iff.mp hac with h | h
    · exact iff_of_true h.1 h.2
    · exact iff_of_false (not_lt_of_gt h.1) (not_lt_of_gt h.2)
  have hbdiff : 0 < b ↔ 0 < d := by
    rcases mul_pos_iff.mp hbd with h | h
    · exact iff_of_true h.1 h.2
    · exact iff_of_false (not_lt_of_gt h.1) (not_lt_of_gt h.2)
  simpa only [zero_mul, lt_self_iff_false, and_false, iff_self, iff_true]
    using and_congr haciff hbdiff

private theorem axis_parity_from_no_origin :
    let cyclicSucc (m : Nat) : Fin (m+1) ≃ Fin (m+1) := {
      toFun := fun i => ⟨(i.val + 1) % (m+1), Nat.mod_lt _ (by omega)⟩
      invFun := fun i => ⟨(i.val + m) % (m+1), Nat.mod_lt _ (by omega)⟩
      left_inv := by
        intro i
        apply Fin.ext
        change (((i.val + 1) % (m+1) + m) % (m+1)) = i.val
        by_cases hi : i.val = m
        · simp [hi]
        · have him : i.val < m := by omega
          have hinner : (i.val + 1) % (m+1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hinner]
          have heq : i.val + 1 + m = (m+1) + i.val := by omega
          rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
          simp [Nat.mod_eq_of_lt i.isLt]
      right_inv := by
        intro i
        apply Fin.ext
        change (((i.val + m) % (m+1) + 1) % (m+1)) = i.val
        by_cases hi : i.val = 0
        · simp [hi]
        · have heq : i.val + m = (m+1) + (i.val-1) := by omega
          have hmod : (i.val + m) % (m+1) = i.val - 1 := by
            have hmodi : (i.val-1) % (m+1) = i.val-1 := Nat.mod_eq_of_lt (by omega)
            rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
            simp [hmodi]
          rw [hmod]
          have hlt : i.val - 1 + 1 < m+1 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
    }
    (∀ {m : Nat}, ∀ (P : Fin (m+1) → Prop), ∀ (Q : Fin (m+1) → Prop), ∀ [DecidablePred P], ∀
        [DecidablePred Q], ∀ (b : Fin (m+1) → Bool), (∀ i, (P i ∧ ¬ Q i ∨ ¬ P i ∧ Q i) ↔ b i ≠ b
        (cyclicSucc m i)) → ((Finset.univ.filter P).card % 2 = (Finset.univ.filter Q).card % 2))
        → ((∀ (a : Real), ∀ (c : Real), (a*c < 0) → (∃ u, 0 < u ∧ u < 1 ∧ (1-u)*a+u*c=0)) → ((∀
        (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d : Real), ∀ (u : Real), ((1-u)*b+u*d=0) →
        ((d-b)*((1-u)*a+u*c)=a*d-b*c)) → ((∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d :
        Real), ∀ (u : Real), ((1-u)*a+u*c=0) → ((a-c)*((1-u)*b+u*d)=a*d-b*c)) → ((∀ (a : Real), ∀
        (b : Real), ∀ (c : Real), ∀ (d : Real), ∀ (K : Real), (a ≠ 0) → ((b ≠ 0) → ((c ≠ 0) → ((d
        ≠ 0) → ((K ≠ 0) → ((K = a*d-b*c) → ((((0<a ∧ 0<b) ↔ (0<c ∧ 0<d)) ↔ ((b*d<0 ∧ 0<K*(d-b)) ↔
        (a*c<0 ∧ 0<K*(a-c))))))))))) → ((∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d : Real),
        (0 < a*c) → ((0 < b*d) → ((((0<a ∧ 0<b) ↔ (0<c ∧ 0<d)) ↔ ((b*d<0 ∧ 0<(0:Real)*(d-b)) ↔
        (a*c<0 ∧ 0<(0:Real)*(a-c))))))) → (∀ {m : Nat}, ∀ (A : Fin (m+1) → Real), ∀ (B : Fin
        (m+1) → Real), (∀ i, A i ≠ 0) → ((∀ i, B i ≠ 0) → ((∀ i u, u ∈ Set.Icc (0:Real) 1 →
        (1-u)*A i + u*A (cyclicSucc m i) = 0 →
        (1-u)*B i + u*B (cyclicSucc m i) = 0 → False) → ((Finset.univ.filter (fun i =>
        B i * B (cyclicSucc m i) < 0 ∧
          0 < (A i * B (cyclicSucc m i) - B i * A (cyclicSucc m i)) *
            (B (cyclicSucc m i) - B i))).card % 2 =
      (Finset.univ.filter (fun i =>
        A i * A (cyclicSucc m i) < 0 ∧
          0 < (A i * B (cyclicSucc m i) - B i * A (cyclicSucc m i)) *
            (A i - A (cyclicSucc m i)))).card % 2))))))))) := by
  classical
  intro cyclicSucc cyclic_xor_count affine_root_between axis_root_x_identity axis_root_y_identity
      cone_crossing_accounting cone_crossing_accounting_collinear m A B hA hB hno
  classical
  let K : Fin (m+1) → Real := fun i =>
    A i * B (cyclicSucc m i) - B i * A (cyclicSucc m i)
  let X : Fin (m+1) → Prop := fun i =>
    B i * B (cyclicSucc m i) < 0 ∧ 0 < K i * (B (cyclicSucc m i)-B i)
  let Y : Fin (m+1) → Prop := fun i =>
    A i * A (cyclicSucc m i) < 0 ∧ 0 < K i * (A i-A (cyclicSucc m i))
  let L : Fin (m+1) → Prop := fun i => 0 < A i ∧ 0 < B i
  let label : Fin (m+1) → Bool := fun i => decide (L i)
  have hxor : ∀ i, (X i ∧ ¬Y i ∨ ¬X i ∧ Y i) ↔
      label i ≠ label (cyclicSucc m i) := by
    intro i
    have hsameA (hK0 : K i = 0) : 0 < A i * A (cyclicSucc m i) := by
      have hne : A i * A (cyclicSucc m i) ≠ 0 := mul_ne_zero (hA i) (hA _)
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · obtain ⟨u, hu0, hu1, hroot⟩ := affine_root_between (A i)
          (A (cyclicSucc m i)) hneg
        have hden : A i - A (cyclicSucc m i) ≠ 0 := by
          intro heq
          have hEq : A i = A (cyclicSucc m i) := sub_eq_zero.mp heq
          rw [hEq] at hneg
          nlinarith [sq_nonneg (A i)]
        have hBroot : (1-u)*B i + u*B (cyclicSucc m i) = 0 := by
          have hid := axis_root_y_identity (A i) (B i)
            (A (cyclicSucc m i)) (B (cyclicSucc m i)) u hroot
          dsimp [K] at hK0
          have : (A i-A (cyclicSucc m i)) *
              ((1-u)*B i+u*B (cyclicSucc m i)) = 0 := by
            nlinarith [hid, hK0]
          rcases mul_eq_zero.mp this with he | hr
          · exact (hden he).elim
          · exact hr
        exact False.elim (hno i u ⟨le_of_lt hu0, le_of_lt hu1⟩ hroot hBroot)
      · exact hpos
    have hsameB (hK0 : K i = 0) : 0 < B i * B (cyclicSucc m i) := by
      have hne : B i * B (cyclicSucc m i) ≠ 0 := mul_ne_zero (hB i) (hB _)
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · obtain ⟨u, hu0, hu1, hroot⟩ := affine_root_between (B i)
          (B (cyclicSucc m i)) hneg
        have hden : B (cyclicSucc m i) - B i ≠ 0 := by
          intro heq
          have hEq : B (cyclicSucc m i) = B i := sub_eq_zero.mp heq
          rw [hEq] at hneg
          nlinarith [sq_nonneg (B i)]
        have hAroot : (1-u)*A i + u*A (cyclicSucc m i) = 0 := by
          have hid := axis_root_x_identity (A i) (B i)
            (A (cyclicSucc m i)) (B (cyclicSucc m i)) u hroot
          dsimp [K] at hK0
          have : (B (cyclicSucc m i)-B i) *
              ((1-u)*A i+u*A (cyclicSucc m i)) = 0 := by
            nlinarith [hid, hK0]
          rcases mul_eq_zero.mp this with he | hr
          · exact (hden he).elim
          · exact hr
        exact False.elim (hno i u ⟨le_of_lt hu0, le_of_lt hu1⟩ hAroot hroot)
      · exact hpos
    have hcone :
        (L i ↔ L (cyclicSucc m i)) ↔ (X i ↔ Y i) := by
      by_cases hK : K i = 0
      · simpa [L, X, Y, K, hK] using
          cone_crossing_accounting_collinear (A i) (B i)
            (A (cyclicSucc m i)) (B (cyclicSucc m i)) (hsameA hK) (hsameB hK)
      · exact cone_crossing_accounting (A i) (B i)
          (A (cyclicSucc m i)) (B (cyclicSucc m i)) (K i)
          (hA i) (hB i) (hA _) (hB _) hK (by rfl)
    have hlabels : (label i ≠ label (cyclicSucc m i)) ↔
        ¬ (L i ↔ L (cyclicSucc m i)) := by
      by_cases h1 : L i <;> by_cases h2 : L (cyclicSucc m i) <;>
        simp [label, h1, h2]
    have hxor' : (X i ∧ ¬Y i ∨ ¬X i ∧ Y i) ↔ ¬(X i ↔ Y i) := by
      by_cases hx : X i <;> by_cases hy : Y i <;> simp [hx, hy]
    exact hxor'.trans ((not_congr hcone.symm).trans hlabels.symm)
  exact cyclic_xor_count X Y label hxor

private theorem coordinate_hit_d :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    (∀ (x : Real × Real), ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), ∀ (w :
        Real × Real), (det2 d e ≠ 0) → ((∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real v w) ↔ (∃ u
        : Real, 0 ≤ u ∧ u ≤ 1 ∧ (1-u) * coordB d e (v-x) + u * coordB d e (w-x) = 0 ∧ 0 < (1-u) *
        coordA d e (v-x) + u * coordA d e (w-x)))) → ((∀ (a : Real), ∀ (b : Real), ∀ (c : Real),
        ∀ (d : Real), (b ≠ 0) → ((d ≠ 0) → ((∃ u, 0 ≤ u ∧ u ≤ 1 ∧ (1-u)*b+u*d=0 ∧ 0<(1-u)*a+u*c)
        ↔ b*d<0 ∧ 0<(a*d-b*c)*(d-b)))) → (∀ (x : Real × Real), ∀ (d : Real × Real), ∀ (e : Real ×
        Real), ∀ (v : Real × Real), ∀ (w : Real × Real), (det2 d e ≠ 0) → ((coordB d e (v-x) ≠ 0)
        → ((coordB d e (w-x) ≠ 0) → ((∃ t : Real, 0<t ∧ x+t • d ∈ segment Real v w) ↔
        coordB d e (v-x) * coordB d e (w-x) < 0 ∧
        0 < (coordA d e (v-x)*coordB d e (w-x) -
          coordB d e (v-x)*coordA d e (w-x)) *
          (coordB d e (w-x)-coordB d e (v-x))))))) := by
  classical
  intro det2 coordA coordB ray_segment_axes affine_axis_crossing_iff x d e v w hD hb hd
  rw [ray_segment_axes x d e v w hD]
  exact affine_axis_crossing_iff
    (coordA d e (v-x)) (coordB d e (v-x))
    (coordA d e (w-x)) (coordB d e (w-x)) hb hd

private theorem coordinate_hit_e :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    (∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), (det2 d e ≠ 0) → (coordA e d
        v = coordB d e v)) → ((∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real),
        (det2 d e ≠ 0) → (coordB e d v = coordA d e v)) → ((∀ (x : Real × Real), ∀ (d : Real ×
        Real), ∀ (e : Real × Real), ∀ (v : Real × Real), ∀ (w : Real × Real), (det2 d e ≠ 0) →
        ((∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real v w) ↔ (∃ u : Real, 0 ≤ u ∧ u ≤ 1 ∧ (1-u)
        * coordB d e (v-x) + u * coordB d e (w-x) = 0 ∧ 0 < (1-u) * coordA d e (v-x) + u * coordA
        d e (w-x)))) → ((∀ (a : Real), ∀ (b : Real), ∀ (c : Real), ∀ (d : Real), (b ≠ 0) → ((d ≠
        0) → ((∃ u, 0 ≤ u ∧ u ≤ 1 ∧ (1-u)*b+u*d=0 ∧ 0<(1-u)*a+u*c) ↔ b*d<0 ∧ 0<(a*d-b*c)*(d-b))))
        → (∀ (x : Real × Real), ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), ∀
        (w : Real × Real), (det2 d e ≠ 0) → ((coordA d e (v-x) ≠ 0) → ((coordA d e (w-x) ≠ 0) →
        ((∃ t : Real, 0<t ∧ x+t • e ∈ segment Real v w) ↔
        coordA d e (v-x) * coordA d e (w-x) < 0 ∧
        0 < (coordA d e (v-x)*coordB d e (w-x) -
          coordB d e (v-x)*coordA d e (w-x)) *
          (coordA d e (v-x)-coordA d e (w-x))))))))) := by
  classical
  intro det2 coordA coordB coordA_swap coordB_swap ray_segment_axes affine_axis_crossing_iff x d
      e v w hD ha hc
  have hED : det2 e d ≠ 0 := by
    intro h
    have hs : det2 e d = -det2 d e := by dsimp [det2]; ring
    rw [hs] at h
    exact hD (by linarith)
  have ha' : coordB e d (v-x) ≠ 0 := by
    rw [coordB_swap d e (v-x) hD]
    exact ha
  have hc' : coordB e d (w-x) ≠ 0 := by
    rw [coordB_swap d e (w-x) hD]
    exact hc
  rw [ray_segment_axes x e d v w hED]
  rw [coordA_swap d e (v-x) hD, coordB_swap d e (v-x) hD,
    coordA_swap d e (w-x) hD, coordB_swap d e (w-x) hD]
  have hh := affine_axis_crossing_iff
    (coordA e d (v-x)) (coordB e d (v-x))
    (coordA e d (w-x)) (coordB e d (w-x)) ha' hc'
  rw [coordA_swap d e (v-x) hD, coordB_swap d e (v-x) hD,
    coordA_swap d e (w-x) hD, coordB_swap d e (w-x) hD] at hh
  have hterm :
      (coordB d e (v-x)*coordA d e (w-x) -
        coordA d e (v-x)*coordB d e (w-x)) *
        (coordA d e (w-x)-coordA d e (v-x)) =
      (coordA d e (v-x)-coordA d e (w-x)) *
        (coordA d e (v-x)*coordB d e (w-x) -
          coordB d e (v-x)*coordA d e (w-x)) := by ring
  have hpos :
      0 < (coordB d e (v-x)*coordA d e (w-x) -
        coordA d e (v-x)*coordB d e (w-x)) *
        (coordA d e (w-x)-coordA d e (v-x)) ↔
      0 < (coordA d e (v-x)*coordB d e (w-x) -
        coordB d e (v-x)*coordA d e (w-x)) *
        (coordA d e (v-x)-coordA d e (w-x)) := by
    rw [hterm]
    have hcomm :
        (coordA d e (v-x)-coordA d e (w-x)) *
          (coordA d e (v-x)*coordB d e (w-x) -
            coordB d e (v-x)*coordA d e (w-x)) =
        (coordA d e (v-x)*coordB d e (w-x) -
          coordB d e (v-x)*coordA d e (w-x)) *
          (coordA d e (v-x)-coordA d e (w-x)) := by ring
    rw [hcomm]
  exact hh.trans (and_congr Iff.rfl hpos)

private theorem cyclic_direction_parity_nonparallel :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
    let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
    (∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real × Real), (det2 d e ≠ 0) → (v = coordA
        d e v • d + coordB d e v • e)) → ((∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real
        × Real), ∀ (w : Real × Real), ∀ (u : Real), coordA d e (v + u • (w-v)) = (1-u) * coordA d
        e v + u * coordA d e w) → ((∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real ×
        Real), ∀ (w : Real × Real), ∀ (u : Real), coordB d e (v + u • (w-v)) = (1-u) * coordB d e
        v + u * coordB d e w) → (
    let cyclicSucc (m : Nat) : Fin (m+1) ≃ Fin (m+1) := {
      toFun := fun i => ⟨(i.val + 1) % (m+1), Nat.mod_lt _ (by omega)⟩
      invFun := fun i => ⟨(i.val + m) % (m+1), Nat.mod_lt _ (by omega)⟩
      left_inv := by
        intro i
        apply Fin.ext
        change (((i.val + 1) % (m+1) + m) % (m+1)) = i.val
        by_cases hi : i.val = m
        · simp [hi]
        · have him : i.val < m := by omega
          have hinner : (i.val + 1) % (m+1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hinner]
          have heq : i.val + 1 + m = (m+1) + i.val := by omega
          rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
          simp [Nat.mod_eq_of_lt i.isLt]
      right_inv := by
        intro i
        apply Fin.ext
        change (((i.val + m) % (m+1) + 1) % (m+1)) = i.val
        by_cases hi : i.val = 0
        · simp [hi]
        · have heq : i.val + m = (m+1) + (i.val-1) := by omega
          have hmod : (i.val + m) % (m+1) = i.val - 1 := by
            have hmodi : (i.val-1) % (m+1) = i.val-1 := Nat.mod_eq_of_lt (by omega)
            rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
            simp [hmodi]
          rw [hmod]
          have hlt : i.val - 1 + 1 < m+1 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
    }
    (∀ {m : Nat}, ∀ (A : Fin (m+1) → Real), ∀ (B : Fin (m+1) → Real), (∀ i, A i ≠ 0) → ((∀ i, B i
        ≠ 0) → ((∀ i u, u ∈ Set.Icc (0:Real) 1 → (1-u)*A i + u*A (cyclicSucc m i) = 0 → (1-u)*B i
        + u*B (cyclicSucc m i) = 0 → False) → ((Finset.univ.filter (fun i => B i * B (cyclicSucc
        m i) < 0 ∧ 0 < (A i * B (cyclicSucc m i) - B i * A (cyclicSucc m i)) * (B (cyclicSucc m
        i) - B i))).card % 2 = (Finset.univ.filter (fun i => A i * A (cyclicSucc m i) < 0 ∧ 0 <
        (A i * B (cyclicSucc m i) - B i * A (cyclicSucc m i)) * (A i - A (cyclicSucc m i)))).card
        % 2)))) → ((∀ (x : Real × Real), ∀ (d : Real × Real), ∀ (e : Real × Real), ∀ (v : Real ×
        Real), ∀ (w : Real × Real), (det2 d e ≠ 0) → ((coordB d e (v-x) ≠ 0) → ((coordB d e (w-x)
        ≠ 0) → ((∃ t : Real, 0<t ∧ x+t • d ∈ segment Real v w) ↔ coordB d e (v-x) * coordB d e
        (w-x) < 0 ∧ 0 < (coordA d e (v-x)*coordB d e (w-x) - coordB d e (v-x)*coordA d e (w-x)) *
        (coordB d e (w-x)-coordB d e (v-x)))))) → ((∀ (x : Real × Real), ∀ (d : Real × Real), ∀
        (e : Real × Real), ∀ (v : Real × Real), ∀ (w : Real × Real), (det2 d e ≠ 0) → ((coordA d
        e (v-x) ≠ 0) → ((coordA d e (w-x) ≠ 0) → ((∃ t : Real, 0<t ∧ x+t • e ∈ segment Real v w)
        ↔ coordA d e (v-x) * coordA d e (w-x) < 0 ∧ 0 < (coordA d e (v-x)*coordB d e (w-x) -
        coordB d e (v-x)*coordA d e (w-x)) * (coordA d e (v-x)-coordA d e (w-x)))))) → (∀ {m :
        Nat}, ∀ (v : Fin (m+1) → Real × Real), ∀ (x : Real × Real), ∀ (d : Real × Real), ∀ (e :
        Real × Real), (det2 d e ≠ 0) → ((∀ i, x ∉ segment Real (v i) (v (cyclicSucc m i))) → ((∀
        i, det2 d (v i-x) ≠ 0) → ((∀ i, det2 e (v i-x) ≠ 0) → (Set.ncard {i : Fin (m+1) | ∃ t :
        Real, 0<t ∧
        x+t • d ∈ segment Real (v i) (v (cyclicSucc m i))} % 2 =
      Set.ncard {i : Fin (m+1) | ∃ t : Real, 0<t ∧
        x+t • e ∈ segment Real (v i) (v (cyclicSucc m i))} % 2)))))))))) := by
  classical
  intro det2 coordA coordB basis_coordinates coordA_affine coordB_affine cyclicSucc
      axis_parity_from_no_origin coordinate_hit_d coordinate_hit_e m v x d e hD hx hdv hev
  classical
  let A : Fin (m+1) → Real := fun i => coordA d e (v i-x)
  let B : Fin (m+1) → Real := fun i => coordB d e (v i-x)
  have hA : ∀ i, A i ≠ 0 := by
    intro i
    apply div_ne_zero
    · have hswap : det2 (v i-x) e = -det2 e (v i-x) := by dsimp [det2]; ring
      rw [hswap]
      exact neg_ne_zero.mpr (hev i)
    · exact hD
  have hB : ∀ i, B i ≠ 0 := by
    intro i
    exact div_ne_zero (hdv i) hD
  have hno : ∀ i u, u ∈ Set.Icc (0:Real) 1 →
      (1-u)*A i+u*A (cyclicSucc m i)=0 →
      (1-u)*B i+u*B (cyclicSucc m i)=0 → False := by
    intro i u hu ha hb
    let z := (v i-x)+u • ((v (cyclicSucc m i)-x)-(v i-x))
    have hzA : coordA d e z = 0 := by
      dsimp [z, A] at ha ⊢
      rw [coordA_affine]
      exact ha
    have hzB : coordB d e z = 0 := by
      dsimp [z, B] at hb ⊢
      rw [coordB_affine]
      exact hb
    have hz : z = 0 := by
      rw [basis_coordinates d e z hD]
      simp [hzA, hzB]
    have hsum : x+z = v i+u • (v (cyclicSucc m i)-v i) := by
      dsimp [z]
      module
    rw [hz] at hsum
    have hmem : x ∈ segment Real (v i) (v (cyclicSucc m i)) := by
      rw [segment_eq_image']
      exact ⟨u, hu, by simpa using hsum.symm⟩
    exact hx i hmem
  have haxes := axis_parity_from_no_origin A B hA hB hno
  let PX : Fin (m+1) → Prop := fun i =>
    ∃ t : Real, 0<t ∧ x+t • d ∈ segment Real (v i) (v (cyclicSucc m i))
  let PY : Fin (m+1) → Prop := fun i =>
    ∃ t : Real, 0<t ∧ x+t • e ∈ segment Real (v i) (v (cyclicSucc m i))
  let X : Fin (m+1) → Prop := fun i =>
    B i*B (cyclicSucc m i)<0 ∧
      0<(A i*B (cyclicSucc m i)-B i*A (cyclicSucc m i))*(B (cyclicSucc m i)-B i)
  let Y : Fin (m+1) → Prop := fun i =>
    A i*A (cyclicSucc m i)<0 ∧
      0<(A i*B (cyclicSucc m i)-B i*A (cyclicSucc m i))*(A i-A (cyclicSucc m i))
  have hPX : ∀ i, PX i ↔ X i := by
    intro i
    exact coordinate_hit_d x d e (v i) (v (cyclicSucc m i)) hD (hB i) (hB _)
  have hPY : ∀ i, PY i ↔ Y i := by
    intro i
    exact coordinate_hit_e x d e (v i) (v (cyclicSucc m i)) hD (hA i) (hA _)
  have hsetX : {i : Fin (m+1) | PX i} = {i | X i} := by
    ext i
    exact hPX i
  have hsetY : {i : Fin (m+1) | PY i} = {i | Y i} := by
    ext i
    exact hPY i
  have hnX : Set.ncard {i : Fin (m+1) | PX i} = (Finset.univ.filter X).card := by
    rw [hsetX, Set.ncard_eq_toFinset_card]
    congr 1
    ext i
    simp
  have hnY : Set.ncard {i : Fin (m+1) | PY i} = (Finset.univ.filter Y).card := by
    rw [hsetY, Set.ncard_eq_toFinset_card]
    congr 1
    ext i
    simp
  rw [hnX, hnY]
  simpa [X, Y, A, B] using haxes

private theorem choose_common_generic :
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    ∀ {n : Nat}, ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : Real × Real), ∀
        (e : Real × Real), (x ∉ P3544T1BoundaryCarrier p) → ((d ≠ 0) → ((e ≠ 0) → (∃ f : Real ×
        Real,
        (∀ i, det2 f (p.vertex i-x) ≠ 0) ∧
        (∀ i, det2 f (p.vertex (i+1)-p.vertex i) ≠ 0) ∧
        det2 f d ≠ 0 ∧ det2 f e ≠ 0))) := by
  classical
  intro det2 n p x d e hx hd he
  classical
  have hvertices : ∀ i, p.vertex i ≠ x := by
    intro i hiv
    have hv : p.vertex i ∈ ⋃ j, segment Real (p.vertex j) (p.vertex (j+1)) :=
      Set.mem_iUnion.mpr ⟨i, left_mem_segment Real _ _⟩
    exact hx (hiv ▸ hv)
  obtain ⟨g, hgV, hgE⟩ := (P3597T1GenericRayStability p).1 x hvertices
  have hgn : g ≠ 0 := by
    intro hzero
    have hh := hgV 0
    rw [hzero] at hh
    exact hh (by simp [])
  let k : Real × Real := (-g.2, g.1)
  have hIndependent (z : Real × Real) (h1 : det2 g z = 0)
      (h2 : det2 k z = 0) : z=0 := by
    have hpos : 0 < g.1^2+g.2^2 := by
      have hcoord : g.1 ≠ 0 ∨ g.2 ≠ 0 := by
        by_contra h
        push Not at h
        apply hgn
        exact Prod.ext h.1 h.2
      rcases hcoord with hcoord | hcoord
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hcoord) (sq_nonneg _)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hcoord)
    have hposne : g.1^2+g.2^2 ≠ 0 := ne_of_gt hpos
    have hz1 : (g.1^2+g.2^2)*z.1=0 := by
      dsimp [det2, k] at h1 h2 ⊢
      linear_combination -g.2 * h1 - g.1 * h2
    have hz2 : (g.1^2+g.2^2)*z.2=0 := by
      dsimp [det2, k] at h1 h2 ⊢
      linear_combination g.1 * h1 - g.2 * h2
    have hz1' : z.1=0 := (mul_eq_zero.mp hz1).resolve_left hposne
    have hz2' : z.2=0 := (mul_eq_zero.mp hz2).resolve_left hposne
    exact Prod.ext hz1' hz2'
  let W : Fin (n+3) × Bool → Real × Real := fun j =>
    if j.2 then p.vertex j.1-x else p.vertex (j.1+1)-p.vertex j.1
  have hbase : ∀ j, det2 g (W j) ≠ 0 := by
    intro j
    cases j with
    | mk i b =>
      cases b with
      | false => simpa [W, det2] using hgE i
      | true => simpa [W, det2] using hgV i
  let bad : (Real × Real) → Real := fun w =>
    if det2 k w = 0 then 0 else -det2 g w / det2 k w
  let S : Finset Real := Finset.univ.image (fun j => bad (W j))
  let S' : Finset Real := insert (bad d) (insert (bad e) S)
  have hcard : S'.card < ENat.card Real := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.natCast_lt_top _
  obtain ⟨s, hs⟩ := Finset.exists_notMem_of_card_lt_enatCard hcard
  let f : Real × Real := g+s • k
  have avoid (w : Real × Real) (hcoef : det2 k w=0 → det2 g w ≠0)
      (hmem : bad w∈S') : det2 f w ≠0 := by
    intro hz
    have hlin : det2 g w+s*det2 k w=0 := by
      have heq : det2 (g+s • k) w = det2 g w+s*det2 k w := by
        dsimp [det2, smul_eq_mul]; ring
      dsimp [f] at hz
      rw [heq] at hz
      exact hz
    by_cases hc : det2 k w=0
    · exact hcoef hc (by simpa [hc] using hlin)
    · have hs' : s= -det2 g w/det2 k w := by
        apply (eq_div_iff hc).2
        nlinarith [hlin]
      have hsb : s=bad w := by simpa [bad, hc] using hs'
      have hmem' : s∈S' := by rw [hsb]; exact hmem
      exact hs hmem'
  have hfv : ∀ i, det2 f (p.vertex i-x) ≠ 0 := by
    intro i
    apply avoid
    · intro _
      simpa [W, det2] using hbase (i,true)
    · have hm : bad (W (i,true))∈S :=
        Finset.mem_image.mpr ⟨(i,true), Finset.mem_univ _, rfl⟩
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa [W] using hm))
  have hfe : ∀ i, det2 f (p.vertex (i+1)-p.vertex i) ≠ 0 := by
    intro i
    apply avoid
    · intro _
      simpa [W, det2] using hbase (i,false)
    · have hm : bad (W (i,false))∈S :=
        Finset.mem_image.mpr ⟨(i,false), Finset.mem_univ _, rfl⟩
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa [W] using hm))
  have hfd : det2 f d ≠ 0 := by
    apply avoid
    · intro hc hg
      exact hd (hIndependent d hg hc)
    · simp [S']
  have hfe' : det2 f e ≠ 0 := by
    apply avoid
    · intro hc hg
      exact he (hIndependent e hg hc)
    · simp [S']
  exact ⟨f, hfv, hfe, hfd, hfe'⟩

private theorem hcyc :
    ∀ (n : Nat),
    let cyclicSucc (m : Nat) : Fin (m+1) ≃ Fin (m+1) := {
      toFun := fun i => ⟨(i.val + 1) % (m+1), Nat.mod_lt _ (by omega)⟩
      invFun := fun i => ⟨(i.val + m) % (m+1), Nat.mod_lt _ (by omega)⟩
      left_inv := by
        intro i
        apply Fin.ext
        change (((i.val + 1) % (m+1) + m) % (m+1)) = i.val
        by_cases hi : i.val = m
        · simp [hi]
        · have him : i.val < m := by omega
          have hinner : (i.val + 1) % (m+1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hinner]
          have heq : i.val + 1 + m = (m+1) + i.val := by omega
          rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
          simp [Nat.mod_eq_of_lt i.isLt]
      right_inv := by
        intro i
        apply Fin.ext
        change (((i.val + m) % (m+1) + 1) % (m+1)) = i.val
        by_cases hi : i.val = 0
        · simp [hi]
        · have heq : i.val + m = (m+1) + (i.val-1) := by omega
          have hmod : (i.val + m) % (m+1) = i.val - 1 := by
            have hmodi : (i.val-1) % (m+1) = i.val-1 := Nat.mod_eq_of_lt (by omega)
            rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
            simp [hmodi]
          rw [hmod]
          have hlt : i.val - 1 + 1 < m+1 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
    }
    (∀ {m : Nat}, ∀ (i : Fin (m+1)), cyclicSucc m i = i + 1) → (
    let m := n+2
    ∀ (i : Fin (m+1)), cyclicSucc m i = i+1) := by
  classical
  intro n cyclicSucc cyclicSucc_eq_add m i
  simpa [m] using cyclicSucc_eq_add i

private theorem hxseg :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), (x ∉
        P3544T1BoundaryCarrier p) → (
    let cyclicSucc (m : Nat) : Fin (m+1) ≃ Fin (m+1) := {
      toFun := fun i => ⟨(i.val + 1) % (m+1), Nat.mod_lt _ (by omega)⟩
      invFun := fun i => ⟨(i.val + m) % (m+1), Nat.mod_lt _ (by omega)⟩
      left_inv := by
        intro i
        apply Fin.ext
        change (((i.val + 1) % (m+1) + m) % (m+1)) = i.val
        by_cases hi : i.val = m
        · simp [hi]
        · have him : i.val < m := by omega
          have hinner : (i.val + 1) % (m+1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hinner]
          have heq : i.val + 1 + m = (m+1) + i.val := by omega
          rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
          simp [Nat.mod_eq_of_lt i.isLt]
      right_inv := by
        intro i
        apply Fin.ext
        change (((i.val + m) % (m+1) + 1) % (m+1)) = i.val
        by_cases hi : i.val = 0
        · simp [hi]
        · have heq : i.val + m = (m+1) + (i.val-1) := by omega
          have hmod : (i.val + m) % (m+1) = i.val - 1 := by
            have hmodi : (i.val-1) % (m+1) = i.val-1 := Nat.mod_eq_of_lt (by omega)
            rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
            simp [hmodi]
          rw [hmod]
          have hlt : i.val - 1 + 1 < m+1 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
    }
    let m := n+2
    let v : Fin (m+1) → Real × Real := p.vertex
    (∀ (i : Fin (m+1)), cyclicSucc m i = i+1) → (∀ i, x ∉ segment Real (v i) (v (cyclicSucc m
        i)))) := by
  classical
  intro n p x hx cyclicSucc m v hcyc i hi
  apply hx
  change x ∈ ⋃ j, segment Real (p.vertex j) (p.vertex (j+1))
  exact Set.mem_iUnion.mpr ⟨i, by simpa [v, hcyc] using hi⟩

private theorem hdv0 :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : Real × Real), (∀
        i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) → (
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let m := n+2
    let v : Fin (m+1) → Real × Real := p.vertex
    ∀ i, det2 d (v i-x) ≠ 0) := by
  classical
  intro n p x d hdv det2 m v i
  simpa [det2, v] using hdv i

private abbrev hdv'0 := ApollonianSuperharmonic.DirectionParityLemmas.hdv0

private theorem hdn :
    ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (x : Real × Real), ∀ (d : Real × Real),
    let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
    let m := n+2
    let v : Fin (m+1) → Real × Real := p.vertex
    (∀ i, det2 d (v i-x) ≠ 0) → (d ≠ 0) := by
  classical
  intro n p x d det2 m v hdv0 hz
  have h := hdv0 0
  rw [hz] at h
  exact h (by simp [det2])

private abbrev hd'n := ApollonianSuperharmonic.DirectionParityLemmas.hdn

end DirectionParityLemmas

theorem P3597T1DirectionParity {n : Nat} (p : P3381T1PolygonBoundary n)
    (x d d' : Real × Real) (hx : x ∉ P3544T1BoundaryCarrier p)
    (hdv : ∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0)
    (hdv' : ∀ i, d'.1 * (p.vertex i - x).2 - d'.2 * (p.vertex i - x).1 ≠ 0)
     :
    Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
      x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} % 2 =
    Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
      x + t • d' ∈ segment Real (p.vertex i) (p.vertex (i + 1))} % 2 := by
-- BODY
  classical
  let det2 (v w : Real × Real) : Real := v.1 * w.2 - v.2 * w.1
  let coordA (d e : Real × Real) (v : Real × Real) : Real := det2 v e / det2 d e
  let coordB (d e : Real × Real) (v : Real × Real) : Real := det2 d v / det2 d e
  let basis_coordinates (d e v : Real × Real) (hD : det2 d e ≠ 0) :
      v = coordA d e v • d + coordB d e v • e := DirectionParityLemmas.basis_coordinates d e v hD
  let coordA_swap (d e v : Real × Real) (hD : det2 d e ≠ 0) :
      coordA e d v = coordB d e v := DirectionParityLemmas.coordA_swap d e v hD
  let coordB_swap (d e v : Real × Real) (hD : det2 d e ≠ 0) :
      coordB e d v = coordA d e v := DirectionParityLemmas.coordB_swap d e v hD
  let coordA_affine (d e v w : Real × Real) (u : Real) :
      coordA d e (v + u • (w-v)) = (1-u) * coordA d e v + u * coordA d e w :=
          DirectionParityLemmas.coordA_affine d e v w u
  let coordB_affine (d e v w : Real × Real) (u : Real) :
      coordB d e (v + u • (w-v)) = (1-u) * coordB d e v + u * coordB d e w :=
          DirectionParityLemmas.coordB_affine d e v w u
  let coordA_scale (d e : Real × Real) (hD : det2 d e ≠ 0) (t : Real) :
      coordA d e (t • d) = t := DirectionParityLemmas.coordA_scale d e hD t
  let coordB_scale (d e : Real × Real) (hD : det2 d e ≠ 0) (t : Real) :
      coordB d e (t • d) = 0 := DirectionParityLemmas.coordB_scale d e t
  let ray_segment_axes (x d e v w : Real × Real) (hD : det2 d e ≠ 0) :
      (∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real v w) ↔
      (∃ u : Real, 0 ≤ u ∧ u ≤ 1 ∧
        (1-u) * coordB d e (v-x) + u * coordB d e (w-x) = 0 ∧
        0 < (1-u) * coordA d e (v-x) + u * coordA d e (w-x)) :=
            DirectionParityLemmas.ray_segment_axes basis_coordinates coordA_affine coordB_affine
            coordA_scale coordB_scale x d e v w hD
  let cyclicSucc (m : Nat) : Fin (m+1) ≃ Fin (m+1) := {
    toFun := fun i => ⟨(i.val + 1) % (m+1), Nat.mod_lt _ (by omega)⟩
    invFun := fun i => ⟨(i.val + m) % (m+1), Nat.mod_lt _ (by omega)⟩
    left_inv := by
      intro i
      apply Fin.ext
      change (((i.val + 1) % (m+1) + m) % (m+1)) = i.val
      by_cases hi : i.val = m
      · simp [hi]
      · have him : i.val < m := by omega
        have hinner : (i.val + 1) % (m+1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hinner]
        have heq : i.val + 1 + m = (m+1) + i.val := by omega
        rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
        simp [Nat.mod_eq_of_lt i.isLt]
    right_inv := by
      intro i
      apply Fin.ext
      change (((i.val + m) % (m+1) + 1) % (m+1)) = i.val
      by_cases hi : i.val = 0
      · simp [hi]
      · have heq : i.val + m = (m+1) + (i.val-1) := by omega
        have hmod : (i.val + m) % (m+1) = i.val - 1 := by
          have hmodi : (i.val-1) % (m+1) = i.val-1 := Nat.mod_eq_of_lt (by omega)
          rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
          simp [hmodi]
        rw [hmod]
        have hlt : i.val - 1 + 1 < m+1 := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
  }
  let cyclicSucc_eq_add {m : Nat} (i : Fin (m+1)) : cyclicSucc m i = i + 1 :=
      DirectionParityLemmas.cyclicSucc_eq_add (m := m) i
  let cyclic_xor_count {m : Nat} (P Q : Fin (m+1) → Prop)
      [DecidablePred P] [DecidablePred Q] (b : Fin (m+1) → Bool)
      (hxor : ∀ i, (P i ∧ ¬ Q i ∨ ¬ P i ∧ Q i) ↔
        b i ≠ b (cyclicSucc m i)) :
      (Finset.univ.filter P).card % 2 = (Finset.univ.filter Q).card % 2 :=
          DirectionParityLemmas.cyclic_xor_count (m := m) P Q b hxor
  let affine_root_between (a c : Real) (hac : a*c < 0) :
      ∃ u, 0 < u ∧ u < 1 ∧ (1-u)*a+u*c=0 := DirectionParityLemmas.affine_root_between a c hac
  let axis_root_x_identity (a b c d u : Real)
      (hy : (1-u)*b+u*d=0) :
      (d-b)*((1-u)*a+u*c)=a*d-b*c := DirectionParityLemmas.axis_root_x_identity a b c d u hy
  let axis_root_y_identity (a b c d u : Real)
      (hx : (1-u)*a+u*c=0) :
      (a-c)*((1-u)*b+u*d)=a*d-b*c := DirectionParityLemmas.axis_root_y_identity a b c d u hx
  let affine_pos (a c u : Real) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
      (ha : 0 < a) (hc : 0 < c) : 0 < (1-u)*a+u*c := DirectionParityLemmas.affine_pos a c u hu0
          hu1 ha hc
  let affine_neg (a c u : Real) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
      (ha : a < 0) (hc : c < 0) : (1-u)*a+u*c < 0 := DirectionParityLemmas.affine_neg a c u hu0
          hu1 ha hc
  let root_positive_product (e z K : Real) (he : e ≠ 0) (h : e*z=K) :
      0 < z ↔ 0 < K*e := DirectionParityLemmas.root_positive_product e z K he h
  let affine_axis_crossing_iff (a b c d : Real) (hb : b ≠ 0) (hd : d ≠ 0) :
      (∃ u, 0 ≤ u ∧ u ≤ 1 ∧ (1-u)*b+u*d=0 ∧ 0<(1-u)*a+u*c) ↔
        b*d<0 ∧ 0<(a*d-b*c)*(d-b) := DirectionParityLemmas.affine_axis_crossing_iff
            affine_root_between affine_pos affine_neg root_positive_product a b c d hb hd
  let cone_crossing_accounting (a b c d K : Real)
      (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
      (hK : K ≠ 0) (hKeq : K = a*d-b*c) :
      (((0<a ∧ 0<b) ↔ (0<c ∧ 0<d)) ↔
        ((b*d<0 ∧ 0<K*(d-b)) ↔ (a*c<0 ∧ 0<K*(a-c)))) :=
            DirectionParityLemmas.cone_crossing_accounting a b c d K ha hb hc hd hK hKeq
  let cone_crossing_accounting_collinear (a b c d : Real)
      (hac : 0 < a*c) (hbd : 0 < b*d) :
      (((0<a ∧ 0<b) ↔ (0<c ∧ 0<d)) ↔
        ((b*d<0 ∧ 0<(0:Real)*(d-b)) ↔ (a*c<0 ∧ 0<(0:Real)*(a-c)))) :=
            DirectionParityLemmas.cone_crossing_accounting_collinear a b c d hac hbd
  let axis_parity_from_no_origin {m : Nat} (A B : Fin (m+1) → Real)
      (hA : ∀ i, A i ≠ 0) (hB : ∀ i, B i ≠ 0)
      (hno : ∀ i u, u ∈ Set.Icc (0:Real) 1 →
        (1-u)*A i + u*A (cyclicSucc m i) = 0 →
        (1-u)*B i + u*B (cyclicSucc m i) = 0 → False) :
      (Finset.univ.filter (fun i =>
        B i * B (cyclicSucc m i) < 0 ∧
          0 < (A i * B (cyclicSucc m i) - B i * A (cyclicSucc m i)) *
            (B (cyclicSucc m i) - B i))).card % 2 =
      (Finset.univ.filter (fun i =>
        A i * A (cyclicSucc m i) < 0 ∧
          0 < (A i * B (cyclicSucc m i) - B i * A (cyclicSucc m i)) *
            (A i - A (cyclicSucc m i)))).card % 2 :=
                DirectionParityLemmas.axis_parity_from_no_origin cyclic_xor_count
                affine_root_between axis_root_x_identity axis_root_y_identity
                cone_crossing_accounting cone_crossing_accounting_collinear (m := m) A B hA hB hno
  let coordinate_hit_d (x d e v w : Real × Real)
      (hD : det2 d e ≠ 0)
      (hb : coordB d e (v-x) ≠ 0) (hd : coordB d e (w-x) ≠ 0) :
      (∃ t : Real, 0<t ∧ x+t • d ∈ segment Real v w) ↔
        coordB d e (v-x) * coordB d e (w-x) < 0 ∧
        0 < (coordA d e (v-x)*coordB d e (w-x) -
          coordB d e (v-x)*coordA d e (w-x)) *
          (coordB d e (w-x)-coordB d e (v-x)) := DirectionParityLemmas.coordinate_hit_d
              ray_segment_axes affine_axis_crossing_iff x d e v w hD hb hd
  let coordinate_hit_e (x d e v w : Real × Real)
      (hD : det2 d e ≠ 0)
      (ha : coordA d e (v-x) ≠ 0) (hc : coordA d e (w-x) ≠ 0) :
      (∃ t : Real, 0<t ∧ x+t • e ∈ segment Real v w) ↔
        coordA d e (v-x) * coordA d e (w-x) < 0 ∧
        0 < (coordA d e (v-x)*coordB d e (w-x) -
          coordB d e (v-x)*coordA d e (w-x)) *
          (coordA d e (v-x)-coordA d e (w-x)) := DirectionParityLemmas.coordinate_hit_e
              coordA_swap coordB_swap ray_segment_axes affine_axis_crossing_iff x d e v w hD ha hc
  let cyclic_direction_parity_nonparallel {m : Nat}
      (v : Fin (m+1) → Real × Real) (x d e : Real × Real)
      (hD : det2 d e ≠ 0)
      (hx : ∀ i, x ∉ segment Real (v i) (v (cyclicSucc m i)))
      (hdv : ∀ i, det2 d (v i-x) ≠ 0)
      (hev : ∀ i, det2 e (v i-x) ≠ 0) :
      Set.ncard {i : Fin (m+1) | ∃ t : Real, 0<t ∧
        x+t • d ∈ segment Real (v i) (v (cyclicSucc m i))} % 2 =
      Set.ncard {i : Fin (m+1) | ∃ t : Real, 0<t ∧
        x+t • e ∈ segment Real (v i) (v (cyclicSucc m i))} % 2 :=
            DirectionParityLemmas.cyclic_direction_parity_nonparallel basis_coordinates
            coordA_affine coordB_affine axis_parity_from_no_origin coordinate_hit_d
            coordinate_hit_e (m := m) v x d e hD hx hdv hev
  let choose_common_generic {n : Nat} (p : P3381T1PolygonBoundary n)
      (x d e : Real × Real) (hx : x ∉ P3544T1BoundaryCarrier p)
      (hd : d ≠ 0) (he : e ≠ 0) :
      ∃ f : Real × Real,
        (∀ i, det2 f (p.vertex i-x) ≠ 0) ∧
        (∀ i, det2 f (p.vertex (i+1)-p.vertex i) ≠ 0) ∧
        det2 f d ≠ 0 ∧ det2 f e ≠ 0 := DirectionParityLemmas.choose_common_generic (n := n) p x d
            e hx hd he
  let m := n+2
  let v : Fin (m+1) → Real × Real := p.vertex
  have hcyc (i : Fin (m+1)) : cyclicSucc m i = i+1 := DirectionParityLemmas.hcyc n
      cyclicSucc_eq_add i
  have hxseg : ∀ i, x ∉ segment Real (v i) (v (cyclicSucc m i)) := DirectionParityLemmas.hxseg n
      p x hx hcyc
  have hdv0 : ∀ i, det2 d (v i-x) ≠ 0 := DirectionParityLemmas.hdv0 n p x d hdv
  have hdv'0 : ∀ i, det2 d' (v i-x) ≠ 0 := DirectionParityLemmas.hdv'0 n p x d' hdv'
  have hdn : d ≠ 0 := DirectionParityLemmas.hdn n p x d hdv0
  have hd'n : d' ≠ 0 := DirectionParityLemmas.hd'n n p x d' hdv'0
  by_cases hD : det2 d d' ≠ 0
  · simpa [v, hcyc] using cyclic_direction_parity_nonparallel
      (m := m) v x d d' hD hxseg hdv0 hdv'0
  · obtain ⟨f, hfv, hfe, hfd, hfd'⟩ := choose_common_generic p x d d' hx hdn hd'n
    have hdf : det2 d f ≠ 0 := by
      intro hz
      apply hfd
      have hs : det2 f d = -det2 d f := by dsimp [det2]; ring
      rw [hs, hz]
      simp
    have hd'f : det2 d' f ≠ 0 := by
      intro hz
      apply hfd'
      have hs : det2 f d' = -det2 d' f := by dsimp [det2]; ring
      rw [hs, hz]
      simp
    have h1 := cyclic_direction_parity_nonparallel
      (m := m) v x d f hdf hxseg hdv0 (by simpa [det2] using hfv)
    have h2 := cyclic_direction_parity_nonparallel
      (m := m) v x d' f hd'f hxseg hdv'0 (by simpa [det2] using hfv)
    simpa [v, hcyc] using h1.trans h2.symm

end ApollonianSuperharmonic

end
