/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Functions

/-!
The real covering space and its quotient by the physical angle lattice.
-/

@[expose] public section
noncomputable section
open Set
namespace KamProject.Arnold1963

/-- Real action coordinates paired with unwrapped real angles. -/
abbrev RealPhaseCover (n : ℕ) := RealSpace n × RealSpace n

/-- Complexification of both real action and unwrapped angle coordinates. -/
def complexifyPhase {n : ℕ} (x : RealPhaseCover n) : ComplexPhaseSpace n :=
  (complexify x.1, complexify x.2)

/-- Real-part projection of complex action and angle coordinates. -/
def realPartPhase {n : ℕ} (x : ComplexPhaseSpace n) : RealPhaseCover n :=
  (realPart x.1, realPart x.2)

@[simp] theorem realPartPhase_complexifyPhase {n : ℕ} (x : RealPhaseCover n) :
    realPartPhase (complexifyPhase x) = x := by simp [realPartPhase, complexifyPhase]

theorem conjPhase_complexifyPhase {n : ℕ} (x : RealPhaseCover n) :
    conjPhase (complexifyPhase x) = complexifyPhase x := by simp [conjPhase, complexifyPhase]

theorem complexify_realPart_of_conj {n : ℕ} {z : ComplexSpace n} (h : conjVec z = z) :
    complexify (realPart z) = z := by
  funext j
  apply Complex.ext
  · rfl
  · have hh := congrArg (fun v : ComplexSpace n => (v j).im) h
    simp only [conjVec, Complex.star_def, Complex.conj_im] at hh
    change 0 = (z j).im
    linarith

theorem complexifyPhase_realPartPhase_of_conj {n : ℕ} {z : ComplexPhaseSpace n}
    (h : conjPhase z = z) : complexifyPhase (realPartPhase z) = z := by
  exact Prod.ext (complexify_realPart_of_conj (congrArg Prod.fst h))
    (complexify_realPart_of_conj (congrArg Prod.snd h))

/-- The real angle shift corresponding to integer multiples of the period. -/
def realAngleShift {n : ℕ} (k : FourierIndex n) : RealSpace n :=
  fun j => 2 * Real.pi * (k j : ℝ)

/-- Translation of unwrapped real phase space by an integer angle-period shift. -/
def realPhaseShift {n : ℕ} (k : FourierIndex n) (x : RealPhaseCover n) : RealPhaseCover n :=
  (x.1, x.2 + realAngleShift k)

/-- Projection from unwrapped real angles to angles modulo `2π`. -/
def torusProjection {n : ℕ} (x : RealPhaseCover n) : RealPhaseSpace n :=
  (x.1, fun j => (x.2 j : AddCircle (2 * Real.pi)))

@[simp] theorem torusProjection_shift {n : ℕ} (k : FourierIndex n) (x : RealPhaseCover n) :
    torusProjection (realPhaseShift k x) = torusProjection x := by
  apply Prod.ext
  · rfl
  funext j
  change ((x.2 j + 2 * Real.pi * (k j : ℝ) : ℝ) : AddCircle (2 * Real.pi)) = _
  rw [AddCircle.coe_add]
  have hh : ((2 * Real.pi * (k j : ℝ) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff _).2
    exact ⟨k j, by simp [zsmul_eq_mul, mul_comm]⟩
  rw [hh, add_zero]
  rfl

theorem torusProjection_eq_iff {n : ℕ} (x y : RealPhaseCover n) :
    torusProjection x = torusProjection y ↔ ∃ k : FourierIndex n, x = realPhaseShift k y := by
  constructor
  · intro he
    have hp := congrArg Prod.fst he
    change x.1 = y.1 at hp
    have hq : ∀ j, ∃ m : ℤ, m • (2 * Real.pi) = x.2 j - y.2 j := by
      intro j
      apply (AddCircle.coe_eq_zero_iff _).1
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact congrArg (fun z : RealPhaseSpace n => z.2 j) he
    choose k hk using hq
    refine ⟨k, Prod.ext hp ?_⟩
    funext j
    have hh := hk j
    simp only [zsmul_eq_mul] at hh
    change x.2 j = y.2 j + 2 * Real.pi * (k j : ℝ)
    linarith
  · rintro ⟨k, rfl⟩
    exact torusProjection_shift k y

local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- Representatives of real torus angles in the fundamental interval `(0, 2π]`. -/
def torusRepresentative {n : ℕ} (x : RealPhaseSpace n) : RealPhaseCover n :=
  (x.1, fun j => (AddCircle.equivIoc (2 * Real.pi) 0 (x.2 j) : ℝ))

@[simp] theorem torusProjection_representative {n : ℕ} (x : RealPhaseSpace n) :
    torusProjection (torusRepresentative x) = x := by
  apply Prod.ext
  · rfl
  funext j
  exact AddCircle.coe_equivIoc

end KamProject.Arnold1963
