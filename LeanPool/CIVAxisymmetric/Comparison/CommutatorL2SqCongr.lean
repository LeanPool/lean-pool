/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.ComparisonLimits
public import LeanPool.CIVAxisymmetric.Comparison.CommutatorL2SqNonneg

/-!
# Commutator L2 Sq Congr

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open CKN


noncomputable section

namespace CIV

/-- The DiPerna–Lions commutator is unchanged when the transported function `g` is replaced
by an a.e.-equal representative on a single spatial slice. -/
theorem diPernaLionsCommutator_congr_ae_slice {m : ℕ} {ε : ℝ} {b : Vec m → Vec m}
    {divb g g' : Vec m → ℝ} (h : g =ᵐ[volume] g') (x : Vec m) :
    diPernaLionsCommutator m ε b divb g x = diPernaLionsCommutator m ε b divb g' x := by
  unfold diPernaLionsCommutator
  have h1 : (∫ y : Vec m, g y *
        ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      = ∫ y : Vec m, g' y *
        ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) :=
    integral_congr_ae (h.mono fun y hy => by simp only [hy])
  have h2 : (∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y))
      = ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g' y) :=
    integral_congr_ae (h.mono fun y hy => by simp only [hy])
  rw [h1, h2]

/-- The squared `L²` mass on a ball of the DiPerna–Lions commutator is unchanged when the
transported function `q` is replaced by an a.e.-equal representative on a single time slice. -/
theorem commutatorL2Sq_congr_ae_slice {m : ℕ} {ε Rb s : ℝ} {B : Vec m × ℝ → Vec m}
    {divB q q' : Vec m × ℝ → ℝ}
    (h : (fun y : Vec m => q (y, s)) =ᵐ[volume] (fun y : Vec m => q' (y, s))) :
    commutatorL2Sq m ε Rb B divB q s = commutatorL2Sq m ε Rb B divB q' s := by
  unfold commutatorL2Sq
  refine setIntegral_congr_fun measurableSet_closedBall (fun x hx => ?_)
  have hx' := diPernaLionsCommutator_congr_ae_slice (b := fun y => B (y, s))
    (divb := fun y => divB (y, s)) (ε := ε) h x
  simp only [sq]
  rw [hx']

/-- The square root of the squared `L²` mass of the commutator is unchanged when the
transported function `q` is replaced by an a.e.-equal representative on a single time slice. -/
theorem sqrt_commutatorL2Sq_congr_ae_slice {m : ℕ} {ε Rb s : ℝ} {B : Vec m × ℝ → Vec m}
    {divB q q' : Vec m × ℝ → ℝ}
    (h : (fun y : Vec m => q (y, s)) =ᵐ[volume] (fun y : Vec m => q' (y, s))) :
    Real.sqrt (commutatorL2Sq m ε Rb B divB q s)
      = Real.sqrt (commutatorL2Sq m ε Rb B divB q' s) := by
  rw [commutatorL2Sq_congr_ae_slice h]

/-- The squared `L²` mass of the commutator is equal on a set `S` whenever `q` and `q'` agree
a.e. on every slice `s ∈ S`. -/
theorem commutatorL2Sq_eqOn_of_forall_ae_slice {m : ℕ} {ε Rb : ℝ} {S : Set ℝ}
    {B : Vec m × ℝ → Vec m} {divB q q' : Vec m × ℝ → ℝ}
    (h : ∀ s ∈ S, (fun y : Vec m => q (y, s)) =ᵐ[volume] (fun y : Vec m => q' (y, s))) :
    EqOn (fun s => commutatorL2Sq m ε Rb B divB q s)
      (fun s => commutatorL2Sq m ε Rb B divB q' s) S := by
  intro s hs
  exact commutatorL2Sq_congr_ae_slice (h s hs)

/-- If the square root of the commutator mass for `q'` is continuous on `S`, then so is it
for any `q` that agrees with `q'` a.e. on each slice in `S`. -/
theorem continuousOn_sqrt_commutatorL2Sq_congr {m : ℕ} {ε Rb : ℝ} {S : Set ℝ}
    {B : Vec m × ℝ → Vec m} {divB q q' : Vec m × ℝ → ℝ}
    (h : ∀ s ∈ S, (fun y : Vec m => q (y, s)) =ᵐ[volume] (fun y : Vec m => q' (y, s)))
    (hcont : ContinuousOn (fun s => Real.sqrt (commutatorL2Sq m ε Rb B divB q' s)) S) :
    ContinuousOn (fun s => Real.sqrt (commutatorL2Sq m ε Rb B divB q s)) S := by
  have heq : EqOn (fun s => Real.sqrt (commutatorL2Sq m ε Rb B divB q s))
      (fun s => Real.sqrt (commutatorL2Sq m ε Rb B divB q' s)) S := by
    intro s hs
    exact sqrt_commutatorL2Sq_congr_ae_slice (h s hs)
  exact hcont.congr heq

end CIV
