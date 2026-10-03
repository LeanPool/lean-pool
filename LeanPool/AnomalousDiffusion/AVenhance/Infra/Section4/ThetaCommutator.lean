/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Product
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! First-order transport commutator identities for smooth Euclidean fields. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section4

/-- The scalar transport term associated with a vector field and a scalar function. -/
def classicalTransport (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  Homogenization.vecDot (b x) (AVenhance.spaceGrad u x)

/-- Coordinate derivative of a product of two smooth scalar functions. -/
theorem classicalProduct_firstDerivative (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y * g y) x i =
      f x * AVenhance.spaceGrad g x i + AVenhance.spaceGrad f x i * g x := by
  change fderiv ℝ (fun y => f y * g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, AVenhance.spaceGrad]
  ring

/-- Coordinate derivative commutes with subtraction for smooth scalar functions. -/
theorem classicalSpaceGrad_sub (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y - g y) x i =
      AVenhance.spaceGrad f x i - AVenhance.spaceGrad g x i := by
  change fderiv ℝ (fun y => f y - g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem ThetaCommutator.classicalSpaceGrad_contDiff (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad f x i) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem ThetaCommutator.classicalTransport_contDiff (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.1 hb) j).mul (ThetaCommutator.classicalSpaceGrad_contDiff u hu j)

/-- An ordered word of coordinate derivatives applied to a scalar function. -/
def classicalWordDerivative : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ
  | [], f => f
  | i :: w, f => fun x => AVenhance.spaceGrad (classicalWordDerivative w f) x i

theorem classicalWordDerivative_contDiff (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w f) := by
  induction w generalizing f hf with
  | nil => exact hf
  | cons i w ih =>
    exact ThetaCommutator.classicalSpaceGrad_contDiff (classicalWordDerivative w f) (ih f hf) i

/-- Coordinate directions of a spatial derivative word indexed by its length. -/
def ThetaCommutator.thetaWordDirections (w : List (Fin 2)) : Fin w.length → Fin 2 :=
  fun j => w.get j

/-- The ordered-word convention agrees with iterated Fréchet differentiation
on the corresponding ordered coordinate directions. -/
theorem thetaWordDerivative_eq_iteratedFDeriv (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    classicalWordDerivative w f x =
      iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j)) := by
  induction w generalizing f hf x with
  | nil =>
      simp [classicalWordDerivative, ThetaCommutator.thetaWordDirections]
  | cons i w ih =>
      have hcont : ContDiff ℝ (w.length + 1) f := hf.of_le (by simp)
      have hn : (w.length : ℕ∞) < (w.length : ℕ∞) + 1 :=
        (ENat.lt_add_one_iff (by simp)).2 le_rfl
      have hn' : (w.length : WithTop ℕ∞) < (w.length : WithTop ℕ∞) + 1 := by
        simpa using (WithTop.coe_lt_coe.mpr hn)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length f) x :=
        (hcont.differentiable_iteratedFDeriv hn') x
      let I : Fin (w.length + 1) → Fin 2 := fun j => (i :: w).get j
      have hIzero : I 0 = i := by simp [I]
      have hIsucc (j : Fin w.length) : I j.succ = ThetaCommutator.thetaWordDirections w j := by
        simp [I, ThetaCommutator.thetaWordDirections]
      have htailFun : classicalWordDerivative w f =
          (fun y => iteratedFDeriv ℝ w.length f y
            (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j))) := by
        funext y
        exact ih f hf y
      have htailDirs :
          (fun j : Fin w.length => Homogenization.basisVec
            (ThetaCommutator.thetaWordDirections w j)) =
          (fun j => Homogenization.basisVec (I j.succ)) := by
        funext j
        rw [hIsucc]
      have hstep := AVenhance.Infra.Section4.ordered_derivative_eq_gradient_component
        (i := I) hdiff
      have hstep' := hstep
      rw [hIzero] at hstep'
      calc
        classicalWordDerivative (i :: w) f x =
            AVenhance.spaceGrad (classicalWordDerivative w f) x i := rfl
        _ = AVenhance.spaceGrad
            (fun y => iteratedFDeriv ℝ w.length f y
              (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j))) x i :=
                  by
              rw [htailFun]
        _ = iteratedFDeriv ℝ (w.length + 1) f x
            (fun j => Homogenization.basisVec (I j)) := by
              rw [htailDirs]
              exact hstep'.symm
        _ = iteratedFDeriv ℝ (List.length (i :: w)) f x
            (fun j => Homogenization.basisVec
              (ThetaCommutator.thetaWordDirections (i :: w) j)) := by
              simp [ThetaCommutator.thetaWordDirections, I]

/-- The ordered derivative identification with the tuple written using
`List.get`, for hypotheses quantified over all coordinate tuples. -/
theorem thetaWordDerivative_eq_iteratedFDeriv_get (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    classicalWordDerivative w f x =
      iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (w.get j)) := by
  calc
    _ = iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j)) :=
      thetaWordDerivative_eq_iteratedFDeriv w f hf x
    _ = iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (w.get j)) := by
      congr 1

/-- Negation passes through an ordered word of spatial derivatives. -/
theorem classicalWordDerivative_neg (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    classicalWordDerivative w (fun x => -f x) =
      fun x => -classicalWordDerivative w f x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      have htail := classicalWordDerivative_contDiff w f hf
      funext x
      change AVenhance.spaceGrad
          (classicalWordDerivative w (fun y => -f y)) x i =
        -AVenhance.spaceGrad (classicalWordDerivative w f) x i
      rw [ih]
      have h := classicalSpaceGrad_sub (fun _ : Vec 2 => (0 : ℝ))
        (classicalWordDerivative w f) contDiff_const htail i x
      simp [AVenhance.spaceGrad]

/-- Coordinate bounds for all order-`n` Fréchet derivatives immediately give
the same bound for each ordered coordinate word. -/
theorem classicalWordDerivative_abs_le_of_iteratedFDeriv
    (w : List (Fin 2)) (f : Vec 2 → ℝ) (B : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ i : Fin w.length → Fin 2, ∀ x : Vec 2,
      ‖iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (i j))‖ ≤ B) :
    ∀ x : Vec 2, |classicalWordDerivative w f x| ≤ B := by
  intro x
  rw [thetaWordDerivative_eq_iteratedFDeriv w f hf x]
  simpa [Real.norm_eq_abs] using hbound (ThetaCommutator.thetaWordDirections w) x

/-- Smooth mixed coordinate derivatives commute. -/
theorem classicalSpaceGrad_commute (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x i =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x j := by
  let g : Vec 2 → Vec 2 →L[ℝ] ℝ := fun y => fderiv ℝ f y
  have hfirst (y : Vec 2) : HasFDerivAt f (fderiv ℝ f y) y :=
    (hf.differentiable (by simp) y).hasFDerivAt
  have hsecond : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    exact hf.fderiv_right (by simp)
  have hsecond' (y : Vec 2) : HasFDerivAt g (fderiv ℝ g y) y :=
    (hsecond.differentiable (by simp) y).hasFDerivAt
  have hsymmetric := second_derivative_symmetric hfirst (hsecond' x)
    (Homogenization.basisVec i) (Homogenization.basisVec j)
  have hleft : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y j) x i =
        fderiv ℝ g x (Homogenization.basisVec i) (Homogenization.basisVec j) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (Homogenization.basisVec j)) x
      (Homogenization.basisVec i) = _
    rw [fderiv_clm_apply (hsecond.differentiable (by simp) x) (by fun_prop)]
    simp [g]
  have hright : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y i) x j =
        fderiv ℝ g x (Homogenization.basisVec j) (Homogenization.basisVec i) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (Homogenization.basisVec i)) x
      (Homogenization.basisVec j) = _
    rw [fderiv_clm_apply (hsecond.differentiable (by simp) x) (by fun_prop)]
    simp [g]
  rw [hleft, hright]
  exact hsymmetric

/-- Smooth ordered coordinate derivatives depend only on the multiset of
directions.  This lets a one-derivative Leibniz split be identified with one
coordinate of the gradient of the complementary word. -/
theorem classicalWordDerivative_eq_of_perm (w v : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (h : w.Perm v) :
    classicalWordDerivative w f = classicalWordDerivative v f := by
  induction h with
  | nil => rfl
  | @cons i w v h ih =>
      funext x
      change AVenhance.spaceGrad (classicalWordDerivative w f) x i =
        AVenhance.spaceGrad (classicalWordDerivative v f) x i
      rw [ih]
  | swap i j w =>
      funext x
      change AVenhance.spaceGrad
          (fun y => AVenhance.spaceGrad (classicalWordDerivative w f) y i) x j =
        AVenhance.spaceGrad
          (fun y => AVenhance.spaceGrad (classicalWordDerivative w f) y j) x i
      exact classicalSpaceGrad_commute (classicalWordDerivative w f)
        (classicalWordDerivative_contDiff w f hf) j i x
  | @trans w v z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A coordinate derivative can be moved through an arbitrary ordered word of smooth coordinate
derivatives. -/
theorem classicalWordDerivative_commute_gradient (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 2) :
    classicalWordDerivative w (fun y => AVenhance.spaceGrad f y j) =
      fun x => AVenhance.spaceGrad (classicalWordDerivative w f) x j := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hrest := ih
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => AVenhance.spaceGrad f y j)) x i = _
    rw [hrest]
    exact classicalSpaceGrad_commute (classicalWordDerivative w f)
      (classicalWordDerivative_contDiff w f hf) i j x

/-- Coordinate derivative of a sum of smooth scalar functions. -/
theorem classicalSpaceGrad_add (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y + g y) x i =
      AVenhance.spaceGrad f x i + AVenhance.spaceGrad g x i := by
  change fderiv ℝ (fun y => f y + g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem classicalContDiff_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) L.sum := by
  induction L with
  | nil =>
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (0 : ℝ))
    exact contDiff_const
  | cons f L ih =>
    have hf := hL f (by simp)
    have htail : ∀ g ∈ L, ContDiff ℝ (⊤ : ℕ∞) g := by
      intro g hg
      exact hL g (by simp [hg])
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => f y + L.sum y)
    exact hf.add (ih htail)

theorem classicalSpaceGrad_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad L.sum x i = (L.map fun f => AVenhance.spaceGrad f x i).sum := by
  induction L with
  | nil => simp [AVenhance.spaceGrad]
  | cons f L ih =>
    have hf := hL f (by simp)
    have htail : ∀ g ∈ L, ContDiff ℝ (⊤ : ℕ∞) g := by
      intro g hg
      exact hL g (by simp [hg])
    change AVenhance.spaceGrad (fun y => f y + L.sum y) x i = _
    rw [classicalSpaceGrad_add f L.sum hf (classicalContDiff_listSum L htail) i x,
      ih htail]
    simp

/-- All ways of distributing an ordered derivative word between two factors. -/
def classicalWordSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | i :: w =>
      (classicalWordSplits w).map (fun p => (i :: p.1, p.2)) ++
      (classicalWordSplits w).map (fun p => (p.1, i :: p.2))

/-- The product term attached to one split of a derivative word. -/
def classicalWordProductTerm (p : List (Fin 2) × List (Fin 2))
    (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun x => classicalWordDerivative p.1 f x * classicalWordDerivative p.2 g x

/-- Leibniz expansion of an ordered word of coordinate derivatives. -/
def classicalWordProductExpansion (w : List (Fin 2)) (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  ((classicalWordSplits w).map fun p => classicalWordProductTerm p f g).sum

/-- The derivative splits with at least one derivative assigned to the first factor. -/
def classicalWordCommutatorSplits : List (Fin 2) →
    List (List (Fin 2) × List (Fin 2))
  | [] => []
  | i :: w =>
      (classicalWordSplits w).map (fun p => (i :: p.1, p.2)) ++
      (classicalWordCommutatorSplits w).map (fun p => (p.1, i :: p.2))

theorem ThetaCommutator.classicalPerm_move_head (i : Fin 2) (u v : List (Fin 2)) :
    (i :: u ++ v).Perm (u ++ i :: v) := by
  induction u with
  | nil => simp
  | cons j u ih =>
      exact (List.Perm.swap j i (u ++ v)).trans (List.Perm.cons j ih)

/-- Every Leibniz split preserves the complete ordered derivative word up to
permutation. -/
theorem classicalWordSplits_perm_append (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordSplits w) :
    w.Perm (p.1 ++ p.2) := by
  induction w generalizing p with
  | nil =>
      simp only [classicalWordSplits, List.mem_singleton] at hp
      subst p
      exact List.Perm.nil
  | cons i w ih =>
      simp only [classicalWordSplits, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have h := ih hq
        simpa using List.Perm.cons i h
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have h := ih hq
        have hc := List.Perm.cons i h
        exact hc.trans (ThetaCommutator.classicalPerm_move_head i q.1 q.2)

/-- The same shuffle invariant holds after the zero-derivative-on-drift term
is removed from the transport commutator. -/
theorem classicalWordCommutatorSplits_perm_append (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)}
    (hp : p ∈ classicalWordCommutatorSplits w) :
    w.Perm (p.1 ++ p.2) := by
  induction w generalizing p with
  | nil => simp [classicalWordCommutatorSplits] at hp
  | cons i w ih =>
      simp only [classicalWordCommutatorSplits, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact (classicalWordSplits_perm_append w hq).cons i
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have h := ih hq
        exact (List.Perm.cons i h).trans (ThetaCommutator.classicalPerm_move_head i q.1 q.2)

/-- The order-`n` derivative in a split with one derivative on the stream
potential is itself a coordinate of the gradient of the complementary
order-`n-1` derivative. -/
theorem classicalWordDerivative_sq_le_gradient_of_perm
    (w v : List (Fin 2)) (i : Fin 2) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2)
    (hperm : w.Perm (i :: v)) :
    (classicalWordDerivative w f x) ^ 2 ≤
      Homogenization.vecNormSq
        (AVenhance.spaceGrad (classicalWordDerivative v f) x) := by
  rw [classicalWordDerivative_eq_of_perm w (i :: v) f hf hperm]
  exact Homogenization.sq_apply_le_vecNormSq
    (AVenhance.spaceGrad (classicalWordDerivative v f) x) i

/-- Specialization of the coordinate estimate to a commutator split with one
derivative on its first factor. -/
theorem classicalWordDerivative_sq_le_gradient_of_first_order_split
    (w : List (Fin 2)) (p : List (Fin 2) × List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2)
    (hp : p ∈ classicalWordCommutatorSplits w)
    (hq : p.1.length = 1) :
    classicalWordDerivative w f x ^ 2 ≤
      Homogenization.vecNormSq
        (AVenhance.spaceGrad (classicalWordDerivative p.2 f) x) := by
  rcases p with ⟨left, right⟩
  cases left with
  | nil => simp at hq
  | cons i left =>
      cases left with
      | nil =>
          have hperm := classicalWordCommutatorSplits_perm_append w hp
          have hperm' : w.Perm (i :: right) := by simpa using hperm
          exact classicalWordDerivative_sq_le_gradient_of_perm
            w right i f hf x hperm'
      | cons j rest => simp at hq

/-- The full Leibniz split list contains `choose n q` occurrences with exactly
`q` derivatives on its first factor, including multiplicities for repeated
coordinate directions. -/
theorem classicalWordSplits_leftLength_count (w : List (Fin 2)) (q : ℕ) :
    ((classicalWordSplits w).filter (fun p => p.1.length = q)).length =
      w.length.choose q := by
  induction w generalizing q with
  | nil =>
      cases q <;> simp [classicalWordSplits]
  | cons i w ih =>
      cases q with
      | zero =>
          simpa [classicalWordSplits, List.filter_map, Function.comp_def,
            List.length_eq_zero_iff] using (ih 0)
      | succ q =>
          simp [classicalWordSplits, List.filter_map, Function.comp_def, ih,
            Nat.choose_succ_succ]

/-- The transport commutator split list has the same binomial multiplicities,
with the zero-derivative-on-drift split removed. -/
theorem classicalWordCommutatorSplits_leftLength_count
    (w : List (Fin 2)) (q : ℕ) :
    ((classicalWordCommutatorSplits w).filter
      (fun p => p.1.length = q)).length =
      if q = 0 then 0 else w.length.choose q := by
  induction w generalizing q with
  | nil =>
      cases q <;> simp [classicalWordCommutatorSplits]
  | cons i w ih =>
      cases q with
      | zero =>
          simpa [classicalWordCommutatorSplits, List.filter_map,
            Function.comp_def, List.length_eq_zero_iff] using (ih 0)
      | succ q =>
          simp [classicalWordCommutatorSplits, List.filter_map, Function.comp_def,
            classicalWordSplits_leftLength_count, ih,
            Nat.choose_succ_succ]

theorem classicalWordSplits_length (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordSplits w) :
    p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil =>
    simp only [classicalWordSplits, List.mem_singleton] at hp
    subst p
    simp
  | cons i w ih =>
    simp only [classicalWordSplits, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := ih hq
      simp only [List.length_cons]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := ih hq
      simp only [List.length_cons]
      omega

theorem classicalWordCommutatorSplits_length (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil => simp [classicalWordCommutatorSplits] at hp
  | cons i w ih =>
    simp only [classicalWordCommutatorSplits, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := classicalWordSplits_length w hq
      simp only [List.length_cons]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := ih hq
      simp only [List.length_cons]
      omega

theorem classicalWordCommutatorSplits_left_ne_nil (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.1 ≠ [] := by
  induction w generalizing p with
  | nil => simp [classicalWordCommutatorSplits] at hp
  | cons i w ih =>
    simp only [classicalWordCommutatorSplits, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih (p := q) hq

theorem classicalWordCommutatorSplits_right_length_lt (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.2.length < w.length := by
  have hlen := classicalWordCommutatorSplits_length w hp
  have hleft : 0 < p.1.length := by
    cases h : p.1 with
    | nil => exact (classicalWordCommutatorSplits_left_ne_nil w hp h).elim
    | cons a L => simp
  omega

/-- The finite Leibniz sum over splits with a nonempty first derivative word. -/
def classicalWordCommutatorExpansion (w : List (Fin 2))
    (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  ((classicalWordCommutatorSplits w).map fun p => classicalWordProductTerm p f g).sum

theorem classicalListSum_eval (L : List (Vec 2 → ℝ)) (x : Vec 2) :
    L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

theorem ThetaCommutator.classicalListSum_map_add {α : Type} (L : List α) (f g : α → ℝ) :
    (L.map fun a => f a + g a).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]; ring

theorem ThetaCommutator.classicalWordProductTerm_contDiff (p : List (Fin 2) × List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordProductTerm p f g) := by
  exact (classicalWordDerivative_contDiff p.1 f hf).mul
    (classicalWordDerivative_contDiff p.2 g hg)

theorem ThetaCommutator.classicalWordProductTerm_firstDerivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordProductTerm p f g) x i =
      classicalWordProductTerm (i :: p.1, p.2) f g x +
        classicalWordProductTerm (p.1, i :: p.2) f g x := by
  rcases p with ⟨u, v⟩
  change AVenhance.spaceGrad
      (fun y => classicalWordDerivative u f y * classicalWordDerivative v g y) x i = _
  rw [classicalProduct_firstDerivative (classicalWordDerivative u f)
    (classicalWordDerivative v g)
    (classicalWordDerivative_contDiff u f hf)
    (classicalWordDerivative_contDiff v g hg) i x]
  simp [classicalWordProductTerm, classicalWordDerivative]
  ring

theorem classicalWordCommutatorExpansion_firstDerivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordCommutatorExpansion w f g) x i =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum +
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (p.1, i :: p.2) f g x).sum := by
  let terms := (classicalWordCommutatorSplits w).map fun p =>
    classicalWordProductTerm p f g
  have hterms : ∀ F ∈ terms, ContDiff ℝ (⊤ : ℕ∞) F := by
    intro F hF
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF
    exact ThetaCommutator.classicalWordProductTerm_contDiff p f g hf hg
  unfold classicalWordCommutatorExpansion
  change AVenhance.spaceGrad terms.sum x i = _
  rw [classicalSpaceGrad_listSum terms hterms i x]
  simp only [terms]
  have hmap :
      (classicalWordCommutatorSplits w).map
          (fun p => AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) =
        (classicalWordCommutatorSplits w).map (fun p =>
          classicalWordProductTerm (i :: p.1, p.2) f g x +
            classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    apply List.map_congr_left
    intro p hp
    exact ThetaCommutator.classicalWordProductTerm_firstDerivative p f g hf hg i x
  have hmap' :
      List.map (fun F => AVenhance.spaceGrad F x i)
          (List.map (fun p => classicalWordProductTerm p f g)
            (classicalWordCommutatorSplits w)) =
        (classicalWordCommutatorSplits w).map (fun p =>
          classicalWordProductTerm (i :: p.1, p.2) f g x +
            classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    rw [List.map_map]
    change (classicalWordCommutatorSplits w).map
        (fun p => AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) = _
    exact hmap
  rw [hmap', ThetaCommutator.classicalListSum_map_add]

theorem ThetaCommutator.classicalWordProductTerm_left_derivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordProductTerm p (fun y => AVenhance.spaceGrad f y i) g x =
      classicalWordProductTerm (i :: p.1, p.2) f g x := by
  rcases p with ⟨u, v⟩
  have hcomm := congrFun (classicalWordDerivative_commute_gradient u f hf i) x
  change classicalWordDerivative u (fun y => AVenhance.spaceGrad f y i) x *
      classicalWordDerivative v g x =
    classicalWordDerivative (i :: u) f x * classicalWordDerivative v g x
  rw [hcomm]
  rfl

theorem ThetaCommutator.classicalWordProductTerm_right_derivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    classicalWordProductTerm p f (fun y => AVenhance.spaceGrad g y i) x =
      classicalWordProductTerm (p.1, i :: p.2) f g x := by
  rcases p with ⟨u, v⟩
  have hcomm := congrFun (classicalWordDerivative_commute_gradient v g hg i) x
  change classicalWordDerivative u f x *
      classicalWordDerivative v (fun y => AVenhance.spaceGrad g y i) x =
    classicalWordDerivative u f x * classicalWordDerivative (i :: v) g x
  rw [hcomm]
  rfl

theorem ThetaCommutator.classicalWordProductExpansion_left_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
      ((classicalWordSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum := by
  unfold classicalWordProductExpansion
  rw [classicalListSum_eval]
  rw [List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  change (classicalWordSplits w).map
      (fun p => classicalWordProductTerm p (fun y => AVenhance.spaceGrad f y i) g x) = _
  apply List.map_congr_left
  intro p hp
  exact ThetaCommutator.classicalWordProductTerm_left_derivative p f g hf i x

theorem ThetaCommutator.classicalWordCommutatorExpansion_left_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum := by
  unfold classicalWordCommutatorExpansion
  rw [classicalListSum_eval]
  rw [List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  change (classicalWordCommutatorSplits w).map
      (fun p => classicalWordProductTerm p (fun y => AVenhance.spaceGrad f y i) g x) = _
  apply List.map_congr_left
  intro p hp
  exact ThetaCommutator.classicalWordProductTerm_left_derivative p f g hf i x

theorem classicalWordCommutatorExpansion_right_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion w f (fun y => AVenhance.spaceGrad g y i) x =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (p.1, i :: p.2) f g x).sum := by
  unfold classicalWordCommutatorExpansion
  rw [classicalListSum_eval]
  rw [List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  change (classicalWordCommutatorSplits w).map
      (fun p => classicalWordProductTerm p f (fun y => AVenhance.spaceGrad g y i) x) = _
  apply List.map_congr_left
  intro p hp
  exact ThetaCommutator.classicalWordProductTerm_right_derivative p f g hg i x

theorem ThetaCommutator.classicalWordCommutatorExpansion_cons
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion (i :: w) f g x =
    classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x +
      classicalWordCommutatorExpansion w f (fun y => AVenhance.spaceGrad g y i) x := by
  change ((classicalWordCommutatorSplits (i :: w)).map fun p =>
      classicalWordProductTerm p f g).sum x = _
  rw [classicalListSum_eval]
  rw [classicalWordCommutatorSplits]
  rw [List.map_append]
  rw [List.map_append]
  rw [List.sum_append]
  simp only [List.map_map, Function.comp_def]
  rw [← ThetaCommutator.classicalWordProductExpansion_left_derivative w f g hf i x,
    ← classicalWordCommutatorExpansion_right_derivative w f g hg i x]

theorem classicalWordCommutatorExpansion_contDiff
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordCommutatorExpansion w f g) := by
  let terms := (classicalWordCommutatorSplits w).map fun p =>
    classicalWordProductTerm p f g
  have hterms : ∀ F ∈ terms, ContDiff ℝ (⊤ : ℕ∞) F := by
    intro F hF
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF
    exact ThetaCommutator.classicalWordProductTerm_contDiff p f g hf hg
  exact classicalContDiff_listSum terms hterms

theorem ThetaCommutator.classicalWordProductExpansion_firstDerivative (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordProductExpansion w f g) x i =
      classicalWordProductExpansion (i :: w) f g x := by
  let terms := (classicalWordSplits w).map fun p => classicalWordProductTerm p f g
  have hterms : ∀ F ∈ terms, ContDiff ℝ (⊤ : ℕ∞) F := by
    intro F hF
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF
    exact ThetaCommutator.classicalWordProductTerm_contDiff p f g hf hg
  unfold classicalWordProductExpansion
  change AVenhance.spaceGrad terms.sum x i = _
  rw [classicalSpaceGrad_listSum terms hterms i x]
  rw [classicalListSum_eval]
  simp only [terms]
  have hmap :
      ((classicalWordSplits w).map fun p =>
        AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) =
      ((classicalWordSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x +
          classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    apply List.map_congr_left
    intro p hp
    exact ThetaCommutator.classicalWordProductTerm_firstDerivative p f g hf hg i x
  have hmap' :
      List.map (fun F => AVenhance.spaceGrad F x i)
          (List.map (fun p => classicalWordProductTerm p f g) (classicalWordSplits w)) =
        ((classicalWordSplits w).map fun p =>
          classicalWordProductTerm (i :: p.1, p.2) f g x +
            classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    rw [List.map_map]
    change (classicalWordSplits w).map
        (fun p => AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) = _
    exact hmap
  rw [hmap']
  rw [ThetaCommutator.classicalListSum_map_add]
  simp only [classicalWordSplits, List.map_append, List.sum_append, List.map_map]
  simp only [← List.map_map]
  simp only [List.map_map, Function.comp_def]

/-- An arbitrary ordered coordinate derivative of a product is the finite Leibniz sum over all
ways to distribute its derivative word between the factors. -/
theorem classicalWordDerivative_mul (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x * g x) =
      classicalWordProductExpansion w f g := by
  induction w with
  | nil =>
    funext x
    simp [classicalWordDerivative, classicalWordProductExpansion,
      classicalWordSplits, classicalWordProductTerm]
  | cons i w ih =>
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => f y * g y)) x i = _
    rw [ih]
    exact ThetaCommutator.classicalWordProductExpansion_firstDerivative w f g hf hg i x

/-- The order-s transport commutator is precisely the Leibniz sum over splits that differentiate
the drift at least once. -/
theorem classicalWordDerivative_mul_commutator (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x * g x) =
      fun x => f x * classicalWordDerivative w g x +
        classicalWordCommutatorExpansion w f g x := by
  induction w generalizing f g with
  | nil =>
    funext x
    simp [classicalWordDerivative, classicalWordCommutatorExpansion,
      classicalWordCommutatorSplits]
  | cons i w ih =>
    have hDg : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w g) :=
      classicalWordDerivative_contDiff w g hg
    have hA : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => f y * classicalWordDerivative w g y) := hf.mul hDg
    have hC : ContDiff ℝ (⊤ : ℕ∞) (classicalWordCommutatorExpansion w f g) :=
      classicalWordCommutatorExpansion_contDiff w f g hf hg
    have hIH := ih f g hf hg
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => f y * g y)) x i = _
    rw [hIH]
    rw [classicalSpaceGrad_add _ _ hA hC i x]
    rw [classicalProduct_firstDerivative f (classicalWordDerivative w g) hf hDg i x]
    rw [classicalWordCommutatorExpansion_firstDerivative w f g hf hg i x]
    rw [ThetaCommutator.classicalWordCommutatorExpansion_cons w f g hf hg i x]
    have hdf : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) :=
      ThetaCommutator.classicalSpaceGrad_contDiff f hf i
    have hprod := classicalWordDerivative_mul w
      (fun y => AVenhance.spaceGrad f y i) g hdf hg
    have hIH' := ih (fun y => AVenhance.spaceGrad f y i) g hdf hg
    have hsplit (x : Vec 2) :
        classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
          AVenhance.spaceGrad f x i * classicalWordDerivative w g x +
            classicalWordCommutatorExpansion w
              (fun y => AVenhance.spaceGrad f y i) g x := by
      calc
        _ = classicalWordDerivative w
            (fun y => AVenhance.spaceGrad f y i * g y) x := (congrFun hprod x).symm
        _ = _ := congrFun hIH' x
    rw [hsplit]
    rw [← ThetaCommutator.classicalWordCommutatorExpansion_left_derivative w f g hf i x,
      ← classicalWordCommutatorExpansion_right_derivative w f g hg i x]
    simp only [classicalWordDerivative]
    ring

theorem ThetaCommutator.classicalWordDerivative_product_commutator_eq
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec 2) :
    classicalWordProductExpansion w f g x -
        f x * classicalWordDerivative w g x =
      classicalWordCommutatorExpansion w f g x := by
  have hprod := congrFun (classicalWordDerivative_mul w f g hf hg) x
  have hcomm := congrFun (classicalWordDerivative_mul_commutator w f g hf hg) x
  rw [← hprod]
  linarith

theorem ThetaCommutator.classicalList_abs_sum_le (L : List ℝ) :
    |L.sum| ≤ (L.map fun a => |a|).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.sum_cons, List.map_cons]
    calc
      |a + L.sum| ≤ |a| + |L.sum| := abs_add_le _ _
      _ ≤ |a| + (List.map (fun a => |a|) L).sum := by nlinarith [ih]

theorem ThetaCommutator.classicalWordCommutatorExpansion_abs_le
    (w : List (Fin 2)) (f g : Vec 2 → ℝ) (x : Vec 2) :
    |classicalWordCommutatorExpansion w f g x| ≤
      ((classicalWordCommutatorSplits w).map fun p =>
        |classicalWordProductTerm p f g x|).sum := by
  unfold classicalWordCommutatorExpansion
  rw [classicalListSum_eval]
  have h := ThetaCommutator.classicalList_abs_sum_le
    (List.map (fun F => F x)
      ((classicalWordCommutatorSplits w).map fun p => classicalWordProductTerm p f g))
  simpa only [List.map_map, Function.comp_def] using h

theorem ThetaCommutator.classicalWordDerivative_finSum (w : List (Fin 2))
    (f : Fin 2 → Vec 2 → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) :
    classicalWordDerivative w (fun x => ∑ j : Fin 2, f j x) =
      fun x => ∑ j : Fin 2, classicalWordDerivative w (f j) x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => ∑ j : Fin 2, f j y)) x i = _
    rw [ih]
    change fderiv ℝ (fun y => ∑ j : Fin 2, classicalWordDerivative w (f j) y)
      x (Homogenization.basisVec i) = _
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j : Fin 2 => classicalWordDerivative w (f j)) (by
        intro j hj
        exact (classicalWordDerivative_contDiff w (f j) (hf j)).differentiable
          (by simp) x)]
    rw [sum_apply]
    simp only [classicalWordDerivative, AVenhance.spaceGrad]

theorem ThetaCommutator.classicalTransport_eq_finSum (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ) :
    classicalTransport b u = fun x => ∑ j : Fin 2,
      b x j * AVenhance.spaceGrad u x j := by
  funext x
  simp [classicalTransport, Homogenization.vecDot]

/-- Arbitrary ordered derivatives of the transport term are given by the finite Leibniz sum over
the drift components and all derivative splits. -/
theorem classicalWordDerivative_transport (w : List (Fin 2))
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    classicalWordDerivative w (classicalTransport b u) =
      fun x => ∑ j : Fin 2,
        classicalWordProductExpansion w (fun y => b y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
  rw [ThetaCommutator.classicalTransport_eq_finSum]
  rw [ThetaCommutator.classicalWordDerivative_finSum w
    (fun j y => b y j * AVenhance.spaceGrad u y j) (by
      intro j
      exact ((contDiff_pi.1 hb) j).mul (ThetaCommutator.classicalSpaceGrad_contDiff u hu j))]
  funext x
  apply Finset.sum_congr rfl
  intro j hj
  exact congrFun
    (classicalWordDerivative_mul w (fun y => b y j)
      (fun y => AVenhance.spaceGrad u y j)
      ((contDiff_pi.1 hb) j) (ThetaCommutator.classicalSpaceGrad_contDiff u hu j)) x

/-- The arbitrary order transport commutator is the sum of exactly the Leibniz terms in which a
derivative lands on the drift, written as the full product expansion with its principal term
removed componentwise. -/
theorem classicalWordDerivative_transport_commutator
    (w : List (Fin 2)) (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec 2) :
    classicalWordDerivative w (classicalTransport b u) x -
        Homogenization.vecDot (b x)
          (AVenhance.spaceGrad (classicalWordDerivative w u) x) =
      ∑ j : Fin 2,
        (classicalWordProductExpansion w (fun y => b y j)
            (fun y => AVenhance.spaceGrad u y j) x -
          b x j * classicalWordDerivative w
            (fun y => AVenhance.spaceGrad u y j) x) := by
  rw [classicalWordDerivative_transport w b u hb hu]
  have hprincipal : ∀ j : Fin 2,
      classicalWordDerivative w (fun y => AVenhance.spaceGrad u y j) x =
        AVenhance.spaceGrad (classicalWordDerivative w u) x j := by
    intro j
    exact congrFun (classicalWordDerivative_commute_gradient w u hu j) x
  simp only [Homogenization.vecDot]
  simp_rw [hprincipal]
  rw [Finset.sum_sub_distrib]

/-- After cancelling the principal transport derivative, the order-s commutator is the finite
sum of the Leibniz terms that differentiate a drift component. -/
theorem classicalWordDerivative_transport_eq_commutatorExpansion
    (w : List (Fin 2)) (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec 2) :
    classicalWordDerivative w (classicalTransport b u) x -
        Homogenization.vecDot (b x)
          (AVenhance.spaceGrad (classicalWordDerivative w u) x) =
      ∑ j : Fin 2,
        classicalWordCommutatorExpansion w (fun y => b y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
  rw [classicalWordDerivative_transport_commutator w b u hb hu x]
  apply Finset.sum_congr rfl
  intro j hj
  exact ThetaCommutator.classicalWordDerivative_product_commutator_eq w
    (fun y => b y j) (fun y => AVenhance.spaceGrad u y j)
    ((contDiff_pi.1 hb) j) (ThetaCommutator.classicalSpaceGrad_contDiff u hu j) x

theorem ThetaCommutator.classicalList_sum_mono {α : Type} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have htail : ∀ z ∈ L, f z ≤ g z := by
      intro z hz
      exact h z (by simp [hz])
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih htail)

end AVenhance.Infra.Section4
