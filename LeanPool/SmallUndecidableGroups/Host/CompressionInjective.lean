/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.Compression
public import LeanPool.SmallUndecidableGroups.Borisov.Model.FinalModelInjective
public import LeanPool.SmallUndecidableGroups.Host.ZStage
public import Mathlib.Tactic.Group

/-!
# Semantic inverse for the six compression eliminations

The compressed presentation need not be identified with the final HNN model
in order to prove that the Borisov group survives the compression.  It is
enough to interpret the three surviving generators `D,S,Z` in the final HNN
model.  The six conjugation equations recover all nine old generators, and
therefore give a homomorphism from the compressed presentation to that model.
The resulting triangle with `Compression.hom` commutes.  Its other side is
the composite of three known injective maps, so `Compression.hom` is
injective.
-/

@[expose] public section

namespace Undecidability
namespace HostCompressionInjective

open BorisovCStage
open BorisovFinalModel
open Host
open HostYStage
open HostZStage

noncomputable section

variable (datum : Thue.StandingDatum)
variable (theta : ThetaData datum)
variable (zeta : ZetaData datum theta)

/-- The final host model after the two proper compression HNN extensions. -/
abbrev Z := ZStage datum theta zeta

/-- The original Borisov model included through both proper HNN stages. -/
def gammaToZ : Gamma datum →* Z datum theta zeta :=
  (toZStage datum theta zeta).comp (toYStage datum theta)

/-- Values of the nine generators immediately before the six eliminations. -/
def oldValue : OldGen → Z datum theta zeta
  | .d => gammaToZ datum theta zeta (HostYStage.d datum)
  | .e => gammaToZ datum theta zeta (HostYStage.e datum)
  | .s1 => gammaToZ datum theta zeta (HostYStage.s1 datum)
  | .s2 => gammaToZ datum theta zeta (HostYStage.s2 datum)
  | .c => gammaToZ datum theta zeta (HostYStage.c datum)
  | .t => gammaToZ datum theta zeta (HostYStage.t datum)
  | .k => gammaToZ datum theta zeta (HostYStage.k datum)
  | .y => toZStage datum theta zeta (yLetter datum theta)
  | .z => zLetter datum theta zeta

/-- Values of the retained generators `(D,S,Z)`. -/
def hostValue : Fin 3 → Z datum theta zeta :=
  ![oldValue datum theta zeta .d,
    oldValue datum theta zeta .s1,
    oldValue datum theta zeta .z]

private theorem inverse_conjugation {G : Type*} [Group G]
    {x a b : G} (h : x⁻¹ * a * x = b⁻¹) :
    x⁻¹ * a⁻¹ * x = b := by
  have hi := congrArg Inv.inv h
  simpa [mul_inv_rev, mul_assoc] using hi

private theorem map_y_conjugates_d :
    (oldValue datum theta zeta .y)⁻¹ *
        oldValue datum theta zeta .d * oldValue datum theta zeta .y =
      (oldValue datum theta zeta .e)⁻¹ := by
  simpa only [oldValue, gammaToZ, MonoidHom.comp_apply, map_mul, map_inv] using
    congrArg (toZStage datum theta zeta) (y_conjugates_d datum theta)

private theorem map_y_conjugates_t :
    (oldValue datum theta zeta .y)⁻¹ *
        oldValue datum theta zeta .t * oldValue datum theta zeta .y =
      oldValue datum theta zeta .k := by
  simpa only [oldValue, gammaToZ, MonoidHom.comp_apply, map_mul, map_inv] using
    congrArg (toZStage datum theta zeta) (y_conjugates_t datum theta)

private theorem map_y_conjugates_e :
    (oldValue datum theta zeta .y)⁻¹ *
        oldValue datum theta zeta .e * oldValue datum theta zeta .y =
      oldValue datum theta zeta .d := by
  simpa only [oldValue, gammaToZ, MonoidHom.comp_apply, map_mul, map_inv] using
    congrArg (toZStage datum theta zeta) (y_conjugates_e datum theta)

private theorem map_y_conjugates_s1 :
    (oldValue datum theta zeta .y)⁻¹ *
        oldValue datum theta zeta .s1 * oldValue datum theta zeta .y =
      (oldValue datum theta zeta .s2)⁻¹ := by
  simpa only [oldValue, gammaToZ, MonoidHom.comp_apply, map_mul, map_inv] using
    congrArg (toZStage datum theta zeta) (y_conjugates_s1 datum theta)

private theorem map_z_conjugates_d :
    (oldValue datum theta zeta .z)⁻¹ *
        oldValue datum theta zeta .d * oldValue datum theta zeta .z =
      oldValue datum theta zeta .t := by
  simpa only [oldValue, gammaToZ, MonoidHom.comp_apply, dY, tY] using
    z_conjugates_d datum theta zeta

private theorem map_z_conjugates_t :
    (oldValue datum theta zeta .z)⁻¹ *
        oldValue datum theta zeta .t * oldValue datum theta zeta .z =
      oldValue datum theta zeta .c := by
  simpa only [oldValue, gammaToZ, MonoidHom.comp_apply, tY, cY] using
    z_conjugates_t datum theta zeta

private theorem map_z_conjugates_c :
    (oldValue datum theta zeta .z)⁻¹ *
        oldValue datum theta zeta .c * oldValue datum theta zeta .z =
      oldValue datum theta zeta .y := by
  simpa only [oldValue, gammaToZ, MonoidHom.comp_apply, cY, y] using
    z_conjugates_c datum theta zeta

/-- Each ordered substitution word evaluates back to the old generator it
eliminated. -/
theorem eval_tau (g : OldGen) :
    Word.eval (hostValue datum theta zeta) (tau g) =
      oldValue datum theta zeta g := by
  let x := hostValue datum theta zeta
  have hd : Word.eval x Host.dWord = oldValue datum theta zeta .d := by
    simp [x, Host.dWord, hostValue]
  have hs : Word.eval x Host.sWord = oldValue datum theta zeta .s1 := by
    simp [x, Host.sWord, hostValue]
  have hz : Word.eval x Host.zWord = oldValue datum theta zeta .z := by
    simp [x, Host.zWord, hostValue]
  have ht : Word.eval x Host.tWord = oldValue datum theta zeta .t := by
    simp only [Host.tWord, Word.eval_product, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Word.eval_inverse, mul_one]
    rw [hd, hz]
    exact map_z_conjugates_d datum theta zeta
  have hc : Word.eval x Host.cWord = oldValue datum theta zeta .c := by
    simp only [Host.cWord, Word.eval_product, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Word.eval_inverse, mul_one]
    rw [ht, hz]
    exact map_z_conjugates_t datum theta zeta
  have hy : Word.eval x Host.yWord = oldValue datum theta zeta .y := by
    simp only [Host.yWord, Word.eval_product, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Word.eval_inverse, mul_one]
    rw [hc, hz]
    exact map_z_conjugates_c datum theta zeta
  have he : Word.eval x Host.eWord = oldValue datum theta zeta .e := by
    simp only [Host.eWord, Word.eval_product, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Word.eval_inverse, mul_one]
    rw [hy, hd]
    exact inverse_conjugation (map_y_conjugates_d datum theta zeta)
  have hk : Word.eval x Host.kWord = oldValue datum theta zeta .k := by
    simp only [Host.kWord, Word.eval_product, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Word.eval_inverse, mul_one]
    rw [hy, ht]
    exact map_y_conjugates_t datum theta zeta
  have hs2 : Word.eval x Host.s2Word = oldValue datum theta zeta .s2 := by
    simp only [Host.s2Word, Word.eval_product, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Word.eval_inverse, mul_one]
    rw [hy, hs]
    exact inverse_conjugation (map_y_conjugates_s1 datum theta zeta)
  cases g <;> simp only [tau]
  · exact hd
  · exact he
  · exact hs
  · exact hs2
  · exact hc
  · exact ht
  · exact hk
  · exact hy
  · exact hz

/-! ## Evaluation of words in the nine-generator alphabet -/

/-- Semantic evaluation of a word in the old, nine-generator alphabet. -/
def evalOld (w : OldWord) : Z datum theta zeta :=
  FreeGroup.lift (oldValue datum theta zeta) (FreeGroup.mk w)

@[simp] theorem evalOld_generator (g : OldGen) :
    evalOld datum theta zeta (OldWord.generator g) =
      oldValue datum theta zeta g := by
  simp [evalOld, OldWord.generator]

@[simp] theorem evalOld_mul (u v : OldWord) :
    evalOld datum theta zeta (OldWord.mul u v) =
      evalOld datum theta zeta u * evalOld datum theta zeta v :=
  map_mul (FreeGroup.lift (oldValue datum theta zeta))
    (FreeGroup.mk u) (FreeGroup.mk v)

@[simp] theorem evalOld_inverse (u : OldWord) :
    evalOld datum theta zeta (OldWord.inverse u) =
      (evalOld datum theta zeta u)⁻¹ := by
  have hm : FreeGroup.mk (OldWord.inverse u) = (FreeGroup.mk u)⁻¹ := by
    rw [FreeGroup.inv_mk]
    rfl
  rw [evalOld, hm]
  exact map_inv (FreeGroup.lift (oldValue datum theta zeta)) (FreeGroup.mk u)

@[simp] theorem evalOld_product (us : List OldWord) :
    evalOld datum theta zeta (OldWord.product us) =
      (us.map (evalOld datum theta zeta)).prod := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      change evalOld datum theta zeta (OldWord.mul u (OldWord.product us)) = _
      simp [ih]

@[simp] theorem evalOld_pow (u : OldWord) (n : ℕ) :
    evalOld datum theta zeta (OldWord.pow u n) =
      evalOld datum theta zeta u ^ n := by
  rw [evalOld, OldWord.pow, ← FreeGroup.pow_mk]
  exact map_pow (FreeGroup.lift (oldValue datum theta zeta))
    (FreeGroup.mk u) n

theorem evalOld_positive (w : List (Fin 2)) :
    evalOld datum theta zeta (OldWord.positive w) =
      (w.map fun i => if i = 0 then oldValue datum theta zeta .s1
        else oldValue datum theta zeta .s2).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change evalOld datum theta zeta
          (OldWord.mul (OldWord.generator (if i = 0 then .s1 else .s2))
            (OldWord.positive w)) = _
      rw [evalOld_mul, evalOld_generator, ih]
      by_cases hi : i = 0 <;> simp [hi]

@[simp] theorem evalOld_relation (u v : OldWord) :
    evalOld datum theta zeta (OldWord.relation u v) =
      evalOld datum theta zeta u * (evalOld datum theta zeta v)⁻¹ := by
  simp [OldWord.relation]

@[simp] theorem evalOld_commutator (u v : OldWord) :
    evalOld datum theta zeta (OldWord.commutator u v) =
      (evalOld datum theta zeta u)⁻¹ *
        (evalOld datum theta zeta v)⁻¹ *
        evalOld datum theta zeta u * evalOld datum theta zeta v := by
  simp [OldWord.commutator, mul_assoc]

/-- Evaluation commutes with substitution of the six eliminated
generators. -/
theorem eval_evaluate (w : OldWord) :
    Word.eval (hostValue datum theta zeta) (OldWord.evaluate tau w) =
      evalOld datum theta zeta w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨g, sign⟩
      have hold : evalOld datum theta zeta ((g, sign) :: w) =
          (if sign then oldValue datum theta zeta g
            else (oldValue datum theta zeta g)⁻¹) *
            evalOld datum theta zeta w := by
        cases sign <;> simp [evalOld, FreeGroup.lift_mk]
      rw [hold]
      cases sign
      · change Word.eval (hostValue datum theta zeta)
            (Word.mul (Word.inverse (tau g)) (OldWord.evaluate tau w)) = _
        rw [Word.eval_mul, Word.eval_inverse, eval_tau, ih]
        simp
      · change Word.eval (hostValue datum theta zeta)
            (Word.mul (tau g) (OldWord.evaluate tau w)) = _
        rw [Word.eval_mul, eval_tau, ih]
        simp

/-! ## The nine surviving relations in the semantic model -/

/-- Borisov's seven generators, included in the final `z`-stage. -/
def borisovValue : Fin 7 → Z datum theta zeta :=
  gammaToZ datum theta zeta ∘
    modelGenerator datum (HostYStage.FreeInput datum)

theorem borisovValue_eq_oldGenerator (i : Fin 7) :
    borisovValue datum theta zeta i =
      oldValue datum theta zeta (Compression.oldGenerator i) := by
  fin_cases i <;> rfl

@[simp] private theorem eval_borisov_dWord :
    Word.eval (borisovValue datum theta zeta) Borisov.dWord =
      oldValue datum theta zeta .d := by
  simpa [Borisov.dWord, Compression.oldGenerator] using
    borisovValue_eq_oldGenerator datum theta zeta (0 : Fin 7)

@[simp] private theorem eval_borisov_eWord :
    Word.eval (borisovValue datum theta zeta) Borisov.eWord =
      oldValue datum theta zeta .e := by
  simpa [Borisov.eWord, Compression.oldGenerator] using
    borisovValue_eq_oldGenerator datum theta zeta (1 : Fin 7)

@[simp] private theorem eval_borisov_s1Word :
    Word.eval (borisovValue datum theta zeta) Borisov.s1Word =
      oldValue datum theta zeta .s1 := by
  simpa [Borisov.s1Word, Compression.oldGenerator] using
    borisovValue_eq_oldGenerator datum theta zeta (2 : Fin 7)

@[simp] private theorem eval_borisov_cWord :
    Word.eval (borisovValue datum theta zeta) Borisov.cWord =
      oldValue datum theta zeta .c := by
  simpa [Borisov.cWord, Compression.oldGenerator] using
    borisovValue_eq_oldGenerator datum theta zeta (4 : Fin 7)

@[simp] private theorem eval_borisov_tWord :
    Word.eval (borisovValue datum theta zeta) Borisov.tWord =
      oldValue datum theta zeta .t := by
  simpa [Borisov.tWord, Compression.oldGenerator] using
    borisovValue_eq_oldGenerator datum theta zeta (5 : Fin 7)

@[simp] private theorem eval_borisov_kWord :
    Word.eval (borisovValue datum theta zeta) Borisov.kWord =
      oldValue datum theta zeta .k := by
  simpa [Borisov.kWord, Compression.oldGenerator] using
    borisovValue_eq_oldGenerator datum theta zeta (6 : Fin 7)

/-- Every Borisov relator remains valid after the two proper HNN
extensions. -/
theorem borisov_relator_eq_one (i : Fin 14) :
    Word.eval (borisovValue datum theta zeta)
        ((Borisov.presentation datum).relator i) = 1 := by
  have hm :
      Word.eval
          (modelGenerator datum (HostYStage.FreeInput datum))
          ((Borisov.presentation datum).relator i) = 1 := by
    calc
      Word.eval
          (modelGenerator datum (HostYStage.FreeInput datum))
          ((Borisov.presentation datum).relator i) =
          toFinalModel datum (HostYStage.FreeInput datum)
            ((Borisov.presentation datum).evalWord
              ((Borisov.presentation datum).relator i)) :=
        (toFinalModel_evalWord datum (HostYStage.FreeInput datum) _).symm
      _ = toFinalModel datum (HostYStage.FreeInput datum) 1 := by
        rw [(Borisov.presentation datum).relator_eq_one i]
      _ = 1 := map_one _
  change Word.eval
      (gammaToZ datum theta zeta ∘
        modelGenerator datum (HostYStage.FreeInput datum))
      ((Borisov.presentation datum).relator i) = 1
  rw [← Word.map_eval, hm, map_one]

private theorem evalOld_positive_eq_borisov (w : List (Fin 2)) :
    evalOld datum theta zeta (OldWord.positive w) =
      Word.eval (borisovValue datum theta zeta) (Borisov.positiveWord w) := by
  simp only [evalOld_positive, Borisov.positiveWord,
    Word.eval_substitutePositive]
  congr 1

private theorem swapped_commutator_eq_one {G : Type*} [Group G]
    {a b : G} (h : a⁻¹ * b⁻¹ * a * b = 1) :
    b⁻¹ * a⁻¹ * b * a = 1 := by
  have hab : a * b = b * a := by
    calc
      a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [h]; simp
  calc
    b⁻¹ * a⁻¹ * b * a = b⁻¹ * a⁻¹ * (b * a) := by group
    _ = b⁻¹ * a⁻¹ * (a * b) := by rw [hab]
    _ = 1 := by group

/-- The eight inherited Borisov relations and the last `y`-relation all
hold before syntactic elimination. -/
theorem surviving_relator_eq_one (i : Fin 9) :
    evalOld datum theta zeta
        (oldSurvivingRelator datum.F datum.E datum.P i) = 1 := by
  fin_cases i
  · simpa [oldSurvivingRelator, Borisov.presentation,
      Borisov.sDRelator, borisovValue_eq_oldGenerator,
      Compression.oldGenerator, mul_assoc] using
      borisov_relator_eq_one datum theta zeta 0
  · simpa [oldSurvivingRelator, Borisov.presentation,
      Borisov.sERelator, borisovValue_eq_oldGenerator,
      Compression.oldGenerator, mul_assoc] using
      borisov_relator_eq_one datum theta zeta 1
  · simpa [oldSurvivingRelator, Borisov.presentation,
      borisovValue_eq_oldGenerator, Compression.oldGenerator,
      mul_assoc] using borisov_relator_eq_one datum theta zeta 4
  · simpa [oldSurvivingRelator, oldSimulationRelator,
      Borisov.presentation, Borisov.simulationRelator,
      evalOld_positive_eq_borisov, borisovValue_eq_oldGenerator,
      Compression.oldGenerator, mul_assoc] using
      borisov_relator_eq_one datum theta zeta 6
  · simpa [oldSurvivingRelator, oldSimulationRelator,
      Borisov.presentation, Borisov.simulationRelator,
      evalOld_positive_eq_borisov, borisovValue_eq_oldGenerator,
      Compression.oldGenerator, mul_assoc] using
      borisov_relator_eq_one datum theta zeta 7
  · simpa [oldSurvivingRelator, oldSimulationRelator,
      Borisov.presentation, Borisov.simulationRelator,
      evalOld_positive_eq_borisov, borisovValue_eq_oldGenerator,
      Compression.oldGenerator, mul_assoc] using
      borisov_relator_eq_one datum theta zeta 8
  · have h :
        (oldValue datum theta zeta .t)⁻¹ *
            (oldValue datum theta zeta .d)⁻¹ *
            oldValue datum theta zeta .t * oldValue datum theta zeta .d = 1 := by
      simpa [Borisov.presentation, mul_assoc] using
        borisov_relator_eq_one datum theta zeta 10
    simpa [oldSurvivingRelator, mul_assoc] using
      swapped_commutator_eq_one h
  · let q := evalOld datum theta zeta (OldWord.positive datum.P)
    have h :
        (oldValue datum theta zeta .k)⁻¹ *
            (q⁻¹ * oldValue datum theta zeta .t * q)⁻¹ *
            oldValue datum theta zeta .k *
              (q⁻¹ * oldValue datum theta zeta .t * q) = 1 := by
      simpa [Borisov.presentation, Borisov.pWord,
        q, evalOld_positive_eq_borisov, mul_assoc] using
        borisov_relator_eq_one datum theta zeta 13
    simpa [oldSurvivingRelator, q, mul_assoc] using
      swapped_commutator_eq_one h
  · change evalOld datum theta zeta
      (OldWord.relation
        (OldWord.product
          [OldWord.inverse (OldWord.generator .y), OldWord.generator .e,
            OldWord.generator .y])
        (OldWord.generator .d)) = 1
    rw [evalOld_relation, evalOld_product]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      evalOld_inverse, evalOld_generator, mul_one]
    calc
      (oldValue datum theta zeta .y)⁻¹ *
            (oldValue datum theta zeta .e * oldValue datum theta zeta .y) *
            (oldValue datum theta zeta .d)⁻¹ =
          ((oldValue datum theta zeta .y)⁻¹ *
              oldValue datum theta zeta .e * oldValue datum theta zeta .y) *
            (oldValue datum theta zeta .d)⁻¹ := by group
      _ = oldValue datum theta zeta .d *
            (oldValue datum theta zeta .d)⁻¹ := by
          rw [map_y_conjugates_e]
      _ = 1 := by simp

/-! ## The decompression homomorphism -/

theorem host_relator_eq_one (i : Fin 9) :
    Word.eval (hostValue datum theta zeta)
        ((presentationOf datum).relator i) = 1 := by
  change Word.eval (hostValue datum theta zeta)
      (OldWord.evaluate tau
        (oldSurvivingRelator datum.F datum.E datum.P i)) = 1
  rw [eval_evaluate]
  exact surviving_relator_eq_one datum theta zeta i

/-- Interpret the compressed three-generator presentation in the final HNN
model.  This is the one-sided semantic inverse needed for injectivity. -/
def fromHost : (presentationOf datum).Group →* Z datum theta zeta :=
  (presentationOf datum).homOfRelators (hostValue datum theta zeta)
    (host_relator_eq_one datum theta zeta)

@[simp] theorem fromHost_of (i : Fin 3) :
    fromHost datum theta zeta (PresentedGroup.of i) =
      hostValue datum theta zeta i :=
  (presentationOf datum).homOfRelators_of _ _ i

theorem fromHost_evalWord (w : HostWord) :
    fromHost datum theta zeta ((presentationOf datum).evalWord w) =
      Word.eval (hostValue datum theta zeta) w :=
  (presentationOf datum).homOfRelators_evalWord _ _ w

/-- The injective route from Borisov's presentation through its semantic
model and the two proper HNN extensions. -/
def borisovToZ :
    (Borisov.presentation datum).Group →* Z datum theta zeta :=
  (gammaToZ datum theta zeta).comp
    (toFinalModel datum (HostYStage.FreeInput datum))

theorem borisovToZ_injective :
    Function.Injective (borisovToZ datum theta zeta) :=
  ((toZStage_injective datum theta zeta).comp
    (toYStage_injective datum theta)).comp
    (toFinalModel_injective datum (HostYStage.FreeInput datum))

/-- The six eliminations commute with the semantic inclusions. -/
theorem fromHost_comp_compression :
    (fromHost datum theta zeta).comp (Compression.hom datum) =
      borisovToZ datum theta zeta := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply, Compression.hom_of, fromHost_evalWord]
  change Word.eval (hostValue datum theta zeta)
      (tau (Compression.oldGenerator i)) = _
  rw [eval_tau]
  change oldValue datum theta zeta (Compression.oldGenerator i) =
    borisovToZ datum theta zeta (PresentedGroup.of i)
  rw [borisovToZ, MonoidHom.comp_apply, toFinalModel_of]
  exact (borisovValue_eq_oldGenerator datum theta zeta i).symm

/-- The subgroup equivalences constructed in Section 3 of the paper imply
injectivity of the compression homomorphism. -/
theorem compression_injective_of
    (theta : ThetaData datum) (zeta : ZetaData datum theta) :
    Compression.Injective datum := by
  intro x x' hxx'
  apply borisovToZ_injective datum theta zeta
  have h := congrArg (fromHost datum theta zeta) hxx'
  have hc := fromHost_comp_compression datum theta zeta
  have hx := DFunLike.congr_fun hc x
  have hx' := DFunLike.congr_fun hc x'
  exact hx.symm.trans (h.trans hx')

end

end HostCompressionInjective

namespace Host

/-- The canonical data from Section 3 of the paper give compression
injectivity for the concrete simulator. -/
theorem _root_.Undecidability.Host.compression_injective (datum : Thue.StandingDatum) :
    Compression.Injective datum :=
  HostCompressionInjective.compression_injective_of datum
    (HostYStage.thetaData datum)
    (HostZStage.zetaData datum (HostYStage.thetaData datum))

end Host
end Undecidability
